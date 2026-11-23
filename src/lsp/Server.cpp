#include "lsp/Server.h"

#include <cctype>
#include <condition_variable>
#include <cstdlib>
#include <istream>
#include <map>
#include <memory>
#include <mutex>
#include <ostream>
#include <thread>

#include "lsp/Analysis.h"
#include "syntax/Lexer.h"

namespace pia::lsp {

// ------------------------------------------------------------ transport

namespace {

// Whether `line` is the header `name` (which is lower case), and if so its
// value. Header names are case-insensitive in LSP, as in HTTP.
std::optional<std::string_view> headerValue(std::string_view line,
                                            std::string_view name) {
  if (line.size() <= name.size())
    return std::nullopt;
  for (size_t i = 0; i < name.size(); ++i)
    if (std::tolower(static_cast<unsigned char>(line[i])) != name[i])
      return std::nullopt;
  return line.substr(name.size());
}

} // namespace

std::optional<std::string> readMessage(std::istream &in) {
  size_t length = 0;
  bool haveLength = false;
  std::string line;
  for (;;) {
    if (!std::getline(in, line))
      return std::nullopt;
    if (!line.empty() && line.back() == '\r')
      line.pop_back();
    if (line.empty()) {
      if (haveLength)
        break;
      continue; // tolerate blank lines between messages
    }
    // Other headers, such as Content-Type, are allowed and ignored.
    std::optional<std::string_view> value =
        headerValue(line, "content-length:");
    if (!value)
      continue;
    length = std::strtoull(std::string(*value).c_str(), nullptr, 10);
    haveLength = true;
  }
  std::string body(length, '\0');
  if (length > 0 && !in.read(body.data(), static_cast<std::streamsize>(length)))
    return std::nullopt;
  return body;
}

void writeMessage(std::ostream &out, const std::string &body) {
  out << "Content-Length: " << body.size() << "\r\n\r\n" << body;
  out.flush();
}

std::string uriToPath(const std::string &uri) {
  const std::string scheme = "file://";
  if (uri.rfind(scheme, 0) != 0)
    return uri;
  std::string path;
  for (size_t i = scheme.size(); i < uri.size(); ++i) {
    if (uri[i] == '%' && i + 2 < uri.size()) {
      path += static_cast<char>(
          std::strtol(uri.substr(i + 1, 2).c_str(), nullptr, 16));
      i += 2;
    } else {
      path += uri[i];
    }
  }
  // file:///c%3A/x on Windows becomes /c:/x; drop the leading slash.
  if (path.size() > 2 && path[0] == '/' && path[2] == ':')
    path.erase(0, 1);
  return path;
}

namespace {

// ------------------------------------------------------------ helpers

Json position(const TextIndex &index, uint32_t offset) {
  Position p = index.position(offset);
  return Json::Object{{"line", p.line}, {"character", p.character}};
}

Json range(const TextIndex &index, Range r) {
  return Json::Object{{"start", position(index, r.begin)},
                      {"end", position(index, r.end)}};
}

uint32_t offsetOf(const TextIndex &index, const Json &pos) {
  return index.offset({static_cast<uint32_t>(pos["line"].asNumber()),
                       static_cast<uint32_t>(pos["character"].asNumber())});
}

std::string counterexampleText(const Goal &g) {
  std::string s;
  for (const auto &[name, value] : g.counterexample) {
    if (!s.empty())
      s += ", ";
    s += name + " = " + value;
  }
  return s;
}

enum class VerifyOn { Save, Change, Off };

struct Settings {
  VerifyOn on = VerifyOn::Save;
  bool showProved = false;
};

void readSettings(const Json &verify, Settings &s) {
  if (!verify.isObject())
    return;
  const std::string &on = verify["on"].asString();
  if (on == "save")
    s.on = VerifyOn::Save;
  if (on == "change")
    s.on = VerifyOn::Change;
  if (on == "off")
    s.on = VerifyOn::Off;
  if (verify["showProved"].isBool())
    s.showProved = verify["showProved"].asBool();
}

struct Document {
  std::string uri;
  std::string path;
  long version = 0;
  std::unique_ptr<Analysis> analysis;
  long proofVersion = -1; // the version `proofs` describes, or -1
  ProofReport proofs;
};

struct Job {
  long version = 0;
  std::string text;
  std::string path;
};

// ------------------------------------------------------------ server

class Server {
public:
  Server(std::istream &in, std::ostream &out, ServerOptions options)
      : in_(in), out_(out), options_(std::move(options)) {
    if (options_.checker)
      worker_ = std::thread([this] { work(); });
  }

  ~Server() {
    {
      std::lock_guard<std::mutex> lock(mutex_);
      stopping_ = true;
    }
    wake_.notify_all();
    if (worker_.joinable())
      worker_.join();
  }

  int run() {
    while (std::optional<std::string> body = readMessage(in_)) {
      std::optional<Json> msg = Json::parse(*body);
      if (!msg || !msg->isObject()) {
        sendError(Json(), -32700, "parse error");
        continue;
      }
      const std::string &method = (*msg)["method"].asString();
      bool isRequest = msg->has("id") && !method.empty();
      if (method == "exit")
        return shutdown_ ? 0 : 1;
      if (method.empty())
        continue; // a response to a request of ours
      std::lock_guard<std::mutex> lock(mutex_);
      if (!initialized_ && method != "initialize") {
        if (isRequest)
          sendError((*msg)["id"], -32002, "server not initialized");
        continue;
      }
      if (shutdown_ && isRequest) {
        sendError((*msg)["id"], -32600, "server is shutting down");
        continue;
      }
      dispatch(method, (*msg)["params"], (*msg)["id"], isRequest);
    }
    return 1; // the client went away without `exit`
  }

private:
  // ---------------------------------------------------------- output

  void send(Json msg) {
    msg["jsonrpc"] = "2.0";
    std::lock_guard<std::mutex> lock(outMutex_);
    writeMessage(out_, msg.dump());
  }
  void reply(const Json &id, Json result) {
    send(Json::Object{{"id", id}, {"result", std::move(result)}});
  }
  void sendError(const Json &id, int code, std::string message) {
    send(
        Json::Object{{"id", id},
                     {"error", Json::Object{{"code", code},
                                            {"message", std::move(message)}}}});
  }
  void notify(std::string method, Json params) {
    send(Json::Object{{"method", std::move(method)},
                      {"params", std::move(params)}});
  }

  // ---------------------------------------------------------- dispatch

  void dispatch(const std::string &method, const Json &params, const Json &id,
                bool isRequest) {
    if (method == "initialize")
      return initialize(params, id);
    if (method == "initialized")
      return;
    if (method == "shutdown") {
      shutdown_ = true;
      return reply(id, Json());
    }
    if (method == "textDocument/didOpen")
      return didOpen(params);
    if (method == "textDocument/didChange")
      return didChange(params);
    if (method == "textDocument/didSave")
      return didSave(params);
    if (method == "textDocument/didClose")
      return didClose(params);
    if (method == "workspace/didChangeConfiguration") {
      readSettings(params["settings"]["pia"]["verify"], settings_);
      for (auto &[uri, doc] : docs_)
        publish(doc);
      return;
    }
    if (method == "textDocument/hover")
      return reply(id, hover(params));
    if (method == "textDocument/definition")
      return reply(id, definition(params));
    if (method == "textDocument/documentSymbol")
      return reply(id, documentSymbols(params));
    if (method == "textDocument/completion")
      return reply(id, completion(params));
    if (method == "textDocument/codeAction")
      return reply(id, codeActions(params));
    if (method == "textDocument/references")
      return reply(id, references(params));
    if (method == "textDocument/documentHighlight")
      return reply(id, highlights(params));
    if (method == "textDocument/prepareRename")
      return reply(id, prepareRename(params));
    if (method == "textDocument/rename")
      return rename(params, id);
    if (method == "workspace/executeCommand")
      return reply(id, executeCommand(params));
    if (isRequest)
      sendError(id, -32601, "method not found: " + method);
  }

  void initialize(const Json &params, const Json &id) {
    initialized_ = true;
    readSettings(params["initializationOptions"]["verify"], settings_);
    Json::Object sync{{"openClose", true},
                      {"change", 1}, // full text
                      {"save", Json::Object{{"includeText", false}}}};
    Json::Object caps{
        {"positionEncoding", "utf-16"},
        {"textDocumentSync", sync},
        {"hoverProvider", true},
        {"definitionProvider", true},
        {"documentSymbolProvider", true},
        {"completionProvider", Json::Object{{"resolveProvider", false}}},
        {"codeActionProvider",
         Json::Object{{"codeActionKinds", Json::Array{"quickfix"}}}},
        {"referencesProvider", true},
        {"documentHighlightProvider", true},
        {"renameProvider", Json::Object{{"prepareProvider", true}}},
        {"executeCommandProvider",
         Json::Object{{"commands", Json::Array{"pia.server.verify"}}}},
        {"experimental",
         Json::Object{{"piaVerifier", static_cast<bool>(options_.checker)}}},
    };
    reply(id, Json::Object{
                  {"capabilities", caps},
                  {"serverInfo", Json::Object{{"name", "pia-lsp"},
                                              {"version", options_.version}}}});
  }

  // ---------------------------------------------------------- documents

  Document *find(const Json &params) {
    auto it = docs_.find(params["textDocument"]["uri"].asString());
    return it == docs_.end() ? nullptr : &it->second;
  }

  void didOpen(const Json &params) {
    const Json &td = params["textDocument"];
    Document &doc = docs_[td["uri"].asString()];
    doc.uri = td["uri"].asString();
    doc.path = uriToPath(doc.uri);
    doc.version = static_cast<long>(td["version"].asNumber());
    doc.analysis = std::make_unique<Analysis>(
        td["text"].asString(), syntax::isLiterateFileName(doc.uri));
    doc.proofVersion = -1;
    publish(doc);
    if (settings_.on != VerifyOn::Off)
      schedule(doc);
  }

  void didChange(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return;
    std::string text = doc->analysis->text();
    for (const Json &change : params["contentChanges"].asArray()) {
      if (!change.has("range")) {
        text = change["text"].asString();
        continue;
      }
      TextIndex index(text);
      uint32_t b = offsetOf(index, change["range"]["start"]);
      uint32_t e = offsetOf(index, change["range"]["end"]);
      if (e < b)
        std::swap(b, e);
      text = text.substr(0, b) + change["text"].asString() + text.substr(e);
    }
    doc->version =
        static_cast<long>(params["textDocument"]["version"].asNumber());
    doc->analysis = std::make_unique<Analysis>(
        std::move(text), syntax::isLiterateFileName(doc->uri));
    publish(*doc);
    if (settings_.on == VerifyOn::Change)
      schedule(*doc);
  }

  void didSave(const Json &params) {
    Document *doc = find(params);
    if (doc && settings_.on != VerifyOn::Off)
      schedule(*doc);
  }

  void didClose(const Json &params) {
    const std::string &uri = params["textDocument"]["uri"].asString();
    docs_.erase(uri);
    jobs_.erase(uri);
    notify("textDocument/publishDiagnostics",
           Json::Object{{"uri", uri}, {"diagnostics", Json::Array{}}});
  }

  Json executeCommand(const Json &params) {
    if (params["command"].asString() != "pia.server.verify")
      return Json();
    for (const Json &arg : params["arguments"].asArray()) {
      std::string uri = arg.isString() ? arg.asString() : arg["uri"].asString();
      auto it = docs_.find(uri);
      if (it != docs_.end())
        schedule(it->second);
    }
    return Json();
  }

  // ---------------------------------------------------------- diagnostics

  void publish(const Document &doc) {
    const Analysis &a = *doc.analysis;
    const TextIndex &index = a.index();
    Json::Array diags;
    auto add = [&](const Diag &d) {
      Json::Object j{{"range", range(index, d.range)},
                     {"severity", static_cast<int>(d.severity)},
                     {"source", d.source},
                     {"message", d.message}};
      if (!d.code.empty())
        j["code"] = d.code;
      diags.push_back(std::move(j));
    };
    for (const Diag &d : a.diagnostics())
      add(d);
    for (const Diag &d : proofDiagnostics(doc))
      add(d);
    Json::Object params{{"uri", doc.uri}, {"diagnostics", std::move(diags)}};
    params["version"] = doc.version;
    notify("textDocument/publishDiagnostics", std::move(params));
  }

  // The proof results as diagnostics, if they are for the document's
  // current version. Results for an older version would point at text that
  // has since moved, so they are left out until the next proof finishes.
  std::vector<Diag> proofDiagnostics(const Document &doc) const {
    std::vector<Diag> out;
    if (doc.proofVersion != doc.version)
      return out;
    const Analysis &a = *doc.analysis;
    auto at = [&](uint32_t line, uint32_t column) {
      return tokenFrom(a.text(), a.index().offsetOfLineColumn(line, column));
    };
    for (const CompileError &e : doc.proofs.errors) {
      Diag d;
      d.range = at(e.line, e.column);
      d.source = "pia";
      d.message = e.message;
      out.push_back(std::move(d));
    }
    for (const Goal &g : doc.proofs.goals) {
      if (g.status == Goal::Status::Proved && !settings_.showProved)
        continue;
      Diag d = goalDiagnostic(g);
      d.range = at(g.line, g.column);
      out.push_back(std::move(d));
    }
    return out;
  }

  static Diag goalDiagnostic(const Goal &g) {
    Diag d;
    d.source = "pia-verify";
    d.code = g.kind;
    switch (g.status) {
    case Goal::Status::Failed:
      d.severity = Severity::Error;
      d.message = "not proved: " + g.claim;
      if (!g.counterexample.empty())
        d.message += "\ncounterexample: " + counterexampleText(g);
      // A goal refuted by a model says so through its counterexample, so the
      // method tag would only repeat it.
      if (g.method != "counterexample" && !g.method.empty())
        d.message += " [" + g.method + "]";
      break;
    case Goal::Status::Skipped:
      d.severity = Severity::Information;
      d.message = "skipped: " + g.claim + " [" + g.method + "]";
      break;
    case Goal::Status::Proved:
      d.severity = Severity::Hint;
      d.message = "proved: " + g.claim + " [" + g.method + "]";
      break;
    }
    return d;
  }

  // ---------------------------------------------------------- proofs

  void schedule(const Document &doc) {
    if (!options_.checker || !doc.analysis->parsed())
      return;
    jobs_[doc.uri] = Job{doc.version, doc.analysis->text(), doc.path};
    wake_.notify_one();
  }

  // Runs on the worker thread. `mutex_` guards docs_ and jobs_.
  void work() {
    std::unique_lock<std::mutex> lock(mutex_);
    for (;;) {
      wake_.wait(lock, [this] { return stopping_ || !jobs_.empty(); });
      if (stopping_)
        return;
      auto it = jobs_.begin();
      std::string uri = it->first;
      Job job = std::move(it->second);
      jobs_.erase(it);
      lock.unlock();
      ProofReport report = options_.checker(job.text, job.path);
      lock.lock();
      auto doc = docs_.find(uri);
      if (doc == docs_.end() || doc->second.version != job.version)
        continue;
      doc->second.proofs = std::move(report);
      doc->second.proofVersion = job.version;
      publish(doc->second);
    }
  }

  // ---------------------------------------------------------- features

  Json hover(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    uint32_t offset = offsetOf(a.index(), params["position"]);
    Range tok = tokenAt(a.text(), offset);
    std::string md;
    if (std::optional<Binding> b = a.resolve(offset))
      md = b->snippet;
    std::string goals = goalsAt(*doc, tok);
    if (!goals.empty()) {
      if (!md.empty())
        md += "\n\n---\n\n";
      md += "**Proof goals**\n\n" + goals;
    }
    if (md.empty())
      return Json();
    return Json::Object{
        {"contents", Json::Object{{"kind", "markdown"}, {"value", md}}},
        {"range", range(a.index(), tok)}};
  }

  // A Markdown list of the current proof goals that start inside `tok`.
  static std::string goalsAt(const Document &doc, Range tok) {
    std::string goals;
    if (doc.proofVersion != doc.version || tok.end == tok.begin)
      return goals;
    const TextIndex &index = doc.analysis->index();
    for (const Goal &g : doc.proofs.goals) {
      uint32_t at = index.offsetOfLineColumn(g.line, g.column);
      if (at < tok.begin || at >= tok.end)
        continue;
      switch (g.status) {
      case Goal::Status::Proved:
        goals += "- ✓ proved: " + g.claim + " *(" + g.method + ")*\n";
        break;
      case Goal::Status::Failed:
        goals += "- ✗ **not proved**: " + g.claim;
        if (!g.counterexample.empty())
          goals += "  \n  counterexample: `" + counterexampleText(g) + "`";
        goals += "\n";
        break;
      case Goal::Status::Skipped:
        goals += "- ○ skipped: " + g.claim + " *(" + g.method + ")*\n";
        break;
      }
    }
    return goals;
  }

  Json definition(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    std::optional<Binding> b =
        a.resolve(offsetOf(a.index(), params["position"]));
    if (!b)
      return Json();
    return Json::Object{{"uri", doc->uri},
                        {"range", range(a.index(), b->nameRange)}};
  }

  Json symbolJson(const TextIndex &index, const Symbol &s) {
    Json::Array children;
    for (const Symbol &c : s.children)
      children.push_back(symbolJson(index, c));
    Json::Object j{{"name", s.name},
                   {"kind", static_cast<int>(s.kind)},
                   {"range", range(index, s.range)},
                   {"selectionRange", range(index, s.selection)},
                   {"children", std::move(children)}};
    if (!s.detail.empty())
      j["detail"] = s.detail;
    return j;
  }

  Json documentSymbols(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    Json::Array out;
    for (const Symbol &s : doc->analysis->symbols())
      out.push_back(symbolJson(doc->analysis->index(), s));
    return out;
  }

  Json completion(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    Json::Array items;
    // CompletionItemKind numbers from the LSP specification.
    enum CompletionItemKind {
      Function = 3,
      Variable = 6,
      Class = 7,
      Keyword = 14
    };
    for (std::string_view k : keywords())
      items.push_back(Json::Object{{"label", k}, {"kind", Keyword}});
    for (const Binding &b :
         a.completions(offsetOf(a.index(), params["position"]))) {
      int kind = b.role == "function" ? Function
                 : b.role == "type"   ? Class
                                      : Variable;
      items.push_back(
          Json::Object{{"label", b.name},
                       {"kind", kind},
                       {"detail", b.role},
                       {"documentation", Json::Object{{"kind", "markdown"},
                                                      {"value", b.snippet}}}});
    }
    return Json::Object{{"isIncomplete", false}, {"items", std::move(items)}};
  }

  // ---------------------------------------------------------- renaming

  // Edits that rename the name bound or used at `offset` to `to`, or none
  // when it does not resolve.
  Json::Array renameEdits(const Analysis &a, uint32_t offset,
                          const std::string &to) {
    Json::Array edits;
    for (Range r : a.references(offset))
      edits.push_back(
          Json::Object{{"range", range(a.index(), r)}, {"newText", to}});
    return edits;
  }

  Json references(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    std::vector<Range> refs =
        a.references(offsetOf(a.index(), params["position"]));
    bool withDecl = params["context"]["includeDeclaration"].asBool(true);
    Json::Array out;
    std::optional<Binding> b =
        a.resolve(offsetOf(a.index(), params["position"]));
    for (size_t i = 0; i < refs.size(); ++i) {
      if (!withDecl && b && refs[i].begin == b->nameRange.begin)
        continue;
      out.push_back(Json::Object{{"uri", doc->uri},
                                 {"range", range(a.index(), refs[i])}});
    }
    return out;
  }

  Json highlights(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    Json::Array out;
    for (Range r : a.references(offsetOf(a.index(), params["position"])))
      out.push_back(Json::Object{{"range", range(a.index(), r)}});
    return out;
  }

  Json prepareRename(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    uint32_t offset = offsetOf(a.index(), params["position"]);
    if (a.references(offset).empty())
      return Json();
    return range(a.index(), tokenAt(a.text(), offset));
  }

  void rename(const Json &params, const Json &id) {
    Document *doc = find(params);
    const std::string &to = params["newName"].asString();
    if (!doc)
      return reply(id, Json());
    if (!isName(to))
      return sendError(id, -32602, "'" + to + "' is not a Pia name");
    const Analysis &a = *doc->analysis;
    Json::Array edits =
        renameEdits(a, offsetOf(a.index(), params["position"]), to);
    if (edits.empty())
      return reply(id, Json());
    reply(id, Json::Object{
                  {"changes", Json::Object{{doc->uri, std::move(edits)}}}});
  }

  static bool isName(const std::string &s) {
    if (s.empty())
      return false;
    auto start = [](char c) {
      return std::isalpha(static_cast<unsigned char>(c)) || c == '_' ||
             static_cast<unsigned char>(c) >= 0x80;
    };
    if (!start(s[0]))
      return false;
    for (char c : s)
      if (!start(c) && !std::isdigit(static_cast<unsigned char>(c)) &&
          c != '\'')
        return false;
    for (std::string_view k : keywords())
      if (s == k)
        return false;
    return true;
  }

  // Quick fixes for the range the client asks about: the fix of each lint
  // there (ADR 0037), and a rename for each shadowing error the client
  // sends back (ADR 0022).
  Json codeActions(const Json &params) {
    Document *doc = find(params);
    if (!doc)
      return Json();
    const Analysis &a = *doc->analysis;
    Json::Array actions;
    uint32_t from = offsetOf(a.index(), params["range"]["start"]);
    uint32_t to = offsetOf(a.index(), params["range"]["end"]);
    for (const pia::syntax::Lint &l : a.lints()) {
      uint32_t end = std::max(l.end, l.loc.offset + 1);
      if (l.edits.empty() || l.fixTitle.empty() || end < from ||
          l.loc.offset > to)
        continue;
      actions.push_back(lintFix(*doc, l, end));
    }
    for (const Json &d : params["context"]["diagnostics"].asArray())
      if (std::optional<Json> fix = shadowingFix(*doc, d))
        actions.push_back(std::move(*fix));
    return actions;
  }

  static Json quickFix(const Document &doc, std::string title, bool preferred,
                       Json diagnostic, Json::Array edits) {
    return Json::Object{
        {"title", std::move(title)},
        {"kind", "quickfix"},
        {"isPreferred", preferred},
        {"diagnostics", Json::Array{std::move(diagnostic)}},
        {"edit",
         Json::Object{{"changes", Json::Object{{doc.uri, std::move(edits)}}}}}};
  }

  static Json lintFix(const Document &doc, const pia::syntax::Lint &l,
                      uint32_t end) {
    const TextIndex &index = doc.analysis->index();
    Json::Array edits;
    for (const pia::syntax::TextEdit &e : l.edits)
      edits.push_back(Json::Object{
          {"range", range(index, Range{e.begin, e.end})}, {"newText", e.text}});
    Json diag = Json::Object{{"range", range(index, Range{l.loc.offset, end})},
                             {"severity", static_cast<int>(Severity::Warning)},
                             {"source", "pia-lint"},
                             {"code", l.name},
                             {"message", l.message}};
    return quickFix(doc, l.fixTitle, l.preferred, std::move(diag),
                    std::move(edits));
  }

  // A shadowing error reads "'<old>' ... so rename it to <new>." and points
  // at the binder or at the `let` that binds it. The fix renames the binder
  // and its uses. Any other diagnostic gets no fix.
  std::optional<Json> shadowingFix(const Document &doc, const Json &d) {
    const Analysis &a = *doc.analysis;
    const std::string &msg = d["message"].asString();
    const std::string marker = "rename it to ";
    size_t at = msg.rfind(marker);
    if (msg.empty() || msg[0] != '\'' || at == std::string::npos)
      return std::nullopt;
    size_t close = msg.find('\'', 1);
    if (close == std::string::npos)
      return std::nullopt;
    std::string from = msg.substr(1, close - 1);
    std::string to = msg.substr(at + marker.size());
    while (!to.empty() && (to.back() == '.' ||
                           std::isspace(static_cast<unsigned char>(to.back()))))
      to.pop_back();
    if (!isName(to))
      return std::nullopt;
    std::optional<uint32_t> binder =
        findBinder(a, offsetOf(a.index(), d["range"]["start"]), from);
    if (!binder)
      return std::nullopt;
    Json::Array edits = renameEdits(a, *binder, to);
    if (edits.empty())
      return std::nullopt;
    return quickFix(doc, "Rename '" + from + "' to '" + to + "'",
                    /*preferred=*/true, d, std::move(edits));
  }

  // The binder of `name` for a diagnostic at `start`: the name itself
  // there, or its first whole-word occurrence later on that line, which is
  // where it is when the diagnostic points at the `let`.
  static std::optional<uint32_t> findBinder(const Analysis &a, uint32_t start,
                                            const std::string &name) {
    const std::string &text = a.text();
    size_t lineEnd = text.find('\n', start);
    if (lineEnd == std::string::npos)
      lineEnd = text.size();
    for (size_t pos = text.find(name, start);
         pos != std::string::npos && pos < lineEnd;
         pos = text.find(name, pos + 1)) {
      Range tok = tokenAt(text, static_cast<uint32_t>(pos));
      if (tok.begin == pos && tok.end == pos + name.size())
        return static_cast<uint32_t>(pos);
    }
    return std::nullopt;
  }

  std::istream &in_;
  std::ostream &out_;
  ServerOptions options_;
  Settings settings_;
  bool initialized_ = false;
  bool shutdown_ = false;

  std::mutex mutex_;    // documents, jobs and settings
  std::mutex outMutex_; // the output stream
  std::condition_variable wake_;
  bool stopping_ = false;
  std::map<std::string, Document> docs_;
  std::map<std::string, Job> jobs_;
  std::thread worker_;
};

} // namespace

int serve(std::istream &in, std::ostream &out, ServerOptions options) {
  Server server(in, out, std::move(options));
  return server.run();
}

} // namespace pia::lsp
