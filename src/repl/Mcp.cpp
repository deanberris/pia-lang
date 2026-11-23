#include "repl/Mcp.h"

#include "repl/Guide.h"

#include <chrono>
#include <cstring>
#include <string>

namespace pia::repl {

namespace {

constexpr const char *kProtocolVersion = "2025-06-18";
constexpr double kDefaultWaitMs = 10000;
constexpr double kMaxWaitMs = 120000;

lsp::Json schema(lsp::Json::Object properties, lsp::Json::Array required) {
  lsp::Json s;
  s["type"] = "object";
  s["properties"] = std::move(properties);
  s["required"] = std::move(required);
  return s;
}

lsp::Json prop(const char *type, const char *description) {
  lsp::Json p;
  p["type"] = type;
  p["description"] = description;
  return p;
}

lsp::Json tools() {
  lsp::Json execute;
  execute["name"] = "execute";
  execute["description"] =
      "Run Pia code in a persistent, verified REPL session. A cell is Pia "
      "code (definitions with let, expressions to evaluate) or a command "
      "(:help, :help <topic> for a guide to the language, :type e, :proof f, "
      ":env, :source f, :redef code, :forget f, "
      ":allow spec, :load file (.pia or literate .pia.md), :reset, :spawn e, "
      ":tasks, :wait n). Definitions join the environment "
      "only if every proof obligation in the whole environment is proved; "
      "failures come back with counterexamples. Expressions are proved, "
      "then compiled and run. Defining a name that exists is an error (no "
      "shadowing); use :redef to replace it, which re-verifies everything "
      "that uses it. Returns the cell's events, or a job number to poll if "
      "it is still running after wait_ms. The result is the REPL's text; "
      "pass json: true for the events as structured JSON as well.";
  execute["inputSchema"] = schema(
      {{"code", prop("string", "The cell: Pia code or a :command")},
       {"wait_ms", prop("number", "How long to wait for the result before "
                                  "returning a job to poll (default 10000)")},
       {"json", prop("boolean", "Also return the cell's events as JSON, "
                                "in structuredContent (default false)")}},
      {"code"});
  lsp::Json poll;
  poll["name"] = "poll";
  poll["description"] =
      "Wait for a job that execute returned, and get its state (queued, "
      "running, done) and, once done, its result.";
  poll["inputSchema"] =
      schema({{"job", prop("number", "The job number from execute")},
              {"wait_ms", prop("number", "How long to wait (default 10000)")},
              {"json", prop("boolean", "Also return the result as JSON, in "
                                       "structuredContent (default false)")}},
             {"job"});
  lsp::Json result;
  result["tools"] = lsp::Json::Array{execute, poll};
  return result;
}

constexpr const char *kGuideScheme = "pia://guide/";

// The guide's topics as MCP resources, for clients that let an agent or a
// person attach them. They are the same text as `:help <topic>`, which
// works in every client because it goes through execute.
lsp::Json resources() {
  lsp::Json::Array list;
  for (const GuideTopic &t : guideTopics()) {
    lsp::Json r;
    r["uri"] = std::string(kGuideScheme) + t.name;
    r["name"] = t.name;
    r["title"] = t.title;
    r["description"] = t.summary;
    r["mimeType"] = "text/markdown";
    list.push_back(std::move(r));
  }
  lsp::Json result;
  result["resources"] = std::move(list);
  return result;
}

lsp::Json textContent(const std::string &text) {
  lsp::Json c;
  c["type"] = "text";
  c["text"] = text;
  return lsp::Json::Array{c};
}

std::chrono::milliseconds waitOf(const lsp::Json &args) {
  double ms = args["wait_ms"].asNumber(kDefaultWaitMs);
  if (ms < 0)
    ms = 0;
  if (ms > kMaxWaitMs)
    ms = kMaxWaitMs;
  return std::chrono::milliseconds(static_cast<long long>(ms));
}

bool wantsJson(const lsp::Json &args) {
  return args["json"].isBool() && args["json"].asBool();
}

lsp::Json reply(const lsp::Json &id, lsp::Json result) {
  lsp::Json r;
  r["jsonrpc"] = "2.0";
  r["id"] = id;
  r["result"] = std::move(result);
  return r;
}

lsp::Json errorReply(const lsp::Json &id, int code,
                     const std::string &message) {
  lsp::Json e;
  e["code"] = code;
  e["message"] = message;
  lsp::Json r;
  r["jsonrpc"] = "2.0";
  r["id"] = id;
  r["error"] = std::move(e);
  return r;
}

} // namespace

// Some clients, Claude Code among them, show an agent the structured
// content in place of the text when both are present, and the events are
// several times longer than the REPL's text. So the JSON is sent only when
// the caller asks for it.
lsp::Json McpServer::jobResult(const Kernel::Status &s, bool json) {
  lsp::Json structured;
  structured["job"] = static_cast<double>(s.job);
  structured["status"] = stateName(s.state);
  std::string text;
  bool isError = s.state == Kernel::State::Unknown;
  if (s.result) {
    lsp::Json cell = toJson(*s.result);
    structured["result"] = cell;
    text = render(*s.result);
    if (text.empty())
      text = s.result->ok ? "ok\n" : "failed\n";
    isError = !s.result->ok;
    // A failed cell carries a line on how to fix each kind of failure in it,
    // so an agent's next cell is more often right without reading a guide.
    if (isError)
      text += guideHints(text);
  } else if (s.state == Kernel::State::Unknown) {
    text = "there is no job " + std::to_string(s.job) + "\n";
  } else {
    text = "job " + std::to_string(s.job) + " is " + stateName(s.state) +
           "; call poll with this job number\n";
  }
  lsp::Json result;
  result["content"] = textContent(text);
  if (json)
    result["structuredContent"] = std::move(structured);
  result["isError"] = isError;
  return result;
}

lsp::Json McpServer::callTool(const std::string &name, const lsp::Json &args) {
  if (name == "execute") {
    if (!args["code"].isString()) {
      lsp::Json r;
      r["content"] = textContent("execute needs a \"code\" string\n");
      r["isError"] = true;
      return r;
    }
    uint64_t job = kernel_.submit(args["code"].asString());
    return jobResult(kernel_.poll(job, waitOf(args)), wantsJson(args));
  }
  if (name == "poll") {
    double job = args["job"].asNumber(0);
    return jobResult(
        kernel_.poll(job < 0 ? 0 : static_cast<uint64_t>(job), waitOf(args)),
        wantsJson(args));
  }
  lsp::Json r;
  r["content"] = textContent("unknown tool " + name + "\n");
  r["isError"] = true;
  return r;
}

lsp::Json McpServer::handle(const lsp::Json &message) {
  const lsp::Json &id = message["id"];
  std::string method =
      message["method"].isString() ? message["method"].asString() : "";
  bool notification = !message.has("id");
  if (method == "initialize") {
    lsp::Json caps;
    caps["tools"] = lsp::Json::Object{};
    caps["resources"] = lsp::Json::Object{};
    lsp::Json info;
    info["name"] = "pia-repl";
    info["version"] = "0.0.0";
    lsp::Json result;
    std::string version = message["params"]["protocolVersion"].isString()
                              ? message["params"]["protocolVersion"].asString()
                              : kProtocolVersion;
    result["protocolVersion"] = version;
    result["capabilities"] = std::move(caps);
    result["serverInfo"] = std::move(info);
    // Clients put the instructions in the agent's context before its first
    // call, so they carry what saves the most failed cells, and they are
    // short, since they cost context in every session.
    result["instructions"] = guideInstructions();
    return reply(id, std::move(result));
  }
  if (notification)
    return lsp::Json();
  if (method == "ping")
    return reply(id, lsp::Json::Object{});
  if (method == "tools/list")
    return reply(id, tools());
  if (method == "resources/list")
    return reply(id, resources());
  if (method == "resources/read") {
    const lsp::Json &uri = message["params"]["uri"];
    std::string u = uri.isString() ? uri.asString() : "";
    const GuideTopic *topic =
        u.rfind(kGuideScheme, 0) == 0
            ? findGuideTopic(std::string_view(u).substr(strlen(kGuideScheme)))
            : nullptr;
    if (!topic)
      return errorReply(id, -32002, "resource not found: " + u);
    lsp::Json c;
    c["uri"] = u;
    c["mimeType"] = "text/markdown";
    c["text"] = topic->text;
    lsp::Json result;
    result["contents"] = lsp::Json::Array{c};
    return reply(id, std::move(result));
  }
  if (method == "tools/call") {
    const lsp::Json &params = message["params"];
    if (!params["name"].isString())
      return errorReply(id, -32602, "tools/call needs a tool name");
    return reply(id, callTool(params["name"].asString(), params["arguments"]));
  }
  return errorReply(id, -32601, "method not found: " + method);
}

void McpServer::serve(std::istream &in, std::ostream &out) {
  std::string line;
  while (std::getline(in, line)) {
    if (line.find_first_not_of(" \t\r") == std::string::npos)
      continue;
    std::optional<lsp::Json> msg = lsp::Json::parse(line);
    lsp::Json r =
        msg ? handle(*msg) : errorReply(lsp::Json(), -32700, "parse error");
    if (r.isNull())
      continue;
    out << r.dump() << "\n";
    out.flush();
  }
}

} // namespace pia::repl
