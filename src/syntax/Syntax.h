// The syntax tree produced by the parser.
//
// It is uniform: every node has a kind, an optional text (a name, a literal
// spelling, an operator), a source location and ordered children. Sema (M4)
// builds its typed AST from this tree. The child layout of each kind is
// listed below; `?` marks an optional child, which is a `None` node when
// absent so positions stay fixed.

#ifndef PIA_SYNTAX_SYNTAX_H
#define PIA_SYNTAX_SYNTAX_H

#include <memory>
#include <ostream>
#include <string>
#include <vector>

#include "syntax/Token.h"

namespace pia::syntax {

#define PIA_NODE_KINDS(X)                                                    \
  X(None)                                                                    \
  /* items */                                                                \
  X(Program)       /* item* */                                               \
  X(LetItem)       /* text=name, flags; Params, RetAnnot?, Contracts, body */ \
  X(MetaOperator)  /* text=op; Fixity?, for-type?, body */                   \
  X(Fixity)        /* text="prec level assoc" */                             \
  X(Interface)     /* text=name; sig items */                                \
  X(Module)        /* text=name; Paths, item* */                             \
  X(Import)        /* text=path */                                           \
  X(ExprItem)      /* expr */                                                \
  X(SigVal)        /* text=name; Annot, Attrs, Contracts */                  \
  X(SigType)       /* text=name; TypeValue */                                \
  X(Sig)           /* a signature value: sig items */                        \
  X(SigInclude)    /* text=concept; type arguments */                        \
  X(SigLemma)      /* text=name; Params, Contracts */                        \
  X(Adapter)       /* text=name; concept type, item* */                      \
  X(Paths)         /* Path* */                                               \
  X(Path)          /* text=A.B.C */                                          \
  /* bindings */                                                             \
  X(Params)        /* Param* */                                              \
  X(Param)         /* text=name; Annot? */                                   \
  X(ParamUnit)                                                               \
  X(ParamHole)                                                               \
  X(RetAnnot)      /* Annot?, Attrs */                                       \
  X(Contracts)     /* Requires|Ensures|Decreases* */                         \
  X(Requires)      /* predicate */                                           \
  X(Ensures)       /* predicate */                                           \
  X(Decreases)     /* measure */                                             \
  X(Invariant)     /* predicate */                                           \
  X(Attrs)         /* Attribute* */                                          \
  X(Attribute)     /* text=name; args */                                     \
  X(NamedArg)      /* text=name; value */                                    \
  /* annotations and types */                                                \
  X(Annot)         /* Modifiers, type, where-predicate? */                   \
  X(Modifiers)     /* text="borrowed in mutable" (any subset, in order) */   \
  X(TypeName)      /* text=name */                                           \
  X(TypeKind)      /* the type of types */                                   \
  X(TypeInst)      /* text=name; type arguments */                           \
  X(RangeType)     /* text=name; lo, hi */                                   \
  X(SliceType)     /* element */                                             \
  X(ArrayType)     /* element, length */                                     \
  X(RecordType)    /* FieldDecl* */                                          \
  X(FieldDecl)     /* text=name; Annot */                                    \
  X(RefinementType) /* text=name; type, predicate */                         \
  X(UnitType)                                                                \
  X(UnionType)     /* type* */                                               \
  X(ArrowType)     /* Domain, result */                                      \
  X(Domain)        /* text=parameter name or empty; Modifiers, type, where? */ \
  X(TypeApp)       /* head, argument* */                                     \
  X(TypeValue)     /* body, Attrs, where-predicate? */                       \
  X(Variants)      /* Ctor* */                                               \
  X(Ctor)          /* text=name; payload? */                                 \
  /* expressions */                                                          \
  X(Name)          /* text=name */                                           \
  X(IntLit) X(FloatLit) X(StringLit) X(BoolLit) /* text=spelling */          \
  X(QuotedIdent)   /* text=name */                                           \
  X(Hole)                                                                    \
  X(Unit)                                                                    \
  X(OperatorValue) /* text=op */                                             \
  X(ListLit)       /* element* */                                            \
  X(RecordLit)     /* FieldInit* */                                          \
  X(RecordUpdate)  /* base, FieldInit* */                                    \
  X(FieldInit)     /* text=name; value */                                    \
  X(Quote)         /* quoted items, QuotedDecl or expression */              \
  X(QuotedDecl)    /* text=name; type */                                     \
  X(Splice)        /* text=name, or one expression child */                  \
  X(Apply)         /* function, argument+ */                                 \
  X(Field)         /* text=field (or $name); object */                       \
  X(Index)         /* object, index */                                       \
  X(Instantiate)   /* function, type argument+ */                            \
  X(Binary)        /* text=op; lhs, rhs */                                   \
  X(Neg)           /* operand */                                             \
  X(Range)         /* lo, hi */                                              \
  X(Assign)        /* place, value */                                        \
  X(If)            /* cond, then, else? */                                   \
  X(For)           /* pattern, iterable, step?, LoopAnnots, body */          \
  X(Spread)        /* pattern, iterable, Attrs, LoopAnnots, body */          \
  X(While)         /* cond, LoopAnnots, body */                              \
  X(LoopAnnots)    /* Invariant|Decreases* */                                \
  X(Quantifier)    /* text=forall|exists; Binder+, body */                   \
  X(Binder)        /* text=name; type? (typed) */                            \
  X(RangeBinder)   /* text=name; range */                                    \
  X(Assert) X(Assume) /* predicate */                                        \
  X(Try)           /* operand: `e?` (ADR 0028) */                            \
  X(Handle)        /* body, Arm+: `body handle | p -> e ...` (ADR 0028) */   \
  X(Sequence)      /* stmt, stmt (right-nested) */                           \
  X(LetIn)         /* text=name, flags; Params, RetAnnot?, Contracts, value, body */ \
  X(Lambda)        /* LParam+, body */                                       \
  X(LParam)        /* pattern, Annot? */                                     \
  X(Match)         /* scrutinee, Arm+ */                                     \
  X(Arm)           /* pattern, body */                                       \
  /* patterns */                                                             \
  X(PVar)          /* text=name */                                           \
  X(PLit)          /* text=spelling */                                       \
  X(PCtor)         /* text=ctor; pattern+ */                                 \
  X(PTyped)        /* pattern, type */                                       \
  X(PRecord)       /* PField* */                                             \
  X(PField)        /* text=field; pattern? */                                \
  X(PSplice)       /* text=name */                                           \
  /* comments, kept beside a node's children, never among them */            \
  X(Comment)       /* text=content; flags="<style> <place>" (ADR 0029) */

enum class NodeKind : uint8_t {
#define PIA_NODE_ENUM(name) name,
  PIA_NODE_KINDS(PIA_NODE_ENUM)
#undef PIA_NODE_ENUM
};

const char *nodeKindName(NodeKind kind);

struct Node;
using NodePtr = std::unique_ptr<Node>;

struct Node {
  NodeKind kind = NodeKind::None;
  std::string text;
  // LetItem/LetIn: "rec", "meta" or "rec meta". Name: "prelude" or
  // "toplevel" when a quote made it (docs/meta.md, "Hygiene").
  std::string flags;
  SourceLoc loc;
  std::vector<NodePtr> kids;
  // The comments attached to this node, in source order (ADR 0029). They
  // are Comment nodes, and no pass but the meta engine looks at them.
  std::vector<NodePtr> comments;

  Node *add(NodePtr kid) {
    kids.push_back(std::move(kid));
    return kids.back().get();
  }
};

NodePtr makeNode(NodeKind kind, SourceLoc loc, std::string text = "");

// A deep copy of `node`.
NodePtr clone(const Node &node);

// Whether a top-level `let` defines a concept (ADR 0034):
// `let meta C (t : type) : concept = sig ... end`.
bool isConceptItem(const Node &item);

// Whether a top-level `let meta` is a type-level metaprogram (ADR 0035):
// its parameters are all types and it returns a type or a bool, as in
// `let meta widen (t : type) : type = ...`. Such metaprograms outlive
// expansion, since types and `where` predicates call them.
bool isTypeLevelMetaItem(const Node &item);

// Writes the tree as an indented S-expression, one node per line. This is the
// `piac --dump-ast` format that the golden tests compare. With `comments`,
// each node's comments come first among its children (`--comments`).
void dump(std::ostream &os, const Node &node, bool comments = false);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_SYNTAX_H
