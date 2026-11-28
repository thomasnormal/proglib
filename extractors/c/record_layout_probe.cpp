// Parser-native record-layout observations for the C extractor.
//
// ASTRecordLayout is Clang's own target/profile answer.  This probe reports
// it verbatim and emits a parser traversal ordinal for each complete
// RecordDecl. The extractor joins that ordinal to the AST node identity,
// never by a type spelling or a fabricated address. It is an observation
// instrument; it does not
// make aggregate semantics live in Lean.
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <sstream>
#include <cstdint>
#include <string>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "record layout probe supports only Clang 21.1.8"
#endif
#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "record layout probe supports only LLVM 21.1.8"
#endif

namespace {

std::string nodeId(const void *node) {
  std::ostringstream text;
  text << "0x" << std::hex << reinterpret_cast<uintptr_t>(node);
  return text.str();
}

std::optional<llvm::json::Value> boundExprJson(const clang::Expr *expression) {
  if (!expression) return std::nullopt;
  const auto type = expression->getType().getAsString();
  if (const auto *literal = llvm::dyn_cast<clang::IntegerLiteral>(expression)) {
    llvm::SmallString<32> value;
    literal->getValue().toString(value, 10, false, false);
    return llvm::json::Object{{"kind", "IntegerLiteral"}, {"value", value.str().str()},
                              {"type", type}};
  }
  if (const auto *ref = llvm::dyn_cast<clang::DeclRefExpr>(expression)) {
    return llvm::json::Object{{"kind", "DeclRefExpr"}, {"decl_id", nodeId(ref->getDecl())},
                              {"name", ref->getDecl()->getNameAsString()},
                              {"decl_kind", ref->getDecl()->getDeclKindName()}, {"type", type}};
  }
  if (const auto *binary = llvm::dyn_cast<clang::BinaryOperator>(expression)) {
    auto lhs = boundExprJson(binary->getLHS());
    auto rhs = boundExprJson(binary->getRHS());
    if (!lhs || !rhs) return std::nullopt;
    return llvm::json::Object{{"kind", "BinaryOperator"}, {"op", binary->getOpcodeStr().str()},
                              {"lhs", std::move(*lhs)}, {"rhs", std::move(*rhs)}, {"type", type}};
  }
  if (const auto *unary = llvm::dyn_cast<clang::UnaryOperator>(expression)) {
    auto sub = boundExprJson(unary->getSubExpr());
    if (!sub) return std::nullopt;
    return llvm::json::Object{{"kind", "UnaryOperator"}, {"op", clang::UnaryOperator::getOpcodeStr(unary->getOpcode()).str()},
                              {"sub", std::move(*sub)}, {"postfix", unary->isPostfix()}, {"type", type}};
  }
  if (const auto *paren = llvm::dyn_cast<clang::ParenExpr>(expression)) {
    auto sub = boundExprJson(paren->getSubExpr());
    if (!sub) return std::nullopt;
    return llvm::json::Object{{"kind", "ParenExpr"}, {"sub", std::move(*sub)}, {"type", type}};
  }
  if (const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(expression)) {
    auto sub = boundExprJson(cast->getSubExpr());
    if (!sub) return std::nullopt;
    return llvm::json::Object{{"kind", "ImplicitCastExpr"},
                              {"cast", cast->getCastKindName()}, {"sub", std::move(*sub)}, {"type", type}};
  }
  return std::nullopt;
}

class Visitor : public clang::RecursiveASTVisitor<Visitor> {
public:
  llvm::json::Array records;
  const clang::ASTContext *context = nullptr;
  unsigned recordIndex = 0;

  void emitTypeLayout(clang::QualType type, clang::SourceLocation beginLoc,
                      clang::SourceLocation endLoc) {
    const auto &sources = context->getSourceManager();
    const auto loc = sources.getExpansionLoc(beginLoc);
    if (!sources.isWrittenInMainFile(loc) || type->isIncompleteType()) return;
    const auto end = clang::Lexer::getLocForEndOfToken(
        sources.getExpansionLoc(endLoc), 0, sources, clang::LangOptions());
    const auto beginOffset = sources.getFileOffset(loc);
    const auto finish = end.isValid() ? sources.getFileOffset(end) : beginOffset;
    const auto size = context->getTypeSizeInChars(type);
    const auto align = context->getTypeAlignInChars(type);
    llvm::json::Object item{
        {"kind", "TypeLayout"},
        {"offset", static_cast<int64_t>(beginOffset)},
        {"token_length", static_cast<int64_t>(finish - beginOffset)},
        {"type", type.getAsString()},
        {"size_bytes", static_cast<int64_t>(size.getQuantity())},
        {"alignment_bytes", static_cast<int64_t>(align.getQuantity())}};
    if (type->isPointerType()) {
      const auto pointee = type->getPointeeType();
      if (!pointee->isIncompleteType()) {
        const auto pointeeSize = context->getTypeSizeInChars(pointee);
        item["pointee_size_bytes"] =
            static_cast<int64_t>(pointeeSize.getQuantity());
      }
    }
    if (type->isArrayType()) {
      const auto element = type->getArrayElementTypeNoTypeQual();
      if (!element->isIncompleteType()) {
        const auto elementSize = context->getTypeSizeInChars(element);
        item["element_type"] = clang::QualType(element, 0).getAsString();
        item["element_size_bytes"] =
            static_cast<int64_t>(elementSize.getQuantity());
      }
      if (const auto *variable = llvm::dyn_cast<clang::VariableArrayType>(
              type.getTypePtrOrNull())) {
        const auto *boundExpr = variable->getSizeExpr()->IgnoreParenImpCasts();
        if (auto boundPayload = boundExprJson(boundExpr))
          item["bound_expr"] = std::move(*boundPayload);
        if (const auto *bound = llvm::dyn_cast<clang::DeclRefExpr>(boundExpr)) {
          const auto boundLoc = sources.getExpansionLoc(bound->getDecl()->getBeginLoc());
          if (sources.isWrittenInMainFile(boundLoc))
            item["bound_decl_offset"] =
                static_cast<int64_t>(sources.getFileOffset(boundLoc));
        }
      }
    }
    records.push_back(std::move(item));
  }

  bool VisitRecordDecl(clang::RecordDecl *record) {
    const unsigned recordOrdinal = recordIndex++;
    if (!record->isCompleteDefinition()) return true;
    const auto &sources = context->getSourceManager();
    const auto loc = sources.getExpansionLoc(record->getBeginLoc());
    if (!sources.isWrittenInMainFile(loc)) return true;
    const auto end_loc = clang::Lexer::getLocForEndOfToken(
        sources.getExpansionLoc(record->getEndLoc()), 0, sources,
        clang::LangOptions());
    const auto begin = sources.getFileOffset(loc);
    const auto finish = end_loc.isValid() ? sources.getFileOffset(end_loc) : begin;
    const auto &layout = context->getASTRecordLayout(record);
    llvm::json::Array fields;
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      llvm::json::Object item{
          {"name", field->getNameAsString()},
          {"offset_bits", static_cast<int64_t>(layout.getFieldOffset(index))},
          {"bitfield", field->isBitField()},
          {"incomplete_array", field->getType()->isIncompleteArrayType()}};
      if (field->isBitField()) {
        if (const auto *width = field->getBitWidth()) {
          const llvm::APSInt value = width->EvaluateKnownConstInt(*context);
          item["width_bits"] = static_cast<int64_t>(value.getZExtValue());
        }
      }
      fields.push_back(std::move(item));
      ++index;
    }
    llvm::json::Object item{
        {"kind", "RecordLayout"},
        {"record_index", static_cast<int64_t>(recordOrdinal)},
        {"offset", static_cast<int64_t>(begin)},
        {"token_length", static_cast<int64_t>(finish - begin)},
        {"name", record->getNameAsString()},
        {"tag_kind", record->isUnion() ? "union" : "struct"},
        {"size_bytes", static_cast<int64_t>(layout.getSize().getQuantity())},
        {"alignment_bytes", static_cast<int64_t>(layout.getAlignment().getQuantity())},
        {"fields", std::move(fields)}};
    records.push_back(std::move(item));
    return true;
  }

  bool VisitEnumConstantDecl(clang::EnumConstantDecl *constant) {
    const auto &sources = context->getSourceManager();
    const auto loc = sources.getExpansionLoc(constant->getBeginLoc());
    if (!sources.isWrittenInMainFile(loc)) return true;
    records.push_back(llvm::json::Object{
        {"kind", "EnumValue"},
        {"offset", static_cast<int64_t>(sources.getFileOffset(loc))},
        {"value", static_cast<int64_t>(constant->getInitVal().getSExtValue())}});
    return true;
  }

  bool VisitVarDecl(clang::VarDecl *decl) {
    if (decl->isImplicit()) return true;
    emitTypeLayout(decl->getType(), decl->getBeginLoc(), decl->getEndLoc());
    return true;
  }

  bool VisitCompoundLiteralExpr(clang::CompoundLiteralExpr *expr) {
    emitTypeLayout(expr->getType(), expr->getBeginLoc(), expr->getEndLoc());
    return true;
  }
};

class Consumer : public clang::ASTConsumer {
public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    Visitor visitor;
    visitor.context = &context;
    if (!visitor.TraverseDecl(context.getTranslationUnitDecl())) return;
    llvm::outs() << llvm::json::Value(std::move(visitor.records)) << "\n";
  }
};

class Action : public clang::PluginASTAction {
public:
  std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
      clang::CompilerInstance &, llvm::StringRef) override {
    return std::make_unique<Consumer>();
  }
  bool ParseArgs(const clang::CompilerInstance &compiler,
                 const std::vector<std::string> &args) override {
    if (!args.empty()) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "record layout probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    const std::string expected = "clang version " CLANG_VERSION_STRING;
    const std::string runtime = clang::getClangFullVersion();
    if (runtime != expected &&
        !llvm::StringRef(runtime).starts_with(expected + " ")) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "record layout probe header/runtime version mismatch");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    return true;
  }
  ActionType getActionType() override { return ReplaceAction; }
};

clang::FrontendPluginRegistry::Add<Action> registration(
    "lean-c-record-layout", "emit parser-native record layouts");
} // namespace
