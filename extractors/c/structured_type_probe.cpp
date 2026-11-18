// Parser-native Clang QualType projection for the C envelope.
//
// The probe walks Clang's QualType tree and emits source offsets for the
// declaration occurrence and for record/enum/typedef identities.  The Python
// extractor joins those offsets to the declaration IDs already canonicalized
// from the same AST dump.  No type spelling is parsed in either layer.
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

#include <optional>
#include <string>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "structured type probe supports only Clang 21.1.8"
#endif
#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "structured type probe supports only LLVM 21.1.8"
#endif

namespace {

using Json = llvm::json::Value;

std::optional<int64_t> sourceOffset(const clang::Decl *decl,
                                    const clang::SourceManager &sources) {
  if (!decl) return std::nullopt;
  const auto location = sources.getExpansionLoc(decl->getBeginLoc());
  if (location.isInvalid() || !sources.isWrittenInMainFile(location))
    return std::nullopt;
  return static_cast<int64_t>(sources.getFileOffset(location));
}

std::optional<Json> typeTree(clang::QualType qualified,
                             const clang::ASTContext &context,
                             unsigned depth);

std::optional<Json> declarationType(const clang::Decl *decl,
                                    const clang::ASTContext &context) {
  const auto offset = sourceOffset(decl->getCanonicalDecl(),
                                   context.getSourceManager());
  if (!offset) return std::nullopt;
  return llvm::json::Object{{"offset", *offset},
                            {"kind", decl->getDeclKindName()}};
}

std::optional<Json> unqualifiedType(clang::QualType unqualified,
                                    const clang::ASTContext &context,
                                    unsigned depth) {
  const clang::Type *type = unqualified.getTypePtrOrNull();
  if (!type) return std::nullopt;
  if (const auto *elaborated = llvm::dyn_cast<clang::ElaboratedType>(type))
    return typeTree(elaborated->getNamedType(), context, depth + 1);
  if (const auto *builtin = llvm::dyn_cast<clang::BuiltinType>(type)) {
    std::optional<std::string> name;
    switch (builtin->getKind()) {
    case clang::BuiltinType::Void: name = "void"; break;
    case clang::BuiltinType::Bool: name = "_Bool"; break;
    case clang::BuiltinType::Char_S:
    case clang::BuiltinType::Char_U: name = "char"; break;
    case clang::BuiltinType::SChar: name = "signed char"; break;
    case clang::BuiltinType::UChar: name = "unsigned char"; break;
    case clang::BuiltinType::Short: name = "short"; break;
    case clang::BuiltinType::UShort: name = "unsigned short"; break;
    case clang::BuiltinType::Int: name = "int"; break;
    case clang::BuiltinType::UInt: name = "unsigned int"; break;
    case clang::BuiltinType::Long: name = "long"; break;
    case clang::BuiltinType::ULong: name = "unsigned long"; break;
    case clang::BuiltinType::LongLong: name = "long long"; break;
    case clang::BuiltinType::ULongLong: name = "unsigned long long"; break;
    default: break;
    }
    if (!name) return std::nullopt;
    return llvm::json::Object{
        {"kind", "builtin"},
        {"name", *name}};
  }
  if (const auto *pointer = llvm::dyn_cast<clang::PointerType>(type)) {
    auto pointee = typeTree(pointer->getPointeeType(), context, depth + 1);
    if (!pointee) return std::nullopt;
    return llvm::json::Object{{"kind", "pointer"},
                              {"pointee", std::move(*pointee)}};
  }
  if (const auto *array = llvm::dyn_cast<clang::ConstantArrayType>(type)) {
    auto element = typeTree(array->getElementType(), context, depth + 1);
    if (!element) return std::nullopt;
    return llvm::json::Object{{"kind", "array"},
                              {"element", std::move(*element)},
                              {"extent", static_cast<int64_t>(array->getSize().getZExtValue())}};
  }
  if (const auto *array = llvm::dyn_cast<clang::IncompleteArrayType>(type)) {
    auto element = typeTree(array->getElementType(), context, depth + 1);
    if (!element) return std::nullopt;
    return llvm::json::Object{{"kind", "array"},
                              {"element", std::move(*element)}, {"extent", nullptr}};
  }
  if (const auto *function = llvm::dyn_cast<clang::FunctionProtoType>(type)) {
    // C's ordinary calling convention and parameter ABI are represented by
    // the function node itself. Exotic C++ method/exception/effect metadata
    // remains an explicit refusal below.
    auto result = typeTree(function->getReturnType(), context, depth + 1);
    if (!result) return std::nullopt;
    llvm::json::Array parameters;
    for (const clang::QualType parameter : function->param_types()) {
      auto item = typeTree(parameter, context, depth + 1);
      if (!item) return std::nullopt;
      parameters.push_back(std::move(*item));
    }
    return llvm::json::Object{{"kind", "function"},
                              {"result", std::move(*result)},
                              {"parameters", std::move(parameters)},
                              {"variadic", function->isVariadic()}};
  }
  if (const auto *record = llvm::dyn_cast<clang::RecordType>(type)) {
    auto declaration = declarationType(record->getDecl(), context);
    if (!declaration) return std::nullopt;
    return llvm::json::Object{{"kind", "record"},
                              {"declaration", std::move(*declaration)}};
  }
  if (const auto *enumeration = llvm::dyn_cast<clang::EnumType>(type)) {
    auto declaration = declarationType(enumeration->getDecl(), context);
    if (!declaration) return std::nullopt;
    return llvm::json::Object{{"kind", "enumeration"},
                              {"declaration", std::move(*declaration)}};
  }
  if (const auto *alias = llvm::dyn_cast<clang::TypedefType>(type)) {
    auto declaration = declarationType(alias->getDecl(), context);
    if (!declaration) return std::nullopt;
    return llvm::json::Object{{"kind", "typedef"},
                              {"declaration", std::move(*declaration)}};
  }
  return std::nullopt;
}

std::optional<Json> typeTree(clang::QualType qualified,
                             const clang::ASTContext &context,
                             unsigned depth) {
  if (qualified.isNull() || depth > 128) return std::nullopt;
  const auto qualifiers = qualified.getLocalQualifiers();
  if (qualifiers.hasRestrict() || qualifiers.hasAddressSpace()) return std::nullopt;
  auto body = unqualifiedType(qualified.getLocalUnqualifiedType(), context, depth);
  if (!body) return std::nullopt;
  if (!qualifiers.hasConst() && !qualifiers.hasVolatile()) return body;
  return llvm::json::Object{{"kind", "qualified"},
                            {"const", qualifiers.hasConst()},
                            {"volatile", qualifiers.hasVolatile()},
                            {"base", std::move(*body)}};
}

class Visitor : public clang::RecursiveASTVisitor<Visitor> {
public:
  llvm::json::Array rows;
  const clang::ASTContext *context = nullptr;

  bool VisitDecl(clang::Decl *decl) {
    if (decl->isImplicit()) return true;
    const auto occurrence = sourceOffset(decl, context->getSourceManager());
    if (!occurrence) return true;
    clang::QualType qualified;
    if (const auto *value = llvm::dyn_cast<clang::ValueDecl>(decl))
      qualified = value->getType();
    else if (const auto *alias = llvm::dyn_cast<clang::TypedefDecl>(decl))
      qualified = alias->getUnderlyingType();
    else
      return true;
    auto tree = typeTree(qualified, *context, 0);
    if (!tree) {
      rows.push_back(llvm::json::Object{
          {"kind", "StructuredType"}, {"offset", *occurrence},
          {"type", llvm::json::Object{{"kind", "unsupported"},
                                       {"reason", "unrepresented Clang QualType"}}}});
      return true;
    }
    rows.push_back(llvm::json::Object{{"kind", "StructuredType"},
                                      {"offset", *occurrence},
                                      {"type", std::move(*tree)}});
    return true;
  }
};

class Consumer : public clang::ASTConsumer {
public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    Visitor visitor;
    visitor.context = &context;
    visitor.TraverseDecl(context.getTranslationUnitDecl());
    llvm::outs() << llvm::json::Value(std::move(visitor.rows)) << "\n";
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
          "structured type probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    return true;
  }
  ActionType getActionType() override { return ReplaceAction; }
};

clang::FrontendPluginRegistry::Add<Action> registration(
    "lean-c-structured-types", "emit parser-native C QualType trees");
} // namespace
