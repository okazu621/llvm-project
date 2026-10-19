//===--- UMLDumper.cpp - Compact UML diagram extraction from the AST ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implements -ast-dump-uml=json: a compact, single-line JSON dump containing
// only the information required to build UML class and sequence diagrams.
//
// Unlike the full AST dump (-ast-dump=json), this dumper never serializes
// system header AST nodes: only declarations whose location lies inside the
// configured project root are emitted, and function bodies are walked only
// for project definitions. The emitted objects mirror the data model of the
// c-cpp-playground design analysis (extractClasses /
// extractSequenceFunctions) so the TypeScript side can consume them directly
// and defer the pure-computation steps (relation resolution, diagram
// merging, expandSequenceFunction).
//
// The output is written as one line of JSON to the selected output stream
// (stdout by default), which keeps Emscripten/WASM stdout reads to a single
// chunk instead of millions of line-at-a-time reads.
//
//===----------------------------------------------------------------------===//

#include "clang/Frontend/ASTConsumers.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclFriend.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/LambdaCapture.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/ExprConcepts.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/TemplateBase.h"
#include "clang/AST/TypeBase.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Specifiers.h"
#include "clang/Lex/Lexer.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/Regex.h"
#include <memory>
#include <string>
#include <utility>

using namespace clang;

namespace {

/// Mirrors UmlAnnotations / parseAnnotations of
/// c-cpp-playground (src/design-analysis/annotations.ts).
struct UmlAnno {
  std::string Role, Label, Note, Group, UseCase, Members, Relation,
      Multiplicity, SourceMultiplicity, Message, ReturnLabel;
  bool HasRole = false, Ignore = false, Entry = false, Expand = false,
      Collapse = false, Async = false;

  bool empty() const {
    return !HasRole && Label.empty() && Note.empty() && Group.empty() &&
           UseCase.empty() && !Ignore && Members.empty() && Relation.empty() &&
           Multiplicity.empty() && SourceMultiplicity.empty() && !Entry &&
           Message.empty() && !Expand && !Collapse && !Async &&
           ReturnLabel.empty();
  }

  /// Apply the fields set in O on top of this (later wins, as in TS spread).
  void apply(const UmlAnno &O) {
    if (O.HasRole) {
      Role = O.Role;
      HasRole = true;
    }
    if (!O.Label.empty())
      Label = O.Label;
    if (!O.Note.empty())
      Note = O.Note;
    if (!O.Group.empty())
      Group = O.Group;
    if (!O.UseCase.empty())
      UseCase = O.UseCase;
    if (O.Ignore)
      Ignore = true;
    if (!O.Members.empty())
      Members = O.Members;
    if (!O.Relation.empty())
      Relation = O.Relation;
    if (!O.Multiplicity.empty())
      Multiplicity = O.Multiplicity;
    if (!O.SourceMultiplicity.empty())
      SourceMultiplicity = O.SourceMultiplicity;
    if (O.Entry)
      Entry = true;
    if (!O.Message.empty())
      Message = O.Message;
    if (O.Expand)
      Expand = true;
    if (O.Collapse)
      Collapse = true;
    if (O.Async)
      Async = true;
    if (!O.ReturnLabel.empty())
      ReturnLabel = O.ReturnLabel;
  }

  llvm::json::Object toJson() const {
    llvm::json::Object O;
    if (HasRole)
      O["role"] = Role;
    if (!Label.empty())
      O["label"] = Label;
    if (!Note.empty())
      O["note"] = Note;
    if (!Group.empty())
      O["group"] = Group;
    if (!UseCase.empty())
      O["usecase"] = UseCase;
    if (Ignore)
      O["ignore"] = true;
    if (!Members.empty())
      O["members"] = Members;
    if (!Relation.empty())
    O["relation"] = Relation;
    if (!Multiplicity.empty())
      O["multiplicity"] = Multiplicity;
    if (!SourceMultiplicity.empty())
      O["sourceMultiplicity"] = SourceMultiplicity;
    if (Entry)
      O["entry"] = true;
    if (!Message.empty())
      O["message"] = Message;
    if (Expand)
      O["expand"] = true;
    if (Collapse)
      O["collapse"] = true;
    if (Async)
      O["messageKind"] = "async";
    if (!ReturnLabel.empty())
      O["returnLabel"] = ReturnLabel;
    return O;
  }

  /// Mirrors parseAnnotations of the TypeScript annotation model.
  static UmlAnno parseValues(const llvm::SmallVectorImpl<std::string> &Values) {
    UmlAnno R;
    static const llvm::Regex MultRe("^([*]|[0-9]+([.][.]([0-9]+|[*]))?)$");
    for (const std::string &V : Values) {
      if (V.rfind("uml::", 0) != 0)
        continue;
      size_t Equal = V.find('=');
      std::string Key =
          V.substr(5, Equal == std::string::npos ? std::string::npos
                                                  : Equal - 5);
      std::string Text =
          Equal == std::string::npos ? "" : V.substr(Equal + 1);
      bool IsRole = Key == "boundary" || Key == "control" || Key == "entity" ||
                    Key == "actor";
      bool IsRelation = Key == "association" || Key == "aggregation" ||
                        Key == "composition" || Key == "dependency" ||
                        Key == "realization";
      if (IsRole && Equal == std::string::npos) {
        R.Role = Key;
        R.HasRole = true;
      } else if (IsRelation && Equal == std::string::npos) {
        R.Relation = Key;
      } else if ((Key == "label" || Key == "note" || Key == "group" ||
                  Key == "usecase" || Key == "message") &&
                 Equal != std::string::npos) {
        if (Key == "label")
          R.Label = Text;
        else if (Key == "note")
          R.Note = Text;
        else if (Key == "group")
          R.Group = Text;
        else if (Key == "usecase")
          R.UseCase = Text;
        else
          R.Message = Text;
      } else if ((Key == "ignore" || Key == "entry" || Key == "expand" ||
                  Key == "collapse") &&
                 Equal == std::string::npos) {
        if (Key == "ignore")
          R.Ignore = true;
        else if (Key == "entry")
          R.Entry = true;
        else if (Key == "expand")
          R.Expand = true;
        else
          R.Collapse = true;
      } else if (Key == "members" && (Text == "none" || Text == "public")) {
        R.Members = Text;
      } else if ((Key == "multiplicity" || Key == "source_multiplicity") &&
                 MultRe.match(llvm::StringRef(Text))) {
        if (Key == "multiplicity")
          R.Multiplicity = Text;
        else
          R.SourceMultiplicity = Text;
      } else if (Key == "async" && Equal == std::string::npos) {
        R.Async = true;
      } else if (Key == "return" && Equal != std::string::npos) {
        R.ReturnLabel = Text;
      }
    }
    return R;
  }
};

/// The raw annotation values of a decl, one per AnnotateAttr (the first
/// string argument of each clang::annotate attribute).
///
/// The new attribute framework stores clang::annotate attributes through
/// Decl::specific_attrs (not the legacy Decl::attrs() array), so we iterate
/// that range. Each AnnotateAttr carries one or more string literals: the
/// leading string in getAnnotation() and the remaining ones in args(). The
/// TypeScript reference reads only the leading string of each attribute, so
/// we mirror that to keep behavior identical.
///
/// The reference attaches node.uml when ANY valid annotate value was read
/// (and sets {} when none of the uml:: keys are recognized), so the result
/// carries the uml-value along with an explicit presence flag.
struct DeclUml {
  UmlAnno Anno;
  bool Has = false;
};
DeclUml annotationsOf(const Decl *D) {
  llvm::SmallVector<std::string, 4> Values;
  for (const auto *An : D->specific_attrs<AnnotateAttr>()) {
    std::string S(An->getAnnotation());
    for (const auto *Arg : An->args())
      if (const auto *SL = llvm::dyn_cast<StringLiteral>(Arg))
        S += SL->getString().str();
    if (!S.empty())
      Values.push_back(std::move(S));
  }
  DeclUml R;
  R.Anno = UmlAnno::parseValues(Values);
  R.Has = !Values.empty();
  return R;
}

/// Mirrors normalize() of the TypeScript reader.
std::string normalizePath(const std::string &P) {
  llvm::SmallVector<std::string, 8> Parts;
  llvm::SmallVector<llvm::StringRef, 8> Pieces;
  llvm::StringRef(P).split(Pieces, "/");
  for (llvm::StringRef Part : Pieces) {
    if (Part == "..") {
      if (!Parts.empty())
        Parts.pop_back();
    } else if (!Part.empty() && Part != ".") {
      Parts.push_back(Part.str());
    }
  }
  std::string R = "/";
  for (size_t I = 0, E = Parts.size(); I != E; ++I) {
    if (I)
      R.push_back('/');
    R += Parts[I];
  }
  return R;
}

/// Mirrors compact() of the TypeScript sequence model.
std::string compact(const std::string &In, size_t Max = 140) {
  std::string R;
  R.reserve(In.size());
  bool PendingSpace = false;
  for (unsigned char Ch : In) {
    if (Ch == ' ' || Ch == '\t' || Ch == '\n' || Ch == '\r' || Ch == '\v' ||
        Ch == '\f') {
      PendingSpace = true;
      continue;
    }
    if (PendingSpace && !R.empty())
      R.push_back(' ');
    PendingSpace = false;
    R.push_back(Ch);
  }
  size_t B = R.find_first_not_of(" \t\n\r\v\f");
  if (B == std::string::npos)
    return "";
  size_t E = R.find_last_not_of(" \t\n\r\f");
  R = R.substr(B, E - B + 1);
  if (R.size() > Max)
    R = R.substr(0, Max - 1) + "\u2026";
  return R;
}

std::string joinScope(const llvm::SmallVectorImpl<std::string> &V,
                      llvm::StringRef Sep) {
  std::string R;
  for (size_t I = 0, E = V.size(); I != E; ++I) {
    if (I)
      R += Sep;
    R += V[I];
  }
  return R;
}

/// Copy a context vector and append one entry.
llvm::SmallVector<std::string, 4>
ctxAppend(const llvm::SmallVector<std::string, 4> &V, const std::string &S) {
  llvm::SmallVector<std::string, 4> R = V;
  R.push_back(S);
  return R;
}

// The JSON AST records the node's exact kind; the TypeScript pipeline
// treats `method` as `kind !== "FunctionDecl"`. CXXMethodDecl /
// constructors / destructors are FunctionDecl *subclasses*, so
// isa<FunctionDecl> cannot distinguish them; compare the exact DeclKind
// instead (a free FunctionDecl has DeclKind::Function).
static bool isMethod(const FunctionDecl *FD) {
  return FD->getDeclKind() != clang::Decl::Function;
}

static std::string accessToString(AccessSpecifier AS) {
  switch (AS) {
  case AS_public:
    return "public";
  case AS_protected:
    return "protected";
  case AS_private:
    return "private";
  case AS_none:
    return "none";
  }
  return "none";
}

static std::string tagUsedString(const RecordDecl *RD) {
  switch (RD->getTagKind()) {
  case TagTypeKind::Class:
    return "class";
  case TagTypeKind::Struct:
    return "struct";
  case TagTypeKind::Union:
    return "union";
  default:
    return "class";
  }
}

struct FnInfo {
  const FunctionDecl *F = nullptr;
  llvm::SmallVector<std::string, 4> Scope;
  std::string Owner, File;
  UmlAnno Anno;
  bool HasAnno = false;
};

struct Participant {
  std::string Id, Name, Type;
  UmlAnno Uml = {};
  bool HasUml = false;
};

struct CallRec {
  std::string To, Label, File, Kind, Callee;
  bool HasCallee = false;
  llvm::SmallVector<std::string, 4> Context;
  unsigned Line = 0;
  bool Indirect = false;
  UmlAnno Uml;
  bool HasUml = false;
  llvm::SmallVector<Participant, 4> Arguments;
};

/// Per-definition state for the body walker.
struct WalkState {
  const FnInfo *Def = nullptr;
  Participant Caller;
  llvm::SmallVector<CallRec, 16> Calls;
  llvm::SmallVector<Participant, 16> Participants;
  llvm::StringMap<unsigned> ParticipantIndex;
};

class UMLDumperConsumer : public ASTConsumer {
public:
  UMLDumperConsumer(raw_ostream &OS, std::string Root, std::string MainFile)
      : OS(OS), Root(std::move(Root)), MainFile(std::move(MainFile)) {}

  void HandleTranslationUnit(ASTContext &C) override {
    Ctx = &C;
    SM = &C.getSourceManager();
    Policy = &C.getPrintingPolicy();

    CurrentFile = normalizePath(MainFile);
    indexDecl(Ctx->getTranslationUnitDecl(), {});

    CurrentFile = normalizePath(MainFile);
    collectDecl(Ctx->getTranslationUnitDecl(), {}, "", CurrentFile);

    CurrentFile = normalizePath(MainFile);
    visitClasses(Ctx->getTranslationUnitDecl(), {}, {}, CurrentFile);

    for (unsigned I : DefinitionIndices) {
      const FnInfo &Def = Functions[I];
      const auto RIt = Roles.find(Def.Owner.c_str());
      if (Def.Anno.Ignore || (RIt != Roles.end() && RIt->second.Ignore))
        continue;
      makeFunctionObject(Def);
    }

    llvm::json::OStream J(OS, /*Indent=*/0);
    J.objectBegin();
    J.attribute("v", 1);
    J.attribute("root", Root);
    J.attributeArray("classes", [this, &J] {
      for (auto &Obj : ClassObjects)
        J.value(llvm::json::Value(std::move(Obj)));
    });
    J.attributeArray("functions", [this, &J] {
      for (auto &Obj : FunctionObjects)
        J.value(llvm::json::Value(std::move(Obj)));
    });
    J.objectEnd();
    OS.flush();
  }

private:
  raw_ostream &OS;
  /// Normalized project root with a trailing '/'.
  std::string Root;
  std::string MainFile;
  std::string CurrentFile;
  const ASTContext *Ctx = nullptr;
  const SourceManager *SM = nullptr;
  const PrintingPolicy *Policy = nullptr;

  llvm::DenseMap<const NamedDecl *, llvm::SmallVector<std::string, 4>>
      Contexts;
  llvm::StringMap<UmlAnno> Roles;
  /// Mirrors the TypeScript `declarations` map, which is keyed by the JSON
  /// node id. The same FunctionDecl can be registered several times (the
  /// JSON AST re-emits shadowed declarations under their UsingShadowDecl),
  /// and the last registration wins; insertion order is preserved.
  llvm::DenseMap<const FunctionDecl *, size_t> Declarations;
  llvm::SmallVector<const FunctionDecl *, 64> DeclarationOrder;
  llvm::DenseMap<const ValueDecl *, std::string> ObjectIds;
  llvm::SmallVector<FnInfo, 32> Functions;
  llvm::SmallVector<unsigned, 32> DefinitionIndices;
  llvm::SmallVector<llvm::json::Object, 16> ClassObjects;
  llvm::SmallVector<llvm::json::Object, 16> FunctionObjects;

  bool isInProject(const std::string &File) const {
    return File.rfind(Root, 0) == 0;
  }

  std::string typeOf(QualType T) const {
    if (T.isNull())
      return "";
    std::string Q = T.getAsString(*Policy);
    QualType D = T.getDesugaredType(*Ctx);
    if (D != T) {
      std::string DS = D.getAsString(*Policy);
      if (DS != Q)
        return DS;
    }
    return Q;
  }

  std::string typeOf(const ValueDecl *D) const { return typeOf(D->getType()); }

  std::string objectId(const ValueDecl *D) const {
    const auto It = ObjectIds.find(D);
    if (It != ObjectIds.end())
      return It->second;
    return "0x" +
           llvm::utohexstr(reinterpret_cast<uint64_t>(D),
                           /*NoLeadingZeros=*/true);
  }

  /// Resolve a location to (file, offset, line) via its expansion location.
  void locInfo(SourceLocation L, std::string &File, unsigned &Offset,
               unsigned &Line) const {
    if (L.isInvalid())
      return;
    SourceLocation E = SM->getExpansionLoc(L);
    if (E.isInvalid())
      return;
    auto [FID, Off] = SM->getDecomposedLoc(E);
    File = std::string(SM->getBufferName(E));
    Offset = Off;
    Line = SM->getLineNumber(FID, Off);
  }

  std::string sourceText(SourceRange R) const {
    if (R.isInvalid())
      return {};
    SourceLocation B = SM->getExpansionLoc(R.getBegin());
    SourceLocation E = SM->getExpansionLoc(R.getEnd());
    if (B.isInvalid() || E.isInvalid())
      return {};
    auto [FIDB, OffB] = SM->getDecomposedLoc(B);
    auto [FIDE, OffE] = SM->getDecomposedLoc(E);
    if (FIDB != FIDE)
      return {};
    unsigned Tok = Lexer::MeasureTokenLength(E, *SM, Ctx->getLangOpts());
    StringRef Buf = SM->getBufferData(FIDB);
    if (OffB > Buf.size() || OffE + Tok > Buf.size())
      return {};
    return Buf.substr(OffB, OffE - OffB + Tok).str();
  }

  std::string mangleName(const FunctionDecl *F) const {
    if (F->isTemplated())
      return {};
    ASTNameGenerator Gen(const_cast<ASTContext &>(*Ctx));
    return Gen.getName(F);
  }

  /// Mirrors keyOf() of the TypeScript sequence model.
  std::string keyOf(const FnInfo &I) const {
    std::string Key = mangleName(I.F);
    if (Key.empty()) {
      llvm::SmallVector<std::string, 4> Scope = I.Scope;
      Scope.push_back(I.F->getNameAsString());
      Key = joinScope(Scope, "::") + ":" + typeOf(I.F);
    }
    // The TypeScript reference appends the file only for a declaration whose
    // JSON kind is exactly "FunctionDecl" (not a method) and that is static.
    if (!isMethod(I.F) && I.F->getStorageClass() == SC_Static)
      Key += ":" + I.File;
    return Key;
  }

  static bool isRecord(const Decl *D) {
    return llvm::isa<CXXRecordDecl>(D) || llvm::isa<RecordDecl>(D) ||
           llvm::isa<ClassTemplateSpecializationDecl>(D);
  }

  /// True when a template specialization is also a member of its lexical
  /// DeclContext's list (as explicit instantiations are), so it would be
  /// visited once more through the enclosing DeclContext; the JSON AST only
  /// exposes such a node there.
  static bool lexicallyReachable(const Decl *S) {
    const DeclContext *LC = S->getLexicalDeclContext();
    return LC && LC->containsDecl(const_cast<Decl *>(S));
  }

  static std::string visibilityOf(const std::string &Access) {
    if (Access == "public")
      return "+";
    if (Access == "protected")
      return "#";
    return "\u2212";
  }

  static void pushObjects(llvm::json::Array &A,
                          llvm::SmallVectorImpl<llvm::json::Object> &V) {
    for (auto &X : V)
      A.push_back(llvm::json::Value(std::move(X)));
  }

  //===------------------------------------------------------------------===//
  // Index pass: contexts and roles (mirrors indexContexts of the
  // TypeScript sequence model).
  //===------------------------------------------------------------------===//

  void indexDecl(const Decl *D, const llvm::SmallVector<std::string, 4> &Scope) {
    if (!D)
      return;
    llvm::SmallVector<std::string, 4> Next = Scope;
    if (const auto *NSD = llvm::dyn_cast<NamespaceDecl>(D))
      Next.push_back(NSD->getIdentifier() ? NSD->getNameAsString()
                                          : std::string("(anonymous)"));
    const NamedDecl *ND = llvm::dyn_cast<NamedDecl>(D);
    if (ND && isRecord(D) && ND->getDeclName() && !D->isImplicit()) {
      // The TypeScript reference drops TemplateArgument nodes during AST
      // pruning, so specialization names never carry template arguments.
      Next.push_back(ND->getNameAsString());
    }
    if (isRecord(D)) {
      DeclUml U = annotationsOf(D);
      if (U.Has)
        Roles[joinScope(Next, "::").c_str()] = std::move(U.Anno);
    }
    if (ND && (llvm::isa<NamespaceDecl>(D) || isRecord(D)))
      Contexts[ND] = Next;

    if (const auto *DC = llvm::dyn_cast<DeclContext>(D))
      for (const Decl *C : DC->decls())
        indexDecl(C, Next);
    if (const auto *CTD = llvm::dyn_cast<ClassTemplateDecl>(D)) {
      indexDecl(CTD->getTemplatedDecl(), Next);
      for (const Decl *S : CTD->specializations())
        if (!lexicallyReachable(S))
          indexDecl(S, Next);
    }
    if (const auto *FTD = llvm::dyn_cast<FunctionTemplateDecl>(D)) {
      indexDecl(FTD->getTemplatedDecl(), Next);
      for (const Decl *S : FTD->specializations())
        indexDecl(S, Next);
    }
    // Bodies and initializers are only needed to find nested project
    // declarations; skip them in system files.
    if (const auto *FD = llvm::dyn_cast<FunctionDecl>(D))
      if (FD->getBody() && isInProject(fileOf(D, CurrentFile)))
        indexStmt(FD->getBody(), Next);
    if (const auto *VD = llvm::dyn_cast<VarDecl>(D))
      if (VD->getInit() && isInProject(fileOf(D, CurrentFile)))
        indexStmt(VD->getInit(), Next);
  }

  void indexStmt(const Stmt *S, const llvm::SmallVector<std::string, 4> &Scope) {
    if (!S)
      return;
    if (const auto *DS = llvm::dyn_cast<DeclStmt>(S)) {
      for (const Decl *D : DS->decls())
        indexDecl(D, Scope);
      return;
    }
    if (const auto *LE = llvm::dyn_cast<LambdaExpr>(S)) {
      if (LE->getBody())
        indexStmt(LE->getBody(), Scope);
      return;
    }
    for (const Stmt *C : S->children())
      indexStmt(C, Scope);
  }

  std::string fileOf(const Decl *D, const std::string &Fallback) const {
    std::string File;
    unsigned Off, Line;
    locInfo(D->getLocation(), File, Off, Line);
    // Normalize (resolve "..") so isInProject comparisons are stable,
    // mirroring normalize() of the TypeScript pipeline.
    return File.empty() ? Fallback : normalizePath(File);
  }

  //===------------------------------------------------------------------===//
  // Collect pass: declarations, object ids, definitions (mirrors collect()
  // of the TypeScript sequence model).
  //===------------------------------------------------------------------===//

  void collectDecl(const Decl *D, const llvm::SmallVector<std::string, 4> &Scope,
                   const std::string &Owner, std::string &CurrentFile) {
    if (!D)
      return;
    // A friend function declaration is not reachable through its class's
    // DeclContext, but the JSON AST re-emits it as a child of the FriendDecl
    // with the lexical scope in effect, so register it here.
    if (const auto *FRD = llvm::dyn_cast<FriendDecl>(D)) {
      const NamedDecl *Friend =
          llvm::dyn_cast_or_null<NamedDecl>(FRD->getFriendDecl());
      if (Friend && (llvm::isa<FunctionDecl>(Friend) ||
                     llvm::isa<FunctionTemplateDecl>(Friend)))
        collectDecl(Friend, Scope, Owner, CurrentFile);
      return;
    }
    std::string File = fileOf(D, CurrentFile);
    if (!File.empty())
      CurrentFile = File;

    // Register object ids for all named value declarations (the TypeScript
    // reference registers VarDecl / ParmVarDecl / FieldDecl). Note that
    // FieldDecl is not a VarDecl in Clang, so it is handled separately.
    if (const auto *VD = llvm::dyn_cast<VarDecl>(D)) {
      std::string VFile;
      unsigned Off, Line;
      locInfo(VD->getLocation(), VFile, Off, Line);
      if (!VFile.empty() && isInProject(VFile))
        ObjectIds[VD] = VFile + ":" + llvm::utostr(Off) + ":" +
                        VD->getNameAsString();
    } else if (const auto *FD = llvm::dyn_cast<FieldDecl>(D)) {
      std::string VFile;
      unsigned Off, Line;
      locInfo(FD->getLocation(), VFile, Off, Line);
      if (!VFile.empty() && isInProject(VFile))
        ObjectIds[FD] = VFile + ":" + llvm::utostr(Off) + ":" +
                        FD->getNameAsString();
    }

    llvm::SmallVector<std::string, 4> NextScope = Scope;
    std::string NextOwner = Owner;
    if (llvm::isa<NamespaceDecl>(D) || (isRecord(D) && !D->isImplicit())) {
      const NamedDecl *ND = llvm::dyn_cast<NamedDecl>(D);
      const auto It = ND ? Contexts.find(ND) : Contexts.end();
      if (It != Contexts.end())
        NextScope = It->second;
      if (isRecord(D))
        NextOwner = joinScope(NextScope, "::");
    }

    if (const auto *FD = llvm::dyn_cast<FunctionDecl>(D)) {
      // Register parameters so their object ids are source-based (the
      // TypeScript reference uses the same objectId scheme for ParmVarDecl).
      for (const auto *P : FD->parameters()) {
        std::string PFile;
        unsigned POff, PLine;
        locInfo(P->getLocation(), PFile, POff, PLine);
        if (!PFile.empty() && isInProject(PFile))
          ObjectIds[P] = PFile + ":" + llvm::utostr(POff) + ":" +
                         P->getNameAsString();
      }
      if (FD->getDeclName()) {
        bool Method = isMethod(FD);
        // For a method, the owning scope is the record itself even for an
        // out-of-line definition (whose DeclContext is the enclosing
        // namespace); the JSON parentDeclContextId points at the record.
        const NamedDecl *ParentND =
            Method
                ? llvm::cast<CXXMethodDecl>(FD)->getParent()
                : llvm::dyn_cast<NamedDecl>(FD->getDeclContext());
        llvm::SmallVector<std::string, 4> Resolved = Scope;
        const auto It = ParentND ? Contexts.find(ParentND) : Contexts.end();
        if (It != Contexts.end())
          Resolved = It->second;
        FnInfo Info;
        Info.F = FD;
        Info.Scope = Resolved;
        Info.Owner =
            Method ? joinScope(Resolved, "::") : std::string();
        DeclUml DU = annotationsOf(FD);
        Info.Anno = DU.Anno;
        Info.HasAnno = DU.Has;
        Info.File = CurrentFile;
        size_t Index = Functions.size();
        Functions.push_back(std::move(Info));
        // The TypeScript pipeline re-registers the same declaration on every
        // JSON node that carries it (lexically, out-of-line, and inside a
        // UsingShadowDecl) and the last registration wins for call lookups.
        const auto DIt = Declarations.find(FD);
        if (DIt == Declarations.end()) {
          Declarations[FD] = Index;
          DeclarationOrder.push_back(FD);
        } else
          DIt->second = Index;
        // A method declared in the class and defined out-of-line appears as
        // two FunctionDecl nodes linked through previousDecl; the shared
        // body is attached only to the definition node. Mirror the
        // TypeScript pipeline, which treats a node as a definition when its
        // own inner contains the CompoundStmt/CXXTryStmt. Using
        // doesThisDeclarationHaveABody() (instead of getBody(), which
        // follows the redeclaration chain) prevents emitting both the
        // in-class declaration and the out-of-line definition when they
        // live in the same file.
        if (FD->doesThisDeclarationHaveABody() && !FD->isImplicit() &&
            hasFunctionBody(FD) && isInProject(Functions.back().File))
          DefinitionIndices.push_back((unsigned)Index);
        llvm::SmallVector<std::string, 4> Local = Resolved;
        Local.push_back(FD->getNameAsString() + "()");
        NextScope = std::move(Local);
      }
    }
    // A UsingShadowDecl re-emits its shadowed declaration as a child node in
    // the JSON AST, so the walk registers the declaration again with the
    // scope of the using declaration itself (contexts lookups fail there),
    // and mirrors map-insertion last-write-wins semantics.
    if (const auto *USD = llvm::dyn_cast<UsingShadowDecl>(D)) {
      const FunctionDecl *Shadowed =
          llvm::dyn_cast_or_null<FunctionDecl>(USD->getTargetDecl());
      if (Shadowed && Shadowed->getDeclName()) {
        bool ShadowMethod = isMethod(Shadowed);
        llvm::SmallVector<std::string, 4> Resolved = Scope;
        FnInfo Info;
        Info.F = Shadowed;
        Info.Scope = Resolved;
        Info.Owner = ShadowMethod ? joinScope(Resolved, "::") : std::string();
        DeclUml DU = annotationsOf(Shadowed);
        Info.Anno = DU.Anno;
        Info.HasAnno = DU.Has;
        Info.File = CurrentFile;
        size_t Index = Functions.size();
        Functions.push_back(std::move(Info));
        const auto DIt = Declarations.find(Shadowed);
        if (DIt == Declarations.end()) {
          Declarations[Shadowed] = Index;
          DeclarationOrder.push_back(Shadowed);
        } else
          DIt->second = Index;
        if (Shadowed->doesThisDeclarationHaveABody() &&
            !Shadowed->isImplicit() && hasFunctionBody(Shadowed) &&
            isInProject(Functions.back().File))
          DefinitionIndices.push_back((unsigned)Index);
      }
    }

    // A FunctionDecl is not descended through DeclContext::decls(): local
    // declarations inside a body are visited once via the body statement
    // walk below (and would otherwise be registered twice).
    if (const auto *DC = llvm::dyn_cast<DeclContext>(D))
      if (!llvm::isa<FunctionDecl>(D))
        for (const Decl *C : DC->decls()) {
          // A lambda's closure record is a member of the enclosing
          // function's DeclContext, but the TypeScript reference (JSON AST)
          // only exposes it under the LambdaExpr, which is never descended.
          if (const auto *CRD = llvm::dyn_cast<CXXRecordDecl>(C))
            if (CRD->isLambda())
              continue;
          collectDecl(C, NextScope, NextOwner, CurrentFile);
        }
    if (const auto *CTD = llvm::dyn_cast<ClassTemplateDecl>(D)) {
      collectDecl(CTD->getTemplatedDecl(), NextScope, NextOwner, CurrentFile);
      for (const Decl *S : CTD->specializations())
        if (!lexicallyReachable(S))
          collectDecl(S, NextScope, NextOwner, CurrentFile);
    }
    if (const auto *FTD = llvm::dyn_cast<FunctionTemplateDecl>(D)) {
      collectDecl(FTD->getTemplatedDecl(), NextScope, NextOwner, CurrentFile);
      for (const Decl *S : FTD->specializations())
        collectDecl(S, NextScope, NextOwner, CurrentFile);
    }
    if (const auto *FD = llvm::dyn_cast<FunctionDecl>(D))
      if (FD->getBody() && isInProject(CurrentFile))
        collectStmt(FD->getBody(), NextScope, NextOwner, CurrentFile);
    if (const auto *VD = llvm::dyn_cast<VarDecl>(D))
      if (VD->getInit() && isInProject(CurrentFile))
        collectStmt(VD->getInit(), NextScope, NextOwner, CurrentFile);
  }

  void collectStmt(const Stmt *S, const llvm::SmallVector<std::string, 4> &Scope,
                   const std::string &Owner, std::string &CurrentFile) {
    if (!S)
      return;
    if (const auto *DS = llvm::dyn_cast<DeclStmt>(S)) {
      for (const Decl *D : DS->decls())
        collectDecl(D, Scope, Owner, CurrentFile);
      return;
    }
    // Mirror collect() of the TypeScript pipeline: never descend into a
    // lambda, so a lambda's closure (operator()/destructor) and local
    // declarations inside it are not collected as functions.
    if (llvm::isa<LambdaExpr>(S))
      return;
    for (const Stmt *C : S->children())
      collectStmt(C, Scope, Owner, CurrentFile);
  }

  static bool hasFunctionBody(const FunctionDecl *FD) {
    const Stmt *B = FD->getBody();
    return B && (llvm::isa<CompoundStmt>(B) || llvm::isa<CXXTryStmt>(B));
  }

  //===------------------------------------------------------------------===//
  // Class extraction (mirrors extractClasses of the TypeScript class model).
  //===------------------------------------------------------------------===//

  void visitClasses(const Decl *D,
                    const llvm::SmallVector<std::string, 4> &Scope,
                    const llvm::SmallVector<std::string, 4> &Params,
                    std::string &CurrentFile) {
    if (!D)
      return;
    std::string File = fileOf(D, CurrentFile);
    if (!File.empty())
      CurrentFile = File;

    llvm::SmallVector<std::string, 4> Next = Scope;
    // The TypeScript reference resets the inherited template parameter list
    // at every node and only fills it again on the ClassTemplateDecl that
    // declares the parameters.
    llvm::SmallVector<std::string, 4> NextParams;
    if (const auto *CTD = llvm::dyn_cast<ClassTemplateDecl>(D))
      for (const NamedDecl *P : CTD->getTemplateParameters()->asArray())
        NextParams.push_back(
            P->getDeclName().isEmpty() ? std::string("?")
                                       : P->getNameAsString());
    if (const auto *NSD = llvm::dyn_cast<NamespaceDecl>(D))
      Next.push_back(NSD->getIdentifier() ? NSD->getNameAsString()
                                          : "(anonymous:" + File + ")");
    const NamedDecl *ND = llvm::dyn_cast<NamedDecl>(D);
    if (ND && isRecord(D) && ND->getDeclName() && !D->isImplicit()) {
      // A class template specialization's own arguments are pruned out of
      // the JSON AST, so specialization names never carry template
      // arguments; the template pattern uses the captured parameter names.
      llvm::SmallVector<std::string, 4> Args =
          llvm::isa<ClassTemplateSpecializationDecl>(D)
              ? llvm::SmallVector<std::string, 4>{}
              : Params;
      std::string Name = ND->getNameAsString();
      if (!Args.empty())
        Name += "<" + joinScope(Args, ", ") + ">";
      Next.push_back(Name);
      if (llvm::cast<RecordDecl>(D)->isCompleteDefinition() &&
          isInProject(CurrentFile)) {
        recordClass(llvm::cast<RecordDecl>(D), Scope, Next, CurrentFile);
      }
    }
    if (const auto *FD = llvm::dyn_cast<FunctionDecl>(D))
      if (FD->getDeclName())
        Next.push_back(FD->getNameAsString() + "()");

    // A FunctionDecl is not descended through DeclContext::decls(): local
    // declarations inside a body are visited once via the body statement
    // walk below and would otherwise be recorded twice.
    if (const auto *DC = llvm::dyn_cast<DeclContext>(D))
      if (!llvm::isa<FunctionDecl>(D))
        for (const Decl *C : DC->decls())
          visitClasses(C, Next, NextParams, CurrentFile);
    const auto *FDPtr = llvm::dyn_cast<FunctionDecl>(D);
    if (FDPtr) {
      // Default argument expressions can declare nothing, but mirror the
      // JSON-tree recursion of the TypeScript reference anyway.
      for (const ParmVarDecl *P : FDPtr->parameters())
        if (P->getInit() && isInProject(CurrentFile))
          visitClassesStmt(P->getInit(), Next, NextParams, CurrentFile);
      if (FDPtr->getBody() && isInProject(CurrentFile))
        visitClassesStmt(FDPtr->getBody(), Next, NextParams, CurrentFile);
    }
    if (const auto *CTD = llvm::dyn_cast<ClassTemplateDecl>(D)) {
      visitClasses(CTD->getTemplatedDecl(), Next, NextParams, CurrentFile);
      for (const Decl *S : CTD->specializations())
        if (!lexicallyReachable(S))
          visitClasses(S, Next, NextParams, CurrentFile);
    }
    if (const auto *FTD = llvm::dyn_cast<FunctionTemplateDecl>(D)) {
      visitClasses(FTD->getTemplatedDecl(), Next, NextParams, CurrentFile);
      for (const Decl *S : FTD->specializations())
        visitClasses(S, Next, NextParams, CurrentFile);
    }
    if (const auto *VD = llvm::dyn_cast<VarDecl>(D))
      if (VD->getInit() && isInProject(CurrentFile))
        visitClassesStmt(VD->getInit(), Next, NextParams, CurrentFile);
  }

  void visitClassesStmt(const Stmt *S,
                        const llvm::SmallVector<std::string, 4> &Scope,
                        const llvm::SmallVector<std::string, 4> &Params,
                        std::string &CurrentFile) {
    if (!S)
      return;
    if (const auto *DS = llvm::dyn_cast<DeclStmt>(S)) {
      for (const Decl *D : DS->decls())
        visitClasses(D, Scope, Params, CurrentFile);
      return;
    }
    if (const auto *LE = llvm::dyn_cast<LambdaExpr>(S)) {
      if (LE->getBody())
        visitClassesStmt(LE->getBody(), Scope, Params, CurrentFile);
      return;
    }
    for (const Stmt *C : S->children())
      visitClassesStmt(C, Scope, Params, CurrentFile);
  }

  void recordClass(const RecordDecl *RD,
                   const llvm::SmallVector<std::string, 4> &Scope,
                   const llvm::SmallVector<std::string, 4> &Next,
                   const std::string &File) {
    std::string Access =
        tagUsedString(RD) == "class" ? "private" : "public";
    llvm::SmallVector<llvm::json::Object, 16> Fields;
    llvm::SmallVector<llvm::json::Object, 16> Methods;

    auto addField = [&](const ValueDecl *DD, bool Static) {
      DeclUml MU = annotationsOf(DD);
      if (MU.Anno.Ignore)
        return;
      std::string TypeQual = DD->getType().getAsString(*Policy);
      std::string Type = typeOf(DD);
      std::string Name = DD->getNameAsString().empty()
                             ? std::string("(anonymous)")
                             : DD->getNameAsString();
      llvm::json::Object O;
      O["name"] = Name;
      O["type"] = Type;
      O["access"] = Access;
      if (Static)
        O["static"] = true;
      std::string Text = visibilityOf(Access) + " " +
                         (MU.Anno.Label.empty() ? Name : MU.Anno.Label) + " : " +
                         (TypeQual.empty() ? "?" : TypeQual) +
                         (Static ? " {static}" : "");
      O["text"] = Text;
      if (MU.Has)
        O["uml"] = MU.Anno.toJson();
      Fields.push_back(std::move(O));
    };

    auto addMethod = [&](const FunctionDecl *FD) {
      if (FD->isImplicit() || !FD->getDeclName())
        return;
      DeclUml MU = annotationsOf(FD);
      if (MU.Anno.Ignore)
        return;
      std::string Sig = FD->getType().getAsString(*Policy);
      llvm::SmallVector<std::string, 8> Params2;
      for (const auto *P : FD->parameters()) {
        std::string PName = P->getNameAsString();
        Params2.push_back((PName.empty() ? "" : PName + ": ") +
                          P->getType().getAsString(*Policy));
      }
      if (Sig.find("...") != std::string::npos)
        Params2.push_back("...");
      bool Constructor = llvm::isa<CXXConstructorDecl>(FD) ||
                         llvm::isa<CXXDestructorDecl>(FD);
      size_t Paren = Sig.find("(");
      std::string ReturnType =
          Sig.substr(0, Paren == std::string::npos ? 0 : Paren);
      {
        size_t B = ReturnType.find_first_not_of(" \t\n\r\v\f");
        size_t E = ReturnType.find_last_not_of(" \t\n\r\f");
        ReturnType = B == std::string::npos ? std::string()
                                            : ReturnType.substr(B, E - B + 1);
      }
      std::string Quals;
      if (Sig.find(") const volatile") != std::string::npos)
        Quals = "const volatile";
      else if (Sig.find(") const") != std::string::npos)
        Quals = "const";
      else if (Sig.find(") volatile") != std::string::npos)
        Quals = "volatile";
      bool Static = FD->getStorageClass() == SC_Static;
      llvm::json::Object O;
      O["name"] = FD->getNameAsString();
      O["access"] = Access;
      O["type"] = typeOf(FD);
      std::string Text = visibilityOf(Access) + " " +
                         (MU.Anno.Label.empty() ? FD->getNameAsString()
                                           : MU.Anno.Label) +
                         "(" + joinScope(Params2, ", ") + ")" +
                         (Constructor ? ""
                                      : " : " +
                                            (ReturnType.empty() ? "?"
                                                               : ReturnType)) +
                         (Quals.empty() ? "" : " {" + Quals + "}") +
                         (Static ? " {static}" : "") +
                         (FD->isPureVirtual() ? " {abstract}" : "");
      O["text"] = Text;
      if (MU.Has)
        O["uml"] = MU.Anno.toJson();
      Methods.push_back(std::move(O));
    };

    for (const Decl *M : RD->decls()) {
      if (const auto *ASD = llvm::dyn_cast<AccessSpecDecl>(M)) {
        Access = accessToString(ASD->getAccess());
      } else if (const auto *FD = llvm::dyn_cast<FieldDecl>(M)) {
        addField(FD, /*Static=*/false);
      } else if (const auto *VD = llvm::dyn_cast<VarDecl>(M)) {
        if (VD->getStorageClass() == SC_Static)
          addField(VD, /*Static=*/true);
      } else if (llvm::isa<CXXMethodDecl>(M) || llvm::isa<CXXConstructorDecl>(M) ||
                 llvm::isa<CXXDestructorDecl>(M) ||
                 llvm::isa<CXXConversionDecl>(M)) {
        addMethod(llvm::cast<FunctionDecl>(M));
      } else if (const auto *FTD = llvm::dyn_cast<FunctionTemplateDecl>(M)) {
        if (const auto *MD =
                llvm::dyn_cast<CXXMethodDecl>(FTD->getTemplatedDecl()))
          addMethod(MD);
        // The JSON AST exposes instantiated member-function-template
        // specializations as additional CXXMethodDecl children of the
        // FunctionTemplateDecl; the TypeScript class model emits each of
        // them, so match that here.
        for (const Decl *S : FTD->specializations())
          if (const auto *MD = llvm::dyn_cast<CXXMethodDecl>(S))
            addMethod(MD);
      }
    }

    llvm::SmallVector<std::string, 8> Bases;
    if (const auto *CRD = llvm::dyn_cast<CXXRecordDecl>(RD))
      for (const auto &BS : CRD->bases())
        Bases.push_back(typeOf(BS.getType()));

    std::string Qualified = joinScope(Next, "::");
    DeclUml U = annotationsOf(RD);

    std::string LocFile;
    unsigned Off, Line;
    locInfo(RD->getLocation(), LocFile, Off, Line);
    if (LocFile.empty())
      LocFile = File;

    llvm::json::Object O;
    O["id"] = LocFile + ":" + llvm::utostr(Off) + ":" + Qualified;
    O["name"] = Next.back();
    O["qualifiedName"] = Qualified;
    O["scope"] = llvm::json::Array(Scope);
    O["file"] = LocFile.substr(Root.size());
    O["kind"] = tagUsedString(RD);
    O["abstract"] =
        llvm::isa<CXXRecordDecl>(RD) && llvm::cast<CXXRecordDecl>(RD)->isAbstract();
    {
      llvm::json::Array F;
      pushObjects(F, Fields);
      O["fields"] = std::move(F);
    }
    {
      llvm::json::Array M;
      pushObjects(M, Methods);
      O["methods"] = std::move(M);
    }
    {
      llvm::json::Array B;
      for (const std::string &X : Bases)
        B.push_back(llvm::json::Value(X));
      O["bases"] = std::move(B);
    }
    if (U.Has)
      O["uml"] = U.Anno.toJson();
    ClassObjects.push_back(std::move(O));
  }

  //===------------------------------------------------------------------===//
  // Sequence extraction (mirrors extractSequenceFunctions of the
  // TypeScript sequence model).
  //===------------------------------------------------------------------===//

  /// Strip reference/pointer symbols and top-level qualifier keywords,
  /// mirroring metadataType() of the TypeScript sequence model.
  std::string metadataType(const std::string &In) const {
    std::string S = In;
    size_t Pos;
    while ((Pos = S.find('&')) != std::string::npos)
      S.erase(Pos, 1);
    while ((Pos = S.find('*')) != std::string::npos)
      S.erase(Pos, 1);
    static const char *const Kws[] = {"const", "volatile", "class", "struct"};
    std::string Out;
    size_t Start = 0;
    for (size_t I = 0; I <= S.size(); ++I) {
      if (I == S.size() || S[I] == ' ' || S[I] == '\t' || S[I] == '\n' ||
          S[I] == '\r') {
        std::string Tok = S.substr(Start, I - Start);
        Start = I + 1;
        if (Tok.empty())
          continue;
        bool IsKw = false;
        for (const char *K : Kws)
          if (Tok == K) {
            IsKw = true;
            break;
          }
        if (!IsKw)
          Out += (Out.empty() ? "" : " ") + Tok;
      }
    }
    return compact(Out);
  }

  /// Mirrors metadata() of the TypeScript sequence model; a non-null result
  /// (even an empty {}) means the role lookup hit, mirroring JS truthiness
  /// of a registered annotation object.
  const UmlAnno *metadata(const std::string &Type,
                    const llvm::SmallVector<std::string, 4> &Scope) const {
    std::string Clean = metadataType(Type);
    for (size_t I = Scope.size(); ; --I) {
      llvm::SmallVector<std::string, 4> V(Scope.begin(), Scope.begin() + I);
      V.push_back(Clean);
      const auto It = Roles.find(joinScope(V, "::").c_str());
      if (It != Roles.end())
        return &It->second;
      if (I == 0)
        break;
    }
    return nullptr;
  }

  static const Expr *unwrap(const Expr *E) {
    for (;;) {
      const Expr *C = nullptr;
      if (const auto *IC = llvm::dyn_cast<ImplicitCastExpr>(E))
        C = IC->getSubExpr();
      else if (const auto *P = llvm::dyn_cast<ParenExpr>(E))
        C = P->getSubExpr();
      else if (const auto *C2 = llvm::dyn_cast<ExprWithCleanups>(E))
        C = C2->getSubExpr();
      else if (const auto *M = llvm::dyn_cast<MaterializeTemporaryExpr>(E))
        C = M->getSubExpr();
      else if (const auto *B = llvm::dyn_cast<CXXBindTemporaryExpr>(E))
        C = B->getSubExpr();
      else if (const auto *C3 = llvm::dyn_cast<CStyleCastExpr>(E))
        C = C3->getSubExpr();
      else if (const auto *C4 = llvm::dyn_cast<CXXStaticCastExpr>(E))
        C = C4->getSubExpr();
      else if (const auto *C5 = llvm::dyn_cast<CXXDynamicCastExpr>(E))
        C = C5->getSubExpr();
      else if (const auto *C6 = llvm::dyn_cast<CXXConstCastExpr>(E))
        C = C6->getSubExpr();
      else if (const auto *C7 = llvm::dyn_cast<CXXFunctionalCastExpr>(E))
        C = C7->getSubExpr();
      if (!C)
        break;
      E = C;
    }
    return E;
  }

  std::string conditionText(const Stmt *S) const {
    std::string Src = sourceText(S->getSourceRange());
    size_t Start = Src.find('(');
    if (Start == std::string::npos)
      return S->getStmtClassName();
    int Depth = 0;
    for (size_t I = Start; I < Src.size(); ++I) {
      if (Src[I] == '(')
        ++Depth;
      if (Src[I] == ')' && --Depth == 0)
        return compact(Src.substr(0, I + 1), 100);
    }
    return compact(Src.substr(0, 100));
  }

  Participant makeExpression(const Expr *E, const Participant &Caller) const {
    const Expr *N = unwrap(E);
    if (!N || llvm::isa<CXXThisExpr>(N))
      return Caller;
    if (const auto *DRE = llvm::dyn_cast<DeclRefExpr>(N)) {
      const ValueDecl *RD = DRE->getDecl();
      return {"object:" + objectId(RD),
              RD ? RD->getNameAsString()
                : (sourceText(N->getSourceRange()).empty()
                       ? std::string("object")
                       : sourceText(N->getSourceRange())),
              (RD ? typeOf(RD) : std::string()).empty()
                  ? typeOf(N->getType())
                  : typeOf(RD)};
    }
    if (const auto *ME = llvm::dyn_cast<MemberExpr>(N)) {
      Participant Base = makeExpression(ME->getBase(), Caller);
      const ValueDecl *MD = ME->getMemberDecl();
      std::string Id = Base.Id + "." + objectId(MD);
      std::string Name = (Base.Id == Caller.Id ? std::string("this")
                                               : Base.Name) +
                         "." + (MD ? MD->getNameAsString() : std::string());
      return {std::move(Id), std::move(Name), typeOf(N->getType())};
    }
    if (const auto *UO = llvm::dyn_cast<UnaryOperator>(N))
      if (UO->getOpcode() == UO_Deref || UO->getOpcode() == UO_AddrOf)
        return makeExpression(UO->getSubExpr(), Caller);
    std::string T = sourceText(N->getSourceRange());
    std::string Type = typeOf(N->getType());
    return {"expression:" + compact(T) + ":" + Type,
            compact(T, 60).empty() ? std::string("(\u5f0f)") : compact(T, 60),
            Type};
  }

  const FnInfo *findFunction(const Decl *RefDecl) const {
    // RefDecl may be null (the callee is neither a DeclRefExpr nor a member
    // expression), so use the null-safe form; dyn_cast is UB on null.
    const FunctionDecl *FD = llvm::dyn_cast_or_null<FunctionDecl>(RefDecl);
    if (!FD)
      return nullptr;
    const auto It = Declarations.find(FD);
    if (It == Declarations.end())
      return nullptr;
    return &Functions[It->second];
  }

  /// Mirrors the constructor lookup of the TypeScript sequence model, which
  /// searches its `declarations` map by owner/type instead of trusting the
  /// AST link. Notably, an element `new T[n]` produces a CXXConstructExpr
  /// whose type is `T[]`, so the owner never matches and the reference emits
  /// no constructor (hence no `callee`).
  const FunctionDecl *resolveConstructor(const CXXConstructExpr *CCE,
                                         const WalkState &W) const {
    const FunctionDecl *Ctor = CCE->getConstructor();
    if (!Ctor)
      return nullptr;
    const std::string ExprType = typeOf(CCE->getType());
    const std::string CtorType =
        CCE->getConstructor()->getType().getAsString(*Policy);
    auto Candidate = [&](bool DropLast) {
      llvm::SmallVector<std::string, 4> V(W.Def->Scope.begin(),
                                          W.Def->Scope.end());
      if (DropLast && !V.empty())
        V.pop_back();
      V.push_back(ExprType);
      return joinScope(V, "::");
    };
    // Mirror the TypeScript pipeline: first match in declaration-map
    // insertion order among constructors (last registration of each
    // declaration wins), then a fallback candidate set.
    const auto *First = [&]() -> const FnInfo * {
      for (const FunctionDecl *DD : DeclarationOrder) {
        const auto DIt = Declarations.find(DD);
        if (DIt == Declarations.end())
          continue;
        const FnInfo &CI = Functions[DIt->second];
        if (!llvm::isa<CXXConstructorDecl>(CI.F))
          continue;
        if (CI.Owner == Candidate(/*DropLast=*/true) && typeOf(CI.F) == CtorType)
          return &CI;
      }
      return nullptr;
    }();
    if (First)
      return First->F;
    const auto *Fallback = [&]() -> const FnInfo * {
      for (const FunctionDecl *DD : DeclarationOrder) {
        const auto DIt = Declarations.find(DD);
        if (DIt == Declarations.end())
          continue;
        const FnInfo &CI = Functions[DIt->second];
        if (!llvm::isa<CXXConstructorDecl>(CI.F))
          continue;
        if ((CI.Owner == ExprType ||
             CI.Owner == Candidate(/*DropLast=*/false)) &&
            typeOf(CI.F) == CtorType)
          return &CI;
      }
      return nullptr;
    }();
    return Fallback ? Fallback->F : nullptr;
  }

  void addCall(const Participant &To, const std::string &Label,
               const llvm::SmallVector<std::string, 4> &Context,
               SourceRange Pos, bool Indirect, const Decl *RefDecl,
               const llvm::SmallVectorImpl<const Expr *> &Args,
               WalkState &W) const {
    const FnInfo *Decl = findFunction(RefDecl);
    UmlAnno Annotations = Decl ? Decl->Anno : UmlAnno();
    bool AnnotationsPresent = Decl && Decl->HasAnno;
    const UmlAnno *Role = metadata(To.Type == "\u30af\u30e9\u30b9 / static" ? To.Name
                                                                 : To.Type,
                            W.Def->Scope);
    if (Annotations.Ignore || (Role && Role->Ignore))
      return;
    Participant Recipient = To;
    // Mirror the TypeScript reference, which always overwrites the
    // recipient's uml with `role ?? (to.type === "関数" ? annotations :
    // undefined)` and never keeps a previously stored value.
    if (Role) {
      Recipient.Uml = *Role;
      Recipient.HasUml = true;
    } else if (To.Type == "\u95a2\u6570" && AnnotationsPresent) {
      Recipient.Uml = Annotations;
      Recipient.HasUml = true;
    } else {
      Recipient.Uml = UmlAnno();
      Recipient.HasUml = false;
    }
    const auto PIt = W.ParticipantIndex.find(To.Id.c_str());
    if (PIt == W.ParticipantIndex.end()) {
      W.ParticipantIndex[To.Id.c_str()] = W.Participants.size();
      W.Participants.push_back(Recipient);
    } else
      W.Participants[PIt->second] = Recipient;

    CallRec C;
    C.To = To.Id;
    C.Label = compact(Annotations.Message.empty() ? Label : Annotations.Message);
    C.Context = Context;
    std::string File;
    unsigned Off, Line;
    locInfo(Pos.getBegin(), File, Off, Line);
    C.Line = Line;
    C.Indirect = Indirect;
    C.Kind = Annotations.Async ? "async" : "sync";
    if (Decl && isInProject(Decl->File)) {
      C.Callee = keyOf(*Decl);
      C.HasCallee = true;
    }
    C.Uml = Annotations;
    C.HasUml = AnnotationsPresent;
    C.File = W.Def->File.substr(Root.size());
    for (const Expr *A : Args)
      C.Arguments.push_back(makeExpression(A, W.Caller));
    W.Calls.push_back(std::move(C));
  }

  /// Recursively walk a function definition body, mirroring walk() of the
  /// TypeScript sequence model.
  void walkStmt(const Stmt *S, llvm::SmallVector<std::string, 4> Context,
                const Participant *Constructed, WalkState &W) const {
    if (!S)
      return;

    if (const auto *LE = llvm::dyn_cast<LambdaExpr>(S)) {
      // Capture initializers run here; the lambda's deferred body does not.
      for (const auto &I : LE->capture_inits())
        if (I)
          walkStmt(I, Context, nullptr, W);
      return;
    }
    if (llvm::isa<UnaryExprOrTypeTraitExpr>(S) ||
        llvm::isa<CXXNoexceptExpr>(S) || llvm::isa<TypeTraitExpr>(S) ||
        llvm::isa<RequiresExpr>(S))
      return;
    if (const auto *IS = llvm::dyn_cast<IfStmt>(S)) {
      if (IS->hasInitStorage())
        walkStmt(IS->getInit(), Context, Constructed, W);
      if (IS->hasVarStorage()) {
        const VarDecl *Var = IS->getConditionVariable();
        if (Var) {
          Participant Object{"object:" + objectId(Var),
                             Var->getNameAsString().empty()
                                 ? std::string("(local)")
                                 : Var->getNameAsString(),
                             typeOf(Var)};
          if (Var->getInit())
            walkStmt(Var->getInit(), Context, &Object, W);
        }
      }
      // Mirror the TypeScript walk: the condition is walked with the plain
      // context, while the then/else bodies carry a single "cond / then"
      // (or "cond / else") context entry.
      std::string Cond = conditionText(IS);
      walkStmt(IS->getCond(), Context, Constructed, W);
      walkStmt(IS->getThen(), ctxAppend(Context, Cond + " / then"), Constructed,
               W);
      if (IS->getElse())
        walkStmt(IS->getElse(), ctxAppend(Context, Cond + " / else"),
                 Constructed, W);
      return;
    }
    if (const auto *FRS = llvm::dyn_cast<CXXForRangeStmt>(S)) {
      // The init statement and the range expression run once, before the
      // loop; the loop variable's initializer and the hidden
      // begin()/end()/!=/++ calls are not attributed.
      if (FRS->getInit())
        walkStmt(FRS->getInit(), Context, Constructed, W);
      if (const DeclStmt *RS = FRS->getRangeStmt())
        if (const VarDecl *RD = llvm::dyn_cast<VarDecl>(RS->getSingleDecl()))
          if (RD->getInit())
            walkStmt(RD->getInit(), Context, Constructed, W);
      if (FRS->getBody())
        walkStmt(FRS->getBody(), ctxAppend(Context, conditionText(FRS)),
                 Constructed, W);
      return;
    }
    if (llvm::isa<ForStmt>(S) || llvm::isa<WhileStmt>(S) ||
        llvm::isa<DoStmt>(S) || llvm::isa<SwitchStmt>(S) ||
        llvm::isa<ConditionalOperator>(S) || llvm::isa<CaseStmt>(S) ||
        llvm::isa<DefaultStmt>(S) || llvm::isa<CXXCatchStmt>(S)) {
      std::string Label;
      if (llvm::isa<ConditionalOperator>(S))
        Label = std::string("\u6761\u4ef6\u6f14\u7b97\u5b50 ?:");
      else if (llvm::isa<CaseStmt>(S) || llvm::isa<DefaultStmt>(S)) {
        std::string Src = sourceText(S->getSourceRange());
        size_t Colon = Src.find(':');
        Label = compact(Src.substr(0, Colon == std::string::npos
                                         ? Src.size()
                                         : Colon));
      } else
        Label = conditionText(S);
      for (const Stmt *C : S->children())
        walkStmt(C, ctxAppend(Context, Label), Constructed, W);
      return;
    }
    if (const auto *BO = llvm::dyn_cast<BinaryOperator>(S))
      if (BO->getOpcode() == BO_LAnd || BO->getOpcode() == BO_LOr) {
        walkStmt(BO->getLHS(), Context, Constructed, W);
        walkStmt(BO->getRHS(),
                 ctxAppend(Context,
                           std::string("\u77ed\u7d61\u8a55\u4fa1 ") +
                               std::string(BO->getOpcodeStr().str())),
                 Constructed, W);
        return;
      }
    if (const auto *DE = llvm::dyn_cast<CXXDefaultInitExpr>(S)) {
      // The default initializer's subexpression is not a generic Stmt
      // child; walk it explicitly so the inner construction is recorded.
      if (DE->getExpr())
        walkStmt(DE->getExpr(), Context, Constructed, W);
      return;
    }
    if (const auto *DA = llvm::dyn_cast<CXXDefaultArgExpr>(S)) {
      // children() is empty for a default argument expression; the JSON AST
      // exposes the wrapped expression as a child that the walk descends
      // into, so nested calls in the default run in the caller's context.
      if (DA->getExpr())
        walkStmt(DA->getExpr(), Context, Constructed, W);
      return;
    }
    if (const auto *DS = llvm::dyn_cast<DeclStmt>(S)) {
      // Pass a copy each iteration: a moved-from Context would drop the
      // enclosing context for every declaration after the first.
      for (const Decl *D : DS->decls())
        walkDeclOf(D, Context, Constructed, W);
      return;
    }
    if (const auto *CE = llvm::dyn_cast<CallExpr>(S)) {
      handleCall(CE, std::move(Context), W);
      return;
    }
    if (const auto *CCE = llvm::dyn_cast<CXXConstructExpr>(S)) {
      for (const Stmt *C : CCE->children())
        walkStmt(C, Context, nullptr, W);
      Participant Target;
      if (Constructed)
        Target = *Constructed;
      else {
        std::string File;
        unsigned Off, Line;
        locInfo(CCE->getSourceRange().getBegin(), File, Off, Line);
        std::string Type = typeOf(CCE->getType());
        Target = {"temporary:" + llvm::utostr(Off) + ":" + Type,
                  std::string("(\u4e00\u6642\u30aa\u30d6\u30b8\u30a7\u30af\u30c8)"),
                  Type};
      }
      std::string ArgsText;
      for (const Expr *A : CCE->arguments()) {
        std::string Part = compact(sourceText(A->getSourceRange()), 50);
        if (Part.empty())
          Part = typeOf(A->getType());
        if (!ArgsText.empty())
          ArgsText += ", ";
        ArgsText += Part;
      }
      const FunctionDecl *Ctor = resolveConstructor(CCE, W);
      std::string Type = typeOf(CCE->getType());
      llvm::SmallVector<const Expr *, 8> AllArgs(CCE->arguments().begin(),
                                                 CCE->arguments().end());
      addCall(Target, std::string("\u00abcreate\u00bb ") + Type + "(" +
                         ArgsText + ")",
              Context, CCE->getSourceRange(), /*Indirect=*/false,
              Ctor ? Ctor : nullptr, AllArgs, W);
      return;
    }
    // Dependent template calls remain unresolved in Clang's primary
    // template AST.
    if (llvm::isa<CXXDependentScopeMemberExpr>(S) ||
        llvm::isa<UnresolvedLookupExpr>(S))
      return;
    // Pass a copy each iteration: moving Context out on the first child
    // would drop the enclosing context for the remaining children.
    for (const Stmt *C : S->children())
      walkStmt(C, Context, Constructed, W);
  }

  void walkDeclOf(const Decl *D, llvm::SmallVector<std::string, 4> Context,
                  const Participant *Constructed, WalkState &W) const {
    if (const auto *VD = llvm::dyn_cast<VarDecl>(D)) {
      Participant Object{"object:" + objectId(VD),
                         VD->getNameAsString().empty()
                             ? std::string("(\u30ea\u30bd\u30fc\u30eb)")
                             : VD->getNameAsString(),
                         typeOf(VD)};
      if (VD->getInit())
        walkStmt(VD->getInit(), std::move(Context), &Object, W);
      if (const auto *DD = llvm::dyn_cast<DecompositionDecl>(VD))
        for (const auto *B : DD->bindings())
          if (const Expr *BI = B->getBinding())
            walkStmt(BI, std::move(Context), nullptr, W);
      return;
    }
    // Function and record declarations inside bodies are skipped (their
    // bodies are separate functions / handled by the class pass).
  }

  void handleCall(const CallExpr *CE,
                  llvm::SmallVector<std::string, 4> Context,
                  WalkState &W) const {
    // Arguments and receiver expressions are evaluated before the outer
    // invocation.
    for (const Stmt *C : CE->children())
      walkStmt(C, Context, nullptr, W);

    const Expr *CalleeExpr = unwrap(CE->getCallee());
    const NamedDecl *Reference = nullptr;
    QualType RefType;
    if (const auto *DRE = llvm::dyn_cast<DeclRefExpr>(CalleeExpr)) {
      Reference = llvm::dyn_cast<NamedDecl>(DRE->getDecl());
      RefType = DRE->getType();
    }
    const FunctionDecl *Direct = CE->getDirectCallee();
    const Decl *RefDecl = nullptr;
    bool DependentMember = llvm::isa<CXXDependentScopeMemberExpr>(CalleeExpr);
    bool Member = llvm::isa<MemberExpr>(CalleeExpr) || DependentMember;
    bool OperatorMember = llvm::isa<CXXOperatorCallExpr>(CE) &&
                          llvm::isa_and_nonnull<CXXMethodDecl>(Direct);
    if (Member)
      RefDecl = llvm::cast<MemberExpr>(CalleeExpr)->getMemberDecl();
    else if (Reference)
      RefDecl = Reference;

    // The old pipeline's `declarations` map only contains project
    // functions (AstReader prunes system AST nodes), so a system callee
    // must fall back to the callee's source text for its name, count as
    // indirect when it is a member operator, and must not be treated as a
    // `static:` recipient.
    const FnInfo *Decl = findFunction(RefDecl);
    const bool DeclInProject = Decl && isInProject(Decl->File);

    bool Indirect =
        DependentMember ||
        (!Member &&
         (!llvm::isa_and_nonnull<FunctionDecl>(Reference) ||
          (OperatorMember && !DeclInProject)));

    Participant Recipient;
    if (DeclInProject && !Decl->Owner.empty() && Direct &&
        Direct->getStorageClass() == SC_Static)
      Recipient = (Decl->Owner == W.Def->Owner &&
                       W.Def->F->getStorageClass() == SC_Static)
                      ? W.Caller
                      : (Participant{std::string("static:") + Decl->Owner,
                                     Decl->Owner,
                                     std::string("\u30af\u30e9\u30b9 / static")});
    else if (Member)
      Recipient = makeExpression(llvm::cast<MemberExpr>(CalleeExpr)->getBase(),
                                 W.Caller);
    else if (OperatorMember && (!Decl || Direct->getStorageClass() != SC_Static))
      Recipient = makeExpression(CE->getArg(0), W.Caller);
    else if (Indirect)
      Recipient = makeExpression(CalleeExpr, W.Caller);
    else {
      std::string Name;
      if (DeclInProject && Direct)
        Name = Decl->Scope.empty()
                   ? Direct->getNameAsString()
                   : joinScope(Decl->Scope, "::") + "::" +
                         Direct->getNameAsString();
      else
        Name = compact(CalleeExpr ? sourceText(CalleeExpr->getSourceRange())
                                  : std::string(),
                       60);
      if (Name.empty() && Reference)
        Name = Reference->getNameAsString();
      if (Name.empty())
        Name = std::string("\u95a2\u6570");
      std::string SelfName =
          W.Def->Scope.empty()
              ? W.Def->F->getNameAsString()
              : joinScope(W.Def->Scope, "::") + "::" +
                    W.Def->F->getNameAsString();
      bool SameFunction =
          W.Def->Owner.empty() && Name == SelfName &&
          (Reference && Direct &&
           RefType.getAsString(*Policy) ==
               W.Def->F->getType().getAsString(*Policy));
      if (SameFunction ||
          (DeclInProject && Decl->Owner == W.Def->Owner &&
           W.Def->F->getStorageClass() == SC_Static))
        Recipient = W.Caller;
      else if (DeclInProject && !Decl->Owner.empty())
        Recipient = {std::string("static:") + Decl->Owner, Decl->Owner,
                     std::string("\u30af\u30e9\u30b9 / static")};
      else
        Recipient = {
            "function:" + Name +
               ":" +
                   (Reference ? RefType.getAsString(*Policy)
                              : std::string()),
            Name, std::string("\u95a2\u6570")};
    }

    std::string Display = sourceText(CE->getSourceRange());
    if (Display.empty()) {
      if (Direct)
        Display = Direct->getNameAsString() + "()";
      else if (Reference)
        Display = Reference->getNameAsString() + "()";
      else
        Display = "call()";
    }

    llvm::SmallVector<const Expr *, 8> Args;
    if (OperatorMember) {
      // A member operator call stores the implicit object as argument 0;
      // the TypeScript reference keeps children.slice(2) (callee + object
      // removed), i.e. every explicit argument after the object.
      for (unsigned I = 1; I < CE->getNumArgs(); ++I)
        Args.push_back(CE->getArg(I));
    } else {
      Args.assign(CE->arguments().begin(), CE->arguments().end());
    }
    addCall(Recipient, Display, std::move(Context), CE->getSourceRange(),
            Indirect, RefDecl, Args, W);
  }

  llvm::json::Object participantToJson(const Participant &P) const {
    llvm::json::Object O;
    O["id"] = P.Id;
    O["name"] = P.Name;
    O["type"] = P.Type;
    if (P.HasUml)
      O["uml"] = P.Uml.toJson();
    return O;
  }

  llvm::json::Object callToJson(const CallRec &C) const {
    llvm::json::Object O;
    O["to"] = C.To;
    O["label"] = C.Label;
    O["context"] = llvm::json::Array(C.Context);
    O["line"] = C.Line;
    O["indirect"] = C.Indirect;
    O["kind"] = C.Kind;
    if (C.HasCallee)
      O["callee"] = C.Callee;
    if (C.HasUml)
      O["uml"] = C.Uml.toJson();
    O["file"] = C.File;
    {
      llvm::json::Array A;
      for (const Participant &A2 : C.Arguments)
        A.push_back(participantToJson(A2));
      O["arguments"] = std::move(A);
    }
    return O;
  }

  void makeFunctionObject(const FnInfo &Def) {
    const FunctionDecl *F = Def.F;
    std::string Qualified =
        Def.Scope.empty()
            ? F->getNameAsString()
            : joinScope(Def.Scope, "::") + "::" + F->getNameAsString();
    llvm::SmallVector<std::string, 8> Params;
    for (const auto *P : F->parameters())
      Params.push_back(P->getType().getAsString(*Policy));
    if (F->isVariadic())
      Params.push_back("...");
    std::string Sig = F->getType().getAsString(*Policy);
    std::string Qualifiers;
    size_t P1 = Sig.find(") ");
    if (P1 != std::string::npos && P1 + 2 < Sig.size())
      Qualifiers = Sig.substr(P1 + 2);
    std::string Signature = Qualified + "(" + joinScope(Params, ", ") + ")" +
                            (Qualifiers.empty() ? "" : " " + Qualifiers);
    std::string File;
    unsigned Off, Line;
    locInfo(F->getLocation(), File, Off, Line);
    std::string Id = Def.File + ":" + llvm::utostr(Off) + ":" + Signature;

    Participant Caller;
    if (!Def.Owner.empty() && F->getStorageClass() != SC_Static)
      Caller = {"this", "this", Def.Owner};
    else
      Caller = {"caller", Def.Owner.empty() ? Qualified : Def.Owner,
                Def.Owner.empty() ? std::string("\u95a2\u6570")
                                  : std::string("\u30af\u30e9\u30b9 / static")};
    if (const UmlAnno *R = metadata(Def.Owner, Def.Scope)) {
      Caller.Uml = *R;
      Caller.HasUml = true;
    } else {
      Caller.Uml = Def.Anno;
      Caller.HasUml = Def.HasAnno;
    }

    WalkState W;
    W.Def = &Def;
    W.Caller = Caller;
    W.Participants.push_back(Caller);
    W.ParticipantIndex[Caller.Id.c_str()] = 0;

    // Walk the definition body (constructor initializers first). A base
    // initializer constructs `this` (the caller), not a temporary.
    if (const auto *Ctor = llvm::dyn_cast<CXXConstructorDecl>(F))
      for (const auto *Init : Ctor->inits()) {
        if (!Init->getInit())
          continue;
        if (Init->isAnyMemberInitializer()) {
          Participant P = {"this." + objectId(Init->getAnyMember()),
                           "this." + Init->getAnyMember()->getNameAsString(),
                           typeOf(Init->getAnyMember())};
          walkStmt(Init->getInit(), {}, &P, W);
        } else if (Init->isBaseInitializer()) {
          // A base initializer constructs `this` (the caller), not a
          // temporary.
          walkStmt(Init->getInit(), {}, &W.Caller, W);
        } else {
          // A delegating initializer has no `anyInit`/`baseInit` in the JSON
          // AST, so the TypeScript reference walks it as a temporary.
          walkStmt(Init->getInit(), {}, nullptr, W);
        }
      }
    if (const Stmt *B = F->getBody())
      walkStmt(B, {}, nullptr, W);

    llvm::json::Object O;
    O["id"] = Id;
    O["key"] = keyOf(Def);
    UmlAnno FuncUml;
    const auto RIt = Roles.find(Def.Owner.c_str());
    if (RIt != Roles.end()) {
      FuncUml.Group = RIt->second.Group;
      FuncUml.UseCase = RIt->second.UseCase;
    }
    FuncUml.apply(Def.Anno);
    if (!FuncUml.empty())
      O["uml"] = FuncUml.toJson();
    {
      llvm::json::Array P;
      for (const auto *P2 : F->parameters())
        P.push_back("object:" + objectId(P2));
      O["parameters"] = std::move(P);
    }
    O["name"] = Qualified;
    O["signature"] = Signature;
    O["file"] = Def.File.substr(Root.size());
    O["line"] = Line;
    // The old pipeline shares one object between `caller` and the `this`
    // participant, so updates made while walking (callee annotations on a
    // `this` recipient) must also be visible on the emitted caller.
    O["caller"] = participantToJson(W.Participants[W.ParticipantIndex[Caller.Id.c_str()]]);
    {
      llvm::json::Array P;
      for (const Participant &P2 : W.Participants)
        P.push_back(participantToJson(P2));
      O["participants"] = std::move(P);
    }
    {
      llvm::json::Array C;
      for (const CallRec &C2 : W.Calls)
        C.push_back(callToJson(C2));
      O["calls"] = std::move(C);
    }
    FunctionObjects.push_back(std::move(O));
  }
};

} // namespace

std::unique_ptr<clang::ASTConsumer>
clang::CreateASTUMLDumper(std::unique_ptr<raw_ostream> OS,
                         StringRef ProjectRoot, StringRef MainFile) {
  const bool RootFromMainFile = ProjectRoot.empty();
  std::string Root = normalizePath(
      RootFromMainFile ? std::string(MainFile) : std::string(ProjectRoot));
  if (Root.size() > 1 && Root.back() == '/')
    Root.pop_back();
  // When the root was derived from the main file, it is a file path; use
  // its directory instead. An explicitly given root is already a directory.
  if (RootFromMainFile) {
    size_t S = Root.rfind('/');
    Root = S == std::string::npos ? std::string("/") : Root.substr(0, S);
  }
  raw_ostream &OStream = OS ? *OS : llvm::outs();
  return std::unique_ptr<clang::ASTConsumer>(
      new UMLDumperConsumer(OStream, Root + "/",
                            normalizePath(std::string(MainFile))));
}
