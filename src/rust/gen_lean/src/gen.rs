#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]

pub use gen_init::r#gen::Init;
pub use gen_std::r#gen::Std;
pub mod Lean {
    pub mod index {
        include!("gen/Lean.rs");
    }
    pub use index::*;
    pub mod AddDecl {
        include!("gen/Lean/AddDecl.rs");
    }
    pub mod Attributes {
        include!("gen/Lean/Attributes.rs");
    }
    pub mod AuxRecursor {
        include!("gen/Lean/AuxRecursor.rs");
    }
    pub mod BuiltinDocAttr {
        include!("gen/Lean/BuiltinDocAttr.rs");
    }
    pub mod Class {
        include!("gen/Lean/Class.rs");
    }
    pub mod CompactedRegion {
        include!("gen/Lean/CompactedRegion.rs");
    }
    pub mod Compiler {
        pub mod index {
            include!("gen/Lean/Compiler.rs");
        }
        pub use index::*;
        pub mod BorrowedAnnotation {
            include!("gen/Lean/Compiler/BorrowedAnnotation.rs");
        }
        pub mod CSimpAttr {
            include!("gen/Lean/Compiler/CSimpAttr.rs");
        }
        pub mod ClosedTermCache {
            include!("gen/Lean/Compiler/ClosedTermCache.rs");
        }
        pub mod ExportAttr {
            include!("gen/Lean/Compiler/ExportAttr.rs");
        }
        pub mod ExternAttr {
            include!("gen/Lean/Compiler/ExternAttr.rs");
        }
        pub mod FFI {
            include!("gen/Lean/Compiler/FFI.rs");
        }
        pub mod IR {
            pub mod index {
                include!("gen/Lean/Compiler/IR.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Compiler/IR/Basic.rs");
            }
            pub mod Checker {
                include!("gen/Lean/Compiler/IR/Checker.rs");
            }
            pub mod CompilerM {
                include!("gen/Lean/Compiler/IR/CompilerM.rs");
            }
            pub mod EmitLLVM {
                include!("gen/Lean/Compiler/IR/EmitLLVM.rs");
            }
            pub mod EmitUtil {
                include!("gen/Lean/Compiler/IR/EmitUtil.rs");
            }
            pub mod Format {
                include!("gen/Lean/Compiler/IR/Format.rs");
            }
            pub mod LLVMBindings {
                include!("gen/Lean/Compiler/IR/LLVMBindings.rs");
            }
            pub mod Meta {
                include!("gen/Lean/Compiler/IR/Meta.rs");
            }
            pub mod NormIds {
                include!("gen/Lean/Compiler/IR/NormIds.rs");
            }
            pub mod Sorry {
                include!("gen/Lean/Compiler/IR/Sorry.rs");
            }
            pub mod ToIR {
                include!("gen/Lean/Compiler/IR/ToIR.rs");
            }
            pub mod ToIRType {
                include!("gen/Lean/Compiler/IR/ToIRType.rs");
            }
            pub mod UnboxResult {
                include!("gen/Lean/Compiler/IR/UnboxResult.rs");
            }
        }
        pub mod ImplementedByAttr {
            include!("gen/Lean/Compiler/ImplementedByAttr.rs");
        }
        pub mod InitAttr {
            include!("gen/Lean/Compiler/InitAttr.rs");
        }
        pub mod InlineAttrs {
            include!("gen/Lean/Compiler/InlineAttrs.rs");
        }
        pub mod LCNF {
            pub mod index {
                include!("gen/Lean/Compiler/LCNF.rs");
            }
            pub use index::*;
            pub mod AlphaEqv {
                include!("gen/Lean/Compiler/LCNF/AlphaEqv.rs");
            }
            pub mod AuxDeclCache {
                include!("gen/Lean/Compiler/LCNF/AuxDeclCache.rs");
            }
            pub mod BaseTypes {
                include!("gen/Lean/Compiler/LCNF/BaseTypes.rs");
            }
            pub mod Basic {
                include!("gen/Lean/Compiler/LCNF/Basic.rs");
            }
            pub mod Bind {
                include!("gen/Lean/Compiler/LCNF/Bind.rs");
            }
            pub mod CSE {
                include!("gen/Lean/Compiler/LCNF/CSE.rs");
            }
            pub mod Check {
                include!("gen/Lean/Compiler/LCNF/Check.rs");
            }
            pub mod Closure {
                include!("gen/Lean/Compiler/LCNF/Closure.rs");
            }
            pub mod CoalesceRC {
                include!("gen/Lean/Compiler/LCNF/CoalesceRC.rs");
            }
            pub mod CompatibleTypes {
                include!("gen/Lean/Compiler/LCNF/CompatibleTypes.rs");
            }
            pub mod CompilerM {
                include!("gen/Lean/Compiler/LCNF/CompilerM.rs");
            }
            pub mod ConfigOptions {
                include!("gen/Lean/Compiler/LCNF/ConfigOptions.rs");
            }
            pub mod DeclHash {
                include!("gen/Lean/Compiler/LCNF/DeclHash.rs");
            }
            pub mod DependsOn {
                include!("gen/Lean/Compiler/LCNF/DependsOn.rs");
            }
            pub mod ElimDead {
                include!("gen/Lean/Compiler/LCNF/ElimDead.rs");
            }
            pub mod ElimDeadBranches {
                include!("gen/Lean/Compiler/LCNF/ElimDeadBranches.rs");
            }
            pub mod EmitRust {
                pub mod index {
                    include!("gen/Lean/Compiler/LCNF/EmitRust.rs");
                }
                pub use index::*;
            }
            pub mod EmitUtil {
                include!("gen/Lean/Compiler/LCNF/EmitUtil.rs");
            }
            pub mod ExpandResetReuse {
                include!("gen/Lean/Compiler/LCNF/ExpandResetReuse.rs");
            }
            pub mod ExplicitBoxing {
                include!("gen/Lean/Compiler/LCNF/ExplicitBoxing.rs");
            }
            pub mod ExplicitRC {
                include!("gen/Lean/Compiler/LCNF/ExplicitRC.rs");
            }
            pub mod ExtractClosed {
                include!("gen/Lean/Compiler/LCNF/ExtractClosed.rs");
            }
            pub mod FVarUtil {
                include!("gen/Lean/Compiler/LCNF/FVarUtil.rs");
            }
            pub mod FixedParams {
                include!("gen/Lean/Compiler/LCNF/FixedParams.rs");
            }
            pub mod FloatLetIn {
                include!("gen/Lean/Compiler/LCNF/FloatLetIn.rs");
            }
            pub mod InferBorrow {
                include!("gen/Lean/Compiler/LCNF/InferBorrow.rs");
            }
            pub mod InferType {
                include!("gen/Lean/Compiler/LCNF/InferType.rs");
            }
            pub mod Internalize {
                include!("gen/Lean/Compiler/LCNF/Internalize.rs");
            }
            pub mod Irrelevant {
                include!("gen/Lean/Compiler/LCNF/Irrelevant.rs");
            }
            pub mod JoinPoints {
                include!("gen/Lean/Compiler/LCNF/JoinPoints.rs");
            }
            pub mod LCtx {
                include!("gen/Lean/Compiler/LCNF/LCtx.rs");
            }
            pub mod LambdaLifting {
                include!("gen/Lean/Compiler/LCNF/LambdaLifting.rs");
            }
            pub mod Level {
                include!("gen/Lean/Compiler/LCNF/Level.rs");
            }
            pub mod LiveVars {
                include!("gen/Lean/Compiler/LCNF/LiveVars.rs");
            }
            pub mod Main {
                include!("gen/Lean/Compiler/LCNF/Main.rs");
            }
            pub mod MonadScope {
                include!("gen/Lean/Compiler/LCNF/MonadScope.rs");
            }
            pub mod MonoTypes {
                include!("gen/Lean/Compiler/LCNF/MonoTypes.rs");
            }
            pub mod OtherDecl {
                include!("gen/Lean/Compiler/LCNF/OtherDecl.rs");
            }
            pub mod PassManager {
                include!("gen/Lean/Compiler/LCNF/PassManager.rs");
            }
            pub mod Passes {
                include!("gen/Lean/Compiler/LCNF/Passes.rs");
            }
            pub mod PhaseExt {
                include!("gen/Lean/Compiler/LCNF/PhaseExt.rs");
            }
            pub mod PrettyPrinter {
                include!("gen/Lean/Compiler/LCNF/PrettyPrinter.rs");
            }
            pub mod Probing {
                include!("gen/Lean/Compiler/LCNF/Probing.rs");
            }
            pub mod PropagateBorrow {
                include!("gen/Lean/Compiler/LCNF/PropagateBorrow.rs");
            }
            pub mod PublicDeclsExt {
                include!("gen/Lean/Compiler/LCNF/PublicDeclsExt.rs");
            }
            pub mod PullFunDecls {
                include!("gen/Lean/Compiler/LCNF/PullFunDecls.rs");
            }
            pub mod PullLetDecls {
                include!("gen/Lean/Compiler/LCNF/PullLetDecls.rs");
            }
            pub mod PushProj {
                include!("gen/Lean/Compiler/LCNF/PushProj.rs");
            }
            pub mod ReduceArity {
                include!("gen/Lean/Compiler/LCNF/ReduceArity.rs");
            }
            pub mod ReduceJpArity {
                include!("gen/Lean/Compiler/LCNF/ReduceJpArity.rs");
            }
            pub mod Renaming {
                include!("gen/Lean/Compiler/LCNF/Renaming.rs");
            }
            pub mod ResetReuse {
                include!("gen/Lean/Compiler/LCNF/ResetReuse.rs");
            }
            pub mod ScopeM {
                include!("gen/Lean/Compiler/LCNF/ScopeM.rs");
            }
            pub mod Simp {
                pub mod index {
                    include!("gen/Lean/Compiler/LCNF/Simp.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("gen/Lean/Compiler/LCNF/Simp/Basic.rs");
                }
                pub mod Config {
                    include!("gen/Lean/Compiler/LCNF/Simp/Config.rs");
                }
                pub mod ConstantFold {
                    include!("gen/Lean/Compiler/LCNF/Simp/ConstantFold.rs");
                }
                pub mod DefaultAlt {
                    include!("gen/Lean/Compiler/LCNF/Simp/DefaultAlt.rs");
                }
                pub mod DiscrM {
                    include!("gen/Lean/Compiler/LCNF/Simp/DiscrM.rs");
                }
                pub mod FunDeclInfo {
                    include!("gen/Lean/Compiler/LCNF/Simp/FunDeclInfo.rs");
                }
                pub mod InlineCandidate {
                    include!("gen/Lean/Compiler/LCNF/Simp/InlineCandidate.rs");
                }
                pub mod InlineProj {
                    include!("gen/Lean/Compiler/LCNF/Simp/InlineProj.rs");
                }
                pub mod JpCases {
                    include!("gen/Lean/Compiler/LCNF/Simp/JpCases.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Compiler/LCNF/Simp/Main.rs");
                }
                pub mod SimpM {
                    include!("gen/Lean/Compiler/LCNF/Simp/SimpM.rs");
                }
                pub mod SimpValue {
                    include!("gen/Lean/Compiler/LCNF/Simp/SimpValue.rs");
                }
                pub mod Used {
                    include!("gen/Lean/Compiler/LCNF/Simp/Used.rs");
                }
            }
            pub mod SimpCase {
                include!("gen/Lean/Compiler/LCNF/SimpCase.rs");
            }
            pub mod SimpleGroundExpr {
                include!("gen/Lean/Compiler/LCNF/SimpleGroundExpr.rs");
            }
            pub mod SpecInfo {
                include!("gen/Lean/Compiler/LCNF/SpecInfo.rs");
            }
            pub mod Specialize {
                include!("gen/Lean/Compiler/LCNF/Specialize.rs");
            }
            pub mod SplitSCC {
                include!("gen/Lean/Compiler/LCNF/SplitSCC.rs");
            }
            pub mod StructProjCases {
                include!("gen/Lean/Compiler/LCNF/StructProjCases.rs");
            }
            pub mod ToDecl {
                include!("gen/Lean/Compiler/LCNF/ToDecl.rs");
            }
            pub mod ToExpr {
                include!("gen/Lean/Compiler/LCNF/ToExpr.rs");
            }
            pub mod ToImpure {
                include!("gen/Lean/Compiler/LCNF/ToImpure.rs");
            }
            pub mod ToImpureType {
                include!("gen/Lean/Compiler/LCNF/ToImpureType.rs");
            }
            pub mod ToLCNF {
                include!("gen/Lean/Compiler/LCNF/ToLCNF.rs");
            }
            pub mod ToMono {
                include!("gen/Lean/Compiler/LCNF/ToMono.rs");
            }
            pub mod Toposort {
                include!("gen/Lean/Compiler/LCNF/Toposort.rs");
            }
            pub mod Types {
                include!("gen/Lean/Compiler/LCNF/Types.rs");
            }
            pub mod Util {
                include!("gen/Lean/Compiler/LCNF/Util.rs");
            }
            pub mod Visibility {
                include!("gen/Lean/Compiler/LCNF/Visibility.rs");
            }
        }
        pub mod Main {
            include!("gen/Lean/Compiler/Main.rs");
        }
        pub mod MetaAttr {
            include!("gen/Lean/Compiler/MetaAttr.rs");
        }
        pub mod ModPkgExt {
            include!("gen/Lean/Compiler/ModPkgExt.rs");
        }
        pub mod NameDemangling {
            include!("gen/Lean/Compiler/NameDemangling.rs");
        }
        pub mod NameMangling {
            include!("gen/Lean/Compiler/NameMangling.rs");
        }
        pub mod NeverExtractAttr {
            include!("gen/Lean/Compiler/NeverExtractAttr.rs");
        }
        pub mod NoncomputableAttr {
            include!("gen/Lean/Compiler/NoncomputableAttr.rs");
        }
        pub mod Old {
            include!("gen/Lean/Compiler/Old.rs");
        }
        pub mod Options {
            include!("gen/Lean/Compiler/Options.rs");
        }
        pub mod Specialize {
            include!("gen/Lean/Compiler/Specialize.rs");
        }
    }
    pub mod CoreM {
        include!("gen/Lean/CoreM.rs");
    }
    pub mod Data {
        pub mod index {
            include!("gen/Lean/Data.rs");
        }
        pub use index::*;
        pub mod Array {
            include!("gen/Lean/Data/Array.rs");
        }
        pub mod AssocList {
            include!("gen/Lean/Data/AssocList.rs");
        }
        pub mod DeclarationRange {
            include!("gen/Lean/Data/DeclarationRange.rs");
        }
        pub mod EditDistance {
            include!("gen/Lean/Data/EditDistance.rs");
        }
        pub mod Format {
            include!("gen/Lean/Data/Format.rs");
        }
        pub mod FuzzyMatching {
            include!("gen/Lean/Data/FuzzyMatching.rs");
        }
        pub mod Iterators {
            pub mod index {
                include!("gen/Lean/Data/Iterators.rs");
            }
            pub use index::*;
            pub mod Producers {
                pub mod index {
                    include!("gen/Lean/Data/Iterators/Producers.rs");
                }
                pub use index::*;
                pub mod PersistentHashMap {
                    include!("gen/Lean/Data/Iterators/Producers/PersistentHashMap.rs");
                }
            }
        }
        pub mod Json {
            pub mod index {
                include!("gen/Lean/Data/Json.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Data/Json/Basic.rs");
            }
            pub mod Elab {
                include!("gen/Lean/Data/Json/Elab.rs");
            }
            pub mod FromToJson {
                pub mod index {
                    include!("gen/Lean/Data/Json/FromToJson.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("gen/Lean/Data/Json/FromToJson/Basic.rs");
                }
                pub mod Extra {
                    include!("gen/Lean/Data/Json/FromToJson/Extra.rs");
                }
            }
            pub mod Parser {
                include!("gen/Lean/Data/Json/Parser.rs");
            }
            pub mod Printer {
                include!("gen/Lean/Data/Json/Printer.rs");
            }
            pub mod Stream {
                include!("gen/Lean/Data/Json/Stream.rs");
            }
        }
        pub mod JsonRpc {
            include!("gen/Lean/Data/JsonRpc.rs");
        }
        pub mod KVMap {
            include!("gen/Lean/Data/KVMap.rs");
        }
        pub mod LBool {
            include!("gen/Lean/Data/LBool.rs");
        }
        pub mod LOption {
            include!("gen/Lean/Data/LOption.rs");
        }
        pub mod Lsp {
            pub mod index {
                include!("gen/Lean/Data/Lsp.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Data/Lsp/Basic.rs");
            }
            pub mod BasicAux {
                include!("gen/Lean/Data/Lsp/BasicAux.rs");
            }
            pub mod CancelParams {
                include!("gen/Lean/Data/Lsp/CancelParams.rs");
            }
            pub mod Capabilities {
                include!("gen/Lean/Data/Lsp/Capabilities.rs");
            }
            pub mod Client {
                include!("gen/Lean/Data/Lsp/Client.rs");
            }
            pub mod CodeActions {
                include!("gen/Lean/Data/Lsp/CodeActions.rs");
            }
            pub mod Communication {
                include!("gen/Lean/Data/Lsp/Communication.rs");
            }
            pub mod Diagnostics {
                include!("gen/Lean/Data/Lsp/Diagnostics.rs");
            }
            pub mod Extra {
                include!("gen/Lean/Data/Lsp/Extra.rs");
            }
            pub mod InitShutdown {
                include!("gen/Lean/Data/Lsp/InitShutdown.rs");
            }
            pub mod Internal {
                include!("gen/Lean/Data/Lsp/Internal.rs");
            }
            pub mod Ipc {
                include!("gen/Lean/Data/Lsp/Ipc.rs");
            }
            pub mod LanguageFeatures {
                include!("gen/Lean/Data/Lsp/LanguageFeatures.rs");
            }
            pub mod TextSync {
                include!("gen/Lean/Data/Lsp/TextSync.rs");
            }
            pub mod Utf16 {
                include!("gen/Lean/Data/Lsp/Utf16.rs");
            }
            pub mod Window {
                include!("gen/Lean/Data/Lsp/Window.rs");
            }
            pub mod Workspace {
                include!("gen/Lean/Data/Lsp/Workspace.rs");
            }
        }
        pub mod Name {
            include!("gen/Lean/Data/Name.rs");
        }
        pub mod NameMap {
            pub mod index {
                include!("gen/Lean/Data/NameMap.rs");
            }
            pub use index::*;
            pub mod AdditionalOperations {
                include!("gen/Lean/Data/NameMap/AdditionalOperations.rs");
            }
            pub mod Basic {
                include!("gen/Lean/Data/NameMap/Basic.rs");
            }
        }
        pub mod NameTrie {
            include!("gen/Lean/Data/NameTrie.rs");
        }
        pub mod OpenDecl {
            include!("gen/Lean/Data/OpenDecl.rs");
        }
        pub mod Options {
            include!("gen/Lean/Data/Options.rs");
        }
        pub mod PPContext {
            include!("gen/Lean/Data/PPContext.rs");
        }
        pub mod PersistentArray {
            include!("gen/Lean/Data/PersistentArray.rs");
        }
        pub mod PersistentHashMap {
            include!("gen/Lean/Data/PersistentHashMap.rs");
        }
        pub mod PersistentHashSet {
            include!("gen/Lean/Data/PersistentHashSet.rs");
        }
        pub mod Position {
            include!("gen/Lean/Data/Position.rs");
        }
        pub mod PrefixTree {
            include!("gen/Lean/Data/PrefixTree.rs");
        }
        pub mod RArray {
            include!("gen/Lean/Data/RArray.rs");
        }
        pub mod RBMap {
            include!("gen/Lean/Data/RBMap.rs");
        }
        pub mod RBTree {
            include!("gen/Lean/Data/RBTree.rs");
        }
        pub mod SMap {
            include!("gen/Lean/Data/SMap.rs");
        }
        pub mod SSet {
            include!("gen/Lean/Data/SSet.rs");
        }
        pub mod Trie {
            include!("gen/Lean/Data/Trie.rs");
        }
    }
    pub mod Declaration {
        include!("gen/Lean/Declaration.rs");
    }
    pub mod DeclarationRange {
        include!("gen/Lean/DeclarationRange.rs");
    }
    pub mod DefEqAttrib {
        include!("gen/Lean/DefEqAttrib.rs");
    }
    pub mod DeprecatedModule {
        include!("gen/Lean/DeprecatedModule.rs");
    }
    pub mod DocString {
        pub mod index {
            include!("gen/Lean/DocString.rs");
        }
        pub use index::*;
        pub mod Add {
            include!("gen/Lean/DocString/Add.rs");
        }
        pub mod Extension {
            include!("gen/Lean/DocString/Extension.rs");
        }
        pub mod Formatter {
            include!("gen/Lean/DocString/Formatter.rs");
        }
        pub mod Links {
            include!("gen/Lean/DocString/Links.rs");
        }
        pub mod Markdown {
            include!("gen/Lean/DocString/Markdown.rs");
        }
        pub mod Parser {
            include!("gen/Lean/DocString/Parser.rs");
        }
        pub mod Syntax {
            include!("gen/Lean/DocString/Syntax.rs");
        }
        pub mod Types {
            include!("gen/Lean/DocString/Types.rs");
        }
    }
    pub mod Elab {
        pub mod index {
            include!("gen/Lean/Elab.rs");
        }
        pub use index::*;
        pub mod App {
            include!("gen/Lean/Elab/App.rs");
        }
        pub mod Arg {
            include!("gen/Lean/Elab/Arg.rs");
        }
        pub mod AssertExists {
            include!("gen/Lean/Elab/AssertExists.rs");
        }
        pub mod Attributes {
            include!("gen/Lean/Elab/Attributes.rs");
        }
        pub mod AutoBound {
            include!("gen/Lean/Elab/AutoBound.rs");
        }
        pub mod AuxDef {
            include!("gen/Lean/Elab/AuxDef.rs");
        }
        pub mod BinderPredicates {
            include!("gen/Lean/Elab/BinderPredicates.rs");
        }
        pub mod Binders {
            include!("gen/Lean/Elab/Binders.rs");
        }
        pub mod BindersUtil {
            include!("gen/Lean/Elab/BindersUtil.rs");
        }
        pub mod BuiltinCommand {
            include!("gen/Lean/Elab/BuiltinCommand.rs");
        }
        pub mod BuiltinDo {
            pub mod index {
                include!("gen/Lean/Elab/BuiltinDo.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Elab/BuiltinDo/Basic.rs");
            }
            pub mod For {
                include!("gen/Lean/Elab/BuiltinDo/For.rs");
            }
            pub mod If {
                include!("gen/Lean/Elab/BuiltinDo/If.rs");
            }
            pub mod Jump {
                include!("gen/Lean/Elab/BuiltinDo/Jump.rs");
            }
            pub mod Let {
                include!("gen/Lean/Elab/BuiltinDo/Let.rs");
            }
            pub mod Match {
                include!("gen/Lean/Elab/BuiltinDo/Match.rs");
            }
            pub mod MatchExpr {
                include!("gen/Lean/Elab/BuiltinDo/MatchExpr.rs");
            }
            pub mod Misc {
                include!("gen/Lean/Elab/BuiltinDo/Misc.rs");
            }
            pub mod Repeat {
                include!("gen/Lean/Elab/BuiltinDo/Repeat.rs");
            }
            pub mod TryCatch {
                include!("gen/Lean/Elab/BuiltinDo/TryCatch.rs");
            }
        }
        pub mod BuiltinEvalCommand {
            include!("gen/Lean/Elab/BuiltinEvalCommand.rs");
        }
        pub mod BuiltinNotation {
            include!("gen/Lean/Elab/BuiltinNotation.rs");
        }
        pub mod BuiltinTerm {
            include!("gen/Lean/Elab/BuiltinTerm.rs");
        }
        pub mod Calc {
            include!("gen/Lean/Elab/Calc.rs");
        }
        pub mod CheckTactic {
            include!("gen/Lean/Elab/CheckTactic.rs");
        }
        pub mod Coinductive {
            include!("gen/Lean/Elab/Coinductive.rs");
        }
        pub mod Command {
            pub mod index {
                include!("gen/Lean/Elab/Command.rs");
            }
            pub use index::*;
            pub mod Scope {
                include!("gen/Lean/Elab/Command/Scope.rs");
            }
            pub mod WithWeakNamespace {
                include!("gen/Lean/Elab/Command/WithWeakNamespace.rs");
            }
        }
        pub mod ComputedFields {
            include!("gen/Lean/Elab/ComputedFields.rs");
        }
        pub mod Config {
            include!("gen/Lean/Elab/Config.rs");
        }
        pub mod ConfigEval {
            pub mod index {
                include!("gen/Lean/Elab/ConfigEval.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Elab/ConfigEval/Basic.rs");
            }
            pub mod Builtins {
                include!("gen/Lean/Elab/ConfigEval/Builtins.rs");
            }
            pub mod Commands {
                include!("gen/Lean/Elab/ConfigEval/Commands.rs");
            }
            pub mod DeriveEvalConfigItem {
                include!("gen/Lean/Elab/ConfigEval/DeriveEvalConfigItem.rs");
            }
            pub mod DeriveEvalExpr {
                include!("gen/Lean/Elab/ConfigEval/DeriveEvalExpr.rs");
            }
            pub mod DeriveEvalTerm {
                include!("gen/Lean/Elab/ConfigEval/DeriveEvalTerm.rs");
            }
            pub mod Extra {
                include!("gen/Lean/Elab/ConfigEval/Extra.rs");
            }
            pub mod Instances {
                include!("gen/Lean/Elab/ConfigEval/Instances.rs");
            }
            pub mod MetaInstances {
                include!("gen/Lean/Elab/ConfigEval/MetaInstances.rs");
            }
            pub mod Types {
                include!("gen/Lean/Elab/ConfigEval/Types.rs");
            }
            pub mod Util {
                include!("gen/Lean/Elab/ConfigEval/Util.rs");
            }
        }
        pub mod DeclModifiers {
            include!("gen/Lean/Elab/DeclModifiers.rs");
        }
        pub mod DeclNameGen {
            include!("gen/Lean/Elab/DeclNameGen.rs");
        }
        pub mod DeclUtil {
            include!("gen/Lean/Elab/DeclUtil.rs");
        }
        pub mod Declaration {
            include!("gen/Lean/Elab/Declaration.rs");
        }
        pub mod DeclarationRange {
            include!("gen/Lean/Elab/DeclarationRange.rs");
        }
        pub mod DefView {
            include!("gen/Lean/Elab/DefView.rs");
        }
        pub mod DeprecatedArg {
            include!("gen/Lean/Elab/DeprecatedArg.rs");
        }
        pub mod DeprecatedSyntax {
            include!("gen/Lean/Elab/DeprecatedSyntax.rs");
        }
        pub mod Deriving {
            pub mod index {
                include!("gen/Lean/Elab/Deriving.rs");
            }
            pub use index::*;
            pub mod BEq {
                include!("gen/Lean/Elab/Deriving/BEq.rs");
            }
            pub mod Basic {
                include!("gen/Lean/Elab/Deriving/Basic.rs");
            }
            pub mod DecEq {
                include!("gen/Lean/Elab/Deriving/DecEq.rs");
            }
            pub mod FromToJson {
                include!("gen/Lean/Elab/Deriving/FromToJson.rs");
            }
            pub mod Hashable {
                include!("gen/Lean/Elab/Deriving/Hashable.rs");
            }
            pub mod Inhabited {
                include!("gen/Lean/Elab/Deriving/Inhabited.rs");
            }
            pub mod LawfulBEq {
                include!("gen/Lean/Elab/Deriving/LawfulBEq.rs");
            }
            pub mod Nonempty {
                include!("gen/Lean/Elab/Deriving/Nonempty.rs");
            }
            pub mod Ord {
                include!("gen/Lean/Elab/Deriving/Ord.rs");
            }
            pub mod ReflBEq {
                include!("gen/Lean/Elab/Deriving/ReflBEq.rs");
            }
            pub mod Repr {
                include!("gen/Lean/Elab/Deriving/Repr.rs");
            }
            pub mod SizeOf {
                include!("gen/Lean/Elab/Deriving/SizeOf.rs");
            }
            pub mod ToExpr {
                include!("gen/Lean/Elab/Deriving/ToExpr.rs");
            }
            pub mod TypeName {
                include!("gen/Lean/Elab/Deriving/TypeName.rs");
            }
            pub mod Util {
                include!("gen/Lean/Elab/Deriving/Util.rs");
            }
        }
        pub mod Do {
            pub mod index {
                include!("gen/Lean/Elab/Do.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Elab/Do/Basic.rs");
            }
            pub mod Control {
                include!("gen/Lean/Elab/Do/Control.rs");
            }
            pub mod InferControlInfo {
                include!("gen/Lean/Elab/Do/InferControlInfo.rs");
            }
            pub mod Legacy {
                include!("gen/Lean/Elab/Do/Legacy.rs");
            }
            pub mod PatternVar {
                include!("gen/Lean/Elab/Do/PatternVar.rs");
            }
            pub mod Switch {
                include!("gen/Lean/Elab/Do/Switch.rs");
            }
        }
        pub mod DocString {
            pub mod index {
                include!("gen/Lean/Elab/DocString.rs");
            }
            pub use index::*;
            pub mod Builtin {
                pub mod index {
                    include!("gen/Lean/Elab/DocString/Builtin.rs");
                }
                pub use index::*;
                pub mod Keywords {
                    include!("gen/Lean/Elab/DocString/Builtin/Keywords.rs");
                }
                pub mod Parsing {
                    include!("gen/Lean/Elab/DocString/Builtin/Parsing.rs");
                }
                pub mod Postponed {
                    include!("gen/Lean/Elab/DocString/Builtin/Postponed.rs");
                }
                pub mod Scopes {
                    include!("gen/Lean/Elab/DocString/Builtin/Scopes.rs");
                }
            }
        }
        pub mod ElabRules {
            include!("gen/Lean/Elab/ElabRules.rs");
        }
        pub mod ErrorExplanation {
            include!("gen/Lean/Elab/ErrorExplanation.rs");
        }
        pub mod ErrorUtils {
            include!("gen/Lean/Elab/ErrorUtils.rs");
        }
        pub mod Eval {
            include!("gen/Lean/Elab/Eval.rs");
        }
        pub mod Exception {
            include!("gen/Lean/Elab/Exception.rs");
        }
        pub mod Extra {
            include!("gen/Lean/Elab/Extra.rs");
        }
        pub mod Frontend {
            include!("gen/Lean/Elab/Frontend.rs");
        }
        pub mod GenInjective {
            include!("gen/Lean/Elab/GenInjective.rs");
        }
        pub mod GuardMsgs {
            include!("gen/Lean/Elab/GuardMsgs.rs");
        }
        pub mod Idbg {
            include!("gen/Lean/Elab/Idbg.rs");
        }
        pub mod Import {
            include!("gen/Lean/Elab/Import.rs");
        }
        pub mod Inductive {
            include!("gen/Lean/Elab/Inductive.rs");
        }
        pub mod InfoTree {
            pub mod index {
                include!("gen/Lean/Elab/InfoTree.rs");
            }
            pub use index::*;
            pub mod InlayHints {
                include!("gen/Lean/Elab/InfoTree/InlayHints.rs");
            }
            pub mod Main {
                include!("gen/Lean/Elab/InfoTree/Main.rs");
            }
            pub mod Types {
                include!("gen/Lean/Elab/InfoTree/Types.rs");
            }
        }
        pub mod InfoTrees {
            include!("gen/Lean/Elab/InfoTrees.rs");
        }
        pub mod InheritDoc {
            include!("gen/Lean/Elab/InheritDoc.rs");
        }
        pub mod LetRec {
            include!("gen/Lean/Elab/LetRec.rs");
        }
        pub mod Level {
            include!("gen/Lean/Elab/Level.rs");
        }
        pub mod Macro {
            include!("gen/Lean/Elab/Macro.rs");
        }
        pub mod MacroArgUtil {
            include!("gen/Lean/Elab/MacroArgUtil.rs");
        }
        pub mod MacroRules {
            include!("gen/Lean/Elab/MacroRules.rs");
        }
        pub mod Match {
            include!("gen/Lean/Elab/Match.rs");
        }
        pub mod MatchAltView {
            include!("gen/Lean/Elab/MatchAltView.rs");
        }
        pub mod MatchExpr {
            include!("gen/Lean/Elab/MatchExpr.rs");
        }
        pub mod Mixfix {
            include!("gen/Lean/Elab/Mixfix.rs");
        }
        pub mod MutualDef {
            include!("gen/Lean/Elab/MutualDef.rs");
        }
        pub mod MutualInductive {
            include!("gen/Lean/Elab/MutualInductive.rs");
        }
        pub mod Notation {
            include!("gen/Lean/Elab/Notation.rs");
        }
        pub mod Open {
            include!("gen/Lean/Elab/Open.rs");
        }
        pub mod Parallel {
            include!("gen/Lean/Elab/Parallel.rs");
        }
        pub mod ParseImportsFast {
            include!("gen/Lean/Elab/ParseImportsFast.rs");
        }
        pub mod PatternVar {
            include!("gen/Lean/Elab/PatternVar.rs");
        }
        pub mod PreDefinition {
            pub mod index {
                include!("gen/Lean/Elab/PreDefinition.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Elab/PreDefinition/Basic.rs");
            }
            pub mod EqUnfold {
                include!("gen/Lean/Elab/PreDefinition/EqUnfold.rs");
            }
            pub mod Eqns {
                include!("gen/Lean/Elab/PreDefinition/Eqns.rs");
            }
            pub mod EqnsUtils {
                include!("gen/Lean/Elab/PreDefinition/EqnsUtils.rs");
            }
            pub mod FixedParams {
                include!("gen/Lean/Elab/PreDefinition/FixedParams.rs");
            }
            pub mod Main {
                include!("gen/Lean/Elab/PreDefinition/Main.rs");
            }
            pub mod MkInhabitant {
                include!("gen/Lean/Elab/PreDefinition/MkInhabitant.rs");
            }
            pub mod Mutual {
                include!("gen/Lean/Elab/PreDefinition/Mutual.rs");
            }
            pub mod PartialFixpoint {
                pub mod index {
                    include!("gen/Lean/Elab/PreDefinition/PartialFixpoint.rs");
                }
                pub use index::*;
                pub mod Eqns {
                    include!("gen/Lean/Elab/PreDefinition/PartialFixpoint/Eqns.rs");
                }
                pub mod Induction {
                    include!("gen/Lean/Elab/PreDefinition/PartialFixpoint/Induction.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Elab/PreDefinition/PartialFixpoint/Main.rs");
                }
            }
            pub mod Structural {
                pub mod index {
                    include!("gen/Lean/Elab/PreDefinition/Structural.rs");
                }
                pub use index::*;
                pub mod BRecOn {
                    include!("gen/Lean/Elab/PreDefinition/Structural/BRecOn.rs");
                }
                pub mod Basic {
                    include!("gen/Lean/Elab/PreDefinition/Structural/Basic.rs");
                }
                pub mod Eqns {
                    include!("gen/Lean/Elab/PreDefinition/Structural/Eqns.rs");
                }
                pub mod FindRecArg {
                    include!("gen/Lean/Elab/PreDefinition/Structural/FindRecArg.rs");
                }
                pub mod IndGroupInfo {
                    include!("gen/Lean/Elab/PreDefinition/Structural/IndGroupInfo.rs");
                }
                pub mod IndPred {
                    include!("gen/Lean/Elab/PreDefinition/Structural/IndPred.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Elab/PreDefinition/Structural/Main.rs");
                }
                pub mod Preprocess {
                    include!("gen/Lean/Elab/PreDefinition/Structural/Preprocess.rs");
                }
                pub mod RecArgInfo {
                    include!("gen/Lean/Elab/PreDefinition/Structural/RecArgInfo.rs");
                }
                pub mod SmartUnfolding {
                    include!("gen/Lean/Elab/PreDefinition/Structural/SmartUnfolding.rs");
                }
            }
            pub mod TerminationHint {
                include!("gen/Lean/Elab/PreDefinition/TerminationHint.rs");
            }
            pub mod TerminationMeasure {
                include!("gen/Lean/Elab/PreDefinition/TerminationMeasure.rs");
            }
            pub mod WF {
                pub mod index {
                    include!("gen/Lean/Elab/PreDefinition/WF.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("gen/Lean/Elab/PreDefinition/WF/Basic.rs");
                }
                pub mod Eqns {
                    include!("gen/Lean/Elab/PreDefinition/WF/Eqns.rs");
                }
                pub mod Fix {
                    include!("gen/Lean/Elab/PreDefinition/WF/Fix.rs");
                }
                pub mod FloatRecApp {
                    include!("gen/Lean/Elab/PreDefinition/WF/FloatRecApp.rs");
                }
                pub mod GuessLex {
                    include!("gen/Lean/Elab/PreDefinition/WF/GuessLex.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Elab/PreDefinition/WF/Main.rs");
                }
                pub mod PackMutual {
                    include!("gen/Lean/Elab/PreDefinition/WF/PackMutual.rs");
                }
                pub mod Preprocess {
                    include!("gen/Lean/Elab/PreDefinition/WF/Preprocess.rs");
                }
                pub mod Rel {
                    include!("gen/Lean/Elab/PreDefinition/WF/Rel.rs");
                }
                pub mod Unfold {
                    include!("gen/Lean/Elab/PreDefinition/WF/Unfold.rs");
                }
            }
        }
        pub mod Print {
            include!("gen/Lean/Elab/Print.rs");
        }
        pub mod Quotation {
            pub mod index {
                include!("gen/Lean/Elab/Quotation.rs");
            }
            pub use index::*;
            pub mod Precheck {
                include!("gen/Lean/Elab/Quotation/Precheck.rs");
            }
            pub mod Util {
                include!("gen/Lean/Elab/Quotation/Util.rs");
            }
        }
        pub mod RecAppSyntax {
            include!("gen/Lean/Elab/RecAppSyntax.rs");
        }
        pub mod RecommendedSpelling {
            include!("gen/Lean/Elab/RecommendedSpelling.rs");
        }
        pub mod SetOption {
            include!("gen/Lean/Elab/SetOption.rs");
        }
        pub mod StructInst {
            include!("gen/Lean/Elab/StructInst.rs");
        }
        pub mod StructInstHint {
            include!("gen/Lean/Elab/StructInstHint.rs");
        }
        pub mod Structure {
            include!("gen/Lean/Elab/Structure.rs");
        }
        pub mod Syntax {
            include!("gen/Lean/Elab/Syntax.rs");
        }
        pub mod SyntheticMVars {
            include!("gen/Lean/Elab/SyntheticMVars.rs");
        }
        pub mod Tactic {
            pub mod index {
                include!("gen/Lean/Elab/Tactic.rs");
            }
            pub use index::*;
            pub mod AsAuxLemma {
                include!("gen/Lean/Elab/Tactic/AsAuxLemma.rs");
            }
            pub mod BVDecide {
                pub mod index {
                    include!("gen/Lean/Elab/Tactic/BVDecide.rs");
                }
                pub use index::*;
                pub mod BVCheck {
                    include!("gen/Lean/Elab/Tactic/BVDecide/BVCheck.rs");
                }
                pub mod BVDecide {
                    include!("gen/Lean/Elab/Tactic/BVDecide/BVDecide.rs");
                }
                pub mod BVTrace {
                    include!("gen/Lean/Elab/Tactic/BVDecide/BVTrace.rs");
                }
                pub mod Normalize {
                    include!("gen/Lean/Elab/Tactic/BVDecide/Normalize.rs");
                }
            }
            pub mod Basic {
                include!("gen/Lean/Elab/Tactic/Basic.rs");
            }
            pub mod BoolToPropSimps {
                include!("gen/Lean/Elab/Tactic/BoolToPropSimps.rs");
            }
            pub mod BuiltinTactic {
                include!("gen/Lean/Elab/Tactic/BuiltinTactic.rs");
            }
            pub mod Calc {
                include!("gen/Lean/Elab/Tactic/Calc.rs");
            }
            pub mod Cbv {
                include!("gen/Lean/Elab/Tactic/Cbv.rs");
            }
            pub mod CbvSimproc {
                include!("gen/Lean/Elab/Tactic/CbvSimproc.rs");
            }
            pub mod Change {
                include!("gen/Lean/Elab/Tactic/Change.rs");
            }
            pub mod Classical {
                include!("gen/Lean/Elab/Tactic/Classical.rs");
            }
            pub mod Config {
                include!("gen/Lean/Elab/Tactic/Config.rs");
            }
            pub mod Congr {
                include!("gen/Lean/Elab/Tactic/Congr.rs");
            }
            pub mod Conv {
                pub mod index {
                    include!("gen/Lean/Elab/Tactic/Conv.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("gen/Lean/Elab/Tactic/Conv/Basic.rs");
                }
                pub mod Cbv {
                    include!("gen/Lean/Elab/Tactic/Conv/Cbv.rs");
                }
                pub mod Change {
                    include!("gen/Lean/Elab/Tactic/Conv/Change.rs");
                }
                pub mod Congr {
                    include!("gen/Lean/Elab/Tactic/Conv/Congr.rs");
                }
                pub mod Delta {
                    include!("gen/Lean/Elab/Tactic/Conv/Delta.rs");
                }
                pub mod Lets {
                    include!("gen/Lean/Elab/Tactic/Conv/Lets.rs");
                }
                pub mod Pattern {
                    include!("gen/Lean/Elab/Tactic/Conv/Pattern.rs");
                }
                pub mod Rewrite {
                    include!("gen/Lean/Elab/Tactic/Conv/Rewrite.rs");
                }
                pub mod Simp {
                    include!("gen/Lean/Elab/Tactic/Conv/Simp.rs");
                }
                pub mod Unfold {
                    include!("gen/Lean/Elab/Tactic/Conv/Unfold.rs");
                }
            }
            pub mod Decide {
                include!("gen/Lean/Elab/Tactic/Decide.rs");
            }
            pub mod Delta {
                include!("gen/Lean/Elab/Tactic/Delta.rs");
            }
            pub mod DiscrTreeKey {
                include!("gen/Lean/Elab/Tactic/DiscrTreeKey.rs");
            }
            pub mod Do {
                pub mod index {
                    include!("gen/Lean/Elab/Tactic/Do.rs");
                }
                pub use index::*;
                pub mod Attr {
                    include!("gen/Lean/Elab/Tactic/Do/Attr.rs");
                }
                pub mod Internal {
                    pub mod index {
                        include!("gen/Lean/Elab/Tactic/Do/Internal.rs");
                    }
                    pub use index::*;
                    pub mod VCGen {
                        pub mod index {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen.rs");
                        }
                        pub use index::*;
                        pub mod Context {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Context.rs");
                        }
                        pub mod Driver {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Driver.rs");
                        }
                        pub mod Entails {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Entails.rs");
                        }
                        pub mod Frontend {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Frontend.rs");
                        }
                        pub mod Reduce {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Reduce.rs");
                        }
                        pub mod RuleCache {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/RuleCache.rs");
                        }
                        pub mod RuleConstruction {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/RuleConstruction.rs");
                        }
                        pub mod Solve {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Solve.rs");
                        }
                        pub mod SpecDB {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/SpecDB.rs");
                        }
                        pub mod Util {
                            include!("gen/Lean/Elab/Tactic/Do/Internal/VCGen/Util.rs");
                        }
                    }
                }
                pub mod LetElim {
                    include!("gen/Lean/Elab/Tactic/Do/LetElim.rs");
                }
                pub mod ProofMode {
                    pub mod index {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode.rs");
                    }
                    pub use index::*;
                    pub mod Assumption {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Assumption.rs");
                    }
                    pub mod Basic {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Basic.rs");
                    }
                    pub mod Cases {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Cases.rs");
                    }
                    pub mod Clear {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Clear.rs");
                    }
                    pub mod Constructor {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Constructor.rs");
                    }
                    pub mod Delab {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Delab.rs");
                    }
                    pub mod Exact {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Exact.rs");
                    }
                    pub mod Exfalso {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Exfalso.rs");
                    }
                    pub mod Focus {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Focus.rs");
                    }
                    pub mod Frame {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Frame.rs");
                    }
                    pub mod Have {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Have.rs");
                    }
                    pub mod Intro {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Intro.rs");
                    }
                    pub mod LeftRight {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/LeftRight.rs");
                    }
                    pub mod MGoal {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/MGoal.rs");
                    }
                    pub mod Pure {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Pure.rs");
                    }
                    pub mod Refine {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Refine.rs");
                    }
                    pub mod RenameI {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/RenameI.rs");
                    }
                    pub mod Revert {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Revert.rs");
                    }
                    pub mod Specialize {
                        include!("gen/Lean/Elab/Tactic/Do/ProofMode/Specialize.rs");
                    }
                }
                pub mod Spec {
                    include!("gen/Lean/Elab/Tactic/Do/Spec.rs");
                }
                pub mod Syntax {
                    include!("gen/Lean/Elab/Tactic/Do/Syntax.rs");
                }
                pub mod VCGen {
                    pub mod index {
                        include!("gen/Lean/Elab/Tactic/Do/VCGen.rs");
                    }
                    pub use index::*;
                    pub mod Basic {
                        include!("gen/Lean/Elab/Tactic/Do/VCGen/Basic.rs");
                    }
                    pub mod Split {
                        include!("gen/Lean/Elab/Tactic/Do/VCGen/Split.rs");
                    }
                    pub mod SuggestInvariant {
                        include!("gen/Lean/Elab/Tactic/Do/VCGen/SuggestInvariant.rs");
                    }
                }
            }
            pub mod Doc {
                include!("gen/Lean/Elab/Tactic/Doc.rs");
            }
            pub mod ElabTerm {
                include!("gen/Lean/Elab/Tactic/ElabTerm.rs");
            }
            pub mod ExposeNames {
                include!("gen/Lean/Elab/Tactic/ExposeNames.rs");
            }
            pub mod Ext {
                include!("gen/Lean/Elab/Tactic/Ext.rs");
            }
            pub mod FalseOrByContra {
                include!("gen/Lean/Elab/Tactic/FalseOrByContra.rs");
            }
            pub mod Generalize {
                include!("gen/Lean/Elab/Tactic/Generalize.rs");
            }
            pub mod Grind {
                pub mod index {
                    include!("gen/Lean/Elab/Tactic/Grind.rs");
                }
                pub use index::*;
                pub mod Anchor {
                    include!("gen/Lean/Elab/Tactic/Grind/Anchor.rs");
                }
                pub mod Annotated {
                    include!("gen/Lean/Elab/Tactic/Grind/Annotated.rs");
                }
                pub mod Basic {
                    include!("gen/Lean/Elab/Tactic/Grind/Basic.rs");
                }
                pub mod BuiltinTactic {
                    include!("gen/Lean/Elab/Tactic/Grind/BuiltinTactic.rs");
                }
                pub mod Config {
                    include!("gen/Lean/Elab/Tactic/Grind/Config.rs");
                }
                pub mod DSimprocDSL {
                    include!("gen/Lean/Elab/Tactic/Grind/DSimprocDSL.rs");
                }
                pub mod DSimprocDSLBuiltin {
                    include!("gen/Lean/Elab/Tactic/Grind/DSimprocDSLBuiltin.rs");
                }
                pub mod Filter {
                    include!("gen/Lean/Elab/Tactic/Grind/Filter.rs");
                }
                pub mod Have {
                    include!("gen/Lean/Elab/Tactic/Grind/Have.rs");
                }
                pub mod Lint {
                    include!("gen/Lean/Elab/Tactic/Grind/Lint.rs");
                }
                pub mod LintExceptions {
                    include!("gen/Lean/Elab/Tactic/Grind/LintExceptions.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Elab/Tactic/Grind/Main.rs");
                }
                pub mod Param {
                    include!("gen/Lean/Elab/Tactic/Grind/Param.rs");
                }
                pub mod RegisterSymDSimp {
                    include!("gen/Lean/Elab/Tactic/Grind/RegisterSymDSimp.rs");
                }
                pub mod RegisterSymSimp {
                    include!("gen/Lean/Elab/Tactic/Grind/RegisterSymSimp.rs");
                }
                pub mod ShowState {
                    include!("gen/Lean/Elab/Tactic/Grind/ShowState.rs");
                }
                pub mod SimprocDSL {
                    include!("gen/Lean/Elab/Tactic/Grind/SimprocDSL.rs");
                }
                pub mod SimprocDSLBuiltin {
                    include!("gen/Lean/Elab/Tactic/Grind/SimprocDSLBuiltin.rs");
                }
                pub mod Sym {
                    include!("gen/Lean/Elab/Tactic/Grind/Sym.rs");
                }
                pub mod Trace {
                    include!("gen/Lean/Elab/Tactic/Grind/Trace.rs");
                }
                pub mod WithGrindTacticM {
                    include!("gen/Lean/Elab/Tactic/Grind/WithGrindTacticM.rs");
                }
            }
            pub mod Guard {
                include!("gen/Lean/Elab/Tactic/Guard.rs");
            }
            pub mod Impossible {
                include!("gen/Lean/Elab/Tactic/Impossible.rs");
            }
            pub mod Induction {
                include!("gen/Lean/Elab/Tactic/Induction.rs");
            }
            pub mod Injection {
                include!("gen/Lean/Elab/Tactic/Injection.rs");
            }
            pub mod Lets {
                include!("gen/Lean/Elab/Tactic/Lets.rs");
            }
            pub mod LibrarySearch {
                include!("gen/Lean/Elab/Tactic/LibrarySearch.rs");
            }
            pub mod Location {
                include!("gen/Lean/Elab/Tactic/Location.rs");
            }
            pub mod Match {
                include!("gen/Lean/Elab/Tactic/Match.rs");
            }
            pub mod Meta {
                include!("gen/Lean/Elab/Tactic/Meta.rs");
            }
            pub mod Monotonicity {
                include!("gen/Lean/Elab/Tactic/Monotonicity.rs");
            }
            pub mod NormCast {
                include!("gen/Lean/Elab/Tactic/NormCast.rs");
            }
            pub mod Omega {
                pub mod index {
                    include!("gen/Lean/Elab/Tactic/Omega.rs");
                }
                pub use index::*;
                pub mod Core {
                    include!("gen/Lean/Elab/Tactic/Omega/Core.rs");
                }
                pub mod Frontend {
                    include!("gen/Lean/Elab/Tactic/Omega/Frontend.rs");
                }
                pub mod MinNatAbs {
                    include!("gen/Lean/Elab/Tactic/Omega/MinNatAbs.rs");
                }
                pub mod OmegaM {
                    include!("gen/Lean/Elab/Tactic/Omega/OmegaM.rs");
                }
            }
            pub mod RCases {
                include!("gen/Lean/Elab/Tactic/RCases.rs");
            }
            pub mod RenameInaccessibles {
                include!("gen/Lean/Elab/Tactic/RenameInaccessibles.rs");
            }
            pub mod Repeat {
                include!("gen/Lean/Elab/Tactic/Repeat.rs");
            }
            pub mod Rewrite {
                include!("gen/Lean/Elab/Tactic/Rewrite.rs");
            }
            pub mod Rewrites {
                include!("gen/Lean/Elab/Tactic/Rewrites.rs");
            }
            pub mod Rfl {
                include!("gen/Lean/Elab/Tactic/Rfl.rs");
            }
            pub mod Show {
                include!("gen/Lean/Elab/Tactic/Show.rs");
            }
            pub mod ShowTerm {
                include!("gen/Lean/Elab/Tactic/ShowTerm.rs");
            }
            pub mod Simp {
                include!("gen/Lean/Elab/Tactic/Simp.rs");
            }
            pub mod SimpArith {
                include!("gen/Lean/Elab/Tactic/SimpArith.rs");
            }
            pub mod SimpTrace {
                include!("gen/Lean/Elab/Tactic/SimpTrace.rs");
            }
            pub mod Simpa {
                include!("gen/Lean/Elab/Tactic/Simpa.rs");
            }
            pub mod Simproc {
                include!("gen/Lean/Elab/Tactic/Simproc.rs");
            }
            pub mod SolveByElim {
                include!("gen/Lean/Elab/Tactic/SolveByElim.rs");
            }
            pub mod Split {
                include!("gen/Lean/Elab/Tactic/Split.rs");
            }
            pub mod Symm {
                include!("gen/Lean/Elab/Tactic/Symm.rs");
            }
            pub mod TreeTacAttr {
                include!("gen/Lean/Elab/Tactic/TreeTacAttr.rs");
            }
            pub mod Try {
                include!("gen/Lean/Elab/Tactic/Try.rs");
            }
            pub mod Unfold {
                include!("gen/Lean/Elab/Tactic/Unfold.rs");
            }
        }
        pub mod Task {
            include!("gen/Lean/Elab/Task.rs");
        }
        pub mod Term {
            pub mod index {
                include!("gen/Lean/Elab/Term.rs");
            }
            pub use index::*;
            pub mod TermElabM {
                include!("gen/Lean/Elab/Term/TermElabM.rs");
            }
        }
        pub mod Time {
            include!("gen/Lean/Elab/Time.rs");
        }
        pub mod Util {
            include!("gen/Lean/Elab/Util.rs");
        }
        pub mod WhereFinally {
            include!("gen/Lean/Elab/WhereFinally.rs");
        }
    }
    pub mod EnvExtension {
        include!("gen/Lean/EnvExtension.rs");
    }
    pub mod Environment {
        include!("gen/Lean/Environment.rs");
    }
    pub mod ErrorExplanation {
        include!("gen/Lean/ErrorExplanation.rs");
    }
    pub mod Exception {
        include!("gen/Lean/Exception.rs");
    }
    pub mod Expr {
        include!("gen/Lean/Expr.rs");
    }
    pub mod ExtraModUses {
        include!("gen/Lean/ExtraModUses.rs");
    }
    pub mod HeadIndex {
        include!("gen/Lean/HeadIndex.rs");
    }
    pub mod Hygiene {
        include!("gen/Lean/Hygiene.rs");
    }
    pub mod IdentifierSuggestion {
        include!("gen/Lean/IdentifierSuggestion.rs");
    }
    pub mod ImportingFlag {
        include!("gen/Lean/ImportingFlag.rs");
    }
    pub mod InternalExceptionId {
        include!("gen/Lean/InternalExceptionId.rs");
    }
    pub mod KeyedDeclsAttribute {
        include!("gen/Lean/KeyedDeclsAttribute.rs");
    }
    pub mod LabelAttribute {
        include!("gen/Lean/LabelAttribute.rs");
    }
    pub mod Language {
        pub mod Basic {
            include!("gen/Lean/Language/Basic.rs");
        }
        pub mod Lean {
            pub mod index {
                include!("gen/Lean/Language/Lean.rs");
            }
            pub use index::*;
            pub mod Types {
                include!("gen/Lean/Language/Lean/Types.rs");
            }
        }
        pub mod Util {
            include!("gen/Lean/Language/Util.rs");
        }
    }
    pub mod Level {
        include!("gen/Lean/Level.rs");
    }
    pub mod LibrarySuggestions {
        pub mod index {
            include!("gen/Lean/LibrarySuggestions.rs");
        }
        pub use index::*;
        pub mod Basic {
            include!("gen/Lean/LibrarySuggestions/Basic.rs");
        }
        pub mod Default {
            include!("gen/Lean/LibrarySuggestions/Default.rs");
        }
        pub mod MePo {
            include!("gen/Lean/LibrarySuggestions/MePo.rs");
        }
        pub mod SineQuaNon {
            include!("gen/Lean/LibrarySuggestions/SineQuaNon.rs");
        }
        pub mod SymbolFrequency {
            include!("gen/Lean/LibrarySuggestions/SymbolFrequency.rs");
        }
    }
    pub mod Linter {
        pub mod index {
            include!("gen/Lean/Linter.rs");
        }
        pub use index::*;
        pub mod Basic {
            include!("gen/Lean/Linter/Basic.rs");
        }
        pub mod Builtin {
            include!("gen/Lean/Linter/Builtin.rs");
        }
        pub mod CheckUnivs {
            include!("gen/Lean/Linter/CheckUnivs.rs");
        }
        pub mod Coe {
            include!("gen/Lean/Linter/Coe.rs");
        }
        pub mod ConstructorAsVariable {
            include!("gen/Lean/Linter/ConstructorAsVariable.rs");
        }
        pub mod DefProp {
            include!("gen/Lean/Linter/DefProp.rs");
        }
        pub mod Deprecated {
            include!("gen/Lean/Linter/Deprecated.rs");
        }
        pub mod DocsOnAlt {
            include!("gen/Lean/Linter/DocsOnAlt.rs");
        }
        pub mod EnvLinter {
            pub mod index {
                include!("gen/Lean/Linter/EnvLinter.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Linter/EnvLinter/Basic.rs");
            }
            pub mod Frontend {
                include!("gen/Lean/Linter/EnvLinter/Frontend.rs");
            }
            pub mod Nolint {
                include!("gen/Lean/Linter/EnvLinter/Nolint.rs");
            }
        }
        pub mod Extra {
            pub mod index {
                include!("gen/Lean/Linter/Extra.rs");
            }
            pub use index::*;
            pub mod DupNamespace {
                include!("gen/Lean/Linter/Extra/DupNamespace.rs");
            }
            pub mod UnnecessarySeqFocus {
                include!("gen/Lean/Linter/Extra/UnnecessarySeqFocus.rs");
            }
            pub mod UnreachableTactic {
                include!("gen/Lean/Linter/Extra/UnreachableTactic.rs");
            }
            pub mod UnusedDecidableInType {
                include!("gen/Lean/Linter/Extra/UnusedDecidableInType.rs");
            }
        }
        pub mod GlobalAttributeIn {
            include!("gen/Lean/Linter/GlobalAttributeIn.rs");
        }
        pub mod Init {
            include!("gen/Lean/Linter/Init.rs");
        }
        pub mod List {
            include!("gen/Lean/Linter/List.rs");
        }
        pub mod MissingDocs {
            include!("gen/Lean/Linter/MissingDocs.rs");
        }
        pub mod Omit {
            include!("gen/Lean/Linter/Omit.rs");
        }
        pub mod PersistentLintLog {
            include!("gen/Lean/Linter/PersistentLintLog.rs");
        }
        pub mod Sets {
            include!("gen/Lean/Linter/Sets.rs");
        }
        pub mod TacticTypeCheck {
            include!("gen/Lean/Linter/TacticTypeCheck.rs");
        }
        pub mod UnusedSimpArgs {
            include!("gen/Lean/Linter/UnusedSimpArgs.rs");
        }
        pub mod UnusedVariables {
            include!("gen/Lean/Linter/UnusedVariables.rs");
        }
        pub mod Util {
            include!("gen/Lean/Linter/Util.rs");
        }
    }
    pub mod LoadDynlib {
        include!("gen/Lean/LoadDynlib.rs");
    }
    pub mod LocalContext {
        include!("gen/Lean/LocalContext.rs");
    }
    pub mod Log {
        include!("gen/Lean/Log.rs");
    }
    pub mod Message {
        include!("gen/Lean/Message.rs");
    }
    pub mod Meta {
        pub mod index {
            include!("gen/Lean/Meta.rs");
        }
        pub use index::*;
        pub mod ACLt {
            include!("gen/Lean/Meta/ACLt.rs");
        }
        pub mod AbstractMVars {
            include!("gen/Lean/Meta/AbstractMVars.rs");
        }
        pub mod AbstractNestedProofs {
            include!("gen/Lean/Meta/AbstractNestedProofs.rs");
        }
        pub mod AppBuilder {
            include!("gen/Lean/Meta/AppBuilder.rs");
        }
        pub mod ArgsPacker {
            pub mod index {
                include!("gen/Lean/Meta/ArgsPacker.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Meta/ArgsPacker/Basic.rs");
            }
        }
        pub mod Basic {
            include!("gen/Lean/Meta/Basic.rs");
        }
        pub mod BinderNameHint {
            include!("gen/Lean/Meta/BinderNameHint.rs");
        }
        pub mod Canonicalizer {
            include!("gen/Lean/Meta/Canonicalizer.rs");
        }
        pub mod CasesInfo {
            include!("gen/Lean/Meta/CasesInfo.rs");
        }
        pub mod Check {
            include!("gen/Lean/Meta/Check.rs");
        }
        pub mod CheckTactic {
            include!("gen/Lean/Meta/CheckTactic.rs");
        }
        pub mod Closure {
            include!("gen/Lean/Meta/Closure.rs");
        }
        pub mod Coe {
            include!("gen/Lean/Meta/Coe.rs");
        }
        pub mod CoeAttr {
            include!("gen/Lean/Meta/CoeAttr.rs");
        }
        pub mod CollectFVars {
            include!("gen/Lean/Meta/CollectFVars.rs");
        }
        pub mod CollectMVars {
            include!("gen/Lean/Meta/CollectMVars.rs");
        }
        pub mod CompletionName {
            include!("gen/Lean/Meta/CompletionName.rs");
        }
        pub mod CongrTheorems {
            include!("gen/Lean/Meta/CongrTheorems.rs");
        }
        pub mod Constructions {
            pub mod index {
                include!("gen/Lean/Meta/Constructions.rs");
            }
            pub use index::*;
            pub mod BRecOn {
                include!("gen/Lean/Meta/Constructions/BRecOn.rs");
            }
            pub mod CasesOn {
                include!("gen/Lean/Meta/Constructions/CasesOn.rs");
            }
            pub mod CasesOnSameCtor {
                include!("gen/Lean/Meta/Constructions/CasesOnSameCtor.rs");
            }
            pub mod CtorElim {
                include!("gen/Lean/Meta/Constructions/CtorElim.rs");
            }
            pub mod CtorIdx {
                include!("gen/Lean/Meta/Constructions/CtorIdx.rs");
            }
            pub mod NoConfusion {
                include!("gen/Lean/Meta/Constructions/NoConfusion.rs");
            }
            pub mod RecOn {
                include!("gen/Lean/Meta/Constructions/RecOn.rs");
            }
            pub mod SparseCasesOn {
                include!("gen/Lean/Meta/Constructions/SparseCasesOn.rs");
            }
            pub mod SparseCasesOnEq {
                include!("gen/Lean/Meta/Constructions/SparseCasesOnEq.rs");
            }
        }
        pub mod CtorIdxHInj {
            include!("gen/Lean/Meta/CtorIdxHInj.rs");
        }
        pub mod CtorRecognizer {
            include!("gen/Lean/Meta/CtorRecognizer.rs");
        }
        pub mod DecLevel {
            include!("gen/Lean/Meta/DecLevel.rs");
        }
        pub mod Diagnostics {
            include!("gen/Lean/Meta/Diagnostics.rs");
        }
        pub mod DiscrTree {
            pub mod index {
                include!("gen/Lean/Meta/DiscrTree.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Meta/DiscrTree/Basic.rs");
            }
            pub mod Main {
                include!("gen/Lean/Meta/DiscrTree/Main.rs");
            }
            pub mod Types {
                include!("gen/Lean/Meta/DiscrTree/Types.rs");
            }
            pub mod Util {
                include!("gen/Lean/Meta/DiscrTree/Util.rs");
            }
        }
        pub mod Eqns {
            include!("gen/Lean/Meta/Eqns.rs");
        }
        pub mod Eval {
            include!("gen/Lean/Meta/Eval.rs");
        }
        pub mod ExprDefEq {
            include!("gen/Lean/Meta/ExprDefEq.rs");
        }
        pub mod ExprLens {
            include!("gen/Lean/Meta/ExprLens.rs");
        }
        pub mod ExprTraverse {
            include!("gen/Lean/Meta/ExprTraverse.rs");
        }
        pub mod ForEachExpr {
            include!("gen/Lean/Meta/ForEachExpr.rs");
        }
        pub mod FunInfo {
            include!("gen/Lean/Meta/FunInfo.rs");
        }
        pub mod GeneralizeTelescope {
            include!("gen/Lean/Meta/GeneralizeTelescope.rs");
        }
        pub mod GeneralizeVars {
            include!("gen/Lean/Meta/GeneralizeVars.rs");
        }
        pub mod GetUnfoldableConst {
            include!("gen/Lean/Meta/GetUnfoldableConst.rs");
        }
        pub mod HasAssignableMVar {
            include!("gen/Lean/Meta/HasAssignableMVar.rs");
        }
        pub mod HasNotBit {
            include!("gen/Lean/Meta/HasNotBit.rs");
        }
        pub mod HaveTelescope {
            include!("gen/Lean/Meta/HaveTelescope.rs");
        }
        pub mod Hint {
            include!("gen/Lean/Meta/Hint.rs");
        }
        pub mod IndPredBelow {
            include!("gen/Lean/Meta/IndPredBelow.rs");
        }
        pub mod Inductive {
            include!("gen/Lean/Meta/Inductive.rs");
        }
        pub mod InferType {
            include!("gen/Lean/Meta/InferType.rs");
        }
        pub mod Injective {
            include!("gen/Lean/Meta/Injective.rs");
        }
        pub mod Instances {
            include!("gen/Lean/Meta/Instances.rs");
        }
        pub mod IntInstTesters {
            include!("gen/Lean/Meta/IntInstTesters.rs");
        }
        pub mod Iterator {
            include!("gen/Lean/Meta/Iterator.rs");
        }
        pub mod KAbstract {
            include!("gen/Lean/Meta/KAbstract.rs");
        }
        pub mod KExprMap {
            include!("gen/Lean/Meta/KExprMap.rs");
        }
        pub mod LazyDiscrTree {
            include!("gen/Lean/Meta/LazyDiscrTree.rs");
        }
        pub mod LetToHave {
            include!("gen/Lean/Meta/LetToHave.rs");
        }
        pub mod LevelDefEq {
            include!("gen/Lean/Meta/LevelDefEq.rs");
        }
        pub mod LitValues {
            include!("gen/Lean/Meta/LitValues.rs");
        }
        pub mod Match {
            pub mod index {
                include!("gen/Lean/Meta/Match.rs");
            }
            pub use index::*;
            pub mod AltTelescopes {
                include!("gen/Lean/Meta/Match/AltTelescopes.rs");
            }
            pub mod Basic {
                include!("gen/Lean/Meta/Match/Basic.rs");
            }
            pub mod CaseArraySizes {
                include!("gen/Lean/Meta/Match/CaseArraySizes.rs");
            }
            pub mod CaseValues {
                include!("gen/Lean/Meta/Match/CaseValues.rs");
            }
            pub mod MVarRenaming {
                include!("gen/Lean/Meta/Match/MVarRenaming.rs");
            }
            pub mod Match {
                include!("gen/Lean/Meta/Match/Match.rs");
            }
            pub mod MatchEqs {
                include!("gen/Lean/Meta/Match/MatchEqs.rs");
            }
            pub mod MatchEqsExt {
                include!("gen/Lean/Meta/Match/MatchEqsExt.rs");
            }
            pub mod MatchPatternAttr {
                include!("gen/Lean/Meta/Match/MatchPatternAttr.rs");
            }
            pub mod MatcherApp {
                pub mod index {
                    include!("gen/Lean/Meta/Match/MatcherApp.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("gen/Lean/Meta/Match/MatcherApp/Basic.rs");
                }
                pub mod Transform {
                    include!("gen/Lean/Meta/Match/MatcherApp/Transform.rs");
                }
            }
            pub mod MatcherInfo {
                include!("gen/Lean/Meta/Match/MatcherInfo.rs");
            }
            pub mod NamedPatterns {
                include!("gen/Lean/Meta/Match/NamedPatterns.rs");
            }
            pub mod Rewrite {
                include!("gen/Lean/Meta/Match/Rewrite.rs");
            }
            pub mod SimpH {
                include!("gen/Lean/Meta/Match/SimpH.rs");
            }
            pub mod SolveOverlap {
                include!("gen/Lean/Meta/Match/SolveOverlap.rs");
            }
            pub mod Value {
                include!("gen/Lean/Meta/Match/Value.rs");
            }
        }
        pub mod MatchUtil {
            include!("gen/Lean/Meta/MatchUtil.rs");
        }
        pub mod MethodSpecs {
            include!("gen/Lean/Meta/MethodSpecs.rs");
        }
        pub mod MkIffOfInductiveProp {
            include!("gen/Lean/Meta/MkIffOfInductiveProp.rs");
        }
        pub mod MonadSimp {
            include!("gen/Lean/Meta/MonadSimp.rs");
        }
        pub mod NatInstTesters {
            include!("gen/Lean/Meta/NatInstTesters.rs");
        }
        pub mod NatTable {
            include!("gen/Lean/Meta/NatTable.rs");
        }
        pub mod Native {
            include!("gen/Lean/Meta/Native.rs");
        }
        pub mod Offset {
            include!("gen/Lean/Meta/Offset.rs");
        }
        pub mod Order {
            include!("gen/Lean/Meta/Order.rs");
        }
        pub mod PPBinder {
            include!("gen/Lean/Meta/PPBinder.rs");
        }
        pub mod PPGoal {
            include!("gen/Lean/Meta/PPGoal.rs");
        }
        pub mod PProdN {
            include!("gen/Lean/Meta/PProdN.rs");
        }
        pub mod ProdN {
            include!("gen/Lean/Meta/ProdN.rs");
        }
        pub mod RecExt {
            include!("gen/Lean/Meta/RecExt.rs");
        }
        pub mod RecursorInfo {
            include!("gen/Lean/Meta/RecursorInfo.rs");
        }
        pub mod Reduce {
            include!("gen/Lean/Meta/Reduce.rs");
        }
        pub mod ReduceEval {
            include!("gen/Lean/Meta/ReduceEval.rs");
        }
        pub mod SameCtorUtils {
            include!("gen/Lean/Meta/SameCtorUtils.rs");
        }
        pub mod SizeOf {
            include!("gen/Lean/Meta/SizeOf.rs");
        }
        pub mod Sorry {
            include!("gen/Lean/Meta/Sorry.rs");
        }
        pub mod SplitSparseCasesOn {
            include!("gen/Lean/Meta/SplitSparseCasesOn.rs");
        }
        pub mod StringLitProof {
            include!("gen/Lean/Meta/StringLitProof.rs");
        }
        pub mod Structure {
            include!("gen/Lean/Meta/Structure.rs");
        }
        pub mod Sym {
            pub mod index {
                include!("gen/Lean/Meta/Sym.rs");
            }
            pub use index::*;
            pub mod AbstractS {
                include!("gen/Lean/Meta/Sym/AbstractS.rs");
            }
            pub mod AlphaShareBuilder {
                include!("gen/Lean/Meta/Sym/AlphaShareBuilder.rs");
            }
            pub mod AlphaShareCommon {
                include!("gen/Lean/Meta/Sym/AlphaShareCommon.rs");
            }
            pub mod Apply {
                include!("gen/Lean/Meta/Sym/Apply.rs");
            }
            pub mod Arith {
                pub mod index {
                    include!("gen/Lean/Meta/Sym/Arith.rs");
                }
                pub use index::*;
                pub mod Classify {
                    include!("gen/Lean/Meta/Sym/Arith/Classify.rs");
                }
                pub mod DenoteExpr {
                    include!("gen/Lean/Meta/Sym/Arith/DenoteExpr.rs");
                }
                pub mod EvalNum {
                    include!("gen/Lean/Meta/Sym/Arith/EvalNum.rs");
                }
                pub mod Functions {
                    include!("gen/Lean/Meta/Sym/Arith/Functions.rs");
                }
                pub mod MonadCanon {
                    include!("gen/Lean/Meta/Sym/Arith/MonadCanon.rs");
                }
                pub mod MonadRing {
                    include!("gen/Lean/Meta/Sym/Arith/MonadRing.rs");
                }
                pub mod MonadSemiring {
                    include!("gen/Lean/Meta/Sym/Arith/MonadSemiring.rs");
                }
                pub mod MonadVar {
                    include!("gen/Lean/Meta/Sym/Arith/MonadVar.rs");
                }
                pub mod Poly {
                    include!("gen/Lean/Meta/Sym/Arith/Poly.rs");
                }
                pub mod Reify {
                    include!("gen/Lean/Meta/Sym/Arith/Reify.rs");
                }
                pub mod ToExpr {
                    include!("gen/Lean/Meta/Sym/Arith/ToExpr.rs");
                }
                pub mod Types {
                    include!("gen/Lean/Meta/Sym/Arith/Types.rs");
                }
                pub mod VarRename {
                    include!("gen/Lean/Meta/Sym/Arith/VarRename.rs");
                }
            }
            pub mod Canon {
                include!("gen/Lean/Meta/Sym/Canon.rs");
            }
            pub mod DSimp {
                pub mod index {
                    include!("gen/Lean/Meta/Sym/DSimp.rs");
                }
                pub use index::*;
                pub mod App {
                    include!("gen/Lean/Meta/Sym/DSimp/App.rs");
                }
                pub mod DSimpM {
                    include!("gen/Lean/Meta/Sym/DSimp/DSimpM.rs");
                }
                pub mod DSimproc {
                    include!("gen/Lean/Meta/Sym/DSimp/DSimproc.rs");
                }
                pub mod Forall {
                    include!("gen/Lean/Meta/Sym/DSimp/Forall.rs");
                }
                pub mod Lambda {
                    include!("gen/Lean/Meta/Sym/DSimp/Lambda.rs");
                }
                pub mod Let {
                    include!("gen/Lean/Meta/Sym/DSimp/Let.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Meta/Sym/DSimp/Main.rs");
                }
                pub mod Reduce {
                    include!("gen/Lean/Meta/Sym/DSimp/Reduce.rs");
                }
                pub mod Result {
                    include!("gen/Lean/Meta/Sym/DSimp/Result.rs");
                }
                pub mod Variant {
                    include!("gen/Lean/Meta/Sym/DSimp/Variant.rs");
                }
            }
            pub mod Eta {
                include!("gen/Lean/Meta/Sym/Eta.rs");
            }
            pub mod ExprPtr {
                include!("gen/Lean/Meta/Sym/ExprPtr.rs");
            }
            pub mod Grind {
                include!("gen/Lean/Meta/Sym/Grind.rs");
            }
            pub mod InferType {
                include!("gen/Lean/Meta/Sym/InferType.rs");
            }
            pub mod InstantiateMVarsS {
                include!("gen/Lean/Meta/Sym/InstantiateMVarsS.rs");
            }
            pub mod InstantiateS {
                include!("gen/Lean/Meta/Sym/InstantiateS.rs");
            }
            pub mod Intro {
                include!("gen/Lean/Meta/Sym/Intro.rs");
            }
            pub mod IsClass {
                include!("gen/Lean/Meta/Sym/IsClass.rs");
            }
            pub mod LitValues {
                include!("gen/Lean/Meta/Sym/LitValues.rs");
            }
            pub mod LooseBVarsS {
                include!("gen/Lean/Meta/Sym/LooseBVarsS.rs");
            }
            pub mod MaxFVar {
                include!("gen/Lean/Meta/Sym/MaxFVar.rs");
            }
            pub mod Offset {
                include!("gen/Lean/Meta/Sym/Offset.rs");
            }
            pub mod Pattern {
                include!("gen/Lean/Meta/Sym/Pattern.rs");
            }
            pub mod ProofInstInfo {
                include!("gen/Lean/Meta/Sym/ProofInstInfo.rs");
            }
            pub mod ReplaceS {
                include!("gen/Lean/Meta/Sym/ReplaceS.rs");
            }
            pub mod Simp {
                pub mod index {
                    include!("gen/Lean/Meta/Sym/Simp.rs");
                }
                pub use index::*;
                pub mod App {
                    include!("gen/Lean/Meta/Sym/Simp/App.rs");
                }
                pub mod Attr {
                    include!("gen/Lean/Meta/Sym/Simp/Attr.rs");
                }
                pub mod CongrInfo {
                    include!("gen/Lean/Meta/Sym/Simp/CongrInfo.rs");
                }
                pub mod ControlFlow {
                    include!("gen/Lean/Meta/Sym/Simp/ControlFlow.rs");
                }
                pub mod Debug {
                    include!("gen/Lean/Meta/Sym/Simp/Debug.rs");
                }
                pub mod Discharger {
                    include!("gen/Lean/Meta/Sym/Simp/Discharger.rs");
                }
                pub mod DiscrTree {
                    include!("gen/Lean/Meta/Sym/Simp/DiscrTree.rs");
                }
                pub mod EvalGround {
                    include!("gen/Lean/Meta/Sym/Simp/EvalGround.rs");
                }
                pub mod Forall {
                    include!("gen/Lean/Meta/Sym/Simp/Forall.rs");
                }
                pub mod Goal {
                    include!("gen/Lean/Meta/Sym/Simp/Goal.rs");
                }
                pub mod Have {
                    include!("gen/Lean/Meta/Sym/Simp/Have.rs");
                }
                pub mod Lambda {
                    include!("gen/Lean/Meta/Sym/Simp/Lambda.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Meta/Sym/Simp/Main.rs");
                }
                pub mod RegisterCommand {
                    include!("gen/Lean/Meta/Sym/Simp/RegisterCommand.rs");
                }
                pub mod Result {
                    include!("gen/Lean/Meta/Sym/Simp/Result.rs");
                }
                pub mod Rewrite {
                    include!("gen/Lean/Meta/Sym/Simp/Rewrite.rs");
                }
                pub mod SimpM {
                    include!("gen/Lean/Meta/Sym/Simp/SimpM.rs");
                }
                pub mod Simproc {
                    include!("gen/Lean/Meta/Sym/Simp/Simproc.rs");
                }
                pub mod Telescope {
                    include!("gen/Lean/Meta/Sym/Simp/Telescope.rs");
                }
                pub mod Theorems {
                    include!("gen/Lean/Meta/Sym/Simp/Theorems.rs");
                }
                pub mod Variant {
                    include!("gen/Lean/Meta/Sym/Simp/Variant.rs");
                }
            }
            pub mod SymM {
                include!("gen/Lean/Meta/Sym/SymM.rs");
            }
            pub mod SynthInstance {
                include!("gen/Lean/Meta/Sym/SynthInstance.rs");
            }
            pub mod Util {
                include!("gen/Lean/Meta/Sym/Util.rs");
            }
        }
        pub mod SynthInstance {
            include!("gen/Lean/Meta/SynthInstance.rs");
        }
        pub mod Tactic {
            pub mod index {
                include!("gen/Lean/Meta/Tactic.rs");
            }
            pub use index::*;
            pub mod AC {
                pub mod index {
                    include!("gen/Lean/Meta/Tactic/AC.rs");
                }
                pub use index::*;
                pub mod Main {
                    include!("gen/Lean/Meta/Tactic/AC/Main.rs");
                }
            }
            pub mod Acyclic {
                include!("gen/Lean/Meta/Tactic/Acyclic.rs");
            }
            pub mod Apply {
                include!("gen/Lean/Meta/Tactic/Apply.rs");
            }
            pub mod Assert {
                include!("gen/Lean/Meta/Tactic/Assert.rs");
            }
            pub mod Assumption {
                include!("gen/Lean/Meta/Tactic/Assumption.rs");
            }
            pub mod AuxLemma {
                include!("gen/Lean/Meta/Tactic/AuxLemma.rs");
            }
            pub mod BVDecide {
                pub mod index {
                    include!("gen/Lean/Meta/Tactic/BVDecide.rs");
                }
                pub use index::*;
                pub mod Attr {
                    include!("gen/Lean/Meta/Tactic/BVDecide/Attr.rs");
                }
                pub mod Counterexample {
                    include!("gen/Lean/Meta/Tactic/BVDecide/Counterexample.rs");
                }
                pub mod External {
                    include!("gen/Lean/Meta/Tactic/BVDecide/External.rs");
                }
                pub mod LRAT {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/BVDecide/LRAT.rs");
                    }
                    pub use index::*;
                    pub mod Cert {
                        include!("gen/Lean/Meta/Tactic/BVDecide/LRAT/Cert.rs");
                    }
                    pub mod Trim {
                        include!("gen/Lean/Meta/Tactic/BVDecide/LRAT/Trim.rs");
                    }
                }
                pub mod Main {
                    include!("gen/Lean/Meta/Tactic/BVDecide/Main.rs");
                }
                pub mod Normalize {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize.rs");
                    }
                    pub use index::*;
                    pub mod AC {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/AC.rs");
                    }
                    pub mod AndFlatten {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/AndFlatten.rs");
                    }
                    pub mod ApplyControlFlow {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/ApplyControlFlow.rs");
                    }
                    pub mod Basic {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/Basic.rs");
                    }
                    pub mod EmbeddedConstraint {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/EmbeddedConstraint.rs");
                    }
                    pub mod Enums {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/Enums.rs");
                    }
                    pub mod IntToBitVec {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/IntToBitVec.rs");
                    }
                    pub mod Rewrite {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/Rewrite.rs");
                    }
                    pub mod ShortCircuit {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/ShortCircuit.rs");
                    }
                    pub mod Simproc {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/Simproc.rs");
                    }
                    pub mod Structures {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/Structures.rs");
                    }
                    pub mod TypeAnalysis {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Normalize/TypeAnalysis.rs");
                    }
                }
                pub mod Prover {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Prover.rs");
                    }
                    pub use index::*;
                    pub mod Basic {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Prover/Basic.rs");
                    }
                    pub mod Bitblast {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.rs");
                    }
                }
                pub mod Reflect {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect.rs");
                    }
                    pub use index::*;
                    pub mod Basic {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/Basic.rs");
                    }
                    pub mod ReifiedBVExpr {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedBVExpr.rs");
                    }
                    pub mod ReifiedBVLogical {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedBVLogical.rs");
                    }
                    pub mod ReifiedBVPred {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedBVPred.rs");
                    }
                    pub mod ReifiedLemmas {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedLemmas.rs");
                    }
                    pub mod Reify {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/Reify.rs");
                    }
                    pub mod SatAtBVLogical {
                        include!("gen/Lean/Meta/Tactic/BVDecide/Reflect/SatAtBVLogical.rs");
                    }
                }
                pub mod TacticContext {
                    include!("gen/Lean/Meta/Tactic/BVDecide/TacticContext.rs");
                }
            }
            pub mod Backtrack {
                include!("gen/Lean/Meta/Tactic/Backtrack.rs");
            }
            pub mod Cases {
                include!("gen/Lean/Meta/Tactic/Cases.rs");
            }
            pub mod CasesOnStuckLHS {
                include!("gen/Lean/Meta/Tactic/CasesOnStuckLHS.rs");
            }
            pub mod Cbv {
                pub mod index {
                    include!("gen/Lean/Meta/Tactic/Cbv.rs");
                }
                pub use index::*;
                pub mod BuiltinCbvSimprocs {
                    pub mod Array {
                        include!("gen/Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/Array.rs");
                    }
                    pub mod Core {
                        include!("gen/Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/Core.rs");
                    }
                    pub mod String {
                        include!("gen/Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/String.rs");
                    }
                }
                pub mod CbvEvalExt {
                    include!("gen/Lean/Meta/Tactic/Cbv/CbvEvalExt.rs");
                }
                pub mod CbvSimproc {
                    include!("gen/Lean/Meta/Tactic/Cbv/CbvSimproc.rs");
                }
                pub mod ControlFlow {
                    include!("gen/Lean/Meta/Tactic/Cbv/ControlFlow.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Meta/Tactic/Cbv/Main.rs");
                }
                pub mod Opaque {
                    include!("gen/Lean/Meta/Tactic/Cbv/Opaque.rs");
                }
                pub mod TheoremsLookup {
                    include!("gen/Lean/Meta/Tactic/Cbv/TheoremsLookup.rs");
                }
                pub mod Util {
                    include!("gen/Lean/Meta/Tactic/Cbv/Util.rs");
                }
            }
            pub mod Cleanup {
                include!("gen/Lean/Meta/Tactic/Cleanup.rs");
            }
            pub mod Clear {
                include!("gen/Lean/Meta/Tactic/Clear.rs");
            }
            pub mod Congr {
                include!("gen/Lean/Meta/Tactic/Congr.rs");
            }
            pub mod Constructor {
                include!("gen/Lean/Meta/Tactic/Constructor.rs");
            }
            pub mod Contradiction {
                include!("gen/Lean/Meta/Tactic/Contradiction.rs");
            }
            pub mod Delta {
                include!("gen/Lean/Meta/Tactic/Delta.rs");
            }
            pub mod ElimInfo {
                include!("gen/Lean/Meta/Tactic/ElimInfo.rs");
            }
            pub mod ExposeNames {
                include!("gen/Lean/Meta/Tactic/ExposeNames.rs");
            }
            pub mod Ext {
                include!("gen/Lean/Meta/Tactic/Ext.rs");
            }
            pub mod FVarSubst {
                include!("gen/Lean/Meta/Tactic/FVarSubst.rs");
            }
            pub mod FunInd {
                include!("gen/Lean/Meta/Tactic/FunInd.rs");
            }
            pub mod FunIndCollect {
                include!("gen/Lean/Meta/Tactic/FunIndCollect.rs");
            }
            pub mod FunIndInfo {
                include!("gen/Lean/Meta/Tactic/FunIndInfo.rs");
            }
            pub mod Generalize {
                include!("gen/Lean/Meta/Tactic/Generalize.rs");
            }
            pub mod Grind {
                pub mod index {
                    include!("gen/Lean/Meta/Tactic/Grind.rs");
                }
                pub use index::*;
                pub mod AC {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/Grind/AC.rs");
                    }
                    pub use index::*;
                    pub mod Action {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Action.rs");
                    }
                    pub mod DenoteExpr {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/DenoteExpr.rs");
                    }
                    pub mod Eq {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Eq.rs");
                    }
                    pub mod Internalize {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Internalize.rs");
                    }
                    pub mod Inv {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Inv.rs");
                    }
                    pub mod PP {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/PP.rs");
                    }
                    pub mod Proof {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Proof.rs");
                    }
                    pub mod Seq {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Seq.rs");
                    }
                    pub mod ToExpr {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/ToExpr.rs");
                    }
                    pub mod Types {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Types.rs");
                    }
                    pub mod Util {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Util.rs");
                    }
                    pub mod Var {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/Var.rs");
                    }
                    pub mod VarRename {
                        include!("gen/Lean/Meta/Tactic/Grind/AC/VarRename.rs");
                    }
                }
                pub mod Action {
                    include!("gen/Lean/Meta/Tactic/Grind/Action.rs");
                }
                pub mod Anchor {
                    include!("gen/Lean/Meta/Tactic/Grind/Anchor.rs");
                }
                pub mod Arith {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith.rs");
                    }
                    pub use index::*;
                    pub mod CommRing {
                        pub mod index {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing.rs");
                        }
                        pub use index::*;
                        pub mod Action {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Action.rs");
                        }
                        pub mod DenoteExpr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/DenoteExpr.rs");
                        }
                        pub mod EqCnstr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/EqCnstr.rs");
                        }
                        pub mod Functions {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Functions.rs");
                        }
                        pub mod Internalize {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Internalize.rs");
                        }
                        pub mod Inv {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Inv.rs");
                        }
                        pub mod MonadRing {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/MonadRing.rs");
                        }
                        pub mod MonadSemiring {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/MonadSemiring.rs");
                        }
                        pub mod NonCommRingM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/NonCommRingM.rs");
                        }
                        pub mod NonCommSemiringM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/NonCommSemiringM.rs");
                        }
                        pub mod PP {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/PP.rs");
                        }
                        pub mod Power {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Power.rs");
                        }
                        pub mod Proof {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Proof.rs");
                        }
                        pub mod Reify {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Reify.rs");
                        }
                        pub mod RingId {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/RingId.rs");
                        }
                        pub mod RingM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/RingM.rs");
                        }
                        pub mod SafePoly {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/SafePoly.rs");
                        }
                        pub mod SemiringM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/SemiringM.rs");
                        }
                        pub mod Types {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/CommRing/Types.rs");
                        }
                    }
                    pub mod Cutsat {
                        pub mod index {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat.rs");
                        }
                        pub use index::*;
                        pub mod Action {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Action.rs");
                        }
                        pub mod CommRing {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/CommRing.rs");
                        }
                        pub mod DvdCnstr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/DvdCnstr.rs");
                        }
                        pub mod EqCnstr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/EqCnstr.rs");
                        }
                        pub mod Inv {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Inv.rs");
                        }
                        pub mod LeCnstr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/LeCnstr.rs");
                        }
                        pub mod MBTC {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/MBTC.rs");
                        }
                        pub mod Model {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Model.rs");
                        }
                        pub mod Nat {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Nat.rs");
                        }
                        pub mod Norm {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Norm.rs");
                        }
                        pub mod Proof {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.rs");
                        }
                        pub mod ReorderVars {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/ReorderVars.rs");
                        }
                        pub mod Search {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Search.rs");
                        }
                        pub mod SearchM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/SearchM.rs");
                        }
                        pub mod ToInt {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/ToInt.rs");
                        }
                        pub mod ToIntInfo {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/ToIntInfo.rs");
                        }
                        pub mod Types {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Types.rs");
                        }
                        pub mod Util {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Util.rs");
                        }
                        pub mod Var {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/Var.rs");
                        }
                        pub mod VarRename {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/VarRename.rs");
                        }
                    }
                    pub mod EvalNum {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/EvalNum.rs");
                    }
                    pub mod FieldNormNum {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/FieldNormNum.rs");
                    }
                    pub mod Insts {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Insts.rs");
                    }
                    pub mod IsRelevant {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/IsRelevant.rs");
                    }
                    pub mod Linear {
                        pub mod index {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear.rs");
                        }
                        pub use index::*;
                        pub mod Action {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Action.rs");
                        }
                        pub mod Den {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Den.rs");
                        }
                        pub mod DenoteExpr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/DenoteExpr.rs");
                        }
                        pub mod IneqCnstr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/IneqCnstr.rs");
                        }
                        pub mod Internalize {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Internalize.rs");
                        }
                        pub mod Inv {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Inv.rs");
                        }
                        pub mod LinearM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/LinearM.rs");
                        }
                        pub mod MBTC {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/MBTC.rs");
                        }
                        pub mod Model {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Model.rs");
                        }
                        pub mod OfNatModule {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/OfNatModule.rs");
                        }
                        pub mod PP {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/PP.rs");
                        }
                        pub mod Proof {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Proof.rs");
                        }
                        pub mod PropagateEq {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/PropagateEq.rs");
                        }
                        pub mod Reify {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Reify.rs");
                        }
                        pub mod Search {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Search.rs");
                        }
                        pub mod SearchM {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/SearchM.rs");
                        }
                        pub mod StructId {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/StructId.rs");
                        }
                        pub mod ToExpr {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/ToExpr.rs");
                        }
                        pub mod Types {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Types.rs");
                        }
                        pub mod Util {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Util.rs");
                        }
                        pub mod Var {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/Var.rs");
                        }
                        pub mod VarRename {
                            include!("gen/Lean/Meta/Tactic/Grind/Arith/Linear/VarRename.rs");
                        }
                    }
                    pub mod Main {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Main.rs");
                    }
                    pub mod Model {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Model.rs");
                    }
                    pub mod ModelUtil {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/ModelUtil.rs");
                    }
                    pub mod Propagate {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Propagate.rs");
                    }
                    pub mod Simproc {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Simproc.rs");
                    }
                    pub mod Types {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Types.rs");
                    }
                    pub mod Util {
                        include!("gen/Lean/Meta/Tactic/Grind/Arith/Util.rs");
                    }
                }
                pub mod Attr {
                    include!("gen/Lean/Meta/Tactic/Grind/Attr.rs");
                }
                pub mod Beta {
                    include!("gen/Lean/Meta/Tactic/Grind/Beta.rs");
                }
                pub mod Cases {
                    include!("gen/Lean/Meta/Tactic/Grind/Cases.rs");
                }
                pub mod CasesMatch {
                    include!("gen/Lean/Meta/Tactic/Grind/CasesMatch.rs");
                }
                pub mod CastLike {
                    include!("gen/Lean/Meta/Tactic/Grind/CastLike.rs");
                }
                pub mod CheckResult {
                    include!("gen/Lean/Meta/Tactic/Grind/CheckResult.rs");
                }
                pub mod CollectParams {
                    include!("gen/Lean/Meta/Tactic/Grind/CollectParams.rs");
                }
                pub mod Core {
                    include!("gen/Lean/Meta/Tactic/Grind/Core.rs");
                }
                pub mod Ctor {
                    include!("gen/Lean/Meta/Tactic/Grind/Ctor.rs");
                }
                pub mod CtorIdx {
                    include!("gen/Lean/Meta/Tactic/Grind/CtorIdx.rs");
                }
                pub mod Diseq {
                    include!("gen/Lean/Meta/Tactic/Grind/Diseq.rs");
                }
                pub mod EMatch {
                    include!("gen/Lean/Meta/Tactic/Grind/EMatch.rs");
                }
                pub mod EMatchAction {
                    include!("gen/Lean/Meta/Tactic/Grind/EMatchAction.rs");
                }
                pub mod EMatchTheorem {
                    include!("gen/Lean/Meta/Tactic/Grind/EMatchTheorem.rs");
                }
                pub mod EMatchTheoremParam {
                    include!("gen/Lean/Meta/Tactic/Grind/EMatchTheoremParam.rs");
                }
                pub mod EMatchTheoremPtr {
                    include!("gen/Lean/Meta/Tactic/Grind/EMatchTheoremPtr.rs");
                }
                pub mod EqResolution {
                    include!("gen/Lean/Meta/Tactic/Grind/EqResolution.rs");
                }
                pub mod Ext {
                    include!("gen/Lean/Meta/Tactic/Grind/Ext.rs");
                }
                pub mod ExtAttr {
                    include!("gen/Lean/Meta/Tactic/Grind/ExtAttr.rs");
                }
                pub mod Extension {
                    include!("gen/Lean/Meta/Tactic/Grind/Extension.rs");
                }
                pub mod Filter {
                    include!("gen/Lean/Meta/Tactic/Grind/Filter.rs");
                }
                pub mod Finish {
                    include!("gen/Lean/Meta/Tactic/Grind/Finish.rs");
                }
                pub mod ForallProp {
                    include!("gen/Lean/Meta/Tactic/Grind/ForallProp.rs");
                }
                pub mod Injection {
                    include!("gen/Lean/Meta/Tactic/Grind/Injection.rs");
                }
                pub mod Injective {
                    include!("gen/Lean/Meta/Tactic/Grind/Injective.rs");
                }
                pub mod Internalize {
                    include!("gen/Lean/Meta/Tactic/Grind/Internalize.rs");
                }
                pub mod Intro {
                    include!("gen/Lean/Meta/Tactic/Grind/Intro.rs");
                }
                pub mod Inv {
                    include!("gen/Lean/Meta/Tactic/Grind/Inv.rs");
                }
                pub mod LawfulEqCmp {
                    include!("gen/Lean/Meta/Tactic/Grind/LawfulEqCmp.rs");
                }
                pub mod Lookahead {
                    include!("gen/Lean/Meta/Tactic/Grind/Lookahead.rs");
                }
                pub mod MBTC {
                    include!("gen/Lean/Meta/Tactic/Grind/MBTC.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Meta/Tactic/Grind/Main.rs");
                }
                pub mod MarkNestedSubsingletons {
                    include!("gen/Lean/Meta/Tactic/Grind/MarkNestedSubsingletons.rs");
                }
                pub mod MatchCond {
                    include!("gen/Lean/Meta/Tactic/Grind/MatchCond.rs");
                }
                pub mod MatchDiscrOnly {
                    include!("gen/Lean/Meta/Tactic/Grind/MatchDiscrOnly.rs");
                }
                pub mod Order {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/Grind/Order.rs");
                    }
                    pub use index::*;
                    pub mod Assert {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/Assert.rs");
                    }
                    pub mod Internalize {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/Internalize.rs");
                    }
                    pub mod OrderM {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/OrderM.rs");
                    }
                    pub mod Proof {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/Proof.rs");
                    }
                    pub mod StructId {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/StructId.rs");
                    }
                    pub mod Types {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/Types.rs");
                    }
                    pub mod Util {
                        include!("gen/Lean/Meta/Tactic/Grind/Order/Util.rs");
                    }
                }
                pub mod OrderInsts {
                    include!("gen/Lean/Meta/Tactic/Grind/OrderInsts.rs");
                }
                pub mod PP {
                    include!("gen/Lean/Meta/Tactic/Grind/PP.rs");
                }
                pub mod Parser {
                    include!("gen/Lean/Meta/Tactic/Grind/Parser.rs");
                }
                pub mod Proj {
                    include!("gen/Lean/Meta/Tactic/Grind/Proj.rs");
                }
                pub mod Proof {
                    include!("gen/Lean/Meta/Tactic/Grind/Proof.rs");
                }
                pub mod ProofUtil {
                    include!("gen/Lean/Meta/Tactic/Grind/ProofUtil.rs");
                }
                pub mod Propagate {
                    include!("gen/Lean/Meta/Tactic/Grind/Propagate.rs");
                }
                pub mod PropagateInj {
                    include!("gen/Lean/Meta/Tactic/Grind/PropagateInj.rs");
                }
                pub mod PropagatorAttr {
                    include!("gen/Lean/Meta/Tactic/Grind/PropagatorAttr.rs");
                }
                pub mod ProveEq {
                    include!("gen/Lean/Meta/Tactic/Grind/ProveEq.rs");
                }
                pub mod ReflCmp {
                    include!("gen/Lean/Meta/Tactic/Grind/ReflCmp.rs");
                }
                pub mod RegisterCommand {
                    include!("gen/Lean/Meta/Tactic/Grind/RegisterCommand.rs");
                }
                pub mod RevertAll {
                    include!("gen/Lean/Meta/Tactic/Grind/RevertAll.rs");
                }
                pub mod Simp {
                    include!("gen/Lean/Meta/Tactic/Grind/Simp.rs");
                }
                pub mod SimpUtil {
                    include!("gen/Lean/Meta/Tactic/Grind/SimpUtil.rs");
                }
                pub mod Solve {
                    include!("gen/Lean/Meta/Tactic/Grind/Solve.rs");
                }
                pub mod Split {
                    include!("gen/Lean/Meta/Tactic/Grind/Split.rs");
                }
                pub mod SynthInstance {
                    include!("gen/Lean/Meta/Tactic/Grind/SynthInstance.rs");
                }
                pub mod Theorems {
                    include!("gen/Lean/Meta/Tactic/Grind/Theorems.rs");
                }
                pub mod Types {
                    include!("gen/Lean/Meta/Tactic/Grind/Types.rs");
                }
                pub mod Util {
                    include!("gen/Lean/Meta/Tactic/Grind/Util.rs");
                }
                pub mod VarRename {
                    include!("gen/Lean/Meta/Tactic/Grind/VarRename.rs");
                }
            }
            pub mod IndependentOf {
                include!("gen/Lean/Meta/Tactic/IndependentOf.rs");
            }
            pub mod Induction {
                include!("gen/Lean/Meta/Tactic/Induction.rs");
            }
            pub mod Injection {
                include!("gen/Lean/Meta/Tactic/Injection.rs");
            }
            pub mod Intro {
                include!("gen/Lean/Meta/Tactic/Intro.rs");
            }
            pub mod Lets {
                include!("gen/Lean/Meta/Tactic/Lets.rs");
            }
            pub mod LibrarySearch {
                include!("gen/Lean/Meta/Tactic/LibrarySearch.rs");
            }
            pub mod NormCast {
                include!("gen/Lean/Meta/Tactic/NormCast.rs");
            }
            pub mod Refl {
                include!("gen/Lean/Meta/Tactic/Refl.rs");
            }
            pub mod Rename {
                include!("gen/Lean/Meta/Tactic/Rename.rs");
            }
            pub mod Repeat {
                include!("gen/Lean/Meta/Tactic/Repeat.rs");
            }
            pub mod Replace {
                include!("gen/Lean/Meta/Tactic/Replace.rs");
            }
            pub mod Revert {
                include!("gen/Lean/Meta/Tactic/Revert.rs");
            }
            pub mod Rewrite {
                include!("gen/Lean/Meta/Tactic/Rewrite.rs");
            }
            pub mod Rewrites {
                include!("gen/Lean/Meta/Tactic/Rewrites.rs");
            }
            pub mod Rfl {
                include!("gen/Lean/Meta/Tactic/Rfl.rs");
            }
            pub mod Simp {
                pub mod index {
                    include!("gen/Lean/Meta/Tactic/Simp.rs");
                }
                pub use index::*;
                pub mod Arith {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/Simp/Arith.rs");
                    }
                    pub use index::*;
                    pub mod Int {
                        pub mod index {
                            include!("gen/Lean/Meta/Tactic/Simp/Arith/Int.rs");
                        }
                        pub use index::*;
                        pub mod Basic {
                            include!("gen/Lean/Meta/Tactic/Simp/Arith/Int/Basic.rs");
                        }
                        pub mod Simp {
                            include!("gen/Lean/Meta/Tactic/Simp/Arith/Int/Simp.rs");
                        }
                    }
                    pub mod Nat {
                        pub mod index {
                            include!("gen/Lean/Meta/Tactic/Simp/Arith/Nat.rs");
                        }
                        pub use index::*;
                        pub mod Basic {
                            include!("gen/Lean/Meta/Tactic/Simp/Arith/Nat/Basic.rs");
                        }
                        pub mod Simp {
                            include!("gen/Lean/Meta/Tactic/Simp/Arith/Nat/Simp.rs");
                        }
                    }
                    pub mod Util {
                        include!("gen/Lean/Meta/Tactic/Simp/Arith/Util.rs");
                    }
                }
                pub mod Attr {
                    include!("gen/Lean/Meta/Tactic/Simp/Attr.rs");
                }
                pub mod BuiltinSimprocs {
                    pub mod index {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs.rs");
                    }
                    pub use index::*;
                    pub mod Array {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Array.rs");
                    }
                    pub mod BitVec {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.rs");
                    }
                    pub mod Char {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Char.rs");
                    }
                    pub mod Core {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.rs");
                    }
                    pub mod CtorIdx {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/CtorIdx.rs");
                    }
                    pub mod Fin {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Fin.rs");
                    }
                    pub mod Int {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Int.rs");
                    }
                    pub mod List {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/List.rs");
                    }
                    pub mod MethodSpecs {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/MethodSpecs.rs");
                    }
                    pub mod Nat {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Nat.rs");
                    }
                    pub mod SInt {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.rs");
                    }
                    pub mod String {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/String.rs");
                    }
                    pub mod UInt {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.rs");
                    }
                    pub mod Util {
                        include!("gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Util.rs");
                    }
                }
                pub mod Diagnostics {
                    include!("gen/Lean/Meta/Tactic/Simp/Diagnostics.rs");
                }
                pub mod LoopProtection {
                    include!("gen/Lean/Meta/Tactic/Simp/LoopProtection.rs");
                }
                pub mod Main {
                    include!("gen/Lean/Meta/Tactic/Simp/Main.rs");
                }
                pub mod RegisterCommand {
                    include!("gen/Lean/Meta/Tactic/Simp/RegisterCommand.rs");
                }
                pub mod Rewrite {
                    include!("gen/Lean/Meta/Tactic/Simp/Rewrite.rs");
                }
                pub mod SimpAll {
                    include!("gen/Lean/Meta/Tactic/Simp/SimpAll.rs");
                }
                pub mod SimpCongrTheorems {
                    include!("gen/Lean/Meta/Tactic/Simp/SimpCongrTheorems.rs");
                }
                pub mod SimpTheorems {
                    include!("gen/Lean/Meta/Tactic/Simp/SimpTheorems.rs");
                }
                pub mod Simproc {
                    include!("gen/Lean/Meta/Tactic/Simp/Simproc.rs");
                }
                pub mod Types {
                    include!("gen/Lean/Meta/Tactic/Simp/Types.rs");
                }
            }
            pub mod SolveByElim {
                include!("gen/Lean/Meta/Tactic/SolveByElim.rs");
            }
            pub mod Split {
                include!("gen/Lean/Meta/Tactic/Split.rs");
            }
            pub mod SplitIf {
                include!("gen/Lean/Meta/Tactic/SplitIf.rs");
            }
            pub mod Subst {
                include!("gen/Lean/Meta/Tactic/Subst.rs");
            }
            pub mod Symm {
                include!("gen/Lean/Meta/Tactic/Symm.rs");
            }
            pub mod Try {
                pub mod index {
                    include!("gen/Lean/Meta/Tactic/Try.rs");
                }
                pub use index::*;
                pub mod Collect {
                    include!("gen/Lean/Meta/Tactic/Try/Collect.rs");
                }
            }
            pub mod TryThis {
                include!("gen/Lean/Meta/Tactic/TryThis.rs");
            }
            pub mod Unfold {
                include!("gen/Lean/Meta/Tactic/Unfold.rs");
            }
            pub mod UnifyEq {
                include!("gen/Lean/Meta/Tactic/UnifyEq.rs");
            }
            pub mod Util {
                include!("gen/Lean/Meta/Tactic/Util.rs");
            }
        }
        pub mod Transform {
            include!("gen/Lean/Meta/Transform.rs");
        }
        pub mod TransparencyMode {
            include!("gen/Lean/Meta/TransparencyMode.rs");
        }
        pub mod TryThis {
            include!("gen/Lean/Meta/TryThis.rs");
        }
        pub mod UnificationHint {
            include!("gen/Lean/Meta/UnificationHint.rs");
        }
        pub mod WHNF {
            include!("gen/Lean/Meta/WHNF.rs");
        }
        pub mod WrapInstance {
            include!("gen/Lean/Meta/WrapInstance.rs");
        }
    }
    pub mod MetavarContext {
        include!("gen/Lean/MetavarContext.rs");
    }
    pub mod Modifiers {
        include!("gen/Lean/Modifiers.rs");
    }
    pub mod MonadEnv {
        include!("gen/Lean/MonadEnv.rs");
    }
    pub mod Namespace {
        include!("gen/Lean/Namespace.rs");
    }
    pub mod OriginalConstKind {
        include!("gen/Lean/OriginalConstKind.rs");
    }
    pub mod Parser {
        pub mod index {
            include!("gen/Lean/Parser.rs");
        }
        pub use index::*;
        pub mod Attr {
            include!("gen/Lean/Parser/Attr.rs");
        }
        pub mod Basic {
            include!("gen/Lean/Parser/Basic.rs");
        }
        pub mod Command {
            include!("gen/Lean/Parser/Command.rs");
        }
        pub mod Do {
            include!("gen/Lean/Parser/Do.rs");
        }
        pub mod Extension {
            include!("gen/Lean/Parser/Extension.rs");
        }
        pub mod Extra {
            include!("gen/Lean/Parser/Extra.rs");
        }
        pub mod Level {
            include!("gen/Lean/Parser/Level.rs");
        }
        pub mod Module {
            pub mod index {
                include!("gen/Lean/Parser/Module.rs");
            }
            pub use index::*;
            pub mod Syntax {
                include!("gen/Lean/Parser/Module/Syntax.rs");
            }
        }
        pub mod StrInterpolation {
            include!("gen/Lean/Parser/StrInterpolation.rs");
        }
        pub mod Syntax {
            include!("gen/Lean/Parser/Syntax.rs");
        }
        pub mod Tactic {
            pub mod index {
                include!("gen/Lean/Parser/Tactic.rs");
            }
            pub use index::*;
            pub mod Doc {
                include!("gen/Lean/Parser/Tactic/Doc.rs");
            }
        }
        pub mod Term {
            pub mod index {
                include!("gen/Lean/Parser/Term.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Parser/Term/Basic.rs");
            }
            pub mod Doc {
                include!("gen/Lean/Parser/Term/Doc.rs");
            }
        }
        pub mod Types {
            include!("gen/Lean/Parser/Types.rs");
        }
    }
    pub mod ParserCompiler {
        pub mod index {
            include!("gen/Lean/ParserCompiler.rs");
        }
        pub use index::*;
        pub mod Attribute {
            include!("gen/Lean/ParserCompiler/Attribute.rs");
        }
    }
    pub mod PrettyPrinter {
        pub mod index {
            include!("gen/Lean/PrettyPrinter.rs");
        }
        pub use index::*;
        pub mod Basic {
            include!("gen/Lean/PrettyPrinter/Basic.rs");
        }
        pub mod Delaborator {
            pub mod index {
                include!("gen/Lean/PrettyPrinter/Delaborator.rs");
            }
            pub use index::*;
            pub mod Attributes {
                include!("gen/Lean/PrettyPrinter/Delaborator/Attributes.rs");
            }
            pub mod Basic {
                include!("gen/Lean/PrettyPrinter/Delaborator/Basic.rs");
            }
            pub mod Builtins {
                include!("gen/Lean/PrettyPrinter/Delaborator/Builtins.rs");
            }
            pub mod DeclWithSig {
                include!("gen/Lean/PrettyPrinter/Delaborator/DeclWithSig.rs");
            }
            pub mod FieldNotation {
                include!("gen/Lean/PrettyPrinter/Delaborator/FieldNotation.rs");
            }
            pub mod Metavariable {
                include!("gen/Lean/PrettyPrinter/Delaborator/Metavariable.rs");
            }
            pub mod Options {
                include!("gen/Lean/PrettyPrinter/Delaborator/Options.rs");
            }
            pub mod SubExpr {
                include!("gen/Lean/PrettyPrinter/Delaborator/SubExpr.rs");
            }
            pub mod TopDownAnalyze {
                include!("gen/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.rs");
            }
        }
        pub mod Formatter {
            include!("gen/Lean/PrettyPrinter/Formatter.rs");
        }
        pub mod Parenthesizer {
            include!("gen/Lean/PrettyPrinter/Parenthesizer.rs");
        }
    }
    pub mod PrivateName {
        include!("gen/Lean/PrivateName.rs");
    }
    pub mod ProjFns {
        include!("gen/Lean/ProjFns.rs");
    }
    pub mod ReducibilityAttrs {
        include!("gen/Lean/ReducibilityAttrs.rs");
    }
    pub mod Replay {
        include!("gen/Lean/Replay.rs");
    }
    pub mod ReservedNameAction {
        include!("gen/Lean/ReservedNameAction.rs");
    }
    pub mod ResolveName {
        include!("gen/Lean/ResolveName.rs");
    }
    pub mod Runtime {
        include!("gen/Lean/Runtime.rs");
    }
    pub mod ScopedEnvExtension {
        include!("gen/Lean/ScopedEnvExtension.rs");
    }
    pub mod Server {
        pub mod index {
            include!("gen/Lean/Server.rs");
        }
        pub use index::*;
        pub mod AsyncList {
            include!("gen/Lean/Server/AsyncList.rs");
        }
        pub mod CodeActions {
            pub mod index {
                include!("gen/Lean/Server/CodeActions.rs");
            }
            pub use index::*;
            pub mod Attr {
                include!("gen/Lean/Server/CodeActions/Attr.rs");
            }
            pub mod Basic {
                include!("gen/Lean/Server/CodeActions/Basic.rs");
            }
            pub mod Provider {
                include!("gen/Lean/Server/CodeActions/Provider.rs");
            }
            pub mod UnknownIdentifier {
                include!("gen/Lean/Server/CodeActions/UnknownIdentifier.rs");
            }
        }
        pub mod Completion {
            pub mod index {
                include!("gen/Lean/Server/Completion.rs");
            }
            pub use index::*;
            pub mod CompletionCollectors {
                include!("gen/Lean/Server/Completion/CompletionCollectors.rs");
            }
            pub mod CompletionInfoSelection {
                include!("gen/Lean/Server/Completion/CompletionInfoSelection.rs");
            }
            pub mod CompletionItemCompression {
                include!("gen/Lean/Server/Completion/CompletionItemCompression.rs");
            }
            pub mod CompletionResolution {
                include!("gen/Lean/Server/Completion/CompletionResolution.rs");
            }
            pub mod CompletionUtils {
                include!("gen/Lean/Server/Completion/CompletionUtils.rs");
            }
            pub mod EligibleHeaderDecls {
                include!("gen/Lean/Server/Completion/EligibleHeaderDecls.rs");
            }
            pub mod ImportCompletion {
                include!("gen/Lean/Server/Completion/ImportCompletion.rs");
            }
            pub mod SyntheticCompletion {
                include!("gen/Lean/Server/Completion/SyntheticCompletion.rs");
            }
        }
        pub mod FileSource {
            include!("gen/Lean/Server/FileSource.rs");
        }
        pub mod FileWorker {
            pub mod index {
                include!("gen/Lean/Server/FileWorker.rs");
            }
            pub use index::*;
            pub mod ExampleHover {
                include!("gen/Lean/Server/FileWorker/ExampleHover.rs");
            }
            pub mod InlayHints {
                include!("gen/Lean/Server/FileWorker/InlayHints.rs");
            }
            pub mod RequestHandling {
                include!("gen/Lean/Server/FileWorker/RequestHandling.rs");
            }
            pub mod SemanticHighlighting {
                include!("gen/Lean/Server/FileWorker/SemanticHighlighting.rs");
            }
            pub mod SetupFile {
                include!("gen/Lean/Server/FileWorker/SetupFile.rs");
            }
            pub mod SignatureHelp {
                include!("gen/Lean/Server/FileWorker/SignatureHelp.rs");
            }
            pub mod Utils {
                include!("gen/Lean/Server/FileWorker/Utils.rs");
            }
            pub mod WidgetRequests {
                include!("gen/Lean/Server/FileWorker/WidgetRequests.rs");
            }
        }
        pub mod GoTo {
            include!("gen/Lean/Server/GoTo.rs");
        }
        pub mod InfoUtils {
            include!("gen/Lean/Server/InfoUtils.rs");
        }
        pub mod Logging {
            include!("gen/Lean/Server/Logging.rs");
        }
        pub mod ProtocolOverview {
            include!("gen/Lean/Server/ProtocolOverview.rs");
        }
        pub mod References {
            include!("gen/Lean/Server/References.rs");
        }
        pub mod RequestCancellation {
            include!("gen/Lean/Server/RequestCancellation.rs");
        }
        pub mod Requests {
            include!("gen/Lean/Server/Requests.rs");
        }
        pub mod Rpc {
            pub mod index {
                include!("gen/Lean/Server/Rpc.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lean/Server/Rpc/Basic.rs");
            }
            pub mod Deriving {
                include!("gen/Lean/Server/Rpc/Deriving.rs");
            }
            pub mod RequestHandling {
                include!("gen/Lean/Server/Rpc/RequestHandling.rs");
            }
        }
        pub mod ServerTask {
            include!("gen/Lean/Server/ServerTask.rs");
        }
        pub mod Snapshots {
            include!("gen/Lean/Server/Snapshots.rs");
        }
        pub mod Test {
            pub mod index {
                include!("gen/Lean/Server/Test.rs");
            }
            pub use index::*;
            pub mod Cancel {
                include!("gen/Lean/Server/Test/Cancel.rs");
            }
            pub mod Refs {
                include!("gen/Lean/Server/Test/Refs.rs");
            }
            pub mod Runner {
                include!("gen/Lean/Server/Test/Runner.rs");
            }
        }
        pub mod Utils {
            include!("gen/Lean/Server/Utils.rs");
        }
        pub mod Watchdog {
            include!("gen/Lean/Server/Watchdog.rs");
        }
    }
    pub mod Setup {
        include!("gen/Lean/Setup.rs");
    }
    pub mod Shell {
        include!("gen/Lean/Shell.rs");
    }
    pub mod Structure {
        include!("gen/Lean/Structure.rs");
    }
    pub mod SubExpr {
        include!("gen/Lean/SubExpr.rs");
    }
    pub mod Syntax {
        include!("gen/Lean/Syntax.rs");
    }
    pub mod ToExpr {
        include!("gen/Lean/ToExpr.rs");
    }
    pub mod ToLevel {
        include!("gen/Lean/ToLevel.rs");
    }
    pub mod Util {
        pub mod index {
            include!("gen/Lean/Util.rs");
        }
        pub use index::*;
        pub mod CollectAxioms {
            include!("gen/Lean/Util/CollectAxioms.rs");
        }
        pub mod CollectFVars {
            include!("gen/Lean/Util/CollectFVars.rs");
        }
        pub mod CollectLevelMVars {
            include!("gen/Lean/Util/CollectLevelMVars.rs");
        }
        pub mod CollectLevelParams {
            include!("gen/Lean/Util/CollectLevelParams.rs");
        }
        pub mod CollectLooseBVars {
            include!("gen/Lean/Util/CollectLooseBVars.rs");
        }
        pub mod CollectMVars {
            include!("gen/Lean/Util/CollectMVars.rs");
        }
        pub mod Diff {
            include!("gen/Lean/Util/Diff.rs");
        }
        pub mod FVarSubset {
            include!("gen/Lean/Util/FVarSubset.rs");
        }
        pub mod FindExpr {
            include!("gen/Lean/Util/FindExpr.rs");
        }
        pub mod FindLevelMVar {
            include!("gen/Lean/Util/FindLevelMVar.rs");
        }
        pub mod FindMVar {
            include!("gen/Lean/Util/FindMVar.rs");
        }
        pub mod FoldConsts {
            include!("gen/Lean/Util/FoldConsts.rs");
        }
        pub mod ForEachExpr {
            include!("gen/Lean/Util/ForEachExpr.rs");
        }
        pub mod ForEachExprWhere {
            include!("gen/Lean/Util/ForEachExprWhere.rs");
        }
        pub mod HasConstCache {
            include!("gen/Lean/Util/HasConstCache.rs");
        }
        pub mod Heartbeats {
            include!("gen/Lean/Util/Heartbeats.rs");
        }
        pub mod InstantiateLevelParams {
            include!("gen/Lean/Util/InstantiateLevelParams.rs");
        }
        pub mod LakePath {
            include!("gen/Lean/Util/LakePath.rs");
        }
        pub mod LeanOptions {
            include!("gen/Lean/Util/LeanOptions.rs");
        }
        pub mod MonadBacktrack {
            include!("gen/Lean/Util/MonadBacktrack.rs");
        }
        pub mod MonadCache {
            include!("gen/Lean/Util/MonadCache.rs");
        }
        pub mod NumApps {
            include!("gen/Lean/Util/NumApps.rs");
        }
        pub mod NumObjs {
            include!("gen/Lean/Util/NumObjs.rs");
        }
        pub mod OccursCheck {
            include!("gen/Lean/Util/OccursCheck.rs");
        }
        pub mod PPExt {
            include!("gen/Lean/Util/PPExt.rs");
        }
        pub mod ParamMinimizer {
            include!("gen/Lean/Util/ParamMinimizer.rs");
        }
        pub mod Path {
            include!("gen/Lean/Util/Path.rs");
        }
        pub mod Profile {
            include!("gen/Lean/Util/Profile.rs");
        }
        pub mod Profiler {
            include!("gen/Lean/Util/Profiler.rs");
        }
        pub mod ProfilerServer {
            include!("gen/Lean/Util/ProfilerServer.rs");
        }
        pub mod PtrSet {
            include!("gen/Lean/Util/PtrSet.rs");
        }
        pub mod RecDepth {
            include!("gen/Lean/Util/RecDepth.rs");
        }
        pub mod Recognizers {
            include!("gen/Lean/Util/Recognizers.rs");
        }
        pub mod ReplaceExpr {
            include!("gen/Lean/Util/ReplaceExpr.rs");
        }
        pub mod ReplaceLevel {
            include!("gen/Lean/Util/ReplaceLevel.rs");
        }
        pub mod Reprove {
            include!("gen/Lean/Util/Reprove.rs");
        }
        pub mod SCC {
            include!("gen/Lean/Util/SCC.rs");
        }
        pub mod SafeExponentiation {
            include!("gen/Lean/Util/SafeExponentiation.rs");
        }
        pub mod ShareCommon {
            include!("gen/Lean/Util/ShareCommon.rs");
        }
        pub mod Sorry {
            include!("gen/Lean/Util/Sorry.rs");
        }
        pub mod SortExprs {
            include!("gen/Lean/Util/SortExprs.rs");
        }
        pub mod TestExtern {
            include!("gen/Lean/Util/TestExtern.rs");
        }
        pub mod Trace {
            include!("gen/Lean/Util/Trace.rs");
        }
        pub mod UnusedBinders {
            include!("gen/Lean/Util/UnusedBinders.rs");
        }
    }
    pub mod Widget {
        pub mod index {
            include!("gen/Lean/Widget.rs");
        }
        pub use index::*;
        pub mod Basic {
            include!("gen/Lean/Widget/Basic.rs");
        }
        pub mod Commands {
            include!("gen/Lean/Widget/Commands.rs");
        }
        pub mod Diff {
            include!("gen/Lean/Widget/Diff.rs");
        }
        pub mod InteractiveCode {
            include!("gen/Lean/Widget/InteractiveCode.rs");
        }
        pub mod InteractiveDiagnostic {
            include!("gen/Lean/Widget/InteractiveDiagnostic.rs");
        }
        pub mod InteractiveGoal {
            include!("gen/Lean/Widget/InteractiveGoal.rs");
        }
        pub mod TaggedText {
            include!("gen/Lean/Widget/TaggedText.rs");
        }
        pub mod Types {
            include!("gen/Lean/Widget/Types.rs");
        }
        pub mod UserWidget {
            include!("gen/Lean/Widget/UserWidget.rs");
        }
    }
}
