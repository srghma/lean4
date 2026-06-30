#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports, unsafe_op_in_unsafe_fn)]

pub mod ffi {
    pub use gen_init_ffi::*;
    pub use gen_std_ffi::*;
    pub use gen_lean_ffi::*;
}

pub mod r#gen {
    pub use gen_init::r#gen::Init;
    pub use gen_std::r#gen::Std;
    pub mod Lean {
        pub mod AddDecl {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/AddDecl.rs");
        }
        pub mod Attributes {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Attributes.rs");
        }
        pub mod AuxRecursor {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/AuxRecursor.rs");
        }
        pub mod BuiltinDocAttr {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/BuiltinDocAttr.rs");
        }
        pub mod Class {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Class.rs");
        }
        pub mod CompactedRegion {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/CompactedRegion.rs");
        }
        pub mod Compiler {
            pub mod BorrowedAnnotation {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/BorrowedAnnotation.rs");
            }
            pub mod ClosedTermCache {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/ClosedTermCache.rs");
            }
            pub mod CSimpAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/CSimpAttr.rs");
            }
            pub mod ExportAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/ExportAttr.rs");
            }
            pub mod ExternAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/ExternAttr.rs");
            }
            pub mod FFI {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/FFI.rs");
            }
            pub mod ImplementedByAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/ImplementedByAttr.rs");
            }
            pub mod InitAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/InitAttr.rs");
            }
            pub mod InlineAttrs {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/InlineAttrs.rs");
            }
            pub mod IR {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/Basic.rs");
                }
                pub mod Checker {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/Checker.rs");
                }
                pub mod CompilerM {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/CompilerM.rs");
                }
                pub mod EmitLLVM {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/EmitLLVM.rs");
                }
                pub mod EmitUtil {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/EmitUtil.rs");
                }
                pub mod Format {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/Format.rs");
                }
                pub mod LLVMBindings {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/LLVMBindings.rs");
                }
                pub mod Meta {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/Meta.rs");
                }
                pub mod NormIds {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/NormIds.rs");
                }
                pub mod Sorry {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/Sorry.rs");
                }
                pub mod ToIR {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/ToIR.rs");
                }
                pub mod ToIRType {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/ToIRType.rs");
                }
                pub mod UnboxResult {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/IR/UnboxResult.rs");
                }
            }
            pub mod LCNF {
                pub mod AlphaEqv {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/AlphaEqv.rs");
                }
                pub mod AuxDeclCache {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/AuxDeclCache.rs");
                }
                pub mod BaseTypes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/BaseTypes.rs");
                }
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Basic.rs");
                }
                pub mod Bind {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Bind.rs");
                }
                pub mod Check {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Check.rs");
                }
                pub mod Closure {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Closure.rs");
                }
                pub mod CoalesceRC {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/CoalesceRC.rs");
                }
                pub mod CompatibleTypes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/CompatibleTypes.rs");
                }
                pub mod CompilerM {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/CompilerM.rs");
                }
                pub mod ConfigOptions {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ConfigOptions.rs");
                }
                pub mod CSE {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/CSE.rs");
                }
                pub mod DeclHash {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/DeclHash.rs");
                }
                pub mod DependsOn {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/DependsOn.rs");
                }
                pub mod ElimDead {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ElimDead.rs");
                }
                pub mod ElimDeadBranches {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ElimDeadBranches.rs");
                }
                pub mod EmitRust {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/EmitRust.rs");
                }
                pub mod EmitUtil {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/EmitUtil.rs");
                }
                pub mod ExpandResetReuse {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ExpandResetReuse.rs");
                }
                pub mod ExplicitBoxing {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ExplicitBoxing.rs");
                }
                pub mod ExplicitRC {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ExplicitRC.rs");
                }
                pub mod ExtractClosed {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ExtractClosed.rs");
                }
                pub mod FixedParams {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/FixedParams.rs");
                }
                pub mod FloatLetIn {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/FloatLetIn.rs");
                }
                pub mod FVarUtil {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/FVarUtil.rs");
                }
                pub mod InferBorrow {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/InferBorrow.rs");
                }
                pub mod InferType {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/InferType.rs");
                }
                pub mod Internalize {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Internalize.rs");
                }
                pub mod Irrelevant {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Irrelevant.rs");
                }
                pub mod JoinPoints {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/JoinPoints.rs");
                }
                pub mod LambdaLifting {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/LambdaLifting.rs");
                }
                pub mod LCtx {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/LCtx.rs");
                }
                pub mod Level {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Level.rs");
                }
                pub mod LiveVars {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/LiveVars.rs");
                }
                pub mod MonadScope {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/MonadScope.rs");
                }
                pub mod MonoTypes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/MonoTypes.rs");
                }
                pub mod OtherDecl {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/OtherDecl.rs");
                }
                pub mod PassManager {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PassManager.rs");
                }
                pub mod PhaseExt {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PhaseExt.rs");
                }
                pub mod PrettyPrinter {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PrettyPrinter.rs");
                }
                pub mod Probing {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Probing.rs");
                }
                pub mod PropagateBorrow {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PropagateBorrow.rs");
                }
                pub mod PublicDeclsExt {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PublicDeclsExt.rs");
                }
                pub mod PullFunDecls {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PullFunDecls.rs");
                }
                pub mod PullLetDecls {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/PullLetDecls.rs");
                }
                pub mod Renaming {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Renaming.rs");
                }
                pub mod ResetReuse {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ResetReuse.rs");
                }
                pub mod ScopeM {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ScopeM.rs");
                }
                pub mod Simp {
                    pub mod Basic {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Simp/Basic.rs");
                    }
                    pub mod Config {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Simp/Config.rs");
                    }
                    pub mod FunDeclInfo {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Simp/FunDeclInfo.rs");
                    }
                }
                pub mod SimpCase {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/SimpCase.rs");
                }
                pub mod SimpleGroundExpr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/SimpleGroundExpr.rs");
                }
                pub mod SplitSCC {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/SplitSCC.rs");
                }
                pub mod ToExpr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ToExpr.rs");
                }
                pub mod ToImpureType {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/ToImpureType.rs");
                }
                pub mod Types {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Types.rs");
                }
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/LCNF/Util.rs");
                }
            }
            pub mod MetaAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/MetaAttr.rs");
            }
            pub mod ModPkgExt {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/ModPkgExt.rs");
            }
            pub mod NameDemangling {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/NameDemangling.rs");
            }
            pub mod NameMangling {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/NameMangling.rs");
            }
            pub mod NeverExtractAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/NeverExtractAttr.rs");
            }
            pub mod NoncomputableAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/NoncomputableAttr.rs");
            }
            pub mod Old {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/Old.rs");
            }
            pub mod Options {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/Options.rs");
            }
            pub mod Specialize {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Compiler/Specialize.rs");
            }
        }
        pub mod CoreM {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/CoreM.rs");
        }
        pub mod Data {
            pub mod index {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data.rs");
            }
            pub use index::*;
            pub mod Array {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Array.rs");
            }
            pub mod AssocList {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/AssocList.rs");
            }
            pub mod DeclarationRange {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/DeclarationRange.rs");
            }
            pub mod EditDistance {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/EditDistance.rs");
            }
            pub mod Format {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Format.rs");
            }
            pub mod Iterators {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Iterators.rs");
                }
                pub use index::*;
                pub mod Producers {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Iterators/Producers.rs");
                    }
                    pub use index::*;
                    pub mod PersistentHashMap {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Iterators/Producers/PersistentHashMap.rs");
                    }
                }
            }
            pub mod Json {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/Basic.rs");
                }
                pub mod Elab {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/Elab.rs");
                }
                pub mod FromToJson {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/FromToJson.rs");
                    }
                    pub use index::*;
                    pub mod Basic {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/FromToJson/Basic.rs");
                    }
                    pub mod Extra {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/FromToJson/Extra.rs");
                    }
                }
                pub mod Parser {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/Parser.rs");
                }
                pub mod Printer {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/Printer.rs");
                }
                pub mod Stream {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Json/Stream.rs");
                }
            }
            pub mod JsonRpc {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/JsonRpc.rs");
            }
            pub mod KVMap {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/KVMap.rs");
            }
            pub mod LBool {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/LBool.rs");
            }
            pub mod LOption {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/LOption.rs");
            }
            pub mod Lsp {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Basic.rs");
                }
                pub mod BasicAux {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/BasicAux.rs");
                }
                pub mod CancelParams {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/CancelParams.rs");
                }
                pub mod Capabilities {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Capabilities.rs");
                }
                pub mod Client {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Client.rs");
                }
                pub mod CodeActions {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/CodeActions.rs");
                }
                pub mod Communication {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Communication.rs");
                }
                pub mod Diagnostics {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Diagnostics.rs");
                }
                pub mod Extra {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Extra.rs");
                }
                pub mod InitShutdown {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/InitShutdown.rs");
                }
                pub mod Internal {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Internal.rs");
                }
                pub mod Ipc {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Ipc.rs");
                }
                pub mod LanguageFeatures {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/LanguageFeatures.rs");
                }
                pub mod TextSync {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/TextSync.rs");
                }
                pub mod Utf16 {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Utf16.rs");
                }
                pub mod Window {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Window.rs");
                }
                pub mod Workspace {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Lsp/Workspace.rs");
                }
            }
            pub mod Name {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Name.rs");
            }
            pub mod NameMap {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/NameMap.rs");
                }
                pub use index::*;
                pub mod AdditionalOperations {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/NameMap/AdditionalOperations.rs");
                }
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/NameMap/Basic.rs");
                }
            }
            pub mod NameTrie {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/NameTrie.rs");
            }
            pub mod OpenDecl {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/OpenDecl.rs");
            }
            pub mod Options {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Options.rs");
            }
            pub mod PersistentArray {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/PersistentArray.rs");
            }
            pub mod PersistentHashMap {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/PersistentHashMap.rs");
            }
            pub mod PersistentHashSet {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/PersistentHashSet.rs");
            }
            pub mod Position {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Position.rs");
            }
            pub mod PPContext {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/PPContext.rs");
            }
            pub mod PrefixTree {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/PrefixTree.rs");
            }
            pub mod RArray {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/RArray.rs");
            }
            pub mod RBMap {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/RBMap.rs");
            }
            pub mod RBTree {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/RBTree.rs");
            }
            pub mod SMap {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/SMap.rs");
            }
            pub mod SSet {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/SSet.rs");
            }
            pub mod Trie {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Data/Trie.rs");
            }
        }
        pub mod Declaration {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Declaration.rs");
        }
        pub mod DeclarationRange {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DeclarationRange.rs");
        }
        pub mod DefEqAttrib {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DefEqAttrib.rs");
        }
        pub mod DeprecatedModule {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DeprecatedModule.rs");
        }
        pub mod DocString {
            pub mod Extension {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DocString/Extension.rs");
            }
            pub mod Links {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DocString/Links.rs");
            }
            pub mod Markdown {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DocString/Markdown.rs");
            }
            pub mod Types {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/DocString/Types.rs");
            }
        }
        pub mod Elab {
            pub mod Config {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/Config.rs");
            }
            pub mod ConfigEval {
                pub mod Commands {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/ConfigEval/Commands.rs");
                }
            }
            pub mod DocString {
                pub mod Builtin {
                    pub mod Parsing {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/DocString/Builtin/Parsing.rs");
                    }
                }
            }
            pub mod ErrorUtils {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/ErrorUtils.rs");
            }
            pub mod Exception {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/Exception.rs");
            }
            pub mod InfoTree {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/InfoTree.rs");
                }
                pub use index::*;
                pub mod InlayHints {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/InfoTree/InlayHints.rs");
                }
                pub mod Main {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/InfoTree/Main.rs");
                }
                pub mod Types {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/InfoTree/Types.rs");
                }
            }
            pub mod InheritDoc {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/InheritDoc.rs");
            }
            pub mod PreDefinition {
                pub mod Structural {
                    pub mod Basic {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/PreDefinition/Structural/Basic.rs");
                    }
                    pub mod IndGroupInfo {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/PreDefinition/Structural/IndGroupInfo.rs");
                    }
                    pub mod Preprocess {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/PreDefinition/Structural/Preprocess.rs");
                    }
                }
                pub mod WF {
                    pub mod FloatRecApp {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/PreDefinition/WF/FloatRecApp.rs");
                    }
                }
            }
            pub mod RecAppSyntax {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/RecAppSyntax.rs");
            }
            pub mod SetOption {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/SetOption.rs");
            }
            pub mod Tactic {
                pub mod Omega {
                    pub mod MinNatAbs {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Elab/Tactic/Omega/MinNatAbs.rs");
                    }
                }
            }
        }
        pub mod EnvExtension {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/EnvExtension.rs");
        }
        pub mod Environment {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Environment.rs");
        }
        pub mod ErrorExplanation {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ErrorExplanation.rs");
        }
        pub mod Exception {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Exception.rs");
        }
        pub mod Expr {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Expr.rs");
        }
        pub mod ExtraModUses {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ExtraModUses.rs");
        }
        pub mod HeadIndex {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/HeadIndex.rs");
        }
        pub mod Hygiene {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Hygiene.rs");
        }
        pub mod ImportingFlag {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ImportingFlag.rs");
        }
        pub mod InternalExceptionId {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/InternalExceptionId.rs");
        }
        pub mod Language {
            pub mod Basic {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Language/Basic.rs");
            }
            pub mod Util {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Language/Util.rs");
            }
        }
        pub mod Level {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Level.rs");
        }
        pub mod Linter {
            pub mod Deprecated {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Linter/Deprecated.rs");
            }
            pub mod EnvLinter {
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Linter/EnvLinter/Basic.rs");
                }
                pub mod Nolint {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Linter/EnvLinter/Nolint.rs");
                }
            }
            pub mod Init {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Linter/Init.rs");
            }
            pub mod PersistentLintLog {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Linter/PersistentLintLog.rs");
            }
        }
        pub mod LoadDynlib {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/LoadDynlib.rs");
        }
        pub mod LocalContext {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/LocalContext.rs");
        }
        pub mod Log {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Log.rs");
        }
        pub mod Message {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Message.rs");
        }
        pub mod Meta {
            pub mod AbstractMVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/AbstractMVars.rs");
            }
            pub mod ACLt {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ACLt.rs");
            }
            pub mod ArgsPacker {
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ArgsPacker/Basic.rs");
                }
            }
            pub mod Basic {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Basic.rs");
            }
            pub mod BinderNameHint {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/BinderNameHint.rs");
            }
            pub mod Canonicalizer {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Canonicalizer.rs");
            }
            pub mod CasesInfo {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CasesInfo.rs");
            }
            pub mod Check {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Check.rs");
            }
            pub mod CheckTactic {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CheckTactic.rs");
            }
            pub mod CoeAttr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CoeAttr.rs");
            }
            pub mod CollectFVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CollectFVars.rs");
            }
            pub mod CollectMVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CollectMVars.rs");
            }
            pub mod CompletionName {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CompletionName.rs");
            }
            pub mod Constructions {
                pub mod CasesOn {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Constructions/CasesOn.rs");
                }
                pub mod CtorIdx {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Constructions/CtorIdx.rs");
                }
                pub mod RecOn {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Constructions/RecOn.rs");
                }
                pub mod SparseCasesOn {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Constructions/SparseCasesOn.rs");
                }
            }
            pub mod CtorRecognizer {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/CtorRecognizer.rs");
            }
            pub mod DecLevel {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/DecLevel.rs");
            }
            pub mod DiscrTree {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/DiscrTree.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/DiscrTree/Basic.rs");
                }
                pub mod Main {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/DiscrTree/Main.rs");
                }
                pub mod Types {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/DiscrTree/Types.rs");
                }
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/DiscrTree/Util.rs");
                }
            }
            pub mod Eval {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Eval.rs");
            }
            pub mod ExprLens {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ExprLens.rs");
            }
            pub mod ExprTraverse {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ExprTraverse.rs");
            }
            pub mod ForEachExpr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ForEachExpr.rs");
            }
            pub mod FunInfo {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/FunInfo.rs");
            }
            pub mod GeneralizeTelescope {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/GeneralizeTelescope.rs");
            }
            pub mod GeneralizeVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/GeneralizeVars.rs");
            }
            pub mod GetUnfoldableConst {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/GetUnfoldableConst.rs");
            }
            pub mod HasAssignableMVar {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/HasAssignableMVar.rs");
            }
            pub mod HasNotBit {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/HasNotBit.rs");
            }
            pub mod Inductive {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Inductive.rs");
            }
            pub mod InferType {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/InferType.rs");
            }
            pub mod Instances {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Instances.rs");
            }
            pub mod IntInstTesters {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/IntInstTesters.rs");
            }
            pub mod Iterator {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Iterator.rs");
            }
            pub mod KAbstract {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/KAbstract.rs");
            }
            pub mod KExprMap {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/KExprMap.rs");
            }
            pub mod LetToHave {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/LetToHave.rs");
            }
            pub mod LevelDefEq {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/LevelDefEq.rs");
            }
            pub mod LitValues {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/LitValues.rs");
            }
            pub mod Match {
                pub mod MatcherApp {
                    pub mod Basic {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Match/MatcherApp/Basic.rs");
                    }
                }
                pub mod MatcherInfo {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Match/MatcherInfo.rs");
                }
                pub mod MatchPatternAttr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Match/MatchPatternAttr.rs");
                }
                pub mod MVarRenaming {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Match/MVarRenaming.rs");
                }
                pub mod Value {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Match/Value.rs");
                }
            }
            pub mod MatchUtil {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/MatchUtil.rs");
            }
            pub mod MonadSimp {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/MonadSimp.rs");
            }
            pub mod NatInstTesters {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/NatInstTesters.rs");
            }
            pub mod NatTable {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/NatTable.rs");
            }
            pub mod Offset {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Offset.rs");
            }
            pub mod PPBinder {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/PPBinder.rs");
            }
            pub mod PPGoal {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/PPGoal.rs");
            }
            pub mod PProdN {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/PProdN.rs");
            }
            pub mod ProdN {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ProdN.rs");
            }
            pub mod RecExt {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/RecExt.rs");
            }
            pub mod RecursorInfo {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/RecursorInfo.rs");
            }
            pub mod Reduce {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Reduce.rs");
            }
            pub mod ReduceEval {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/ReduceEval.rs");
            }
            pub mod SameCtorUtils {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/SameCtorUtils.rs");
            }
            pub mod Sorry {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sorry.rs");
            }
            pub mod Sym {
                pub mod AlphaShareCommon {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/AlphaShareCommon.rs");
                }
                pub mod Arith {
                    pub mod Poly {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/Arith/Poly.rs");
                    }
                    pub mod ToExpr {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/Arith/ToExpr.rs");
                    }
                    pub mod VarRename {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/Arith/VarRename.rs");
                    }
                }
                pub mod Eta {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/Eta.rs");
                }
                pub mod ExprPtr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/ExprPtr.rs");
                }
                pub mod LitValues {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/LitValues.rs");
                }
                pub mod Offset {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Sym/Offset.rs");
                }
            }
            pub mod Tactic {
                pub mod BVDecide {
                    pub mod External {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/BVDecide/External.rs");
                    }
                    pub mod LRAT {
                        pub mod index {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/BVDecide/LRAT.rs");
                        }
                        pub use index::*;
                        pub mod Cert {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/BVDecide/LRAT/Cert.rs");
                        }
                        pub mod Trim {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/BVDecide/LRAT/Trim.rs");
                        }
                    }
                }
                pub mod Cbv {
                    pub mod Opaque {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Cbv/Opaque.rs");
                    }
                }
                pub mod ElimInfo {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/ElimInfo.rs");
                }
                pub mod FunIndInfo {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/FunIndInfo.rs");
                }
                pub mod FVarSubst {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/FVarSubst.rs");
                }
                pub mod Grind {
                    pub mod AC {
                        pub mod Seq {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/AC/Seq.rs");
                        }
                        pub mod ToExpr {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/AC/ToExpr.rs");
                        }
                        pub mod VarRename {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/AC/VarRename.rs");
                        }
                    }
                    pub mod Arith {
                        pub mod Cutsat {
                            pub mod VarRename {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/VarRename.rs");
                            }
                        }
                        pub mod Linear {
                            pub mod ToExpr {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/Arith/Linear/ToExpr.rs");
                            }
                            pub mod VarRename {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/Arith/Linear/VarRename.rs");
                            }
                        }
                        pub mod Types {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/Arith/Types.rs");
                        }
                    }
                    pub mod CastLike {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/CastLike.rs");
                    }
                    pub mod CheckResult {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/CheckResult.rs");
                    }
                    pub mod VarRename {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Grind/VarRename.rs");
                    }
                }
                pub mod Repeat {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Repeat.rs");
                }
                pub mod Simp {
                    pub mod Arith {
                        pub mod Nat {
                            pub mod Basic {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Simp/Arith/Nat/Basic.rs");
                            }
                        }
                        pub mod Util {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Simp/Arith/Util.rs");
                        }
                    }
                    pub mod SimpCongrTheorems {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Tactic/Simp/SimpCongrTheorems.rs");
                    }
                }
            }
            pub mod Transform {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/Transform.rs");
            }
            pub mod TransparencyMode {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/TransparencyMode.rs");
            }
            pub mod WHNF {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Meta/WHNF.rs");
            }
        }
        pub mod MetavarContext {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/MetavarContext.rs");
        }
        pub mod Modifiers {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Modifiers.rs");
        }
        pub mod MonadEnv {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/MonadEnv.rs");
        }
        pub mod Namespace {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Namespace.rs");
        }
        pub mod OriginalConstKind {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/OriginalConstKind.rs");
        }
        pub mod Parser {
            pub mod Basic {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Parser/Basic.rs");
            }
            pub mod Extension {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Parser/Extension.rs");
            }
            pub mod StrInterpolation {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Parser/StrInterpolation.rs");
            }
            pub mod Term {
                pub mod Doc {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Parser/Term/Doc.rs");
                }
            }
            pub mod Types {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Parser/Types.rs");
            }
        }
        pub mod ParserCompiler {
            pub mod Attribute {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ParserCompiler/Attribute.rs");
            }
        }
        pub mod PrettyPrinter {
            pub mod Delaborator {
                pub mod Attributes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/PrettyPrinter/Delaborator/Attributes.rs");
                }
                pub mod Options {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/PrettyPrinter/Delaborator/Options.rs");
                }
                pub mod SubExpr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/PrettyPrinter/Delaborator/SubExpr.rs");
                }
            }
        }
        pub mod PrivateName {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/PrivateName.rs");
        }
        pub mod ProjFns {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ProjFns.rs");
        }
        pub mod ReducibilityAttrs {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ReducibilityAttrs.rs");
        }
        pub mod Replay {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Replay.rs");
        }
        pub mod ReservedNameAction {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ReservedNameAction.rs");
        }
        pub mod ResolveName {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ResolveName.rs");
        }
        pub mod Runtime {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Runtime.rs");
        }
        pub mod ScopedEnvExtension {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ScopedEnvExtension.rs");
        }
        pub mod Server {
            pub mod AsyncList {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/AsyncList.rs");
            }
            pub mod Completion {
                pub mod CompletionItemCompression {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/Completion/CompletionItemCompression.rs");
                }
                pub mod EligibleHeaderDecls {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/Completion/EligibleHeaderDecls.rs");
                }
            }
            pub mod FileSource {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/FileSource.rs");
            }
            pub mod Logging {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/Logging.rs");
            }
            pub mod RequestCancellation {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/RequestCancellation.rs");
            }
            pub mod Rpc {
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/Rpc/Basic.rs");
                }
            }
            pub mod ServerTask {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/ServerTask.rs");
            }
            pub mod Test {
                pub mod Refs {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Server/Test/Refs.rs");
                }
            }
        }
        pub mod Setup {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Setup.rs");
        }
        pub mod Structure {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Structure.rs");
        }
        pub mod SubExpr {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/SubExpr.rs");
        }
        pub mod Syntax {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Syntax.rs");
        }
        pub mod ToExpr {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ToExpr.rs");
        }
        pub mod ToLevel {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/ToLevel.rs");
        }
        pub mod Util {
            pub mod CollectAxioms {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/CollectAxioms.rs");
            }
            pub mod CollectFVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/CollectFVars.rs");
            }
            pub mod CollectLevelMVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/CollectLevelMVars.rs");
            }
            pub mod CollectLevelParams {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/CollectLevelParams.rs");
            }
            pub mod CollectLooseBVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/CollectLooseBVars.rs");
            }
            pub mod CollectMVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/CollectMVars.rs");
            }
            pub mod Diff {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Diff.rs");
            }
            pub mod FindExpr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/FindExpr.rs");
            }
            pub mod FindLevelMVar {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/FindLevelMVar.rs");
            }
            pub mod FindMVar {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/FindMVar.rs");
            }
            pub mod FoldConsts {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/FoldConsts.rs");
            }
            pub mod ForEachExpr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ForEachExpr.rs");
            }
            pub mod ForEachExprWhere {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ForEachExprWhere.rs");
            }
            pub mod FVarSubset {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/FVarSubset.rs");
            }
            pub mod HasConstCache {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/HasConstCache.rs");
            }
            pub mod Heartbeats {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Heartbeats.rs");
            }
            pub mod InstantiateLevelParams {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/InstantiateLevelParams.rs");
            }
            pub mod LakePath {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/LakePath.rs");
            }
            pub mod LeanOptions {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/LeanOptions.rs");
            }
            pub mod MonadBacktrack {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/MonadBacktrack.rs");
            }
            pub mod MonadCache {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/MonadCache.rs");
            }
            pub mod NumApps {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/NumApps.rs");
            }
            pub mod NumObjs {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/NumObjs.rs");
            }
            pub mod OccursCheck {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/OccursCheck.rs");
            }
            pub mod ParamMinimizer {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ParamMinimizer.rs");
            }
            pub mod Path {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Path.rs");
            }
            pub mod PPExt {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/PPExt.rs");
            }
            pub mod Profile {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Profile.rs");
            }
            pub mod Profiler {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Profiler.rs");
            }
            pub mod ProfilerServer {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ProfilerServer.rs");
            }
            pub mod PtrSet {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/PtrSet.rs");
            }
            pub mod RecDepth {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/RecDepth.rs");
            }
            pub mod Recognizers {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Recognizers.rs");
            }
            pub mod ReplaceExpr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ReplaceExpr.rs");
            }
            pub mod ReplaceLevel {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ReplaceLevel.rs");
            }
            pub mod SafeExponentiation {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/SafeExponentiation.rs");
            }
            pub mod SCC {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/SCC.rs");
            }
            pub mod ShareCommon {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/ShareCommon.rs");
            }
            pub mod Sorry {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Sorry.rs");
            }
            pub mod SortExprs {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/SortExprs.rs");
            }
            pub mod Trace {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/Trace.rs");
            }
            pub mod UnusedBinders {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Util/UnusedBinders.rs");
            }
        }
        pub mod Widget {
            pub mod TaggedText {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Widget/TaggedText.rs");
            }
            pub mod Types {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_1/src/gen/Lean/Widget/Types.rs");
            }
        }
    }
}
