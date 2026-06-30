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
            pub use gen_lean_part_1::r#gen::Lean::AddDecl::*;
        }
        pub mod Attributes {
            pub use gen_lean_part_1::r#gen::Lean::Attributes::*;
        }
        pub mod AuxRecursor {
            pub use gen_lean_part_1::r#gen::Lean::AuxRecursor::*;
        }
        pub mod BuiltinDocAttr {
            pub use gen_lean_part_1::r#gen::Lean::BuiltinDocAttr::*;
        }
        pub mod Class {
            pub use gen_lean_part_1::r#gen::Lean::Class::*;
        }
        pub mod CompactedRegion {
            pub use gen_lean_part_1::r#gen::Lean::CompactedRegion::*;
        }
        pub mod Compiler {
            pub mod index {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler.rs");
            }
            pub use index::*;
            pub mod BorrowedAnnotation {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::BorrowedAnnotation::*;
            }
            pub mod ClosedTermCache {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::ClosedTermCache::*;
            }
            pub mod CSimpAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::CSimpAttr::*;
            }
            pub mod ExportAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::ExportAttr::*;
            }
            pub mod ExternAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::ExternAttr::*;
            }
            pub mod FFI {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::FFI::*;
            }
            pub mod ImplementedByAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::ImplementedByAttr::*;
            }
            pub mod InitAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::InitAttr::*;
            }
            pub mod InlineAttrs {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::InlineAttrs::*;
            }
            pub mod IR {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::*;
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::Basic::*;
                }
                pub mod Checker {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::Checker::*;
                }
                pub mod CompilerM {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::CompilerM::*;
                }
                pub mod EmitLLVM {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::EmitLLVM::*;
                }
                pub mod EmitUtil {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::EmitUtil::*;
                }
                pub mod Format {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::Format::*;
                }
                pub mod LLVMBindings {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::LLVMBindings::*;
                }
                pub mod Meta {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::Meta::*;
                }
                pub mod NormIds {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::NormIds::*;
                }
                pub mod Sorry {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::Sorry::*;
                }
                pub mod ToIR {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::ToIR::*;
                }
                pub mod ToIRType {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::ToIRType::*;
                }
                pub mod UnboxResult {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::IR::UnboxResult::*;
                }
            }
            pub mod LCNF {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF.rs");
                }
                pub use index::*;
                pub mod AlphaEqv {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::AlphaEqv::*;
                }
                pub mod AuxDeclCache {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::AuxDeclCache::*;
                }
                pub mod BaseTypes {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::BaseTypes::*;
                }
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Basic::*;
                }
                pub mod Bind {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Bind::*;
                }
                pub mod Check {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Check::*;
                }
                pub mod Closure {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Closure::*;
                }
                pub mod CoalesceRC {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::CoalesceRC::*;
                }
                pub mod CompatibleTypes {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::CompatibleTypes::*;
                }
                pub mod CompilerM {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::CompilerM::*;
                }
                pub mod ConfigOptions {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ConfigOptions::*;
                }
                pub mod CSE {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::CSE::*;
                }
                pub mod DeclHash {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::DeclHash::*;
                }
                pub mod DependsOn {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::DependsOn::*;
                }
                pub mod ElimDead {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ElimDead::*;
                }
                pub mod ElimDeadBranches {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ElimDeadBranches::*;
                }
                pub mod EmitRust {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::EmitRust::*;
                }
                pub mod EmitUtil {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::EmitUtil::*;
                }
                pub mod ExpandResetReuse {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ExpandResetReuse::*;
                }
                pub mod ExplicitBoxing {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ExplicitBoxing::*;
                }
                pub mod ExplicitRC {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ExplicitRC::*;
                }
                pub mod ExtractClosed {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ExtractClosed::*;
                }
                pub mod FixedParams {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::FixedParams::*;
                }
                pub mod FloatLetIn {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::FloatLetIn::*;
                }
                pub mod FVarUtil {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::FVarUtil::*;
                }
                pub mod InferBorrow {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::InferBorrow::*;
                }
                pub mod InferType {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::InferType::*;
                }
                pub mod Internalize {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Internalize::*;
                }
                pub mod Irrelevant {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Irrelevant::*;
                }
                pub mod JoinPoints {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::JoinPoints::*;
                }
                pub mod LambdaLifting {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::LambdaLifting::*;
                }
                pub mod LCtx {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::LCtx::*;
                }
                pub mod Level {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Level::*;
                }
                pub mod LiveVars {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::LiveVars::*;
                }
                pub mod Main {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Main.rs");
                }
                pub mod MonadScope {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::MonadScope::*;
                }
                pub mod MonoTypes {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::MonoTypes::*;
                }
                pub mod OtherDecl {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::OtherDecl::*;
                }
                pub mod Passes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Passes.rs");
                }
                pub mod PassManager {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PassManager::*;
                }
                pub mod PhaseExt {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PhaseExt::*;
                }
                pub mod PrettyPrinter {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PrettyPrinter::*;
                }
                pub mod Probing {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Probing::*;
                }
                pub mod PropagateBorrow {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PropagateBorrow::*;
                }
                pub mod PublicDeclsExt {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PublicDeclsExt::*;
                }
                pub mod PullFunDecls {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PullFunDecls::*;
                }
                pub mod PullLetDecls {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::PullLetDecls::*;
                }
                pub mod PushProj {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/PushProj.rs");
                }
                pub mod ReduceArity {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/ReduceArity.rs");
                }
                pub mod ReduceJpArity {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/ReduceJpArity.rs");
                }
                pub mod Renaming {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Renaming::*;
                }
                pub mod ResetReuse {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ResetReuse::*;
                }
                pub mod ScopeM {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ScopeM::*;
                }
                pub mod Simp {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp.rs");
                    }
                    pub use index::*;
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Simp::Basic::*;
                    }
                    pub mod Config {
                        pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Simp::Config::*;
                    }
                    pub mod ConstantFold {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/ConstantFold.rs");
                    }
                    pub mod DefaultAlt {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/DefaultAlt.rs");
                    }
                    pub mod DiscrM {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/DiscrM.rs");
                    }
                    pub mod FunDeclInfo {
                        pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Simp::FunDeclInfo::*;
                    }
                    pub mod InlineCandidate {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/InlineCandidate.rs");
                    }
                    pub mod InlineProj {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/InlineProj.rs");
                    }
                    pub mod JpCases {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/JpCases.rs");
                    }
                    pub mod Main {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/Main.rs");
                    }
                    pub mod SimpM {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/SimpM.rs");
                    }
                    pub mod SimpValue {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/SimpValue.rs");
                    }
                    pub mod Used {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Simp/Used.rs");
                    }
                }
                pub mod SimpCase {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::SimpCase::*;
                }
                pub mod SimpleGroundExpr {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::SimpleGroundExpr::*;
                }
                pub mod Specialize {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Specialize.rs");
                }
                pub mod SpecInfo {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/SpecInfo.rs");
                }
                pub mod SplitSCC {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::SplitSCC::*;
                }
                pub mod StructProjCases {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/StructProjCases.rs");
                }
                pub mod ToDecl {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/ToDecl.rs");
                }
                pub mod ToExpr {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ToExpr::*;
                }
                pub mod ToImpure {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/ToImpure.rs");
                }
                pub mod ToImpureType {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ToImpureType::*;
                }
                pub mod ToLCNF {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/ToLCNF.rs");
                }
                pub mod ToMono {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/ToMono.rs");
                }
                pub mod Toposort {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Toposort.rs");
                }
                pub mod Types {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Types::*;
                }
                pub mod Util {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Util::*;
                }
                pub mod Visibility {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/LCNF/Visibility.rs");
                }
            }
            pub mod Main {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Compiler/Main.rs");
            }
            pub mod MetaAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::MetaAttr::*;
            }
            pub mod ModPkgExt {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::ModPkgExt::*;
            }
            pub mod NameDemangling {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::NameDemangling::*;
            }
            pub mod NameMangling {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::NameMangling::*;
            }
            pub mod NeverExtractAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::NeverExtractAttr::*;
            }
            pub mod NoncomputableAttr {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::NoncomputableAttr::*;
            }
            pub mod Old {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::Old::*;
            }
            pub mod Options {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::Options::*;
            }
            pub mod Specialize {
                pub use gen_lean_part_1::r#gen::Lean::Compiler::Specialize::*;
            }
        }
        pub mod CoreM {
            pub use gen_lean_part_1::r#gen::Lean::CoreM::*;
        }
        pub mod Data {
            pub use gen_lean_part_1::r#gen::Lean::Data::*;
            pub mod Array {
                pub use gen_lean_part_1::r#gen::Lean::Data::Array::*;
            }
            pub mod AssocList {
                pub use gen_lean_part_1::r#gen::Lean::Data::AssocList::*;
            }
            pub mod DeclarationRange {
                pub use gen_lean_part_1::r#gen::Lean::Data::DeclarationRange::*;
            }
            pub mod EditDistance {
                pub use gen_lean_part_1::r#gen::Lean::Data::EditDistance::*;
            }
            pub mod Format {
                pub use gen_lean_part_1::r#gen::Lean::Data::Format::*;
            }
            pub mod Iterators {
                pub use gen_lean_part_1::r#gen::Lean::Data::Iterators::*;
                pub mod Producers {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Iterators::Producers::*;
                    pub mod PersistentHashMap {
                        pub use gen_lean_part_1::r#gen::Lean::Data::Iterators::Producers::PersistentHashMap::*;
                    }
                }
            }
            pub mod Json {
                pub use gen_lean_part_1::r#gen::Lean::Data::Json::*;
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Json::Basic::*;
                }
                pub mod Elab {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Json::Elab::*;
                }
                pub mod FromToJson {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Json::FromToJson::*;
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Data::Json::FromToJson::Basic::*;
                    }
                    pub mod Extra {
                        pub use gen_lean_part_1::r#gen::Lean::Data::Json::FromToJson::Extra::*;
                    }
                }
                pub mod Parser {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Json::Parser::*;
                }
                pub mod Printer {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Json::Printer::*;
                }
                pub mod Stream {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Json::Stream::*;
                }
            }
            pub mod JsonRpc {
                pub use gen_lean_part_1::r#gen::Lean::Data::JsonRpc::*;
            }
            pub mod KVMap {
                pub use gen_lean_part_1::r#gen::Lean::Data::KVMap::*;
            }
            pub mod LBool {
                pub use gen_lean_part_1::r#gen::Lean::Data::LBool::*;
            }
            pub mod LOption {
                pub use gen_lean_part_1::r#gen::Lean::Data::LOption::*;
            }
            pub mod Lsp {
                pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::*;
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Basic::*;
                }
                pub mod BasicAux {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::BasicAux::*;
                }
                pub mod CancelParams {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::CancelParams::*;
                }
                pub mod Capabilities {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Capabilities::*;
                }
                pub mod Client {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Client::*;
                }
                pub mod CodeActions {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::CodeActions::*;
                }
                pub mod Communication {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Communication::*;
                }
                pub mod Diagnostics {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Diagnostics::*;
                }
                pub mod Extra {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Extra::*;
                }
                pub mod InitShutdown {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::InitShutdown::*;
                }
                pub mod Internal {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Internal::*;
                }
                pub mod Ipc {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Ipc::*;
                }
                pub mod LanguageFeatures {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::LanguageFeatures::*;
                }
                pub mod TextSync {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::TextSync::*;
                }
                pub mod Utf16 {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Utf16::*;
                }
                pub mod Window {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Window::*;
                }
                pub mod Workspace {
                    pub use gen_lean_part_1::r#gen::Lean::Data::Lsp::Workspace::*;
                }
            }
            pub mod Name {
                pub use gen_lean_part_1::r#gen::Lean::Data::Name::*;
            }
            pub mod NameMap {
                pub use gen_lean_part_1::r#gen::Lean::Data::NameMap::*;
                pub mod AdditionalOperations {
                    pub use gen_lean_part_1::r#gen::Lean::Data::NameMap::AdditionalOperations::*;
                }
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Data::NameMap::Basic::*;
                }
            }
            pub mod NameTrie {
                pub use gen_lean_part_1::r#gen::Lean::Data::NameTrie::*;
            }
            pub mod OpenDecl {
                pub use gen_lean_part_1::r#gen::Lean::Data::OpenDecl::*;
            }
            pub mod Options {
                pub use gen_lean_part_1::r#gen::Lean::Data::Options::*;
            }
            pub mod PersistentArray {
                pub use gen_lean_part_1::r#gen::Lean::Data::PersistentArray::*;
            }
            pub mod PersistentHashMap {
                pub use gen_lean_part_1::r#gen::Lean::Data::PersistentHashMap::*;
            }
            pub mod PersistentHashSet {
                pub use gen_lean_part_1::r#gen::Lean::Data::PersistentHashSet::*;
            }
            pub mod Position {
                pub use gen_lean_part_1::r#gen::Lean::Data::Position::*;
            }
            pub mod PPContext {
                pub use gen_lean_part_1::r#gen::Lean::Data::PPContext::*;
            }
            pub mod PrefixTree {
                pub use gen_lean_part_1::r#gen::Lean::Data::PrefixTree::*;
            }
            pub mod RArray {
                pub use gen_lean_part_1::r#gen::Lean::Data::RArray::*;
            }
            pub mod RBMap {
                pub use gen_lean_part_1::r#gen::Lean::Data::RBMap::*;
            }
            pub mod RBTree {
                pub use gen_lean_part_1::r#gen::Lean::Data::RBTree::*;
            }
            pub mod SMap {
                pub use gen_lean_part_1::r#gen::Lean::Data::SMap::*;
            }
            pub mod SSet {
                pub use gen_lean_part_1::r#gen::Lean::Data::SSet::*;
            }
            pub mod Trie {
                pub use gen_lean_part_1::r#gen::Lean::Data::Trie::*;
            }
        }
        pub mod Declaration {
            pub use gen_lean_part_1::r#gen::Lean::Declaration::*;
        }
        pub mod DeclarationRange {
            pub use gen_lean_part_1::r#gen::Lean::DeclarationRange::*;
        }
        pub mod DefEqAttrib {
            pub use gen_lean_part_1::r#gen::Lean::DefEqAttrib::*;
        }
        pub mod DeprecatedModule {
            pub use gen_lean_part_1::r#gen::Lean::DeprecatedModule::*;
        }
        pub mod DocString {
            pub mod index {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/DocString.rs");
            }
            pub use index::*;
            pub mod Extension {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Extension::*;
            }
            pub mod Formatter {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/DocString/Formatter.rs");
            }
            pub mod Links {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Links::*;
            }
            pub mod Markdown {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Markdown::*;
            }
            pub mod Parser {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/DocString/Parser.rs");
            }
            pub mod Syntax {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/DocString/Syntax.rs");
            }
            pub mod Types {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Types::*;
            }
        }
        pub mod Elab {
            pub mod Attributes {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Attributes.rs");
            }
            pub mod BindersUtil {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/BindersUtil.rs");
            }
            pub mod Command {
                pub mod Scope {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Command/Scope.rs");
                }
            }
            pub mod Config {
                pub use gen_lean_part_1::r#gen::Lean::Elab::Config::*;
            }
            pub mod ConfigEval {
                pub mod Commands {
                    pub use gen_lean_part_1::r#gen::Lean::Elab::ConfigEval::Commands::*;
                }
            }
            pub mod DeclarationRange {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/DeclarationRange.rs");
            }
            pub mod DeclUtil {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/DeclUtil.rs");
            }
            pub mod DeprecatedSyntax {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/DeprecatedSyntax.rs");
            }
            pub mod DocString {
                pub mod Builtin {
                    pub mod Parsing {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::DocString::Builtin::Parsing::*;
                    }
                }
            }
            pub mod ErrorUtils {
                pub use gen_lean_part_1::r#gen::Lean::Elab::ErrorUtils::*;
            }
            pub mod Exception {
                pub use gen_lean_part_1::r#gen::Lean::Elab::Exception::*;
            }
            pub mod Import {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Import.rs");
            }
            pub mod InfoTree {
                pub use gen_lean_part_1::r#gen::Lean::Elab::InfoTree::*;
                pub mod InlayHints {
                    pub use gen_lean_part_1::r#gen::Lean::Elab::InfoTree::InlayHints::*;
                }
                pub mod Main {
                    pub use gen_lean_part_1::r#gen::Lean::Elab::InfoTree::Main::*;
                }
                pub mod Types {
                    pub use gen_lean_part_1::r#gen::Lean::Elab::InfoTree::Types::*;
                }
            }
            pub mod InheritDoc {
                pub use gen_lean_part_1::r#gen::Lean::Elab::InheritDoc::*;
            }
            pub mod Mixfix {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Mixfix.rs");
            }
            pub mod Open {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Open.rs");
            }
            pub mod ParseImportsFast {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/ParseImportsFast.rs");
            }
            pub mod PreDefinition {
                pub mod Structural {
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::Structural::Basic::*;
                    }
                    pub mod IndGroupInfo {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::Structural::IndGroupInfo::*;
                    }
                    pub mod Preprocess {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::Structural::Preprocess::*;
                    }
                }
                pub mod TerminationHint {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/PreDefinition/TerminationHint.rs");
                }
                pub mod WF {
                    pub mod FloatRecApp {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::WF::FloatRecApp::*;
                    }
                }
            }
            pub mod RecAppSyntax {
                pub use gen_lean_part_1::r#gen::Lean::Elab::RecAppSyntax::*;
            }
            pub mod SetOption {
                pub use gen_lean_part_1::r#gen::Lean::Elab::SetOption::*;
            }
            pub mod Tactic {
                pub mod BoolToPropSimps {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Tactic/BoolToPropSimps.rs");
                }
                pub mod Omega {
                    pub mod Core {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Tactic/Omega/Core.rs");
                    }
                    pub mod MinNatAbs {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::Tactic::Omega::MinNatAbs::*;
                    }
                    pub mod OmegaM {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Tactic/Omega/OmegaM.rs");
                    }
                }
            }
            pub mod Util {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/Util.rs");
            }
            pub mod WhereFinally {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Elab/WhereFinally.rs");
            }
        }
        pub mod EnvExtension {
            pub use gen_lean_part_1::r#gen::Lean::EnvExtension::*;
        }
        pub mod Environment {
            pub use gen_lean_part_1::r#gen::Lean::Environment::*;
        }
        pub mod ErrorExplanation {
            pub use gen_lean_part_1::r#gen::Lean::ErrorExplanation::*;
        }
        pub mod Exception {
            pub use gen_lean_part_1::r#gen::Lean::Exception::*;
        }
        pub mod Expr {
            pub use gen_lean_part_1::r#gen::Lean::Expr::*;
        }
        pub mod ExtraModUses {
            pub use gen_lean_part_1::r#gen::Lean::ExtraModUses::*;
        }
        pub mod HeadIndex {
            pub use gen_lean_part_1::r#gen::Lean::HeadIndex::*;
        }
        pub mod Hygiene {
            pub use gen_lean_part_1::r#gen::Lean::Hygiene::*;
        }
        pub mod ImportingFlag {
            pub use gen_lean_part_1::r#gen::Lean::ImportingFlag::*;
        }
        pub mod InternalExceptionId {
            pub use gen_lean_part_1::r#gen::Lean::InternalExceptionId::*;
        }
        pub mod KeyedDeclsAttribute {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/KeyedDeclsAttribute.rs");
        }
        pub mod LabelAttribute {
            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/LabelAttribute.rs");
        }
        pub mod Language {
            pub mod Basic {
                pub use gen_lean_part_1::r#gen::Lean::Language::Basic::*;
            }
            pub mod Util {
                pub use gen_lean_part_1::r#gen::Lean::Language::Util::*;
            }
        }
        pub mod Level {
            pub use gen_lean_part_1::r#gen::Lean::Level::*;
        }
        pub mod Linter {
            pub mod Deprecated {
                pub use gen_lean_part_1::r#gen::Lean::Linter::Deprecated::*;
            }
            pub mod EnvLinter {
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Linter::EnvLinter::Basic::*;
                }
                pub mod Nolint {
                    pub use gen_lean_part_1::r#gen::Lean::Linter::EnvLinter::Nolint::*;
                }
            }
            pub mod Init {
                pub use gen_lean_part_1::r#gen::Lean::Linter::Init::*;
            }
            pub mod PersistentLintLog {
                pub use gen_lean_part_1::r#gen::Lean::Linter::PersistentLintLog::*;
            }
        }
        pub mod LoadDynlib {
            pub use gen_lean_part_1::r#gen::Lean::LoadDynlib::*;
        }
        pub mod LocalContext {
            pub use gen_lean_part_1::r#gen::Lean::LocalContext::*;
        }
        pub mod Log {
            pub use gen_lean_part_1::r#gen::Lean::Log::*;
        }
        pub mod Message {
            pub use gen_lean_part_1::r#gen::Lean::Message::*;
        }
        pub mod Meta {
            pub mod AbstractMVars {
                pub use gen_lean_part_1::r#gen::Lean::Meta::AbstractMVars::*;
            }
            pub mod AbstractNestedProofs {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/AbstractNestedProofs.rs");
            }
            pub mod ACLt {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ACLt::*;
            }
            pub mod AppBuilder {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/AppBuilder.rs");
            }
            pub mod ArgsPacker {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/ArgsPacker.rs");
                }
                pub use index::*;
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::ArgsPacker::Basic::*;
                }
            }
            pub mod Basic {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Basic::*;
            }
            pub mod BinderNameHint {
                pub use gen_lean_part_1::r#gen::Lean::Meta::BinderNameHint::*;
            }
            pub mod Canonicalizer {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Canonicalizer::*;
            }
            pub mod CasesInfo {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CasesInfo::*;
            }
            pub mod Check {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Check::*;
            }
            pub mod CheckTactic {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CheckTactic::*;
            }
            pub mod Closure {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Closure.rs");
            }
            pub mod Coe {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Coe.rs");
            }
            pub mod CoeAttr {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CoeAttr::*;
            }
            pub mod CollectFVars {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CollectFVars::*;
            }
            pub mod CollectMVars {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CollectMVars::*;
            }
            pub mod CompletionName {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CompletionName::*;
            }
            pub mod CongrTheorems {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/CongrTheorems.rs");
            }
            pub mod Constructions {
                pub mod CasesOn {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Constructions::CasesOn::*;
                }
                pub mod CtorIdx {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Constructions::CtorIdx::*;
                }
                pub mod RecOn {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Constructions::RecOn::*;
                }
                pub mod SparseCasesOn {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Constructions::SparseCasesOn::*;
                }
            }
            pub mod CtorRecognizer {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CtorRecognizer::*;
            }
            pub mod DecLevel {
                pub use gen_lean_part_1::r#gen::Lean::Meta::DecLevel::*;
            }
            pub mod DiscrTree {
                pub use gen_lean_part_1::r#gen::Lean::Meta::DiscrTree::*;
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::DiscrTree::Basic::*;
                }
                pub mod Main {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::DiscrTree::Main::*;
                }
                pub mod Types {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::DiscrTree::Types::*;
                }
                pub mod Util {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::DiscrTree::Util::*;
                }
            }
            pub mod Eqns {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Eqns.rs");
            }
            pub mod Eval {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Eval::*;
            }
            pub mod ExprDefEq {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/ExprDefEq.rs");
            }
            pub mod ExprLens {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ExprLens::*;
            }
            pub mod ExprTraverse {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ExprTraverse::*;
            }
            pub mod ForEachExpr {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ForEachExpr::*;
            }
            pub mod FunInfo {
                pub use gen_lean_part_1::r#gen::Lean::Meta::FunInfo::*;
            }
            pub mod GeneralizeTelescope {
                pub use gen_lean_part_1::r#gen::Lean::Meta::GeneralizeTelescope::*;
            }
            pub mod GeneralizeVars {
                pub use gen_lean_part_1::r#gen::Lean::Meta::GeneralizeVars::*;
            }
            pub mod GetUnfoldableConst {
                pub use gen_lean_part_1::r#gen::Lean::Meta::GetUnfoldableConst::*;
            }
            pub mod HasAssignableMVar {
                pub use gen_lean_part_1::r#gen::Lean::Meta::HasAssignableMVar::*;
            }
            pub mod HasNotBit {
                pub use gen_lean_part_1::r#gen::Lean::Meta::HasNotBit::*;
            }
            pub mod HaveTelescope {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/HaveTelescope.rs");
            }
            pub mod Inductive {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Inductive::*;
            }
            pub mod InferType {
                pub use gen_lean_part_1::r#gen::Lean::Meta::InferType::*;
            }
            pub mod Instances {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Instances::*;
            }
            pub mod IntInstTesters {
                pub use gen_lean_part_1::r#gen::Lean::Meta::IntInstTesters::*;
            }
            pub mod Iterator {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Iterator::*;
            }
            pub mod KAbstract {
                pub use gen_lean_part_1::r#gen::Lean::Meta::KAbstract::*;
            }
            pub mod KExprMap {
                pub use gen_lean_part_1::r#gen::Lean::Meta::KExprMap::*;
            }
            pub mod LazyDiscrTree {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/LazyDiscrTree.rs");
            }
            pub mod LetToHave {
                pub use gen_lean_part_1::r#gen::Lean::Meta::LetToHave::*;
            }
            pub mod LevelDefEq {
                pub use gen_lean_part_1::r#gen::Lean::Meta::LevelDefEq::*;
            }
            pub mod LitValues {
                pub use gen_lean_part_1::r#gen::Lean::Meta::LitValues::*;
            }
            pub mod Match {
                pub mod AltTelescopes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Match/AltTelescopes.rs");
                }
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Match/Basic.rs");
                }
                pub mod CaseArraySizes {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Match/CaseArraySizes.rs");
                }
                pub mod CaseValues {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Match/CaseValues.rs");
                }
                pub mod MatchEqsExt {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Match/MatchEqsExt.rs");
                }
                pub mod MatcherApp {
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Match::MatcherApp::Basic::*;
                    }
                }
                pub mod MatcherInfo {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Match::MatcherInfo::*;
                }
                pub mod MatchPatternAttr {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Match::MatchPatternAttr::*;
                }
                pub mod MVarRenaming {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Match::MVarRenaming::*;
                }
                pub mod NamedPatterns {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Match/NamedPatterns.rs");
                }
                pub mod Value {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Match::Value::*;
                }
            }
            pub mod MatchUtil {
                pub use gen_lean_part_1::r#gen::Lean::Meta::MatchUtil::*;
            }
            pub mod MonadSimp {
                pub use gen_lean_part_1::r#gen::Lean::Meta::MonadSimp::*;
            }
            pub mod NatInstTesters {
                pub use gen_lean_part_1::r#gen::Lean::Meta::NatInstTesters::*;
            }
            pub mod Native {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Native.rs");
            }
            pub mod NatTable {
                pub use gen_lean_part_1::r#gen::Lean::Meta::NatTable::*;
            }
            pub mod Offset {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Offset::*;
            }
            pub mod Order {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Order.rs");
            }
            pub mod PPBinder {
                pub use gen_lean_part_1::r#gen::Lean::Meta::PPBinder::*;
            }
            pub mod PPGoal {
                pub use gen_lean_part_1::r#gen::Lean::Meta::PPGoal::*;
            }
            pub mod PProdN {
                pub use gen_lean_part_1::r#gen::Lean::Meta::PProdN::*;
            }
            pub mod ProdN {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ProdN::*;
            }
            pub mod RecExt {
                pub use gen_lean_part_1::r#gen::Lean::Meta::RecExt::*;
            }
            pub mod RecursorInfo {
                pub use gen_lean_part_1::r#gen::Lean::Meta::RecursorInfo::*;
            }
            pub mod Reduce {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Reduce::*;
            }
            pub mod ReduceEval {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ReduceEval::*;
            }
            pub mod SameCtorUtils {
                pub use gen_lean_part_1::r#gen::Lean::Meta::SameCtorUtils::*;
            }
            pub mod SizeOf {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/SizeOf.rs");
            }
            pub mod Sorry {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Sorry::*;
            }
            pub mod StringLitProof {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/StringLitProof.rs");
            }
            pub mod Structure {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Structure.rs");
            }
            pub mod Sym {
                pub mod AbstractS {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/AbstractS.rs");
                }
                pub mod AlphaShareBuilder {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/AlphaShareBuilder.rs");
                }
                pub mod AlphaShareCommon {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::AlphaShareCommon::*;
                }
                pub mod Apply {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Apply.rs");
                }
                pub mod Arith {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith.rs");
                    }
                    pub use index::*;
                    pub mod Classify {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/Classify.rs");
                    }
                    pub mod DenoteExpr {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/DenoteExpr.rs");
                    }
                    pub mod EvalNum {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/EvalNum.rs");
                    }
                    pub mod Functions {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/Functions.rs");
                    }
                    pub mod MonadCanon {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/MonadCanon.rs");
                    }
                    pub mod MonadRing {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/MonadRing.rs");
                    }
                    pub mod MonadSemiring {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/MonadSemiring.rs");
                    }
                    pub mod MonadVar {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/MonadVar.rs");
                    }
                    pub mod Poly {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Arith::Poly::*;
                    }
                    pub mod Reify {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/Reify.rs");
                    }
                    pub mod ToExpr {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Arith::ToExpr::*;
                    }
                    pub mod Types {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Arith/Types.rs");
                    }
                    pub mod VarRename {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Arith::VarRename::*;
                    }
                }
                pub mod Canon {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Canon.rs");
                }
                pub mod DSimp {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp.rs");
                    }
                    pub use index::*;
                    pub mod App {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/App.rs");
                    }
                    pub mod DSimpM {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/DSimpM.rs");
                    }
                    pub mod DSimproc {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/DSimproc.rs");
                    }
                    pub mod Forall {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Forall.rs");
                    }
                    pub mod Lambda {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Lambda.rs");
                    }
                    pub mod Let {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Let.rs");
                    }
                    pub mod Main {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Main.rs");
                    }
                    pub mod Reduce {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Reduce.rs");
                    }
                    pub mod Result {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Result.rs");
                    }
                    pub mod Variant {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/DSimp/Variant.rs");
                    }
                }
                pub mod Eta {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Eta::*;
                }
                pub mod ExprPtr {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::ExprPtr::*;
                }
                pub mod InferType {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/InferType.rs");
                }
                pub mod InstantiateMVarsS {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/InstantiateMVarsS.rs");
                }
                pub mod InstantiateS {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/InstantiateS.rs");
                }
                pub mod Intro {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Intro.rs");
                }
                pub mod IsClass {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/IsClass.rs");
                }
                pub mod LitValues {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::LitValues::*;
                }
                pub mod LooseBVarsS {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/LooseBVarsS.rs");
                }
                pub mod MaxFVar {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/MaxFVar.rs");
                }
                pub mod Offset {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Offset::*;
                }
                pub mod Pattern {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Pattern.rs");
                }
                pub mod ProofInstInfo {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/ProofInstInfo.rs");
                }
                pub mod ReplaceS {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/ReplaceS.rs");
                }
                pub mod Simp {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp.rs");
                    }
                    pub use index::*;
                    pub mod App {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/App.rs");
                    }
                    pub mod Attr {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Attr.rs");
                    }
                    pub mod CongrInfo {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/CongrInfo.rs");
                    }
                    pub mod ControlFlow {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/ControlFlow.rs");
                    }
                    pub mod Debug {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Debug.rs");
                    }
                    pub mod Discharger {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Discharger.rs");
                    }
                    pub mod DiscrTree {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/DiscrTree.rs");
                    }
                    pub mod EvalGround {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/EvalGround.rs");
                    }
                    pub mod Forall {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Forall.rs");
                    }
                    pub mod Goal {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Goal.rs");
                    }
                    pub mod Have {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Have.rs");
                    }
                    pub mod Lambda {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Lambda.rs");
                    }
                    pub mod Main {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Main.rs");
                    }
                    pub mod RegisterCommand {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/RegisterCommand.rs");
                    }
                    pub mod Result {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Result.rs");
                    }
                    pub mod Rewrite {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Rewrite.rs");
                    }
                    pub mod SimpM {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/SimpM.rs");
                    }
                    pub mod Simproc {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Simproc.rs");
                    }
                    pub mod Telescope {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Telescope.rs");
                    }
                    pub mod Theorems {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Theorems.rs");
                    }
                    pub mod Variant {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Simp/Variant.rs");
                    }
                }
                pub mod SymM {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/SymM.rs");
                }
                pub mod SynthInstance {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/SynthInstance.rs");
                }
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Sym/Util.rs");
                }
            }
            pub mod SynthInstance {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/SynthInstance.rs");
            }
            pub mod Tactic {
                pub mod Assert {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Assert.rs");
                }
                pub mod Assumption {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Assumption.rs");
                }
                pub mod AuxLemma {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/AuxLemma.rs");
                }
                pub mod Backtrack {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Backtrack.rs");
                }
                pub mod BVDecide {
                    pub mod External {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::BVDecide::External::*;
                    }
                    pub mod LRAT {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::*;
                        pub mod Cert {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::Cert::*;
                        }
                        pub mod Trim {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::Trim::*;
                        }
                    }
                    pub mod Reflect {
                        pub mod index {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect.rs");
                        }
                        pub use index::*;
                        pub mod Basic {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/Basic.rs");
                        }
                        pub mod ReifiedBVExpr {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedBVExpr.rs");
                        }
                        pub mod ReifiedBVLogical {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedBVLogical.rs");
                        }
                        pub mod ReifiedBVPred {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedBVPred.rs");
                        }
                        pub mod ReifiedLemmas {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedLemmas.rs");
                        }
                        pub mod Reify {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/Reify.rs");
                        }
                        pub mod SatAtBVLogical {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/BVDecide/Reflect/SatAtBVLogical.rs");
                        }
                    }
                }
                pub mod Cbv {
                    pub mod BuiltinCbvSimprocs {
                        pub mod Array {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/Array.rs");
                        }
                        pub mod Core {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/Core.rs");
                        }
                        pub mod String {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/String.rs");
                        }
                    }
                    pub mod CbvEvalExt {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/CbvEvalExt.rs");
                    }
                    pub mod CbvSimproc {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/CbvSimproc.rs");
                    }
                    pub mod ControlFlow {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/ControlFlow.rs");
                    }
                    pub mod Opaque {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Cbv::Opaque::*;
                    }
                    pub mod TheoremsLookup {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/TheoremsLookup.rs");
                    }
                    pub mod Util {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cbv/Util.rs");
                    }
                }
                pub mod Cleanup {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Cleanup.rs");
                }
                pub mod Clear {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Clear.rs");
                }
                pub mod Delta {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Delta.rs");
                }
                pub mod ElimInfo {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::ElimInfo::*;
                }
                pub mod ExposeNames {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/ExposeNames.rs");
                }
                pub mod Ext {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Ext.rs");
                }
                pub mod FunIndCollect {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/FunIndCollect.rs");
                }
                pub mod FunIndInfo {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::FunIndInfo::*;
                }
                pub mod FVarSubst {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::FVarSubst::*;
                }
                pub mod Generalize {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Generalize.rs");
                }
                pub mod Grind {
                    pub mod AC {
                        pub mod Seq {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::AC::Seq::*;
                        }
                        pub mod ToExpr {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::AC::ToExpr::*;
                        }
                        pub mod Var {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/AC/Var.rs");
                        }
                        pub mod VarRename {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::AC::VarRename::*;
                        }
                    }
                    pub mod Arith {
                        pub mod Cutsat {
                            pub mod ToIntInfo {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Arith/Cutsat/ToIntInfo.rs");
                            }
                            pub mod VarRename {
                                pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::VarRename::*;
                            }
                        }
                        pub mod FieldNormNum {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Arith/FieldNormNum.rs");
                        }
                        pub mod Linear {
                            pub mod ToExpr {
                                pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::ToExpr::*;
                            }
                            pub mod VarRename {
                                pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::VarRename::*;
                            }
                        }
                        pub mod Simproc {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Arith/Simproc.rs");
                        }
                        pub mod Types {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::Arith::Types::*;
                        }
                        pub mod Util {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Arith/Util.rs");
                        }
                    }
                    pub mod CastLike {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::CastLike::*;
                    }
                    pub mod CheckResult {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::CheckResult::*;
                    }
                    pub mod EqResolution {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/EqResolution.rs");
                    }
                    pub mod ExtAttr {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/ExtAttr.rs");
                    }
                    pub mod Extension {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Extension.rs");
                    }
                    pub mod Injection {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Injection.rs");
                    }
                    pub mod MatchDiscrOnly {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/MatchDiscrOnly.rs");
                    }
                    pub mod Parser {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Parser.rs");
                    }
                    pub mod RevertAll {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/RevertAll.rs");
                    }
                    pub mod SynthInstance {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/SynthInstance.rs");
                    }
                    pub mod Theorems {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Theorems.rs");
                    }
                    pub mod Util {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Grind/Util.rs");
                    }
                    pub mod VarRename {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::VarRename::*;
                    }
                }
                pub mod IndependentOf {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/IndependentOf.rs");
                }
                pub mod Induction {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Induction.rs");
                }
                pub mod Injection {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Injection.rs");
                }
                pub mod Intro {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Intro.rs");
                }
                pub mod Lets {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Lets.rs");
                }
                pub mod NormCast {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/NormCast.rs");
                }
                pub mod Rename {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Rename.rs");
                }
                pub mod Repeat {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Repeat::*;
                }
                pub mod Replace {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Replace.rs");
                }
                pub mod Revert {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Revert.rs");
                }
                pub mod Simp {
                    pub mod Arith {
                        pub mod index {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Arith.rs");
                        }
                        pub use index::*;
                        pub mod Int {
                            pub mod index {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Arith/Int.rs");
                            }
                            pub use index::*;
                            pub mod Basic {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Arith/Int/Basic.rs");
                            }
                            pub mod Simp {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Arith/Int/Simp.rs");
                            }
                        }
                        pub mod Nat {
                            pub mod index {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Arith/Nat.rs");
                            }
                            pub use index::*;
                            pub mod Basic {
                                pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Simp::Arith::Nat::Basic::*;
                            }
                            pub mod Simp {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Arith/Nat/Simp.rs");
                            }
                        }
                        pub mod Util {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Simp::Arith::Util::*;
                        }
                    }
                    pub mod Attr {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Attr.rs");
                    }
                    pub mod BuiltinSimprocs {
                        pub mod Array {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Array.rs");
                        }
                        pub mod BitVec {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/BitVec.rs");
                        }
                        pub mod Char {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Char.rs");
                        }
                        pub mod Core {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.rs");
                        }
                        pub mod CtorIdx {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/CtorIdx.rs");
                        }
                        pub mod Fin {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Fin.rs");
                        }
                        pub mod Int {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Int.rs");
                        }
                        pub mod List {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/List.rs");
                        }
                        pub mod Nat {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Nat.rs");
                        }
                        pub mod SInt {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.rs");
                        }
                        pub mod String {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/String.rs");
                        }
                        pub mod UInt {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.rs");
                        }
                        pub mod Util {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Util.rs");
                        }
                    }
                    pub mod LoopProtection {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/LoopProtection.rs");
                    }
                    pub mod RegisterCommand {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/RegisterCommand.rs");
                    }
                    pub mod Rewrite {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Rewrite.rs");
                    }
                    pub mod SimpCongrTheorems {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::*;
                    }
                    pub mod Simproc {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Simproc.rs");
                    }
                    pub mod SimpTheorems {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/SimpTheorems.rs");
                    }
                    pub mod Types {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Simp/Types.rs");
                    }
                }
                pub mod Subst {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Subst.rs");
                }
                pub mod Symm {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Symm.rs");
                }
                pub mod UnifyEq {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/UnifyEq.rs");
                }
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/Tactic/Util.rs");
                }
            }
            pub mod Transform {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Transform::*;
            }
            pub mod TransparencyMode {
                pub use gen_lean_part_1::r#gen::Lean::Meta::TransparencyMode::*;
            }
            pub mod UnificationHint {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/UnificationHint.rs");
            }
            pub mod WHNF {
                pub use gen_lean_part_1::r#gen::Lean::Meta::WHNF::*;
            }
            pub mod WrapInstance {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Meta/WrapInstance.rs");
            }
        }
        pub mod MetavarContext {
            pub use gen_lean_part_1::r#gen::Lean::MetavarContext::*;
        }
        pub mod Modifiers {
            pub use gen_lean_part_1::r#gen::Lean::Modifiers::*;
        }
        pub mod MonadEnv {
            pub use gen_lean_part_1::r#gen::Lean::MonadEnv::*;
        }
        pub mod Namespace {
            pub use gen_lean_part_1::r#gen::Lean::Namespace::*;
        }
        pub mod OriginalConstKind {
            pub use gen_lean_part_1::r#gen::Lean::OriginalConstKind::*;
        }
        pub mod Parser {
            pub mod Attr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Attr.rs");
            }
            pub mod Basic {
                pub use gen_lean_part_1::r#gen::Lean::Parser::Basic::*;
            }
            pub mod Command {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Command.rs");
            }
            pub mod Do {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Do.rs");
            }
            pub mod Extension {
                pub use gen_lean_part_1::r#gen::Lean::Parser::Extension::*;
            }
            pub mod Extra {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Extra.rs");
            }
            pub mod Level {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Level.rs");
            }
            pub mod Module {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Module.rs");
                }
                pub use index::*;
                pub mod Syntax {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Module/Syntax.rs");
                }
            }
            pub mod StrInterpolation {
                pub use gen_lean_part_1::r#gen::Lean::Parser::StrInterpolation::*;
            }
            pub mod Tactic {
                pub mod Doc {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Tactic/Doc.rs");
                }
            }
            pub mod Term {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Term.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/Parser/Term/Basic.rs");
                }
                pub mod Doc {
                    pub use gen_lean_part_1::r#gen::Lean::Parser::Term::Doc::*;
                }
            }
            pub mod Types {
                pub use gen_lean_part_1::r#gen::Lean::Parser::Types::*;
            }
        }
        pub mod ParserCompiler {
            pub mod index {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/ParserCompiler.rs");
            }
            pub use index::*;
            pub mod Attribute {
                pub use gen_lean_part_1::r#gen::Lean::ParserCompiler::Attribute::*;
            }
        }
        pub mod PrettyPrinter {
            pub mod Basic {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Basic.rs");
            }
            pub mod Delaborator {
                pub mod Attributes {
                    pub use gen_lean_part_1::r#gen::Lean::PrettyPrinter::Delaborator::Attributes::*;
                }
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Delaborator/Basic.rs");
                }
                pub mod FieldNotation {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Delaborator/FieldNotation.rs");
                }
                pub mod Metavariable {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Delaborator/Metavariable.rs");
                }
                pub mod Options {
                    pub use gen_lean_part_1::r#gen::Lean::PrettyPrinter::Delaborator::Options::*;
                }
                pub mod SubExpr {
                    pub use gen_lean_part_1::r#gen::Lean::PrettyPrinter::Delaborator::SubExpr::*;
                }
                pub mod TopDownAnalyze {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.rs");
                }
            }
            pub mod Formatter {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Formatter.rs");
            }
            pub mod Parenthesizer {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_2/src/gen/Lean/PrettyPrinter/Parenthesizer.rs");
            }
        }
        pub mod PrivateName {
            pub use gen_lean_part_1::r#gen::Lean::PrivateName::*;
        }
        pub mod ProjFns {
            pub use gen_lean_part_1::r#gen::Lean::ProjFns::*;
        }
        pub mod ReducibilityAttrs {
            pub use gen_lean_part_1::r#gen::Lean::ReducibilityAttrs::*;
        }
        pub mod Replay {
            pub use gen_lean_part_1::r#gen::Lean::Replay::*;
        }
        pub mod ReservedNameAction {
            pub use gen_lean_part_1::r#gen::Lean::ReservedNameAction::*;
        }
        pub mod ResolveName {
            pub use gen_lean_part_1::r#gen::Lean::ResolveName::*;
        }
        pub mod Runtime {
            pub use gen_lean_part_1::r#gen::Lean::Runtime::*;
        }
        pub mod ScopedEnvExtension {
            pub use gen_lean_part_1::r#gen::Lean::ScopedEnvExtension::*;
        }
        pub mod Server {
            pub mod AsyncList {
                pub use gen_lean_part_1::r#gen::Lean::Server::AsyncList::*;
            }
            pub mod Completion {
                pub mod CompletionItemCompression {
                    pub use gen_lean_part_1::r#gen::Lean::Server::Completion::CompletionItemCompression::*;
                }
                pub mod EligibleHeaderDecls {
                    pub use gen_lean_part_1::r#gen::Lean::Server::Completion::EligibleHeaderDecls::*;
                }
            }
            pub mod FileSource {
                pub use gen_lean_part_1::r#gen::Lean::Server::FileSource::*;
            }
            pub mod Logging {
                pub use gen_lean_part_1::r#gen::Lean::Server::Logging::*;
            }
            pub mod RequestCancellation {
                pub use gen_lean_part_1::r#gen::Lean::Server::RequestCancellation::*;
            }
            pub mod Rpc {
                pub mod Basic {
                    pub use gen_lean_part_1::r#gen::Lean::Server::Rpc::Basic::*;
                }
            }
            pub mod ServerTask {
                pub use gen_lean_part_1::r#gen::Lean::Server::ServerTask::*;
            }
            pub mod Test {
                pub mod Refs {
                    pub use gen_lean_part_1::r#gen::Lean::Server::Test::Refs::*;
                }
            }
        }
        pub mod Setup {
            pub use gen_lean_part_1::r#gen::Lean::Setup::*;
        }
        pub mod Structure {
            pub use gen_lean_part_1::r#gen::Lean::Structure::*;
        }
        pub mod SubExpr {
            pub use gen_lean_part_1::r#gen::Lean::SubExpr::*;
        }
        pub mod Syntax {
            pub use gen_lean_part_1::r#gen::Lean::Syntax::*;
        }
        pub mod ToExpr {
            pub use gen_lean_part_1::r#gen::Lean::ToExpr::*;
        }
        pub mod ToLevel {
            pub use gen_lean_part_1::r#gen::Lean::ToLevel::*;
        }
        pub mod Util {
            pub mod CollectAxioms {
                pub use gen_lean_part_1::r#gen::Lean::Util::CollectAxioms::*;
            }
            pub mod CollectFVars {
                pub use gen_lean_part_1::r#gen::Lean::Util::CollectFVars::*;
            }
            pub mod CollectLevelMVars {
                pub use gen_lean_part_1::r#gen::Lean::Util::CollectLevelMVars::*;
            }
            pub mod CollectLevelParams {
                pub use gen_lean_part_1::r#gen::Lean::Util::CollectLevelParams::*;
            }
            pub mod CollectLooseBVars {
                pub use gen_lean_part_1::r#gen::Lean::Util::CollectLooseBVars::*;
            }
            pub mod CollectMVars {
                pub use gen_lean_part_1::r#gen::Lean::Util::CollectMVars::*;
            }
            pub mod Diff {
                pub use gen_lean_part_1::r#gen::Lean::Util::Diff::*;
            }
            pub mod FindExpr {
                pub use gen_lean_part_1::r#gen::Lean::Util::FindExpr::*;
            }
            pub mod FindLevelMVar {
                pub use gen_lean_part_1::r#gen::Lean::Util::FindLevelMVar::*;
            }
            pub mod FindMVar {
                pub use gen_lean_part_1::r#gen::Lean::Util::FindMVar::*;
            }
            pub mod FoldConsts {
                pub use gen_lean_part_1::r#gen::Lean::Util::FoldConsts::*;
            }
            pub mod ForEachExpr {
                pub use gen_lean_part_1::r#gen::Lean::Util::ForEachExpr::*;
            }
            pub mod ForEachExprWhere {
                pub use gen_lean_part_1::r#gen::Lean::Util::ForEachExprWhere::*;
            }
            pub mod FVarSubset {
                pub use gen_lean_part_1::r#gen::Lean::Util::FVarSubset::*;
            }
            pub mod HasConstCache {
                pub use gen_lean_part_1::r#gen::Lean::Util::HasConstCache::*;
            }
            pub mod Heartbeats {
                pub use gen_lean_part_1::r#gen::Lean::Util::Heartbeats::*;
            }
            pub mod InstantiateLevelParams {
                pub use gen_lean_part_1::r#gen::Lean::Util::InstantiateLevelParams::*;
            }
            pub mod LakePath {
                pub use gen_lean_part_1::r#gen::Lean::Util::LakePath::*;
            }
            pub mod LeanOptions {
                pub use gen_lean_part_1::r#gen::Lean::Util::LeanOptions::*;
            }
            pub mod MonadBacktrack {
                pub use gen_lean_part_1::r#gen::Lean::Util::MonadBacktrack::*;
            }
            pub mod MonadCache {
                pub use gen_lean_part_1::r#gen::Lean::Util::MonadCache::*;
            }
            pub mod NumApps {
                pub use gen_lean_part_1::r#gen::Lean::Util::NumApps::*;
            }
            pub mod NumObjs {
                pub use gen_lean_part_1::r#gen::Lean::Util::NumObjs::*;
            }
            pub mod OccursCheck {
                pub use gen_lean_part_1::r#gen::Lean::Util::OccursCheck::*;
            }
            pub mod ParamMinimizer {
                pub use gen_lean_part_1::r#gen::Lean::Util::ParamMinimizer::*;
            }
            pub mod Path {
                pub use gen_lean_part_1::r#gen::Lean::Util::Path::*;
            }
            pub mod PPExt {
                pub use gen_lean_part_1::r#gen::Lean::Util::PPExt::*;
            }
            pub mod Profile {
                pub use gen_lean_part_1::r#gen::Lean::Util::Profile::*;
            }
            pub mod Profiler {
                pub use gen_lean_part_1::r#gen::Lean::Util::Profiler::*;
            }
            pub mod ProfilerServer {
                pub use gen_lean_part_1::r#gen::Lean::Util::ProfilerServer::*;
            }
            pub mod PtrSet {
                pub use gen_lean_part_1::r#gen::Lean::Util::PtrSet::*;
            }
            pub mod RecDepth {
                pub use gen_lean_part_1::r#gen::Lean::Util::RecDepth::*;
            }
            pub mod Recognizers {
                pub use gen_lean_part_1::r#gen::Lean::Util::Recognizers::*;
            }
            pub mod ReplaceExpr {
                pub use gen_lean_part_1::r#gen::Lean::Util::ReplaceExpr::*;
            }
            pub mod ReplaceLevel {
                pub use gen_lean_part_1::r#gen::Lean::Util::ReplaceLevel::*;
            }
            pub mod SafeExponentiation {
                pub use gen_lean_part_1::r#gen::Lean::Util::SafeExponentiation::*;
            }
            pub mod SCC {
                pub use gen_lean_part_1::r#gen::Lean::Util::SCC::*;
            }
            pub mod ShareCommon {
                pub use gen_lean_part_1::r#gen::Lean::Util::ShareCommon::*;
            }
            pub mod Sorry {
                pub use gen_lean_part_1::r#gen::Lean::Util::Sorry::*;
            }
            pub mod SortExprs {
                pub use gen_lean_part_1::r#gen::Lean::Util::SortExprs::*;
            }
            pub mod Trace {
                pub use gen_lean_part_1::r#gen::Lean::Util::Trace::*;
            }
            pub mod UnusedBinders {
                pub use gen_lean_part_1::r#gen::Lean::Util::UnusedBinders::*;
            }
        }
        pub mod Widget {
            pub mod TaggedText {
                pub use gen_lean_part_1::r#gen::Lean::Widget::TaggedText::*;
            }
            pub mod Types {
                pub use gen_lean_part_1::r#gen::Lean::Widget::Types::*;
            }
        }
    }
}
