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
            pub use gen_lean_part_2::r#gen::Lean::Compiler::*;
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
                pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::*;
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
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Main::*;
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
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Passes::*;
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
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::PushProj::*;
                }
                pub mod ReduceArity {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::ReduceArity::*;
                }
                pub mod ReduceJpArity {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::ReduceJpArity::*;
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
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::*;
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Simp::Basic::*;
                    }
                    pub mod Config {
                        pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Simp::Config::*;
                    }
                    pub mod ConstantFold {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::ConstantFold::*;
                    }
                    pub mod DefaultAlt {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::DefaultAlt::*;
                    }
                    pub mod DiscrM {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::DiscrM::*;
                    }
                    pub mod FunDeclInfo {
                        pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Simp::FunDeclInfo::*;
                    }
                    pub mod InlineCandidate {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::InlineCandidate::*;
                    }
                    pub mod InlineProj {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::InlineProj::*;
                    }
                    pub mod JpCases {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::JpCases::*;
                    }
                    pub mod Main {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::Main::*;
                    }
                    pub mod SimpM {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::SimpM::*;
                    }
                    pub mod SimpValue {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::SimpValue::*;
                    }
                    pub mod Used {
                        pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Simp::Used::*;
                    }
                }
                pub mod SimpCase {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::SimpCase::*;
                }
                pub mod SimpleGroundExpr {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::SimpleGroundExpr::*;
                }
                pub mod Specialize {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Specialize::*;
                }
                pub mod SpecInfo {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::SpecInfo::*;
                }
                pub mod SplitSCC {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::SplitSCC::*;
                }
                pub mod StructProjCases {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::StructProjCases::*;
                }
                pub mod ToDecl {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::ToDecl::*;
                }
                pub mod ToExpr {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ToExpr::*;
                }
                pub mod ToImpure {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::ToImpure::*;
                }
                pub mod ToImpureType {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::ToImpureType::*;
                }
                pub mod ToLCNF {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::ToLCNF::*;
                }
                pub mod ToMono {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::ToMono::*;
                }
                pub mod Toposort {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Toposort::*;
                }
                pub mod Types {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Types::*;
                }
                pub mod Util {
                    pub use gen_lean_part_1::r#gen::Lean::Compiler::LCNF::Util::*;
                }
                pub mod Visibility {
                    pub use gen_lean_part_2::r#gen::Lean::Compiler::LCNF::Visibility::*;
                }
            }
            pub mod Main {
                pub use gen_lean_part_2::r#gen::Lean::Compiler::Main::*;
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
            pub use gen_lean_part_2::r#gen::Lean::DocString::*;
            pub mod Add {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/DocString/Add.rs");
            }
            pub mod Extension {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Extension::*;
            }
            pub mod Formatter {
                pub use gen_lean_part_2::r#gen::Lean::DocString::Formatter::*;
            }
            pub mod Links {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Links::*;
            }
            pub mod Markdown {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Markdown::*;
            }
            pub mod Parser {
                pub use gen_lean_part_2::r#gen::Lean::DocString::Parser::*;
            }
            pub mod Syntax {
                pub use gen_lean_part_2::r#gen::Lean::DocString::Syntax::*;
            }
            pub mod Types {
                pub use gen_lean_part_1::r#gen::Lean::DocString::Types::*;
            }
        }
        pub mod Elab {
            pub mod Arg {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Arg.rs");
            }
            pub mod AssertExists {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/AssertExists.rs");
            }
            pub mod Attributes {
                pub use gen_lean_part_2::r#gen::Lean::Elab::Attributes::*;
            }
            pub mod AutoBound {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/AutoBound.rs");
            }
            pub mod AuxDef {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/AuxDef.rs");
            }
            pub mod Binders {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Binders.rs");
            }
            pub mod BindersUtil {
                pub use gen_lean_part_2::r#gen::Lean::Elab::BindersUtil::*;
            }
            pub mod BuiltinCommand {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinCommand.rs");
            }
            pub mod BuiltinDo {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/Basic.rs");
                }
                pub mod For {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/For.rs");
                }
                pub mod If {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/If.rs");
                }
                pub mod Jump {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/Jump.rs");
                }
                pub mod Let {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/Let.rs");
                }
                pub mod Match {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/Match.rs");
                }
                pub mod MatchExpr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/MatchExpr.rs");
                }
                pub mod Misc {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/Misc.rs");
                }
                pub mod Repeat {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/Repeat.rs");
                }
                pub mod TryCatch {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinDo/TryCatch.rs");
                }
            }
            pub mod BuiltinTerm {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/BuiltinTerm.rs");
            }
            pub mod CheckTactic {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/CheckTactic.rs");
            }
            pub mod Command {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Command.rs");
                }
                pub use index::*;
                pub mod Scope {
                    pub use gen_lean_part_2::r#gen::Lean::Elab::Command::Scope::*;
                }
                pub mod WithWeakNamespace {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Command/WithWeakNamespace.rs");
                }
            }
            pub mod ComputedFields {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ComputedFields.rs");
            }
            pub mod Config {
                pub use gen_lean_part_1::r#gen::Lean::Elab::Config::*;
            }
            pub mod ConfigEval {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/Basic.rs");
                }
                pub mod Commands {
                    pub use gen_lean_part_1::r#gen::Lean::Elab::ConfigEval::Commands::*;
                }
                pub mod DeriveEvalConfigItem {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/DeriveEvalConfigItem.rs");
                }
                pub mod DeriveEvalExpr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/DeriveEvalExpr.rs");
                }
                pub mod DeriveEvalTerm {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/DeriveEvalTerm.rs");
                }
                pub mod Extra {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/Extra.rs");
                }
                pub mod Instances {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/Instances.rs");
                }
                pub mod MetaInstances {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/MetaInstances.rs");
                }
                pub mod Types {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/Types.rs");
                }
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ConfigEval/Util.rs");
                }
            }
            pub mod DeclarationRange {
                pub use gen_lean_part_2::r#gen::Lean::Elab::DeclarationRange::*;
            }
            pub mod DeclModifiers {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DeclModifiers.rs");
            }
            pub mod DeclNameGen {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DeclNameGen.rs");
            }
            pub mod DeclUtil {
                pub use gen_lean_part_2::r#gen::Lean::Elab::DeclUtil::*;
            }
            pub mod DefView {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DefView.rs");
            }
            pub mod DeprecatedArg {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DeprecatedArg.rs");
            }
            pub mod DeprecatedSyntax {
                pub use gen_lean_part_2::r#gen::Lean::Elab::DeprecatedSyntax::*;
            }
            pub mod Deriving {
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Deriving/Util.rs");
                }
            }
            pub mod Do {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do/Basic.rs");
                }
                pub mod Control {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do/Control.rs");
                }
                pub mod InferControlInfo {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do/InferControlInfo.rs");
                }
                pub mod Legacy {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do/Legacy.rs");
                }
                pub mod PatternVar {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do/PatternVar.rs");
                }
                pub mod Switch {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Do/Switch.rs");
                }
            }
            pub mod DocString {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DocString.rs");
                }
                pub use index::*;
                pub mod Builtin {
                    pub mod Keywords {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DocString/Builtin/Keywords.rs");
                    }
                    pub mod Parsing {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::DocString::Builtin::Parsing::*;
                    }
                    pub mod Postponed {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DocString/Builtin/Postponed.rs");
                    }
                    pub mod Scopes {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/DocString/Builtin/Scopes.rs");
                    }
                }
            }
            pub mod ElabRules {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/ElabRules.rs");
            }
            pub mod ErrorUtils {
                pub use gen_lean_part_1::r#gen::Lean::Elab::ErrorUtils::*;
            }
            pub mod Eval {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Eval.rs");
            }
            pub mod Exception {
                pub use gen_lean_part_1::r#gen::Lean::Elab::Exception::*;
            }
            pub mod GenInjective {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/GenInjective.rs");
            }
            pub mod Idbg {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Idbg.rs");
            }
            pub mod Import {
                pub use gen_lean_part_2::r#gen::Lean::Elab::Import::*;
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
            pub mod InfoTrees {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/InfoTrees.rs");
            }
            pub mod InheritDoc {
                pub use gen_lean_part_1::r#gen::Lean::Elab::InheritDoc::*;
            }
            pub mod Level {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Level.rs");
            }
            pub mod Macro {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Macro.rs");
            }
            pub mod MacroArgUtil {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/MacroArgUtil.rs");
            }
            pub mod MacroRules {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/MacroRules.rs");
            }
            pub mod Match {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Match.rs");
            }
            pub mod MatchAltView {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/MatchAltView.rs");
            }
            pub mod MatchExpr {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/MatchExpr.rs");
            }
            pub mod Mixfix {
                pub use gen_lean_part_2::r#gen::Lean::Elab::Mixfix::*;
            }
            pub mod Open {
                pub use gen_lean_part_2::r#gen::Lean::Elab::Open::*;
            }
            pub mod ParseImportsFast {
                pub use gen_lean_part_2::r#gen::Lean::Elab::ParseImportsFast::*;
            }
            pub mod PatternVar {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PatternVar.rs");
            }
            pub mod PreDefinition {
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Basic.rs");
                }
                pub mod Eqns {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Eqns.rs");
                }
                pub mod EqnsUtils {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/EqnsUtils.rs");
                }
                pub mod FixedParams {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/FixedParams.rs");
                }
                pub mod MkInhabitant {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/MkInhabitant.rs");
                }
                pub mod Mutual {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Mutual.rs");
                }
                pub mod PartialFixpoint {
                    pub mod Eqns {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/PartialFixpoint/Eqns.rs");
                    }
                    pub mod Induction {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/PartialFixpoint/Induction.rs");
                    }
                }
                pub mod Structural {
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::Structural::Basic::*;
                    }
                    pub mod BRecOn {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Structural/BRecOn.rs");
                    }
                    pub mod Eqns {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Structural/Eqns.rs");
                    }
                    pub mod FindRecArg {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Structural/FindRecArg.rs");
                    }
                    pub mod IndGroupInfo {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::Structural::IndGroupInfo::*;
                    }
                    pub mod IndPred {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Structural/IndPred.rs");
                    }
                    pub mod Preprocess {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::Structural::Preprocess::*;
                    }
                    pub mod RecArgInfo {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Structural/RecArgInfo.rs");
                    }
                    pub mod SmartUnfolding {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/Structural/SmartUnfolding.rs");
                    }
                }
                pub mod TerminationHint {
                    pub use gen_lean_part_2::r#gen::Lean::Elab::PreDefinition::TerminationHint::*;
                }
                pub mod TerminationMeasure {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/TerminationMeasure.rs");
                }
                pub mod WF {
                    pub mod Basic {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/WF/Basic.rs");
                    }
                    pub mod Eqns {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/WF/Eqns.rs");
                    }
                    pub mod Fix {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/WF/Fix.rs");
                    }
                    pub mod FloatRecApp {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::PreDefinition::WF::FloatRecApp::*;
                    }
                    pub mod PackMutual {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/WF/PackMutual.rs");
                    }
                    pub mod Rel {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/WF/Rel.rs");
                    }
                    pub mod Unfold {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/PreDefinition/WF/Unfold.rs");
                    }
                }
            }
            pub mod Print {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Print.rs");
            }
            pub mod Quotation {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Quotation.rs");
                }
                pub use index::*;
                pub mod Precheck {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Quotation/Precheck.rs");
                }
                pub mod Util {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Quotation/Util.rs");
                }
            }
            pub mod RecAppSyntax {
                pub use gen_lean_part_1::r#gen::Lean::Elab::RecAppSyntax::*;
            }
            pub mod RecommendedSpelling {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/RecommendedSpelling.rs");
            }
            pub mod SetOption {
                pub use gen_lean_part_1::r#gen::Lean::Elab::SetOption::*;
            }
            pub mod StructInstHint {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/StructInstHint.rs");
            }
            pub mod Syntax {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Syntax.rs");
            }
            pub mod SyntheticMVars {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/SyntheticMVars.rs");
            }
            pub mod Tactic {
                pub mod AsAuxLemma {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/AsAuxLemma.rs");
                }
                pub mod Basic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Basic.rs");
                }
                pub mod BoolToPropSimps {
                    pub use gen_lean_part_2::r#gen::Lean::Elab::Tactic::BoolToPropSimps::*;
                }
                pub mod CbvSimproc {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/CbvSimproc.rs");
                }
                pub mod Change {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Change.rs");
                }
                pub mod Classical {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Classical.rs");
                }
                pub mod Congr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Congr.rs");
                }
                pub mod Decide {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Decide.rs");
                }
                pub mod Delta {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Delta.rs");
                }
                pub mod DiscrTreeKey {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/DiscrTreeKey.rs");
                }
                pub mod Do {
                    pub mod Attr {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/Attr.rs");
                    }
                    pub mod Internal {
                        pub mod VCGen {
                            pub mod SpecDB {
                                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/Internal/VCGen/SpecDB.rs");
                            }
                        }
                    }
                    pub mod LetElim {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/LetElim.rs");
                    }
                    pub mod ProofMode {
                        pub mod Assumption {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Assumption.rs");
                        }
                        pub mod Basic {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Basic.rs");
                        }
                        pub mod Clear {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Clear.rs");
                        }
                        pub mod Constructor {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Constructor.rs");
                        }
                        pub mod Delab {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Delab.rs");
                        }
                        pub mod Exact {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Exact.rs");
                        }
                        pub mod Exfalso {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Exfalso.rs");
                        }
                        pub mod Focus {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Focus.rs");
                        }
                        pub mod Frame {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Frame.rs");
                        }
                        pub mod Have {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Have.rs");
                        }
                        pub mod Intro {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Intro.rs");
                        }
                        pub mod LeftRight {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/LeftRight.rs");
                        }
                        pub mod MGoal {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/MGoal.rs");
                        }
                        pub mod Refine {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Refine.rs");
                        }
                        pub mod RenameI {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/RenameI.rs");
                        }
                        pub mod Revert {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Revert.rs");
                        }
                        pub mod Specialize {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/ProofMode/Specialize.rs");
                        }
                    }
                    pub mod VCGen {
                        pub mod Split {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/VCGen/Split.rs");
                        }
                        pub mod SuggestInvariant {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Do/VCGen/SuggestInvariant.rs");
                        }
                    }
                }
                pub mod Doc {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Doc.rs");
                }
                pub mod ElabTerm {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/ElabTerm.rs");
                }
                pub mod ExposeNames {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/ExposeNames.rs");
                }
                pub mod FalseOrByContra {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/FalseOrByContra.rs");
                }
                pub mod Generalize {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Generalize.rs");
                }
                pub mod Grind {
                    pub mod Annotated {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Grind/Annotated.rs");
                    }
                }
                pub mod Impossible {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Impossible.rs");
                }
                pub mod Induction {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Induction.rs");
                }
                pub mod Injection {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Injection.rs");
                }
                pub mod Lets {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Lets.rs");
                }
                pub mod Location {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Location.rs");
                }
                pub mod Match {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Match.rs");
                }
                pub mod Meta {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/Meta.rs");
                }
                pub mod Omega {
                    pub mod Core {
                        pub use gen_lean_part_2::r#gen::Lean::Elab::Tactic::Omega::Core::*;
                    }
                    pub mod MinNatAbs {
                        pub use gen_lean_part_1::r#gen::Lean::Elab::Tactic::Omega::MinNatAbs::*;
                    }
                    pub mod OmegaM {
                        pub use gen_lean_part_2::r#gen::Lean::Elab::Tactic::Omega::OmegaM::*;
                    }
                }
                pub mod TreeTacAttr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Tactic/TreeTacAttr.rs");
                }
            }
            pub mod Term {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Term.rs");
                }
                pub use index::*;
                pub mod TermElabM {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Elab/Term/TermElabM.rs");
                }
            }
            pub mod Util {
                pub use gen_lean_part_2::r#gen::Lean::Elab::Util::*;
            }
            pub mod WhereFinally {
                pub use gen_lean_part_2::r#gen::Lean::Elab::WhereFinally::*;
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
            pub use gen_lean_part_2::r#gen::Lean::KeyedDeclsAttribute::*;
        }
        pub mod LabelAttribute {
            pub use gen_lean_part_2::r#gen::Lean::LabelAttribute::*;
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::AbstractNestedProofs::*;
            }
            pub mod ACLt {
                pub use gen_lean_part_1::r#gen::Lean::Meta::ACLt::*;
            }
            pub mod AppBuilder {
                pub use gen_lean_part_2::r#gen::Lean::Meta::AppBuilder::*;
            }
            pub mod ArgsPacker {
                pub use gen_lean_part_2::r#gen::Lean::Meta::ArgsPacker::*;
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::Closure::*;
            }
            pub mod Coe {
                pub use gen_lean_part_2::r#gen::Lean::Meta::Coe::*;
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::CongrTheorems::*;
            }
            pub mod Constructions {
                pub mod BRecOn {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Constructions/BRecOn.rs");
                }
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
                pub mod SparseCasesOnEq {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Constructions/SparseCasesOnEq.rs");
                }
            }
            pub mod CtorIdxHInj {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/CtorIdxHInj.rs");
            }
            pub mod CtorRecognizer {
                pub use gen_lean_part_1::r#gen::Lean::Meta::CtorRecognizer::*;
            }
            pub mod DecLevel {
                pub use gen_lean_part_1::r#gen::Lean::Meta::DecLevel::*;
            }
            pub mod Diagnostics {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Diagnostics.rs");
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::Eqns::*;
            }
            pub mod Eval {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Eval::*;
            }
            pub mod ExprDefEq {
                pub use gen_lean_part_2::r#gen::Lean::Meta::ExprDefEq::*;
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::HaveTelescope::*;
            }
            pub mod Hint {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Hint.rs");
            }
            pub mod IndPredBelow {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/IndPredBelow.rs");
            }
            pub mod Inductive {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Inductive::*;
            }
            pub mod InferType {
                pub use gen_lean_part_1::r#gen::Lean::Meta::InferType::*;
            }
            pub mod Injective {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Injective.rs");
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::LazyDiscrTree::*;
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
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match.rs");
                }
                pub use index::*;
                pub mod AltTelescopes {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Match::AltTelescopes::*;
                }
                pub mod Basic {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Match::Basic::*;
                }
                pub mod CaseArraySizes {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Match::CaseArraySizes::*;
                }
                pub mod CaseValues {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Match::CaseValues::*;
                }
                pub mod Match {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/Match.rs");
                }
                pub mod MatchEqs {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/MatchEqs.rs");
                }
                pub mod MatchEqsExt {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Match::MatchEqsExt::*;
                }
                pub mod MatcherApp {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/MatcherApp.rs");
                    }
                    pub use index::*;
                    pub mod Basic {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Match::MatcherApp::Basic::*;
                    }
                    pub mod Transform {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/MatcherApp/Transform.rs");
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
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Match::NamedPatterns::*;
                }
                pub mod Rewrite {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/Rewrite.rs");
                }
                pub mod SimpH {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/SimpH.rs");
                }
                pub mod SolveOverlap {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Match/SolveOverlap.rs");
                }
                pub mod Value {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Match::Value::*;
                }
            }
            pub mod MatchUtil {
                pub use gen_lean_part_1::r#gen::Lean::Meta::MatchUtil::*;
            }
            pub mod MethodSpecs {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/MethodSpecs.rs");
            }
            pub mod MonadSimp {
                pub use gen_lean_part_1::r#gen::Lean::Meta::MonadSimp::*;
            }
            pub mod NatInstTesters {
                pub use gen_lean_part_1::r#gen::Lean::Meta::NatInstTesters::*;
            }
            pub mod Native {
                pub use gen_lean_part_2::r#gen::Lean::Meta::Native::*;
            }
            pub mod NatTable {
                pub use gen_lean_part_1::r#gen::Lean::Meta::NatTable::*;
            }
            pub mod Offset {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Offset::*;
            }
            pub mod Order {
                pub use gen_lean_part_2::r#gen::Lean::Meta::Order::*;
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
                pub use gen_lean_part_2::r#gen::Lean::Meta::SizeOf::*;
            }
            pub mod Sorry {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Sorry::*;
            }
            pub mod SplitSparseCasesOn {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/SplitSparseCasesOn.rs");
            }
            pub mod StringLitProof {
                pub use gen_lean_part_2::r#gen::Lean::Meta::StringLitProof::*;
            }
            pub mod Structure {
                pub use gen_lean_part_2::r#gen::Lean::Meta::Structure::*;
            }
            pub mod Sym {
                pub mod AbstractS {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::AbstractS::*;
                }
                pub mod AlphaShareBuilder {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::AlphaShareBuilder::*;
                }
                pub mod AlphaShareCommon {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::AlphaShareCommon::*;
                }
                pub mod Apply {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Apply::*;
                }
                pub mod Arith {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::*;
                    pub mod Classify {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::Classify::*;
                    }
                    pub mod DenoteExpr {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::DenoteExpr::*;
                    }
                    pub mod EvalNum {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::EvalNum::*;
                    }
                    pub mod Functions {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::Functions::*;
                    }
                    pub mod MonadCanon {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::MonadCanon::*;
                    }
                    pub mod MonadRing {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::MonadRing::*;
                    }
                    pub mod MonadSemiring {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::MonadSemiring::*;
                    }
                    pub mod MonadVar {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::MonadVar::*;
                    }
                    pub mod Poly {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Arith::Poly::*;
                    }
                    pub mod Reify {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::Reify::*;
                    }
                    pub mod ToExpr {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Arith::ToExpr::*;
                    }
                    pub mod Types {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Arith::Types::*;
                    }
                    pub mod VarRename {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Arith::VarRename::*;
                    }
                }
                pub mod Canon {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Canon::*;
                }
                pub mod DSimp {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::*;
                    pub mod App {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::App::*;
                    }
                    pub mod DSimpM {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::DSimpM::*;
                    }
                    pub mod DSimproc {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::DSimproc::*;
                    }
                    pub mod Forall {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Forall::*;
                    }
                    pub mod Lambda {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Lambda::*;
                    }
                    pub mod Let {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Let::*;
                    }
                    pub mod Main {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Main::*;
                    }
                    pub mod Reduce {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Reduce::*;
                    }
                    pub mod Result {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Result::*;
                    }
                    pub mod Variant {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::DSimp::Variant::*;
                    }
                }
                pub mod Eta {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Eta::*;
                }
                pub mod ExprPtr {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::ExprPtr::*;
                }
                pub mod InferType {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::InferType::*;
                }
                pub mod InstantiateMVarsS {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::InstantiateMVarsS::*;
                }
                pub mod InstantiateS {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::InstantiateS::*;
                }
                pub mod Intro {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Intro::*;
                }
                pub mod IsClass {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::IsClass::*;
                }
                pub mod LitValues {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::LitValues::*;
                }
                pub mod LooseBVarsS {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::LooseBVarsS::*;
                }
                pub mod MaxFVar {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::MaxFVar::*;
                }
                pub mod Offset {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Sym::Offset::*;
                }
                pub mod Pattern {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Pattern::*;
                }
                pub mod ProofInstInfo {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::ProofInstInfo::*;
                }
                pub mod ReplaceS {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::ReplaceS::*;
                }
                pub mod Simp {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::*;
                    pub mod App {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::App::*;
                    }
                    pub mod Attr {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Attr::*;
                    }
                    pub mod CongrInfo {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::CongrInfo::*;
                    }
                    pub mod ControlFlow {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::ControlFlow::*;
                    }
                    pub mod Debug {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Debug::*;
                    }
                    pub mod Discharger {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Discharger::*;
                    }
                    pub mod DiscrTree {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::DiscrTree::*;
                    }
                    pub mod EvalGround {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::EvalGround::*;
                    }
                    pub mod Forall {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Forall::*;
                    }
                    pub mod Goal {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Goal::*;
                    }
                    pub mod Have {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Have::*;
                    }
                    pub mod Lambda {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Lambda::*;
                    }
                    pub mod Main {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Main::*;
                    }
                    pub mod RegisterCommand {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::RegisterCommand::*;
                    }
                    pub mod Result {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Result::*;
                    }
                    pub mod Rewrite {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Rewrite::*;
                    }
                    pub mod SimpM {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::SimpM::*;
                    }
                    pub mod Simproc {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Simproc::*;
                    }
                    pub mod Telescope {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Telescope::*;
                    }
                    pub mod Theorems {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Theorems::*;
                    }
                    pub mod Variant {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Simp::Variant::*;
                    }
                }
                pub mod SymM {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::SymM::*;
                }
                pub mod SynthInstance {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::SynthInstance::*;
                }
                pub mod Util {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Sym::Util::*;
                }
            }
            pub mod SynthInstance {
                pub use gen_lean_part_2::r#gen::Lean::Meta::SynthInstance::*;
            }
            pub mod Tactic {
                pub mod Acyclic {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Acyclic.rs");
                }
                pub mod Apply {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Apply.rs");
                }
                pub mod Assert {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Assert::*;
                }
                pub mod Assumption {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Assumption::*;
                }
                pub mod AuxLemma {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::AuxLemma::*;
                }
                pub mod Backtrack {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Backtrack::*;
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
                    pub mod Normalize {
                        pub mod ApplyControlFlow {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/BVDecide/Normalize/ApplyControlFlow.rs");
                        }
                    }
                    pub mod Reflect {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::*;
                        pub mod Basic {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::*;
                        }
                        pub mod ReifiedBVExpr {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVExpr::*;
                        }
                        pub mod ReifiedBVLogical {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVLogical::*;
                        }
                        pub mod ReifiedBVPred {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVPred::*;
                        }
                        pub mod ReifiedLemmas {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedLemmas::*;
                        }
                        pub mod Reify {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Reify::*;
                        }
                        pub mod SatAtBVLogical {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::SatAtBVLogical::*;
                        }
                    }
                }
                pub mod Cases {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Cases.rs");
                }
                pub mod CasesOnStuckLHS {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/CasesOnStuckLHS.rs");
                }
                pub mod Cbv {
                    pub mod BuiltinCbvSimprocs {
                        pub mod Array {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::BuiltinCbvSimprocs::Array::*;
                        }
                        pub mod Core {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::BuiltinCbvSimprocs::Core::*;
                        }
                        pub mod String {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::BuiltinCbvSimprocs::String::*;
                        }
                    }
                    pub mod CbvEvalExt {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::CbvEvalExt::*;
                    }
                    pub mod CbvSimproc {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::CbvSimproc::*;
                    }
                    pub mod ControlFlow {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::ControlFlow::*;
                    }
                    pub mod Opaque {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Cbv::Opaque::*;
                    }
                    pub mod TheoremsLookup {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::TheoremsLookup::*;
                    }
                    pub mod Util {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cbv::Util::*;
                    }
                }
                pub mod Cleanup {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Cleanup::*;
                }
                pub mod Clear {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Clear::*;
                }
                pub mod Congr {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Congr.rs");
                }
                pub mod Constructor {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Constructor.rs");
                }
                pub mod Contradiction {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Contradiction.rs");
                }
                pub mod Delta {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Delta::*;
                }
                pub mod ElimInfo {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::ElimInfo::*;
                }
                pub mod ExposeNames {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::ExposeNames::*;
                }
                pub mod Ext {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Ext::*;
                }
                pub mod FunIndCollect {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::FunIndCollect::*;
                }
                pub mod FunIndInfo {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::FunIndInfo::*;
                }
                pub mod FVarSubst {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::FVarSubst::*;
                }
                pub mod Generalize {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Generalize::*;
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
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::AC::Var::*;
                        }
                        pub mod VarRename {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::AC::VarRename::*;
                        }
                    }
                    pub mod Arith {
                        pub mod Cutsat {
                            pub mod ToIntInfo {
                                pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToIntInfo::*;
                            }
                            pub mod VarRename {
                                pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::VarRename::*;
                            }
                        }
                        pub mod FieldNormNum {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Arith::FieldNormNum::*;
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
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Arith::Simproc::*;
                        }
                        pub mod Types {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::Arith::Types::*;
                        }
                        pub mod Util {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::*;
                        }
                    }
                    pub mod Cases {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Grind/Cases.rs");
                    }
                    pub mod CasesMatch {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Grind/CasesMatch.rs");
                    }
                    pub mod CastLike {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::CastLike::*;
                    }
                    pub mod CheckResult {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::CheckResult::*;
                    }
                    pub mod EqResolution {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::EqResolution::*;
                    }
                    pub mod ExtAttr {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::ExtAttr::*;
                    }
                    pub mod Extension {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Extension::*;
                    }
                    pub mod Injection {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Injection::*;
                    }
                    pub mod MatchDiscrOnly {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::MatchDiscrOnly::*;
                    }
                    pub mod Parser {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Parser::*;
                    }
                    pub mod RevertAll {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::RevertAll::*;
                    }
                    pub mod SynthInstance {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::*;
                    }
                    pub mod Theorems {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Theorems::*;
                    }
                    pub mod Util {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Grind::Util::*;
                    }
                    pub mod VarRename {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Grind::VarRename::*;
                    }
                }
                pub mod IndependentOf {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::IndependentOf::*;
                }
                pub mod Induction {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Induction::*;
                }
                pub mod Injection {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Injection::*;
                }
                pub mod Intro {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Intro::*;
                }
                pub mod Lets {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Lets::*;
                }
                pub mod NormCast {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::NormCast::*;
                }
                pub mod Refl {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Refl.rs");
                }
                pub mod Rename {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Rename::*;
                }
                pub mod Repeat {
                    pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Repeat::*;
                }
                pub mod Replace {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Replace::*;
                }
                pub mod Revert {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Revert::*;
                }
                pub mod Rewrite {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Rewrite.rs");
                }
                pub mod Simp {
                    pub mod index {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Simp.rs");
                    }
                    pub use index::*;
                    pub mod Arith {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Arith::*;
                        pub mod Int {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::*;
                            pub mod Basic {
                                pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::Basic::*;
                            }
                            pub mod Simp {
                                pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::Simp::*;
                            }
                        }
                        pub mod Nat {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Arith::Nat::*;
                            pub mod Basic {
                                pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Simp::Arith::Nat::Basic::*;
                            }
                            pub mod Simp {
                                pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Arith::Nat::Simp::*;
                            }
                        }
                        pub mod Util {
                            pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Simp::Arith::Util::*;
                        }
                    }
                    pub mod Attr {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Attr::*;
                    }
                    pub mod BuiltinSimprocs {
                        pub mod index {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs.rs");
                        }
                        pub use index::*;
                        pub mod Array {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Array::*;
                        }
                        pub mod BitVec {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::BitVec::*;
                        }
                        pub mod Char {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Char::*;
                        }
                        pub mod Core {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Core::*;
                        }
                        pub mod CtorIdx {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::CtorIdx::*;
                        }
                        pub mod Fin {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Fin::*;
                        }
                        pub mod Int {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Int::*;
                        }
                        pub mod List {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::List::*;
                        }
                        pub mod MethodSpecs {
                            include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Simp/BuiltinSimprocs/MethodSpecs.rs");
                        }
                        pub mod Nat {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Nat::*;
                        }
                        pub mod SInt {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::SInt::*;
                        }
                        pub mod String {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::String::*;
                        }
                        pub mod UInt {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::UInt::*;
                        }
                        pub mod Util {
                            pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Util::*;
                        }
                    }
                    pub mod Diagnostics {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Simp/Diagnostics.rs");
                    }
                    pub mod LoopProtection {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::LoopProtection::*;
                    }
                    pub mod Main {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Simp/Main.rs");
                    }
                    pub mod RegisterCommand {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::RegisterCommand::*;
                    }
                    pub mod Rewrite {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Rewrite::*;
                    }
                    pub mod SimpAll {
                        include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Simp/SimpAll.rs");
                    }
                    pub mod SimpCongrTheorems {
                        pub use gen_lean_part_1::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::*;
                    }
                    pub mod Simproc {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Simproc::*;
                    }
                    pub mod SimpTheorems {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::*;
                    }
                    pub mod Types {
                        pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Simp::Types::*;
                    }
                }
                pub mod Split {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Split.rs");
                }
                pub mod SplitIf {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/SplitIf.rs");
                }
                pub mod Subst {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Subst::*;
                }
                pub mod Symm {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Symm::*;
                }
                pub mod Unfold {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/Tactic/Unfold.rs");
                }
                pub mod UnifyEq {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::UnifyEq::*;
                }
                pub mod Util {
                    pub use gen_lean_part_2::r#gen::Lean::Meta::Tactic::Util::*;
                }
            }
            pub mod Transform {
                pub use gen_lean_part_1::r#gen::Lean::Meta::Transform::*;
            }
            pub mod TransparencyMode {
                pub use gen_lean_part_1::r#gen::Lean::Meta::TransparencyMode::*;
            }
            pub mod TryThis {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Meta/TryThis.rs");
            }
            pub mod UnificationHint {
                pub use gen_lean_part_2::r#gen::Lean::Meta::UnificationHint::*;
            }
            pub mod WHNF {
                pub use gen_lean_part_1::r#gen::Lean::Meta::WHNF::*;
            }
            pub mod WrapInstance {
                pub use gen_lean_part_2::r#gen::Lean::Meta::WrapInstance::*;
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
            pub mod index {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Parser.rs");
            }
            pub use index::*;
            pub mod Attr {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Attr::*;
            }
            pub mod Basic {
                pub use gen_lean_part_1::r#gen::Lean::Parser::Basic::*;
            }
            pub mod Command {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Command::*;
            }
            pub mod Do {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Do::*;
            }
            pub mod Extension {
                pub use gen_lean_part_1::r#gen::Lean::Parser::Extension::*;
            }
            pub mod Extra {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Extra::*;
            }
            pub mod Level {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Level::*;
            }
            pub mod Module {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Module::*;
                pub mod Syntax {
                    pub use gen_lean_part_2::r#gen::Lean::Parser::Module::Syntax::*;
                }
            }
            pub mod StrInterpolation {
                pub use gen_lean_part_1::r#gen::Lean::Parser::StrInterpolation::*;
            }
            pub mod Syntax {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Parser/Syntax.rs");
            }
            pub mod Tactic {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/Parser/Tactic.rs");
                }
                pub use index::*;
                pub mod Doc {
                    pub use gen_lean_part_2::r#gen::Lean::Parser::Tactic::Doc::*;
                }
            }
            pub mod Term {
                pub use gen_lean_part_2::r#gen::Lean::Parser::Term::*;
                pub mod Basic {
                    pub use gen_lean_part_2::r#gen::Lean::Parser::Term::Basic::*;
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
            pub use gen_lean_part_2::r#gen::Lean::ParserCompiler::*;
            pub mod Attribute {
                pub use gen_lean_part_1::r#gen::Lean::ParserCompiler::Attribute::*;
            }
        }
        pub mod PrettyPrinter {
            pub mod index {
                include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/PrettyPrinter.rs");
            }
            pub use index::*;
            pub mod Basic {
                pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Basic::*;
            }
            pub mod Delaborator {
                pub mod index {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/PrettyPrinter/Delaborator.rs");
                }
                pub use index::*;
                pub mod Attributes {
                    pub use gen_lean_part_1::r#gen::Lean::PrettyPrinter::Delaborator::Attributes::*;
                }
                pub mod Basic {
                    pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Delaborator::Basic::*;
                }
                pub mod Builtins {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/PrettyPrinter/Delaborator/Builtins.rs");
                }
                pub mod DeclWithSig {
                    include!("/home/srghma/projects/lean4/src/rust/gen_lean_part_3/src/gen/Lean/PrettyPrinter/Delaborator/DeclWithSig.rs");
                }
                pub mod FieldNotation {
                    pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Delaborator::FieldNotation::*;
                }
                pub mod Metavariable {
                    pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Delaborator::Metavariable::*;
                }
                pub mod Options {
                    pub use gen_lean_part_1::r#gen::Lean::PrettyPrinter::Delaborator::Options::*;
                }
                pub mod SubExpr {
                    pub use gen_lean_part_1::r#gen::Lean::PrettyPrinter::Delaborator::SubExpr::*;
                }
                pub mod TopDownAnalyze {
                    pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Delaborator::TopDownAnalyze::*;
                }
            }
            pub mod Formatter {
                pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Formatter::*;
            }
            pub mod Parenthesizer {
                pub use gen_lean_part_2::r#gen::Lean::PrettyPrinter::Parenthesizer::*;
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
