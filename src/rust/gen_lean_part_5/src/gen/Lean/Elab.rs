// Lean compiler output
// Module: Lean.Elab
// Imports: Lean.Elab.Import Lean.Elab.Exception Lean.Elab.Config Lean.Elab.Command Lean.Elab.Term Lean.Elab.App Lean.Elab.Binders Lean.Elab.BinderPredicates Lean.Elab.LetRec Lean.Elab.Frontend Lean.Elab.BuiltinNotation Lean.Elab.Declaration Lean.Elab.Tactic Lean.Elab.Match Lean.Elab.Quotation Lean.Elab.Syntax Lean.Elab.Do Lean.Elab.StructInst Lean.Elab.StructInstHint Lean.Elab.MutualInductive Lean.Elab.Inductive Lean.Elab.Structure Lean.Elab.Print Lean.Elab.MutualDef Lean.Elab.AuxDef Lean.Elab.PreDefinition Lean.Elab.Deriving Lean.Elab.DeclarationRange Lean.Elab.Extra Lean.Elab.GenInjective Lean.Elab.BuiltinTerm Lean.Elab.Arg Lean.Elab.DeprecatedArg Lean.Elab.PatternVar Lean.Elab.ElabRules Lean.Elab.Macro Lean.Elab.Notation Lean.Elab.Mixfix Lean.Elab.MacroRules Lean.Elab.BuiltinCommand Lean.Elab.AssertExists Lean.Elab.Command.WithWeakNamespace Lean.Elab.BuiltinEvalCommand Lean.Elab.RecAppSyntax Lean.Elab.Eval Lean.Elab.Calc Lean.Elab.InheritDoc Lean.Elab.ParseImportsFast Lean.Elab.GuardMsgs Lean.Elab.CheckTactic Lean.Elab.MatchExpr Lean.Elab.Tactic.Doc Lean.Elab.Time Lean.Elab.RecommendedSpelling Lean.Elab.InfoTrees Lean.Elab.ErrorExplanation Lean.Elab.DocString Lean.Elab.DocString.Builtin Lean.Elab.Parallel Lean.Elab.BuiltinDo Lean.Elab.Idbg Lean.Elab.ConfigEval Lean.Elab.ConfigEval.Builtins Lean.Elab.Tactic.Config
use crate::r#gen::Lean::Elab::App::{initialize_Lean_Elab_App, runtime_initialize_Lean_Elab_App};
use crate::r#gen::Lean::Elab::Arg::{initialize_Lean_Elab_Arg, runtime_initialize_Lean_Elab_Arg};
use crate::r#gen::Lean::Elab::AssertExists::{
    initialize_Lean_Elab_AssertExists, runtime_initialize_Lean_Elab_AssertExists,
};
use crate::r#gen::Lean::Elab::AuxDef::{
    initialize_Lean_Elab_AuxDef, runtime_initialize_Lean_Elab_AuxDef,
};
use crate::r#gen::Lean::Elab::BinderPredicates::{
    initialize_Lean_Elab_BinderPredicates, runtime_initialize_Lean_Elab_BinderPredicates,
};
use crate::r#gen::Lean::Elab::Binders::{
    initialize_Lean_Elab_Binders, runtime_initialize_Lean_Elab_Binders,
};
use crate::r#gen::Lean::Elab::BuiltinCommand::{
    initialize_Lean_Elab_BuiltinCommand, runtime_initialize_Lean_Elab_BuiltinCommand,
};
use crate::r#gen::Lean::Elab::BuiltinDo::{
    initialize_Lean_Elab_BuiltinDo, runtime_initialize_Lean_Elab_BuiltinDo,
};
use crate::r#gen::Lean::Elab::BuiltinEvalCommand::{
    initialize_Lean_Elab_BuiltinEvalCommand, runtime_initialize_Lean_Elab_BuiltinEvalCommand,
};
use crate::r#gen::Lean::Elab::BuiltinNotation::{
    initialize_Lean_Elab_BuiltinNotation, runtime_initialize_Lean_Elab_BuiltinNotation,
};
use crate::r#gen::Lean::Elab::BuiltinTerm::{
    initialize_Lean_Elab_BuiltinTerm, runtime_initialize_Lean_Elab_BuiltinTerm,
};
use crate::r#gen::Lean::Elab::Calc::{
    initialize_Lean_Elab_Calc, runtime_initialize_Lean_Elab_Calc,
};
use crate::r#gen::Lean::Elab::CheckTactic::{
    initialize_Lean_Elab_CheckTactic, runtime_initialize_Lean_Elab_CheckTactic,
};
use crate::r#gen::Lean::Elab::Command::WithWeakNamespace::{
    initialize_Lean_Elab_Command_WithWeakNamespace,
    runtime_initialize_Lean_Elab_Command_WithWeakNamespace,
};
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Config::{
    initialize_Lean_Elab_Config, runtime_initialize_Lean_Elab_Config,
};
use crate::r#gen::Lean::Elab::ConfigEval::Builtins::{
    initialize_Lean_Elab_ConfigEval_Builtins, runtime_initialize_Lean_Elab_ConfigEval_Builtins,
};
use crate::r#gen::Lean::Elab::ConfigEval::{
    initialize_Lean_Elab_ConfigEval, runtime_initialize_Lean_Elab_ConfigEval,
};
use crate::r#gen::Lean::Elab::Declaration::{
    initialize_Lean_Elab_Declaration, runtime_initialize_Lean_Elab_Declaration,
};
use crate::r#gen::Lean::Elab::DeclarationRange::{
    initialize_Lean_Elab_DeclarationRange, runtime_initialize_Lean_Elab_DeclarationRange,
};
use crate::r#gen::Lean::Elab::DeprecatedArg::{
    initialize_Lean_Elab_DeprecatedArg, runtime_initialize_Lean_Elab_DeprecatedArg,
};
use crate::r#gen::Lean::Elab::Deriving::{
    initialize_Lean_Elab_Deriving, runtime_initialize_Lean_Elab_Deriving,
};
use crate::r#gen::Lean::Elab::Do::{initialize_Lean_Elab_Do, runtime_initialize_Lean_Elab_Do};
use crate::r#gen::Lean::Elab::DocString::Builtin::{
    initialize_Lean_Elab_DocString_Builtin, runtime_initialize_Lean_Elab_DocString_Builtin,
};
use crate::r#gen::Lean::Elab::DocString::{
    initialize_Lean_Elab_DocString, runtime_initialize_Lean_Elab_DocString,
};
use crate::r#gen::Lean::Elab::ElabRules::{
    initialize_Lean_Elab_ElabRules, runtime_initialize_Lean_Elab_ElabRules,
};
use crate::r#gen::Lean::Elab::ErrorExplanation::{
    initialize_Lean_Elab_ErrorExplanation, runtime_initialize_Lean_Elab_ErrorExplanation,
};
use crate::r#gen::Lean::Elab::Eval::{
    initialize_Lean_Elab_Eval, runtime_initialize_Lean_Elab_Eval,
};
use crate::r#gen::Lean::Elab::Exception::{
    initialize_Lean_Elab_Exception, runtime_initialize_Lean_Elab_Exception,
};
use crate::r#gen::Lean::Elab::Extra::{
    initialize_Lean_Elab_Extra, runtime_initialize_Lean_Elab_Extra,
};
use crate::r#gen::Lean::Elab::Frontend::{
    initialize_Lean_Elab_Frontend, runtime_initialize_Lean_Elab_Frontend,
};
use crate::r#gen::Lean::Elab::GenInjective::{
    initialize_Lean_Elab_GenInjective, runtime_initialize_Lean_Elab_GenInjective,
};
use crate::r#gen::Lean::Elab::GuardMsgs::{
    initialize_Lean_Elab_GuardMsgs, runtime_initialize_Lean_Elab_GuardMsgs,
};
use crate::r#gen::Lean::Elab::Idbg::{
    initialize_Lean_Elab_Idbg, runtime_initialize_Lean_Elab_Idbg,
};
use crate::r#gen::Lean::Elab::Import::{
    initialize_Lean_Elab_Import, runtime_initialize_Lean_Elab_Import,
};
use crate::r#gen::Lean::Elab::Inductive::{
    initialize_Lean_Elab_Inductive, runtime_initialize_Lean_Elab_Inductive,
};
use crate::r#gen::Lean::Elab::InfoTrees::{
    initialize_Lean_Elab_InfoTrees, runtime_initialize_Lean_Elab_InfoTrees,
};
use crate::r#gen::Lean::Elab::InheritDoc::{
    initialize_Lean_Elab_InheritDoc, runtime_initialize_Lean_Elab_InheritDoc,
};
use crate::r#gen::Lean::Elab::LetRec::{
    initialize_Lean_Elab_LetRec, runtime_initialize_Lean_Elab_LetRec,
};
use crate::r#gen::Lean::Elab::Macro::{
    initialize_Lean_Elab_Macro, runtime_initialize_Lean_Elab_Macro,
};
use crate::r#gen::Lean::Elab::MacroRules::{
    initialize_Lean_Elab_MacroRules, runtime_initialize_Lean_Elab_MacroRules,
};
use crate::r#gen::Lean::Elab::Match::{
    initialize_Lean_Elab_Match, runtime_initialize_Lean_Elab_Match,
};
use crate::r#gen::Lean::Elab::MatchExpr::{
    initialize_Lean_Elab_MatchExpr, runtime_initialize_Lean_Elab_MatchExpr,
};
use crate::r#gen::Lean::Elab::Mixfix::{
    initialize_Lean_Elab_Mixfix, runtime_initialize_Lean_Elab_Mixfix,
};
use crate::r#gen::Lean::Elab::MutualDef::{
    initialize_Lean_Elab_MutualDef, runtime_initialize_Lean_Elab_MutualDef,
};
use crate::r#gen::Lean::Elab::MutualInductive::{
    initialize_Lean_Elab_MutualInductive, runtime_initialize_Lean_Elab_MutualInductive,
};
use crate::r#gen::Lean::Elab::Notation::{
    initialize_Lean_Elab_Notation, runtime_initialize_Lean_Elab_Notation,
};
use crate::r#gen::Lean::Elab::Parallel::{
    initialize_Lean_Elab_Parallel, runtime_initialize_Lean_Elab_Parallel,
};
use crate::r#gen::Lean::Elab::ParseImportsFast::{
    initialize_Lean_Elab_ParseImportsFast, runtime_initialize_Lean_Elab_ParseImportsFast,
};
use crate::r#gen::Lean::Elab::PatternVar::{
    initialize_Lean_Elab_PatternVar, runtime_initialize_Lean_Elab_PatternVar,
};
use crate::r#gen::Lean::Elab::PreDefinition::{
    initialize_Lean_Elab_PreDefinition, runtime_initialize_Lean_Elab_PreDefinition,
};
use crate::r#gen::Lean::Elab::Print::{
    initialize_Lean_Elab_Print, runtime_initialize_Lean_Elab_Print,
};
use crate::r#gen::Lean::Elab::Quotation::{
    initialize_Lean_Elab_Quotation, runtime_initialize_Lean_Elab_Quotation,
};
use crate::r#gen::Lean::Elab::RecAppSyntax::{
    initialize_Lean_Elab_RecAppSyntax, runtime_initialize_Lean_Elab_RecAppSyntax,
};
use crate::r#gen::Lean::Elab::RecommendedSpelling::{
    initialize_Lean_Elab_RecommendedSpelling, runtime_initialize_Lean_Elab_RecommendedSpelling,
};
use crate::r#gen::Lean::Elab::StructInst::{
    initialize_Lean_Elab_StructInst, runtime_initialize_Lean_Elab_StructInst,
};
use crate::r#gen::Lean::Elab::StructInstHint::{
    initialize_Lean_Elab_StructInstHint, runtime_initialize_Lean_Elab_StructInstHint,
};
use crate::r#gen::Lean::Elab::Structure::{
    initialize_Lean_Elab_Structure, runtime_initialize_Lean_Elab_Structure,
};
use crate::r#gen::Lean::Elab::Syntax::{
    initialize_Lean_Elab_Syntax, runtime_initialize_Lean_Elab_Syntax,
};
use crate::r#gen::Lean::Elab::Tactic::Config::{
    initialize_Lean_Elab_Tactic_Config, runtime_initialize_Lean_Elab_Tactic_Config,
};
use crate::r#gen::Lean::Elab::Tactic::Doc::{
    initialize_Lean_Elab_Tactic_Doc, runtime_initialize_Lean_Elab_Tactic_Doc,
};
use crate::r#gen::Lean::Elab::Tactic::{
    initialize_Lean_Elab_Tactic, runtime_initialize_Lean_Elab_Tactic,
};
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Time::{
    initialize_Lean_Elab_Time, runtime_initialize_Lean_Elab_Time,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Import(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_LetRec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Frontend(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Declaration(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Match(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Quotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_StructInst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_StructInstHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MutualInductive(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Inductive(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Structure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Print(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MutualDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AuxDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_GenInjective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Arg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeprecatedArg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PatternVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ElabRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Mixfix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MacroRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AssertExists(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinEvalCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Calc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InheritDoc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_GuardMsgs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_CheckTactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MatchExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_RecommendedSpelling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTrees(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorExplanation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Parallel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Idbg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Builtins(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Import(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Binders(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_LetRec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Frontend(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Declaration(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Match(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Quotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_StructInst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_StructInstHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_MutualInductive(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Inductive(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Structure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Print(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_MutualDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_AuxDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_GenInjective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Arg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeprecatedArg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PatternVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ElabRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Mixfix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_MacroRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_AssertExists(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command_WithWeakNamespace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinEvalCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_RecAppSyntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Calc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_InheritDoc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ParseImportsFast(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_GuardMsgs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_CheckTactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_MatchExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Doc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_RecommendedSpelling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTrees(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ErrorExplanation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DocString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DocString_Builtin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Parallel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Idbg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Builtins(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab(builtin);
}