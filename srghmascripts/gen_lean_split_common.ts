import path from "node:path";

export type LeanSplitCrate =
  | "gen_lean_base"
  | "gen_lean_meta"
  | "gen_lean_meta_tactic"
  | "gen_lean_meta_grind"
  | "gen_lean_compiler"
  | "gen_lean_elab_frontend"
  | "gen_lean_elab_support"
  | "gen_lean_elab_tactic";

export const leanSplitCrates: LeanSplitCrate[] = [
  "gen_lean_base",
  "gen_lean_meta",
  "gen_lean_meta_tactic",
  "gen_lean_meta_grind",
  "gen_lean_compiler",
  "gen_lean_elab_frontend",
  "gen_lean_elab_support",
  "gen_lean_elab_tactic",
];

export const leanElabFrontend = new Set([
  "App",
  "Attributes",
  "AuxDef",
  "Binders",
  "BindersUtil",
  "BuiltinCommand",
  "BuiltinNotation",
  "BuiltinTerm",
  "Coinductive",
  "Command",
  "ComputedFields",
  "Declaration",
  "DeclarationRange",
  "DeclModifiers",
  "DefView",
  "ElabRules",
  "Extra",
  "Inductive",
  "InfoTree",
  "LetRec",
  "Level",
  "MacroArgUtil",
  "Match",
  "MutualDef",
  "MutualInductive",
  "Notation",
  "Open",
  "Parallel",
  "PatternVar",
  "PreDefinition",
  "Print",
  "Quotation",
  "StructInst",
  "Structure",
  "Syntax",
  "SyntheticMVars",
  "Term",
]);

export const leanSplitCrateForRel = (rel: string): LeanSplitCrate => {
  const normalized = rel.replaceAll(path.sep, "/");
  if (normalized === "Lean.rs") return "gen_lean_base";
  const parts = normalized.split("/");
  if (parts[0] !== "Lean") throw new Error(`not a Lean generated file: ${rel}`);

  const top = parts[1]?.replace(/\.rs$/, "");
  const second = parts[2]?.replace(/\.rs$/, "");
  const third = parts[3]?.replace(/\.rs$/, "");

  if (top === "Meta") {
    if (second === "Tactic") {
      return third === "Grind" ? "gen_lean_meta_grind" : "gen_lean_meta_tactic";
    }
    return "gen_lean_meta";
  }
  if (top === "Compiler") return "gen_lean_compiler";
  if (top === "Elab") {
    if (second === "Tactic") return "gen_lean_elab_tactic";
    return leanElabFrontend.has(second ?? "") ? "gen_lean_elab_frontend" : "gen_lean_elab_support";
  }
  if (top === "Server" || top === "Linter") return "gen_lean_elab_tactic";
  return "gen_lean_base";
};

export const ffiCrateForLeanCrate = (crate: LeanSplitCrate) => `${crate}_ffi`;
