/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

function mkText(s) {
  return { tag: "Std$Format$text", _1: s };
}

function mkAppend(a, b) {
  return { tag: "Std$Format$append", _1: a, _2: b };
}

function mkGroup(f) {
  return { tag: "Std$Format$group", _1: f };
}

function mkNest(indent, f) {
  return { tag: "Std$Format$nest", _1: indent, _2: f };
}

function renderPretty(f, flatten = true) {
  switch (f.tag) {
    case "Std$Format$nil":
      return "";
    case "Std$Format$line":
      return flatten ? " " : "\n";
    case "Std$Format$align":
      return "";
    case "Std$Format$text":
      return f._1;
    case "Std$Format$nest":
      return renderPretty(f._2, flatten);
    case "Std$Format$append":
      return renderPretty(f._1, flatten) + renderPretty(f._2, flatten);
    case "Std$Format$group":
      return renderPretty(f._1, true);
    case "Std$Format$tag":
      return renderPretty(f._2, flatten);
    default:
      throw new Error(`unknown Format node: ${f.tag}`);
  }
}

export function Std$Format$pretty(f, width = 120, indent = 0, column = 0) {
  return renderPretty(f, true);
}

export function Std$Format$fill(f) {
  return mkGroup(f);
}

export function Std$Format$bracket(l, f, r) {
  return mkGroup(mkNest(l.length, mkAppend(mkAppend(mkText(l), f), mkText(r))));
}

export function Std$Format$paren(f) {
  return Std$Format$bracket("(", f, ")");
}

export function Std$Format$sbracket(f) {
  return Std$Format$bracket("[", f, "]");
}

export function Std$Format$bracketFill(l, f, r) {
  return Std$Format$bracket(l, f, r);
}

export function Std$Format$joinSep(xs, sep) {
  if (xs.tag === "List$nil") return { tag: "Std$Format$nil" };
  let out = xs._1;
  let rest = xs._2;
  while (rest.tag === "List$cons") {
    out = mkAppend(mkAppend(out, sep), rest._1);
    rest = rest._2;
  }
  return out;
}

