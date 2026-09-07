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

function mkNest(indent, f) {
  return { tag: "Std$Format$nest", _1: indent, _2: f };
}

function mkGroup(f) {
  return { tag: "Std$Format$group", _1: f };
}

export function Int$repr(i, prec) {
  const text = mkText(String(i));
  if (i < 0n && prec >= 1024) {
    return mkGroup(mkNest(1, mkAppend(mkAppend(mkText("("), text), mkText(")"))));
  }
  return text;
}
