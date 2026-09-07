/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

const nil = { tag: "List$nil" };

function cons(head, tail) {
  return { tag: "List$cons", _1: head, _2: tail };
}

function reverseAux(xs, acc) {
  let curr = xs;
  let out = acc;
  while (curr.tag === "List$cons") {
    out = cons(curr._1, out);
    curr = curr._2;
  }
  return out;
}

export function List$reverse$__redArg(as) {
  return reverseAux(as, nil);
}

export function List$reverse(as) {
  return List$reverse$__redArg(as);
}

export function List$appendTR$__redArg(as, bs) {
  return reverseAux(List$reverse$__redArg(as), bs);
}

export function List$appendTR(as, bs) {
  return List$appendTR$__redArg(as, bs);
}

export function List$find_u63_$__redArg(p, xs) {
  let curr = xs;
  while (curr.tag === "List$cons") {
    const head = curr._1;
    if (p(head)) {
      return { tag: "Option$some", _1: head };
    }
    curr = curr._2;
  }
  return { tag: "Option$none" };
}

export function List$find_u63_(p, xs) {
  return List$find_u63_$__redArg(p, xs);
}

export function List$range(n) {
  let i = Number(n);
  let out = nil;
  while (i > 0) {
    i -= 1;
    out = cons(i, out);
  }
  return out;
}
