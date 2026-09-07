/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

export function instDecidableEqOrdering(a, b) {
  if (typeof a === "number" || typeof b === "number") {
    return a === b;
  }
  return a.tag === b.tag;
}
