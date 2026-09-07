/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

export function Bool$instDecidableLe(a, b) {
  return (!a) || b;
}

export function Bool$instDecidableLt(a, b) {
  return (!a) && b;
}
