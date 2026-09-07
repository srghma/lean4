/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

function field(obj, idx) {
  if (obj == null) return undefined;
  if (Array.isArray(obj)) return obj[idx];
  const key = `_${idx + 1}`;
  if (Object.prototype.hasOwnProperty.call(obj, key)) return obj[key];
  return obj[idx];
}

function getPure(inst) {
  const applicative = field(inst, 0);
  return field(applicative, 1) ?? field(applicative, 0);
}

function getBind(inst) {
  return field(inst, 1) ?? field(inst, 0);
}

export function List$forIn_u39_$loop$__redArg(inst, f, asPrime, b) {
  const pure = getPure(inst);
  const bind = getBind(inst);
  if (typeof pure !== "function" || typeof bind !== "function") {
    throw new Error("unsupported monad instance for List.forIn'");
  }

  const loop = (xs, acc) => {
    if (xs.tag !== "List$cons") {
      return pure(acc);
    }
    return bind(f(xs._1, acc), (step) => {
      if (step.tag === "ForInStep$done") {
        return pure(step._1);
      }
      return loop(xs._2, step._1);
    });
  };

  return loop(asPrime, b);
}
