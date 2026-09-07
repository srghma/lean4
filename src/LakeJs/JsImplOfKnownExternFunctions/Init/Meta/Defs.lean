export function lean_version_get_major(...args) {
  throw new Error('not implemented');
}

export function lean_version_get_minor(...args) {
  throw new Error('not implemented');
}

export function lean_version_get_patch(...args) {
  throw new Error('not implemented');
}

export function lean_get_githash(...args) {
  throw new Error('not implemented');
}

export function lean_version_get_is_release(...args) {
  throw new Error('not implemented');
}

export function lean_version_get_special_desc(...args) {
  throw new Error('not implemented');
}

export function lean_internal_is_stage0(...args) {
  throw new Error('not implemented');
}

export function lean_internal_has_llvm_backend(...args) {
  throw new Error('not implemented');
}

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

function reprText(value) {
  if (value && typeof value === "object" && typeof value.tag === "string" && value.tag.startsWith("Std$Format$")) {
    return value;
  }
  if (typeof value === "string") {
    return mkText(value);
  }
  if (typeof value === "bigint" || typeof value === "number" || typeof value === "boolean") {
    return mkText(String(value));
  }
  if (value && value.tag === "PUnit$unit") {
    return mkText("()");
  }
  return mkText(String(value));
}

function addAppParen(f, prec) {
  if (prec >= 1024) {
    return mkGroup(mkNest(1, mkAppend(mkAppend(mkText("("), f), mkText(")"))));
  }
  return f;
}

function reprPreresolved(value) {
  if (typeof value === "string") {
    return mkText(JSON.stringify(value));
  }
  return reprText(value);
}

export function Std$Format$joinSep$__at__$List$repr_u39_$__at__$Lean$Syntax$instReprPreresolved$repr$spec__0$spec__0(xs, sep) {
  if (xs.tag === "List$nil") {
    return { tag: "Std$Format$nil" };
  }
  let out = reprPreresolved(xs._1);
  let rest = xs._2;
  while (rest.tag === "List$cons") {
    out = mkAppend(mkAppend(out, sep), reprPreresolved(rest._1));
    rest = rest._2;
  }
  return out;
}

export function List$repr_u39_$__at__$Lean$Syntax$instReprPreresolved$repr$spec__0$__redArg(xs) {
  if (xs.tag === "List$nil") {
    return mkText("[]");
  }
  return mkGroup(
    mkNest(
      1,
      mkAppend(
        mkAppend(
          mkText("["),
          Std$Format$joinSep$__at__$List$repr_u39_$__at__$Lean$Syntax$instReprPreresolved$repr$spec__0$spec__0(
            xs,
            mkAppend(mkText(","), { tag: "Std$Format$line" })
          )
        ),
        mkText("]")
      )
    )
  );
}

export function Option$repr$__at__$Lean$Meta$instReprConfig__1$repr$spec__0(opt, prec) {
  if (opt.tag === "Option$none") {
    return mkText("none");
  }
  return addAppParen(mkAppend(mkText("some "), reprText(opt._1)), prec);
}
