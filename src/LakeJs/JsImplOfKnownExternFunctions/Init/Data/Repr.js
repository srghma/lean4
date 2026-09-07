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

function quoteCharCore(c, inString = false) {
  if (c === "\n") return "\\n";
  if (c === "\t") return "\\t";
  if (c === "\\") return "\\\\";
  if (c === "\"") return "\\\"";
  if (!inString && c === "'") return "\\'";
  const code = c.codePointAt(0);
  if (code <= 31 || c === "\x7f") {
    return `\\x${code.toString(16).toUpperCase().padStart(2, "0")}`;
  }
  return c;
}

export function lean_string_of_usize(u) {
  return String(u);
}

export function Bool$repr$__redArg(b) {
  return mkText(b ? "true" : "false");
}

export function String$quote(s) {
  return JSON.stringify(s);
}

export function Char$quote(c) {
  return `'${quoteCharCore(c)}'`;
}

export function Repr$addAppParen(f, prec) {
  if (prec >= 1024) {
    return mkGroup(mkNest(1, mkAppend(mkAppend(mkText("("), f), mkText(")"))));
  }
  return f;
}
