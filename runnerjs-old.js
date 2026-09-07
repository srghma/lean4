import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// ---------------------------------------------------------------------------
// IO / Streams
// ---------------------------------------------------------------------------

globalThis.IO$getStdout = () => ({
  _5: (s) => { process.stdout.write(s); return { tag: "EST$Out$ok", _1: null, _2: null }; }
});
globalThis.IO$getStderr = () => ({
  _5: (s) => { process.stderr.write(s); return { tag: "EST$Out$ok", _1: null, _2: null }; }
});
globalThis.IO$getStdin = () => ({ tag: "EST$Out$ok", _1: {}, _2: null });

// ---------------------------------------------------------------------------
// Int / Float complex primitives
// ---------------------------------------------------------------------------

globalThis.Nat$add = (a, b) => a + b;
globalThis.Nat$sub = (a, b) => { const r = a - b; return r < 0 ? 0 : r; };
globalThis.Nat$mul = (a, b) => a * b;
globalThis.Nat$div = (a, b) => b === 0 ? 0 : Math.trunc(a / b);
globalThis.Nat$pow = (a, b) => Math.pow(a, b);
globalThis.Nat$decEq = (a, b) => a === b;
globalThis.Nat$decLt = (a, b) => a < b;
globalThis.Nat$decLe = (a, b) => a <= b;
globalThis.Nat$ble = (a, b) => a <= b;
globalThis.Nat$blt = (a, b) => a < b;
globalThis.Nat$beq = (a, b) => a === b;
globalThis.Nat$reprFast = (a) => String(a);

globalThis.Int$ofNat = (n) => n;
globalThis.Int$negSucc = (n) => -(n + 1);
globalThis.Int$add = (a, b) => a + b;
globalThis.Int$sub = (a, b) => a - b;
globalThis.Int$mul = (a, b) => a * b;
globalThis.Int$neg = (a) => -a;
globalThis.Int$decEq = (a, b) => a === b;
globalThis.Int$decLt = (a, b) => a < b;
globalThis.Int$decLe = (a, b) => a <= b;

globalThis.Int$ediv = (a, b) => {
  if (b === 0) return 0;
  let q = Math.trunc(a / b);
  let r = a % b;
  if (r < 0) {
    if (b > 0) {
      q = q - 1;
    } else {
      q = q + 1;
    }
  }
  return q;
};
globalThis.Nat$div = (a, b) => b === 0 ? 0 : Math.trunc(a / b);
globalThis.Nat$mod = (a, b) => b === 0 ? a : a % b;
globalThis.Int$negSucc = (n) => -(n + 1);
globalThis.Char$ofNat = (n) => String.fromCodePoint(n);
globalThis.Char$toNat = (c) => c.codePointAt(0);
globalThis.USize$add = (a, b) => a + b;
globalThis.USize$sub = (a, b) => a - b;
globalThis.UInt32$add = (a, b) => (a + b) >>> 0;
globalThis.Int$instInhabited = () => ({ default: 0 });

globalThis.Int$emod = (a, b) => {
  if (b === 0) return a;
  let r = a % b;
  if (r < 0) {
    if (b > 0) {
      r = r + b;
    } else {
      r = r - b;
    }
  }
  return r;
};
globalThis.Int$mod = globalThis.Int$emod;

globalThis.Float$ofNat = (n) => Number(n);
globalThis.Float$add = (a, b) => a + b;
globalThis.Float$sub   = (a, b) => a - b;
globalThis.Float$mul   = (a, b) => a * b;
globalThis.Float$div   = (a, b) => a / b;
globalThis.Float$neg   = (a) => -a;
globalThis.Float$decEq = (a, b) => a === b;
globalThis.Float$beq = (a, b) => a === b;
globalThis.Float$decLt = (a, b) => a < b;
globalThis.Float$decLe = (a, b) => a <= b;
globalThis.UInt32$decEq = (a, b) => a === b;
globalThis.UInt32$decLt = (a, b) => a < b;
globalThis.UInt32$land = (a, b) => (a & b) >>> 0;
globalThis.UInt32$lor = (a, b) => (a | b) >>> 0;
globalThis.UInt32$shiftRight = (a, b) => a >>> b;
globalThis.UInt32$shiftLeft = (a, b) => (a << b) >>> 0;
globalThis.UInt32$toNat = (a) => a >>> 0;
function listToArray(xs) {
  if (Array.isArray(xs)) return xs;
  const out = [];
  let curr = xs;
  while (curr && curr.tag === "List$cons") {
    out.push(curr._1);
    curr = curr._2;
  }
  return out;
}
globalThis.Array$empty = () => [];
globalThis.Array$mkEmpty = (n) => [];
globalThis.Array$mk = (a) => listToArray(a);
globalThis.Array$append = (a, b) => [...a, ...b];
globalThis.Array$push = (a, v) => { const a2 = a.slice(); a2.push(v); return a2; };
globalThis.Array$size = (a) => a.length;
globalThis.Array$usize = (a) => a.length;
const arrayGetInternal = (...args) => {
  if (args.length === 2) return args[0][args[1]];
  if (args.length === 3) return args[1][args[2]];
  return undefined;
};
globalThis.Array$getInternalBorrowed = arrayGetInternal;
globalThis.Array$getInternal = arrayGetInternal;
globalThis.Array$get_u33_Internal = arrayGetInternal;
globalThis.Array$get_u33_InternalBorrowed = arrayGetInternal;
globalThis.Array$ugetBorrowed = arrayGetInternal;
globalThis.Array$getObj = (a, i) => a[i];
globalThis.Array$setInternal = (a, i, v) => { const a2 = a.slice(); a2[i] = v; return a2; };
globalThis.List$reverse = (a) => {
  let res = { tag: "List$nil" };
  let curr = a;
  while (curr && curr.tag === "List$cons") {
    res = { tag: "List$cons", _1: curr._1, _2: res };
    curr = curr._2;
  }
  return res;
};
globalThis.List$appendTR$__redArg = (xs, ys) => {
  const arr = listToArray(xs).concat(listToArray(ys));
  let out = { tag: "List$nil" };
  for (let i = arr.length - 1; i >= 0; i--) {
    out = { tag: "List$cons", _1: arr[i], _2: out };
  }
  return out;
};
globalThis.List$range = (n) => {
  let out = { tag: "List$nil" };
  for (let i = n - 1; i >= 0; i--) {
    out = { tag: "List$cons", _1: i, _2: out };
  }
  return out;
};
globalThis.List$forIn_u39_$loop$__redArg = (_monad, f, xs, init) => () => {
  let acc = init;
  for (const x of listToArray(xs)) {
    let step = f.length > 1 ? f(x, acc) : f(x);
    while (typeof step === "function") {
      step = step();
    }
    if (step.tag === "EST$Out$error") return step;
    const state = step._1;
    if (state.tag === "ForInStep$done") {
      return { tag: "EST$Out$ok", _1: state._1 };
    }
    acc = state._1;
  }
  return { tag: "EST$Out$ok", _1: acc };
};

globalThis.Float$ofScientific = (m, s, e) => {
  const m_num = (m);
  const e_num = (e);
  return s ? m_num * Math.pow(10, -e_num) : m_num * Math.pow(10, e_num);
};

globalThis.String$append = (a, b) => a + b;

// ---------------------------------------------------------------------------
// Array / List complex primitives
// ---------------------------------------------------------------------------

globalThis.Array$set = (a, i, v) => { const b = [...a]; b[i] = v; return b; };
globalThis.Array$swap = (a, i, j) => { const tmp = a[i]; a[i] = a[j]; a[j] = tmp; return a; };

globalThis.Array$toList = (arr) => {
  let list = { tag: "List$nil" };
  for (let i = arr.length - 1; i >= 0; i--) {
    list = { tag: "List$cons", _1: arr[i], _2: list };
  }
  return list;
};

// ---------------------------------------------------------------------------
// Repr / ToString helpers
// ---------------------------------------------------------------------------

function reprValue(v) {
  if (v === null || v === undefined) return '(Unit.unit)';
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (typeof v === 'bigint') return v.toString();
  if (typeof v === 'number') {
    return v.toFixed(6);
  }
  if (typeof v === 'string') return JSON.stringify(v);
  if (Array.isArray(v)) {
    return '#[' + v.map(reprValue).join(', ') + ']';
  }
  if (typeof v === 'object') {
    if (v.tag === "List$nil") return "[]";
    if (v.tag === "List$cons") {
      let elements = [];
      let curr = v;
      while (curr && curr.tag === "List$cons") {
        elements.push(reprValue(curr._1));
        curr = curr._2;
      }
      return "[" + elements.join(", ") + "]";
    }
    const keys = Object.keys(v).filter(k => k !== 'tag');
    if ('tag' in v) {
      if (keys.length === 0) return v.tag;
      return `(${v.tag} ${keys.map(k => reprValue(v[k])).join(' ')})`;
    }
    const positional = Object.keys(v).filter(k => k.startsWith('_'));
    if (positional.length > 0) {
      return '{ ' + positional.map(k => reprValue(v[k])).join(', ') + ' }';
    }
    return JSON.stringify(v);
  }
  return String(v);
}

globalThis.Repr$reprStr = reprValue;

// ---------------------------------------------------------------------------
// Std.Format polyfills
// ---------------------------------------------------------------------------

function formatToPretty(f) {
  if (!f) return "";
  if (typeof f === 'string') return f;
  switch (f.tag) {
    case "Std$Format$nil": return "";
    case "Std$Format$line": return " "; // Change from \n to space for single line
    case "Std$Format$text": return f._1;
    case "Std$Format$nest": return formatToPretty(f._2);
    case "Std$Format$append": return formatToPretty(f._1) + formatToPretty(f._2);
    case "Std$Format$group": return formatToPretty(f._1);
    case "Std$Format$fill": return formatToPretty(f._1);
    default: return "";
  }
}

globalThis.Std$Format$pretty = (f, w, i, n) => formatToPretty(f);
globalThis.Std$Format$fill = (f) => f;
globalThis.Repr$addAppParen = (f, p) => (p > 0 ? { tag: "Std$Format$append", _1: { tag: "Std$Format$text", _1: "(" }, _2: { tag: "Std$Format$append", _1: f, _2: { tag: "Std$Format$text", _1: ")" } } } : f);
globalThis.Float$toString = (f) => f.toFixed(6);
globalThis.Float$repr = (f, n) => ({ tag: "Std$Format$text", _1: globalThis.Float$toString(f) });
globalThis.Bool$repr = (b) => ({ tag: "Std$Format$text", _1: b ? "true" : "false" });

globalThis.List$repr_u39_$__at__$Lean$Syntax$instReprPreresolved$repr$spec__0$__redArg = (l) => ({ tag: "Std$Format$text", _1: reprValue(l) });
globalThis.List$repr_u39_$__at__$Lean$Syntax$instReprPreresolved$repr$spec__0 = (l, n) => ({ tag: "Std$Format$text", _1: reprValue(l) });
globalThis.Std$Format$joinSep$__at__$List$repr_u39_$__at__$Lean$Syntax$instReprPreresolved$repr$spec__0$spec__0 = (l, sep) => {
  if (!l || l.tag === "List$nil") return { tag: "Std$Format$nil" };
  let curr = l;
  let out = null;
  while (curr && curr.tag === "List$cons") {
    const next = { tag: "Std$Format$text", _1: reprValue(curr._1) };
    out = out === null ? next : { tag: "Std$Format$append", _1: { tag: "Std$Format$append", _1: out, _2: sep }, _2: next };
    curr = curr._2;
  }
  return out ?? { tag: "Std$Format$nil" };
};
globalThis.Option$repr$__at__$Lean$Meta$instReprConfig__1$repr$spec__0 = (o, p) => {
  if (o.tag === "Option$none") return { tag: "Std$Format$text", _1: "none" };
  return Repr$addAppParen(
    { tag: "Std$Format$append", _1: { tag: "Std$Format$text", _1: "some " }, _2: { tag: "Std$Format$text", _1: String(o._1) } },
    p
  );
};

globalThis.String$decLE = (a, b) => a <= b;
globalThis.String$intercalate = (sep, xs) => {
  if (Array.isArray(xs)) return xs.join(sep);
  return listToArray(xs).join(sep);
};
globalThis.Int$toNat = (n) => n < 0 ? 0 : n;
globalThis.Bool$instDecidableLt = (a, b) => a < b;
globalThis.Bool$instDecidableLe = (a, b) => a <= b;
globalThis.instDecidableEqOrdering = (a, b) => a === b;
globalThis.UInt32$xor = (a, b) => (a ^ b) >>> 0;
globalThis.UInt32$complement = (a) => (~a) >>> 0;
globalThis.mkPanicMessageWithDecl = (_mod, _decl, _line, _col, msg) => msg;
globalThis.instMonadEIO = () => ({});

globalThis.String$Internal$append = (a, b) => a + b;
globalThis.String$Internal$length = (s) => s.length;
globalThis.String$extract = (s, start, stop) => s.slice(start, stop);
globalThis.String$Slice$Pos$nextn = (slice, n, pos) => pos + n;
globalThis.String$Slice$Pattern$Internal$memcmpStr = (lhs, rhs, lstart, rstart, len) =>
  lhs.slice(lstart, lstart + len) === rhs.slice(rstart, rstart + len);
globalThis.Int$repr = (n) => n.toString();
globalThis.String$decEq = (a, b) => a === b;
globalThis.String$decidableLT = (a, b) => a < b;
globalThis.String$append = (a, b) => a + b;
globalThis.String$length = (s) => s.length;
globalThis.Char$quote = (n) => {
  const c = typeof n === 'string' ? n : String.fromCodePoint(n);
  if (c === '\x00') return "'\\x00'";
  if (c === '\\') return "'\\\\'";
  if (c === "'") return "'\\''";
  if (c === '\n') return "'\\n'";
  if (c === '\r') return "'\\r'";
  if (c === '\t') return "'\\t'";
  return `'${c}'`;
};
globalThis.String$quote = (s) => JSON.stringify(s);

// ST.Prim support
class ST_Ref {
  constructor(val) { this.val = val; }
}
globalThis.ST$Prim$mkRef = (val) => new ST_Ref(val);
globalThis.ST$Prim$Ref$get = (ref) => ref.val;
globalThis.ST$Prim$Ref$set = (ref, val) => { ref.val = val; return null; };
globalThis.ST$Prim$Ref$take = (ref) => ref.val;

globalThis.Std$Format$joinSep$__at__$List$repr_u39_$__at__$main$spec__0$spec__0 = (l, s) => {
  let res = "";
  let curr = l;
  while (curr && curr.tag === "List$cons") {
    if (res !== "") res += s;
    res += curr._1;
    curr = curr._2;
  }
  return res;
};

globalThis.String$utf8ByteSize = (s) => (new TextEncoder().encode(s)).length;
globalThis.Array$size = (a) => a.length;

// Handle mangling variations
function polyfillMangling(obj) {
  for (const key of Object.keys(obj)) {
    const val = obj[key];
    const isFunction = typeof val === 'function';
    if (isFunction && !key.includes("_redArg")) {
      obj[key + "__redArg"] = val;
      obj[key + "$__redArg"] = val;
      if (key.includes("$")) {
          obj[key.replace(/\$/g, "_") + "__redArg"] = val;
          obj[key.replace(/\$/g, "_") + "$__redArg"] = val;
      }
    }
    if (key.includes("$")) {
      const underKey = key.replace(/\$/g, "_");
      if (obj[underKey] === undefined) {
        obj[underKey] = val;
      }
    }
  }
}

polyfillMangling(globalThis);

// ---------------------------------------------------------------------------
// Main entry
// ---------------------------------------------------------------------------

const arg = process.argv[2];
if (!arg) {
  console.error('Usage: node runner.js <module.lean.js>');
  process.exit(1);
}

// Resolve relative to cwd, then import by absolute path
const absPath = path.resolve(arg);
import(absPath).then(async m => {
  // Create a mutable copy of exports for cross-module calls if any
  const mutableMod = { ...m };
  polyfillMangling(mutableMod);
  Object.assign(globalThis, mutableMod);
  polyfillMangling(globalThis);

  if (m.main) {
    let res = m.main();
    while (typeof res === 'function') {
      res = res();
    }
  }
}).catch(err => {
  console.error(err.stack || err);
  process.exit(1);
});
