I want to implement js_extern_inlined , this is like extern attribute but instead of string I attach the subset of js code

after it works - I want to use it in @contextScopeItemMention  to replace

  if jsNameBase == "Nat$add" || jsNameBase == "lean_nat_add" || jsNameBase == "Int$add" || jsNameBase == "lean_int_add" || jsNameBase == "Float$add" ||
      jsNameBase == "String$append" || jsNameBase == "lean_string_append" || jsNameBase == "String$Internal$append" || jsNameBase == "USize$add" then
    if args.size == 2 then return JsExpr.binary args[0]! "+" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "+" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$mul" || jsNameBase == "lean_nat_mul" || jsNameBase == "Int$mul" || jsNameBase == "lean_int_mul" || jsNameBase == "Float$mul" then
    if args.size == 2 then return JsExpr.binary args[0]! "*" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "*" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Int$sub" || jsNameBase == "lean_int_sub" || jsNameBase == "Float$sub" || jsNameBase == "USize$sub" then
    if args.size == 2 then return JsExpr.binary args[0]! "-" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "-" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$sub" || jsNameBase == "lean_nat_sub" then
    if args.size == 2 then return JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "max") #[JsExpr.litNum "0", JsExpr.binary args[0]! "-" args[1]!]
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "max") #[JsExpr.litNum "0", JsExpr.binary allArgs[0]! "-" allArgs[1]!]
    else return ← mkNamedCall jsName


with definitions of functions inside of this js_external_inlined

why? what is the difference btw external and js_external_inlined?

external is how to implement ffi in c++ and js, js_external_inlined is fii for js only

if func has external only then after Xxx.lean is compiled to js - we will add `import { funcs } from 'Xxx.external.js`

if func has external and js_external_inlined - we prefer js_external_inlined - we inline this code into generated code. why? it allows to partially of fully evaluate code, bc we know what js is doing!!, cool, right?

