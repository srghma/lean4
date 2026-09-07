import LakeJs.Js

open Lean.Compiler.JS

def lean_nat_gcd := [JS_FUNC|inputs(a, b)|returns=a|
  a = BigInt(a);
  b = BigInt(b);
  while (b != 0) {
    const t = b;
    b = a % b;
    a = t;
  }
]
