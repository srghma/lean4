#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]

#[path = "../../lean_runtime/src/leanh.rs"]
pub mod leanh;

pub mod lean_imports_rs {
    pub mod Init {
        pub mod Core {
            include!("../../lean_runtime/src/lean_imports_rs/Init/Core.rs");
        }
        pub mod Data {
            pub mod Array {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Array/Basic.rs");
                }
                pub mod Set {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Array/Set.rs");
                }
            }
            pub mod ByteArray {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/ByteArray/Basic.rs");
                }
            }
            pub mod Float {
                include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Float.rs");
            }
            pub mod Float32 {
                include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Float32.rs");
            }
            pub mod FloatArray {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/FloatArray/Basic.rs");
                }
            }
            pub mod Int {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Int/Basic.rs");
                }
                pub mod DivMod {
                    pub mod Basic {
                        include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Int/DivMod/Basic.rs");
                    }
                }
            }
            pub mod Nat {
                pub mod Bitwise {
                    pub mod Basic {
                        include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Nat/Bitwise/Basic.rs");
                    }
                }
                pub mod Div {
                    pub mod Basic {
                        include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Nat/Div/Basic.rs");
                    }
                }
                pub mod Gcd {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Nat/Gcd.rs");
                }
                pub mod Log2 {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Nat/Log2.rs");
                }
            }
            pub mod Ord {
                pub mod String {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Ord/String.rs");
                }
            }
            pub mod Repr {
                include!("../../lean_runtime/src/lean_imports_rs/Init/Data/Repr.rs");
            }
            pub mod SInt {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/SInt/Basic.rs");
                }
                pub mod Float {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/SInt/Float.rs");
                }
                pub mod Float32 {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/SInt/Float32.rs");
                }
            }
            pub mod String {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Basic.rs");
                }
                pub mod Bootstrap {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Bootstrap.rs");
                }
                pub mod Defs {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Defs.rs");
                }
                pub mod Length {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Length.rs");
                }
                pub mod Modify {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Modify.rs");
                }
                pub mod Pattern {
                    pub mod Basic {
                        include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Pattern/Basic.rs");
                    }
                }
                pub mod PosRaw {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/PosRaw.rs");
                }
                pub mod Slice {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/String/Slice.rs");
                }
            }
            pub mod UInt {
                pub mod Basic {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/UInt/Basic.rs");
                }
                pub mod BasicAux {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/UInt/BasicAux.rs");
                }
                pub mod Log2 {
                    include!("../../lean_runtime/src/lean_imports_rs/Init/Data/UInt/Log2.rs");
                }
            }
        }
        pub mod Meta {
            pub mod Defs {
                include!("../../lean_runtime/src/lean_imports_rs/Init/Meta/Defs.rs");
            }
        }
        pub mod Prelude {
            include!("../../lean_runtime/src/lean_imports_rs/Init/Prelude.rs");
        }
        pub mod ShareCommon {
            include!("../../lean_runtime/src/lean_imports_rs/Init/ShareCommon.rs");
        }
        pub mod System {
            pub mod IO {
                include!("../../lean_runtime/src/lean_imports_rs/Init/System/IO.rs");
            }
            pub mod Platform {
                include!("../../lean_runtime/src/lean_imports_rs/Init/System/Platform.rs");
            }
            pub mod Promise {
                include!("../../lean_runtime/src/lean_imports_rs/Init/System/Promise.rs");
            }
            pub mod ST {
                include!("../../lean_runtime/src/lean_imports_rs/Init/System/ST.rs");
            }
        }
        pub mod Util {
            include!("../../lean_runtime/src/lean_imports_rs/Init/Util.rs");
        }
    }
    pub mod lake {
        pub mod Lake {
            pub mod Load {
                pub mod Lean {
                    pub mod Elab {
                        include!("../../lean_runtime/src/lean_imports_rs/lake/Lake/Load/Lean/Elab.rs");
                    }
                }
            }
        }
    }
    pub mod Lean {
        pub mod CompactedRegion {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/CompactedRegion.rs");
        }
        pub mod Compiler {
            pub mod FFI {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Compiler/FFI.rs");
            }
            pub mod InitAttr {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Compiler/InitAttr.rs");
            }
            pub mod IR {
                pub mod Checker {
                    include!("../../lean_runtime/src/lean_imports_rs/Lean/Compiler/IR/Checker.rs");
                }
                pub mod LLVMBindings {
                    include!("../../lean_runtime/src/lean_imports_rs/Lean/Compiler/IR/LLVMBindings.rs");
                }
            }
        }
        pub mod DocString {
            pub mod Links {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/DocString/Links.rs");
            }
        }
        pub mod Elab {
            pub mod Tactic {
                pub mod Try {
                    include!("../../lean_runtime/src/lean_imports_rs/Lean/Elab/Tactic/Try.rs");
                }
            }
        }
        pub mod Environment {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/Environment.rs");
        }
        pub mod Expr {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/Expr.rs");
        }
        pub mod Level {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/Level.rs");
        }
        pub mod LoadDynlib {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/LoadDynlib.rs");
        }
        pub mod Meta {
            pub mod Basic {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Basic.rs");
            }
            pub mod Match {
                pub mod MatchEqsExt {
                    include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Match/MatchEqsExt.rs");
                }
            }
            pub mod Sym {
                pub mod DSimp {
                    pub mod DSimpM {
                        include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Sym/DSimp/DSimpM.rs");
                    }
                }
                pub mod Pattern {
                    include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Sym/Pattern.rs");
                }
                pub mod Simp {
                    pub mod SimpM {
                        include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Sym/Simp/SimpM.rs");
                    }
                }
            }
            pub mod Tactic {
                pub mod Grind {
                    pub mod Arith {
                        pub mod Cutsat {
                            pub mod Proof {
                                include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.rs");
                            }
                            pub mod Util {
                                include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Tactic/Grind/Arith/Cutsat/Util.rs");
                            }
                            pub mod Var {
                                include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Tactic/Grind/Arith/Cutsat/Var.rs");
                            }
                        }
                    }
                    pub mod Types {
                        include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Tactic/Grind/Types.rs");
                    }
                    pub mod Util {
                        include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Tactic/Grind/Util.rs");
                    }
                }
                pub mod Simp {
                    pub mod Types {
                        include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/Tactic/Simp/Types.rs");
                    }
                }
            }
            pub mod WHNF {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Meta/WHNF.rs");
            }
        }
        pub mod MetavarContext {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/MetavarContext.rs");
        }
        pub mod MonadEnv {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/MonadEnv.rs");
        }
        pub mod PrettyPrinter {
            pub mod Formatter {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/PrettyPrinter/Formatter.rs");
            }
            pub mod Parenthesizer {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/PrettyPrinter/Parenthesizer.rs");
            }
        }
        pub mod Runtime {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/Runtime.rs");
        }
        pub mod Setup {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/Setup.rs");
        }
        pub mod Shell {
            include!("../../lean_runtime/src/lean_imports_rs/Lean/Shell.rs");
        }
        pub mod Util {
            pub mod FindExpr {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Util/FindExpr.rs");
            }
            pub mod Profile {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Util/Profile.rs");
            }
            pub mod ReplaceExpr {
                include!("../../lean_runtime/src/lean_imports_rs/Lean/Util/ReplaceExpr.rs");
            }
        }
    }
    pub mod Std {
        pub mod Data {
            pub mod ByteSlice {
                include!("../../lean_runtime/src/lean_imports_rs/Std/Data/ByteSlice.rs");
            }
        }
        pub mod Internal {
            pub mod UV {
                pub mod DNS {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/DNS.rs");
                }
                pub mod Loop {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/Loop.rs");
                }
                pub mod Signal {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/Signal.rs");
                }
                pub mod System {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/System.rs");
                }
                pub mod TCP {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/TCP.rs");
                }
                pub mod Timer {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/Timer.rs");
                }
                pub mod UDP {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Internal/UV/UDP.rs");
                }
            }
        }
        pub mod Net {
            pub mod Addr {
                include!("../../lean_runtime/src/lean_imports_rs/Std/Net/Addr.rs");
            }
        }
        pub mod Sync {
            pub mod Mutex {
                include!("../../lean_runtime/src/lean_imports_rs/Std/Sync/Mutex.rs");
            }
            pub mod RecursiveMutex {
                include!("../../lean_runtime/src/lean_imports_rs/Std/Sync/RecursiveMutex.rs");
            }
            pub mod SharedMutex {
                include!("../../lean_runtime/src/lean_imports_rs/Std/Sync/SharedMutex.rs");
            }
        }
        pub mod Time {
            pub mod DateTime {
                pub mod Timestamp {
                    include!("../../lean_runtime/src/lean_imports_rs/Std/Time/DateTime/Timestamp.rs");
                }
            }
            pub mod Zoned {
                pub mod Database {
                    pub mod Windows {
                        include!("../../lean_runtime/src/lean_imports_rs/Std/Time/Zoned/Database/Windows.rs");
                    }
                }
            }
        }
    }

    pub use lake::Lake;
}
