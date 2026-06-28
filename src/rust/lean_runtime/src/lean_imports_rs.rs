pub mod Init {
    #[path = "Core.rs"]
    pub mod Core;
    pub mod Data {
        pub mod Array {
            #[path = "Basic.rs"]
            pub mod Basic;
            #[path = "Set.rs"]
            pub mod Set;
        }
        pub mod ByteArray {
            #[path = "Basic.rs"]
            pub mod Basic;
        }
        #[path = "Float.rs"]
        pub mod Float;
        #[path = "Float32.rs"]
        pub mod Float32;
        pub mod FloatArray {
            #[path = "Basic.rs"]
            pub mod Basic;
        }
        pub mod Int {
            #[path = "Basic.rs"]
            pub mod Basic;
            pub mod DivMod {
                #[path = "Basic.rs"]
                pub mod Basic;
            }
        }
        pub mod Nat {
            pub mod Bitwise {
                #[path = "Basic.rs"]
                pub mod Basic;
            }
            pub mod Div {
                #[path = "Basic.rs"]
                pub mod Basic;
            }
            #[path = "Gcd.rs"]
            pub mod Gcd;
            #[path = "Log2.rs"]
            pub mod Log2;
        }
        pub mod Ord {
            #[path = "String.rs"]
            pub mod String;
        }
        #[path = "Repr.rs"]
        pub mod Repr;
        pub mod SInt {
            #[path = "Basic.rs"]
            pub mod Basic;
            #[path = "Float.rs"]
            pub mod Float;
            #[path = "Float32.rs"]
            pub mod Float32;
        }
        pub mod String {
            #[path = "Basic.rs"]
            pub mod Basic;
            #[path = "Bootstrap.rs"]
            pub mod Bootstrap;
            #[path = "Defs.rs"]
            pub mod Defs;
            #[path = "Length.rs"]
            pub mod Length;
            #[path = "Modify.rs"]
            pub mod Modify;
            pub mod Pattern {
                #[path = "Basic.rs"]
                pub mod Basic;
            }
            #[path = "PosRaw.rs"]
            pub mod PosRaw;
            #[path = "Slice.rs"]
            pub mod Slice;
        }
        pub mod UInt {
            #[path = "Basic.rs"]
            pub mod Basic;
            #[path = "BasicAux.rs"]
            pub mod BasicAux;
            #[path = "Log2.rs"]
            pub mod Log2;
        }
    }
    pub mod Meta {
        #[path = "Defs.rs"]
        pub mod Defs;
    }
    #[path = "Prelude.rs"]
    pub mod Prelude;
    #[path = "ShareCommon.rs"]
    pub mod ShareCommon;
    pub mod System {
        #[path = "IO.rs"]
        pub mod IO;
        #[path = "Platform.rs"]
        pub mod Platform;
        #[path = "Promise.rs"]
        pub mod Promise;
        #[path = "ST.rs"]
        pub mod ST;
    }
    #[path = "Util.rs"]
    pub mod Util;
}
pub mod lake {
    pub mod Lake {
        pub mod Load {
            pub mod Lean {
                #[path = "Elab.rs"]
                pub mod Elab;
            }
        }
    }
}
pub mod Lean {
    #[path = "CompactedRegion.rs"]
    pub mod CompactedRegion;
    pub mod Compiler {
        #[path = "FFI.rs"]
        pub mod FFI;
        #[path = "InitAttr.rs"]
        pub mod InitAttr;
        pub mod IR {
            #[path = "Checker.rs"]
            pub mod Checker;
            #[path = "LLVMBindings.rs"]
            pub mod LLVMBindings;
        }
    }
    pub mod DocString {
        #[path = "Links.rs"]
        pub mod Links;
    }
    pub mod Elab {
        pub mod Tactic {
            #[path = "Try.rs"]
            pub mod Try;
        }
    }
    #[path = "Environment.rs"]
    pub mod Environment;
    #[path = "Expr.rs"]
    pub mod Expr;
    #[path = "Level.rs"]
    pub mod Level;
    #[path = "LoadDynlib.rs"]
    pub mod LoadDynlib;
    pub mod Meta {
        #[path = "Basic.rs"]
        pub mod Basic;
        pub mod Match {
            #[path = "MatchEqsExt.rs"]
            pub mod MatchEqsExt;
        }
        pub mod Sym {
            pub mod DSimp {
                #[path = "DSimpM.rs"]
                pub mod DSimpM;
            }
            #[path = "Pattern.rs"]
            pub mod Pattern;
            pub mod Simp {
                #[path = "SimpM.rs"]
                pub mod SimpM;
            }
        }
        pub mod Tactic {
            pub mod Grind {
                pub mod Arith {
                    pub mod Cutsat {
                        #[path = "Proof.rs"]
                        pub mod Proof;
                        #[path = "Util.rs"]
                        pub mod Util;
                        #[path = "Var.rs"]
                        pub mod Var;
                    }
                }
                #[path = "Types.rs"]
                pub mod Types;
                #[path = "Util.rs"]
                pub mod Util;
            }
            pub mod Simp {
                #[path = "Types.rs"]
                pub mod Types;
            }
        }
        #[path = "WHNF.rs"]
        pub mod WHNF;
    }
    #[path = "MetavarContext.rs"]
    pub mod MetavarContext;
    #[path = "MonadEnv.rs"]
    pub mod MonadEnv;
    pub mod PrettyPrinter {
        #[path = "Formatter.rs"]
        pub mod Formatter;
        #[path = "Parenthesizer.rs"]
        pub mod Parenthesizer;
    }
    #[path = "Runtime.rs"]
    pub mod Runtime;
    #[path = "Setup.rs"]
    pub mod Setup;
    #[path = "Shell.rs"]
    pub mod Shell;
    pub mod Util {
        #[path = "FindExpr.rs"]
        pub mod FindExpr;
        #[path = "Profile.rs"]
        pub mod Profile;
        #[path = "ReplaceExpr.rs"]
        pub mod ReplaceExpr;
    }
}
pub mod Std {
    pub mod Data {
        #[path = "ByteSlice.rs"]
        pub mod ByteSlice;
    }
    pub mod Internal {
        pub mod UV {
            #[path = "DNS.rs"]
            pub mod DNS;
            #[path = "Loop.rs"]
            pub mod Loop;
            #[path = "Signal.rs"]
            pub mod Signal;
            #[path = "System.rs"]
            pub mod System;
            #[path = "TCP.rs"]
            pub mod TCP;
            #[path = "Timer.rs"]
            pub mod Timer;
            #[path = "UDP.rs"]
            pub mod UDP;
        }
    }
    pub mod Net {
        #[path = "Addr.rs"]
        pub mod Addr;
    }
    pub mod Sync {
        #[path = "Mutex.rs"]
        pub mod Mutex;
        #[path = "RecursiveMutex.rs"]
        pub mod RecursiveMutex;
        #[path = "SharedMutex.rs"]
        pub mod SharedMutex;
    }
    pub mod Time {
        pub mod DateTime {
            #[path = "Timestamp.rs"]
            pub mod Timestamp;
        }
        pub mod Zoned {
            pub mod Database {
                #[path = "Windows.rs"]
                pub mod Windows;
            }
        }
    }
}
