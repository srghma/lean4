module

prelude

public import Lean.Kernel.TypeChecker

@[expose] public section

namespace Lean4Lean
namespace Environment

open Lean hiding Environment Exception
open Lean.Kernel TypeChecker

/-
The original Lean4Lean primitive checks rely on compile-time quotation and meta-only support
that does not fit the bootstrapped `src/Lean` module environment yet. Keep the admission hooks
in place but conservatively disable primitive special-casing for now.
-/

def checkPrimitiveDef (_v : DefinitionVal) : M Bool :=
  pure false

def checkPrimitiveInductive (_env : Environment) (_lparams : List Name) (_nparams : Nat)
    (_types : List InductiveType) (_isUnsafe : Bool) : Except Exception Bool :=
  pure false

end Environment
end Lean4Lean
