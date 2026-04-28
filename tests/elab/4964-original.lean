/-!
Issue #4964: nested inductive translation does not support dependent fields
that mention functions over the nested container.
-/

def List.keys (pairs : List (α × β)) : List α :=
  match pairs with
  | [] => []
  | ⟨a, _⟩ :: rest => a :: keys rest

inductive Term : Type where
  | var : String → Term
  | app : Term → Term → Term
  | lam : String → Term → Term
  | record : (entries : List (String × Term)) → (unique : entries.keys.Nodup) → Term
