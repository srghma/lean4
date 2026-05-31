```python
EStateM (ε σ α : Type u) := σ → Result ε σ α
  EST (ε : Type) (σ : Type) : Type → Type := EStateM ε σ # restricted bc restricted to `(σ : Type)` not `IO.RealWorld`
    ST (σ : Type) := EST Empty σ
  EIO (ε : Type) : Type → Type := EStateM ε IO.RealWorld
    IO : Type → Type := EIO Error

ST IO.RealWorld := EStateM Empty IO.RealWorld := IO.RealWorld → Result Empty IO.RealWorld α
```
