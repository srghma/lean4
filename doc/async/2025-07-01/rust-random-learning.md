Pinning

# [Variance](https://doc.rust-lang.org/reference/subtyping.html#variance)

Variance is a property that generic types have with respect to their arguments.
A generic type's _variance_ in a parameter is how the subtyping of the parameter affects the subtyping of the type.

- `F<T>` is _covariant_ over `T` if `T` being a subtype of `U` implies that `F<T>` is a subtype of `F<U>` (subtyping "passes through")
- `F<T>` is _contravariant_ over `T` if `T` being a subtype of `U` implies that `F<U>` is a subtype of `F<T>`
- `F<T>` is _invariant_ over `T` otherwise (no subtyping relation can be derived)

Variance of types is automatically determined as follows

| Type                          | Variance in `'a` | Variance in `T` |
| ----------------------------- | ---------------- | --------------- |
| `&'a T`                       | covariant        | covariant       |
| `&'a mut T`                   | covariant        | invariant       |
| `*const T`                    |                  | covariant       |
| `*mut T`                      |                  | invariant       |
| `[T]` and `[T; n]`            |                  | covariant       |
| `fn() -> T`                   |                  | covariant       |
| `fn(T) -> ()`                 |                  | contravariant   |
| `std::cell::UnsafeCell<T>`    |                  | invariant       |
| `std::marker::PhantomData<T>` |                  | covariant       |
| `dyn Trait<T> + 'a`           | covariant        | invariant       |

make examples

1. covariant_example_in_lifetime (show works), covariant_example_in_type (show works), invariant_example_in_lifetime (show doesnt), invariant_example_in_type (show doesnt), contravariant_example_in_lifetime (show doesnt), contravariant_example_in_type (show doesnt)
2. ....
   ...
3. ...

```rust
```
