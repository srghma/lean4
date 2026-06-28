after `just update-and-regenerate` I run `just check-gen` to see that `gen` dir typechecks (it uses `@[extern]` to import only functions from `lean_imports_rs` and using `@[export]` it defines functions that later rust should use)


here is what script have found and we need to fix (it checks only ./src/**/*.lean files and ./src/rust/lean_runtime/src/*.rs (excludes gen and not yet filled lean_imports_rust (BUT if at least one rust function there will have real body, i.e. it will not just reexport that is defined in ./src/rust/lean_runtime/src/*.rs or (yes, such pattern exists, check /home/srghma/projects/lean4/lean_imports_rust_code_using_extern__duplicates.txt analysis file of lean files) ./src/rust/lean_runtime/src/gen/**/*.rs - then we should update it too, but lets not, I have written full output to `./srghmascripts/exported_imported_lean_rust_fns.ts --only-extern-empty --only-extern-missing --only-export-wrong --only-export-defined --only-export-externc --only-export-dynamic --only-export-missing > ./srghmascripts/exported_imported_lean_rust_fns--exluding-success.txt`)))

```
$ ./srghmascripts/exported_imported_lean_rust_fns.ts --only-extern-empty --only-extern-missing --only-export-wrong --only-export-defined --only-export-externc --only-export-dynamic --only-export-missing
Scanning Lean codebase under: /home/srghma/projects/lean4/src...
Processed 135 Lean files and indexed 89 Rust files.

# List of all functions that lean imports from rust

src/Init/Prelude.lean
  Line 1803: [extern "lean_nat_dec_eq"] Nat.beq <- ❌ (Rust does not define this function)
  Line 1853: [extern "lean_nat_dec_eq"] Nat.decEq <- ❌ (Rust does not define this function)
  Line 1873: [extern "lean_nat_dec_le"] Nat.ble <- ❌ (Rust does not define this function)
  Line 2070: [extern "lean_nat_dec_le"] Nat.decLe <- ❌ (Rust does not define this function)
  Line 2084: [extern "lean_nat_dec_lt"] Nat.decLt <- ❌ (Rust does not define this function)

....

# list of all functions that rust imports from lean

src/Init/Data/String/Basic.lean
  Line 3056: @[export lean_string_offsetofpos] Internal.offsetOfPosImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Basic::lean_string_offsetofpos;`)

src/Init/Prelude.lean
  Line 4729: @[export lean_name_mk_string] mkStr -> src/rust/lean_runtime/src/runtime_object_name.rs:96 -> 🛠️ (Defined in Rust: `pub(crate) unsafe fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {`, should be `use crate::Init::Prelude::lean_name_mk_string;`)
  Line 4736: @[export lean_name_mk_numeral] mkNum -> src/rust/lean_runtime/src/runtime_object_name.rs:104 -> 🛠️ (Defined in Rust: `pub(crate) unsafe fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject {`, should be `use crate::Init::Prelude::lean_name_mk_numeral;`
)
  Line 5610: @[export lean_erase_macro_scopes] Name.eraseMacroScopes -> ❌ (Not found in Rust, should be `use crate::Init::Prelude::lean_erase_macro_scopes;`)
  Line 5621: @[export lean_simp_macro_scopes] Name.simpMacroScopes -> ❌ (Not found in Rust, should be `use crate::Init::Prelude::lean_simp_macro_scopes;`)


......

========================================================================
WORKSPACE ANALYSIS SUMMARY
========================================================================
Lean imports from Rust ([extern]): (Lean <- Rust)
  Total occurrences:                                                          954
  Rust defined this function and function body is not empty (correct) (✅):   559
  Rust defined this function but function body is empty (empty) (⚠️):        0
  Rust does not define this function (missing) (❌):                          395

Rust should import from Lean ([export]): (Lean -> Rust)
  Total occurrences:                                                          245
  Function is found in rust code and import is correct (correct) (✅):        9
  Function is found in rust code, but import is wrong (wrong) (⚠️):          0
  Function is found in rust code, but is defined in rust (defined) (🛠️):     8
  Function is found inside of extern "C" block / FFI (externc) (🔌):          107
  Function is referenced via dynamic string lookup (dynamic) (🔍):            1
  Function is not found in rust code (missing) (❌):                          120
========================================================================
```

# what it means?

## what to do with extern "C" in ./src/rust/lean_runtime/src/*.rs?

in ./src/rust/lean_runtime/src/*.rs `extern "C"` should be only used for importing 3d party deps (e.g. `uv_*` or `__gmp`)


e.g. in ./src/rust/lean_runtime/src/*.rs You will find

```rs
extern "C" {
  fn lean_io_check_canceled_core() -> bool;
  fn lean_io_cancel_core(t: *mut LeanObject);
  fn lean_io_get_task_state_core(t: *mut LeanObject) -> u8;
  fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject;
  fn lean_task_spawn_core(
      c: *mut LeanObject,
      prio: core::ffi::c_uint,
      keep_alive: bool,
  ) -> *mut LeanObject;
  fn lean_task_map_core(
      f: *mut LeanObject,
      t: *mut LeanObject,
      prio: core::ffi::c_uint,
      sync: bool,
      keep_alive: bool,
  ) -> *mut LeanObject;
  fn lean_task_bind_core(
      t: *mut LeanObject,
      f: *mut LeanObject,
      prio: core::ffi::c_uint,
      sync: bool,
      keep_alive: bool,
  ) -> *mut LeanObject;
}
```

these are deps that are defined in lean and should be imported using ordinary `use ` from `gen` dir

e.g.
- `lean_io_check_canceled_core`

      ```
      ~/projects/lean4  ⇅ rust-rewrite ±  rg 'lean_io_check_canceled_core' ./build/release/stage0/
      ./build/release/stage0/include/lean/lean.h
      1337:LEAN_EXPORT bool lean_io_check_canceled_core(void);
      ~/projects/lean4  ⇅ rust-rewrite ±  rg 'lean_io_check_canceled_core' ./src/include/lean/lean_header.template
      548:LEAN_EXPORT bool lean_io_check_canceled_core(void);
      ~/projects/lean4  ⇅ rust-rewrite ±  rg 'lean_io_check_canceled_core' ./origin-master-src/
      ./origin-master-src/runtime/object.h
      287:inline bool io_check_canceled_core() { return lean_io_check_canceled_core(); }

      ./origin-master-src/include/lean/lean.h
      1337:LEAN_EXPORT bool lean_io_check_canceled_core(void);

      ./origin-master-src/runtime/object.cpp
      1246:extern "C" LEAN_EXPORT bool lean_io_check_canceled_core() {

      ./origin-master-src/runtime/io.cpp
      1571:    return lean_io_check_canceled_core();

      ~/projects/lean4  ⇅ rust-rewrite ±  rg 'lean_io_check_canceled_core' ./src/rust/lean_runtime/
     ./src/rust/lean_runtime/src/runtime_io_task.rs
     12:        fn lean_io_check_canceled_core() -> bool;
     61:        lean_io_check_canceled_core() as u8

     ./src/rust/lean_runtime/src/runtime_object_task.rs
     13://   lean_io_check_canceled_core, lean_io_cancel_core
     1056:    pub(crate) fn lean_io_check_canceled_core() -> bool {
      ```

  we have found that since it was defined in origin-master-src then we see that `extern "C"` is just old bad way to import it -> it should be imported using ordinary rust `use`
  same with other modules

-

```rs
    // ---------------------------------------------------------------------------
    // Lean runtime Rust ABI bindings
    // lean_inc, lean_dec, lean_is_scalar, lean_box, lean_unbox, lean_ptr_tag,
    // lean_mark_persistent are Rust functions from super::* — not declared here.
    // lean_alloc_ctor / lean_ctor_get / lean_ctor_set are local shims below.
    // lean_stack_has_space, lean_memory_within_limit, check_heartbeat_exceeded,
    // check_interrupted_flag are Rust functions from super::* — not declared here.
    // ---------------------------------------------------------------------------

    extern "C" {

        // Names
        fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
        fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;
        // lean_name_anonymous: implemented as Rust shim below (Name.anonymous = boxed scalar 0)
        // lean_name_eq_raw is inline C++; implemented as Rust shim below
```

```
~/projects/lean4  ⇅ rust-rewrite ✚  rg -A 3 'lean_name_mk_string' ./build/release/stage0/ ./src/include/lean/lean_header.template ./origin-master-src/ ./src/rust/lean_runtime/ && echo "\n\n+++++++++++++++\n\n"               <<<
./src/rust/lean_runtime/src/library_print.rs
20:        fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
21-        // Lean-compiled (Lean.Expr): mkFVar — takes owned FVarId (= Name at ABI), returns owned Expr.
22-        fn lean_expr_mk_fvar(n: *mut LeanObject) -> *mut LeanObject;
23-        // Rust implementation in kernel_instantiate.rs: both args borrowed, returns owned.
--
307:            lean_name_mk_string(lean_box(0), x_str) // lean_box(0)=anonymous (scalar, no RC)
308-        } else {
309-            lean_inc(n);
310-            n

./src/rust/lean_runtime/src/lib.rs
38:    fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
39-    fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
40-    fn lean_mk_io_error_invalid_argument(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
41-    fn lean_mk_io_error_invalid_argument_file(
--
2257:    let raw_name = lean_name_mk_string(lean_box(0), raw_text);
2258-    LeanName { obj: raw_name }
2259-}
2260-
--
2266:        let raw_name = lean_name_mk_string(name.obj, raw_text);
2267-        name = LeanName { obj: raw_name };
2268-    }
2269-    name
--
4765:        let tmp = lean_name_mk_string(lean_box(0), string);
4766-        lean_mark_persistent(tmp);
4767-        let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
4768-        let state = NameGeneratorState {

./src/rust/lean_runtime/src/kernel_trace.rs
37:        NAME_STRING_TAG => lean_name_mk_string(prefix, lean_ctor_get(suffix, 1)),
38-        NAME_NUMERAL_TAG => lean_name_mk_numeral(prefix, lean_ctor_get(suffix, 1)),
39-        _ => prefix,
40-    }

./src/rust/lean_runtime/src/library_ir_interpreter.rs
96:        fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
97-
98-        // IO helpers
99-        fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool;
--
1226:        let interp_name = lean_name_mk_string(lean_box(0), interp_str);
1227:        let prefer_native_name = lean_name_mk_string(interp_name, prefer_native_str);
1228-        // This name is a process-lifetime immortal global read concurrently from many
1229-        // worker threads (every `Interpreter::new` does a non-atomic `lean_inc`/consume on
1230-        // it via `lean_options_get_bool`). Mark it persistent (rc = 0, inc/dec become
--
2260:        lean_name_mk_string(lean_box(0), str_obj)
2261-    }
2262-
2263-    // ---------------------------------------------------------------------------

./src/rust/lean_runtime/src/runtime_object_name.rs
96:    pub(crate) unsafe fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {
97-        let r = lean_runtime_alloc_ctor(1, 2, 8);
98-        lean_runtime_ctor_set(r, 0, prefix);
99-        lean_runtime_ctor_set(r, 1, s);

./src/rust/lean_runtime/src/kernel_type_checker.rs
38:        fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
39-        fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;
40-        // lean_name_anonymous: implemented as Rust shim below (Name.anonymous = boxed scalar 0)
41-        // lean_name_eq_raw is inline C++; implemented as Rust shim below
--
2689:            // lean_name_mk_string consumes both `cur` and `s` (obj_arg). Do NOT dec
2690-            // them afterwards — ownership is transferred into the new name.
2691:            cur = lean_name_mk_string(cur, s);
2692-        }
2693-        cur
2694-    }
--
6651:        lean_name_mk_string(i, s)
6652-    }
6653-
6654-    /// `name.append_after(i)` (`Name.appendIndexAfter`). BORROWS `n`, returns owned name.
--
6705:                    r = lean_name_mk_string(r, s);
6706-                }
6707-                NamePart::Num(n) => {
6708-                    lean_inc(n);

./origin-master-src/util/name.cpp
23:extern "C" obj_res lean_name_mk_string(obj_arg p, obj_arg s);
24-extern "C" obj_res lean_name_mk_numeral(obj_arg p, obj_arg n);
25-
26-static inline obj_res name_mk_string_of_cstr(obj_arg p, char const * s) {
27:    return lean_name_mk_string(p, mk_string(s));
28-}
29-
30-constexpr char const * anonymous_str = "[anonymous]";
--
114:    object_ref(lean_name_mk_string(prefix.raw(), s.raw())) {
115-    inc(prefix.raw());
116-    inc(s.raw());
117-}

./src/rust/lean_runtime/src/gen/Init/Prelude.rs
10541:pub unsafe fn lean_name_mk_string(
10542-    mut v_p_3572_: *mut LeanObject,
10543-    mut v_s_3573_: *mut LeanObject,
10544-) -> *mut LeanObject {
```

`extern "C"` is just a way to import (bad). it should be imported as `use crate::gen::Init::Prelude::lean_name_mk_string`, and already existing definition `pub(crate) unsafe fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {` should be removed (but check that it will work too. if no - EmitRust probably is wrong).

lean_name_anonymous

```
$ rg -A 3 'lean_name_anonymous' ./build/release/stage0/ ./src/include/lean/lean_header.template ./origin-master-src/ ./src/rust/lean_runtime/ && echo "\n\n+++++++++++++++\n\n"              <<<
./src/rust/lean_runtime/src/kernel_type_checker.rs
40:        // lean_name_anonymous: implemented as Rust shim below (Name.anonymous = boxed scalar 0)
41-        // lean_name_eq_raw is inline C++; implemented as Rust shim below
42-
43-        // Levels
--
920:    pub(crate) unsafe fn lean_name_anonymous() -> *mut LeanObject {
921-        super::lean_box(0)
922-    }
923-
--
2686:        let mut cur = lean_name_anonymous();
2687-        for &part in parts {
2688-            let s = lean_mk_string(part.as_ptr(), part.len());
2689-            // lean_name_mk_string consumes both `cur` and `s` (obj_arg). Do NOT dec
--
6273:        let n = lean_name_anonymous();
6274-        lean_inc(domain);
6275-        lean_inc(body);
6276-        lean_expr_mk_forall(n, domain, body, BI_DEFAULT)
--
7569:                    let anon = lean_name_anonymous();
7570-                    let minor_name = name_replace_prefix(cnstr_name, ind_type_name, anon);
7571-                    let minor = self.mk_local_decl(minor_name, minor_ty, BI_DEFAULT);
7572-                    lean_dec(minor_name);
```

in cpp it is used as `name()` e.g. in `name minor_name = cnstr_name.replace_prefix(ind_type_name, name());` so ok, lets just move this comment to be before `pub(crate) unsafe fn lean_name_anonymous() -> *mut LeanObject {`


-----


more intereseting case is what to do with

```
extern "lean_string_append"
  - src/Init/Data/String/Bootstrap.lean:76  opaque append  expose=false
  - src/Init/Data/String/Defs.lean:93  def String.append  expose=true
```

```
~/projects/lean4  ⇅ rust-rewrite ±✚  rg -A 3 'lean_string_append' ./src/**/*.lean ./src/rust/lean_runtime/src/lean_imports_rs ./src/rust/lean_runtime/src/*.rs
./src/Init/Data/String/Bootstrap.lean
76:@[extern "lean_string_append"]
77-opaque append : String → (@& String) → String
78-
79-@[extern "lean_string_utf8_next"]

./src/Init/Data/String/Defs.lean
93:@[extern "lean_string_append", expose]
94-def String.append (s : String) (t : @& String) : String where
95-  toByteArray := s.toByteArray ++ t.toByteArray
96-  isValidUTF8 := s.isValidUTF8.append t.isValidUTF8

./src/rust/lean_runtime/src/runtime_object_string.rs
331:    pub(crate) unsafe fn lean_string_append(
332-        s1: *mut LeanObject,
333-        s2: *mut LeanObject,
334-    ) -> *mut LeanObject {

./src/rust/lean_runtime/src/lean_imports_rs/Init/Data/String/Defs.rs
8:pub fn lean_string_append(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
9:    todo!("Stub for lean_string_append");
10-}
11-

./src/rust/lean_runtime/src/lean_imports_rs/Init/Data/String/Bootstrap.rs
28:pub fn lean_string_append(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
29:    todo!("Stub for lean_string_append");
30-}
31-
32-pub fn lean_string_utf8_next(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
```

we should move

./src/rust/lean_runtime/src/runtime_object_string.rs
331:    pub(crate) unsafe fn lean_string_append(
332-        s1: *mut LeanObject,
333-        s2: *mut LeanObject,
334-    ) -> *mut LeanObject {

to

./src/rust/lean_runtime/src/lean_imports_rs/Init/Data/String/Defs.rs
8:pub fn lean_string_append(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
9:    todo!("Stub for lean_string_append");
10-}
11-

and then ./src/Init/Data/String/Bootstrap.lean will just reexport from ./src/rust/lean_runtime/src/lean_imports_rs/Init/Data/String/Defs.rs (or , if will be circular deps - define in ./src/rust/lean_runtime/src/lean_imports_rs/Init/Data/String/Defs.rs and reexport from ./src/Init/Data/String/Bootstrap.lean OR if still - defined this function at separate file at all)
