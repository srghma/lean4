# what funcs are used in EmitRust

## 1. In rust and are **used** in EmitC

* `lean_alloc_closure` 🦀 -- used (line 666)
* `lean_alloc_ctor` 🦀 -- used (lines 573, 1028)
* `lean_apply_1` 🦀 -- used (line 680, generated dynamically inside `emitAp` as `"lean_apply_1"`)
* `lean_apply_2` 🦀 -- used (line 680, generated dynamically inside `emitAp` as `"lean_apply_2"`)
* `lean_apply_3` 🦀 -- used (line 680, generated dynamically inside `emitAp` as `"lean_apply_3"`)
* `lean_apply_4` 🦀 -- used (line 680, generated dynamically inside `emitAp` as `"lean_apply_4"`)
* `lean_apply_m` 🦀 -- used (line 677)
* `lean_box` 🦀 -- used (lines 62, 166, 582, 596, 710, 955, 965, 983, 1023)
* `lean_box_float` 🦀 -- used (line 60)
* `lean_box_float32` 🦀 -- used (line 61)
* `lean_box_uint32` 🦀 -- used (line 58)
* `lean_box_uint64` 🦀 -- used (line 59)
* `lean_box_usize` 🦀 -- used (line 57)
* `lean_closure_set` 🦀 -- used (line 669)
* `lean_cstr_to_nat` 🦀 -- used (line 704)
* `lean_ctor_get` 🦀 -- used (line 612)
* `lean_ctor_get_float` 🦀 -- used (line 66)
* `lean_ctor_get_float32` 🦀 -- used (line 67)
* `lean_ctor_get_uint8` 🦀 -- used (line 68)
* `lean_ctor_get_uint16` 🦀 -- used (line 69)
* `lean_ctor_get_uint32` 🦀 -- used (line 70)
* `lean_ctor_get_uint64` 🦀 -- used (line 71)
* `lean_ctor_get_usize` 🦀 -- used (line 616)
* `lean_ctor_release` 🦀 -- used (line 591)
* `lean_ctor_set` 🦀 -- used (lines 578, 802, 1028)
* `lean_ctor_set_float` 🦀 -- used (line 76)
* `lean_ctor_set_float32` 🦀 -- used (line 77)
* `lean_ctor_set_tag` 🦀 -- used (lines 607, 798)
* `lean_ctor_set_uint16` 🦀 -- used (line 79)
* `lean_ctor_set_uint32` 🦀 -- used (line 80)
* `lean_ctor_set_uint64` 🦀 -- used (line 81)
* `lean_ctor_set_uint8` 🦀 -- used (line 78)
* `lean_ctor_set_usize` 🦀 -- used (line 806)
* `lean_dec` 🦀 -- used (line 789)
* `lean_dec_ref` 🦀 -- used (lines 595, 789, 923, 934, 961, 989, 992, 995, 1048, 1063, 1067)
* `lean_dec_ref_known` 🦀 -- used (line 787)
* `lean_del_object` 🦀 -- used (line 794)
* `lean_float_once` 🦀 -- used (line 86)
* `lean_float32_once` 🦀 -- used (line 87)
* `lean_inc` 🦀 -- used (line 775)
* `lean_inc_n` 🦀 -- used (line 778)
* `lean_inc_ref` 🦀 -- used (line 775)
* `lean_inc_ref_n` 🦀 -- used (line 778)
* `lean_io_result_is_error` 🦀 -- used (line 912)
* `lean_io_result_mk_ok` 🦀 -- used (lines 955, 965, 983)
* `lean_is_exclusive` 🦀 -- used (lines 588, 692)
* `lean_is_scalar` 🦀 -- used (line 600)
* `lean_mark_persistent` 🦀 -- used (lines 916, 933, 937)
* `lean_mk_string_unchecked` 🦀 -- used (line 706)
* `lean_obj_once` 🦀 -- used (line 93)
* `lean_obj_tag` 🦀 -- used (line 823)
* `lean_uint16_once` 🦀 -- used (line 89)
* `lean_uint32_once` 🦀 -- used (line 90)
* `lean_uint64_once` 🦀 -- used (line 91)
* `lean_uint8_once` 🦀 -- used (line 88)
* `lean_unbox` 🦀 -- used (line 53)
* `lean_unbox_float` 🦀 -- used (line 51)
* `lean_unbox_float32` 🦀 -- used (line 52)
* `lean_unbox_uint32` 🦀 -- used (lines 49, 1062)
* `lean_unbox_uint64` 🦀 -- used (line 50)
* `lean_unbox_usize` 🦀 -- used (line 48)
* `lean_unsigned_to_nat` 🦀 -- used (line 702)
* `lean_usize_once` 🦀 -- used (line 92)

## 2. Not in rust but in EmitC

* `# lean_io_result_get_value` 🦀 -- used (lines 930, 932, 1062)
* `# lean_setup_args` 🦀 -- used (lines 1014, 1043) [❌ NOT DEFINED IN original LEAN.H]
* `# lean_initialize` 🦀 -- used (lines 1015, 1044) [❌ NOT DEFINED IN original LEAN.H]
* `# lean_initialize_runtime_module` 🦀 -- used (lines 1015, 1044) [❌ NOT DEFINED IN original LEAN.H]
* `# lean_mk_string` 🦀 -- used (line 1028)
* `# lean_io_mark_end_initialization` 🦀 -- used (line 1046)
* `# lean_io_result_is_ok` 🦀 -- used (lines 1047, 1061)
* `# lean_init_task_manager` 🦀 -- used (line 1049)
* `# lean_run_main` 🦀 -- used (line 1050)
* `# lean_finalize_task_manager` 🦀 -- used (line 1060)
* `# lean_io_result_show_error` 🦀 -- used (line 1066)
* `# lean_internal_panic_unreachable` -- used (line 848) *(Note: EmitRust uses native `core::hint::unreachable_unchecked();` instead)*

### Runtime C Types and Macros Used

* `# _lean_main` -- used (lines 27, 1032, 1034) [❌ NOT DEFINED IN original LEAN.H] *(Note: compiler uses `leanMainFn := "_lean_main"`, which generates this identifier)*
* `# lean_once_cell_t` -- used (line 482) *(Note: Rust uses `LeanOnceCell` type instead)*
* `# LEAN_ONCE_CELL_INITIALIZER` -- used (line 482) *(Note: Rust uses structural initialization instead)*
* `# LEAN_SCALAR_PTR_LITERAL` -- used (line 432) *(Note: Rust implements this behavior natively inside the `scalarPtrLiteral` function)*
* `# lean_ctor_object` -- used (lines 322, 345, 392, 439) *(Note: Rust uses `LeanCtorObject` type instead)*
* `# lean_string_object` -- used (line 330) *(Note: Rust uses `LeanStringObject` type instead)*
* `# lean_closure_object` -- used (lines 335, 341) *(Note: Rust uses `LeanClosureObject` type instead)*
* `# lean_array_object` -- used (lines 348, 352) *(Note: Rust uses `LeanArrayObject` type instead)*
* `# lean_sarray_object` -- used (lines 357, 361) *(Note: Rust uses `LeanScalarArrayObject` type instead)*

## 3. In rust but not in EmitC

* `lean_alloc_external`
* `lean_dec_ref_cold`
* `lean_finalize_external_classes` [❌ NOT DEFINED IN original LEAN.H]
* `lean_free_object`
* `lean_get_external_class`
* `lean_is_array`
* `lean_is_closure`
* `lean_is_ctor`
* `lean_is_external`
* `lean_is_mpz`
* `lean_is_mt`
* `lean_is_persistent`
* `lean_is_promise`
* `lean_is_sarray`
* `lean_is_shared` *(Note: `emitIsShared` on line 690 uses `lean_is_exclusive` instead)*
* `lean_is_string`
* `lean_is_task`
* `lean_is_thunk`
* `lean_name_eq_export` [❌ NOT DEFINED IN original LEAN.H] (only lean_name_eq is present)
* `lean_ptr_other`
* `lean_register_external_class`
* `lean_runtime_alloc_external` [❌ NOT DEFINED IN original LEAN.H] (only lean_alloc_external is present)
* `lean_runtime_get_external_data` [❌ NOT DEFINED IN original LEAN.H] (only lean_get_external_data is present)
* `lean_set_external_data`
* `lean_to_array`
* `lean_to_closure`
* `lean_to_ctor`
* `lean_to_external`
* `lean_to_promise`
* `lean_to_ref`
* `lean_to_sarray`
* `lean_to_string`
* `lean_to_task`
* `lean_to_thunk`
