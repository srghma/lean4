// Lean compiler output
// Module: test_rc
// Imports: public import Init public meta import Init
#include <lean/lean.h>

#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
  #endif
  lean_object * lean_mk_empty_array_with_capacity(lean_object * );
  lean_object * lean_array_push(lean_object * , lean_object * );
  lean_object * lean_nat_add(lean_object * , lean_object * );
  lean_object * l_Array_append___redArg(lean_object * , lean_object * );
  static
  const lean_array_object l_test1___closed__0_value = {
    .m_header = {
      .m_rc = 0,
      .m_cs_sz = sizeof(lean_array_object) + sizeof(void * ) * 0,
      .m_other = 0,
      .m_tag = 246
    },
    .m_size = 0,
    .m_capacity = 0,
    .m_data = {}
  };
  static
  const lean_object * l_test1___closed__0 = (const lean_object * ) & l_test1___closed__0_value;
  LEAN_EXPORT lean_object * l_test1(lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_test2(lean_object * , lean_object * );
  LEAN_EXPORT lean_object * l_test1(lean_object * v_x_3_, lean_object * v_y_4_) {
    _start: {
      lean_object * v___x_5_;lean_object * v___x_6_;lean_object * v___x_7_;
      v___x_5_ = ((lean_object * )(l_test1___closed__0));
      v___x_6_ = lean_array_push(v___x_5_, v_x_3_);
      v___x_7_ = lean_array_push(v___x_6_, v_y_4_);
      return v___x_7_;
    }
  }
  LEAN_EXPORT lean_object * l_test2(lean_object * v_x_8_, lean_object * v_y_9_) {
    _start: {
      lean_object * v___x_10_;lean_object * v_init_11_;lean_object * v_a_12_;lean_object * v___x_13_;lean_object * v___x_14_;lean_object * v_b_15_;lean_object * v___x_16_;
      v___x_10_ = ((lean_object * )(l_test1___closed__0));
      v_init_11_ = lean_array_push(v___x_10_, v_x_8_);
      lean_inc(v_y_9_);
      lean_inc_ref(v_init_11_);
      v_a_12_ = lean_array_push(v_init_11_, v_y_9_);
      v___x_13_ = lean_unsigned_to_nat(1u);
      v___x_14_ = lean_nat_add(v_y_9_, v___x_13_);
      lean_dec(v_y_9_);
      v_b_15_ = lean_array_push(v_init_11_, v___x_14_);
      v___x_16_ = l_Array_append___redArg(v_a_12_, v_b_15_);
      lean_dec_ref(v_b_15_);
      return v___x_16_;
    }
  }
  lean_object * initialize_Init(uint8_t builtin);
  lean_object * initialize_Init(uint8_t builtin);
  static bool _G_initialized = false;
  LEAN_EXPORT lean_object * initialize_test__rc(uint8_t builtin) {
    lean_object * res;
    if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
    _G_initialized = true;
    res = initialize_Init(builtin);
    if (lean_io_result_is_error(res)) return res;
    lean_dec_ref(res);
    res = initialize_Init(builtin);
    if (lean_io_result_is_error(res)) return res;
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
  }
  #ifdef __cplusplus
}
#endif
