// Lean compiler output
// Module: Lean.Kernel.EquivManager
// Imports: public import Lean.Kernel.PtrEq
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_ptrEqExpr(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static const lean_array_object l_Lean_Kernel_EquivManager_instInhabitedUnionFind_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Kernel_EquivManager_instInhabitedUnionFind_default___closed__0 = (const lean_object*)&l_Lean_Kernel_EquivManager_instInhabitedUnionFind_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Kernel_EquivManager_instInhabitedUnionFind_default = (const lean_object*)&l_Lean_Kernel_EquivManager_instInhabitedUnionFind_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Kernel_EquivManager_instInhabitedUnionFind = (const lean_object*)&l_Lean_Kernel_EquivManager_instInhabitedUnionFind_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_push(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_root(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_root___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_union(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_union___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_merge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_merge___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_toNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Kernel_EquivManager_isEquiv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Kernel_EquivManager_isEquiv_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_isEquiv(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_isEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_addEquiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_size(lean_object* v_uf_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_array_get_size(v_uf_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_size___boxed(lean_object* v_uf_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Kernel_EquivManager_UnionFind_size(v_uf_7_);
lean_dec_ref(v_uf_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_push(lean_object* v_uf_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_array_get_size(v_uf_9_);
v___x_11_ = lean_array_push(v_uf_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_root(lean_object* v_uf_12_, lean_object* v_n_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_array_get_size(v_uf_12_);
v___x_15_ = lean_nat_dec_lt(v_n_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_inc(v_n_13_);
return v_n_13_;
}
else
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_array_fget_borrowed(v_uf_12_, v_n_13_);
v___x_17_ = lean_nat_dec_eq(v___x_16_, v_n_13_);
if (v___x_17_ == 0)
{
v_n_13_ = v___x_16_;
goto _start;
}
else
{
lean_inc(v_n_13_);
return v_n_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_root___boxed(lean_object* v_uf_19_, lean_object* v_n_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Kernel_EquivManager_UnionFind_root(v_uf_19_, v_n_20_);
lean_dec(v_n_20_);
lean_dec_ref(v_uf_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_union(lean_object* v_uf_22_, lean_object* v_n_u2081_23_, lean_object* v_n_u2082_24_){
_start:
{
lean_object* v_r_u2081_25_; lean_object* v_r_u2082_26_; uint8_t v___x_27_; 
v_r_u2081_25_ = l_Lean_Kernel_EquivManager_UnionFind_root(v_uf_22_, v_n_u2081_23_);
v_r_u2082_26_ = l_Lean_Kernel_EquivManager_UnionFind_root(v_uf_22_, v_n_u2082_24_);
v___x_27_ = lean_nat_dec_eq(v_r_u2081_25_, v_r_u2082_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_array_get_size(v_uf_22_);
v___x_29_ = lean_nat_dec_lt(v_r_u2081_25_, v___x_28_);
if (v___x_29_ == 0)
{
lean_dec(v_r_u2082_26_);
lean_dec(v_r_u2081_25_);
return v_uf_22_;
}
else
{
lean_object* v___x_30_; 
v___x_30_ = lean_array_fset(v_uf_22_, v_r_u2081_25_, v_r_u2082_26_);
lean_dec(v_r_u2081_25_);
return v___x_30_;
}
}
else
{
lean_dec(v_r_u2082_26_);
lean_dec(v_r_u2081_25_);
return v_uf_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_UnionFind_union___boxed(lean_object* v_uf_31_, lean_object* v_n_u2081_32_, lean_object* v_n_u2082_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Kernel_EquivManager_UnionFind_union(v_uf_31_, v_n_u2081_32_, v_n_u2082_33_);
lean_dec(v_n_u2082_33_);
lean_dec(v_n_u2081_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_find(lean_object* v_n_35_, lean_object* v_m_36_){
_start:
{
lean_object* v_uf_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_uf_37_ = lean_ctor_get(v_m_36_, 0);
v___x_38_ = l_Lean_Kernel_EquivManager_UnionFind_root(v_uf_37_, v_n_35_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v_m_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_find___boxed(lean_object* v_n_40_, lean_object* v_m_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Kernel_EquivManager_find(v_n_40_, v_m_41_);
lean_dec(v_n_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_merge(lean_object* v_m_43_, lean_object* v_n1_44_, lean_object* v_n2_45_){
_start:
{
lean_object* v_uf_46_; lean_object* v_toNodeMap_47_; uint8_t v___y_49_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_uf_46_ = lean_ctor_get(v_m_43_, 0);
v_toNodeMap_47_ = lean_ctor_get(v_m_43_, 1);
v___x_60_ = lean_array_get_size(v_uf_46_);
v___x_61_ = lean_nat_dec_lt(v_n1_44_, v___x_60_);
if (v___x_61_ == 0)
{
v___y_49_ = v___x_61_;
goto v___jp_48_;
}
else
{
uint8_t v___x_62_; 
v___x_62_ = lean_nat_dec_lt(v_n2_45_, v___x_60_);
v___y_49_ = v___x_62_;
goto v___jp_48_;
}
v___jp_48_:
{
if (v___y_49_ == 0)
{
return v_m_43_;
}
else
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
lean_inc_ref(v_toNodeMap_47_);
lean_inc_ref(v_uf_46_);
v_isSharedCheck_57_ = !lean_is_exclusive(v_m_43_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; lean_object* v_unused_59_; 
v_unused_58_ = lean_ctor_get(v_m_43_, 1);
lean_dec(v_unused_58_);
v_unused_59_ = lean_ctor_get(v_m_43_, 0);
lean_dec(v_unused_59_);
v___x_51_ = v_m_43_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_m_43_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = l_Lean_Kernel_EquivManager_UnionFind_union(v_uf_46_, v_n1_44_, v_n2_45_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_53_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_toNodeMap_47_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_merge___boxed(lean_object* v_m_63_, lean_object* v_n1_64_, lean_object* v_n2_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Kernel_EquivManager_merge(v_m_63_, v_n1_64_, v_n2_65_);
lean_dec(v_n2_65_);
lean_dec(v_n1_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg(lean_object* v_a_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v_key_70_; lean_object* v_value_71_; lean_object* v_tail_72_; uint8_t v___x_73_; 
v_key_70_ = lean_ctor_get(v_x_68_, 0);
v_value_71_ = lean_ctor_get(v_x_68_, 1);
v_tail_72_ = lean_ctor_get(v_x_68_, 2);
v___x_73_ = lean_expr_eqv(v_key_70_, v_a_67_);
if (v___x_73_ == 0)
{
v_x_68_ = v_tail_72_;
goto _start;
}
else
{
lean_object* v___x_75_; 
lean_inc(v_value_71_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v_value_71_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg___boxed(lean_object* v_a_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg(v_a_76_, v_x_77_);
lean_dec(v_x_77_);
lean_dec_ref(v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg(lean_object* v_m_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_buckets_81_; lean_object* v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v_fold_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_buckets_81_ = lean_ctor_get(v_m_79_, 1);
v___x_82_ = lean_array_get_size(v_buckets_81_);
v___x_83_ = l_Lean_Expr_hash(v_a_80_);
v___x_84_ = 32ULL;
v___x_85_ = lean_uint64_shift_right(v___x_83_, v___x_84_);
v_fold_86_ = lean_uint64_xor(v___x_83_, v___x_85_);
v___x_87_ = 16ULL;
v___x_88_ = lean_uint64_shift_right(v_fold_86_, v___x_87_);
v___x_89_ = lean_uint64_xor(v_fold_86_, v___x_88_);
v___x_90_ = lean_uint64_to_usize(v___x_89_);
v___x_91_ = lean_usize_of_nat(v___x_82_);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_sub(v___x_91_, v___x_92_);
v___x_94_ = lean_usize_land(v___x_90_, v___x_93_);
v___x_95_ = lean_array_uget_borrowed(v_buckets_81_, v___x_94_);
v___x_96_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg(v_a_80_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg___boxed(lean_object* v_m_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg(v_m_97_, v_a_98_);
lean_dec_ref(v_a_98_);
lean_dec_ref(v_m_97_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg(lean_object* v_a_100_, lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
else
{
lean_object* v_key_103_; lean_object* v_tail_104_; uint8_t v___x_105_; 
v_key_103_ = lean_ctor_get(v_x_101_, 0);
v_tail_104_ = lean_ctor_get(v_x_101_, 2);
v___x_105_ = lean_expr_eqv(v_key_103_, v_a_100_);
if (v___x_105_ == 0)
{
v_x_101_ = v_tail_104_;
goto _start;
}
else
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg___boxed(lean_object* v_a_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg(v_a_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec_ref(v_a_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4___redArg(lean_object* v_a_111_, lean_object* v_b_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_dec(v_b_112_);
lean_dec_ref(v_a_111_);
return v_x_113_;
}
else
{
lean_object* v_key_114_; lean_object* v_value_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_128_; 
v_key_114_ = lean_ctor_get(v_x_113_, 0);
v_value_115_ = lean_ctor_get(v_x_113_, 1);
v_tail_116_ = lean_ctor_get(v_x_113_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_128_ == 0)
{
v___x_118_ = v_x_113_;
v_isShared_119_ = v_isSharedCheck_128_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_value_115_);
lean_inc(v_key_114_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_128_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_expr_eqv(v_key_114_, v_a_111_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4___redArg(v_a_111_, v_b_112_, v_tail_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_key_114_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_value_115_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
else
{
lean_object* v___x_126_; 
lean_dec(v_value_115_);
lean_dec(v_key_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_b_112_);
lean_ctor_set(v___x_118_, 0, v_a_111_);
v___x_126_ = v___x_118_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_111_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_b_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_tail_116_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
return v_x_129_;
}
else
{
lean_object* v_key_131_; lean_object* v_value_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_156_; 
v_key_131_ = lean_ctor_get(v_x_130_, 0);
v_value_132_ = lean_ctor_get(v_x_130_, 1);
v_tail_133_ = lean_ctor_get(v_x_130_, 2);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_156_ == 0)
{
v___x_135_ = v_x_130_;
v_isShared_136_ = v_isSharedCheck_156_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_value_132_);
lean_inc(v_key_131_);
lean_dec(v_x_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_156_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_137_ = lean_array_get_size(v_x_129_);
v___x_138_ = l_Lean_Expr_hash(v_key_131_);
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___x_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___x_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_137_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v___x_150_ = lean_array_uget_borrowed(v_x_129_, v___x_149_);
lean_inc(v___x_150_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 2, v___x_150_);
v___x_152_ = v___x_135_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_key_131_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_value_132_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v___x_150_);
v___x_152_ = v_reuseFailAlloc_155_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_array_uset(v_x_129_, v___x_149_, v___x_152_);
v_x_129_ = v___x_153_;
v_x_130_ = v_tail_133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4___redArg(lean_object* v_i_157_, lean_object* v_source_158_, lean_object* v_target_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_array_get_size(v_source_158_);
v___x_161_ = lean_nat_dec_lt(v_i_157_, v___x_160_);
if (v___x_161_ == 0)
{
lean_dec_ref(v_source_158_);
lean_dec(v_i_157_);
return v_target_159_;
}
else
{
lean_object* v_es_162_; lean_object* v___x_163_; lean_object* v_source_164_; lean_object* v_target_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_es_162_ = lean_array_fget(v_source_158_, v_i_157_);
v___x_163_ = lean_box(0);
v_source_164_ = lean_array_fset(v_source_158_, v_i_157_, v___x_163_);
v_target_165_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4_spec__5___redArg(v_target_159_, v_es_162_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_i_157_, v___x_166_);
lean_dec(v_i_157_);
v_i_157_ = v___x_167_;
v_source_158_ = v_source_164_;
v_target_159_ = v_target_165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3___redArg(lean_object* v_data_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_nbuckets_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_170_ = lean_array_get_size(v_data_169_);
v___x_171_ = lean_unsigned_to_nat(2u);
v_nbuckets_172_ = lean_nat_mul(v___x_170_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_box(0);
v___x_175_ = lean_mk_array(v_nbuckets_172_, v___x_174_);
v___x_176_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4___redArg(v___x_173_, v_data_169_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1___redArg(lean_object* v_m_177_, lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_size_180_; lean_object* v_buckets_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_224_; 
v_size_180_ = lean_ctor_get(v_m_177_, 0);
v_buckets_181_ = lean_ctor_get(v_m_177_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_m_177_);
if (v_isSharedCheck_224_ == 0)
{
v___x_183_ = v_m_177_;
v_isShared_184_ = v_isSharedCheck_224_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_buckets_181_);
lean_inc(v_size_180_);
lean_dec(v_m_177_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_224_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v_fold_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v_bkt_198_; uint8_t v___x_199_; 
v___x_185_ = lean_array_get_size(v_buckets_181_);
v___x_186_ = l_Lean_Expr_hash(v_a_178_);
v___x_187_ = 32ULL;
v___x_188_ = lean_uint64_shift_right(v___x_186_, v___x_187_);
v_fold_189_ = lean_uint64_xor(v___x_186_, v___x_188_);
v___x_190_ = 16ULL;
v___x_191_ = lean_uint64_shift_right(v_fold_189_, v___x_190_);
v___x_192_ = lean_uint64_xor(v_fold_189_, v___x_191_);
v___x_193_ = lean_uint64_to_usize(v___x_192_);
v___x_194_ = lean_usize_of_nat(v___x_185_);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_sub(v___x_194_, v___x_195_);
v___x_197_ = lean_usize_land(v___x_193_, v___x_196_);
v_bkt_198_ = lean_array_uget_borrowed(v_buckets_181_, v___x_197_);
v___x_199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg(v_a_178_, v_bkt_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v_size_x27_201_; lean_object* v___x_202_; lean_object* v_buckets_x27_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_200_ = lean_unsigned_to_nat(1u);
v_size_x27_201_ = lean_nat_add(v_size_180_, v___x_200_);
lean_dec(v_size_180_);
lean_inc(v_bkt_198_);
v___x_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_202_, 0, v_a_178_);
lean_ctor_set(v___x_202_, 1, v_b_179_);
lean_ctor_set(v___x_202_, 2, v_bkt_198_);
v_buckets_x27_203_ = lean_array_uset(v_buckets_181_, v___x_197_, v___x_202_);
v___x_204_ = lean_unsigned_to_nat(4u);
v___x_205_ = lean_nat_mul(v_size_x27_201_, v___x_204_);
v___x_206_ = lean_unsigned_to_nat(3u);
v___x_207_ = lean_nat_div(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_array_get_size(v_buckets_x27_203_);
v___x_209_ = lean_nat_dec_le(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
if (v___x_209_ == 0)
{
lean_object* v_val_210_; lean_object* v___x_212_; 
v_val_210_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3___redArg(v_buckets_x27_203_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_val_210_);
lean_ctor_set(v___x_183_, 0, v_size_x27_201_);
v___x_212_ = v___x_183_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_size_x27_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_val_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
else
{
lean_object* v___x_215_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_buckets_x27_203_);
lean_ctor_set(v___x_183_, 0, v_size_x27_201_);
v___x_215_ = v___x_183_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_size_x27_201_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_buckets_x27_203_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v___x_217_; lean_object* v_buckets_x27_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
lean_inc(v_bkt_198_);
v___x_217_ = lean_box(0);
v_buckets_x27_218_ = lean_array_uset(v_buckets_181_, v___x_197_, v___x_217_);
v___x_219_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4___redArg(v_a_178_, v_b_179_, v_bkt_198_);
v___x_220_ = lean_array_uset(v_buckets_x27_218_, v___x_197_, v___x_219_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_220_);
v___x_222_ = v___x_183_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_size_180_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_toNode(lean_object* v_e_225_, lean_object* v_m_226_){
_start:
{
lean_object* v_uf_227_; lean_object* v_toNodeMap_228_; lean_object* v___x_229_; 
v_uf_227_ = lean_ctor_get(v_m_226_, 0);
v_toNodeMap_228_ = lean_ctor_get(v_m_226_, 1);
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg(v_toNodeMap_228_, v_e_225_);
if (lean_obj_tag(v___x_229_) == 1)
{
lean_object* v_val_230_; lean_object* v___x_231_; 
lean_dec_ref(v_e_225_);
v_val_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_val_230_);
lean_ctor_set(v___x_231_, 1, v_m_226_);
return v___x_231_;
}
else
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_242_; 
lean_inc_ref(v_toNodeMap_228_);
lean_inc_ref(v_uf_227_);
lean_dec(v___x_229_);
v_isSharedCheck_242_ = !lean_is_exclusive(v_m_226_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_243_ = lean_ctor_get(v_m_226_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_m_226_, 0);
lean_dec(v_unused_244_);
v___x_233_ = v_m_226_;
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_m_226_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_r_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v_r_235_ = lean_array_get_size(v_uf_227_);
v___x_236_ = l_Lean_Kernel_EquivManager_UnionFind_push(v_uf_227_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1___redArg(v_toNodeMap_228_, v_e_225_, v_r_235_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_237_);
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_r_235_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0(lean_object* v_00_u03b2_245_, lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___redArg(v_m_246_, v_a_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0___boxed(lean_object* v_00_u03b2_249_, lean_object* v_m_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0(v_00_u03b2_249_, v_m_250_, v_a_251_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_m_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1(lean_object* v_00_u03b2_253_, lean_object* v_m_254_, lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1___redArg(v_m_254_, v_a_255_, v_b_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0(lean_object* v_00_u03b2_258_, lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___redArg(v_a_259_, v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0___boxed(lean_object* v_00_u03b2_262_, lean_object* v_a_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Kernel_EquivManager_toNode_spec__0_spec__0(v_00_u03b2_262_, v_a_263_, v_x_264_);
lean_dec(v_x_264_);
lean_dec_ref(v_a_263_);
return v_res_265_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2(lean_object* v_00_u03b2_266_, lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___redArg(v_a_267_, v_x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2___boxed(lean_object* v_00_u03b2_270_, lean_object* v_a_271_, lean_object* v_x_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__2(v_00_u03b2_270_, v_a_271_, v_x_272_);
lean_dec(v_x_272_);
lean_dec_ref(v_a_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3(lean_object* v_00_u03b2_275_, lean_object* v_data_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3___redArg(v_data_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4(lean_object* v_00_u03b2_278_, lean_object* v_a_279_, lean_object* v_b_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__4___redArg(v_a_279_, v_b_280_, v_x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_283_, lean_object* v_i_284_, lean_object* v_source_285_, lean_object* v_target_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4___redArg(v_i_284_, v_source_285_, v_target_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Kernel_EquivManager_toNode_spec__1_spec__3_spec__4_spec__5___redArg(v_x_289_, v_x_290_);
return v___x_291_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Kernel_EquivManager_isEquiv_spec__0(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
if (lean_obj_tag(v_x_293_) == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 1;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
else
{
if (lean_obj_tag(v_x_293_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
else
{
lean_object* v_head_297_; lean_object* v_tail_298_; lean_object* v_head_299_; lean_object* v_tail_300_; uint8_t v___x_301_; 
v_head_297_ = lean_ctor_get(v_x_292_, 0);
v_tail_298_ = lean_ctor_get(v_x_292_, 1);
v_head_299_ = lean_ctor_get(v_x_293_, 0);
v_tail_300_ = lean_ctor_get(v_x_293_, 1);
v___x_301_ = lean_level_eq(v_head_297_, v_head_299_);
if (v___x_301_ == 0)
{
return v___x_301_;
}
else
{
v_x_292_ = v_tail_298_;
v_x_293_ = v_tail_300_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Kernel_EquivManager_isEquiv_spec__0___boxed(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_List_beq___at___00Lean_Kernel_EquivManager_isEquiv_spec__0(v_x_303_, v_x_304_);
lean_dec(v_x_304_);
lean_dec(v_x_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_isEquiv(uint8_t v_useHash_307_, lean_object* v_e1_308_, lean_object* v_e2_309_, lean_object* v_a_310_){
_start:
{
lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v_result_314_; lean_object* v___y_315_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v_d1_331_; lean_object* v_b1_332_; lean_object* v_d2_333_; lean_object* v_b2_334_; lean_object* v___y_335_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___x_355_; uint8_t v___x_356_; uint8_t v___y_358_; 
v___x_355_ = l_Lean_Kernel_ptrEqExpr(v_e1_308_, v_e2_309_);
v___x_356_ = 1;
if (v___x_355_ == 0)
{
if (v_useHash_307_ == 0)
{
goto v___jp_498_;
}
else
{
uint64_t v___x_501_; uint64_t v___x_502_; uint8_t v___x_503_; 
v___x_501_ = l_Lean_Expr_hash(v_e1_308_);
v___x_502_ = l_Lean_Expr_hash(v_e2_309_);
v___x_503_ = lean_uint64_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v_e2_309_);
lean_dec_ref(v_e1_308_);
v___x_504_ = lean_box(v___x_355_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_a_310_);
return v___x_505_;
}
else
{
if (v___x_355_ == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v_e2_309_);
lean_dec_ref(v_e1_308_);
v___x_506_ = lean_box(v___x_355_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_a_310_);
return v___x_507_;
}
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref(v_e2_309_);
lean_dec_ref(v_e1_308_);
v___x_508_ = lean_box(v___x_356_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_310_);
return v___x_509_;
}
v___jp_311_:
{
if (v_result_314_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v___y_313_);
lean_dec(v___y_312_);
v___x_316_ = lean_box(v_result_314_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___y_315_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = l_Lean_Kernel_EquivManager_merge(v___y_315_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec(v___y_312_);
v___x_319_ = lean_box(v_result_314_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
return v___x_320_;
}
}
v___jp_321_:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; uint8_t v___x_327_; 
v_fst_325_ = lean_ctor_get(v___y_324_, 0);
lean_inc(v_fst_325_);
v_snd_326_ = lean_ctor_get(v___y_324_, 1);
lean_inc(v_snd_326_);
lean_dec_ref(v___y_324_);
v___x_327_ = lean_unbox(v_fst_325_);
lean_dec(v_fst_325_);
v___y_312_ = v___y_322_;
v___y_313_ = v___y_323_;
v_result_314_ = v___x_327_;
v___y_315_ = v_snd_326_;
goto v___jp_311_;
}
v___jp_328_:
{
lean_object* v___x_336_; lean_object* v_fst_337_; uint8_t v___x_338_; 
v___x_336_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_d1_331_, v_d2_333_, v___y_335_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_fst_337_);
v___x_338_ = lean_unbox(v_fst_337_);
lean_dec(v_fst_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_b2_334_);
lean_dec_ref(v_b1_332_);
v___y_322_ = v___y_329_;
v___y_323_ = v___y_330_;
v___y_324_ = v___x_336_;
goto v___jp_321_;
}
else
{
lean_object* v_snd_339_; lean_object* v___x_340_; 
v_snd_339_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_snd_339_);
lean_dec_ref(v___x_336_);
v___x_340_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_b1_332_, v_b2_334_, v_snd_339_);
v___y_322_ = v___y_329_;
v___y_323_ = v___y_330_;
v___y_324_ = v___x_340_;
goto v___jp_321_;
}
}
v___jp_341_:
{
lean_object* v_fst_345_; lean_object* v_snd_346_; uint8_t v___x_347_; 
v_fst_345_ = lean_ctor_get(v___y_344_, 0);
lean_inc(v_fst_345_);
v_snd_346_ = lean_ctor_get(v___y_344_, 1);
lean_inc(v_snd_346_);
lean_dec_ref(v___y_344_);
v___x_347_ = lean_unbox(v_fst_345_);
lean_dec(v_fst_345_);
v___y_312_ = v___y_342_;
v___y_313_ = v___y_343_;
v_result_314_ = v___x_347_;
v___y_315_ = v_snd_346_;
goto v___jp_311_;
}
v___jp_348_:
{
lean_object* v_fst_352_; lean_object* v_snd_353_; uint8_t v___x_354_; 
v_fst_352_ = lean_ctor_get(v___y_351_, 0);
lean_inc(v_fst_352_);
v_snd_353_ = lean_ctor_get(v___y_351_, 1);
lean_inc(v_snd_353_);
lean_dec_ref(v___y_351_);
v___x_354_ = lean_unbox(v_fst_352_);
lean_dec(v_fst_352_);
v___y_312_ = v___y_349_;
v___y_313_ = v___y_350_;
v_result_314_ = v___x_354_;
v___y_315_ = v_snd_353_;
goto v___jp_311_;
}
v___jp_357_:
{
if (v___y_358_ == 0)
{
lean_object* v___x_359_; lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v___x_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___x_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_492_; 
lean_inc_ref(v_e1_308_);
v___x_359_ = l_Lean_Kernel_EquivManager_toNode(v_e1_308_, v_a_310_);
v_fst_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_fst_360_);
v_snd_361_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_snd_361_);
lean_dec_ref(v___x_359_);
v___x_362_ = l_Lean_Kernel_EquivManager_find(v_fst_360_, v_snd_361_);
lean_dec(v_fst_360_);
v_fst_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_fst_363_);
v_snd_364_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_snd_364_);
lean_dec_ref(v___x_362_);
lean_inc_ref(v_e2_309_);
v___x_365_ = l_Lean_Kernel_EquivManager_toNode(v_e2_309_, v_snd_364_);
v_fst_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v___x_365_, 1);
lean_inc(v_snd_367_);
lean_dec_ref(v___x_365_);
v___x_368_ = l_Lean_Kernel_EquivManager_find(v_fst_366_, v_snd_367_);
lean_dec(v_fst_366_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
v_snd_370_ = lean_ctor_get(v___x_368_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_492_ == 0)
{
v___x_372_ = v___x_368_;
v_isShared_373_ = v_isSharedCheck_492_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_inc(v_fst_369_);
lean_dec(v___x_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_492_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_eq(v_fst_363_, v_fst_369_);
if (v___x_374_ == 0)
{
switch(lean_obj_tag(v_e1_308_))
{
case 4:
{
if (lean_obj_tag(v_e2_309_) == 4)
{
lean_object* v_declName_375_; lean_object* v_us_376_; lean_object* v_declName_377_; lean_object* v_us_378_; uint8_t v___x_379_; 
lean_del_object(v___x_372_);
v_declName_375_ = lean_ctor_get(v_e1_308_, 0);
lean_inc(v_declName_375_);
v_us_376_ = lean_ctor_get(v_e1_308_, 1);
lean_inc(v_us_376_);
lean_dec_ref(v_e1_308_);
v_declName_377_ = lean_ctor_get(v_e2_309_, 0);
lean_inc(v_declName_377_);
v_us_378_ = lean_ctor_get(v_e2_309_, 1);
lean_inc(v_us_378_);
lean_dec_ref(v_e2_309_);
v___x_379_ = lean_name_eq(v_declName_375_, v_declName_377_);
lean_dec(v_declName_377_);
lean_dec(v_declName_375_);
if (v___x_379_ == 0)
{
lean_dec(v_us_378_);
lean_dec(v_us_376_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_379_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = l_List_beq___at___00Lean_Kernel_EquivManager_isEquiv_spec__0(v_us_376_, v_us_378_);
lean_dec(v_us_378_);
lean_dec(v_us_376_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_380_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_381_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_381_);
v___x_383_ = v___x_372_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_snd_370_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
case 2:
{
if (lean_obj_tag(v_e2_309_) == 2)
{
lean_object* v_mvarId_385_; lean_object* v_mvarId_386_; uint8_t v___x_387_; 
lean_del_object(v___x_372_);
v_mvarId_385_ = lean_ctor_get(v_e1_308_, 0);
lean_inc(v_mvarId_385_);
lean_dec_ref(v_e1_308_);
v_mvarId_386_ = lean_ctor_get(v_e2_309_, 0);
lean_inc(v_mvarId_386_);
lean_dec_ref(v_e2_309_);
v___x_387_ = l_Lean_instBEqMVarId_beq(v_mvarId_385_, v_mvarId_386_);
lean_dec(v_mvarId_386_);
lean_dec(v_mvarId_385_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_387_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_388_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_388_);
v___x_390_ = v___x_372_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_snd_370_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
case 1:
{
if (lean_obj_tag(v_e2_309_) == 1)
{
lean_object* v_fvarId_392_; lean_object* v_fvarId_393_; uint8_t v___x_394_; 
lean_del_object(v___x_372_);
v_fvarId_392_ = lean_ctor_get(v_e1_308_, 0);
lean_inc(v_fvarId_392_);
lean_dec_ref(v_e1_308_);
v_fvarId_393_ = lean_ctor_get(v_e2_309_, 0);
lean_inc(v_fvarId_393_);
lean_dec_ref(v_e2_309_);
v___x_394_ = l_Lean_instBEqFVarId_beq(v_fvarId_392_, v_fvarId_393_);
lean_dec(v_fvarId_393_);
lean_dec(v_fvarId_392_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_394_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_395_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_395_);
v___x_397_ = v___x_372_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_snd_370_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
case 3:
{
if (lean_obj_tag(v_e2_309_) == 3)
{
lean_object* v_u_399_; lean_object* v_u_400_; uint8_t v___x_401_; 
lean_del_object(v___x_372_);
v_u_399_ = lean_ctor_get(v_e1_308_, 0);
lean_inc(v_u_399_);
lean_dec_ref(v_e1_308_);
v_u_400_ = lean_ctor_get(v_e2_309_, 0);
lean_inc(v_u_400_);
lean_dec_ref(v_e2_309_);
v___x_401_ = lean_level_eq(v_u_399_, v_u_400_);
lean_dec(v_u_400_);
lean_dec(v_u_399_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_401_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_402_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_402_);
v___x_404_ = v___x_372_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_snd_370_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
case 9:
{
if (lean_obj_tag(v_e2_309_) == 9)
{
lean_object* v_a_406_; lean_object* v_a_407_; uint8_t v___x_408_; 
lean_del_object(v___x_372_);
v_a_406_ = lean_ctor_get(v_e1_308_, 0);
lean_inc_ref(v_a_406_);
lean_dec_ref(v_e1_308_);
v_a_407_ = lean_ctor_get(v_e2_309_, 0);
lean_inc_ref(v_a_407_);
lean_dec_ref(v_e2_309_);
v___x_408_ = l_Lean_instBEqLiteral_beq(v_a_406_, v_a_407_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_a_406_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_408_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_409_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_409_);
v___x_411_ = v___x_372_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_snd_370_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
case 5:
{
if (lean_obj_tag(v_e2_309_) == 5)
{
lean_object* v_fn_413_; lean_object* v_arg_414_; lean_object* v_fn_415_; lean_object* v_arg_416_; lean_object* v___x_417_; lean_object* v_fst_418_; uint8_t v___x_419_; 
lean_del_object(v___x_372_);
v_fn_413_ = lean_ctor_get(v_e1_308_, 0);
lean_inc_ref(v_fn_413_);
v_arg_414_ = lean_ctor_get(v_e1_308_, 1);
lean_inc_ref(v_arg_414_);
lean_dec_ref(v_e1_308_);
v_fn_415_ = lean_ctor_get(v_e2_309_, 0);
lean_inc_ref(v_fn_415_);
v_arg_416_ = lean_ctor_get(v_e2_309_, 1);
lean_inc_ref(v_arg_416_);
lean_dec_ref(v_e2_309_);
v___x_417_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_fn_413_, v_fn_415_, v_snd_370_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_fst_418_);
v___x_419_ = lean_unbox(v_fst_418_);
lean_dec(v_fst_418_);
if (v___x_419_ == 0)
{
lean_dec_ref(v_arg_416_);
lean_dec_ref(v_arg_414_);
v___y_342_ = v_fst_363_;
v___y_343_ = v_fst_369_;
v___y_344_ = v___x_417_;
goto v___jp_341_;
}
else
{
lean_object* v_snd_420_; lean_object* v___x_421_; 
v_snd_420_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_snd_420_);
lean_dec_ref(v___x_417_);
v___x_421_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_arg_414_, v_arg_416_, v_snd_420_);
v___y_342_ = v_fst_363_;
v___y_343_ = v_fst_369_;
v___y_344_ = v___x_421_;
goto v___jp_341_;
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_422_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_422_);
v___x_424_ = v___x_372_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_snd_370_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
case 6:
{
if (lean_obj_tag(v_e2_309_) == 6)
{
lean_object* v_binderType_426_; lean_object* v_body_427_; lean_object* v_binderType_428_; lean_object* v_body_429_; 
lean_del_object(v___x_372_);
v_binderType_426_ = lean_ctor_get(v_e1_308_, 1);
lean_inc_ref(v_binderType_426_);
v_body_427_ = lean_ctor_get(v_e1_308_, 2);
lean_inc_ref(v_body_427_);
lean_dec_ref(v_e1_308_);
v_binderType_428_ = lean_ctor_get(v_e2_309_, 1);
lean_inc_ref(v_binderType_428_);
v_body_429_ = lean_ctor_get(v_e2_309_, 2);
lean_inc_ref(v_body_429_);
lean_dec_ref(v_e2_309_);
v___y_329_ = v_fst_363_;
v___y_330_ = v_fst_369_;
v_d1_331_ = v_binderType_426_;
v_b1_332_ = v_body_427_;
v_d2_333_ = v_binderType_428_;
v_b2_334_ = v_body_429_;
v___y_335_ = v_snd_370_;
goto v___jp_328_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_430_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_430_);
v___x_432_ = v___x_372_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_snd_370_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
case 10:
{
if (lean_obj_tag(v_e2_309_) == 10)
{
lean_object* v_expr_434_; lean_object* v_expr_435_; lean_object* v___x_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; uint8_t v___x_439_; 
lean_del_object(v___x_372_);
v_expr_434_ = lean_ctor_get(v_e1_308_, 1);
lean_inc_ref(v_expr_434_);
lean_dec_ref(v_e1_308_);
v_expr_435_ = lean_ctor_get(v_e2_309_, 1);
lean_inc_ref(v_expr_435_);
lean_dec_ref(v_e2_309_);
v___x_436_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_expr_434_, v_expr_435_, v_snd_370_);
v_fst_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_438_);
lean_dec_ref(v___x_436_);
v___x_439_ = lean_unbox(v_fst_437_);
lean_dec(v_fst_437_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_439_;
v___y_315_ = v_snd_438_;
goto v___jp_311_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_440_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_440_);
v___x_442_ = v___x_372_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_snd_370_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
case 7:
{
if (lean_obj_tag(v_e2_309_) == 7)
{
lean_object* v_binderType_444_; lean_object* v_body_445_; lean_object* v_binderType_446_; lean_object* v_body_447_; 
lean_del_object(v___x_372_);
v_binderType_444_ = lean_ctor_get(v_e1_308_, 1);
lean_inc_ref(v_binderType_444_);
v_body_445_ = lean_ctor_get(v_e1_308_, 2);
lean_inc_ref(v_body_445_);
lean_dec_ref(v_e1_308_);
v_binderType_446_ = lean_ctor_get(v_e2_309_, 1);
lean_inc_ref(v_binderType_446_);
v_body_447_ = lean_ctor_get(v_e2_309_, 2);
lean_inc_ref(v_body_447_);
lean_dec_ref(v_e2_309_);
v___y_329_ = v_fst_363_;
v___y_330_ = v_fst_369_;
v_d1_331_ = v_binderType_444_;
v_b1_332_ = v_body_445_;
v_d2_333_ = v_binderType_446_;
v_b2_334_ = v_body_447_;
v___y_335_ = v_snd_370_;
goto v___jp_328_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_448_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_448_);
v___x_450_ = v___x_372_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_370_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
case 11:
{
if (lean_obj_tag(v_e2_309_) == 11)
{
lean_object* v_idx_452_; lean_object* v_struct_453_; lean_object* v_idx_454_; lean_object* v_struct_455_; uint8_t v___x_456_; 
lean_del_object(v___x_372_);
v_idx_452_ = lean_ctor_get(v_e1_308_, 1);
lean_inc(v_idx_452_);
v_struct_453_ = lean_ctor_get(v_e1_308_, 2);
lean_inc_ref(v_struct_453_);
lean_dec_ref(v_e1_308_);
v_idx_454_ = lean_ctor_get(v_e2_309_, 1);
lean_inc(v_idx_454_);
v_struct_455_ = lean_ctor_get(v_e2_309_, 2);
lean_inc_ref(v_struct_455_);
lean_dec_ref(v_e2_309_);
v___x_456_ = lean_nat_dec_eq(v_idx_452_, v_idx_454_);
lean_dec(v_idx_454_);
lean_dec(v_idx_452_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_struct_455_);
lean_dec_ref(v_struct_453_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_456_;
v___y_315_ = v_snd_370_;
goto v___jp_311_;
}
else
{
lean_object* v___x_457_; lean_object* v_fst_458_; lean_object* v_snd_459_; uint8_t v___x_460_; 
v___x_457_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_struct_453_, v_struct_455_, v_snd_370_);
v_fst_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_fst_458_);
v_snd_459_ = lean_ctor_get(v___x_457_, 1);
lean_inc(v_snd_459_);
lean_dec_ref(v___x_457_);
v___x_460_ = lean_unbox(v_fst_458_);
lean_dec(v_fst_458_);
v___y_312_ = v_fst_363_;
v___y_313_ = v_fst_369_;
v_result_314_ = v___x_460_;
v___y_315_ = v_snd_459_;
goto v___jp_311_;
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_461_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_461_);
v___x_463_ = v___x_372_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_snd_370_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
case 8:
{
if (lean_obj_tag(v_e2_309_) == 8)
{
lean_object* v_type_465_; lean_object* v_value_466_; lean_object* v_body_467_; lean_object* v_type_468_; lean_object* v_value_469_; lean_object* v_body_470_; lean_object* v___x_471_; lean_object* v_fst_472_; uint8_t v___x_473_; 
lean_del_object(v___x_372_);
v_type_465_ = lean_ctor_get(v_e1_308_, 1);
lean_inc_ref(v_type_465_);
v_value_466_ = lean_ctor_get(v_e1_308_, 2);
lean_inc_ref(v_value_466_);
v_body_467_ = lean_ctor_get(v_e1_308_, 3);
lean_inc_ref(v_body_467_);
lean_dec_ref(v_e1_308_);
v_type_468_ = lean_ctor_get(v_e2_309_, 1);
lean_inc_ref(v_type_468_);
v_value_469_ = lean_ctor_get(v_e2_309_, 2);
lean_inc_ref(v_value_469_);
v_body_470_ = lean_ctor_get(v_e2_309_, 3);
lean_inc_ref(v_body_470_);
lean_dec_ref(v_e2_309_);
v___x_471_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_type_465_, v_type_468_, v_snd_370_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_fst_472_);
v___x_473_ = lean_unbox(v_fst_472_);
lean_dec(v_fst_472_);
if (v___x_473_ == 0)
{
lean_dec_ref(v_body_470_);
lean_dec_ref(v_value_469_);
lean_dec_ref(v_body_467_);
lean_dec_ref(v_value_466_);
v___y_349_ = v_fst_363_;
v___y_350_ = v_fst_369_;
v___y_351_ = v___x_471_;
goto v___jp_348_;
}
else
{
lean_object* v_snd_474_; lean_object* v___x_475_; lean_object* v_fst_476_; uint8_t v___x_477_; 
v_snd_474_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_snd_474_);
lean_dec_ref(v___x_471_);
v___x_475_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_value_466_, v_value_469_, v_snd_474_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
v___x_477_ = lean_unbox(v_fst_476_);
lean_dec(v_fst_476_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_body_470_);
lean_dec_ref(v_body_467_);
v___y_349_ = v_fst_363_;
v___y_350_ = v_fst_369_;
v___y_351_ = v___x_475_;
goto v___jp_348_;
}
else
{
lean_object* v_snd_478_; lean_object* v___x_479_; 
v_snd_478_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_snd_478_);
lean_dec_ref(v___x_475_);
v___x_479_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_307_, v_body_467_, v_body_470_, v_snd_478_);
v___y_349_ = v_fst_363_;
v___y_350_ = v_fst_369_;
v___y_351_ = v___x_479_;
goto v___jp_348_;
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v_e1_308_);
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
v___x_480_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_480_);
v___x_482_ = v___x_372_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_snd_370_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
default: 
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
lean_dec_ref(v_e1_308_);
v___x_484_ = lean_box(v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_484_);
v___x_486_ = v___x_372_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_snd_370_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_dec(v_fst_369_);
lean_dec(v_fst_363_);
lean_dec_ref(v_e2_309_);
lean_dec_ref(v_e1_308_);
v___x_488_ = lean_box(v___x_356_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_488_);
v___x_490_ = v___x_372_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_snd_370_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_493_ = l_Lean_Expr_bvarIdx_x21(v_e1_308_);
lean_dec_ref(v_e1_308_);
v___x_494_ = l_Lean_Expr_bvarIdx_x21(v_e2_309_);
lean_dec_ref(v_e2_309_);
v___x_495_ = lean_nat_dec_eq(v___x_493_, v___x_494_);
lean_dec(v___x_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_a_310_);
return v___x_497_;
}
}
v___jp_498_:
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Expr_isBVar(v_e1_308_);
if (v___x_499_ == 0)
{
v___y_358_ = v___x_499_;
goto v___jp_357_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_Expr_isBVar(v_e2_309_);
v___y_358_ = v___x_500_;
goto v___jp_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_isEquiv___boxed(lean_object* v_useHash_510_, lean_object* v_e1_511_, lean_object* v_e2_512_, lean_object* v_a_513_){
_start:
{
uint8_t v_useHash_boxed_514_; lean_object* v_res_515_; 
v_useHash_boxed_514_ = lean_unbox(v_useHash_510_);
v_res_515_ = l_Lean_Kernel_EquivManager_isEquiv(v_useHash_boxed_514_, v_e1_511_, v_e2_512_, v_a_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_EquivManager_addEquiv(lean_object* v_m_516_, lean_object* v_e1_517_, lean_object* v_e2_518_){
_start:
{
lean_object* v___x_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_525_; 
v___x_519_ = l_Lean_Kernel_EquivManager_toNode(v_e1_517_, v_m_516_);
v_fst_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_fst_520_);
v_snd_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_snd_521_);
lean_dec_ref(v___x_519_);
v___x_522_ = l_Lean_Kernel_EquivManager_toNode(v_e2_518_, v_snd_521_);
v_fst_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_fst_523_);
v_snd_524_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_snd_524_);
lean_dec_ref(v___x_522_);
v___x_525_ = l_Lean_Kernel_EquivManager_merge(v_snd_524_, v_fst_520_, v_fst_523_);
lean_dec(v_fst_523_);
lean_dec(v_fst_520_);
return v___x_525_;
}
}
lean_object* runtime_initialize_Lean_Kernel_PtrEq(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_EquivManager(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Kernel_PtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_EquivManager(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Kernel_PtrEq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_EquivManager(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Kernel_PtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_EquivManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_EquivManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_EquivManager(builtin);
}
#ifdef __cplusplus
}
#endif
