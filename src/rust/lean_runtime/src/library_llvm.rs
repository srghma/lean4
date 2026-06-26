/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

pub(crate) mod library_llvm_impl {
    use super::*;

    extern "C" {
        fn initialize_Lean_Compiler_IR_EmitLLVM(builtin: u8) -> *mut LeanObject;
        fn lean_ir_emit_llvm(
            env: *mut LeanObject,
            mod_name: *mut LeanObject,
            filepath: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[cfg(lean_has_llvm)]
    extern "C" {
        fn LLVMGetFirstTarget() -> usize;
        fn LLVMGetNextTarget(target: usize) -> usize;
        fn LLVMGetTargetName(target: usize) -> *const core::ffi::c_char;
        fn LLVMGetTargetDescription(target: usize) -> *const core::ffi::c_char;
        fn LLVMContextCreate() -> usize;
        fn LLVMBuildCall2(
            builder: usize,
            ty: usize,
            fnval: usize,
            args: *const usize,
            num_args: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMAddFunction(module: usize, name: *const core::ffi::c_char, ty: usize) -> usize;
        fn LLVMGetNamedFunction(module: usize, name: *const core::ffi::c_char) -> usize;
        fn LLVMAddGlobal(module: usize, ty: usize, name: *const core::ffi::c_char) -> usize;
        fn LLVMGetNamedGlobal(module: usize, name: *const core::ffi::c_char) -> usize;
        fn LLVMBuildGlobalString(
            builder: usize,
            string: *const core::ffi::c_char,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMGetUndef(ty: usize) -> usize;
        fn LLVMSetInitializer(global: usize, initializer: usize);
        fn LLVMFunctionType(
            return_ty: usize,
            args: *const usize,
            num_args: usize,
            is_var_arg: u8,
        ) -> usize;
        fn LLVMPointerTypeInContext(ctx: usize, addr_space: usize) -> usize;
        fn LLVMIntTypeInContext(ctx: usize, width: usize) -> usize;
        fn LLVMFloatTypeInContext(ctx: usize) -> usize;
        fn LLVMVoidTypeInContext(ctx: usize) -> usize;
        fn LLVMDoubleTypeInContext(ctx: usize) -> usize;
        fn LLVMPointerType(ty: usize, addr_space: u32) -> usize;
        fn LLVMArrayType(ty: usize, count: usize) -> usize;
        fn LLVMCreateBuilderInContext(ctx: usize) -> usize;
        fn LLVMAppendBasicBlockInContext(
            ctx: usize,
            fnval: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMPositionBuilderAtEnd(builder: usize, bb: usize);
        fn LLVMClearInsertionPosition(builder: usize);
        fn LLVMBuildCondBr(builder: usize, if_: usize, thenbb: usize, elsebb: usize) -> usize;
        fn LLVMBuildBr(builder: usize, bb: usize) -> usize;
        fn LLVMBuildStore(builder: usize, val: usize, slot: usize) -> usize;
        fn LLVMBuildLoad2(
            builder: usize,
            ty: usize,
            slot: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildAlloca(builder: usize, ty: usize, name: *const core::ffi::c_char) -> usize;
        fn LLVMBuildRet(builder: usize, val: usize) -> usize;
        fn LLVMBuildRetVoid(builder: usize) -> usize;
        fn LLVMBuildUnreachable(builder: usize) -> usize;
        fn LLVMBuildInBoundsGEP2(
            builder: usize,
            ty: usize,
            pointer: usize,
            indices: *const usize,
            num_indices: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildGEP2(
            builder: usize,
            ty: usize,
            pointer: usize,
            indices: *const usize,
            num_indices: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildSExt(
            builder: usize,
            val: usize,
            dest_ty: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildZExt(
            builder: usize,
            val: usize,
            dest_ty: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildTrunc(
            builder: usize,
            val: usize,
            dest_ty: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMGetIntTypeWidth(ty: usize) -> core::ffi::c_uint;
        fn LLVMBuildSwitch(builder: usize, val: usize, elsebb: usize, num_cases: usize) -> usize;
        fn LLVMBuildPtrToInt(
            builder: usize,
            ptr: usize,
            dest_ty: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildMul(
            builder: usize,
            lhs: usize,
            rhs: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildAdd(
            builder: usize,
            lhs: usize,
            rhs: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildSub(
            builder: usize,
            lhs: usize,
            rhs: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMBuildNot(builder: usize, v: usize, name: *const core::ffi::c_char) -> usize;
        fn LLVMBuildICmp(
            builder: usize,
            predicate: core::ffi::c_uint,
            x: usize,
            y: usize,
            name: *const core::ffi::c_char,
        ) -> usize;
        fn LLVMAddCase(switch_: usize, on_val: usize, destbb: usize);
        fn LLVMGetBasicBlockParent(bb: usize) -> usize;
        fn LLVMGetInsertBlock(builder: usize) -> usize;
        fn LLVMTypeOf(val: usize) -> usize;
        fn LLVMConstInt(ty: usize, val: u64, sext: u8) -> usize;
        fn LLVMConstArray(elem_ty: usize, vals: *const usize, num_vals: usize) -> usize;
        fn LLVMConstStringInContext(
            ctx: usize,
            string: *const core::ffi::c_char,
            len: usize,
            dont_null_terminate: u8,
        ) -> usize;
        fn LLVMConstPointerNull(elem_ty: usize) -> usize;
        fn LLVMGetParam(f: usize, ix: usize) -> usize;
        fn LLVMCountParams(f: usize) -> core::ffi::c_uint;
        fn LLVMSetTailCall(fnval: usize, is_tail: u8);
        fn LLVMCreateMemoryBufferWithContentsOfFile(
            path: *const core::ffi::c_char,
            out: *mut usize,
            err: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMParseBitcodeInContext(
            ctx: usize,
            membuf: usize,
            out_module: *mut usize,
            err: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMLinkModules2(dest: usize, src: usize) -> core::ffi::c_int;
        fn LLVMCreateTargetMachine(
            target: usize,
            triple: *const core::ffi::c_char,
            cpu: *const core::ffi::c_char,
            features: *const core::ffi::c_char,
            opt_level: core::ffi::c_uint,
            reloc_mode: core::ffi::c_uint,
            code_model: core::ffi::c_uint,
        ) -> usize;
        fn LLVMGetTargetFromTriple(
            triple: *const core::ffi::c_char,
            out_target: *mut usize,
            out_err: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMGetDefaultTargetTriple() -> *mut core::ffi::c_char;
        fn LLVMTargetMachineEmitToFile(
            target_machine: usize,
            module: usize,
            filepath: *mut core::ffi::c_char,
            codegen_type: core::ffi::c_uint,
            err_msg: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMDisposeTargetMachine(tm: usize);
        fn LLVMDisposeModule(module: usize);
        fn LLVMSetVisibility(value: usize, vis: core::ffi::c_uint);
        fn LLVMSetDLLStorageClass(value: usize, cls: core::ffi::c_uint);
        fn LLVMAddAttributeAtIndex(fnval: usize, idx: u64, attr: usize);
        fn LLVMGetFirstGlobal(module: usize) -> usize;
        fn LLVMGetNextGlobal(global: usize) -> usize;
        fn LLVMGetFirstFunction(module: usize) -> usize;
        fn LLVMGetNextFunction(function: usize) -> usize;
        fn LLVMSetLinkage(value: usize, linkage: core::ffi::c_uint);
        fn LLVMGetValueName2(value: usize, len: *mut usize) -> *const core::ffi::c_char;
        fn LLVMIsDeclaration(global: usize) -> u8;
        fn LLVMVerifyModule(
            module: usize,
            action: core::ffi::c_uint,
            err: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMCountBasicBlocks(fnval: usize) -> core::ffi::c_uint;
        fn LLVMGetEntryBasicBlock(fnval: usize) -> usize;
        fn LLVMGetFirstInstruction(bb: usize) -> usize;
        fn LLVMPositionBuilderBefore(builder: usize, instr: usize);
        fn LLVMCreateStringAttribute(
            ctx: usize,
            key: *const core::ffi::c_char,
            key_len: usize,
            value: *const core::ffi::c_char,
            value_len: usize,
        ) -> usize;
        fn LLVMModuleCreateWithNameInContext(name: *const core::ffi::c_char, ctx: usize) -> usize;
        fn LLVMWriteBitcodeToFile(
            module: usize,
            path: *const core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMPrintModuleToString(module: usize) -> *mut core::ffi::c_char;
        fn LLVMPrintModuleToFile(
            module: usize,
            path: *const core::ffi::c_char,
            err_msg: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int;
        fn LLVMDisposeMessage(message: *mut core::ffi::c_char);
        #[cfg(lean_has_llvm)]
        fn LLVMInitializeAllTargetInfos();
        #[cfg(lean_has_llvm)]
        fn LLVMInitializeAllTargets();
        #[cfg(lean_has_llvm)]
        fn LLVMInitializeAllTargetMCs();
        #[cfg(lean_has_llvm)]
        fn LLVMInitializeAllAsmParsers();
        #[cfg(lean_has_llvm)]
        fn LLVMInitializeAllAsmPrinters();
    }

    const LLVM_CODEGEN_OPT_LEVEL_AGGRESSIVE: core::ffi::c_uint = 3;
    const LLVM_RELOC_MODE_PIC: core::ffi::c_uint = 3;
    const LLVM_CODE_MODEL_DEFAULT: core::ffi::c_uint = 0;
    const LLVM_RETURN_STATUS_ACTION: core::ffi::c_uint = 2;

    #[cfg(not(lean_has_llvm))]
    fn llvm_unavailable() -> ! {
        panic!(
            "Please build a version of Lean4 with -DLLVM=ON to invoke the LLVM backend function."
        );
    }

    #[inline]
    pub(crate) unsafe fn lean_init_llvm() -> *mut LeanObject {
        initialize_Lean_Compiler_IR_EmitLLVM(0)
    }

    #[inline]
    pub(crate) unsafe fn lean_emit_llvm(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_ir_emit_llvm(p0, p1, p2)
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_initialize_target_info_impl() -> *mut LeanObject {
        LLVMInitializeAllTargetInfos();
        LLVMInitializeAllTargets();
        LLVMInitializeAllTargetMCs();
        LLVMInitializeAllAsmParsers();
        LLVMInitializeAllAsmPrinters();
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_initialize_target_info_impl() -> *mut LeanObject {
        llvm_unavailable()
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_initialize_target_info() -> *mut LeanObject {
        llvm_initialize_target_info_impl()
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_create_context() -> usize {
        llvm_create_context_impl()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_create_context_impl() -> usize {
        LLVMContextCreate()
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_create_context_impl() -> usize {
        llvm_unavailable()
    }

    #[inline]
    unsafe fn llvm_option_none() -> *mut LeanObject {
        lean_box(0)
    }

    #[inline]
    unsafe fn llvm_option_some(value: usize) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, lean_box(value));
        result
    }

    #[inline]
    unsafe fn llvm_type_array(param_tys: *mut LeanObject) -> Vec<usize> {
        let size = lean_array_size(param_tys);
        let mut tys = Vec::with_capacity(size);
        for i in 0..size {
            tys.push(lean_unbox(lean_array_get_core(param_tys, i)));
        }
        tys
    }

    #[inline]
    unsafe fn llvm_value_array(values: *mut LeanObject) -> Vec<usize> {
        let size = lean_array_size(values);
        let mut out = Vec::with_capacity(size);
        for i in 0..size {
            out.push(lean_unbox(lean_array_get_core(values, i)));
        }
        out
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_call2_impl(
        builder: usize,
        ty: usize,
        fnval: usize,
        args: Vec<usize>,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildCall2(
            builder,
            ty,
            fnval,
            args.as_ptr(),
            args.len(),
            lean_string_cstr(name),
        )
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_call2_impl(
        _builder: usize,
        _ty: usize,
        _fnval: usize,
        _args: Vec<usize>,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_cond_br_impl(
        builder: usize,
        cond: usize,
        thenbb: usize,
        elsebb: usize,
    ) -> usize {
        LLVMBuildCondBr(builder, cond, thenbb, elsebb)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_cond_br_impl(
        _builder: usize,
        _cond: usize,
        _thenbb: usize,
        _elsebb: usize,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_br_impl(builder: usize, bb: usize) -> usize {
        LLVMBuildBr(builder, bb)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_br_impl(_builder: usize, _bb: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_store_impl(builder: usize, val: usize, slot: usize) -> *mut LeanObject {
        LLVMBuildStore(builder, val, slot);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_store_impl(_builder: usize, _val: usize, _slot: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_load2_impl(
        builder: usize,
        ty: usize,
        slot: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildLoad2(builder, ty, slot, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_load2_impl(
        _builder: usize,
        _ty: usize,
        _slot: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_alloca_impl(builder: usize, ty: usize, name: *mut LeanObject) -> usize {
        LLVMBuildAlloca(builder, ty, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_alloca_impl(_builder: usize, _ty: usize, _name: *mut LeanObject) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_ret_impl(builder: usize, v: usize) -> usize {
        LLVMBuildRet(builder, v)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_ret_impl(_builder: usize, _v: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_ret_void_impl(builder: usize) -> usize {
        LLVMBuildRetVoid(builder)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_ret_void_impl(_builder: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_unreachable_impl(builder: usize) -> usize {
        LLVMBuildUnreachable(builder)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_unreachable_impl(_builder: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_inbounds_gep2_impl(
        builder: usize,
        ty: usize,
        pointer: usize,
        indices: Vec<usize>,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildInBoundsGEP2(
            builder,
            ty,
            pointer,
            indices.as_ptr(),
            indices.len(),
            lean_string_cstr(name),
        )
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_inbounds_gep2_impl(
        _builder: usize,
        _ty: usize,
        _pointer: usize,
        _indices: Vec<usize>,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_gep2_impl(
        builder: usize,
        ty: usize,
        pointer: usize,
        indices: Vec<usize>,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildGEP2(
            builder,
            ty,
            pointer,
            indices.as_ptr(),
            indices.len(),
            lean_string_cstr(name),
        )
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_gep2_impl(
        _builder: usize,
        _ty: usize,
        _pointer: usize,
        _indices: Vec<usize>,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_sext_impl(
        builder: usize,
        val: usize,
        ty: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildSExt(builder, val, ty, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_sext_impl(
        _builder: usize,
        _val: usize,
        _ty: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_zext_impl(
        builder: usize,
        val: usize,
        ty: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildZExt(builder, val, ty, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_zext_impl(
        _builder: usize,
        _val: usize,
        _ty: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_sext_or_trunc_impl(
        builder: usize,
        val: usize,
        dest_ty: usize,
        name: *mut LeanObject,
    ) -> usize {
        let val_ty = LLVMTypeOf(val);
        let val_width = LLVMGetIntTypeWidth(val_ty);
        let dest_width = LLVMGetIntTypeWidth(dest_ty);
        if val_width == dest_width {
            val
        } else if val_width < dest_width {
            LLVMBuildSExt(builder, val, dest_ty, lean_string_cstr(name))
        } else {
            LLVMBuildTrunc(builder, val, dest_ty, lean_string_cstr(name))
        }
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_sext_or_trunc_impl(
        _builder: usize,
        _val: usize,
        _dest_ty: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_switch_impl(
        builder: usize,
        val: usize,
        elsebb: usize,
        num_cases: usize,
    ) -> usize {
        LLVMBuildSwitch(builder, val, elsebb, num_cases)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_switch_impl(
        _builder: usize,
        _val: usize,
        _elsebb: usize,
        _num_cases: usize,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_ptr_to_int_impl(
        builder: usize,
        ptr: usize,
        dest_ty: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildPtrToInt(builder, ptr, dest_ty, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_ptr_to_int_impl(
        _builder: usize,
        _ptr: usize,
        _dest_ty: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_mul_impl(
        builder: usize,
        lhs: usize,
        rhs: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildMul(builder, lhs, rhs, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_mul_impl(
        _builder: usize,
        _lhs: usize,
        _rhs: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_add_impl(
        builder: usize,
        lhs: usize,
        rhs: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildAdd(builder, lhs, rhs, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_add_impl(
        _builder: usize,
        _lhs: usize,
        _rhs: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_sub_impl(
        builder: usize,
        lhs: usize,
        rhs: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildSub(builder, lhs, rhs, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_sub_impl(
        _builder: usize,
        _lhs: usize,
        _rhs: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_not_impl(builder: usize, v: usize, name: *mut LeanObject) -> usize {
        LLVMBuildNot(builder, v, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_not_impl(_builder: usize, _v: usize, _name: *mut LeanObject) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_icmp_impl(
        builder: usize,
        predicate: usize,
        x: usize,
        y: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildICmp(
            builder,
            predicate as core::ffi::c_uint,
            x,
            y,
            lean_string_cstr(name),
        )
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_icmp_impl(
        _builder: usize,
        _predicate: usize,
        _x: usize,
        _y: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_add_case_impl(switch_: usize, on_val: usize, destbb: usize) -> *mut LeanObject {
        LLVMAddCase(switch_, on_val, destbb);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_add_case_impl(
        _switch_: usize,
        _on_val: usize,
        _destbb: usize,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_basic_block_parent_impl(bb: usize) -> usize {
        LLVMGetBasicBlockParent(bb)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_basic_block_parent_impl(_bb: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_insert_block_impl(builder: usize) -> usize {
        LLVMGetInsertBlock(builder)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_insert_block_impl(_builder: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_type_of_impl(val: usize) -> usize {
        LLVMTypeOf(val)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_type_of_impl(_val: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_const_int_impl(ty: usize, val: u64, sext: u8) -> usize {
        LLVMConstInt(ty, val, sext)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_const_int_impl(_ty: usize, _val: u64, _sext: u8) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_const_array_impl(elem_ty: usize, vals: Vec<usize>) -> usize {
        LLVMConstArray(elem_ty, vals.as_ptr(), vals.len())
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_const_array_impl(_elem_ty: usize, _vals: Vec<usize>) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_const_string_impl(ctx: usize, s: *mut LeanObject) -> usize {
        LLVMConstStringInContext(ctx, lean_string_cstr(s), lean_string_len(s), 0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_const_string_impl(_ctx: usize, _s: *mut LeanObject) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_const_pointer_null_impl(ty: usize) -> usize {
        LLVMConstPointerNull(ty)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_const_pointer_null_impl(_ty: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_param_impl(f: usize, ix: usize) -> usize {
        LLVMGetParam(f, ix)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_param_impl(_f: usize, _ix: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_count_params_impl(f: usize) -> u64 {
        LLVMCountParams(f) as u64
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_count_params_impl(_f: usize) -> u64 {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_set_tail_call_impl(fnval: usize, is_tail: u8) -> *mut LeanObject {
        LLVMSetTailCall(fnval, is_tail);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_set_tail_call_impl(_fnval: usize, _is_tail: u8) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_create_memory_buffer_with_contents_of_file_impl(path: *mut LeanObject) -> usize {
        let mut membuf = 0;
        let mut err_str: *mut core::ffi::c_char = core::ptr::null_mut();
        let path_cstr = lean_string_cstr(path);
        let is_error =
            LLVMCreateMemoryBufferWithContentsOfFile(path_cstr, &mut membuf, &mut err_str);
        if is_error != 0 {
            if !err_str.is_null() {
                eprintln!(
                    "LLVMCreateMemoryBufferWithContentsOfFile({}) failed: {}",
                    CStr::from_ptr(path_cstr).to_string_lossy(),
                    CStr::from_ptr(err_str).to_string_lossy()
                );
                LLVMDisposeMessage(err_str);
            }
            panic!("failed to create membuf from file");
        }
        membuf
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_create_memory_buffer_with_contents_of_file_impl(
        _path: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_parse_bitcode_impl(ctx: usize, membuf: usize) -> usize {
        let mut out_module = 0;
        let mut err_str: *mut core::ffi::c_char = core::ptr::null_mut();
        let is_error = LLVMParseBitcodeInContext(ctx, membuf, &mut out_module, &mut err_str);
        if is_error != 0 {
            if !err_str.is_null() {
                eprintln!(
                    "LLVMParseBitcodeInContext failed: {}",
                    CStr::from_ptr(err_str).to_string_lossy()
                );
                LLVMDisposeMessage(err_str);
            }
            panic!("failed to parse bitcode");
        }
        out_module
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_parse_bitcode_impl(_ctx: usize, _membuf: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_link_modules_impl(dest: usize, src: usize) -> *mut LeanObject {
        let is_error = LLVMLinkModules2(dest, src);
        assert_eq!(is_error, 0, "failed to link modules");
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_link_modules_impl(_dest: usize, _src: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_create_target_machine_impl(
        target: usize,
        triple: *mut LeanObject,
        cpu: *mut LeanObject,
        features: *mut LeanObject,
    ) -> usize {
        LLVMCreateTargetMachine(
            target,
            lean_string_cstr(triple),
            lean_string_cstr(cpu),
            lean_string_cstr(features),
            LLVM_CODEGEN_OPT_LEVEL_AGGRESSIVE,
            LLVM_RELOC_MODE_PIC,
            LLVM_CODE_MODEL_DEFAULT,
        )
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_create_target_machine_impl(
        _target: usize,
        _triple: *mut LeanObject,
        _cpu: *mut LeanObject,
        _features: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_target_from_triple_impl(triple: *mut LeanObject) -> usize {
        let mut target = 0;
        let mut err_msg: *mut core::ffi::c_char = core::ptr::null_mut();
        let is_error = LLVMGetTargetFromTriple(lean_string_cstr(triple), &mut target, &mut err_msg);
        if is_error != 0 {
            eprintln!(
                "Unable to find target '{}'. Registered targets:",
                CStr::from_ptr(lean_string_cstr(triple)).to_string_lossy()
            );
            let mut target_it = LLVMGetFirstTarget();
            while target_it != 0 {
                eprintln!(
                    "    {:<10} - {}",
                    CStr::from_ptr(LLVMGetTargetName(target_it)).to_string_lossy(),
                    CStr::from_ptr(LLVMGetTargetDescription(target_it)).to_string_lossy()
                );
                target_it = LLVMGetNextTarget(target_it);
            }
            if !err_msg.is_null() {
                LLVMDisposeMessage(err_msg);
            }
            panic!("failed to get target from triple");
        }
        target
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_target_from_triple_impl(_triple: *mut LeanObject) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_default_target_triple_impl() -> *mut LeanObject {
        let triple = LLVMGetDefaultTargetTriple();
        let out = lean_mk_string(triple);
        libc::free(triple.cast());
        out
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_default_target_triple_impl() -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_target_machine_emit_to_file_impl(
        target_machine: usize,
        module: usize,
        filepath: *mut LeanObject,
        codegen_type: usize,
    ) -> *mut LeanObject {
        let mut err_msg: *mut core::ffi::c_char = core::ptr::null_mut();
        let mut filepath_cstr =
            lean_string_cstr(filepath) as *const core::ffi::c_char as *mut core::ffi::c_char;
        let is_error = LLVMTargetMachineEmitToFile(
            target_machine,
            module,
            filepath_cstr,
            codegen_type as core::ffi::c_uint,
            &mut err_msg,
        );
        if is_error != 0 {
            if !err_msg.is_null() {
                eprintln!(
                    "LLVMTargetMachineEmitToFile failed: {}",
                    CStr::from_ptr(err_msg).to_string_lossy()
                );
                LLVMDisposeMessage(err_msg);
            }
            panic!("failed to emit target machine output");
        }
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_target_machine_emit_to_file_impl(
        _target_machine: usize,
        _module: usize,
        _filepath: *mut LeanObject,
        _codegen_type: usize,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_dispose_target_machine_impl(tm: usize) -> *mut LeanObject {
        LLVMDisposeTargetMachine(tm);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_dispose_target_machine_impl(_tm: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_dispose_module_impl(module: usize) -> *mut LeanObject {
        LLVMDisposeModule(module);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_dispose_module_impl(_module: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_set_visibility_impl(value: usize, vis: usize) -> *mut LeanObject {
        LLVMSetVisibility(value, vis as core::ffi::c_uint);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_set_visibility_impl(_value: usize, _vis: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_set_dll_storage_class_impl(value: usize, cls: usize) -> *mut LeanObject {
        LLVMSetDLLStorageClass(value, cls as core::ffi::c_uint);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_set_dll_storage_class_impl(_value: usize, _cls: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_create_string_attribute_impl(
        ctx: usize,
        key: *mut LeanObject,
        value: *mut LeanObject,
    ) -> usize {
        LLVMCreateStringAttribute(
            ctx,
            lean_string_cstr(key),
            lean_string_len(key),
            lean_string_cstr(value),
            lean_string_len(value),
        )
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_create_string_attribute_impl(
        _ctx: usize,
        _key: *mut LeanObject,
        _value: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_add_attribute_at_index_impl(
        fnval: usize,
        idx: usize,
        attr: usize,
    ) -> *mut LeanObject {
        LLVMAddAttributeAtIndex(fnval, idx as u64, attr);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_add_attribute_at_index_impl(
        _fnval: usize,
        _idx: usize,
        _attr: usize,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_first_global_impl(module: usize) -> usize {
        LLVMGetFirstGlobal(module)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_first_global_impl(_module: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_next_global_impl(global: usize) -> usize {
        LLVMGetNextGlobal(global)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_next_global_impl(_global: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_first_function_impl(module: usize) -> usize {
        LLVMGetFirstFunction(module)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_first_function_impl(_module: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_next_function_impl(function: usize) -> usize {
        LLVMGetNextFunction(function)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_next_function_impl(_function: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_set_linkage_impl(value: usize, linkage: usize) -> *mut LeanObject {
        LLVMSetLinkage(value, linkage as core::ffi::c_uint);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_set_linkage_impl(_value: usize, _linkage: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_value_name2_impl(value: usize) -> *mut LeanObject {
        let mut len = 0;
        let name = LLVMGetValueName2(value, &mut len);
        lean_mk_string_from_bytes(name, len)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_value_name2_impl(_value: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_is_declaration_impl(global: usize) -> *mut LeanObject {
        lean_box(LLVMIsDeclaration(global) as usize)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_is_declaration_impl(_global: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_verify_module_impl(module: usize) -> *mut LeanObject {
        let mut msg: *mut core::ffi::c_char = core::ptr::null_mut();
        let broken = LLVMVerifyModule(module, LLVM_RETURN_STATUS_ACTION, &mut msg);
        if broken != 0 {
            if !msg.is_null() {
                let message = lean_mk_string(msg);
                LLVMDisposeMessage(msg);
                return llvm_option_some(message as usize);
            }
            panic!("LLVMVerifyModule failed without a message");
        }
        llvm_option_none()
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_verify_module_impl(_module: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_count_basic_blocks_impl(fn_val: usize) -> u64 {
        LLVMCountBasicBlocks(fn_val) as u64
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_count_basic_blocks_impl(_fn_val: usize) -> u64 {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_entry_basic_block_impl(fn_val: usize) -> usize {
        LLVMGetEntryBasicBlock(fn_val)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_entry_basic_block_impl(_fn_val: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_first_instruction_impl(bb: usize) -> *mut LeanObject {
        let instr = LLVMGetFirstInstruction(bb);
        if instr == 0 {
            llvm_option_none()
        } else {
            llvm_option_some(instr)
        }
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_first_instruction_impl(_bb: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_position_builder_before_impl(builder: usize, instr: usize) -> *mut LeanObject {
        LLVMPositionBuilderBefore(builder, instr);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_position_builder_before_impl(_builder: usize, _instr: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_add_function_impl(
        _ctx: usize,
        module: usize,
        name: *mut LeanObject,
        ty: usize,
    ) -> usize {
        LLVMAddFunction(module, lean_string_cstr(name), ty)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_add_function_impl(
        _ctx: usize,
        _module: usize,
        _name: *mut LeanObject,
        _ty: usize,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_named_function_impl(
        _ctx: usize,
        module: usize,
        name: *mut LeanObject,
    ) -> *mut LeanObject {
        let result = LLVMGetNamedFunction(module, lean_string_cstr(name));
        if result == 0 {
            llvm_option_none()
        } else {
            llvm_option_some(result)
        }
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_named_function_impl(
        _ctx: usize,
        _module: usize,
        _name: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_add_global_impl(
        _ctx: usize,
        module: usize,
        name: *mut LeanObject,
        ty: usize,
    ) -> usize {
        LLVMAddGlobal(module, ty, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_add_global_impl(
        _ctx: usize,
        _module: usize,
        _name: *mut LeanObject,
        _ty: usize,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_named_global_impl(
        _ctx: usize,
        module: usize,
        name: *mut LeanObject,
    ) -> *mut LeanObject {
        let result = LLVMGetNamedGlobal(module, lean_string_cstr(name));
        if result == 0 {
            llvm_option_none()
        } else {
            llvm_option_some(result)
        }
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_named_global_impl(
        _ctx: usize,
        _module: usize,
        _name: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_build_global_string_impl(
        _ctx: usize,
        builder: usize,
        string: *mut LeanObject,
        name: *mut LeanObject,
    ) -> usize {
        LLVMBuildGlobalString(builder, lean_string_cstr(string), lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_build_global_string_impl(
        _ctx: usize,
        _builder: usize,
        _string: *mut LeanObject,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_get_undef_impl(_ctx: usize, ty: usize) -> usize {
        LLVMGetUndef(ty)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_get_undef_impl(_ctx: usize, _ty: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_set_initializer_impl(
        _ctx: usize,
        global: usize,
        initializer: usize,
    ) -> *mut LeanObject {
        LLVMSetInitializer(global, initializer);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_set_initializer_impl(
        _ctx: usize,
        _global: usize,
        _initializer: usize,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_function_type_impl(
        _ctx: usize,
        return_ty: usize,
        arg_tys: *mut LeanObject,
        is_var_arg: u8,
    ) -> usize {
        let tys = llvm_type_array(arg_tys);
        LLVMFunctionType(return_ty, tys.as_ptr(), tys.len(), is_var_arg)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_function_type_impl(
        _ctx: usize,
        _return_ty: usize,
        _arg_tys: *mut LeanObject,
        _is_var_arg: u8,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_opaque_pointer_type_in_context_impl(ctx: usize, addrspace: usize) -> usize {
        LLVMPointerTypeInContext(ctx, addrspace)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_opaque_pointer_type_in_context_impl(_ctx: usize, _addrspace: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_int_type_in_context_impl(ctx: usize, width: usize) -> usize {
        LLVMIntTypeInContext(ctx, width)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_int_type_in_context_impl(_ctx: usize, _width: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_float_type_in_context_impl(ctx: usize) -> usize {
        LLVMFloatTypeInContext(ctx)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_float_type_in_context_impl(_ctx: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_void_type_in_context_impl(ctx: usize) -> usize {
        LLVMVoidTypeInContext(ctx)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_void_type_in_context_impl(_ctx: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_double_type_in_context_impl(ctx: usize) -> usize {
        LLVMDoubleTypeInContext(ctx)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_double_type_in_context_impl(_ctx: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_pointer_type_impl(_ctx: usize, base: usize) -> usize {
        LLVMPointerType(base, 0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_pointer_type_impl(_ctx: usize, _base: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_array_type_impl(_ctx: usize, base: usize, nelem: usize) -> usize {
        LLVMArrayType(base, nelem)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_array_type_impl(_ctx: usize, _base: usize, _nelem: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_create_builder_in_context_impl(ctx: usize) -> usize {
        LLVMCreateBuilderInContext(ctx)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_create_builder_in_context_impl(_ctx: usize) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_append_basic_block_in_context_impl(
        ctx: usize,
        function: usize,
        name: *mut LeanObject,
    ) -> usize {
        LLVMAppendBasicBlockInContext(ctx, function, lean_string_cstr(name))
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_append_basic_block_in_context_impl(
        _ctx: usize,
        _function: usize,
        _name: *mut LeanObject,
    ) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_position_builder_at_end_impl(builder: usize, bb: usize) -> *mut LeanObject {
        LLVMPositionBuilderAtEnd(builder, bb);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_position_builder_at_end_impl(_builder: usize, _bb: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_clear_insertion_position_impl(builder: usize) -> *mut LeanObject {
        LLVMClearInsertionPosition(builder);
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_clear_insertion_position_impl(_builder: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_create_module_impl(ctx: usize, str_obj: *mut LeanObject) -> usize {
        LLVMModuleCreateWithNameInContext(lean_string_cstr(str_obj), ctx)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_create_module_impl(_ctx: usize, _str_obj: *mut LeanObject) -> usize {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_write_bitcode_to_file_impl(
        _ctx: usize,
        mod_: usize,
        filepath: *mut LeanObject,
    ) -> *mut LeanObject {
        let err = LLVMWriteBitcodeToFile(mod_, lean_string_cstr(filepath));
        if err != 0 {
            panic!("LLVMWriteBitcodeToFile failed")
        }
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_write_bitcode_to_file_impl(
        _ctx: usize,
        _mod_: usize,
        _filepath: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_module_to_string_impl(_ctx: usize, mod_: usize) -> *mut LeanObject {
        let str = LLVMPrintModuleToString(mod_);
        let out = lean_mk_string(str);
        libc::free(str.cast());
        out
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_module_to_string_impl(_ctx: usize, _mod_: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_print_module_to_string_impl(_ctx: usize, mod_: usize) -> *mut LeanObject {
        let c_str = LLVMPrintModuleToString(mod_);
        let out = lean_mk_string(c_str);
        LLVMDisposeMessage(c_str);
        out
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_print_module_to_string_impl(_ctx: usize, _mod_: usize) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[cfg(lean_has_llvm)]
    unsafe fn llvm_print_module_to_file_impl(
        _ctx: usize,
        mod_: usize,
        file: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut err_msg: *mut core::ffi::c_char = core::ptr::null_mut();
        let status = LLVMPrintModuleToFile(mod_, lean_string_cstr(file), &mut err_msg);
        if status != 0 {
            if !err_msg.is_null() {
                LLVMDisposeMessage(err_msg);
            }
            panic!("LLVMPrintModuleToFile failed")
        }
        lean_box(0)
    }

    #[cfg(not(lean_has_llvm))]
    unsafe fn llvm_print_module_to_file_impl(
        _ctx: usize,
        _mod_: usize,
        _file: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_unavailable()
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_create_module(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_create_module_impl(lean_unbox(p0), p1)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_write_bitcode_to_file(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_write_bitcode_to_file_impl(lean_unbox(p0), lean_unbox(p1), p2)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_module_to_string(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_module_to_string_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_add_function(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
    ) -> usize {
        llvm_add_function_impl(lean_unbox(p0), lean_unbox(p1), p2, lean_unbox(p3))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_named_function(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_get_named_function_impl(lean_unbox(p0), lean_unbox(p1), p2)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_add_global(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
    ) -> usize {
        llvm_add_global_impl(lean_unbox(p0), lean_unbox(p1), p2, lean_unbox(p3))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_named_global(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_get_named_global_impl(lean_unbox(p0), lean_unbox(p1), p2)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_global_string(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
    ) -> usize {
        llvm_build_global_string_impl(lean_unbox(p0), lean_unbox(p1), p2, p3)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_undef(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_get_undef_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_set_initializer(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_set_initializer_impl(lean_unbox(p0), lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_function_type(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: u8,
    ) -> usize {
        llvm_function_type_impl(lean_unbox(p0), lean_unbox(p1), p2, p3)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_opaque_pointer_type_in_context(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_opaque_pointer_type_in_context_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_int_type_in_context(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_int_type_in_context_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_float_type_in_context(p0: *mut LeanObject) -> usize {
        llvm_float_type_in_context_impl(lean_unbox(p0))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_void_type_in_context(p0: *mut LeanObject) -> usize {
        llvm_void_type_in_context_impl(lean_unbox(p0))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_double_type_in_context(p0: *mut LeanObject) -> usize {
        llvm_double_type_in_context_impl(lean_unbox(p0))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_pointer_type(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_pointer_type_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_array_type(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> usize {
        llvm_array_type_impl(lean_unbox(p0), lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_create_builder_in_context(p0: *mut LeanObject) -> usize {
        llvm_create_builder_in_context_impl(lean_unbox(p0))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_append_basic_block_in_context(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> usize {
        llvm_append_basic_block_in_context_impl(lean_unbox(p0), lean_unbox(p1), p2)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_position_builder_at_end(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_position_builder_at_end_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_clear_insertion_position(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_clear_insertion_position_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_call2(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject,
        p5: *mut LeanObject
    ) -> usize {
        let args = llvm_value_array(p4);
        llvm_build_call2_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), args, p5)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_cond_br(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_cond_br_impl(
            lean_unbox(p1),
            lean_unbox(p2),
            lean_unbox(p3),
            lean_unbox(p4),
        )
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_br(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> usize {
        llvm_build_br_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_store(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_build_store_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_load2(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_load2_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_alloca(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject
    ) -> usize {
        llvm_build_alloca_impl(lean_unbox(p1), lean_unbox(p2), p3)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_ret(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> usize {
        llvm_build_ret_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_ret_void(p0: *mut LeanObject) -> usize {
        llvm_build_ret_void_impl(lean_unbox(p0))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_unreachable(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_build_unreachable_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_inbounds_gep2(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject,
        p5: *mut LeanObject
    ) -> usize {
        let indices = llvm_value_array(p4);
        llvm_build_inbounds_gep2_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), indices, p5)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_gep2(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject,
        p5: *mut LeanObject
    ) -> usize {
        let indices = llvm_value_array(p4);
        llvm_build_gep2_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), indices, p5)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_sext(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_sext_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_zext(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_zext_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_sext_or_trunc(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_sext_or_trunc_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_switch(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_switch_impl(
            lean_unbox(p1),
            lean_unbox(p2),
            lean_unbox(p3),
            lean_unbox(p4),
        )
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_ptr_to_int(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_ptr_to_int_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_mul(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_mul_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_add(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_add_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_sub(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_build_sub_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3), p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_not(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject
    ) -> usize {
        llvm_build_not_impl(lean_unbox(p1), lean_unbox(p2), p3)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_build_icmp(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject,
        p5: *mut LeanObject
    ) -> usize {
        llvm_build_icmp_impl(
            lean_unbox(p1),
            lean_unbox(p2),
            lean_unbox(p3),
            lean_unbox(p4),
            p5,
        )
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_add_case(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        _p3: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_add_case_impl(lean_unbox(p0), lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_basic_block_parent(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_basic_block_parent_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_insert_block(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_insert_block_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_type_of(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_type_of_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_print_module_to_string(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_print_module_to_string_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_print_module_to_file(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> *mut LeanObject {
        llvm_print_module_to_file_impl(lean_unbox(p0), lean_unbox(p1), p2)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_const_int(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject
    ) -> usize {
        llvm_const_int_impl(lean_unbox(p1), lean_unbox(p2) as u64, lean_unbox(p3) as u8)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_const_array(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> usize {
        let vals = llvm_value_array(p2);
        llvm_const_array_impl(lean_unbox(p1), vals)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_const_string(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_const_string_impl(lean_unbox(p0), p1)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_const_pointer_null(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_const_pointer_null_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn llvm_get_param(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> usize {
        llvm_get_param_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn llvm_count_params(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> u64 {
        llvm_count_params_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_set_tail_call(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_set_tail_call_impl(lean_unbox(p1), lean_unbox(p2) as u8)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_parse_bitcode(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
    ) -> usize {
        llvm_parse_bitcode_impl(lean_unbox(p0), lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_link_modules(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_link_modules_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_create_target_machine(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> usize {
        llvm_create_target_machine_impl(lean_unbox(p1), p2, p3, p4)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_target_from_triple(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_target_from_triple_impl(p1)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_default_target_triple() -> *mut LeanObject {
        llvm_get_default_target_triple_impl()
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_target_machine_emit_to_file(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject,
        p4: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_target_machine_emit_to_file_impl(lean_unbox(p1), lean_unbox(p2), p3, lean_unbox(p4))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_dispose_target_machine(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_dispose_target_machine_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_dispose_module(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_dispose_module_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_set_visibility(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_set_visibility_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_set_dll_storage_class(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_set_dll_storage_class_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_add_attribute_at_index(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
        p3: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_add_attribute_at_index_impl(lean_unbox(p1), lean_unbox(p2), lean_unbox(p3))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_first_global(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_first_global_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_next_global(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_next_global_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_first_function(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_first_function_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_next_function(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_next_function_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_set_linkage(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_set_linkage_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_value_name2(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_get_value_name2_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn llvm_is_declaration(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_is_declaration_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_verify_module(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_verify_module_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_count_basic_blocks(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> u64 {
        llvm_count_basic_blocks_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_entry_basic_block(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_get_entry_basic_block_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_get_first_instruction(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_get_first_instruction_impl(lean_unbox(p1))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_position_builder_before(
        _p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject
    ) -> *mut LeanObject {
        llvm_position_builder_before_impl(lean_unbox(p1), lean_unbox(p2))
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_create_memory_buffer_with_contents_of_file(
        _p0: *mut LeanObject,
        p1: *mut LeanObject
    ) -> usize {
        llvm_create_memory_buffer_with_contents_of_file_impl(p1)
    }

    #[inline]
    pub(crate) unsafe fn lean_llvm_create_string_attribute(
        p0: *mut LeanObject,
        p1: *mut LeanObject,
        p2: *mut LeanObject,
    ) -> usize {
        llvm_create_string_attribute_impl(lean_unbox(p0), p1, p2)
    }
}
