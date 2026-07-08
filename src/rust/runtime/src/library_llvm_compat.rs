use core::ffi::{c_char, c_int, c_uint};
use super::*;
use llvm_sys::{analysis, bit_reader, core, target, target_machine};

    #[inline]
    pub unsafe fn LLVMGetFirstTarget() -> usize {
        target::LLVMGetFirstTarget() as usize
    }

    #[inline]
    pub unsafe fn LLVMGetNextTarget(target: usize) -> usize {
        target::LLVMGetNextTarget(target as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetTargetName(target: usize) -> *const c_char {
        target::LLVMGetTargetName(target as _)
    }

    #[inline]
    pub unsafe fn LLVMGetTargetDescription(target: usize) -> *const c_char {
        target::LLVMGetTargetDescription(target as _)
    }

    #[inline]
    pub unsafe fn LLVMContextCreate() -> usize {
        core::LLVMContextCreate() as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildCall2(
        builder: usize,
        ty: usize,
        fnval: usize,
        args: *const usize,
        num_args: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildCall2(builder as _, ty as _, fnval as _, args as *mut _, num_args as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMAddFunction(module: usize, name: *const c_char, ty: usize) -> usize {
        core::LLVMAddFunction(module as _, name, ty as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetNamedFunction(module: usize, name: *const c_char) -> usize {
        core::LLVMGetNamedFunction(module as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMAddGlobal(module: usize, ty: usize, name: *const c_char) -> usize {
        core::LLVMAddGlobal(module as _, ty as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetNamedGlobal(module: usize, name: *const c_char) -> usize {
        core::LLVMGetNamedGlobal(module as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildGlobalString(
        builder: usize,
        string: *const c_char,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildGlobalString(builder as _, string, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetUndef(ty: usize) -> usize {
        core::LLVMGetUndef(ty as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMSetInitializer(global: usize, initializer: usize) {
        core::LLVMSetInitializer(global as _, initializer as _)
    }

    #[inline]
    pub unsafe fn LLVMFunctionType(
        return_ty: usize,
        args: *const usize,
        num_args: usize,
        is_var_arg: u8,
    ) -> usize {
        core::LLVMFunctionType(return_ty as _, args as *const _, num_args as _, is_var_arg) as usize
    }

    #[inline]
    pub unsafe fn LLVMPointerTypeInContext(ctx: usize, addr_space: usize) -> usize {
        core::LLVMPointerTypeInContext(ctx as _, addr_space as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMIntTypeInContext(ctx: usize, width: usize) -> usize {
        core::LLVMIntTypeInContext(ctx as _, width as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMFloatTypeInContext(ctx: usize) -> usize {
        core::LLVMFloatTypeInContext(ctx as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMVoidTypeInContext(ctx: usize) -> usize {
        core::LLVMVoidTypeInContext(ctx as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMDoubleTypeInContext(ctx: usize) -> usize {
        core::LLVMDoubleTypeInContext(ctx as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMPointerType(ty: usize, addr_space: u32) -> usize {
        core::LLVMPointerType(ty as _, addr_space as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMArrayType(ty: usize, count: usize) -> usize {
        core::LLVMArrayType(ty as _, count as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMCreateBuilderInContext(ctx: usize) -> usize {
        core::LLVMCreateBuilderInContext(ctx as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMAppendBasicBlockInContext(
        ctx: usize,
        fnval: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMAppendBasicBlockInContext(ctx as _, fnval as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMPositionBuilderAtEnd(builder: usize, bb: usize) {
        core::LLVMPositionBuilderAtEnd(builder as _, bb as _)
    }

    #[inline]
    pub unsafe fn LLVMClearInsertionPosition(builder: usize) {
        core::LLVMClearInsertionPosition(builder as _)
    }

    #[inline]
    pub unsafe fn LLVMBuildCondBr(builder: usize, if_: usize, thenbb: usize, elsebb: usize) -> usize {
        core::LLVMBuildCondBr(builder as _, if_ as _, thenbb as _, elsebb as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildBr(builder: usize, bb: usize) -> usize {
        core::LLVMBuildBr(builder as _, bb as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildStore(builder: usize, val: usize, slot: usize) -> usize {
        core::LLVMBuildStore(builder as _, val as _, slot as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildLoad2(
        builder: usize,
        ty: usize,
        slot: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildLoad2(builder as _, ty as _, slot as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildAlloca(builder: usize, ty: usize, name: *const c_char) -> usize {
        core::LLVMBuildAlloca(builder as _, ty as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildRet(builder: usize, val: usize) -> usize {
        core::LLVMBuildRet(builder as _, val as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildRetVoid(builder: usize) -> usize {
        core::LLVMBuildRetVoid(builder as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildUnreachable(builder: usize) -> usize {
        core::LLVMBuildUnreachable(builder as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildInBoundsGEP2(
        builder: usize,
        ty: usize,
        pointer: usize,
        indices: *const usize,
        num_indices: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildInBoundsGEP2(builder as _, ty as _, pointer as _, indices as *const _, num_indices as _, name)
            as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildGEP2(
        builder: usize,
        ty: usize,
        pointer: usize,
        indices: *const usize,
        num_indices: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildGEP2(builder as _, ty as _, pointer as _, indices as *const _, num_indices as _, name)
            as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildSExt(
        builder: usize,
        val: usize,
        dest_ty: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildSExt(builder as _, val as _, dest_ty as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildZExt(
        builder: usize,
        val: usize,
        dest_ty: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildZExt(builder as _, val as _, dest_ty as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildTrunc(
        builder: usize,
        val: usize,
        dest_ty: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildTrunc(builder as _, val as _, dest_ty as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetIntTypeWidth(ty: usize) -> c_uint {
        core::LLVMGetIntTypeWidth(ty as _)
    }

    #[inline]
    pub unsafe fn LLVMBuildSwitch(builder: usize, val: usize, elsebb: usize, num_cases: usize) -> usize {
        core::LLVMBuildSwitch(builder as _, val as _, elsebb as _, num_cases as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildPtrToInt(
        builder: usize,
        ptr: usize,
        dest_ty: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildPtrToInt(builder as _, ptr as _, dest_ty as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildMul(builder: usize, lhs: usize, rhs: usize, name: *const c_char) -> usize {
        core::LLVMBuildMul(builder as _, lhs as _, rhs as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildAdd(builder: usize, lhs: usize, rhs: usize, name: *const c_char) -> usize {
        core::LLVMBuildAdd(builder as _, lhs as _, rhs as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildSub(builder: usize, lhs: usize, rhs: usize, name: *const c_char) -> usize {
        core::LLVMBuildSub(builder as _, lhs as _, rhs as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildNot(builder: usize, v: usize, name: *const c_char) -> usize {
        core::LLVMBuildNot(builder as _, v as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMBuildICmp(
        builder: usize,
        predicate: c_uint,
        x: usize,
        y: usize,
        name: *const c_char,
    ) -> usize {
        core::LLVMBuildICmp(builder as _, predicate as _, x as _, y as _, name) as usize
    }

    #[inline]
    pub unsafe fn LLVMAddCase(switch_: usize, on_val: usize, destbb: usize) {
        core::LLVMAddCase(switch_ as _, on_val as _, destbb as _)
    }

    #[inline]
    pub unsafe fn LLVMGetBasicBlockParent(bb: usize) -> usize {
        core::LLVMGetBasicBlockParent(bb as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetInsertBlock(builder: usize) -> usize {
        core::LLVMGetInsertBlock(builder as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMTypeOf(val: usize) -> usize {
        core::LLVMTypeOf(val as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMConstInt(ty: usize, val: u64, sext: u8) -> usize {
        core::LLVMConstInt(ty as _, val, sext) as usize
    }

    #[inline]
    pub unsafe fn LLVMConstArray(elem_ty: usize, vals: *const usize, num_vals: usize) -> usize {
        core::LLVMConstArray(elem_ty as _, vals as *const _, num_vals as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMConstStringInContext(
        ctx: usize,
        string: *const c_char,
        len: usize,
        dont_null_terminate: u8,
    ) -> usize {
        core::LLVMConstStringInContext(ctx as _, string, len as _, dont_null_terminate) as usize
    }

    #[inline]
    pub unsafe fn LLVMConstPointerNull(elem_ty: usize) -> usize {
        core::LLVMConstPointerNull(elem_ty as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetParam(f: usize, ix: usize) -> usize {
        core::LLVMGetParam(f as _, ix as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMCountParams(f: usize) -> c_uint {
        core::LLVMCountParams(f as _)
    }

    #[inline]
    pub unsafe fn LLVMSetTailCall(fnval: usize, is_tail: bool) {
        core::LLVMSetTailCall(fnval as _, is_tail as _)
    }

    #[inline]
    pub unsafe fn LLVMCreateMemoryBufferWithContentsOfFile(
        path: *const c_char,
        out: *mut usize,
        err: *mut *mut c_char,
    ) -> c_int {
        core::LLVMCreateMemoryBufferWithContentsOfFile(path, out as *mut _, err)
    }

    #[inline]
    pub unsafe fn LLVMParseBitcodeInContext(
        ctx: usize,
        membuf: usize,
        out_module: *mut usize,
        err: *mut *mut c_char,
    ) -> c_int {
        bit_reader::LLVMParseBitcodeInContext(ctx as _, membuf as _, out_module as *mut _, err)
    }

    #[inline]
    pub unsafe fn LLVMLinkModules2(dest: usize, src: usize) -> c_int {
        core::LLVMLinkModules2(dest as _, src as _)
    }

    #[inline]
    pub unsafe fn LLVMCreateTargetMachine(
        target: usize,
        triple: *const c_char,
        cpu: *const c_char,
        features: *const c_char,
        opt_level: c_uint,
        reloc_mode: c_uint,
        code_model: c_uint,
    ) -> usize {
        target_machine::LLVMCreateTargetMachine(
            target as _,
            triple,
            cpu,
            features,
            opt_level as _,
            reloc_mode as _,
            code_model as _,
        ) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetTargetFromTriple(
        triple: *const c_char,
        out_target: *mut usize,
        out_err: *mut *mut c_char,
    ) -> c_int {
        target_machine::LLVMGetTargetFromTriple(triple, out_target as *mut _, out_err)
    }

    #[inline]
    pub unsafe fn LLVMGetDefaultTargetTriple() -> *mut c_char {
        target_machine::LLVMGetDefaultTargetTriple()
    }

    #[inline]
    pub unsafe fn LLVMTargetMachineEmitToFile(
        target_machine: usize,
        module: usize,
        filepath: *mut c_char,
        codegen_type: c_uint,
        err_msg: *mut *mut c_char,
    ) -> c_int {
        target_machine::LLVMTargetMachineEmitToFile(
            target_machine as _,
            module as _,
            filepath,
            codegen_type as _,
            err_msg,
        )
    }

    #[inline]
    pub unsafe fn LLVMDisposeTargetMachine(tm: usize) {
        target_machine::LLVMDisposeTargetMachine(tm as _)
    }

    #[inline]
    pub unsafe fn LLVMDisposeModule(module: usize) {
        core::LLVMDisposeModule(module as _)
    }

    #[inline]
    pub unsafe fn LLVMSetVisibility(value: usize, vis: c_uint) {
        core::LLVMSetVisibility(value as _, vis as _)
    }

    #[inline]
    pub unsafe fn LLVMSetDLLStorageClass(value: usize, cls: c_uint) {
        core::LLVMSetDLLStorageClass(value as _, cls as _)
    }

    #[inline]
    pub unsafe fn LLVMAddAttributeAtIndex(fnval: usize, idx: u64, attr: usize) {
        core::LLVMAddAttributeAtIndex(fnval as _, idx as _, attr as _)
    }

    #[inline]
    pub unsafe fn LLVMGetFirstGlobal(module: usize) -> usize {
        core::LLVMGetFirstGlobal(module as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetNextGlobal(global: usize) -> usize {
        core::LLVMGetNextGlobal(global as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetFirstFunction(module: usize) -> usize {
        core::LLVMGetFirstFunction(module as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetNextFunction(function: usize) -> usize {
        core::LLVMGetNextFunction(function as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMSetLinkage(value: usize, linkage: c_uint) {
        core::LLVMSetLinkage(value as _, linkage as _)
    }

    #[inline]
    pub unsafe fn LLVMGetValueName2(value: usize, len: *mut usize) -> *const c_char {
        core::LLVMGetValueName2(value as _, len)
    }

    #[inline]
    pub unsafe fn LLVMIsDeclaration(global: usize) -> u8 {
        core::LLVMIsDeclaration(global as _)
    }

    #[inline]
    pub unsafe fn LLVMVerifyModule(
        module: usize,
        action: c_uint,
        err: *mut *mut c_char,
    ) -> c_int {
        analysis::LLVMVerifyModule(module as _, action as _, err)
    }

    #[inline]
    pub unsafe fn LLVMCountBasicBlocks(fnval: usize) -> c_uint {
        core::LLVMCountBasicBlocks(fnval as _)
    }

    #[inline]
    pub unsafe fn LLVMGetEntryBasicBlock(fnval: usize) -> usize {
        core::LLVMGetEntryBasicBlock(fnval as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMGetFirstInstruction(bb: usize) -> usize {
        core::LLVMGetFirstInstruction(bb as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMPositionBuilderBefore(builder: usize, instr: usize) {
        core::LLVMPositionBuilderBefore(builder as _, instr as _)
    }

    #[inline]
    pub unsafe fn LLVMCreateStringAttribute(
        ctx: usize,
        key: *const c_char,
        key_len: usize,
        value: *const c_char,
        value_len: usize,
    ) -> usize {
        core::LLVMCreateStringAttribute(ctx as _, key, key_len as _, value, value_len as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMModuleCreateWithNameInContext(name: *const c_char, ctx: usize) -> usize {
        core::LLVMModuleCreateWithNameInContext(name, ctx as _) as usize
    }

    #[inline]
    pub unsafe fn LLVMWriteBitcodeToFile(module: usize, path: *const c_char) -> c_int {
        core::LLVMWriteBitcodeToFile(module as _, path)
    }

    #[inline]
    pub unsafe fn LLVMPrintModuleToString(module: usize) -> *mut c_char {
        core::LLVMPrintModuleToString(module as _)
    }

    #[inline]
    pub unsafe fn LLVMPrintModuleToFile(
        module: usize,
        path: *const c_char,
        err_msg: *mut *mut c_char,
    ) -> c_int {
        core::LLVMPrintModuleToFile(module as _, path, err_msg)
    }

    #[inline]
    pub unsafe fn LLVMDisposeMessage(message: *mut c_char) {
        core::LLVMDisposeMessage(message)
    }

    #[inline]
    pub unsafe fn LLVMInitializeAllTargetInfos() {
        target::LLVMInitializeAllTargetInfos()
    }

    #[inline]
    pub unsafe fn LLVMInitializeAllTargets() {
        target::LLVMInitializeAllTargets()
    }

    #[inline]
    pub unsafe fn LLVMInitializeAllTargetMCs() {
        target::LLVMInitializeAllTargetMCs()
    }

    #[inline]
    pub unsafe fn LLVMInitializeAllAsmParsers() {
        target::LLVMInitializeAllAsmParsers()
    }

    #[inline]
    pub unsafe fn LLVMInitializeAllAsmPrinters() {
        target::LLVMInitializeAllAsmPrinters()
    }
