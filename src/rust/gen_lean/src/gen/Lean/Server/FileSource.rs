// Lean compiler output
// Module: Lean.Server.FileSource
// Imports: Lean.Data.Lsp
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getArrVal_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::{initialize_Lean_Data_Lsp, runtime_initialize_Lean_Data_Lsp};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_panic_fn_borrowed;
pub static l_Lean_Lsp_instFileSourceLocation___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Lsp_instFileSourceLocation___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFileSourceLocation___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceLocation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceLocation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceLocation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceTextDocumentIdentifier: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentIdentifier___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceTextDocumentEdit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentEdit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceTextDocumentItem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceTextDocumentPositionParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceCompletionParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceCompletionParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceHoverParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDeclarationParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDefinitionParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceTypeDefinitionParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceReferenceParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceReferenceParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceReferenceParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceReferenceParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceReferenceParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDocumentHighlightParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDocumentSymbolParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceSemanticTokensParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceSemanticTokensRangeParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceFoldingRangeParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourcePlainGoalParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourcePlainTermGoalParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceTextDocumentPositionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceRpcConnectParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceRpcCallParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceRpcCallParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceRpcCallParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceRpcCallParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceRpcCallParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceRpcReleaseParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceRpcReleaseParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceRpcKeepAliveParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceRpcKeepAliveParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceCodeActionParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceCodeActionParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCodeActionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceCodeActionParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCodeActionParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceInlayHintParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceInlayHintParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceInlayHintParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceInlayHintParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceInlayHintParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceSignatureHelpParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceSignatureHelpParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceDocumentColorParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceDocumentColorParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 70, 105, 108, 101, 83, 111, 117,
        114, 99, 101, 0,
    ],
};
static mut l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 76, 115, 112, 46, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110,
        73, 116, 101, 109, 46, 103, 101, 116, 70, 105, 108, 101, 83, 111, 117, 114, 99, 101, 33, 0,
    ],
};
static mut l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 114, 105, 0],
};
static mut l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 109, 112, 108, 101, 116, 105,
        111, 110, 32, 105, 116, 101, 109, 32, 100, 97, 116, 97, 58, 32, 0,
    ],
};
static mut l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        110, 111, 32, 100, 97, 116, 97, 32, 112, 97, 114, 97, 109, 32, 111, 110, 32, 99, 111, 109,
        112, 108, 101, 116, 105, 111, 110, 32, 105, 116, 101, 109, 32, 0,
    ],
};
static mut l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFileSourceCompletionItem___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_CompletionItem_getFileSource_x21 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFileSourceCompletionItem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFileSourceCompletionItem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFileSourceCompletionItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Lsp_instFileSourceLocation___lam__0(
    mut v_l_188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_189_ = crate::leanh::lean_ctor_get(v_l_188_, 0);
    crate::leanh::lean_inc_ref(v_uri_189_);
    return v_uri_189_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceLocation___lam__0___boxed(
    mut v_l_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_191_ = l_Lean_Lsp_instFileSourceLocation___lam__0(v_l_190_);
    crate::leanh::lean_dec_ref(v_l_190_);
    return v_res_191_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(
    mut v_i_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_i_194_);
    return v_i_194_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0___boxed(
    mut v_i_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Lean_Lsp_instFileSourceTextDocumentIdentifier___lam__0(v_i_195_);
    crate::leanh::lean_dec_ref(v_i_195_);
    return v_res_196_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(
    mut v_i_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_200_ = crate::leanh::lean_ctor_get(v_i_199_, 0);
    crate::leanh::lean_inc_ref(v_uri_200_);
    return v_uri_200_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0___boxed(
    mut v_i_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Lean_Lsp_instFileSourceVersionedTextDocumentIdentifier___lam__0(v_i_201_);
    crate::leanh::lean_dec_ref(v_i_201_);
    return v_res_202_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(
    mut v_e_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_206_ = crate::leanh::lean_ctor_get(v_e_205_, 0);
    v_uri_207_ = crate::leanh::lean_ctor_get(v_textDocument_206_, 0);
    crate::leanh::lean_inc_ref(v_uri_207_);
    return v_uri_207_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0___boxed(
    mut v_e_208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_209_ = l_Lean_Lsp_instFileSourceTextDocumentEdit___lam__0(v_e_208_);
    crate::leanh::lean_dec_ref(v_e_208_);
    return v_res_209_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(
    mut v_i_212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_213_ = crate::leanh::lean_ctor_get(v_i_212_, 0);
    crate::leanh::lean_inc_ref(v_uri_213_);
    return v_uri_213_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0___boxed(
    mut v_i_214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Lean_Lsp_instFileSourceTextDocumentItem___lam__0(v_i_214_);
    crate::leanh::lean_dec_ref(v_i_214_);
    return v_res_215_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(
    mut v_p_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_219_ = crate::leanh::lean_ctor_get(v_p_218_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_219_);
    return v_textDocument_219_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0___boxed(
    mut v_p_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_221_ = l_Lean_Lsp_instFileSourceTextDocumentPositionParams___lam__0(v_p_220_);
    crate::leanh::lean_dec_ref(v_p_220_);
    return v_res_221_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(
    mut v_p_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_225_ = crate::leanh::lean_ctor_get(v_p_224_, 0);
    crate::leanh::lean_inc_ref(v_uri_225_);
    return v_uri_225_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0___boxed(
    mut v_p_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_227_ = l_Lean_Lsp_instFileSourceDidOpenTextDocumentParams___lam__0(v_p_226_);
    crate::leanh::lean_dec_ref(v_p_226_);
    return v_res_227_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(
    mut v_p_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_231_ = crate::leanh::lean_ctor_get(v_p_230_, 0);
    v_uri_232_ = crate::leanh::lean_ctor_get(v_textDocument_231_, 0);
    crate::leanh::lean_inc_ref(v_uri_232_);
    return v_uri_232_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0___boxed(
    mut v_p_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l_Lean_Lsp_instFileSourceDidChangeTextDocumentParams___lam__0(v_p_233_);
    crate::leanh::lean_dec_ref(v_p_233_);
    return v_res_234_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(
    mut v_p_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_238_ = crate::leanh::lean_ctor_get(v_p_237_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_238_);
    return v_textDocument_238_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0___boxed(
    mut v_p_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_240_ = l_Lean_Lsp_instFileSourceDidSaveTextDocumentParams___lam__0(v_p_239_);
    crate::leanh::lean_dec_ref(v_p_239_);
    return v_res_240_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(
    mut v_p_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_p_243_);
    return v_p_243_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0___boxed(
    mut v_p_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_245_ = l_Lean_Lsp_instFileSourceDidCloseTextDocumentParams___lam__0(v_p_244_);
    crate::leanh::lean_dec_ref(v_p_244_);
    return v_res_245_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceCompletionParams___lam__0(
    mut v_h_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_249_ = crate::leanh::lean_ctor_get(v_h_248_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_249_);
    return v_textDocument_249_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceCompletionParams___lam__0___boxed(
    mut v_h_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_251_ = l_Lean_Lsp_instFileSourceCompletionParams___lam__0(v_h_250_);
    crate::leanh::lean_dec_ref(v_h_250_);
    return v_res_251_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceReferenceParams___lam__0(
    mut v_h_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTextDocumentPositionParams_259_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_textDocument_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toTextDocumentPositionParams_259_ = crate::leanh::lean_ctor_get(v_h_258_, 0);
    v_textDocument_260_ = crate::leanh::lean_ctor_get(v_toTextDocumentPositionParams_259_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_260_);
    return v_textDocument_260_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceReferenceParams___lam__0___boxed(
    mut v_h_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ = l_Lean_Lsp_instFileSourceReferenceParams___lam__0(v_h_261_);
    crate::leanh::lean_dec_ref(v_h_261_);
    return v_res_262_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(
    mut v_p_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_266_ = crate::leanh::lean_ctor_get(v_p_265_, 0);
    crate::leanh::lean_inc_ref(v_uri_266_);
    return v_uri_266_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0___boxed(
    mut v_p_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_Lsp_instFileSourceWaitForDiagnosticsParams___lam__0(v_p_267_);
    crate::leanh::lean_dec_ref(v_p_267_);
    return v_res_268_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(
    mut v_p_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_275_ = crate::leanh::lean_ctor_get(v_p_274_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_275_);
    return v_textDocument_275_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0___boxed(
    mut v_p_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Lean_Lsp_instFileSourceSemanticTokensRangeParams___lam__0(v_p_276_);
    crate::leanh::lean_dec_ref(v_p_276_);
    return v_res_277_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(
    mut v_p_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTextDocumentPositionParams_285_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_textDocument_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toTextDocumentPositionParams_285_ = crate::leanh::lean_ctor_get(v_p_284_, 0);
    v_textDocument_286_ = crate::leanh::lean_ctor_get(v_toTextDocumentPositionParams_285_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_286_);
    return v_textDocument_286_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceRpcCallParams___lam__0___boxed(
    mut v_p_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Lean_Lsp_instFileSourceRpcCallParams___lam__0(v_p_287_);
    crate::leanh::lean_dec_ref(v_p_287_);
    return v_res_288_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(
    mut v_p_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_292_ = crate::leanh::lean_ctor_get(v_p_291_, 0);
    crate::leanh::lean_inc_ref(v_uri_292_);
    return v_uri_292_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0___boxed(
    mut v_p_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Lean_Lsp_instFileSourceRpcReleaseParams___lam__0(v_p_293_);
    crate::leanh::lean_dec_ref(v_p_293_);
    return v_res_294_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(
    mut v_p_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_298_ = crate::leanh::lean_ctor_get(v_p_297_, 0);
    crate::leanh::lean_inc_ref(v_uri_298_);
    return v_uri_298_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0___boxed(
    mut v_p_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Lean_Lsp_instFileSourceRpcKeepAliveParams___lam__0(v_p_299_);
    crate::leanh::lean_dec_ref(v_p_299_);
    return v_res_300_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(
    mut v_p_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_304_ = crate::leanh::lean_ctor_get(v_p_303_, 2);
    crate::leanh::lean_inc_ref(v_textDocument_304_);
    return v_textDocument_304_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceCodeActionParams___lam__0___boxed(
    mut v_p_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = l_Lean_Lsp_instFileSourceCodeActionParams___lam__0(v_p_305_);
    crate::leanh::lean_dec_ref(v_p_305_);
    return v_res_306_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(
    mut v_p_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_310_ = crate::leanh::lean_ctor_get(v_p_309_, 1);
    crate::leanh::lean_inc_ref(v_textDocument_310_);
    return v_textDocument_310_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceInlayHintParams___lam__0___boxed(
    mut v_p_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Lean_Lsp_instFileSourceInlayHintParams___lam__0(v_p_311_);
    crate::leanh::lean_dec_ref(v_p_311_);
    return v_res_312_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(
    mut v_p_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTextDocumentPositionParams_316_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_textDocument_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toTextDocumentPositionParams_316_ = crate::leanh::lean_ctor_get(v_p_315_, 0);
    v_textDocument_317_ = crate::leanh::lean_ctor_get(v_toTextDocumentPositionParams_316_, 0);
    crate::leanh::lean_inc_ref(v_textDocument_317_);
    return v_textDocument_317_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0___boxed(
    mut v_p_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Lean_Lsp_instFileSourceSignatureHelpParams___lam__0(v_p_318_);
    crate::leanh::lean_dec_ref(v_p_318_);
    return v_res_319_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(
    mut v_p_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_textDocument_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_textDocument_323_ = crate::leanh::lean_ctor_get(v_p_322_, 2);
    crate::leanh::lean_inc_ref(v_textDocument_323_);
    return v_textDocument_323_;
}
pub unsafe fn l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0___boxed(
    mut v_p_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ = l_Lean_Lsp_instFileSourceDocumentColorParams___lam__0(v_p_324_);
    crate::leanh::lean_dec_ref(v_p_324_);
    return v_res_325_;
}
pub unsafe fn l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(
    mut v_msg_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_330_ = l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0;
    v___x_331_ = lean_panic_fn_borrowed(v___x_330_, v_msg_329_);
    return v___x_331_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(
    mut v_j_332_: *mut crate::leanh::LeanObject,
    mut v_k_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = l_Lean_Json_getObjValD(v_j_332_, v_k_333_);
    v___x_335_ = l_Lean_Json_getStr_x3f(v___x_334_);
    return v___x_335_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1___boxed(
    mut v_j_336_: *mut crate::leanh::LeanObject,
    mut v_k_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_338_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(
            v_j_336_, v_k_337_,
        );
    crate::leanh::lean_dec_ref(v_k_337_);
    return v_res_338_;
}
pub unsafe fn l_Lean_Lsp_CompletionItem_getFileSource_x21(
    mut v_item_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_x3f_357_ = crate::leanh::lean_ctor_get(v_item_344_, 6);
                if crate::leanh::lean_obj_tag(v_data_x3f_357_) == 1 {
                    crate::leanh::lean_inc_ref(v_data_x3f_357_);
                    crate::leanh::lean_dec_ref(v_item_344_);
                    v_val_358_ = crate::leanh::lean_ctor_get(v_data_x3f_357_, 0);
                    crate::leanh::lean_inc(v_val_358_);
                    crate::leanh::lean_dec_ref_known(v_data_x3f_357_, 1);
                    match crate::leanh::lean_obj_tag(v_val_358_) {
                        5 => {
                            v___x_359_ = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2;
                            v___x_360_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__1(v_val_358_, v___x_359_);
                            v___y_354_ = v___x_360_;
                            state = 2;
                            continue;
                        }
                        4 => {
                            v___x_361_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_362_ = l_Lean_Json_getArrVal_x3f(v_val_358_, v___x_361_);
                            if crate::leanh::lean_obj_tag(v___x_362_) == 0 {
                                v_a_363_ = crate::leanh::lean_ctor_get(v___x_362_, 0);
                                crate::leanh::lean_inc(v_a_363_);
                                crate::leanh::lean_dec_ref_known(v___x_362_, 1);
                                v_a_346_ = v_a_363_;
                                state = 1;
                                continue;
                            } else {
                                v_a_364_ = crate::leanh::lean_ctor_get(v___x_362_, 0);
                                crate::leanh::lean_inc(v_a_364_);
                                crate::leanh::lean_dec_ref_known(v___x_362_, 1);
                                v___x_365_ = l_Lean_Json_getStr_x3f(v_a_364_);
                                v___y_354_ = v___x_365_;
                                state = 2;
                                continue;
                            }
                        }
                        _ => {
                            v___x_366_ = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__3;
                            v___x_367_ = crate::leanh::lean_unsigned_to_nat(80);
                            v___x_368_ = l_Lean_Json_pretty(v_val_358_, v___x_367_);
                            v___x_369_ = lean_string_append(v___x_366_, v___x_368_);
                            crate::leanh::lean_dec_ref(v___x_368_);
                            v_a_346_ = v___x_369_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_label_370_ = crate::leanh::lean_ctor_get(v_item_344_, 0);
                    crate::leanh::lean_inc_ref(v_label_370_);
                    crate::leanh::lean_dec_ref(v_item_344_);
                    v___x_371_ = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__4;
                    v___x_372_ = lean_string_append(v___x_371_, v_label_370_);
                    crate::leanh::lean_dec_ref(v_label_370_);
                    v_a_346_ = v___x_372_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_347_ = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0;
                v___x_348_ = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1;
                v___x_349_ = crate::leanh::lean_unsigned_to_nat(144);
                v___x_350_ = crate::leanh::lean_unsigned_to_nat(22);
                v___x_351_ = l_mkPanicMessageWithDecl(
                    v___x_347_, v___x_348_, v___x_349_, v___x_350_, v_a_346_,
                );
                crate::leanh::lean_dec_ref(v_a_346_);
                v___x_352_ =
                    l_panic___at___00Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(v___x_351_);
                return v___x_352_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_354_) == 0 {
                    v_a_355_ = crate::leanh::lean_ctor_get(v___y_354_, 0);
                    crate::leanh::lean_inc(v_a_355_);
                    crate::leanh::lean_dec_ref_known(v___y_354_, 1);
                    v_a_346_ = v_a_355_;
                    state = 1;
                    continue;
                } else {
                    v_a_356_ = crate::leanh::lean_ctor_get(v___y_354_, 0);
                    crate::leanh::lean_inc(v_a_356_);
                    crate::leanh::lean_dec_ref_known(v___y_354_, 1);
                    return v_a_356_;
                }
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileSource(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileSource(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_FileSource(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileSource(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileSource(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_FileSource(builtin);
}
