// Rust implementation of Lean.CompactedRegion save/read.

mod library_module_impl {
    use super::*;
    use std::collections::HashMap;
    use std::ffi::{CStr, CString};
    use std::fs::File;
    use std::io::{Read, Write, Seek};
    use std::ptr::{null, null_mut};

    #[derive(Clone)]
    struct DepRegionInfo {
        m_begin: usize,
        m_base_addr: usize,
        m_size: usize,
    }

    #[derive(Clone)]
    struct LibInfo {
        base_addr: usize,
        id: String,
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        #[cfg(target_os = "linux")]
        {
            use std::ffi::CStr;
            let mut libs: Vec<LibInfo> = Vec::new();
            unsafe extern "C" fn callback(
                info: *mut libc::dl_phdr_info,
                _size: usize,
                data: *mut std::ffi::c_void,
            ) -> std::ffi::c_int {
                let libs = &mut *(data as *mut Vec<LibInfo>);
                let id = if (*info).dlpi_name.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr((*info).dlpi_name).to_string_lossy().into_owned()
                };
                libs.push(LibInfo {
                    base_addr: (*info).dlpi_addr as usize,
                    id,
                });
                0
            }
            libc::dl_iterate_phdr(Some(callback), &mut libs as *mut _ as *mut _);
            libs.sort_by_key(|a| a.base_addr);
            libs
        }
        #[cfg(target_os = "macos")]
        {
            extern "C" {
                fn _dyld_image_count() -> u32;
                fn _dyld_get_image_header(image_index: u32) -> *const std::ffi::c_void;
                fn _dyld_get_image_name(image_index: u32) -> *const std::ffi::c_char;
            }
            let mut libs: Vec<LibInfo> = Vec::new();
            let n = _dyld_image_count();
            for i in 0..n {
                let hdr = _dyld_get_image_header(i);
                if hdr.is_null() { continue; }
                let name = _dyld_get_image_name(i);
                if name.is_null() { continue; }
                let id = std::ffi::CStr::from_ptr(name).to_string_lossy().into_owned();
                libs.push(LibInfo {
                    base_addr: hdr as usize,
                    id,
                });
            }
            libs.sort_by_key(|a| a.base_addr);
            libs
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        Vec::new()
    }

    unsafe fn read_lib_table_from_buffer(mut p: *const u8) -> Vec<(usize, isize)> {
        let mut relocs = Vec::new();
        let mut n: u32 = 0;
        std::ptr::copy_nonoverlapping(p, &mut n as *mut u32 as *mut u8, 4);
        p = p.add(4);
        if n == 0 {
            return relocs;
        }
        let current_libs = get_loaded_libs();
        for _ in 0..n {
            let mut old_base: usize = 0;
            std::ptr::copy_nonoverlapping(p, &mut old_base as *mut usize as *mut u8, 8);
            p = p.add(8);
            let mut len: u32 = 0;
            std::ptr::copy_nonoverlapping(p, &mut len as *mut u32 as *mut u8, 4);
            p = p.add(4);
            let id_slice = std::slice::from_raw_parts(p, len as usize);
            let id = String::from_utf8_lossy(id_slice).into_owned();
            p = p.add(len as usize);
            let mut new_base = 0;
            let mut found = false;
            for lib in &current_libs {
                if lib.id == id {
                    new_base = lib.base_addr;
                    found = true;
                    break;
                }
            }
            if !found {
                panic!("library required for closure relocation is not loaded: {}", id);
            }
            let delta = (new_base as isize) - (old_base as isize);
            relocs.push((old_base, delta));
        }
        relocs.sort_by_key(|e| e.0);
        relocs
    }

    #[repr(C)]
    struct MpzObjectGmp {
        _header: LeanObject,
        _mp_alloc: std::ffi::c_int,
        _mp_size: std::ffi::c_int,
        _mp_d: *mut usize,
    }

    #[repr(C)]
    struct MpzObjectNonGmp {
        _header: LeanObject,
        m_sign: std::ffi::c_int,
        m_size: std::ffi::c_int,
        m_digits: *mut u32,
    }

    fn align_size(sz: usize) -> usize {
        let rem = sz % 8;
        if rem != 0 {
            sz + 8 - rem
        } else {
            sz
        }
    }

    unsafe fn lean_sarray_byte_size(o: *mut LeanObject) -> usize {
        let size = (*(o as *const LeanScalarArray)).m_size;
        let elem_size = (*o).m_other as usize;
        core::mem::size_of::<LeanScalarArray>() + elem_size * size
    }

    unsafe fn lean_string_byte_size(o: *mut LeanObject) -> usize {
        let size = (*(o as *const LeanStringObject)).m_size;
        core::mem::size_of::<LeanStringObject>() + size
    }

    unsafe fn lean_ctor_num_objs(o: *mut LeanObject) -> usize {
        (*o).m_other as usize
    }

    struct CompactedRegion {
        m_begin: usize,
        m_base_addr: usize,
        m_size: usize,
        m_next: *mut u8,
        m_end: *mut u8,
        m_dep_regions: Vec<DepRegionInfo>,
    }

    unsafe fn fix_object_ptr(o: *mut LeanObject, region: &CompactedRegion) -> *mut LeanObject {
        if lean_is_scalar(o) {
            return o;
        }
        let addr = o as usize;
        let self_base = region.m_base_addr;
        if addr >= self_base && addr < self_base + region.m_size {
            return (region.m_begin + (addr - self_base)) as *mut LeanObject;
        }
        for dep in &region.m_dep_regions {
            let dep_base = dep.m_base_addr;
            if addr >= dep_base && addr < dep_base + dep.m_size {
                return (dep.m_begin + (addr - dep_base)) as *mut LeanObject;
            }
        }
        panic!("pointer outside compacted region: {:p}", o);
    }

    unsafe fn fix_constructor(o: *mut LeanObject, region: &mut CompactedRegion) {
        let num_objs = lean_ctor_num_objs(o);
        let ptrs = o.add(1) as *mut *mut LeanObject;
        for i in 0..num_objs {
            let field_ptr = ptrs.add(i);
            *field_ptr = fix_object_ptr(*field_ptr, region);
        }
        region.m_next = region.m_next.add(align_size(crate::lean_object_byte_size(o)));
    }

    unsafe fn fix_array(o: *mut LeanObject, region: &mut CompactedRegion) {
        let size = lean_array_size(o);
        let ptrs = lean_array_cptr(o);
        for i in 0..size {
            let field_ptr = ptrs.add(i);
            *field_ptr = fix_object_ptr(*field_ptr, region);
        }
        region.m_next = region.m_next.add(align_size(crate::lean_object_byte_size(o)));
    }

    unsafe fn fix_sarray(o: *mut LeanObject, region: &mut CompactedRegion) {
        region.m_next = region.m_next.add(align_size(lean_sarray_byte_size(o)));
    }

    unsafe fn fix_mpz(o: *mut LeanObject, use_gmp: bool, region: &mut CompactedRegion) {
        if use_gmp {
            let mpz = o as *mut MpzObjectGmp;
            let d_rel = (*mpz)._mp_d as usize;
            (*mpz)._mp_d = (region.m_begin + (d_rel - region.m_base_addr)) as *mut usize;
            let size = (*mpz)._mp_size.abs() as usize;
            region.m_next = region.m_next.add(align_size(core::mem::size_of::<MpzObjectGmp>() + size * core::mem::size_of::<usize>()));
        } else {
            let mpz = o as *mut MpzObjectNonGmp;
            (*mpz).m_digits = (o as *mut u8).add(core::mem::size_of::<MpzObjectNonGmp>()) as *mut u32;
            let size = (*mpz).m_size.abs() as usize;
            region.m_next = region.m_next.add(align_size(core::mem::size_of::<MpzObjectNonGmp>() + size * core::mem::size_of::<u32>()));
        }
    }

    unsafe fn fix_thunk(o: *mut LeanObject, region: &mut CompactedRegion) {
        let thunk = o as *mut LeanThunkObject;
        (*thunk).m_value = fix_object_ptr((*thunk).m_value, region);
        region.m_next = region.m_next.add(align_size(core::mem::size_of::<LeanThunkObject>()));
    }

    unsafe fn fix_ref(o: *mut LeanObject, region: &mut CompactedRegion) {
        let r = o as *mut LeanRefObject;
        (*r).m_value = fix_object_ptr((*r).m_value, region);
        region.m_next = region.m_next.add(align_size(core::mem::size_of::<LeanRefObject>()));
    }

    unsafe fn fix_task(o: *mut LeanObject, region: &mut CompactedRegion) {
        let t = o as *mut LeanTaskObject;
        (*t).m_value = fix_object_ptr((*t).m_value, region);
        region.m_next = region.m_next.add(align_size(core::mem::size_of::<LeanTaskObject>()));
    }

    unsafe fn fix_promise(o: *mut LeanObject, region: &mut CompactedRegion) {
        let p = o as *mut LeanPromiseObject;
        (*p).result = fix_object_ptr((*p).result, region);
        region.m_next = region.m_next.add(align_size(core::mem::size_of::<LeanPromiseObject>()));
    }

    unsafe fn fix_closure(o: *mut LeanObject, region: &mut CompactedRegion) {
        let num_fixed = (*(o as *const LeanClosureObject)).m_num_fixed as usize;
        let ptrs = (o as *mut u8).add(24) as *mut *mut LeanObject;
        for i in 0..num_fixed {
            let field_ptr = ptrs.add(i);
            *field_ptr = fix_object_ptr(*field_ptr, region);
        }
        region.m_next = region.m_next.add(align_size(crate::lean_object_byte_size(o)));
    }

    unsafe fn extract_dep_regions(odep_regions: *mut LeanObject) -> Vec<DepRegionInfo> {
        let mut result = Vec::new();
        if odep_regions.is_null() || lean_is_scalar(odep_regions) {
            return result;
        }
        let n = lean_array_size(odep_regions);
        for i in 0..n {
            let region_usize = lean_unbox(lean_array_get(odep_regions, i));
            if region_usize != 0 {
                let r = &*(region_usize as *const crate::runtime_compact_impl::RustCompactedRegion);
                if !r.mmap_ptr.is_null() {
                    result.push(DepRegionInfo {
                        m_begin: r.m_begin,
                        m_base_addr: r.m_base_addr,
                        m_size: r.size,
                    });
                }
            }
        }
        result.sort_by_key(|a| a.m_base_addr);
        result
    }

    const MAGIC: &[u8; 8] = b"LRGN0001";

    #[derive(Clone, Copy)]
    enum RefValue {
        Null,
        Scalar(usize),
        Node(usize),
    }

    enum NodeKind {
        Constructor {
            tag: u8,
            num_objs: usize,
            scalar_size: usize,
            scalar_bytes: Vec<u8>,
            fields: Vec<RefValue>,
        },
        Array {
            size: usize,
            fields: Vec<RefValue>,
        },
        SArray {
            elem_size: usize,
            size: usize,
            bytes: Vec<u8>,
        },
        String {
            size: usize,
            len: usize,
            bytes: Vec<u8>,
        },
        Mpz {
            bytes: Vec<u8>,
        },
        Thunk {
            closure: RefValue,
            value: RefValue,
        },
        Ref {
            value: RefValue,
        },
        Promise {
            result: RefValue,
        },
        Task {
            value: RefValue,
        },
    }

    struct NodeRecord {
        kind: NodeKind,
    }

    struct SaveGraph {
        seen: HashMap<usize, usize>,
        order: Vec<*mut LeanObject>,
    }

    impl SaveGraph {
        fn new() -> Self {
            Self { seen: HashMap::new(), order: Vec::new() }
        }

        unsafe fn discover_ref(&mut self, obj: *mut LeanObject) -> Result<RefValue, String> {
            if obj.is_null() {
                return Ok(RefValue::Null);
            }
            if lean_is_scalar(obj) {
                return Ok(RefValue::Scalar(obj as usize));
            }
            Ok(RefValue::Node(self.discover_obj(obj)?))
        }

        unsafe fn discover_obj(&mut self, obj: *mut LeanObject) -> Result<usize, String> {
            let addr = obj as usize;
            if let Some(&id) = self.seen.get(&addr) {
                return Ok(id);
            }
            let id = self.order.len();
            self.seen.insert(addr, id);
            self.order.push(obj);

            match lean_ptr_tag(obj) {
                246 => {
                    let len = lean_array_size(obj);
                    for i in 0..len {
                        self.discover_ref(lean_array_get(obj, i))?;
                    }
                }
                247 => {
                    return Err("LeanStructArray objects are not supported by the Rust compacted-region codec yet".to_string());
                }
                248 => {}
                249 => {}
                250 => {}
                244 => {
                    self.discover_ref((obj as *mut LeanPromiseObject).read().result)?;
                }
                245 => {
                    return Err("closures cannot be compacted in the Rust runtime yet".to_string());
                }
                251 => {
                    let thunk = obj as *mut LeanThunkObject;
                    self.discover_ref((*thunk).m_closure)?;
                    self.discover_ref((*thunk).m_value)?;
                }
                252 => {
                    let task = obj as *mut LeanTaskObject;
                    if !(*task).m_imp.is_null() {
                        return Err("cannot compact a running task".to_string());
                    }
                    self.discover_ref((*task).m_value)?;
                }
                253 => {
                    self.discover_ref((obj as *mut LeanRefObject).read().m_value)?;
                }
                254 => {
                    return Err("external objects cannot be compacted".to_string());
                }
                _ => {
                    let num_objs = lean_ctor_num_objs_export(obj) as usize;
                    for i in 0..num_objs {
                        self.discover_ref(lean_ctor_get(obj, i))?;
                    }
                }
            }
            Ok(id)
        }

        unsafe fn build_record(&self, obj: *mut LeanObject) -> Result<NodeRecord, String> {
            Ok(match lean_ptr_tag(obj) {
                246 => {
                    let size = lean_array_size(obj);
                    let mut fields = Vec::with_capacity(size);
                    for i in 0..size {
                        fields.push(self.ref_of(lean_array_get(obj, i)));
                    }
                    NodeRecord { kind: NodeKind::Array { size, fields } }
                }
                247 => return Err("LeanStructArray objects are not supported by the Rust compacted-region codec yet".to_string()),
                248 => {
                    let elem_size = lean_sarray_elem_size(obj) as usize;
                    let size = lean_sarray_size(obj);
                    let bytes = std::slice::from_raw_parts(lean_sarray_cptr(obj), size * elem_size).to_vec();
                    NodeRecord { kind: NodeKind::SArray { elem_size, size, bytes } }
                }
                249 => {
                    let size = lean_string_size(obj);
                    let len = lean_string_len(obj);
                    let bytes = std::slice::from_raw_parts(lean_string_cstr(obj) as *const u8, size).to_vec();
                    NodeRecord { kind: NodeKind::String { size, len, bytes } }
                }
                250 => {
                    let size = super::lean_object_byte_size(obj);
                    let bytes = std::slice::from_raw_parts(obj as *const u8, size).to_vec();
                    NodeRecord { kind: NodeKind::Mpz { bytes } }
                }
                244 => {
                    let result = self.ref_of((obj as *mut LeanPromiseObject).read().result);
                    NodeRecord { kind: NodeKind::Promise { result } }
                }
                245 => return Err("closures cannot be compacted in the Rust runtime yet".to_string()),
                251 => {
                    let thunk = obj as *mut LeanThunkObject;
                    let closure = self.ref_of((*thunk).m_closure);
                    let value = self.ref_of((*thunk).m_value);
                    NodeRecord { kind: NodeKind::Thunk { closure, value } }
                }
                252 => {
                    let task = obj as *mut LeanTaskObject;
                    if !(*task).m_imp.is_null() {
                        return Err("cannot compact a running task".to_string());
                    }
                    let value = self.ref_of((*task).m_value);
                    NodeRecord { kind: NodeKind::Task { value } }
                }
                253 => {
                    let value = self.ref_of((obj as *mut LeanRefObject).read().m_value);
                    NodeRecord { kind: NodeKind::Ref { value } }
                }
                254 => return Err("external objects cannot be compacted".to_string()),
                _ => {
                    let num_objs = lean_ctor_num_objs_export(obj) as usize;
                    let data_sz = lean_object_data_byte_size(obj);
                    let scalar_size = data_sz.saturating_sub(num_objs * core::mem::size_of::<*mut LeanObject>());
                    let scalar_bytes = if scalar_size == 0 {
                        Vec::new()
                    } else {
                        let src = (obj as *const u8).add(core::mem::size_of::<LeanObject>() + num_objs * core::mem::size_of::<*mut LeanObject>());
                        std::slice::from_raw_parts(src, scalar_size).to_vec()
                    };
                    let mut fields = Vec::with_capacity(num_objs);
                    for i in 0..num_objs {
                        fields.push(self.ref_of(lean_ctor_get(obj, i)));
                    }
                    NodeRecord {
                        kind: NodeKind::Constructor {
                            tag: lean_ptr_tag(obj),
                            num_objs,
                            scalar_size,
                            scalar_bytes,
                            fields,
                        },
                    }
                }
            })
        }

        unsafe fn ref_of(&self, obj: *mut LeanObject) -> RefValue {
            if obj.is_null() {
                RefValue::Null
            } else if lean_is_scalar(obj) {
                RefValue::Scalar(obj as usize)
            } else {
                let addr = obj as usize;
                let id = *self.seen.get(&addr).expect("missing node id");
                RefValue::Node(id)
            }
        }
    }

    struct ReadGraph {
        nodes: Vec<NodeRecord>,
    }

    struct BufferCursor<'a> {
        buf: &'a [u8],
        pos: usize,
    }

    impl<'a> BufferCursor<'a> {
        fn new(buf: &'a [u8]) -> Self { Self { buf, pos: 0 } }

        fn read_exact(&mut self, n: usize) -> Result<&'a [u8], String> {
            if self.pos.checked_add(n).filter(|&p| p <= self.buf.len()).is_none() {
                return Err("unexpected EOF while reading compacted region".to_string());
            }
            let s = &self.buf[self.pos..self.pos + n];
            self.pos += n;
            Ok(s)
        }

        fn read_u8(&mut self) -> Result<u8, String> {
            Ok(self.read_exact(1)?[0])
        }

        fn read_u64(&mut self) -> Result<u64, String> {
            let mut b = [0u8; 8];
            b.copy_from_slice(self.read_exact(8)?);
            Ok(u64::from_le_bytes(b))
        }

        fn read_usize(&mut self) -> Result<usize, String> {
            Ok(self.read_u64()? as usize)
        }

        fn read_bytes(&mut self) -> Result<Vec<u8>, String> {
            let len = self.read_usize()?;
            Ok(self.read_exact(len)?.to_vec())
        }
    }

    fn write_u8(w: &mut File, v: u8) -> Result<(), String> {
        w.write_all(&[v]).map_err(|e| e.to_string())
    }

    fn write_u64(w: &mut File, v: u64) -> Result<(), String> {
        w.write_all(&v.to_le_bytes()).map_err(|e| e.to_string())
    }

    fn write_usize(w: &mut File, v: usize) -> Result<(), String> {
        write_u64(w, v as u64)
    }

    fn write_bytes(w: &mut File, bytes: &[u8]) -> Result<(), String> {
        write_usize(w, bytes.len())?;
        w.write_all(bytes).map_err(|e| e.to_string())
    }

    fn read_ref(cur: &mut BufferCursor<'_>) -> Result<RefValue, String> {
        match cur.read_u8()? {
            0 => Ok(RefValue::Null),
            1 => Ok(RefValue::Scalar(cur.read_usize()?)),
            2 => Ok(RefValue::Node(cur.read_usize()?)),
            _ => Err("invalid reference tag in compacted region".to_string()),
        }
    }

    fn write_ref(w: &mut File, r: RefValue) -> Result<(), String> {
        match r {
            RefValue::Null => write_u8(w, 0),
            RefValue::Scalar(v) => {
                write_u8(w, 1)?;
                write_usize(w, v)
            }
            RefValue::Node(id) => {
                write_u8(w, 2)?;
                write_usize(w, id)
            }
        }
    }

    fn alloc_persistent_header(obj: *mut LeanObject, tag: u8) {
        unsafe {
            (*obj).m_rc = 0;
            (*obj).m_cs_sz = 0;
            (*obj).m_other = 0;
            (*obj).m_tag = tag;
        }
    }

    unsafe fn alloc_node(node: &NodeRecord, objs: &[*mut LeanObject]) -> Result<*mut LeanObject, String> {
        Ok(match &node.kind {
            NodeKind::Constructor { tag, num_objs, scalar_size, .. } => {
                let obj = lean_runtime_alloc_ctor_export(*tag as u32, *num_objs as u32, *scalar_size as u32);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::Array { size, .. } => {
                let obj = lean_alloc_array_export(*size, *size);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::SArray { elem_size, size, .. } => {
                let obj = lean_alloc_sarray_export(*elem_size as u32, *size, *size);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::String { size, len, .. } => {
                let obj = lean_alloc_string_export(*size, *size, *len);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::Mpz { bytes } => {
                let obj = lean_alloc_small_object_export(bytes.len()) as *mut LeanObject;
                (*obj).m_rc = 0;
                (*obj).m_cs_sz = bytes.len() as u16;
                (*obj).m_other = 0;
                (*obj).m_tag = 250;
                obj
            }
            NodeKind::Thunk { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanThunkObject>()) as *mut LeanThunkObject;
                alloc_persistent_header(obj as *mut LeanObject, 251);
                obj as *mut LeanObject
            }
            NodeKind::Ref { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanRefObject>()) as *mut LeanRefObject;
                alloc_persistent_header(obj as *mut LeanObject, 253);
                obj as *mut LeanObject
            }
            NodeKind::Promise { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanPromiseObject>()) as *mut LeanPromiseObject;
                alloc_persistent_header(obj as *mut LeanObject, 244);
                obj as *mut LeanObject
            }
            NodeKind::Task { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
                alloc_persistent_header(obj as *mut LeanObject, 252);
                obj as *mut LeanObject
            }
        })
    }

    unsafe fn resolve_ref(r: RefValue, objs: &[*mut LeanObject]) -> *mut LeanObject {
        match r {
            RefValue::Null => null_mut(),
            RefValue::Scalar(v) => v as *mut LeanObject,
            RefValue::Node(id) => objs[id],
        }
    }

    fn describe_file_path(path: *mut LeanObject) -> Result<String, String> {
        Ok(unsafe { crate::cstr_lossy_to_string(lean_string_cstr(path)) })
    }

    fn read_file_bytes(path: &str) -> Result<Vec<u8>, String> {
        let mut f = File::open(path).map_err(|e| e.to_string())?;
        let mut buf = Vec::new();
        f.read_to_end(&mut buf).map_err(|e| e.to_string())?;
        Ok(buf)
    }

    fn write_file_bytes(path: &str, bytes: &[u8]) -> Result<(), String> {
        let mut f = File::create(path).map_err(|e| e.to_string())?;
        f.write_all(bytes).map_err(|e| e.to_string())
    }

    fn parse_graph(buf: &[u8]) -> Result<(RefValue, ReadGraph), String> {
        let mut cur = BufferCursor::new(buf);
        if cur.read_exact(MAGIC.len())? != MAGIC {
            return Err("invalid compacted region magic".to_string());
        }
        let version = cur.read_u64()?;
        if version != 1 && version != 2 {
            return Err("unsupported Rust compacted region graph version".to_string());
        }
        let root = read_ref(&mut cur)?;
        let n_nodes = cur.read_usize()?;
        let mut nodes = Vec::with_capacity(n_nodes);
        for _ in 0..n_nodes {
            let kind = cur.read_u8()?;
            let node = match kind {
                0 => return Err("scalar nodes are not stored explicitly".to_string()),
                1 => {
                    let tag = cur.read_u8()?;
                    let num_objs = cur.read_usize()?;
                    let scalar_size = cur.read_usize()?;
                    let scalar_bytes = cur.read_bytes()?;
                    let mut fields = Vec::with_capacity(num_objs);
                    for _ in 0..num_objs {
                        fields.push(read_ref(&mut cur)?);
                    }
                    NodeRecord { kind: NodeKind::Constructor { tag, num_objs, scalar_size, scalar_bytes, fields } }
                }
                2 => {
                    let size = cur.read_usize()?;
                    if version == 1 {
                        let _capacity = cur.read_usize()?;
                    }
                    let mut fields = Vec::with_capacity(size);
                    for _ in 0..size {
                        fields.push(read_ref(&mut cur)?);
                    }
                    NodeRecord { kind: NodeKind::Array { size, fields } }
                }
                3 => {
                    let elem_size = cur.read_usize()?;
                    let size = cur.read_usize()?;
                    if version == 1 {
                        let _capacity = cur.read_usize()?;
                    }
                    let bytes = cur.read_bytes()?;
                    NodeRecord { kind: NodeKind::SArray { elem_size, size, bytes } }
                }
                4 => {
                    let size = cur.read_usize()?;
                    if version == 1 {
                        let _capacity = cur.read_usize()?;
                    }
                    let len = cur.read_usize()?;
                    let bytes = cur.read_bytes()?;
                    NodeRecord { kind: NodeKind::String { size, len, bytes } }
                }
                5 => {
                    let bytes = cur.read_bytes()?;
                    NodeRecord { kind: NodeKind::Mpz { bytes } }
                }
                6 => {
                    let closure = read_ref(&mut cur)?;
                    let value = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Thunk { closure, value } }
                }
                7 => {
                    let value = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Ref { value } }
                }
                8 => {
                    let result = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Promise { result } }
                }
                9 => {
                    let value = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Task { value } }
                }
                _ => return Err("unknown compacted region node kind".to_string()),
            };
            nodes.push(node);
        }
        if cur.pos != buf.len() {
            return Err("trailing bytes in compacted region".to_string());
        }
        Ok((root, ReadGraph { nodes }))
    }

    unsafe fn materialize_graph(root: RefValue, graph: ReadGraph) -> Result<(*mut LeanObject, Vec<*mut LeanObject>), String> {
        let mut objs = vec![null_mut(); graph.nodes.len()];
        let mut total_size = 0usize;
        for (i, node) in graph.nodes.iter().enumerate() {
            let obj = alloc_node(node, &objs)?;
            total_size = total_size.saturating_add(super::lean_object_byte_size(obj));
            objs[i] = obj;
        }

        for (i, node) in graph.nodes.iter().enumerate() {
            let obj = objs[i];
            match &node.kind {
                NodeKind::Constructor { num_objs, scalar_size, scalar_bytes, fields, .. } => {
                    let ptrs = (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject;
                    for (j, field) in fields.iter().enumerate().take(*num_objs) {
                        *ptrs.add(j) = resolve_ref(*field, &objs);
                    }
                    let scalar_dst = (obj as *mut u8).add(core::mem::size_of::<LeanObject>() + num_objs * core::mem::size_of::<*mut LeanObject>());
                    std::ptr::copy_nonoverlapping(scalar_bytes.as_ptr(), scalar_dst, *scalar_size);
                }
                NodeKind::Array { size, fields } => {
                    let ptrs = super::lean_array_cptr(obj);
                    for (j, field) in fields.iter().enumerate().take(*size) {
                        ptrs.add(j).write(resolve_ref(*field, &objs));
                    }
                }
                NodeKind::SArray { elem_size, bytes, .. } => {
                    let dst = super::lean_sarray_cptr(obj) as *mut u8;
                    std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
                    let _ = elem_size;
                }
                NodeKind::String { bytes, .. } => {
                    let dst = super::lean_string_cstr(obj) as *mut u8;
                    std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
                }
                NodeKind::Mpz { bytes } => {
                    let dst = obj as *mut u8;
                    std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
                }
                NodeKind::Thunk { closure, value } => {
                    let thunk = obj as *mut LeanThunkObject;
                    (*thunk).m_closure = resolve_ref(*closure, &objs);
                    (*thunk).m_value = resolve_ref(*value, &objs);
                }
                NodeKind::Ref { value } => {
                    let r = obj as *mut LeanRefObject;
                    (*r).m_value = resolve_ref(*value, &objs);
                }
                NodeKind::Promise { result } => {
                    let p = obj as *mut LeanPromiseObject;
                    (*p).result = resolve_ref(*result, &objs);
                }
                NodeKind::Task { value } => {
                    let t = obj as *mut LeanTaskObject;
                    (*t).m_value = resolve_ref(*value, &objs);
                    (*t).m_imp = null_mut();
                }
            }
        }

        let root = match root {
            RefValue::Null => null_mut(),
            RefValue::Scalar(v) => v as *mut LeanObject,
            RefValue::Node(id) => objs[id],
        };
        Ok((root, objs))
    }

    fn serialize_ref<W: Write>(w: &mut W, r: RefValue) -> Result<(), String> {
        match r {
            RefValue::Null => {
                w.write_all(&[0]).map_err(|e| e.to_string())
            }
            RefValue::Scalar(v) => {
                w.write_all(&[1]).map_err(|e| e.to_string())?;
                w.write_all(&(v as u64).to_le_bytes()).map_err(|e| e.to_string())
            }
            RefValue::Node(id) => {
                w.write_all(&[2]).map_err(|e| e.to_string())?;
                w.write_all(&(id as u64).to_le_bytes()).map_err(|e| e.to_string())
            }
        }
    }

    fn serialize_graph(root: RefValue, graph: &[NodeRecord]) -> Result<Vec<u8>, String> {
        let mut out = Vec::new();
        out.write_all(MAGIC).map_err(|e| e.to_string())?;
        out.write_all(&2u64.to_le_bytes()).map_err(|e| e.to_string())?;
        serialize_ref(&mut out, root)?;
        out.write_all(&(graph.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
        for node in graph {
            match &node.kind {
                NodeKind::Constructor { tag, num_objs, scalar_size, scalar_bytes, fields } => {
                    out.write_all(&[1, *tag]).map_err(|e| e.to_string())?;
                    out.write_all(&(*num_objs as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*scalar_size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(scalar_bytes.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(scalar_bytes).map_err(|e| e.to_string())?;
                    for field in fields {
                        serialize_ref(&mut out, *field)?;
                    }
                }
                NodeKind::Array { size, fields } => {
                    out.write_all(&[2]).map_err(|e| e.to_string())?;
                    out.write_all(&(*size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    for field in fields {
                        serialize_ref(&mut out, *field)?;
                    }
                }
                NodeKind::SArray { elem_size, size, bytes } => {
                    out.write_all(&[3]).map_err(|e| e.to_string())?;
                    out.write_all(&(*elem_size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(bytes.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(bytes).map_err(|e| e.to_string())?;
                }
                NodeKind::String { size, len, bytes } => {
                    out.write_all(&[4]).map_err(|e| e.to_string())?;
                    out.write_all(&(*size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*len as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(bytes.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(bytes).map_err(|e| e.to_string())?;
                }
                NodeKind::Mpz { bytes } => {
                    out.write_all(&[5]).map_err(|e| e.to_string())?;
                    out.write_all(&(bytes.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(bytes).map_err(|e| e.to_string())?;
                }
                NodeKind::Thunk { closure, value } => {
                    out.write_all(&[6]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *closure)?;
                    serialize_ref(&mut out, *value)?;
                }
                NodeKind::Ref { value } => {
                    out.write_all(&[7]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *value)?;
                }
                NodeKind::Promise { result } => {
                    out.write_all(&[8]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *result)?;
                }
                NodeKind::Task { value } => {
                    out.write_all(&[9]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *value)?;
                }
            }
        }
        Ok(out)
    }

    unsafe fn roundtrip_root(root: *mut LeanObject) -> Result<(RefValue, Vec<NodeRecord>), String> {
        let mut graph = SaveGraph::new();
        let root_ref = graph.discover_ref(root)?;
        let mut records = Vec::with_capacity(graph.order.len());
        for &obj in &graph.order {
            records.push(graph.build_record(obj)?);
        }
        Ok((root_ref, records))
    }

    unsafe fn mk_io_user_error_from_cstr(msg: &CString) -> *mut LeanObject {
        let str_obj = lean_mk_string(msg.as_ptr());
        #[cfg(test)]
        {
            str_obj
        }
        #[cfg(not(test))]
        {
            lean_mk_io_user_error(str_obj)
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_save(
        ofname: *mut LeanObject,
        _module_name: *mut LeanObject,
        odata: *mut LeanObject,
        _odep_regions: *mut LeanObject,
        _oprev: *mut LeanObject,
        _allow_closures: u8,
        _w: *mut LeanObject,
    ) -> *mut LeanObject {
        let result = (|| -> Result<*mut LeanObject, String> {
            let path = describe_file_path(ofname)?;
            let (root_ref, records) = roundtrip_root(odata)?;
            let bytes = serialize_graph(root_ref, &records)?;
            write_file_bytes(&path, &bytes)?;
            Ok(lean_io_result_mk_ok(lean_box(0)))
        })();
        match result {
            Ok(v) => v,
            Err(msg) => {
                let fallback = CString::new("compacted region error").unwrap();
                let cmsg = CString::new(msg).map_err(|e| e.to_string()).ok();
                match cmsg {
                    Some(cmsg) => lean_io_result_mk_error(mk_io_user_error_from_cstr(&cmsg)),
                    None => lean_io_result_mk_error(mk_io_user_error_from_cstr(&fallback)),
                }
            }
        }
    }

    unsafe fn read_rust_format(
        path: &str,
        _w: *mut LeanObject,
    ) -> Result<*mut LeanObject, String> {
        let bytes = read_file_bytes(path)?;
        let (root_ref, graph) = parse_graph(&bytes)?;
        let (root, objs) = materialize_graph(root_ref, graph)?;
        let region = Box::new(crate::runtime_compact_impl::RustCompactedRegion::new(bytes.len(), objs));
        let region_ptr = Box::into_raw(region) as usize;
        let pair = lean_runtime_alloc_ctor_export(0, 2, 0);
        lean_ctor_set(pair, 0, root);
        lean_ctor_set(pair, 1, lean_box(region_ptr));
        Ok(lean_io_result_mk_ok(pair))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_read(
        ofname: *mut LeanObject,
        odep_regions: *mut LeanObject,
        w: *mut LeanObject,
    ) -> *mut LeanObject {
        let result = (|| -> Result<*mut LeanObject, String> {
            let path = describe_file_path(ofname)?;
            let mut file = File::open(&path).map_err(|e| e.to_string())?;
            let metadata = file.metadata().map_err(|e| e.to_string())?;
            let file_size = metadata.len() as usize;
            if file_size < 88 {
                // Cannot be a C++ .olean file since the header is 88 bytes, so it must be Rust format
                return read_rust_format(&path, w);
            }
            let mut header_bytes = [0u8; 88];
            file.read_exact(&mut header_bytes).map_err(|e| e.to_string())?;
            if &header_bytes[0..5] != b"olean" {
                // fallback to Rust format
                return read_rust_format(&path, w);
            }
            
            let version = header_bytes[5];
            let flags = header_bytes[6];
            let mut base_addr: usize = 0;
            std::ptr::copy_nonoverlapping(&header_bytes[80] as *const u8, &mut base_addr as *mut usize as *mut u8, 8);
            if version != 2 && version != 3 {
                return Err("unsupported olean version".to_string());
            }
            let use_gmp = (flags & 1) != 0;

            let mut is_memory_mapped = false;
            let mut mmap_ptr = std::ptr::null_mut();
            
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            {
                use std::os::fd::AsRawFd;
                let fd = file.as_raw_fd();
                let prot = libc::PROT_READ | libc::PROT_WRITE;
                let flags = libc::MAP_PRIVATE;
                let map_addr = libc::mmap(
                    base_addr as *mut _,
                    file_size,
                    prot,
                    flags,
                    fd,
                    0,
                );
                if map_addr != libc::MAP_FAILED && map_addr == base_addr as *mut _ {
                    mmap_ptr = map_addr as *mut u8;
                    is_memory_mapped = true;
                } else {
                    if map_addr != libc::MAP_FAILED {
                        libc::munmap(map_addr, file_size);
                    }
                }
            }

            if mmap_ptr.is_null() {
                mmap_ptr = libc::malloc(file_size) as *mut u8;
                if mmap_ptr.is_null() {
                    return Err("out of memory".to_string());
                }
                is_memory_mapped = false;
                file.seek(std::io::SeekFrom::Start(0)).map_err(|e| e.to_string())?;
                let slice = std::slice::from_raw_parts_mut(mmap_ptr, file_size);
                file.read_exact(slice).map_err(|e| e.to_string())?;
            }

            let dep_regions = extract_dep_regions(odep_regions);
            let mut lib_relocs = Vec::new();
            let mut closure_offsets = Vec::new();
            let mut data_section_off = 88;
            let mut data_section_sz = file_size - 88;
            if version == 3 {
                let mut data_size: usize = 0;
                std::ptr::copy_nonoverlapping(mmap_ptr.add(88), &mut data_size as *mut usize as *mut u8, 8);
                data_section_off = 96;
                data_section_sz = data_size;
                
                let mut p = mmap_ptr.add(96 + data_size);
                let mut num_closure_offsets: u32 = 0;
                std::ptr::copy_nonoverlapping(p, &mut num_closure_offsets as *mut u32 as *mut u8, 4);
                p = p.add(4);
                if num_closure_offsets > 0 {
                    for _ in 0..num_closure_offsets {
                        let mut off: u64 = 0;
                        std::ptr::copy_nonoverlapping(p, &mut off as *mut u64 as *mut u8, 8);
                        p = p.add(8);
                        closure_offsets.push(off as usize);
                    }
                    lib_relocs = read_lib_table_from_buffer(p);
                }
            }

            let m_begin = mmap_ptr.add(data_section_off);
            let m_base_addr = base_addr + data_section_off;
            let needs_fn_reloc = lib_relocs.iter().any(|e| e.1 != 0);
            if needs_fn_reloc && !closure_offsets.is_empty() {
                let begin = m_begin;
                for off in closure_offsets {
                    let fn_field = begin.add(off) as *mut *mut std::ffi::c_void;
                    let func = *fn_field as usize;
                    let mut low = 0;
                    let mut high = lib_relocs.len();
                    while low < high {
                        let mid = (low + high) / 2;
                        if lib_relocs[mid].0 <= func {
                            low = mid + 1;
                        } else {
                            high = mid;
                        }
                    }
                    if low > 0 {
                        let delta = lib_relocs[low - 1].1;
                        if delta != 0 {
                            *fn_field = (func as isize + delta) as *mut std::ffi::c_void;
                        }
                    }
                }
            }

            let mut needs_dep_reloc = false;
            for dep in &dep_regions {
                if dep.m_begin != dep.m_base_addr {
                    needs_dep_reloc = true;
                    break;
                }
            }

            let root_offset_ptr = m_begin as *const usize;
            let root_offset = *root_offset_ptr;
            
            let temp_region = CompactedRegion {
                m_begin: m_begin as usize,
                m_base_addr: m_base_addr,
                m_size: data_section_sz,
                m_next: std::ptr::null_mut(),
                m_end: std::ptr::null_mut(),
                m_dep_regions: dep_regions.clone(),
            };

            let root = if m_begin as usize == m_base_addr && !needs_dep_reloc {
                fix_object_ptr(root_offset as *mut LeanObject, &temp_region)
            } else {
                let mut region = CompactedRegion {
                    m_begin: m_begin as usize,
                    m_base_addr: m_base_addr,
                    m_size: data_section_sz,
                    m_next: m_begin.add(8),
                    m_end: m_begin.add(data_section_sz),
                    m_dep_regions: dep_regions,
                };
                while region.m_next < region.m_end {
                    let curr = region.m_next as *mut LeanObject;
                    let tag = (*curr).m_tag;
                    if tag <= 243 {
                        fix_constructor(curr, &mut region);
                    } else {
                        match tag {
                            246 => fix_array(curr, &mut region),
                            248 => fix_sarray(curr, &mut region),
                            249 => {
                                let sz = lean_string_byte_size(curr);
                                region.m_next = region.m_next.add(align_size(sz));
                            }
                            250 => fix_mpz(curr, use_gmp, &mut region),
                            251 => fix_thunk(curr, &mut region),
                            252 => fix_task(curr, &mut region),
                            244 => fix_promise(curr, &mut region),
                            253 => fix_ref(curr, &mut region),
                            245 => fix_closure(curr, &mut region),
                            _ => panic!("unknown tag: {}", tag),
                        }
                    }
                }
                fix_object_ptr(root_offset as *mut LeanObject, &temp_region)
            };

            let region_ptr = Box::into_raw(Box::new(crate::runtime_compact_impl::RustCompactedRegion {
                size: data_section_sz,
                is_memory_mapped: is_memory_mapped,
                objects: Vec::new(),
                mmap_ptr: mmap_ptr,
                mmap_size: file_size,
                m_begin: m_begin as usize,
                m_base_addr: m_base_addr,
            })) as usize;

            let pair = lean_runtime_alloc_ctor_export(0, 2, 0);
            lean_ctor_set(pair, 0, root);
            lean_ctor_set(pair, 1, lean_box(region_ptr));
            Ok(lean_io_result_mk_ok(pair))
        })();
        match result {
            Ok(v) => v,
            Err(msg) => {
                let fallback = CString::new("compacted region error").unwrap();
                let cmsg = CString::new(msg).map_err(|e| e.to_string()).ok();
                match cmsg {
                    Some(cmsg) => lean_io_result_mk_error(mk_io_user_error_from_cstr(&cmsg)),
                    None => lean_io_result_mk_error(mk_io_user_error_from_cstr(&fallback)),
                }
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::fs;
        use std::ffi::CString;
        use crate::runtime_misc_exports::{lean_thunk_get_own, lean_thunk_pure};
        use std::time::{SystemTime, UNIX_EPOCH};

        unsafe fn temp_path(name: &str) -> String {
            let ts = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
            format!("{}/lean_runtime_{}_{}.olean", std::env::temp_dir().display(), name, ts)
        }

        #[test]
        fn compacted_region_roundtrip_array() {
            unsafe {
                let path = temp_path("array");
                let c_path = CString::new(path.clone()).unwrap();
                let s = lean_mk_string(c_path.as_ptr());
                let a = lean_alloc_array_export(2, 8);
                lean_array_cptr(a).write(lean_box(11));
                lean_array_cptr(a).add(1).write(lean_box(22));
                let save = lean_compacted_region_save(s, null_mut(), a, null_mut(), null_mut(), 0, null_mut());
                if !lean_io_result_is_ok(save) {
                    let err = lean_io_result_get_error(save);
                    let err_str = crate::cstr_lossy_to_string(lean_string_cstr(err));
                    panic!("lean_compacted_region_save failed: {}", err_str);
                }
                let read = lean_compacted_region_read(s, null_mut(), null_mut());
                if !lean_io_result_is_ok(read) {
                    let err = lean_io_result_get_error(read);
                    let err_str = crate::cstr_lossy_to_string(lean_string_cstr(err));
                    panic!("lean_compacted_region_read failed: {}", err_str);
                }
                let pair = lean_io_result_get_value(read);
                let arr = lean_ctor_get(pair, 0);
                assert_eq!(lean_array_size(arr), 2);
                assert_eq!(lean_array_capacity(arr), 2);
                assert_eq!(lean_unbox(lean_array_get(arr, 0)), 11);
                assert_eq!(lean_unbox(lean_array_get(arr, 1)), 22);
                let region = lean_unbox(lean_ctor_get(pair, 1));
                let freed = crate::runtime_compact_impl::lean_compacted_region_free(region, null_mut());
                assert!(lean_io_result_is_ok(freed));
                let _ = fs::remove_file(path);
            }
        }

        #[test]
        fn compacted_region_roundtrip_thunk_keeps_thunk_tag() {
            unsafe {
                let path = temp_path("thunk");
                let c_path = CString::new(path.clone()).unwrap();
                let s = lean_mk_string(c_path.as_ptr());
                let thunk = lean_thunk_pure(lean_box(77));
                let save = lean_compacted_region_save(s, null_mut(), thunk, null_mut(), null_mut(), 0, null_mut());
                assert!(lean_io_result_is_ok(save));
                let read = lean_compacted_region_read(s, null_mut(), null_mut());
                assert!(lean_io_result_is_ok(read));
                let pair = lean_io_result_get_value(read);
                let restored = lean_ctor_get(pair, 0);
                assert_eq!(lean_ptr_tag(restored), 251);
                assert_eq!(lean_unbox(lean_thunk_get_own(restored)), 77);
                let region = lean_unbox(lean_ctor_get(pair, 1));
                let freed = crate::runtime_compact_impl::lean_compacted_region_free(region, null_mut());
                assert!(lean_io_result_is_ok(freed));
                let _ = fs::remove_file(path);
            }
        }
    }
}
