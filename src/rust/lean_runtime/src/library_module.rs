// Rust implementation of Lean.CompactedRegion save/read.

mod library_module_impl {
    use super::*;
    use std::collections::HashMap;
    use std::ffi::{CStr, CString};
    use std::fs::File;
    use std::io::{Read, Write};
    use std::ptr::{null, null_mut};

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
            capacity: usize,
            fields: Vec<RefValue>,
        },
        SArray {
            elem_size: usize,
            size: usize,
            capacity: usize,
            bytes: Vec<u8>,
        },
        String {
            size: usize,
            capacity: usize,
            len: usize,
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
                248 => {}
                249 => {}
                247 => {
                    self.discover_ref((obj as *mut LeanPromiseObject).read().result)?;
                }
                252 => {
                    let thunk = obj as *mut LeanThunkObject;
                    self.discover_ref((*thunk).m_closure)?;
                    self.discover_ref((*thunk).m_value)?;
                }
                253 => {
                    let task = obj as *mut LeanTaskObject;
                    if !(*task).m_imp.is_null() {
                        return Err("cannot compact a running task".to_string());
                    }
                    self.discover_ref((*task).m_value)?;
                }
                254 => {
                    self.discover_ref((obj as *mut LeanRefObject).read().m_value)?;
                }
                245 => {
                    return Err("external objects cannot be compacted".to_string());
                }
                250 => {
                    return Err("closures cannot be compacted in the Rust runtime yet".to_string());
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
                    let capacity = lean_array_capacity(obj);
                    let mut fields = Vec::with_capacity(size);
                    for i in 0..size {
                        fields.push(self.ref_of(lean_array_get(obj, i)));
                    }
                    NodeRecord { kind: NodeKind::Array { size, capacity, fields } }
                }
                248 => {
                    let elem_size = lean_sarray_elem_size(obj) as usize;
                    let size = lean_sarray_size(obj);
                    let capacity = lean_sarray_capacity(obj);
                    let bytes = std::slice::from_raw_parts(lean_sarray_cptr(obj), size * elem_size).to_vec();
                    NodeRecord { kind: NodeKind::SArray { elem_size, size, capacity, bytes } }
                }
                249 => {
                    let size = lean_string_size(obj);
                    let capacity = lean_string_capacity(obj);
                    let len = lean_string_len(obj);
                    let bytes = std::slice::from_raw_parts(lean_string_cstr(obj) as *const u8, size).to_vec();
                    NodeRecord { kind: NodeKind::String { size, capacity, len, bytes } }
                }
                247 => {
                    let result = self.ref_of((obj as *mut LeanPromiseObject).read().result);
                    NodeRecord { kind: NodeKind::Promise { result } }
                }
                252 => {
                    let thunk = obj as *mut LeanThunkObject;
                    let closure = self.ref_of((*thunk).m_closure);
                    let value = self.ref_of((*thunk).m_value);
                    NodeRecord { kind: NodeKind::Thunk { closure, value } }
                }
                253 => {
                    let task = obj as *mut LeanTaskObject;
                    if !(*task).m_imp.is_null() {
                        return Err("cannot compact a running task".to_string());
                    }
                    let value = self.ref_of((*task).m_value);
                    NodeRecord { kind: NodeKind::Task { value } }
                }
                254 => {
                    let value = self.ref_of((obj as *mut LeanRefObject).read().m_value);
                    NodeRecord { kind: NodeKind::Ref { value } }
                }
                245 => return Err("external objects cannot be compacted".to_string()),
                250 => return Err("closures cannot be compacted in the Rust runtime yet".to_string()),
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
            NodeKind::Array { size, capacity, .. } => {
                let obj = lean_alloc_array_export(*size, *capacity);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::SArray { elem_size, size, capacity, .. } => {
                let obj = lean_alloc_sarray_export(*elem_size as u32, *size, *capacity);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::String { size, capacity, len, .. } => {
                let obj = lean_alloc_string_export(*size, *capacity, *len);
                (*obj).m_rc = 0;
                obj
            }
            NodeKind::Thunk { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanThunkObject>()) as *mut LeanThunkObject;
                alloc_persistent_header(obj as *mut LeanObject, 252);
                obj as *mut LeanObject
            }
            NodeKind::Ref { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanRefObject>()) as *mut LeanRefObject;
                alloc_persistent_header(obj as *mut LeanObject, 254);
                obj as *mut LeanObject
            }
            NodeKind::Promise { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanPromiseObject>()) as *mut LeanPromiseObject;
                alloc_persistent_header(obj as *mut LeanObject, 247);
                obj as *mut LeanObject
            }
            NodeKind::Task { .. } => {
                let obj = lean_alloc_small_object_export(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
                alloc_persistent_header(obj as *mut LeanObject, 253);
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
        let _version = cur.read_u64()?;
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
                    let capacity = cur.read_usize()?;
                    let mut fields = Vec::with_capacity(size);
                    for _ in 0..size {
                        fields.push(read_ref(&mut cur)?);
                    }
                    NodeRecord { kind: NodeKind::Array { size, capacity, fields } }
                }
                3 => {
                    let elem_size = cur.read_usize()?;
                    let size = cur.read_usize()?;
                    let capacity = cur.read_usize()?;
                    let bytes = cur.read_bytes()?;
                    NodeRecord { kind: NodeKind::SArray { elem_size, size, capacity, bytes } }
                }
                4 => {
                    let size = cur.read_usize()?;
                    let capacity = cur.read_usize()?;
                    let len = cur.read_usize()?;
                    let bytes = cur.read_bytes()?;
                    NodeRecord { kind: NodeKind::String { size, capacity, len, bytes } }
                }
                5 => {
                    let closure = read_ref(&mut cur)?;
                    let value = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Thunk { closure, value } }
                }
                6 => {
                    let value = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Ref { value } }
                }
                7 => {
                    let result = read_ref(&mut cur)?;
                    NodeRecord { kind: NodeKind::Promise { result } }
                }
                8 => {
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
                NodeKind::Array { size, fields, .. } => {
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
        out.write_all(&1u64.to_le_bytes()).map_err(|e| e.to_string())?;
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
                NodeKind::Array { size, capacity, fields } => {
                    out.write_all(&[2]).map_err(|e| e.to_string())?;
                    out.write_all(&(*size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*capacity as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    for field in fields {
                        serialize_ref(&mut out, *field)?;
                    }
                }
                NodeKind::SArray { elem_size, size, capacity, bytes } => {
                    out.write_all(&[3]).map_err(|e| e.to_string())?;
                    out.write_all(&(*elem_size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*capacity as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(bytes.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(bytes).map_err(|e| e.to_string())?;
                }
                NodeKind::String { size, capacity, len, bytes } => {
                    out.write_all(&[4]).map_err(|e| e.to_string())?;
                    out.write_all(&(*size as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*capacity as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(*len as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(&(bytes.len() as u64).to_le_bytes()).map_err(|e| e.to_string())?;
                    out.write_all(bytes).map_err(|e| e.to_string())?;
                }
                NodeKind::Thunk { closure, value } => {
                    out.write_all(&[5]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *closure)?;
                    serialize_ref(&mut out, *value)?;
                }
                NodeKind::Ref { value } => {
                    out.write_all(&[6]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *value)?;
                }
                NodeKind::Promise { result } => {
                    out.write_all(&[7]).map_err(|e| e.to_string())?;
                    serialize_ref(&mut out, *result)?;
                }
                NodeKind::Task { value } => {
                    out.write_all(&[8]).map_err(|e| e.to_string())?;
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
                    Some(cmsg) => lean_io_result_mk_error(lean_mk_string(cmsg.as_ptr())),
                    None => lean_io_result_mk_error(lean_mk_string(fallback.as_ptr())),
                }
            }
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_read(
        ofname: *mut LeanObject,
        _odep_regions: *mut LeanObject,
        _w: *mut LeanObject,
    ) -> *mut LeanObject {
        let result = (|| -> Result<*mut LeanObject, String> {
            let path = describe_file_path(ofname)?;
            let bytes = read_file_bytes(&path)?;
            let (root_ref, graph) = parse_graph(&bytes)?;
            let (root, objs) = materialize_graph(root_ref, graph)?;
            let region = Box::new(crate::runtime_compact_impl::RustCompactedRegion::new(bytes.len(), objs));
            let region_ptr = Box::into_raw(region) as usize;
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
                    Some(cmsg) => lean_io_result_mk_error(lean_mk_string(cmsg.as_ptr())),
                    None => lean_io_result_mk_error(lean_mk_string(fallback.as_ptr())),
                }
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::fs;
        use std::ffi::CString;
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
                let a = lean_alloc_array_export(2, 2);
                lean_array_cptr(a).write(lean_box(11));
                lean_array_cptr(a).add(1).write(lean_box(22));
                let save = lean_compacted_region_save(s, null_mut(), a, null_mut(), null_mut(), 0, null_mut());
                assert!(lean_io_result_is_ok(save));
                let read = lean_compacted_region_read(s, null_mut(), null_mut());
                assert!(lean_io_result_is_ok(read));
                let pair = lean_io_result_get_value(read);
                let arr = lean_ctor_get(pair, 0);
                assert_eq!(lean_array_size(arr), 2);
                assert_eq!(lean_unbox(lean_array_get(arr, 0)), 11);
                assert_eq!(lean_unbox(lean_array_get(arr, 1)), 22);
                let region = lean_unbox(lean_ctor_get(pair, 1));
                let freed = crate::runtime_compact_impl::lean_compacted_region_free(region, null_mut());
                assert!(lean_io_result_is_ok(freed));
                let _ = fs::remove_file(path);
            }
        }
    }
}
