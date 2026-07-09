/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

pub fn finalize_constants() {
    unsafe {
        for index in 0..LIBRARY_CONSTANT_PATHS.len() {
            let value = LIBRARY_CONSTANTS[index].obj;
            if !value.is_null() {
                lean_dec(value); // since persisted object then...?
                LIBRARY_CONSTANTS[index].obj = ptr::null_mut();
            }
        }
    }
}
