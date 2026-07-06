/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compatibility init/finalize hooks for the C++ quotient facade.
The remaining typed quotient helpers are inline in quot.h.
*/

mod kernel_quot_impl {
    pub fn initialize_quot() {}
    pub fn finalize_quot() {}
}
