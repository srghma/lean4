/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "kernel/environment.h"
#include "runtime/exception.h"
#include "runtime/object_ref.h"
#include "runtime/string_ref.h"
#include "util/name.h"
#include "util/options.h"

extern "C" void initialize_ir_interpreter();
extern "C" void finalize_ir_interpreter();
extern "C" lean::object * lean_eval_const_at_kernel_env(
    lean::object * env, lean::object * opts, lean::object * fn, size_t n, lean::object ** args);

namespace lean {
namespace ir {
object * run_boxed_kernel(environment const & env, options const & opts, name const & fn, unsigned n, object ** args) {
    object_ref result(lean_eval_const_at_kernel_env(env.raw(), opts.raw(), fn.raw(), n, args));
    object * value = cnstr_get(result.raw(), 0);
    if (cnstr_tag(result.raw()) == 0) {
        string_ref msg(value, true);
        throw exception(msg.to_std_string());
    }
    inc(value);
    return value;
}
}

LEAN_EXPORT void initialize_ir_interpreter() {
}

LEAN_EXPORT void finalize_ir_interpreter() {
    ::finalize_ir_interpreter();
}
}
