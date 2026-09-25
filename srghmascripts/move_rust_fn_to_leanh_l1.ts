#!/usr/bin/env bun

import path from "node:path";
import { moveRustFn, usage, workRoot, type Destination, type FnOccurrence } from "./lib/move_rust_fn";

const emittedFunctions = new Set([
  "lean_alloc_closure",
  "lean_alloc_ctor",
  "lean_box",
  "lean_box_float",
  "lean_box_float32",
  "lean_box_uint32",
  "lean_box_uint64",
  "lean_box_usize",
  "lean_closure_set",
  "lean_cstr_to_nat",
  "lean_ctor_get",
  "lean_ctor_get_float",
  "lean_ctor_get_float32",
  "lean_ctor_get_uint8",
  "lean_ctor_get_uint16",
  "lean_ctor_get_uint32",
  "lean_ctor_get_uint64",
  "lean_ctor_get_usize",
  "lean_ctor_release",
  "lean_ctor_set",
  "lean_ctor_set_float",
  "lean_ctor_set_float32",
  "lean_ctor_set_tag",
  "lean_ctor_set_uint8",
  "lean_ctor_set_uint16",
  "lean_ctor_set_uint32",
  "lean_ctor_set_uint64",
  "lean_ctor_set_usize",
  "lean_dec",
  "lean_dec_ref",
  "lean_dec_ref_known",
  "lean_del_object",
  "lean_float_once",
  "lean_float32_once",
  "lean_inc",
  "lean_inc_n",
  "lean_inc_ref",
  "lean_inc_ref_n",
  "lean_init_task_manager",
  "lean_initialize",
  "lean_initialize_runtime_module",
  "lean_io_mark_end_initialization",
  "lean_io_result_get_value",
  "lean_io_result_is_error",
  "lean_io_result_is_ok",
  "lean_io_result_mk_ok",
  "lean_io_result_show_error",
  "lean_is_exclusive",
  "lean_is_scalar",
  "lean_mark_persistent",
  "lean_mk_string",
  "lean_mk_string_unchecked",
  "lean_obj_once",
  "lean_obj_tag",
  "lean_run_main",
  "lean_setup_args",
  "lean_uint8_dec_eq",
  "lean_uint8_dec_le",
  "lean_uint8_dec_lt",
  "lean_uint8_of_nat_mk",
  "lean_uint8_once",
  "lean_uint8_to_nat",
  "lean_uint16_dec_eq",
  "lean_uint16_dec_le",
  "lean_uint16_dec_lt",
  "lean_uint16_of_nat",
  "lean_uint16_of_nat_mk",
  "lean_uint16_once",
  "lean_uint16_to_nat",
  "lean_uint32_dec_eq",
  "lean_uint32_dec_le",
  "lean_uint32_dec_lt",
  "lean_uint32_of_nat",
  "lean_uint32_of_nat_mk",
  "lean_uint32_once",
  "lean_uint32_to_nat",
  "lean_uint64_dec_eq",
  "lean_uint64_dec_le",
  "lean_uint64_dec_lt",
  "lean_uint64_of_nat",
  "lean_uint64_of_nat_mk",
  "lean_uint64_once",
  "lean_uint64_to_nat",
  "lean_unbox",
  "lean_unbox_float",
  "lean_unbox_float32",
  "lean_unbox_uint32",
  "lean_unbox_uint64",
  "lean_unbox_usize",
  "lean_unsigned_to_nat",
  "lean_usize_once",
  "lean_finalize_task_manager",
  "lean_internal_panic_unreachable",
]);

type Destination = {
  targetDir: string;
  moduleFile: string;
};

function getDestinationForFn(fnName: string): Destination {
  const isEmitted = emittedFunctions.has(fnName);
  return isEmitted
    ? {
        targetDir: path.join(workRoot, "leanh_l1/src/emitted"),
        moduleFile: path.join(workRoot, "leanh_l1/src/emitted/mod.rs"),
      }
    : {
        targetDir: path.join(workRoot, "leanh_l1/src/priv"),
        moduleFile: path.join(workRoot, "leanh_l1/src/priv/mod.rs"),
    };
}

async function main() {
  const fnNames = process.argv.slice(2);
  if (fnNames.length === 0) {
    usage("Usage: move_rust_fn_to_leanh_l1.ts <function_name> [function_name ...]");
  }
  for (const fnName of fnNames) {
    await moveRustFn(fnName, {
      usage: "Usage: move_rust_fn_to_leanh_l1.ts <function_name> [function_name ...]",
      currentRoots: [workRoot],
      ignoreDir: path.join(workRoot, "leanh_l1/src"),
      getDestination: (_sourceOcc: FnOccurrence) => getDestinationForFn(fnName),
      logScriptName: "move_rust_fn_to_leanh_l1.ts",
    });
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
