find_program(CARGO_EXECUTABLE cargo REQUIRED)

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(LEAN_RUST_PROFILE dev)
  set(LEAN_RUST_TARGET_DIR ${CMAKE_BINARY_DIR}/rust/debug)
  set(LEAN_RUST_CARGO_ARGS)
else()
  set(LEAN_RUST_PROFILE release)
  set(LEAN_RUST_TARGET_DIR ${CMAKE_BINARY_DIR}/rust/release)
  set(LEAN_RUST_CARGO_ARGS --release)
endif()

set(LEAN_RUST_HAS_ADDRESS_SANITIZER 0)
if(CMAKE_CXX_FLAGS MATCHES "fsanitize=address" OR LEAN_EXTRA_CXX_FLAGS MATCHES "fsanitize=address")
  set(LEAN_RUST_HAS_ADDRESS_SANITIZER 1)
endif()
if(STAGE EQUAL 0)
  set(LEAN_RUST_IS_STAGE0 1)
else()
  set(LEAN_RUST_IS_STAGE0 0)
endif()

set(LEANMAIN_RLIB ${CMAKE_BINARY_DIR}/lib/temp/libleanmain.rlib)
set(LEANSHELL_RLIB ${CMAKE_BINARY_DIR}/lib/temp/libleanshell.rlib)
add_custom_command(
  OUTPUT ${LEANMAIN_RLIB} ${LEANSHELL_RLIB}
  COMMAND
    ${CMAKE_COMMAND} -E env
    CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/rust
    LEAN_RUST_GITHASH=${GIT_SHA1}
    LEAN_RUST_BUILD_TYPE=${CMAKE_BUILD_TYPE}
    LEAN_RUST_VERSION_STRING=${LEAN_VERSION_STRING}
    LEAN_RUST_MANUAL_ROOT=${LEAN_MANUAL_ROOT}
    LEAN_RUST_HAS_LLVM=$<IF:$<BOOL:${LLVM}>,1,0>
    LEAN_RUST_HAS_ADDRESS_SANITIZER=${LEAN_RUST_HAS_ADDRESS_SANITIZER}
    LEAN_RUST_HAS_MIMALLOC=$<IF:$<BOOL:${USE_MIMALLOC}>,1,0>
    LEAN_RUST_SMALL_ALLOCATOR=$<IF:$<BOOL:${SMALL_ALLOCATOR}>,1,0>
    LEAN_RUST_USE_GMP=$<IF:$<BOOL:${USE_GMP}>,1,0>
    LEAN_RUST_MULTI_THREAD=$<IF:$<BOOL:${MULTI_THREAD}>,1,0>
    LEAN_RUST_DEBUG=$<IF:$<CONFIG:Debug>,1,$<IF:$<CONFIG:RelWithAssert>,1,0>>
    LEAN_RUST_LEANC_EXTRA_CC_FLAGS=${LEANC_EXTRA_CC_FLAGS}
    LEAN_RUST_LEANC_INTERNAL_FLAGS=${LEANC_INTERNAL_FLAGS}
    LEAN_RUST_LEANC_STATIC_LINKER_FLAGS=${LEANC_STATIC_LINKER_FLAGS}
    LEAN_RUST_LEANC_SHARED_LINKER_FLAGS=${LEANC_SHARED_LINKER_FLAGS}
    LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS=${LEAN_EXTRA_LINKER_FLAGS}
    LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE=${LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE}
    LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS=${LEANC_INTERNAL_LINKER_FLAGS}
    LEAN_RUST_IS_STAGE0=${LEAN_RUST_IS_STAGE0}
    ${CARGO_EXECUTABLE} build --manifest-path ${LEAN_SOURCE_DIR}/rust/Cargo.toml --package lean_shell ${LEAN_RUST_CARGO_ARGS}
  COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/lib/temp
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${LEAN_RUST_TARGET_DIR}/liblean_shell.rlib ${LEANMAIN_RLIB}
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${LEANMAIN_RLIB} ${LEANSHELL_RLIB}
  DEPENDS ${LEAN_SOURCE_DIR}/rust/Cargo.toml ${LEAN_SOURCE_DIR}/rust/lean_shell/Cargo.toml ${LEAN_SOURCE_DIR}/rust/lean_shell/src/lib.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/Cargo.toml
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/build.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/lib.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_util.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_mpz.rs
  VERBATIM
)
add_custom_target(leanmain DEPENDS ${LEANMAIN_RLIB})
add_custom_target(leanshell DEPENDS ${LEANSHELL_RLIB})

# library must contain at least one non-manifest file
# We use `CONFIGURE` instead of `WRITE` so as to avoid touching the file on each run
file(CONFIGURE OUTPUT ${CMAKE_BINARY_DIR}/temp/empty.c CONTENT "")
add_library(leanmanifest STATIC ${CMAKE_BINARY_DIR}/temp/empty.c manifest.rc)
set_target_properties(
  leanmanifest
  PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib/lean OUTPUT_NAME leanmanifest
)

if(LLVM)
  if(CMAKE_SYSTEM_NAME MATCHES "Linux")
    set(LLVM_SYSTEM_LIBS "-lz -ltinfo")
  elseif(CMAKE_SYSTEM_NAME MATCHES "Darwin")
    # macOS doesn't have -Bstatic, so let cmake search for the libraries
    find_library(LIBZ NAMES z REQUIRED)
    find_library(NCURSES NAMES ncurses REQUIRED)
    set(LLVM_SYSTEM_LIBS "${LIBZ} ${NCURSES}")
  else()
    set(LLVM_SYSTEM_LIBS "-lz")
  endif()
  if(NOT CMAKE_SYSTEM_NAME MATCHES "Darwin")
    string(
      APPEND LEAN_EXE_LINKER_FLAGS
      " `llvm-config --link-static --ldflags --libs nativecodegen` -Wl,-Bstatic ${LLVM_SYSTEM_LIBS} -Wl,-Bdynamic"
    )
  else()
    string(APPEND LEAN_EXE_LINKER_FLAGS " `llvm-config --ldflags --libs nativecodegen` ${LLVM_SYSTEM_LIBS}")
  endif()
  if(CMAKE_SYSTEM_NAME MATCHES "Windows")
    string(APPEND LEAN_EXE_LINKER_FLAGS " -lole32 -luuid")
  endif()
endif()

add_custom_target(
  lean
  ALL
  WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
  DEPENDS leanshared leanmain
  COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make lean
  COMMAND_EXPAND_LISTS
)
