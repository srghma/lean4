source_init "$1"

if [[ "$1" == *"_es6.lean" ]]; then
  echo "Compiling to JS"
  run_before "$1"

  lean -j "$1.js" -Dcompiler.postponeCompile=false "${TEST_LEAN_ARGS[@]}" "$1" || fail "Failed to compile $1 into $1.js"

  CAPTURED="$1.js"
  if [[ -f "$1.js.expected" ]]; then
    $DIFF -- "$1.js.expected" "$1.js" || fail "Unexpected JS output"
  else
    fail "Missing $1.js.expected"
  fi

  run_after "$1"
else
  # Original C++ tests are disabled as requested
  echo "C++ tests disabled for $1"
fi
