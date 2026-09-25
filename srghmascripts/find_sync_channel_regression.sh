#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  srghmascripts/find_sync_channel_regression.sh [OPTIONS]

Walk backward commit-by-commit from a bad commit and find where
tests/elab/sync_channel.lean starts hanging/failing.

Options:
  --bad COMMIT        Commit to start from. Default: HEAD
  --good COMMIT       Stop once this commit is reached. Default: upstream/master
  --runs N            Test repetitions per commit. Default: 5
  --timeout SEC       Timeout per repetition. Default: 90
  --threads N         LEAN_NUM_THREADS value. Default: 2
  --build-target T    Build target. Default: stage1
  --no-build          Do not build at each commit
  --keep-going        Continue after build failures
  -h, --help          Show this help

Notes:
  * Requires a clean git worktree.
  * Checks out commits, so run it from a disposable worktree if possible.
  * Exit code 0 means a transition was found.
  * Exit code 1 means no good commit was found before --good.
  * Exit code 2 means setup/usage/build failure.
EOF
}

bad_ref=HEAD
good_ref=upstream/master
runs=5
timeout_sec=90
lean_threads=2
build_target=stage1
do_build=1
keep_going=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --bad)
      bad_ref="${2:?missing value for --bad}"
      shift 2
      ;;
    --good)
      good_ref="${2:?missing value for --good}"
      shift 2
      ;;
    --runs)
      runs="${2:?missing value for --runs}"
      shift 2
      ;;
    --timeout)
      timeout_sec="${2:?missing value for --timeout}"
      shift 2
      ;;
    --threads)
      lean_threads="${2:?missing value for --threads}"
      shift 2
      ;;
    --build-target)
      build_target="${2:?missing value for --build-target}"
      shift 2
      ;;
    --no-build)
      do_build=0
      shift
      ;;
    --keep-going)
      keep_going=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if ! [[ "$runs" =~ ^[1-9][0-9]*$ ]]; then
  echo "--runs must be a positive integer" >&2
  exit 2
fi

if ! [[ "$timeout_sec" =~ ^[1-9][0-9]*$ ]]; then
  echo "--timeout must be a positive integer" >&2
  exit 2
fi

if ! [[ "$lean_threads" =~ ^[0-9]+$ ]]; then
  echo "--threads must be a non-negative integer" >&2
  exit 2
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if [[ -n "$(git status --porcelain)" ]]; then
  echo "refusing to checkout commits with a dirty worktree" >&2
  echo "commit/stash your work first, or run this in a separate git worktree" >&2
  exit 2
fi

bad_commit="$(git rev-parse --verify "$bad_ref^{commit}")"
good_commit="$(git rev-parse --verify "$good_ref^{commit}")"
original_head="$(git rev-parse --verify HEAD)"
original_branch="$(git symbolic-ref --quiet --short HEAD || true)"
log_dir="/tmp/lean4-sync-channel-regression-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$log_dir"

restore_head() {
  if [[ -n "$original_branch" ]]; then
    git checkout -q "$original_branch"
  else
    git checkout -q "$original_head"
  fi
}
trap restore_head EXIT

build_commit() {
  local commit="$1"
  local log="$log_dir/build-$commit.log"
  echo "building $commit ($build_target)"
  if make -C build/release "$build_target" -j"$(nproc)" >"$log" 2>&1; then
    return 0
  fi
  echo "BUILD_FAIL $commit log=$log"
  tail -n 80 "$log"
  return 1
}

test_commit() {
  local commit="$1"
  local run log
  for run in $(seq 1 "$runs"); do
    log="$log_dir/test-$commit-run-$run.log"
    echo "testing $commit run $run/$runs"
    if ! LEAN_NUM_THREADS="$lean_threads" timeout "$timeout_sec" \
      build/release/stage1/bin/lean \
      --root=tests/elab \
      -DprintMessageEndPos=true \
      -Dlinter.all=false \
      -DElab.inServer=true \
      -Dcompiler.postponeCompile=false \
      tests/elab/sync_channel.lean >"$log" 2>&1; then
      local status=$?
      echo "BAD $commit run=$run status=$status log=$log"
      tail -n 80 "$log"
      return 1
    fi
  done
  echo "GOOD $commit ($runs/$runs runs passed)"
  return 0
}

echo "logs: $log_dir"
echo "bad start: $bad_commit"
echo "good stop: $good_commit"
echo "runs per commit: $runs, timeout: ${timeout_sec}s, LEAN_NUM_THREADS=$lean_threads"

prev_bad=""

while read -r commit; do
  echo
  echo "=== $commit $(git log -1 --format=%s "$commit") ==="
  git checkout -q "$commit"

  if [[ "$do_build" -eq 1 ]]; then
    if ! build_commit "$commit"; then
      if [[ "$keep_going" -eq 1 ]]; then
        echo "skipping unbuildable commit because --keep-going was set"
        continue
      fi
      exit 2
    fi
  fi

  if test_commit "$commit"; then
    if [[ -n "$prev_bad" ]]; then
      echo
      echo "Regression boundary found:"
      echo "  last good:  $commit"
      echo "  first bad:  $prev_bad"
      echo
      git --no-pager log --oneline --decorate -2 "$prev_bad" --not "$commit^" || true
      echo "logs: $log_dir"
      exit 0
    fi
    echo "start commit is already good; no regression found from --bad"
    echo "logs: $log_dir"
    exit 1
  fi

  prev_bad="$commit"

  if [[ "$commit" == "$good_commit" ]]; then
    break
  fi
done < <(git rev-list --first-parent "$bad_commit" "^$good_commit")

echo
echo "No good commit found before stop commit."
echo "last observed bad: ${prev_bad:-none}"
echo "stop commit: $good_commit"
echo "logs: $log_dir"
exit 1
