#!/usr/bin/env bash
# Regression tests for the StrataBoole backend.
#
# Each test is a C0 program with a golden file holding the output of
# `c0vc --verify`. A `// args: ...` line in a test adds compiler options.
#
#   tests/boole/run.sh            compare against the golden files
#   tests/boole/run.sh --update   regenerate the golden files
#
# Needs an SMT solver on PATH (z3 by default; set SOLVER to change it).

set -u
cd "$(dirname "$0")"
C0VC=${C0VC:-../../.lake/build/bin/c0vc}
SOLVER=${SOLVER:-z3}
update=false
[ "${1:-}" = "--update" ] && update=true

pass=0
fail=0
for test in *.c0; do
  expected="${test%.c0}.expected"
  args=$(sed -n 's|^// args: ||p' "$test")
  # shellcheck disable=SC2086
  actual=$("$C0VC" --verify --solver="$SOLVER" $args "$test" 2>&1)
  if $update; then
    printf '%s\n' "$actual" > "$expected"
    echo "updated $expected"
  elif [ -f "$expected" ] && [ "$actual" = "$(cat "$expected")" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL $test"
    diff <(cat "$expected" 2>/dev/null) <(printf '%s\n' "$actual") | sed 's/^/  /'
  fi
done

$update && exit 0
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
