#!/usr/bin/env bash
# check.sh — type-check the ZF Lambdapi package.
# Usage:
#   ./check.sh            # check every module in the package
#   ./check.sh Ordinal.lp # check specific files (deps compiled automatically)
#
# Files live in the `zf` package (root_path = ZF, see lambdapi.pkg), so the
# ZF.* module path is resolved by Lambdapi from the local lambdapi.pkg — no
# --map-dir is needed. The Stdlib.* package must be available in Lambdapi's
# global library root (it ships with a standard Lambdapi install).
set -euo pipefail
cd "$(dirname "$0")"

if [ $# -eq 0 ]; then
  # Build the whole PORT: every root *.lp except scratch/experimental files
  # listed in .check-exclude. Without this, a broken experiment (e.g. GST.lp)
  # turns the aggregate build red and masks the true state of the port.
  set --
  exclude=""
  if [ -f .check-exclude ]; then
    exclude=$(grep -vE '^\s*(#|$)' .check-exclude || true)
  fi
  for f in *.lp; do
    skip=""
    for e in $exclude; do [ "$f" = "$e" ] && skip=1; done
    [ -z "$skip" ] && set -- "$@" "$f"
  done
fi

lambdapi check -c "$@"
echo "OK: type-checked successfully."
