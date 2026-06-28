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
  set -- *.lp
fi

lambdapi check -c "$@"
echo "OK: type-checked successfully."
