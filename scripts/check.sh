#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/catalog.py check
# Suppress cached dependency build warnings. Native lint reports remain visible;
# Colib compilation warnings remain errors through warningAsError in lakefile.toml.
case "${1:-}" in
  '') lake --log-level=error build Colib ;;
  --compiled) : ;; # CI has just verified this run's production outputs with native Lake.
  *) echo 'Usage: scripts/check.sh [--compiled]' >&2; exit 2 ;;
esac
lake --log-level=error test
bash .github/lint/run.sh Colib
python3 scripts/lint_style.py
lake exe mathlib/mk_all --lib Colib --check

# Pinned independent production auditor, separate from mathematical dependencies.
tool_root="${COLIB_TOOLS_DIR:-.lake/tools}"
auditor="$tool_root/axiom-audit"
if ! test -d "$auditor/.git"; then
  mkdir -p "$tool_root"
  git clone --depth 1 --branch v0.1.2 https://github.com/leanprover-community/axiom-audit.git "$auditor"
fi
test "$(git -C "$auditor" rev-parse HEAD)" = 46024e005996495c65ef609368e11ab39c4222e3
cp lean-toolchain "$auditor/lean-toolchain"
(cd "$auditor" && lake build)
lake env "$auditor/.lake/build/bin/axiom-audit" --root Colib

python3 scripts/catalog.py build
python3 scripts/site.py
