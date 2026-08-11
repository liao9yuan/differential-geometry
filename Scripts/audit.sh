#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "== Building audit modules from current source =="
modules=(
  DifferentialGeometry.Tensor.Auxiliary.Perm
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
  DifferentialGeometry.Tensor.Alternating.Wedge
  DifferentialGeometry.Tensor.Exterior.Defs
  DifferentialGeometry.Tensor.Exterior.Basic
  DifferentialGeometry.Tensor.Exterior.Pullback
  DifferentialGeometry.Tensor.Exterior.Cochain
  DifferentialGeometry.Tensor.Exterior.Leibniz
  DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm
  DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
  DifferentialGeometry.Tensor.Alternating.Comp
  DifferentialGeometry.Tensor.Exterior.ZeroForm
)
for m in "${modules[@]}"; do
  lake build "$m" || { echo "FAIL: $m failed to build"; exit 1; }
done

echo "== Running the Mathlib linter set on de Rham foundation modules =="
lake env lean Scripts/Lint.lean

echo "== Checking exact public signatures =="
lake env lean Scripts/Sigs.lean

echo "== Checking public API inventory =="
lake env lean Scripts/PublicApi.lean

echo "== Checking private-declaration reachability =="
python3 Scripts/reachability.py

echo "== Checking axiom closures of headline theorems =="
lake env lean Scripts/Axioms.lean

echo "== Checking root aggregate wiring (auto-enumerated leaves) =="
if ! rg -q '^import DifferentialGeometry\.Tensor\.Auxiliary\.Perm$' DifferentialGeometry.lean; then
  echo "FAIL: leaf import missing for DifferentialGeometry.Tensor.Auxiliary.Perm"
  exit 1
fi
missing=0
while IFS= read -r leaf; do
  rel="${leaf#DifferentialGeometry/}"
  rel="${rel%.lean}"
  mod="DifferentialGeometry.${rel//\//.}"
  if ! grep -q "import $mod" DifferentialGeometry.lean; then
    echo "FAIL: leaf module $mod is not imported by the root aggregate DifferentialGeometry.lean"
    missing=1
  fi
done < <(find DifferentialGeometry -name '*.lean' -not -path '*/External/*' | sort)
if [ "$missing" -ne 0 ]; then
  exit 1
fi

echo "== Checking for forbidden constructs in de Rham sources and audit scripts =="
if rg -n "set_option (maxHeartbeats|maxRecDepth|synthInstance.maxHeartbeats)|#check |#print |#eval |#reduce |logInfo |\bsorry\b|\badmit\b|^axiom |\btrustMe\b" \
    DifferentialGeometry/Tensor DifferentialGeometry/Bundle DifferentialGeometry/Analysis/Calculus/AnalyticTransfer.lean \
    Scripts --glob '*.lean' --glob '!**/External/**'; then
  echo "FAIL: forbidden construct found"
  exit 1
fi
nolint_files=$(rg -l "@\[nolint" DifferentialGeometry/Tensor DifferentialGeometry/Bundle DifferentialGeometry/Analysis/Calculus/AnalyticTransfer.lean --glob '*.lean' --glob '!**/External/**' 2>/dev/null || true)
nolint_count=0
for f in $nolint_files; do
  c=$(grep -c "@\[nolint" "$f" || true)
  nolint_count=$((nolint_count + c))
done
scripts_nolint_files=$(rg -l "@\[nolint" Scripts --glob '*.lean' 2>/dev/null || true)
scripts_nolint=0
for f in $scripts_nolint_files; do
  c=$(grep -c "@\[nolint" "$f" || true)
  scripts_nolint=$((scripts_nolint + c))
done
if [ "$scripts_nolint" -gt 0 ]; then
  echo "FAIL: @[nolint] present in Scripts/"
  exit 1
fi
if [ "$nolint_count" -gt 0 ]; then
  echo "WARNING: $nolint_count @[nolint] occurrences in de Rham sources require owner approval (currently pending)"
fi

echo "== Checking for scratch or diagnostic files at the repository root =="
if compgen -G "$ROOT"/Scratch*.lean >/dev/null; then
  echo "FAIL: stray scratch file found at repository root"
  ls "$ROOT"/Scratch*.lean
  exit 1
fi

echo "== Checking for proof debt in the de Rham foundation tree =="
if rg -n "\b(sorry|admit|axiom|trustMe)\b" \
    DifferentialGeometry/Tensor DifferentialGeometry/Bundle \
    DifferentialGeometry/Analysis/Calculus/AnalyticTransfer.lean \
    --glob '*.lean' --glob '!**/External/**'; then
  echo "FAIL: sorry/admit/axiom/trustMe found in de Rham tree"
  exit 1
fi

echo "== Checking build warnings against allowlist =="
lake build DifferentialGeometry > /tmp/audit_build.log 2>&1 || { cat /tmp/audit_build.log; echo "FAIL: root build failed"; exit 1; }
grep "warning" /tmp/audit_build.log | sed -E 's/^warning: //' | sort > /tmp/audit_warnings.txt
if ! diff -u Scripts/warnings.allowlist /tmp/audit_warnings.txt; then
  echo "FAIL: build warnings differ from the allowlist (add new warnings only with owner approval)"
  exit 1
fi
echo "NOTE: the warnings in Scripts/warnings.allowlist are pre-existing and await owner approval as a baseline"

echo "== Checking whitespace errors =="
BASE_REF="${1:-}"
if [ -n "$BASE_REF" ]; then
  if ! git diff --check "$BASE_REF..HEAD" --; then
    echo "FAIL: whitespace errors in range $BASE_REF..HEAD"
    exit 1
  fi
else
  git diff --check
fi

echo "Audit passed."
