#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

modules=(
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement
  DifferentialGeometry.Tensor.Alternating.Wedge
  DifferentialGeometry.Tensor.Exterior.Basic
  DifferentialGeometry.Tensor.Exterior.Cochain
  DifferentialGeometry.Tensor.Exterior.Pullback
  DifferentialGeometry.Tensor.Exterior.Defs
  DifferentialGeometry.Tensor.Exterior.Leibniz
  DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm
  DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
  DifferentialGeometry.Tensor.Alternating.Comp
)

echo "== Building audit modules with the Mathlib standard linter set =="
for m in "${modules[@]}"; do
  out="$(mktemp)"
  if ! lake build "$m" >"$out" 2>&1; then
    cat "$out"
    rm -f "$out"
    echo "FAIL: $m failed to build"
    exit 1
  fi
  if grep -E "warning" "$out" | grep -v "Geometry/Flow" ; then
    cat "$out"
    rm -f "$out"
    echo "FAIL: $m produced linter warnings"
    exit 1
  fi
  rm -f "$out"
done

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
  echo "FAIL: in-scope sorry/admit/axiom/trustMe found"
  exit 1
fi

echo "== Checking whitespace errors =="
git diff --check

echo "Audit passed."
