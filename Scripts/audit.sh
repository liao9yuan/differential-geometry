#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "== Building audit modules from current source =="
for m in \
  DifferentialGeometry.Tensor.Auxiliary.Perm \
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement \
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition \
  DifferentialGeometry.Tensor.Alternating.Wedge \
  DifferentialGeometry.Tensor.Exterior.Defs \
  DifferentialGeometry.Tensor.Exterior.Basic \
  DifferentialGeometry.Tensor.Exterior.Pullback \
  DifferentialGeometry.Tensor.Exterior.Cochain \
  DifferentialGeometry.Tensor.Exterior.Leibniz \
  DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm \
  DifferentialGeometry.Analysis.Calculus.AnalyticTransfer \
  DifferentialGeometry.Tensor.Alternating.Comp; do
  lake build "$m" || { echo "FAIL: $m failed to build"; exit 1; }
done

echo "== Running the Mathlib linter set on de Rham foundation modules =="
lake env lean Scripts/Lint.lean

echo "== Checking public API manifest =="
lake env lean Scripts/PublicApi.lean

echo "== Checking axiom closures of headline theorems =="
lake env lean Scripts/Axioms.lean

echo "== Checking root aggregate wiring =="
for m in \
  DifferentialGeometry.Tensor.Auxiliary.Perm \
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement \
  DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition \
  DifferentialGeometry.Tensor.Alternating.Wedge \
  DifferentialGeometry.Tensor.Exterior.Defs \
  DifferentialGeometry.Tensor.Exterior.Basic \
  DifferentialGeometry.Tensor.Exterior.Pullback \
  DifferentialGeometry.Tensor.Exterior.Cochain \
  DifferentialGeometry.Tensor.Exterior.Leibniz \
  DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm \
  DifferentialGeometry.Analysis.Calculus.AnalyticTransfer \
  DifferentialGeometry.Tensor.Alternating.Comp; do
  if ! grep -q "import $m" DifferentialGeometry.lean; then
    echo "FAIL: $m is not imported by the root aggregate DifferentialGeometry.lean"
    exit 1
  fi
done

echo "== Checking for forbidden constructs in the de Rham tree =="
if rg -n "set_option (maxHeartbeats|maxRecDepth|synthInstance.maxHeartbeats)|#check |#print |#eval |#reduce |logInfo" \
    DifferentialGeometry/Tensor DifferentialGeometry/Bundle \
    DifferentialGeometry/Analysis/Calculus/AnalyticTransfer.lean \
    --glob '*.lean' --glob '!**/External/**'; then
  echo "FAIL: forbidden diagnostic or resource-override construct found"
  exit 1
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

echo "== Checking whitespace errors =="
git diff --check

echo "Audit passed."
