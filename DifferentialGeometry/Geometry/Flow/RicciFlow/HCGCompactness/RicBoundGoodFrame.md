# RicBoundGoodFrame.lean — the good-frame producer (ric_bound bricks 1+2 geometry)

## ✅ ALL GREEN sorry-free (2026-06-11, focus-checked)

The per-point producer the `ric_bound` assembly consumes.  Chain (all in this file
unless noted):

- `gramInv_inverse` — `(gramE e₀ g basisE y)⁻¹` realizes
  `MetricInverseInBasis_gen g y (toBasisAt hy)` for `y ∈ baseSet`
  (`nonsing_inv_mul`/`mul_nonsing_inv` entries + `toBasisAt_coe`; gramE entry = rfl).
- `gramInv_symm` — inverse Gram symmetric (`(gramE_herm …).inv`).
- `gramE_eq_one` — Gram = 1 at a frame-orthonormal point.
- `gramInv_near_id` — **continuity producer**: from `gramE x = 1`, an open
  `u' ∋ x ⊆ baseSet` with `|(gramE z)⁻¹ i j − δᵢⱼ| ≤ ε` on `u'`.  Route:
  `gCompField_mdiffOn` (Claim1Wiring B2) → entry `ContinuousWithinAt` →
  Pi-assembly → `continuousAt_matrix_inv` (Mathlib Topology.Instances.Matrix;
  `Ring.inverse_eq_inv'` + `continuousAt_inv₀`) → per-entry `Tendsto.eventually`
  closed-ball → `Filter.eventually_all` (Fintype) → `mem_nhdsWithin`.
- `exists_orthonormalBasis_of_posDef` (private) + `exists_trivONBasis` —
  **the keystone, PORTED from ApproximateIsometry.lean** (raw-values form: a
  model-fibre basis whose trivialization frame is g-ON at x).  Ported because
  ApproximateIsometry is NOT BUILDABLE against the current tree (see below);
  dedup once repaired.
- **`exists_goodFrame_compBound`** — THE endpoint: ∀ x, ∃ basisE, ∃ open u' ∋ x
  ⊆ baseSet, frame gRef-ON at x (raw values), and ∀ z ∈ u', ∀ (0,s)-tensor A,
  `∑ component0S(toBasisAt hz) A ² ≤ 2^s · normSq0S gRef z s A`.
  Via `quad_lb_of_near_id` (ε := 1/(2(n+1)), C := 2) +
  `sum_comp_sq_le_pow_normSq0S` (Comparison.lean) + component0S↔tensor0SComponent
  rfl-bridge.

## Lean lessons

- `continuousWithinAt_pi` does NOT rw against `Matrix`-typed goals
  (`instTopologicalSpaceMatrix` ≠ syntactic `Pi.topologicalSpace`): state the
  Pi-typed `have` (`fun i j => … : Idx → Idx → ℝ`) and `exact` it (defeq).
- `Matrix.inv_one` does not exist: use `Matrix.inv_eq_left_inv (by rw [one_mul])`.
- `div_le_div_iff` renamed/unavailable: use `div_le_iff₀`.
- Keystone port needs `import Mathlib.LinearAlgebra.QuadraticForm.Basic`
  (`exists_orthogonal_basis`, `isOrthoᵢ_def`).

## ⚠ MAJOR FINDING: ApproximateIsometry.lean is BROKEN vs the current tree

`lake build +…ApproximateIsometry` fails with dozens of unknown identifiers:
`LeviCivita.leviCivitaConnectionOfMetric` (old namespace; now
`DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric`),
`Tensor0SBundle.normRS`/`normSqRS_le_of_metric_equiv`/`normRS_eq_sqrt_normSqRS`
(moved/renamed), `abs_quad02_le_norm`, `abs_component0S_le_sqrt_normSq0S`
(lives in RicciOperatorNormBound now?), plus 2 heartbeat timeouts.  The file was
green when written (2026-06-0x) but API refactors since then drifted it and it
is not in the regular build closure, so nothing caught it.  The keystone region
(≈4790–4910) itself is clean — only its neighbors break.  Ch4/Thm 3.9 notes
claiming "ApproximateIsometry 5925L 0-sorry" describe a STALE state.

## REMAINING for ric_bound (next bricks)

1. **Tower application**: `compL2(iterCovComp frame chr (frameComp0S T) j z)² =
   ∑ component0S(toBasisAt hz)(iterCov … j z)²` (via `iterCovComp_eq_iterCov`,
   the B5-proof pattern) → feed `exists_goodFrame_compBound` ⟹
   `compL2(tower) ≤ √(2^{r+j}) · √normSq0S gRef z (iterCov tower)` on u'.
2. Shi moving→fixed: `normSq0S_le_of_metric_equiv` (Comparison.lean) through
   eq 3.3 + the moving-Christoffel `iterCovComp_eq_iterCov`.
3. Ricci-component smoothness producer (B2 pattern for `ricciSection (LC g)`).
4. Finite-subcover uniformization over compact K + max constants.
5. RicBound.lean assembly (apply `aN_intrinsic_point` per point; R4f arity
   bridge for the RHS).
