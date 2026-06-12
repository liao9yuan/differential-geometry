import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.NablaRicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

/-!
# The per-direction tension-field curvature IBP: refuted nullity, restated difference atom

This module formerly stated the **frame-summed tension-field curvature-divergence nullity**: for a
fixed smooth Parseval frame family `V a` and each fixed slot-`0` direction `b`,
```
∑_a ∫_M ⟨R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S, slot0_{V b}(∇S)⟩_g dvol_g = 0.
```

That statement is **FALSE** (confirmed 2026-06-12; see `PROVE_REFUTED.md`, "Kernel (rank-0 Bochner) —
the per-b TENSION-FIELD NULLITY family").  Mechanism: under a point-dependent gauge rotation of the
Parseval family the tension-field carrier reads the family's pure gauge freedom (the rotation
generator `τ = dφ(V₁)V₂ − dφ(V₂)V₁`) while `0` is gauge-invariant, so the per-`b` nullity equates a
gauge-variant quantity to an invariant one; an explicit `S²` endpoint evaluates the left side to a
nonzero value.  Only statements whose two sides carry **matching** rotation-variance under
family-gauge rotations are admissible per-direction; the variance-matched true atom is the **IBP
difference identity**
```
∑_a ∫ ⟨elt3IiiIv (V a)(V b), ∇_{V b} S⟩ = ∑_a ∫ ⟨elt1 (V a)(V b), ∇_{V b} S⟩ − ∑_a ∫ residue (V a)(V b),
```
whose single on-disk statement is
`parsevalFrameSum_tensionFieldCurvature_perB_eq_group1_sub_residue`
(`ParsevalSevenTermBochnerFold`): it is stated there, not here, because its right side is written in
the fold's private group carriers (`bochnerGroupElt1`, `bochnerGroup2Residue`), which live next to it.

This file intentionally retains its import closure (the differentiated-Ricci carriers, the
frame-summed covariant-IBP engine `MovingFrameIntegratedNullity`, Theorem A and the contracted second
Bianchi) and no declarations; it is the import seam through which the seven-term fold reaches that
infrastructure.
-/
