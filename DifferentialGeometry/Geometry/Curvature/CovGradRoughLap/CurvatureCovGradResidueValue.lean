import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ParsevalSevenTermBochnerFold
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

/-!
# The residue-form curvature/covariant-gradient cross-pairing value

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, covariant rank `s`, and a
smooth compactly-supported `(0, s)`-tensor `S`, this file extracts the **frame-free integrated
Bochner residue-form value** of the curvature cross-pairing: the global metric `L²` pairing of the
order-`2` rough-Laplacian / covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s
S` against `∇S := covGrad g 0 s S` splits into the pure-Riemann trace, the Bochner–Lichnerowicz
Ricci trace, and the differentiated-curvature `(∇R) S` content in residue form
```
⟨Curv S, ∇S⟩_{L²}
  = ⟨GcurvSection g s S, ∇S⟩_{L²} + ⟨ricTraceSection g s S, ∇S⟩_{L²}
      + ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²}
      − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²},   Φ₀ := curvOpField g s.
```

It is the downstream junction of the two halves of the kernel chain: the three-section curvature
value `tensorL2Inner_curv_covGrad_eq_genuineThreeSection_value`
(`MovingFrameRemainderFrameSumBridge`, glued over the seven-term Parseval fold of
`ParsevalSevenTermBochnerFold`) and the sorry-free `L²` B-rule split
`tensorL2Inner_genuineDiffCurv_eq_covGradBase_sub_slotExtend` proved here.  Consumers transitively
depend on the `sorryAx` of the two posited fold primitives (`D = −(G₁ + I₂)` and the operator-field
identification `⟨appCc (covGrad Φ₀) S, ∇S⟩ = G₄ − I₂`, both `ParsevalSevenTermBochnerFold`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- **The differentiated-curvature operator-field pairing equals the gradient-of-base pairing minus the
passenger-slot pairing (the `L²`-level B-rule split, sorry-free).** The global metric `L²` pairing of the
differentiated-curvature operator-field section `genuineDiffCurvSection g s S = appCc (covGrad Φ₀) S`
(`Φ₀ := curvOpField g s`) against `∇S := covGrad g 0 s S` equals the pairing of the covariant gradient of
the order-`0` pure-Riemann curvature trace `∇(pureRGenuineDiffOp g 0 s S)` against `∇S`, minus the pairing
of the passenger-slot operator-field action `appCc (slotExtend Φ₀) (∇S)` against `∇S`:
```
⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}
  = ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²} − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²}.
```

This is the `L²`-pairing reading of the section-level B-rule inversion
`genuineDiffCurvSection_eq_covGrad_sub_slotExtend` (`genuineDiffCurvSection g s S =
∇(pureRGenuineDiffOp g 0 s S) − appCc (slotExtend Φ₀) (∇S)`): rearranged to the additive form
`∇(pureRGenuineDiffOp g 0 s S) = genuineDiffCurvSection g s S + appCc (slotExtend Φ₀) (∇S)`, the left
additivity of the `L²` pairing `tensorL2Inner_add_left` (with the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) splits the gradient-of-base pairing into the two summand pairings.
It is the bridge through which the operator-field atom's right-hand side
`⟨appCc (covGrad Φ₀) S, ∇S⟩` is identified with the operator residue's right-hand side
`⟨∇(pureRᵍ S), ∇S⟩ − ⟨appCc (slotExtend Φ₀)(∇S), ∇S⟩`; sorry-free. -/
private theorem tensorL2Inner_genuineDiffCurv_eq_covGradBase_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- The section-level B-rule inversion `genuineDiffCurvSection g s S = ∇(pureRᵍ S) − appCc (slotExtend Φ₀)(∇S)`,
  -- rearranged to the additive form `∇(pureRᵍ S) = genuineDiffCurvSection g s S + appCc (slotExtend Φ₀)(∇S)`.
  have hsec := genuineDiffCurvSection_eq_covGrad_sub_slotExtend (I := I) (M := M) g s S
  rw [eq_sub_iff_add_eq] at hsec
  simp only [Nat.add_zero] at hsec
  -- The atom-2 right-hand carrier `appCc Φ₀'-form` is the differentiated-curvature section by definition.
  have hatom : (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun =
      (genuineDiffCurvSection (I := I) (M := M) g s S).toFun := rfl
  -- Left additivity of the `L²` pairing on the additive form, via the cross-integrabilities.
  have hadd := tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (genuineDiffCurvSection (I := I) (M := M) g s S).toFun
      (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S)).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (genuineDiffCurvSection (I := I) (M := M) g s S)
        (covGrad (I := I) (M := M) g 0 s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S))
        (covGrad (I := I) (M := M) g 0 s S))
  simp only [Nat.add_zero] at hadd
  rw [hatom, ← hsec, SmoothCcTensor.toFun_add, hadd]
  ring

/-- **The integrated tensor Bochner extraction (the frame-free four-pairing value of the curvature
cross-pairing).**  The global metric `L²` pairing of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` against `∇S := covGrad g 0 s S` splits into the pure-Riemann
curvature trace, the Bochner–Lichnerowicz Ricci trace, and the differentiated-curvature (`∇R`)
operator-field content in residue form:
```
⟨Curv S, ∇S⟩_{L²}
  = ⟨GcurvSection g s S, ∇S⟩_{L²} + ⟨ricTraceSection g s S, ∇S⟩_{L²}
      + ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²}
      − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²},   Φ₀ := curvOpField g s.
```
Sorry-free glue over the healthy upstream three-section value
`tensorL2Inner_curv_covGrad_eq_genuineThreeSection_value` (`MovingFrameRemainderFrameSumBridge`,
itself glue over the seven-term Parseval fold chain of `ParsevalSevenTermBochnerFold`) and the
sorry-free `L²` B-rule split `tensorL2Inner_genuineDiffCurv_eq_covGradBase_sub_slotExtend`.  It
does NOT transit any per-group Bochner-fold value (the former fold route through `G₃ = ricTrace` and
`G₂ + G₄ = operator residue` was deleted — those per-group values are FALSE in dim ≥ 3,
`PROVE_REFUTED.md`); consumers transitively depend on the `sorryAx` of the two posited fold
primitives (`D = −(G₁ + I₂)` and the operator-field identification
`⟨appCc (covGrad Φ₀) S, ∇S⟩ = G₄ − I₂`). -/
theorem tensorL2Inner_curv_covGrad_eq_gcurvRicOperatorResidue_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hStar := tensorL2Inner_curv_covGrad_eq_genuineThreeSection_value (I := I) (M := M) g s S
  have hB := tensorL2Inner_genuineDiffCurv_eq_covGradBase_sub_slotExtend (I := I) (M := M) g s S
  linarith [hStar, hB]

end Connection
end Integral
end DifferentialGeometry

end
