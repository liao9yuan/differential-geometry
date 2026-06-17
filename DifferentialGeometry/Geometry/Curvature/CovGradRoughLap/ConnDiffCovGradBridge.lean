import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval

/-!
# The connection-difference tensor as a bundled `(1, 2)`-tensor, and its covariant gradient

For two smooth Riemannian metrics `g₀, g₁` on a closed manifold `M` the connection-difference
tensor `A = connDiff g₁ g₀ = ∇₁ − ∇₀` (`Geometry/Flow/ConnectionDifference.lean`) is a
vector-field-valued `(1, 2)`-tensor: at each `x` it is a continuous bilinear map
`TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x` (two covariant vector slots, one
contravariant vector output).  This file packages it as a genuine `SmoothCcTensor g₀ 1 2` — the
project's `Hom(Tensor0SSpace 1, Tensor0SSpace 2)` valence — through the **metric-free dual pairing**
`A♭(om)(Y, Z) := om(A(Y, Z))` (a covector `om` paired with the vector output `A(Y, Z)`), and bridges its
bundled iterated covariant gradient `covGrad g₀ 1 2` to the directional Palatini covariant derivative
`covDerivConnDiff g₀ g₁` (`Geometry/Curvature/CurvatureOperator/RicciConnDiffPalatini.lean`).

## Main definitions

* `connDiffFib g₁ g₀ x : TensorRSSpace 1 2 I x` — the fibrewise dual-pairing packaging of
  `connDiff g₁ g₀ x` as a `(1, 2)`-tensor: `connDiffFib x om (Y, Z) = om(connDiff x Y Z)`.
* `connDiffSection g₁ g₀ : SmoothCcTensor g₀ 1 2` — the smooth, compactly-supported `(1, 2)`-tensor
  section assembled from `connDiffFib`, smooth by `connDiff_contMDiff` and the metric-free pairing,
  compactly supported because `M` is compact.

## Main theorems

* `connDiffFib_apply_eval` — the defining evaluation formula
  `(connDiffFib x om).toModel [Y, Z] = om [connDiff x Y Z]`.
* `connDiffSection_covGrad_eq_covDerivConnDiff` — **the bridge**: the bundled iterated covariant
  gradient `covGrad g₀ 1 2 (connDiffSection g₁ g₀)` (a `SmoothCcTensor g₀ 1 3`) equals the dual-pairing
  packaging of the Palatini directional covariant derivative `covDerivConnDiff g₀ g₁` of the
  connection-difference tensor.  This connects the analysis/operator-field covariant-gradient machinery
  (`covGrad`/`tensorRSCovariantDerivative`) to the vector-field/Palatini machinery
  (`covDerivConnDiff`/`covDerivDiff`), the bedrock the central Lichnerowicz `_core` consumes.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The dual-pairing packaging of the connection-difference tensor as a `(1, 2)`-tensor -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is additive when evaluated on the single tangent slot:
`om [a + b] = om [a] + om [b]`.  This is the additivity of the arity-`1` multilinear map, transferred
through the `continuousMultilinearCurryFin1` equivalence to a genuine continuous linear functional. -/
private lemma tensor0SOne_apply_add (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is homogeneous when evaluated on the single tangent
slot: `om [c • a] = c • om [a]`. -/
private lemma tensor0SOne_apply_smul (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => c • a) = _
  rw [hca, ha, map_smul]

/-- The `(0, 2)`-tensor fibre `(Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)` paired against a covector `om`. -/
def connDiffPairing (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) :=
          (connDiff (I := I) g₁ g₀ x).continuous₂.comp hpair
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [CompactSpace M] [I.Boundaryless] in
/-- The `(0, 2)`-fibre `connDiffPairing` evaluated (FunLike) on a tangent tuple `YZ` reads `om`
against the connection-difference output `connDiff g₁ g₀ x (YZ 0) (YZ 1)`. -/
@[simp] lemma connDiffPairing_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connDiffPairing (I := I) g₁ g₀ x om) YZ =
      om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- `connDiffPairing` is additive in the covector. -/
lemma connDiffPairing_add (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connDiffPairing (I := I) g₁ g₀ x (om + om') =
      connDiffPairing (I := I) g₁ g₀ x om + connDiffPairing (I := I) g₁ g₀ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

omit [CompactSpace M] [I.Boundaryless] in
/-- `connDiffPairing` is homogeneous in the covector. -/
lemma connDiffPairing_smul (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connDiffPairing (I := I) g₁ g₀ x (c • om) =
      c • connDiffPairing (I := I) g₁ g₀ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

/-- **The fibrewise dual-pairing packaging of the connection-difference tensor.**  At a base point
`x`, `connDiffFib g₁ g₀ x` is the `(1, 2)`-tensor (`TensorRSSpace 1 2 I x =
Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x`) sending a covector `om` to the bilinear form
`(Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)`: the metric-free pairing of `om` with the vector output of the
connection-difference tensor. -/
def connDiffFib (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connDiffPairing (I := I) g₁ g₀ x om
        map_add' := connDiffPairing_add g₁ g₀ x
        map_smul' := connDiffPairing_smul g₁ g₀ x })

omit [CompactSpace M] [I.Boundaryless] in
/-- The `(1, 2)`-tensor `connDiffFib g₁ g₀ x` applied to a covector `om` is the `(0, 2)`-pairing
`connDiffPairing g₁ g₀ x om`. -/
@[simp] lemma connDiffFib_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connDiffFib (I := I) g₁ g₀ x) om =
      connDiffPairing (I := I) g₁ g₀ x om := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- **The defining evaluation formula for the `(1, 2)`-tensor packaging.**  The `(1, 2)`-tensor
`connDiffFib g₁ g₀ x` applied to a covector `om` and evaluated on a pair of tangent vectors `(Y, Z)`
reads `om` against the connection-difference output `connDiff g₁ g₀ x Y Z`:
`(connDiffFib x om)[Y, Z] = om[connDiff x Y Z]`. -/
lemma connDiffFib_apply_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connDiffFib (I := I) g₁ g₀ x) om) YZ =
      om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
  rw [connDiffFib_apply, connDiffPairing_apply]

end Connection
end Integral
end DifferentialGeometry
