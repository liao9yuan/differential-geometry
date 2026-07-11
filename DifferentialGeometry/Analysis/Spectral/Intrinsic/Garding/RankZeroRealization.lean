import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FractionalPower
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Tensor.RSTensor.RankZero

/-!
# Rank-zero spectral realization

This file identifies the rough connection Laplacian of a finite-support
rank-zero spectral representative both with the spectral scale Laplacian in
`L²` and with the invariant scalar Laplace--Beltrami operator pointwise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The rank-zero spectral rough Laplacian at base Sobolev order zero, with its
domain normalized from `H^(0 + 2)` to `H²`. -/
noncomputable def scalarScaleLap (g : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g 0 0 2 →L[ℝ]
      tensorHs (I := I) (M := M) g 0 0 0 :=
  (tensorScaleLaplacian (I := I) (M := M)
    (g := g) (r := 0) (s := 0) 0).comp
      (tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0)
        (by norm_num : (2 : ℝ) = 0 + 2)).toContinuousLinearEquiv.toContinuousLinearMap

omit [BoundarylessManifold I M] in
/-- The scalar scale Laplacian multiplies the `i`-th coordinate by `-λᵢ`. -/
@[simp] theorem scalarScaleLap_coeff
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 0) :
    (scalarScaleLap (I := I) (M := M) g v).coeff i =
      -TensorEigenIdx.lambda (I := I) (M := M) i * v.coeff i := by
  simp only [scalarScaleLap, ContinuousLinearMap.comp_apply,
    tensorScaleLaplacian_coeff]
  change -TensorEigenIdx.lambda (I := I) (M := M) i *
      (tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0) _ v).coeff i =
    -TensorEigenIdx.lambda (I := I) (M := M) i * v.coeff i
  rw [tensorHs.castEquiv_coeff]

omit [BoundarylessManifold I M] in
/-- The scalar spectral Laplacian is norm-non-increasing from `H²` to `H⁰`. -/
theorem norm_scalarLap_le
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2) :
    ‖scalarScaleLap (I := I) (M := M) g v‖ ≤ ‖v‖ := by
  change ‖scaleLaplacianFun (I := I) (M := M)
      (tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0) _ v)‖ ≤ ‖v‖
  calc
    _ ≤ ‖tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0) _ v‖ :=
      norm_scaleLaplacianFun_le (I := I) (M := M) _
    _ = ‖v‖ := (tensorHs.castEquiv (I := I) (M := M)
      (g := g) (r := 0) (s := 0) _).norm_map v

/-- The genuine smooth scalar represented by a finite-support rank-zero
spectral Sobolev element. -/
noncomputable def reprScalar0
    {g : SmoothRiemannianMetric I M}
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) : M → ℝ :=
  TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
    (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection

omit [BoundarylessManifold I M] in
/-- The scalar readout of the finite rank-zero spectral representative is
smooth. -/
theorem reprScalar0_smooth
    {g : SmoothRiemannianMetric I M}
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ContMDiff I 𝓘(ℝ) ∞ (reprScalar0 (I := I) (M := M) v hv) :=
  TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞))
    (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection

omit [BoundarylessManifold I M] in
/-- The finite rank-zero spectral representative is the canonical mixed lift
of its scalar readout. -/
theorem repr_eq_lift
    {g : SmoothRiemannianMetric I M}
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    (Tensor0SField.fromScalarField ∞
      (reprScalar0 (I := I) (M := M) v hv)
      (reprScalar0_smooth (I := I) (M := M) v hv)).toTensorRSField ∞ =
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection := by
  simpa [reprScalar0] using
    (TensorRSField.lift_scalar0 (n := (∞ : WithTop ℕ∞))
      (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection)

/-- Pointwise, the rough Laplacian of the finite rank-zero spectral
representative is the canonical lift of its invariant scalar Laplacian. -/
theorem rawLap_repr_scalar
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) (x : M) :
    rawTensorConnLap (I := I) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection x =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (laplacian (I := I) (LeviCivita (I := I) g) g
            (reprScalar0 (I := I) (M := M) v hv) x)) := by
  rw [← repr_eq_lift (I := I) (M := M) v hv]
  exact rawLap_scalar (I := I) (M := M) g
    (reprScalar0_smooth (I := I) (M := M) v hv) x

/-- In fixed-metric `L²`, the rough Laplacian of a finite-support smooth
representative is exactly the spectral scale Laplacian. -/
theorem rawLap_repr_toL2
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    SmoothCcTensor.toL2
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv)) =
      tensorHsToL2 (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (show (0 : ℝ) ≤ 0 by norm_num)
        (scalarScaleLap (I := I) (M := M) g v) := by
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc).repr.injective
  ext i
  change tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv))) i =
    tensorL2Coeff (I := I) (M := M) hc
      (tensorHsToL2 (I := I) (M := M) hc
        (show (0 : ℝ) ≤ 0 by norm_num)
        (scalarScaleLap (I := I) (M := M) g v)) i
  rw [rawLap_coeff (I := I) (M := M) g 0 hc
      (tensorHsSmoothRepr (I := I) (M := M) v hv) i]
  have hrepr := tensorHsSmoothRepr_toL2 (I := I) (M := M)
    (show (0 : ℝ) ≤ 2 by norm_num) v hv
  rw [SmoothCcTensor.toL2_apply, hrepr, tensorHsToL2_tensorL2Coeff,
    tensorHsToL2_tensorL2Coeff, scalarScaleLap_coeff]

/-- The fixed-metric rough Laplacian estimate for a finite spectral
representative, with a constant independent of its spectral support. -/
theorem rawLap_repr_norm
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv))‖ ≤ ‖v‖ := by
  rw [rawLap_repr_toL2 (I := I) (M := M) g v hv,
    tensorHsToL2_apply]
  exact (tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
    (show (0 : ℝ) ≤ 0 by norm_num)
    (scalarScaleLap (I := I) (M := M) g v)).trans
      (norm_scalarLap_le (I := I) (M := M) g v)

/-- The covariant gradient of a finite rank-zero spectral representative is
bounded in fixed-metric `L²` by its spectral `H²` norm, independently of the
finite support. -/
theorem grad_repr_norm
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ‖SmoothCcTensor.toL2
        (covGrad (I := I) (M := M) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv))‖ ≤ ‖v‖ := by
  let S : SmoothCcTensor g 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) v hv
  rw [SmoothCcTensor.norm_toL2]
  have hgreen :
      ‖covGrad (I := I) (M := M) g 0 0 S‖ ^ 2 ≤
        ‖rawTensorConnLapSmooth (I := I) g 0 0 S‖ * ‖S‖ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
        (covGrad (I := I) (M := M) g 0 0 S),
      SmoothCcTensor.norm_def (I := I) (M := M)
        (rawTensorConnLapSmooth (I := I) g 0 0 S),
      SmoothCcTensor.norm_def (I := I) (M := M) S]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self_gen
      (I := I) (M := M) g 0 S
  have hLap : ‖rawTensorConnLapSmooth (I := I) g 0 0 S‖ ≤ ‖v‖ := by
    rw [← SmoothCcTensor.norm_toL2]
    simpa [S] using rawLap_repr_norm (I := I) (M := M) g v hv
  have hS : ‖S‖ ≤ ‖v‖ := by
    rw [← SmoothCcTensor.norm_toL2]
    change ‖SmoothCcTensor.toL2
      (tensorHsSmoothRepr (I := I) (M := M) v hv)‖ ≤ ‖v‖
    rw [SmoothCcTensor.toL2_apply,
      tensorHsSmoothRepr_toL2 (I := I) (M := M)
        (show (0 : ℝ) ≤ 2 by norm_num) v hv,
      tensorHsToL2_apply]
    exact tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
      (show (0 : ℝ) ≤ 2 by norm_num) v
  have hprod :
      ‖rawTensorConnLapSmooth (I := I) g 0 0 S‖ * ‖S‖ ≤ ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖v‖ * ‖v‖ :=
        mul_le_mul hLap hS (norm_nonneg S) (norm_nonneg v)
      _ = ‖v‖ ^ 2 := by ring
  nlinarith [le_trans hgreen hprod,
    norm_nonneg (covGrad (I := I) (M := M) g 0 0 S), norm_nonneg v]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
