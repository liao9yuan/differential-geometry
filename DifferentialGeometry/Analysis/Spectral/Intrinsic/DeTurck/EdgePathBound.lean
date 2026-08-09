import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePartnerBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePathPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer

/-!
# Pointwise bound for the path-integrated closed-edge partner

This module transfers the complete fixed-path-parameter bound for the raw
closed-edge formal partner through `pathIntegralCoeffField`.  The resulting
bound keeps the passenger and test tensors independent and does not perform
spatial integration by parts.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped BigOperators Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private abbrev JointRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Set Real)
    (Φ : Real → SmoothCcTensor g r s) : Prop :=
  ContMDiffOn (I.prod 𝓘(Real, Real))
    (I.prod 𝓘(Real, TensorRSModel r s Real E)) ∞
    (fun p : M × Real => TotalSpace.mk' (TensorRSModel r s Real E)
      (E := fun x : M => TensorRSSpace r s I x) p.1
      ((Φ p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ S)

/-- A pointwise fibre cap transfers unchanged through a unit-length smooth
coefficient path integral. -/
private theorem fiber_path_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Real → SmoothCcTensor g r s) (S : Set Real)
    (hS : IsOpen S) (hSI : Set.uIcc (0 : Real) 1 ⊆ S)
    (hjoint : JointRS (I := I) g r s S Φ)
    (x : M) (A : Real) (hA : 0 ≤ A)
    (hsup : ∀ t ∈ Set.Icc (0 : Real) 1,
      fiberLpFun g r s (Φ t) x ≤ A) :
    fiberLpFun g r s
        (pathIntegralCoeffField (I := I) (M := M) g r s
          Φ S hS hSI hjoint) x ≤ A := by
  have hIcc : Set.Icc (0 : Real) 1 ⊆ S := by
    simpa only [Set.uIcc_of_le zero_le_one] using hSI
  have hcont : ContinuousOn
      (fun t : Real => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.Icc (0 : Real) 1) :=
    (jointContMDiff_toModel_continuous_slice
      (I := I) g r s Φ S hjoint x).mono hIcc
  have hsq :=
    riemannianFiberNormSq_pathIntegralCoeffField_le_sq
      (I := I) (M := M) g r s Φ S hS hSI hjoint x A hA hcont
      (fun t ht => by simpa only [fiberLpFun] using hsup t ht)
  have hroot := Real.sqrt_le_sqrt hsq
  simpa only [fiberLpFun, Real.sqrt_sq hA] using hroot

/-- The complete path-integrated raw top partner is pointwise bilinear in its
passenger and test tensors, with one coefficient chosen before the metric,
raw permutations, and path vary. -/
theorem edgeTopInt_zero_unif :
    ∃ K : Real, 0 ≤ K ∧
      ∀ (g : SmoothRiemannianMetric I M)
        (T P V : SmoothCcTensor g 0 2) {delta : Real},
        0 ≤ delta → delta ≤ 1 / 2 →
        ∀ (hdelta_lt : delta < 1)
          (hdelta : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) delta)
          (hdeltaZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) delta)
          (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ x : M,
            fiberLpFun g 0 4
                (edgeTopPartnerInt (I := I) (M := M) g T P V
                  hdelta_lt hdelta hdeltaZ qA qB q epsilon) x ≤
              K * fiberLpFun g 0 2 P x * fiberLpFun g 0 2 V x := by
  obtain ⟨K, hK, htop⟩ := edgeTopBi_zero_unif (I := I) (M := M)
  refine ⟨K, hK, ?_⟩
  intro g T P V delta hdelta0 hdelta_half hdelta_lt hdelta hdeltaZ
    qA qB q epsilon hepsilon x
  unfold edgeTopPartnerInt
  apply fiber_path_le (I := I) (M := M)
  · exact mul_nonneg
      (mul_nonneg hK (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · intro t ht
    exact htop g T P V hdelta0 hdelta_half hdelta hdeltaZ
      qA qB q epsilon hepsilon t ht x

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
