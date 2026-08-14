import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRefoldPairing

noncomputable section


open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem riemannC2_eq_kernel
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) (s : ℝ) :
    riemannPalatiniRefoldC2Family
        (I := I) (M := M) g T hδ hδZ qA qB s =
      s • curvatureRefoldKernelCoeffField (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g
          (symmS (I := I) (M := M) g T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
          (symmS (I := I) (M := M) g T))
        (qA 0) (qA 1) (qA 2) (qA 3) := by
  have h0 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ s) T (qA 0)
  have h1 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ s) T (qA 1)
  have h2 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ s) T (qA 2)
  have h3 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ s) T (qA 3)
  rw [riemannPalatiniRefoldC2Family, hq 0, hq 1, hq 2, hq 3]
  simp only [Equiv.Perm.mul_def, curvatureRefoldKernelCoeffField,
    curvatureActionKernelCoeffField]
  rw [← h0, ← h1, ← h2, ← h3]
  module

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
