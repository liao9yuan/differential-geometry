import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MovingPairTrace

/-!
# Exact Ricci--DeTurck refold pairing

This file contains the exact algebraic pair-trace identities used to move the
second derivatives hidden in the order-zero Ricci--DeTurck coefficient into an
explicit order-two coefficient.  It deliberately has no energy, Green identity,
or high-regularity assumptions.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The Ricci order-zero combination left after adding and subtracting one
Riemann coefficient. -/
def edgeRicciHalf (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g g₁ +
    (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g g₁

/-- A frame-paired Ricci C2 family is the corresponding Palatini kernel
weighted by the symmetric part of the metric deviation. -/
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
  simp only [Equiv.Perm.mul_def, curvatureRefoldKernelCoeffField]
  rw [← h0, ← h1, ← h2, ← h3]
  module

private lemma edge_rank0_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) •
      unitZeroSec (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitZeroSec_apply, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

/-- The moving-metric pair trace arranged so that applying it to a rank-two
tensor reproduces one Palatini refold monomial. -/
def edgePairMono (g gm : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 6 2
    (mvPairTraceOp (I := I) (M := M) g gm)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (domDomCongrSection (I := I) g
          (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
/-- One moving pair-trace action is exactly one Palatini refold monomial. -/
theorem edgeMonoRefold (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    appCc (I := I) (M := M) g 2 2
        (edgePairMono (I := I) (M := M) g gm G σ) S =
      appCc (I := I) (M := M) g 4 2
        (curvatureRefoldMonomialCoeffField (I := I) (M := M) g gm
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ) G := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection]
  apply ContinuousLinearMap.ext
  intro t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [edge_rank0_decomp (I := I) (M := M) x t]
  simp only [map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [mvPairTrace_apply (I := I) (M := M) g gm
    (domDomCongrSection (I := I) g
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitZeroSec (I := I) (M := M) x)) v]
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (curvatureRefoldMonomialCoeffField (I := I) (M := M) g gm
        (ccTensorUnitValueSection (I := I) (M := M) g S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ).toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitZeroSec (I := I) (M := M) x))) =
    curvatureRefoldMonomialBiContrFib (I := I) (M := M) gm
      (ccTensorUnitValueSection (I := I) (M := M) g S) σ x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitZeroSec (I := I) (M := M) x)) from rfl]
  rw [curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (domDomCongrSection (I := I) g
          (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g 4
        (domDomCongrSection (I := I) g
          (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G) x
      from rfl]
  simp only [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg₂ (· * ·) rfl ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
    unitModel (I := I) (M := M) g 4 G x from rfl]
  refine congrArg _ ?_
  funext i
  rw [Equiv.trans_apply]
  generalize σ i = k
  fin_cases k <;> rfl

/-- Pair-trace form of the DeTurck part of the second-order refold family. -/
def edgeLiePairFam (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  s • ∑ i : Fin 3, ε i • ((1 / 2 : ℝ) •
    (edgePairMono (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) (q i)
      + edgePairMono (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

/-- The DeTurck second-order action is exactly the application of its
rank-two pair-trace form to the metric difference. -/
theorem edgeLiePair_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ)
    (s : ℝ) :
    appCc (I := I) (M := M) g 2 2
        (edgeLiePairFam (I := I) (M := M) g T hδ hδZ q ε s) T =
      appCc (I := I) (M := M) g 4 2
        (deTurckLieCovDerivRefoldC2Family
          (I := I) (M := M) g T hδ hδZ q ε s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [edgeLiePairFam, deTurckLieCovDerivRefoldC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_smul_left, appCc_add_left]
  rw [edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 0),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 0).trans (Equiv.swap (0 : Fin 4) 1)),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 1),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 1).trans (Equiv.swap (0 : Fin 4) 1)),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 2),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 2).trans (Equiv.swap (0 : Fin 4) 1))]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
