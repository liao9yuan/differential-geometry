import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJet1Diff
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifJetTowerMatch
import DifferentialGeometry.Tensor.Mixed.Field

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Tensor

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


def ccOfField (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ A
  hasCompactSupport := HasCompactSupport.of_compactSpace _


@[simp] theorem ccOfField_unit (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    ccUnitField (I := I) g s (ccOfField (I := I) g s A) = A :=
  MixedSection.toMultilinearSection_fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ A

theorem rfns_ccOfField_eq (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j (ccOfField (I := I) g s A)).toSection x) =
      normSq0S (I := I) g x (s + j) (iterCov (I := I) g s A j x) := by
  rw [rfns_iterCovGrad_eq (I := I) g s j (ccOfField (I := I) g s A) x, ccOfField_unit]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in

private theorem zeroS_eq_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hunit :
      Tensor0SNabla.tensor0Iso I M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitZeroSec_apply] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem rs0_apply_eq_smul {s : ℕ} (x : M)
    (Φ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace 0 I x) :
    Φ D = (Tensor0SNabla.tensor0Iso I M x D) • Φ (unitZeroSec (I := I) (M := M) x) := by
  conv_lhs => rw [zeroS_eq_unit (I := I) (M := M) x D]
  rw [map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
theorem cc_ext_unit (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W₁ W₂ : SmoothCcTensor g 0 s)
    (h : ∀ x : M, ccUnitField (I := I) g s W₁ x = ccUnitField (I := I) g s W₂ x) :
    W₁ = W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  rw [rs0_apply_eq_smul (I := I) (M := M) x
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₁.toSection x) D,
    rs0_apply_eq_smul (I := I) (M := M) x
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₂.toSection x) D]
  exact congrArg _ (h x)

theorem iterCovGrad_ccOfField (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    iteratedCovGrad (I := I) g 0 s j (ccOfField (I := I) g s A) =
      ccOfField (I := I) g (s + j) (iterCov (I := I) g s A j) := by
  refine cc_ext_unit (I := I) g _ _ (fun x => ?_)
  have hL := congrFun
    (iterCovGrad_unit_eq (I := I) g s (ccOfField (I := I) g s A) j) x
  rw [ccOfField_unit (I := I) g s A] at hL
  have hR : ccUnitField (I := I) g (s + j)
      (ccOfField (I := I) g (s + j) (iterCov (I := I) g s A j)) x =
      iterCov (I := I) g s A j x := by
    rw [ccOfField_unit (I := I) g (s + j) (iterCov (I := I) g s A j)]
  rw [hR]
  exact hL


def rmSection (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 4 :=
  ccOfField (I := I) g 4 (metricRm04 (I := I) (M := M) g)


@[simp] theorem rmSection_unit (g : SmoothRiemannianMetric I M) :
    ccUnitField (I := I) g 4 (rmSection (I := I) (M := M) g) =
      metricRm04 (I := I) (M := M) g :=
  ccOfField_unit (I := I) g 4 (metricRm04 (I := I) (M := M) g)

theorem rfns_rmSection_eq (g : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j (rmSection (I := I) (M := M) g)).toSection x) =
      normSq0S (I := I) g x (4 + j)
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) j x) :=
  rfns_ccOfField_eq (I := I) g 4 j (metricRm04 (I := I) (M := M) g) x

theorem iterCovGrad_rmSection (g : SmoothRiemannianMetric I M) (a : ℕ) :
    iteratedCovGrad (I := I) g 0 4 a (rmSection (I := I) (M := M) g) =
      ccOfField (I := I) g (4 + a)
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) a) :=
  iterCovGrad_ccOfField (I := I) g 4 a (metricRm04 (I := I) (M := M) g)

private theorem sqLeOfSqrtLe {a K : ℝ} (ha : 0 ≤ a) (h : Real.sqrt a ≤ K) :
    a ≤ K ^ 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

theorem exists_rmJetSup (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + a) x
          ((iteratedCovGrad (I := I) g 0 4 a (rmSection (I := I) (M := M) g)).toSection x) ≤
        K ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_curvJet_sup (I := I) (M := M) g a
  refine ⟨K, hK0, fun x => ?_⟩
  refine sqLeOfSqrtLe (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (4 + a) x _) ?_
  rw [rfns_rmSection_eq (I := I) g a x]
  exact hK x

theorem exists_rmJetSups (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ a, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j (rmSection (I := I) (M := M) g)).toSection x) ≤
        K ^ 2 := by
  induction a with
  | zero =>
      obtain ⟨K, hK0, hK⟩ := exists_rmJetSup (I := I) (M := M) g 0
      refine ⟨K, hK0, fun j hj x => ?_⟩
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact hK x
  | succ a ih =>
      obtain ⟨K, hK0, hK⟩ := ih
      obtain ⟨K', hK'0, hK'⟩ := exists_rmJetSup (I := I) (M := M) g (a + 1)
      refine ⟨max K K', le_trans hK0 (le_max_left _ _), fun j hj x => ?_⟩
      rcases eq_or_lt_of_le hj with rfl | hlt
      · have hmono : K' ^ 2 ≤ max K K' ^ 2 := by nlinarith [le_max_right K K']
        exact le_trans (hK' x) hmono
      · have hmono : K ^ 2 ≤ max K K' ^ 2 := by nlinarith [le_max_left K K']
        exact le_trans (hK j (Nat.lt_succ_iff.mp hlt) x) hmono


theorem unifRmSecSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((rmSection (I := I) (M := M) g₀).toSection x) ≤ C ^ 2 := by
  obtain ⟨C, hC0, hC⟩ :=
    unifRm04Sup (I := I) (M := M) gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2
  refine ⟨C, hC0, fun x => ?_⟩
  have hkey : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((rmSection (I := I) (M := M) g₀).toSection x) =
      normSq0S (I := I) g₀ x 4 (metricRm04 (I := I) (M := M) g₀ x) :=
    rfns_rmSection_eq (I := I) g₀ 0 x
  refine sqLeOfSqrtLe (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x _) ?_
  rw [hkey]
  exact hC x

end RicciFlow
end PDE
end DifferentialGeometry
