import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricLoweringTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifJetTowerMatch
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifReverseJetTwo

/-!
# Three-dimensional class-uniform Morrey estimates for mixed tensors

The existing class-uniform Morrey theorem is covariant: it applies to
`SmoothCcTensor g 0 s`.  The live short-time consumers also need mixed tensors,
first at valence `(3, 2)`.  This file lowers every upper index with the variable
metric `g`, applies the covariant theorem at rank `r + s`, and transfers the
pointwise and `L²` jet norms back by the exact same-metric lowering isometry.

The public interface is deliberately three-dimensional.  It is generic in the
mixed valence `(r, s)`, while the Sobolev window is fixed to the exact orders
`0,1,2`.  A later general-dimensional API can replace this finite window without
changing the lowering layer.
-/

set_option autoImplicit false

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The explicit class-uniform mixed Morrey constant in dimension three.
The two reverse metric-jet constants and every Sobolev constant are selected
from the fixed background and `Λ` before the class metric varies. -/
def morreyRSC (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (r s : ℕ) : ℝ :=
  let L₁ := max (revJetOneC (E := E) Λ) Λ
  let L₂ := revJetTwoC (E := E) Λ
  morreyUnifConst Λ
    (baseMorreyConst (I := I) (M := M) gBase 0 (r + s))
    (kjetConst (Module.finrank ℝ E) Λ L₁ L₂ (r + s))
    (Module.finrank ℝ E) (r + s)

/-- The explicit mixed Morrey constant is nonnegative when `1 ≤ Λ`. -/
lemma morreyRSC_nonneg (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (r s : ℕ) :
    0 ≤ morreyRSC (I := I) (M := M) gBase Λ r s := by
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ
  have hL₁ : 0 ≤ max (revJetOneC (E := E) Λ) Λ :=
    hΛ0.trans (le_max_right _ _)
  have hL₂ : 0 ≤ revJetTwoC (E := E) Λ := by
    dsimp [revJetTwoC]
    exact le_max_left _ _
  unfold morreyRSC
  exact morreyUnifConst_nonneg hΛ0
    (baseMorreyConst_nonneg (I := I) (M := M) gBase 0 (r + s))
    (kjetConst_nonneg hΛ0 hL₁ hL₂ (Module.finrank ℝ E) (r + s))
    (Module.finrank ℝ E) (r + s)

/-- **Class-uniform mixed Morrey in dimension three.**

For fixed `gBase`, `Λ`, and valence `(r,s)`, one nonnegative constant is chosen
before the class metric `g` varies.  Uniform equivalence and the first two
forward metric jets bounded by `Λ` then control the pointwise mixed fibre norm
by the `L²` covariant-jet window `j = 0,1,2`. -/
theorem morreyRS_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (S : SmoothCcTensor g r s) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g r s x
              (S.toSection x) ≤
            C ^ 2 * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
  refine ⟨morreyRSC (I := I) (M := M) gBase Λ r s,
    morreyRSC_nonneg (I := I) (M := M) gBase hΛ r s, ?_⟩
  intro g hEq hjet1 hjet2 S x
  let L₁ := max (revJetOneC (E := E) Λ) Λ
  let L₂ := revJetTwoC (E := E) Λ
  obtain ⟨hL₁, hL₂, hfwd1, hrev1, hrev2⟩ :=
    reverseJetPack (I := I) gBase g hEq hjet1 hjet2
  have hwin : Module.finrank ℝ E / 2 + 2 = 3 := by omega
  have hcov := fibreMorrey_unif_class (I := I) gBase g
    (Λ' := L₁) (Λ'' := L₂) hEq hfwd1 hrev1 hrev2 hL₁ hL₂ hwin
    (r + s) (lowerCc (I := I) (M := M) g r s S) x
  have hcov3 :
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + s) x
          ((lowerCc (I := I) (M := M) g r s S).toSection x) ≤
        morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 (r + s) j
              (lowerCc (I := I) (M := M) g r s S)‖ ^ 2 := by
    simpa only [morreyRSC, L₁, L₂, hwin] using hcov
  calc
    riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + s) x
          ((lowerCc (I := I) (M := M) g r s S).toSection x) :=
      (lowerCc_rfns (I := I) (M := M) g r s S x).symm
    _ ≤ morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (r + s) j
            (lowerCc (I := I) (M := M) g r s S)‖ ^ 2 := hcov3
    _ = morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j S‖ ^ 2 := by
      apply congrArg (fun z : ℝ => morreyRSC (I := I) (M := M) gBase Λ r s ^ 2 * z)
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj2 : j ≤ 2 := by
        have hj3 := Finset.mem_range.mp hj
        omega
      rw [lowerCc_jet_norm (I := I) (M := M) g r s j S hj2]

end RicciFlow
end PDE
end DifferentialGeometry

end
