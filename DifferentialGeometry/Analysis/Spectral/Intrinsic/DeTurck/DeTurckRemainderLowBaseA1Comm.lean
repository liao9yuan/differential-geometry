import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBasePair

/-!
# Bundle-generic facts about one low-base first-order action

For ANY low-base action bundle — in particular for an arbitrary DeTurck
background — the two adjacent-scale completions `a1Hi : H3 → H2` and
`a1Lo : H2 → H1` are the completions of one smooth-core formula.  This
module records the three consequences that need no coefficient estimate at
the call site:

* `a1_comm`: the commuting square `incl ∘ a1Hi = a1Lo ∘ incl`;
* `a1Hi_app` / `a1Lo_app`: each completion realizes the smooth-core action
  `A.a1` on the dense smooth range;
* `a1Hi_add` / `a1Lo_add`: both completions are additive in the coefficient
  data, so a bundle whose `C0` and `C1` split as a sum has completions that
  split the same way.

The additivity pair is what lets a refolded bundle be certified by summing
the affine packets of its summands: the packet produces a sum of `a1Hi`s,
while the refold identity is phrased on the summed bundle.

Everything is re-assembled from the PUBLIC producers `a1_pair`, `a1_h3_h2`,
`a1_h2_h1` rather than by editing the oversized settled module
`DeTurckRemainderLowBaseLip.lean` (which keeps a private `a1_comm_any`),
whose full re-elaboration exceeds the focused-check memory budget.  If that
module is ever legitimately rebuilt, its private `a1_comm_any` should be
replaced by `a1_comm` (this file does not import it, so no cycle arises).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
private theorem jetNN
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ lowJetSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The two smooth-core jet estimates of one first-order low-base action hold
with a single explicit constant assembled from the action's own coefficient
jets.  No hypothesis on the bundle is needed, so every bundle-generic
consequence of `a1_pair` is available through this producer. -/
private theorem a1_jetQ
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      (∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 2
            (A.a1 (I := I) (M := M) W) ≤
          Q * lowJetSq (I := I) (M := M) g 3 W) ∧
      (∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 1
            (A.a1 (I := I) (M := M) W) ≤
          Q * lowJetSq (I := I) (M := M) g 2 W) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    a1_h3_h2 (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    a1_h2_h1 (I := I) (M := M) hDim g
  let J : ℝ :=
    lowJetSq (I := I) (M := M) g 2 A.C0 +
      lowJetSq (I := I) (M := M) g 2 A.C1
  let B : ℝ := Real.sqrt J
  let C : ℝ := Ch + Cl
  let Q : ℝ := (C * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (jetNN (I := I) (M := M) g A.C0)
      (jetNN (I := I) (M := M) g A.C1)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hC : 0 ≤ C := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hcoeff :
      lowJetSq (I := I) (M := M) g 2 A.C0 +
          lowJetSq (I := I) (M := M) g 2 A.C1 ≤ B ^ 2 := by
    rw [hBsq]
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 3 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 3 W :=
      jetNN (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = lowJetSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤
        (Ch * B * D) ^ 2 :=
          hhigh A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hD) 2
      _ = Q * lowJetSq (I := I) (M := M) g 3 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
      jetNN (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤
        (Cl * B * D) ^ 2 :=
          hlow A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hD) 2
      _ = Q * lowJetSq (I := I) (M := M) g 2 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  exact ⟨Q, hQ, hHi, hLo⟩

/-- The adjacent-scale commuting square of one first-order low-base action,
for ANY action bundle: the `H3 → H2` and `H2 → H1` completions realize one
smooth-core formula. -/
theorem a1_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.a1Hi (I := I) (M := M)) =
      (A.a1Lo (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, hpair⟩ := a1_pair (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := a1_jetQ (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.2.2

/-- The `H3 → H2` completion of one first-order low-base action realizes the
smooth-core action on the dense smooth range, for ANY action bundle. -/
theorem a1Hi_app
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) :
    A.a1Hi (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.a1 (I := I) (M := M) W) := by
  obtain ⟨_, _, hpair⟩ := a1_pair (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := a1_jetQ (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.1 W

/-- The `H2 → H1` completion of one first-order low-base action realizes the
smooth-core action on the dense smooth range, for ANY action bundle. -/
theorem a1Lo_app
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) :
    A.a1Lo (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.a1 (I := I) (M := M) W) := by
  obtain ⟨_, _, hpair⟩ := a1_pair (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := a1_jetQ (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.2.1 W

/-- The smooth-core first-order action is additive in the coefficient data. -/
private theorem a1_add_core
    (g : SmoothRiemannianMetric I M) (A B F : LowBaseActionData g)
    (h0 : F.C0 = A.C0 + B.C0) (h1 : F.C1 = A.C1 + B.C1)
    (W : SmoothCcTensor g 0 2) :
    F.a1 (I := I) (M := M) W =
      A.a1 (I := I) (M := M) W + B.a1 (I := I) (M := M) W := by
  simp only [LowBaseActionData.a1, h0, h1, appCc_add_left]
  abel

/-- **The `H3 → H2` completion is additive in the coefficient data.**  A bundle
whose order-zero and order-one coefficients are the sums of those of two other
bundles has the sum of their completions.  This is what lets a summed affine
packet certify a refolded bundle. -/
theorem a1Hi_add
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A B F : LowBaseActionData g)
    (h0 : F.C0 = A.C0 + B.C0) (h1 : F.C1 = A.C1 + B.C1) :
    F.a1Hi (I := I) (M := M) =
      A.a1Hi (I := I) (M := M) + B.a1Hi (I := I) (M := M) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  refine hdense.induction_on x
    (isClosed_eq (F.a1Hi (I := I) (M := M)).continuous
      (A.a1Hi (I := I) (M := M) +
        B.a1Hi (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, ContinuousLinearMap.add_apply,
    a1Hi_app (I := I) (M := M) hDim g F W,
    a1Hi_app (I := I) (M := M) hDim g A W,
    a1Hi_app (I := I) (M := M) hDim g B W,
    a1_add_core (I := I) (M := M) g A B F h0 h1 W,
    ccTensorToHs_add]

/-- **The `H2 → H1` completion is additive in the coefficient data**, the
adjacent-scale partner of `a1Hi_add`. -/
theorem a1Lo_add
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A B F : LowBaseActionData g)
    (h0 : F.C0 = A.C0 + B.C0) (h1 : F.C1 = A.C1 + B.C1) :
    F.a1Lo (I := I) (M := M) =
      A.a1Lo (I := I) (M := M) + B.a1Lo (I := I) (M := M) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  refine hdense.induction_on x
    (isClosed_eq (F.a1Lo (I := I) (M := M)).continuous
      (A.a1Lo (I := I) (M := M) +
        B.a1Lo (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, ContinuousLinearMap.add_apply,
    a1Lo_app (I := I) (M := M) hDim g F W,
    a1Lo_app (I := I) (M := M) hDim g A W,
    a1Lo_app (I := I) (M := M) hDim g B W,
    a1_add_core (I := I) (M := M) g A B F h0 h1 W,
    ccTensorToHs_add]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
