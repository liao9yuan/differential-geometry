import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# Compatible low-base Ricci--DeTurck action pairs

This module completes the pair-reduced second-order action on the adjacent
Sobolev scales used by the low-regularity Ricci--DeTurck bootstrap.
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
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- In dimension three, the pair-reduced second-order action is small from
spectral `H4` to spectral `H2`, with a coefficient controlled only by the
spectral `H2` radius of the state. -/
theorem pairRedA2_h4_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ U : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (pairRedA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)‖ ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
  obtain ⟨ρe, Ce, hρe, hCe, hextra⟩ :=
    extraA2_h4_h2 (I := I) (M := M) hDim g
  obtain ⟨ρr, Cr, hρr, hCr, hrefold⟩ :=
    rhsRefold2Int_h4_h2 (I := I) (M := M) hDim g
  refine ⟨min ρe ρr, Ce + Cr, lt_min hρe hρr,
    add_nonneg hCe hCr, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT U
  have hRe : R ≤ ρe := hRρ.trans (min_le_left _ _)
  have hRr : R ≤ ρr := hRρ.trans (min_le_right _ _)
  have he := hextra T hδ_lt hδ hδZ hR hRe hT U
  have hr := hrefold T hδ_lt hδ hδZ hR hRr hT U
  have hsub (A B : SmoothCcTensor g 0 2) :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (A - B) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) A -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) B := by
    rw [sub_eq_add_neg, show -B = (-1 : ℝ) • B by simp,
      ccTensorToHs_add, ccTensorToHs_smul]
    rw [sub_eq_add_neg, neg_one_smul]
  rw [pairRedA2Act, hsub]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (extraA2Act (I := I) (M := M)
            g T U hδ_lt hδ hδZ)‖ +
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (appCc (I := I) (M := M) g 4 2
            (rhsRefold2Int (I := I) (M := M)
              g T hδ_lt hδ hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 U))‖ :=
      norm_sub_le _ _
    _ ≤ Ce * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ +
        Cr * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ :=
      add_le_add he hr
    _ = (Ce + Cr) * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by ring

/-- The same pair-reduced action is small from spectral `H3` to spectral
`H1`, with the same low-base state control. -/
theorem pairRedA2_h3_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ U : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (pairRedA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)‖ ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρe, Ce, hρe, hCe, hextra⟩ :=
    extraA2_h3_h1 (I := I) (M := M) hDim g
  obtain ⟨ρr, Cr, hρr, hCr, hrefold⟩ :=
    rhsRefold2Int_h3_h1 (I := I) (M := M) hDim g
  refine ⟨min ρe ρr, Ce + Cr, lt_min hρe hρr,
    add_nonneg hCe hCr, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT U
  have hRe : R ≤ ρe := hRρ.trans (min_le_left _ _)
  have hRr : R ≤ ρr := hRρ.trans (min_le_right _ _)
  have he := hextra T hδ_lt hδ hδZ hR hRe hT U
  have hr := hrefold T hδ_lt hδ hδZ hR hRr hT U
  have hsub (A B : SmoothCcTensor g 0 2) :
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) (A - B) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) A -
          ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) B := by
    rw [sub_eq_add_neg, show -B = (-1 : ℝ) • B by simp,
      ccTensorToHs_add, ccTensorToHs_smul]
    rw [sub_eq_add_neg, neg_one_smul]
  rw [pairRedA2Act, hsub]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (extraA2Act (I := I) (M := M)
            g T U hδ_lt hδ hδZ)‖ +
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (appCc (I := I) (M := M) g 4 2
            (rhsRefold2Int (I := I) (M := M)
              g T hδ_lt hδ hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 U))‖ :=
      norm_sub_le _ _
    _ ≤ Ce * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
        Cr * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ :=
      add_le_add he hr
    _ = (Ce + Cr) * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by ring

private noncomputable def pairRedA2Core
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (σ : ℝ) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 σ where
  toFun := fun U =>
    ccTensorToHs (I := I) (M := M) g 2 σ
      (pairRedA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ)
  map_add' := fun U V => by
    rw [pairRedA2_add (I := I) (M := M) g T U V hδ_lt hδ hδZ,
      ccTensorToHs_add]
  map_smul' := fun c U => by
    rw [pairRedA2_smul (I := I) (M := M) g T U c hδ_lt hδ hδZ,
      ccTensorToHs_smul]
    rfl

/-- The pair-reduced additional second-order action completed from spectral
`H4` to spectral `H2`. -/
noncomputable def pairRedA2Hi
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (2 : ℝ) :=
  (pairRedA2Core (I := I) (M := M) g T (2 : ℝ) hδ_lt hδ hδZ).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ))

/-- The pair-reduced additional second-order action completed from spectral
`H3` to spectral `H1`. -/
noncomputable def pairRedA2Lo
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (1 : ℝ) :=
  (pairRedA2Core (I := I) (M := M) g T (1 : ℝ) hδ_lt hδ hδZ).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

/-- The two completions of the pair-reduced action have one common small-ball
bound, agree with the same smooth action, and commute with Sobolev inclusion. -/
theorem exists_pairRedA2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ‖pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ C * R ∧
        ‖pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ C * R ∧
        (∀ U : SmoothCcTensor g 0 2,
          pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (pairRedA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)) ∧
        (∀ U : SmoothCcTensor g 0 2,
          pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (pairRedA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)) ∧
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
            (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ) =
          (pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
              (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρh, Ch, hρh, hCh, hhigh⟩ :=
    pairRedA2_h4_h2 (I := I) (M := M) hDim g
  obtain ⟨ρl, Cl, hρl, hCl, hlow⟩ :=
    pairRedA2_h3_h1 (I := I) (M := M) hDim g
  refine ⟨min ρh ρl, Ch + Cl, lt_min hρh hρl,
    add_nonneg hCh hCl, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT
  have hRh : R ≤ ρh := hRρ.trans (min_le_left _ _)
  have hRl : R ≤ ρl := hRρ.trans (min_le_right _ _)
  have hhigh' := hhigh T hδ_lt hδ hδZ hR hRh hT
  have hlow' := hlow T hδ_lt hδ hδZ hR hRl hT
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hHiNorm :
      ‖pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ Ch * R := by
    unfold pairRedA2Hi
    exact LinearMap.opNorm_extendOfNorm_le
      hdense4 (mul_nonneg hCh hR) hhigh'
  have hLoNorm :
      ‖pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ Cl * R := by
    unfold pairRedA2Lo
    exact LinearMap.opNorm_extendOfNorm_le
      hdense3 (mul_nonneg hCl hR) hlow'
  have hHiCore (U : SmoothCcTensor g 0 2) :
      pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (pairRedA2Act (I := I) (M := M)
            g T U hδ_lt hδ hδZ) := by
    change
      ((pairRedA2Core (I := I) (M := M)
        g T (2 : ℝ) hδ_lt hδ hδZ).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) U) =
        (pairRedA2Core (I := I) (M := M)
          g T (2 : ℝ) hδ_lt hδ hδZ) U
    apply LinearMap.extendOfNorm_eq hdense4
    exact ⟨Ch * R, hhigh'⟩
  have hLoCore (U : SmoothCcTensor g 0 2) :
      pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (pairRedA2Act (I := I) (M := M)
            g T U hδ_lt hδ hδZ) := by
    change
      ((pairRedA2Core (I := I) (M := M)
        g T (1 : ℝ) hδ_lt hδ hδZ).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) U) =
        (pairRedA2Core (I := I) (M := M)
          g T (1 : ℝ) hδ_lt hδ hδZ) U
    apply LinearMap.extendOfNorm_eq hdense3
    exact ⟨Cl * R, hlow'⟩
  have hHiNorm' :
      ‖pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤
        (Ch + Cl) * R :=
    hHiNorm.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCl) hR)
  have hLoNorm' :
      ‖pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤
        (Ch + Cl) * R :=
    hLoNorm.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCh) hR)
  refine ⟨hHiNorm', hLoNorm', hHiCore, hLoCore, ?_⟩
  let L :=
    (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
      (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (pairRedA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ)
  let L' :=
    (pairRedA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ).comp
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
        (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num))
  have hfun : (L : _ → _) = L' :=
    hdense4.equalizer L.continuous L'.continuous (by
      funext U
      simp only [Function.comp_apply, L, L', ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [hHiCore]
      have hin :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
              (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U := by
        apply DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
        funext i
        simp only [
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply,
          ccTensorToHs_coeff]
      rw [hin, hLoCore]
      apply DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
      funext i
      simp only [
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply,
        ccTensorToHs_coeff])
  apply ContinuousLinearMap.ext
  intro U
  exact congrFun hfun U

/-! ## Combined lower path action -/

/-- The complete lower path action after the Ricci and DeTurck coefficients
have been combined.  It contains only the zero-order path coefficient, the
one-order path coefficient, and the fixed curvature term. -/
def pathA1Act
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 2 2
      (rhsLow0PathIntegral (I := I) (M := M) g g T 0
        hδ_lt hδ hδ_lt hδZ)
      (iteratedCovGrad (I := I) g 0 2 0 U) +
    appCc (I := I) (M := M) g 3 2
      (rhsLow1PathIntegral (I := I) (M := M) g g T 0
        hδ_lt hδ hδ_lt hδZ)
      (iteratedCovGrad (I := I) g 0 2 1 U) +
    appCc (I := I) (M := M) g 2 2
      (phiMetCurvCoeff (I := I) g g g)
      (iteratedCovGrad (I := I) g 0 2 0 U)

/-- The combined lower path action is additive in its passenger. -/
theorem pathA1_add
    (g : SmoothRiemannianMetric I M)
    (T U V : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pathA1Act (I := I) (M := M) g T (U + V) hδ_lt hδ hδZ =
      pathA1Act (I := I) (M := M) g T U hδ_lt hδ hδZ +
        pathA1Act (I := I) (M := M) g T V hδ_lt hδ hδZ := by
  simp only [pathA1Act, iteratedCovGrad_add, appCc_add_right]
  abel

/-- The combined lower path action commutes with scalar multiplication in its
passenger. -/
theorem pathA1_smul
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (c : ℝ)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pathA1Act (I := I) (M := M) g T (c • U) hδ_lt hδ hδZ =
      c • pathA1Act (I := I) (M := M) g T U hδ_lt hδ hδZ := by
  simp only [pathA1Act, iteratedCovGrad_smul, appCc_smul_right]
  module

/-- The complete remainder is the principal-cometric action, the pair-reduced
top action, and the combined lower path action.  This identity is the algebraic
base from which the remaining order-zero high head must be extracted. -/
theorem remainder_path_split
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    realizedRHSArm (I := I) g g T hδ_lt hδ -
          realizedRHSArm (I := I) g g 0 hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2 T =
      deTurckPrincipalCometricArm (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ 1) T +
        pairRedA2Act (I := I) (M := M) g T T hδ_lt hδ hδZ +
        pathA1Act (I := I) (M := M) g T T hδ_lt hδ hδZ := by
  have hzero : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
    intro x v w
    have h0 : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := (zero_smul ℝ _).symm
    rw [h0]
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul, zero_mul]
  rw [rhsArm_sub_eq_paths (I := I) (M := M) g g T 0
    hTsymm hzero hδ_lt hδ hδ_lt hδZ]
  simp only [sub_zero]
  rw [show
      (appCc (I := I) (M := M) g 2 2
            (rhsLow0PathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 0 T) +
          appCc (I := I) (M := M) g 3 2
            (rhsLow1PathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          appCc (I := I) (M := M) g 4 2
            (rhsTopPathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
          rawTensorConnLapSmooth (I := I) g 0 2 T =
        appCc (I := I) (M := M) g 2 2
            (rhsLow0PathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 0 T) +
          appCc (I := I) (M := M) g 3 2
            (rhsLow1PathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          (appCc (I := I) (M := M) g 4 2
              (rhsTopPathIntegral (I := I) (M := M) g g T 0
                hδ_lt hδ hδ_lt hδZ)
              (iteratedCovGrad (I := I) g 0 2 2 T) -
            rawTensorConnLapSmooth (I := I) g 0 2 T) by abel]
  rw [top_path_split (I := I) (M := M) g g T 0
    hδ_lt hδ hδ_lt hδZ T]
  have htop :
      appCc (I := I) (M := M) g 4 2
          (rhsTopPathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ -
            deTurckPhiMetTotal (I := I) (M := M) g g g)
          (iteratedCovGrad (I := I) g 0 2 2 T) =
        deTurckPrincipalCometricArm (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ 1) T +
          pairRedA2Act (I := I) (M := M) g T T hδ_lt hδ hδZ := by
    rw [pairRedA2_eq (I := I) (M := M) g T T hδ_lt hδ hδZ]
    abel
  rw [htop]
  simp only [pathA1Act]
  abel

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
