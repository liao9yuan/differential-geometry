import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFJetRadiusFree
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence

/-!
# Radius-free jet-L² bound for the DeTurck-Lie coefficient field

Consumer sibling of THE GATE
(`boundedFactorGridWindow_integral_radiusFree_topSeparated`) and its per-order workhorse
(`antidiagonalTupleGrid_integral_radiusFree`), the **third brick** of the Pro-ruled repair of
UNIF item-2.  See `ShortTime/THREEARM_RECON.md` §11/§11c and the per-file note
`DeTurckLieCoeffDiffRadiusFree.md`.  The arm0 exemplar is
`Analysis/Spectral/Tensor/CovGrad/CurvatureCoeffDiffRadiusFree.lean`
(`ricciArmOrder0BaseCoeff_summed_l2_radiusFree`).

The R-dependent original is
`deTurckLieCoeffField_realizedFam_jetL2_summed_topSeparated`
(`DeTurckLieCoeffL2JetBound.lean:799`), whose combined `Kc` routes — through the private
DeTurck-vector-field tower (`wAlpha`/`wOmega`/`wXi`/`wCA`) — into the two ball-uniform
integrators `diagonalProductGrid_rfns_integral_ballUniform_succ` (VF file) and
`antidiagonalTupleGrid_integral_ballUniform_tameWindow` (monolith).  Both integrators have the
**exact same integrand** as the radius-free workhorse `antidiagonalTupleGrid_integral_radiusFree`
(monolith :14455); the radius enters *only* in their constants (`Λ = C_emb·R` before the
`R^{7k}` grid).  Replacing them with the fixed-`Λ₀` workhorse makes the whole coefficient bound
radius-free:
```
∑_{i ≤ a} ‖∇ⁱ(deTurckLieCoeffField g₀ g₁ g_bg)‖²
   ≤ Ktop · ∑_{j ≤ a+2} ‖∇ʲ(symmS g₀ T)‖²
   + Klow · (1 + ∑_{j ≤ a+1} ‖∇ʲ(symmS g₀ T)‖²)
```
with `Ktop`, `Klow` depending only on `g₀`, `g_bg`, `a`, `dim E`, `δ₀` — no ball radius `R`, no
`H^{a+2}` ball hypothesis; the only smallness input is the fibre operator-norm bound
`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ` with `δ ≤ δ₀`.

**Status (COMPLETE — 2026-07-26, session 5).** Both public theorems are proved and axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).  The summed deliverable and its `symmS`
fibre-small wiring reduce to the *per-order* radius-free engine
`deTurckLieCoeffField_perOrder_l2_radiusFree`, which is discharged via the `DLa + DLb` split: the DLb
arm through `deTurckLieWEndoInsert`/`wAlpha_L2_topsep_rf`, the DLa arm by integrating the R-free
pointwise `rfns_iCG_dLaField_topsep` through `antidiagonalTupleGrid_integral_radiusFree` (in place of
the two ball-uniform integrators).  The full route is analysed in `DeTurckLieCoeffDiffRadiusFree.md`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorBilinSymm_apply
    ccTensorBilinSymm_symm)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Per-order DLa / DLb radius-free engines feeding the frontier. -/

set_option linter.unusedVariables false in
/-- Radius-free per-order jet-L² bound for the `deTurckLieDLaCoeffField` arm.  Integrates the public
R-free pointwise top-separated engine `rfns_iCG_dLaField_topsep` (top `(appCcGdiag i)²·rfns(∇^{i+2}P)`,
`dLaGridWin (i+3)` remainder) through the radius-free workhorse
`antidiagonalTupleGrid_integral_radiusFree`, in place of the ball-uniform tame-window integrator. -/
private lemma dLaField_perOrder_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℕ → ℝ, (∀ i, 0 ≤ Ktop i) ∧ ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Ktop_a, hKtop_a_nn, Kc_a, hKc_a_nn, hfield⟩ :=
    rfns_iCG_dLaField_topsep (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i,
    fun i => mul_nonneg (mul_nonneg hKtop_a_nn (appCcGdiag_nonneg (E := E) i))
      (appCcGdiag_nonneg (E := E) i),
    fun i => Kc_a i * ∑ k ∈ Finset.range (i + 3), K_rf k,
    fun i => mul_nonneg (hKc_a_nn i) (Finset.sum_nonneg fun k _ => hK_rf_nn k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set S' : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)).toSection x) ≤
        (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) +
          Kc_a i * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3) :=
    fun x => hfield g₁ P htie hδ_le hδ0 hδ i x
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    intro k
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
        = (fun x => ∑ nn ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple nn k,
            ∏ m : Fin nn, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x; rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]; exact hK_rf P hsup k
  have hwin_int : MeasureTheory.Integrable
      (fun x => dLaGridWin
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [dLaGridWin]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
  have htop_int : MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg))
    (fun x => (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
      + Kc_a i * dLaGridWin
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3))
    ((htop_int.const_mul (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i)).add
      (hwin_int.const_mul (Kc_a i))) hpt
  rw [MeasureTheory.integral_add
      (htop_int.const_mul (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i))
      (hwin_int.const_mul (Kc_a i)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  have hnormsq : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hwin_bd : (∫ x, dLaGridWin
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by
    simp only [dLaGridWin]
    rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1), Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hAG k).2 ?_
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega))
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2
      ≤ (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i) *
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        + Kc_a i * (∫ x, dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ = (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
        + Kc_a i * (∫ x, dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := by rw [hnormsq]
    _ ≤ (Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
        + Kc_a i * ((∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S')) := by
        have hmul := mul_le_mul_of_nonneg_left hwin_bd (hKc_a_nn i)
        linarith [hmul]
    _ = Ktop_a * appCcGdiag (E := E) i * appCcGdiag (E := E) i *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
        + (Kc_a i * ∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by ring

set_option linter.unusedVariables false in
/-- Radius-free per-order jet-L² bound for the `deTurckLieDLbCoeffField` arm.  `‖∇ⁱDLb‖² ≤
4·finrank·‖∇ⁱwEndoInsert‖²` (`normSq_iCG_dlbField_le`); the insert jet equals the `wAlpha` jet
(`norm_iCG_wEndoInsert_eq_wAlpha`), top-separated by the radius-free `wAlpha_L2_topsep_rf`. -/
private lemma dLbField_perOrder_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kb_top, hKb_top_nn, Kb_flow, hKb_flow_nn, hwalpha⟩ :=
    wAlpha_L2_topsep_rf (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  have h4fr_nn : (0 : ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨4 * (Module.finrank ℝ E : ℝ) * Kb_top, mul_nonneg h4fr_nn hKb_top_nn,
    fun i => 4 * (Module.finrank ℝ E : ℝ) * Kb_flow i,
    fun i => mul_nonneg h4fr_nn (hKb_flow_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  have hdlb := normSq_iCG_dlbField_le (I := I) (M := M) g₀ g₁ g_bg i
  rw [norm_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀ g₁ g_bg i] at hdlb
  have hwa := hwalpha g₁ P htie hδ_le hδ0 hδ hsup i hi
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2
      ≤ 4 * (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := hdlb
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (Kb_top * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Kb_flow i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hwa h4fr_nn
    _ = 4 * (Module.finrank ℝ E : ℝ) * Kb_top *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          4 * (Module.finrank ℝ E : ℝ) * Kb_flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

/-! ### Radius-free per-order engine (the frontier). -/

set_option linter.unusedVariables false in
/-- **Radius-free per-order jet-L² bound for the DeTurck-Lie coefficient field**
`deTurckLieCoeffField g₀ g₁ g_bg`.  With a fixed zeroth-order fibre bound `Λ₀` (from fibre
smallness, not a Sobolev ball radius), the order-`i` jet-L² norm splits into a top leak
`Atop i · ‖∇^{i+2}(symmS g₀ T)‖²` and a low part
`Alow i · (1 + ∑_{j ≤ i+1} ‖∇ʲ(symmS g₀ T)‖²)`, with `Atop`, `Alow` depending only on `g₀`,
`g_bg`, `a`, `dim E`, `Λ₀`.  Sibling of `deTurckLieCoeffField_realizedFam_jetL2_perOrder_topSeparated`
with the radius-free workhorse `antidiagonalTupleGrid_integral_radiusFree` in place of the two
ball-uniform integrators.

PROVED (session 5): `deTurckLieCoeffField = DLa + DLb` (`‖∇ⁱfield‖² ≤ 2‖∇ⁱDLa‖² + 2‖∇ⁱDLb‖²`).
`DLb` = `4·finrank·‖∇ⁱwEndoInsert‖²` = `4·finrank·‖∇ⁱwAlpha‖²` (the `deTurckLieWEndoInsert` isometry
`norm_iCG_wEndoInsert_eq_wAlpha`), top-separated by the R-free `wAlpha_L2_topsep_rf` (`dLbField_perOrder_rf`).
`DLa` integrates the R-free pointwise `rfns_iCG_dLaField_topsep` through
`antidiagonalTupleGrid_integral_radiusFree` in place of the ball-uniform tame-window integrator
(`dLaField_perOrder_rf`).  Perturbation `P := symmS g₀ T`; one `Finset.sum_range_succ` peels the top
cell out of the `i+3` window into `Atop`.  See the `.md` note. -/
theorem deTurckLieCoeffField_perOrder_l2_radiusFree
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Atop : ℕ → ℝ, (∀ i, 0 ≤ Atop i) ∧ ∃ Alow : ℕ → ℝ, (∀ i, 0 ≤ Alow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((symmS (I := I) (M := M) g₀ T).toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ) (hi : i ≤ a),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Ka_top, hKa_top_nn, Ka_low, hKa_low_nn, hDLa⟩ :=
    dLaField_perOrder_rf (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  obtain ⟨Kb_top, hKb_top_nn, Kb_low, hKb_low_nn, hDLb⟩ :=
    dLbField_perOrder_rf (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  refine ⟨fun i => 2 * Ka_top i + 2 * Kb_top + (2 * Ka_low i + 2 * Kb_low i),
    fun i => by
      have := hKa_top_nn i; have := hKb_top_nn; have := hKa_low_nn i; have := hKb_low_nn i
      linarith,
    fun i => 2 * Ka_low i + 2 * Kb_low i,
    fun i => by have := hKa_low_nn i; have := hKb_low_nn i; linarith, ?_⟩
  intro g₁ T δ hδ_le hδ0 hδ htie hsup i hi
  set P : SmoothCcTensor g₀ 0 2 := symmS (I := I) (M := M) g₀ T with hP_def
  have htie' : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    rw [hP_def,
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ccTensorBilinSymm_symmS_apply
        (I := I) (M := M) g₀ T y v w]
    exact htie y v w
  have hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    rw [hP_def]
    exact DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.gFibreOpBound_symmS
      (I := I) (M := M) g₀ T hδ
  have ha := hDLa g₁ P htie' hδ_le hδ0 hδ' hsup i
  have hb := hDLb g₁ P htie' hδ_le hδ0 hδ' hsup i hi
  -- combined triangle `‖∇ⁱ field‖² ≤ 2‖∇ⁱ DLa‖² + 2‖∇ⁱ DLb‖²`.
  have hcomb : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 := by
    have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)
        = iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)
          + iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg) := by
      rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg,
        iteratedCovGrad_add]
    rw [hgrad]
    nlinarith [norm_add_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg))
        (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)
          + iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ -
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖)]
  -- range split: peel `‖∇^{i+2}P‖²` (index `i+2`) out of the `i+3` low window into the top.
  have hsplit : (∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) =
      (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
    rw [show i + 3 = (i + 2) + 1 from rfl, Finset.sum_range_succ]
  rw [hsplit] at ha hb
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 :=
        hcomb
    _ ≤ 2 * (Ka_top i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Ka_low i * (1 +
              ((∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2))) +
          2 * (Kb_top * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Kb_low i * (1 +
              ((∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2))) := by
        have h1 := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)
        have h2 := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
        linarith [h1, h2]
    _ = (2 * Ka_top i + 2 * Kb_top + (2 * Ka_low i + 2 * Kb_low i)) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
        (2 * Ka_low i + 2 * Kb_low i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

/-! ### Radius-free summed sibling (the consumer-gate deliverable). -/

set_option linter.unusedVariables false in
/-- **Radius-free summed jet-L² bound for the DeTurck-Lie coefficient field.**
Summing the per-order radius-free engine over `i ≤ a` gives a single bound whose top data weight
is at order `a+2` and low data weight at order `a+1`, with constants `Ktop`, `Klow` depending only
on `g₀`, `g_bg`, `a`, `dim E`, `δ₀` — no ball radius `R`, no `H^{a+2}` ball hypothesis.  This is
the DeTurck-Lie consumer sibling of THE GATE, the third brick of the Pro-ruled repair of UNIF
item-2; the perturbation grids run over `symmS g₀ T`.  Sibling of
`deTurckLieCoeffField_realizedFam_jetL2_summed_topSeparated` (`:799`). -/
theorem deTurckLieCoeffField_summed_l2_radiusFree
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Klow : ℝ, 0 ≤ Klow ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w),
        ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop * (∑ j ∈ Finset.range (a + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) +
          Klow * (1 + ∑ j ∈ Finset.range (a + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Atop, hAtop_nn, Alow, hAlow_nn, hper⟩ :=
    deTurckLieCoeffField_perOrder_l2_radiusFree (I := I) (M := M) g₀ g_bg a ha_super hδ₀
      (Λ₀ := max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) (le_max_left _ _)
  refine ⟨∑ i ∈ Finset.range (a + 1), Atop i,
    Finset.sum_nonneg (fun i _ => hAtop_nn i), ?_⟩
  refine ⟨∑ i ∈ Finset.range (a + 1), Alow i,
    Finset.sum_nonneg (fun i _ => hAlow_nn i), ?_⟩
  intro g₁ T δ hδ_le hδ htie
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    -- 0 ≤ δ from the fibre bound at a nonzero tangent vector.
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hδ₀0 : 0 ≤ δ₀ := le_trans hδ0 hδ_le
    have hmaxeq : max 0 ((Module.finrank ℝ E : ℝ) * δ₀) = (Module.finrank ℝ E : ℝ) * δ₀ :=
      max_eq_right (mul_nonneg (Nat.cast_nonneg _) hδ₀0)
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
        (max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) ^ 2 := by
      intro x
      rw [hmaxeq]
      exact rfns_symmS_zero_le_fibreSmall (I := I) (M := M) g₀ hδ₀0 T hδ_le hδ0 hδ x
    have hper' : ∀ i, i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) :=
      fun i hi => hper g₁ T hδ_le hδ0 hδ htie hsup i hi
    -- sum over i ≤ a.
    set w : ℕ → ℝ := fun j =>
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 with hw
    have hw_nn : ∀ j, 0 ≤ w j := fun j => sq_nonneg _
    calc ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1),
            (Atop i * w (i + 2) + Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hper' i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = (∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)) +
            ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) +
            (∑ i ∈ Finset.range (a + 1), Alow i) * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
          refine add_le_add ?_ ?_
          · -- top weight lands at range (a+3)
            calc ∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)
                ≤ ∑ i ∈ Finset.range (a + 1), Atop i * (∑ j ∈ Finset.range (a + 3), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAtop_nn i)
                  exact Finset.single_le_sum (f := fun j => w j) (fun j _ => hw_nn j)
                    (Finset.mem_range.mpr (by omega))
              _ = (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) := by
                  rw [Finset.sum_mul]
          · -- low weight lands at range (a+2)
            calc ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)
                ≤ ∑ i ∈ Finset.range (a + 1),
                    Alow i * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAlow_nn i)
                  have hsub : Finset.range (i + 2) ⊆ Finset.range (a + 2) := by
                    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
                  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw_nn j)
                  linarith
              _ = (∑ i ∈ Finset.range (a + 1), Alow i) *
                    (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  rw [Finset.sum_mul]
  · -- empty M: every L² norm is 0.
    haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hL0 : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]; ring
    rw [hL0]
    have h1 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Atop i) *
        (∑ j ∈ Finset.range (a + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) :=
      mul_nonneg (Finset.sum_nonneg (fun i _ => hAtop_nn i))
        (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h2 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Alow i) *
        (1 + ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
      refine mul_nonneg (Finset.sum_nonneg (fun i _ => hAlow_nn i)) ?_
      have : 0 ≤ ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    linarith

end Connection
end Integral
end DifferentialGeometry
