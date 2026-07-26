import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound

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

**Status (honest partial).** The summed deliverable and its `symmS` fibre-small wiring are
proved here from the *per-order* radius-free engine `deTurckLieCoeffField_perOrder_l2_radiusFree`.
That engine is the single remaining frontier: it is the R-free sibling of the private
`wAlpha_L2_topsep` lifted through the `deTurckLieWEndoInsert` isometry and the `DLa + DLb` split,
and its proof is the mechanical (no-unreceivable-term) re-derivation of the private DeTurck-VF
tower with the two ball-uniform integrators swapped for `antidiagonalTupleGrid_integral_radiusFree`.
It carries ONE flagged `sorry`; the route is analysed in `DeTurckLieCoeffDiffRadiusFree.md`.
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

FRONTIER (one flagged `sorry`): the proof is the mechanical re-derivation of the private
DeTurck-vector-field tower — `deTurckLieCoeffField = DLa + DLb`, `‖∇ⁱDL·‖ = ‖∇ⁱ wAlpha‖` via the
`deTurckLieWEndoInsert` endo-insert isometry, `wAlpha` residual through R-free
`wOmega_lowOrder`/`connDiffSection_lowOrder` and R-free `wOmega_L2_topsep` — with the two
ball-uniform integrators (`diagonalProductGrid_rfns_integral_ballUniform_succ`,
`antidiagonalTupleGrid_integral_ballUniform_tameWindow`) each replaced by
`antidiagonalTupleGrid_integral_radiusFree` (same integrand, fixed `Λ₀`; the per-index top jets
sum into the top/low envelope).  No unreceivable term arises.  See the `.md` note. -/
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
  sorry

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
