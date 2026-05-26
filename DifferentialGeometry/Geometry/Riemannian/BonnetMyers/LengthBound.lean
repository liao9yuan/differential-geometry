import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Riemannian.Variation.SecondVariation
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.Bochner
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false

/-!
# Bonnet-Myers length bound

This file packages the analytic core of the Bonnet-Myers diameter
theorem: a unit-speed minimising geodesic on a complete Riemannian
manifold whose Ricci curvature is bounded below by `(n-1) K` (with
`K > 0`) has length at most `π / √K`.

The proof routes through the second-variation index form applied to
the family `V_i(t) := sin(πt/L) · e_i(t)`, where `e_i` is a parallel
orthonormal frame of `(γ')⊥` along `γ`.
-/

noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

/-! ## Trace identity: sum of sectional curvatures equals Ricci -/

/-- **trace-identity-sum-sec-curv-equals-ricci.** For a unit vector
`X ∈ T_x M` and any orthonormal family `e : Fin (Module.finrank ℝ E - 1)
→ T_x M` orthogonal to `X`,
`∑_i ⟨R(e_i, X) X, e_i⟩_g = Ric(X, X)`.

The proof realises the Ricci tensor as the trace of `Z ↦ R(Z, X) X`
in the orthonormal basis `{X, e_1, …, e_{n-1}}`; the `X`-summand
`⟨R(X, X) X, X⟩` vanishes by curvature antisymmetry. -/
theorem trace_identity_sum_sec_curv_equals_ricci
    (g : SmoothRiemannianMetric I M) (x : M) (X : E)
    (hUnit : g.inner x X X = 1)
    (e : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (hPerp : ∀ i, g.inner x (e i) X = 0) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i))
      = ricciTensor (I := I) g x X X := by
  classical
  -- Set up: write n = (n - 1) + 1, using NeZero (Module.finrank ℝ E).
  have hn_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn_eq : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E :=
    Nat.succ_pred_eq_of_pos hn_pos
  -- Build an n-element basis B : Fin n → T_x M from {X, e_0, ..., e_{n-2}}.
  -- Construct B' : Fin (n - 1 + 1) → E via Fin.cases, then transport to Fin n via hn_eq.
  let B' : Fin (Module.finrank ℝ E - 1 + 1) → E := Fin.cases X e
  let B : Fin (Module.finrank ℝ E) → E := fun i => B' (Fin.cast hn_eq.symm i)
  -- B 0 = X.
  have hB_zero : B (⟨0, hn_pos⟩ : Fin (Module.finrank ℝ E)) = X := by
    change B' (Fin.cast hn_eq.symm ⟨0, hn_pos⟩) = X
    have hcast_eq : Fin.cast hn_eq.symm (⟨0, hn_pos⟩ : Fin (Module.finrank ℝ E)) =
        (0 : Fin (Module.finrank ℝ E - 1 + 1)) := by
      apply Fin.ext
      rfl
    rw [hcast_eq]
    rfl
  -- σ i : Fin n with val = i.val + 1, for i : Fin (n - 1).
  have hσ_lt : ∀ i : Fin (Module.finrank ℝ E - 1), i.val + 1 < Module.finrank ℝ E := by
    intro i
    have hi : i.val < Module.finrank ℝ E - 1 := i.isLt
    omega
  let σ : Fin (Module.finrank ℝ E - 1) → Fin (Module.finrank ℝ E) :=
    fun i => ⟨i.val + 1, hσ_lt i⟩
  -- B (σ i) = e i.
  have hB_succ : ∀ i : Fin (Module.finrank ℝ E - 1), B (σ i) = e i := by
    intro i
    change B' (Fin.cast hn_eq.symm (σ i)) = e i
    have hsucc_eq : Fin.cast hn_eq.symm (σ i) = Fin.succ i := by
      apply Fin.ext
      rfl
    rw [hsucc_eq]
    rfl
  -- B is g-orthonormal.
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    by_cases hi : i.val = 0
    · have hi_eq : i = ⟨0, hn_pos⟩ := Fin.ext hi
      by_cases hj : j.val = 0
      · have hj_eq : j = ⟨0, hn_pos⟩ := Fin.ext hj
        rw [hi_eq, hj_eq, hB_zero, hUnit]
        rw [if_pos rfl]
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        let k : Fin (Module.finrank ℝ E - 1) :=
          ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j = σ k := by
          apply Fin.ext
          change j.val = (j.val - 1) + 1
          omega
        rw [hi_eq, hj_eq, hB_zero, hB_succ]
        have h_inner : g.inner x X (e k) = 0 := by
          rw [g.symm x X (e k)]
          exact hPerp k
        rw [h_inner]
        rw [if_neg]
        intro h
        have hval := congrArg Fin.val h
        change 0 = k.val + 1 at hval
        omega
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      let k : Fin (Module.finrank ℝ E - 1) :=
        ⟨i.val - 1, by have := i.isLt; omega⟩
      have hi_eq : i = σ k := by
        apply Fin.ext
        change i.val = (i.val - 1) + 1
        omega
      by_cases hj : j.val = 0
      · have hj_eq : j = ⟨0, hn_pos⟩ := Fin.ext hj
        rw [hi_eq, hj_eq, hB_succ, hB_zero]
        have h_inner : g.inner x (e k) X = 0 := hPerp k
        rw [h_inner]
        rw [if_neg]
        intro h
        have hval := congrArg Fin.val h
        change k.val + 1 = 0 at hval
        omega
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        let l : Fin (Module.finrank ℝ E - 1) :=
          ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j = σ l := by
          apply Fin.ext
          change j.val = (j.val - 1) + 1
          omega
        rw [hi_eq, hj_eq, hB_succ, hB_succ]
        have h_inner : g.inner x (e k) (e l) = if k = l then (1 : ℝ) else 0 := hON k l
        rw [h_inner]
        by_cases hkl : k = l
        · rw [hkl]
          simp
        · rw [if_neg hkl, if_neg]
          intro hσ_eq
          apply hkl
          apply Fin.ext
          have hval := congrArg Fin.val hσ_eq
          change k.val + 1 = l.val + 1 at hval
          omega
  -- Apply the orthonormal trace formula for Ricci.
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x X X B hB_orth]
  -- Split sum: Fin n ≃ Fin (n - 1 + 1) via finCongr hn_eq.
  have hsum_split :
      ∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x X X X) X +
          ∑ i : Fin (Module.finrank ℝ E - 1),
            g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i) := by
    have heq_sum :
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i) =
        ∑ j : Fin (Module.finrank ℝ E - 1 + 1),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B (finCongr hn_eq j)) X X)
            (B (finCongr hn_eq j)) :=
      (Equiv.sum_comp (finCongr hn_eq)
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i))).symm
    rw [heq_sum]
    rw [Fin.sum_univ_succ]
    have h0 : (finCongr hn_eq (0 : Fin (Module.finrank ℝ E - 1 + 1)) :
              Fin (Module.finrank ℝ E)) = ⟨0, hn_pos⟩ := by
      apply Fin.ext
      rfl
    rw [h0, hB_zero]
    refine congrArg (fun s : ℝ =>
        g.inner x (riemannOp (LeviCivita (I := I) g) x X X X) X + s)
      (Finset.sum_congr rfl ?_)
    intro i _
    have heq : finCongr hn_eq i.succ = σ i := by
      apply Fin.ext
      rfl
    rw [heq, hB_succ]
  rw [hsum_split]
  -- R(X, X) X = 0 by antisymmetry of R in the first two slots.
  have hR_self : riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
    have h := riemannOp_swap (LeviCivita (I := I) g) x X X X
    have hsum : riemannOp (LeviCivita (I := I) g) x X X X +
        riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
      rw [eq_neg_iff_add_eq_zero] at h
      exact h
    have h_two : (2 : ℝ) • riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
      rw [two_smul]; exact hsum
    rcases smul_eq_zero.mp h_two with h2_zero | hv_zero
    · exact absurd h2_zero (by norm_num)
    · exact hv_zero
  rw [hR_self]
  -- g.inner x 0 X = 0, so first term vanishes.
  simp only [map_zero, ContinuousLinearMap.zero_apply, zero_add]

/-! ## Sum-index-form frame evaluation -/

/-- **sum-index-form-frame-evaluation.** For a unit-speed geodesic
`γ : [0, L] → M`, a parallel orthonormal frame `e : Fin
(Module.finrank ℝ E - 1) → SectionAlongCurve I M γ` of `(γ')⊥`, and
the variation fields `V_i(t) := sin(πt/L) · e_i(t)`,
`∑_i indexForm g γ 0 L V_i V_i =
  ∫₀^L [(n-1)(π/L)² cos²(πt/L) - sin²(πt/L) · Ric(γ', γ')] dt`.

The proof uses parallelism of `e_i` to compute `∇_t V_i =
(π/L) cos(πt/L) · e_i`, hence `‖∇_t V_i‖² = (π/L)² cos²(πt/L)`. Summing
over `i` and applying `trace_identity_sum_sec_curv_equals_ricci`
pointwise on each `γ(t)` yields the displayed integrand. -/
theorem sum_index_form_frame_evaluation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L)
    (uPrime : ℝ → E)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      = ∫ t in (0 : ℝ)..L,
          ((Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)) := sorry

/-! ## Sum-index-form bound from the Ricci hypothesis -/

/-- **sum-index-form-bound-by-curvature-hypothesis.** Given the lower
Ricci bound `(n-1) K · g(v, v) ≤ Ric(v, v)` (i.e.
`RicciBoundedBelow g ((n-1) K)`), the sum of index forms on the family
`V_i(t) := sin(πt/L) · e_i(t)` is bounded above by
`(n-1)(L/2)((π/L)² - K)`.

The proof applies monotonicity of the interval integral to
`sum_index_form_frame_evaluation`, plugs in the Ricci hypothesis on
the unit speed `γ'`, and evaluates the trigonometric integrals via
`integral_sin_sq` and `integral_cos_sq`. -/
theorem sum_index_form_bound_by_curvature_hypothesis
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L) {K : ℝ}
    (_hRic : RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K))
    (uPrime : ℝ → E)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      ≤ (Module.finrank ℝ E - 1 : ℝ) * (L / 2) * ((Real.pi / L) ^ 2 - K) := sorry

/-! ## Length-bound contradiction assembly -/

/-- **length-bound-contradiction-assembly.** *Bonnet-Myers length
bound.* For a unit-speed minimising geodesic `γ : [0, L] → M` on a
Riemannian manifold whose Ricci curvature satisfies
`(n-1) K · g(v, v) ≤ Ric(v, v)` with `K > 0`, the length `L` is at
most `π / √K`.

The proof is by contradiction. If `π/√K < L`, then `(π/L)² < K`, so
`sum_index_form_bound_by_curvature_hypothesis` produces a strictly
negative sum of index forms. On the other hand
`minimiser_implies_second_variation_nonneg` applied to each `V_i`
gives `0 ≤ indexForm g γ 0 L V_i V_i`, hence the sum is non-negative.
This contradiction forces `L ≤ π / √K`. -/
theorem length_bound_contradiction_assembly
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L) {K : ℝ}
    (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K))
    (uPrime : ℝ → E)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (_hmin : ∀ η : ℝ → M, η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L) :
    L ≤ Real.pi / Real.sqrt K := sorry

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
