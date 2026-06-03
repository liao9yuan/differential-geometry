import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Matching the joint iterated derivative of two families with a common one-sided jet

For the parametrized half-line smooth-extension glue (`borel_halfLine_extend_param`) one must
know that two functions on the closed slab `Set.Ici 0 ×ˢ V` which are both `C∞` there and which
share their entire one-sided `t`-jet at every seam parameter `z ∈ V` have the *same* joint
iterated Fréchet derivative at every seam point `(0, z)`.

The natural reduction sets `D := Φ - ψ`. By linearity of `iteratedDerivWithin` over subtraction
the hypothesis becomes that *all* one-sided `t`-jets of `D` vanish on `V`:
`∀ i, ∀ w ∈ V, iteratedDerivWithin i (D · w) (Set.Ici 0) 0 = 0`, and the goal becomes
`iteratedFDerivWithin n D (Set.Ici 0 ×ˢ V) (0, z) = 0`. This `t`-jet–vanishing reduction is what
this file establishes (`iteratedFDerivWithin_prod_match` is then immediate from
`iteratedFDerivWithin_prod_match_zero_of_jet_vanish` by `iteratedFDerivWithin_sub_apply`).

## The deep step

The vanishing `iteratedFDerivWithin_prod_match_zero_of_jet_vanish` is the bivariate-Taylor /
mixed-partial heart of the half-line glue. Expanding the multilinear map
`iteratedFDerivWithin n D (Ici 0 ×ˢ V) (0, w)` on a tuple of product vectors splits it (by
multilinearity) into the `2ⁿ` pure mixed terms grouping some slots in the `t`-direction `(1,0)`
and the rest in the `z`-direction `(0,v)`. Each pure term, after the `t`-slots are gathered (which
needs `Cⁿ` permutation symmetry of `iteratedFDerivWithin`), is a `z`-derivative of a `t`-jet of
`D`. Since every `t`-jet of `D` is, as a function of the seam parameter, identically `0` on `V`,
each such `z`-derivative vanishes.

`Cⁿ` permutation symmetry of `iteratedFDerivWithin` within a half-space at order `> 2` is **not**
available in Mathlib: it provides only the second-order symmetry
`ContDiffWithinAt.isSymmSndFDerivWithinAt` (valid at `C²`, hence at `C∞`) and the full
permutation symmetry `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` only under analyticity
(`ContDiffWithinAt 𝕜 ω`, strictly stronger than `C∞`). The `C∞` `n`-th order bootstrap from the
second-order Clairaut symmetry is a self-contained deep result that Mathlib deliberately routes
through analyticity instead; it is the single isolated `sorry` here, transitively inherited by
`borel_halfLine_extend_param`. Everything else in the file is sorry-free.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

section ProdMatch

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Vanishing form of the seam jet match.** If `D` is `C∞` on the closed slab `Ici 0 ×ˢ V`
(`V` open) and *every* one-sided `t`-jet of `D` vanishes at every seam parameter `w ∈ V`, then
the joint iterated Fréchet derivative of `D` vanishes at every seam point `(0, w)`.

This is the bivariate-Taylor heart of the parametrized half-line glue: the `n`-th joint derivative
at `(0, w)`, expanded over product directions, is a sum of `z`-derivatives of `t`-jets of `D`, each
of which is the `z`-derivative of the identically-zero seam function `w ↦ ∂ₜ^i D(0, w)`. Gathering
the `t`-slots needs the `C∞` `n`-th order permutation symmetry of `iteratedFDerivWithin`, which is
absent from Mathlib (only second-order Clairaut and the analytic-case full symmetry exist); that
gathering is the file's sole deferred input. -/
theorem iteratedFDerivWithin_prod_match_zero_of_jet_vanish
    {D : ℝ × E → F} {V : Set E} (hV : IsOpen V)
    (hD : ContDiffOn ℝ ∞ D (Set.Ici (0:ℝ) ×ˢ V))
    (hjet : ∀ i : ℕ, ∀ w ∈ V,
      iteratedDerivWithin i (fun t => D (t, w)) (Set.Ici 0) 0 = 0)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n D (Set.Ici (0:ℝ) ×ˢ V) (0, z) = 0 := by
  sorry

/-- **Matching joint iterated derivatives from a common one-sided jet.** Two families `Φ, ψ` that
are both `C∞` on the closed slab `Ici 0 ×ˢ V` (`V` open) and share their entire one-sided `t`-jet
`i ↦ iteratedDerivWithin i (·, w)|_{Ici 0} 0` at every seam parameter `w ∈ V` have the same joint
iterated Fréchet derivative at every seam point `(0, z)`.

Reduces, via linearity of `iteratedFDerivWithin`/`iteratedDerivWithin` over subtraction, to the
vanishing statement `iteratedFDerivWithin_prod_match_zero_of_jet_vanish` for the difference
`D = Φ - ψ`. -/
theorem iteratedFDerivWithin_prod_match
    {Φ ψ : ℝ × E → F} {V : Set E} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ici (0:ℝ) ×ˢ V)) (hψ : ContDiffOn ℝ ∞ ψ (Set.Ici (0:ℝ) ×ˢ V))
    (htjet : ∀ i : ℕ, Set.EqOn (fun w => iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0)
                               (fun w => iteratedDerivWithin i (fun t => ψ (t, w)) (Set.Ici 0) 0) V)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n Φ (Set.Ici (0:ℝ) ×ˢ V) (0, z)
      = iteratedFDerivWithin ℝ n ψ (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by
  -- Work with the difference `D = Φ - ψ`; the goal becomes `iteratedFDerivWithin n D · = 0`.
  set S : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hS_def
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
  have hmem : ((0:ℝ), z) ∈ S := ⟨Set.self_mem_Ici, hz⟩
  have hΦn : ContDiffWithinAt ℝ n Φ S (0, z) :=
    (hΦ (0, z) hmem).of_le (by exact_mod_cast le_top)
  have hψn : ContDiffWithinAt ℝ n ψ S (0, z) :=
    (hψ (0, z) hmem).of_le (by exact_mod_cast le_top)
  -- `iteratedFDerivWithin n (Φ - ψ) = iteratedFDerivWithin n Φ - iteratedFDerivWithin n ψ`.
  have hsub : iteratedFDerivWithin ℝ n (Φ - ψ) S (0, z)
      = iteratedFDerivWithin ℝ n Φ S (0, z) - iteratedFDerivWithin ℝ n ψ S (0, z) :=
    iteratedFDerivWithin_sub_apply hΦn hψn hUD hmem
  -- The difference is `C∞` on `S`.
  have hD : ContDiffOn ℝ ∞ (Φ - ψ) S := hΦ.sub hψ
  -- All one-sided `t`-jets of the difference vanish on `V`, by linearity of `iteratedDerivWithin`.
  have hjet : ∀ i : ℕ, ∀ w ∈ V,
      iteratedDerivWithin i (fun t => (Φ - ψ) (t, w)) (Set.Ici 0) 0 = 0 := by
    intro i w hw
    have hΦw : ContDiffWithinAt ℝ i (fun t => Φ (t, w)) (Set.Ici 0) 0 := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => Φ (t, w)) (Set.Ici 0) 0 := by
        have hmaps : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Ici 0) S :=
          fun t ht => ⟨ht, hw⟩
        have hpair : ContDiffWithinAt ℝ ∞ (fun t : ℝ => (t, w)) (Set.Ici 0) 0 :=
          (contDiff_id.prodMk contDiff_const).contDiffWithinAt
        exact (hΦ (0, w) ⟨Set.self_mem_Ici, hw⟩).comp 0 hpair hmaps
      exact hcomp.of_le (by exact_mod_cast le_top)
    have hψw : ContDiffWithinAt ℝ i (fun t => ψ (t, w)) (Set.Ici 0) 0 := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => ψ (t, w)) (Set.Ici 0) 0 := by
        have hmaps : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Ici 0) S :=
          fun t ht => ⟨ht, hw⟩
        have hpair : ContDiffWithinAt ℝ ∞ (fun t : ℝ => (t, w)) (Set.Ici 0) 0 :=
          (contDiff_id.prodMk contDiff_const).contDiffWithinAt
        exact (hψ (0, w) ⟨Set.self_mem_Ici, hw⟩).comp 0 hpair hmaps
      exact hcomp.of_le (by exact_mod_cast le_top)
    have hsubt : (fun t => (Φ - ψ) (t, w)) = (fun t => Φ (t, w)) - (fun t => ψ (t, w)) := by
      funext t; simp [Pi.sub_apply]
    have htjetw : iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0
        = iteratedDerivWithin i (fun t => ψ (t, w)) (Set.Ici 0) 0 := htjet i hw
    rw [hsubt, iteratedDerivWithin_sub Set.self_mem_Ici (uniqueDiffOn_Ici 0) hΦw hψw,
      htjetw, sub_self]
  -- Apply the vanishing form and unwind.
  have hzero : iteratedFDerivWithin ℝ n (Φ - ψ) S (0, z) = 0 :=
    iteratedFDerivWithin_prod_match_zero_of_jet_vanish hV hD hjet n hz
  rw [hzero] at hsub
  exact sub_eq_zero.mp hsub.symm

end ProdMatch

end Analysis
end DifferentialGeometry
