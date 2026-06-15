import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.ConjugatingFlowProperties

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Regularity of the extended Ricci-flow solution (Dispatch B) — BANKED GATE BRICK

Toward assembling `IsSolutionOn` for the extended metric family produced by
`ricci_flow_extends_construction` (from its chart-Gram `C∞`/continuity outputs), the linchpin is a
builder `metricFamilySmoothOn_of_chartGram` whose only nontrivial field, `frameCompSmooth`, needs the
metric bilinear-CLM bundle section to be jointly `C∞` on a **general** open time interval.

The banked `metricCLMSection_jointContMDiffOn_of_chartGram`
(`ShortTimeFlow/ConjugatingFlowProperties.lean`) provides this only on `Ioo 0 T`.  This file's
`metricCLMSection_jointContMDiffOn_of_chartGram_Ioo` **generalizes it to any `Ioo a b`** by an affine
time-shift — the decisive feasibility brick proving the linchpin is constructible (the keystone's
`(0,T)` hardcoding only used openness, so the shift transports cleanly).

STATUS (2026-06-14, Dispatch B 2h time-box): gate brick DONE + verified.  The remaining linchpin
fields (`coeff`/`coeff_cont` time-slice extraction, `frameCompSmooth` via `clm_bundle_apply₂` against
the C∞ frame, `metricTensor_cont` via `metricTensorCont_of_chartGram`) plus the full `IsSolutionOn`
assembly — and especially the genuinely-UNBUILT `rm04Cont` (0,4)-Riemann carrier continuity — are the
multi-session remainder.  This file is reusable for BOTH the `IsSolutionOn Shat` of `extends_of_rmBounded`
AND the `ham3_short_isSolution` sorry.  See `MaximalTime.md`.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Metric bilinear-CLM section joint `C∞` on a general open interval `Ioo a b`.**
Time-shift of `metricCLMSection_jointContMDiffOn_of_chartGram` (which is stated on `Ioo 0 T`):
apply it to `g (· + a)` on `Ioo 0 (b - a)`, then transport along the affine maps `t ↦ t ± a`. -/
theorem metricCLMSection_jointContMDiffOn_of_chartGram_Ioo
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2)))
      (Set.Ioo a b ×ˢ Set.univ) := by
  -- the shifted family and the two affine reparametrisations
  set gsh : ℝ → SmoothRiemannianMetric I M := fun s => g (s + a) with hgsh
  -- `add a : (t,m) ↦ (t + a, m)` maps `Ioo 0 (b-a) ×ˢ U` into `Ioo a b ×ˢ U`
  have haddC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 + a, p.2)) :=
    (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
  -- `sub a : (t,m) ↦ (t - a, m)` maps `Ioo a b ×ˢ U` into `Ioo 0 (b-a) ×ˢ U`
  have hsubC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 - a, p.2)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  -- chart-Gram of the shifted family on `Ioo 0 (b-a)` (precompose `hgram` with `add a`)
  have hgram_sh : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (gsh p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1 + a, p.2))
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      rintro ⟨s, m⟩ ⟨hs, hm⟩
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hm⟩
    exact (hgram x₀ i j).comp haddC.contMDiffOn hmaps
  -- the shifted CLM section is `C∞` on `Ioo 0 (b-a) ×ˢ univ`
  have hsh := metricCLMSection_jointContMDiffOn_of_chartGram (I := I) gsh (b - a) hgram_sh
  -- transport back along `sub a`
  have hmaps2 : Set.MapsTo (fun p : ℝ × M => (p.1 - a, p.2))
      (Set.Ioo a b ×ˢ (Set.univ : Set M))
      (Set.Ioo (0 : ℝ) (b - a) ×ˢ (Set.univ : Set M)) := by
    rintro ⟨t, m⟩ ⟨ht, _⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Set.mem_univ _⟩
  have hcomp := hsh.comp hsubC.contMDiffOn hmaps2
  -- the composite equals the target section (gsh (t - a) = g t)
  refine hcomp.congr ?_
  rintro ⟨t, m⟩ _
  simp only [Function.comp_apply, hgsh, sub_add_cancel]

end DifferentialGeometry.PDE.RicciFlow
