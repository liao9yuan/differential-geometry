import DifferentialGeometry.Integral.Measure.Family

/-!
# Packaging joint-smooth time-parameterised Riemannian metric families

A thin bridge between a joint-smooth time-parameterised Riemannian metric family
and the pointwise regularity interface used by the volume-variation engine.

A `SmoothRiemannianMetricFamily` bundles a time-indexed family of smooth
Riemannian metrics on `M` together with a joint `C^∞` hypothesis on
`(t, x) ↦ g_t(x)` at the chart-local Gram-matrix level. From such a family, the
packaging lemma `metricFamilyRegularAt_of_smoothFamily` produces the
`MetricFamilyRegularAt` interface required by the engine.

The analogue `functionRegularAt_of_jointContMDiff` covers a real-valued
integrand `f : ℝ → M → ℝ` that is jointly smooth on `ℝ × M`.

## Main declarations

* `SmoothRiemannianMetricFamily I M` : jointly-smooth metric family.
* `SmoothRiemannianMetricFamily.coe_mk` : unfolding lemma.
* `metricFamilyRegularAt_of_smoothFamily` : extract the regularity interface.
* `functionRegularAt_of_jointContMDiff` : extract the regularity interface for
  a jointly-smooth integrand.

## Note on the `[I.Boundaryless]` hypothesis

The bridge lemmas in this file carry an `[I.Boundaryless]` hypothesis. This
hypothesis is local to this bridge file: it is needed by the current proofs
that translate joint smoothness on `ℝ × M` into the pointwise `MetricFamilyRegularAt`
interface (the proofs unfold chart-Gram entries via `(extChartAt I α).symm`,
which is `C^∞` at every target point only when the chart target is open in `E`,
i.e., only under `[I.Boundaryless]`).

This hypothesis does **not** propagate into the integration / divergence /
parabolic engines. Those engines consume only the `MetricFamilyRegularAt`
and `FunctionRegularAt` interfaces, which are defined without any
`Boundaryless` reference. Down-stream calls that need a with-boundary
packaging should furnish a different bridge (e.g., one constructed from
`fderivWithin (range I)`-style joint regularity), without revisiting the
present file.
-/

noncomputable section

open Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- A jointly-smooth time-parameterised family of Riemannian metrics on `M`.
The joint smoothness field asserts `C^∞` in both arguments `(t, x) ∈ ℝ × M`, at
the level of the Gram matrices of the canonical chart-local frames.

Concretely, for every `x₀ : M`, the map `(t, x) ↦ chartGramMatrix (toFun t) x₀ x`
is required to be `C^∞` on `ℝ × (trivializationAt E (TangentSpace I) x₀).baseSet`.
This matrix-level formulation avoids the technical subtleties of defining a
pulled-back tangent bundle on `ℝ × M` and is equivalent, on chart domains, to
joint bundle-level smoothness. -/
structure SmoothRiemannianMetricFamily where
  /-- The underlying time-indexed metric family. -/
  toFun : ℝ → SmoothRiemannianMetric I M
  /-- Joint `C^∞` smoothness of each chart-local Gram-matrix entry in `(t, x)`. -/
  contMDiffOn_chartGramMatrix_entry :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (toFun p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

/-- Coerce a family to the underlying function `ℝ → SmoothRiemannianMetric I M`. -/
instance : CoeFun (SmoothRiemannianMetricFamily I M)
    (fun _ => ℝ → SmoothRiemannianMetric I M) :=
  ⟨SmoothRiemannianMetricFamily.toFun⟩

@[simp] lemma SmoothRiemannianMetricFamily.coe_mk
    (toFun : ℝ → SmoothRiemannianMetric I M) (h) :
    (({ toFun := toFun,
          contMDiffOn_chartGramMatrix_entry := h } : SmoothRiemannianMetricFamily I M) :
      ℝ → SmoothRiemannianMetric I M) = toFun := rfl

/-! ## Bridge: jointly-smooth family → `MetricFamilyRegularAt`

From a `SmoothRiemannianMetricFamily`, every Gram-matrix entry is
time-differentiable at every time (restricted to the chart base set), and each
such entry and its time-derivative is jointly continuous on
`ℝ ×ˢ base_α`. These are exactly the three fields of
`MetricFamilyRegularAt`. -/

namespace SmoothRiemannianMetricFamily

private lemma contDiff_chartGramMatrix_time
    (gFam : SmoothRiemannianMetricFamily I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (fun t : ℝ => chartGramMatrix (I := I) (gFam t) x₀ x i j) := by
  have hjoint := gFam.contMDiffOn_chartGramMatrix_entry x₀ i j
  refine contDiff_iff_contDiffAt.mpr (fun t => ?_)
  have hp : (t, x) ∈
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet : Set (ℝ × M)) :=
    ⟨Set.mem_univ _, hx⟩
  have hjoint_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => chartGramMatrix (I := I) (gFam p.1) x₀ p.2 i j) (t, x) := by
    apply (hjoint (t, x) hp).contMDiffAt
    exact IsOpen.mem_nhds
      ((isOpen_univ).prod
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet)) hp
  have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
      (fun t : ℝ => (t, x)) t :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have hcomp := hjoint_at.comp t hincl
  rwa [contMDiffAt_iff_contDiffAt] at hcomp

end SmoothRiemannianMetricFamily

/-- From a jointly-smooth family, extract the minimum pointwise regularity
interface at any base time.

The hypothesis `[I.Boundaryless]` is required by the current proof, which
pulls each chart-local Gram-matrix entry back to a function on a Euclidean
domain via the chart and computes the time-derivative via `fderiv`; this
chart-image-as-Euclidean-open argument requires the chart target to be open
in `E`. The pointwise regularity interface `MetricFamilyRegularAt` itself is
boundary-tolerant; users on a manifold with boundary may construct it
directly from their joint smoothness assumption without invoking this
packaging lemma. -/
theorem metricFamilyRegularAt_of_smoothFamily
    [I.Boundaryless]
    (gFam : SmoothRiemannianMetricFamily I M) (t₀ : ℝ) :
    MetricFamilyRegularAt (I := I) gFam.toFun t₀ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Pointwise `HasDerivAt` at every time, from time-slice smoothness.
    intro x₀ i j x hx t
    have hcd := gFam.contDiff_chartGramMatrix_time x₀ hx i j
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
    exact (hcd.differentiable hne).differentiableAt.hasDerivAt
  · -- Joint continuity of each Gram-matrix entry.
    intro x₀ i j
    exact (gFam.contMDiffOn_chartGramMatrix_entry x₀ i j).continuousOn
  · -- Joint continuity of the time-derivative of each Gram-matrix entry.
    -- The key step: the joint `ContMDiffOn` implies `ContDiffOn` on an open set in
    -- `ℝ × E` after pulling back via a chart, and the partial derivative is
    -- therefore continuous in the joint variable.
    intro x₀ i j
    refine continuousOn_iff_continuous_restrict.mpr ?_
    refine continuous_iff_continuousAt.mpr (fun q₀ => ?_)
    set r₀ : ℝ := q₀.val.1
    set y₀ : M := q₀.val.2
    have hq₀_mem : q₀.val ∈
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet : Set (ℝ × M)) :=
      q₀.property
    have hy₀_base : y₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hq₀_mem.2
    set ec0 : PartialEquiv M E := extChartAt I y₀
    have hy₀_src : y₀ ∈ ec0.source := mem_extChartAt_source (I := I) y₀
    have hec0_tgt_open : IsOpen ec0.target := isOpen_extChartAt_target (I := I) y₀
    have hx₀_base_open : IsOpen (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet
    set U0 : Set M := ec0.source ∩ (trivializationAt E (TangentSpace I) x₀).baseSet
    have hU0_open : IsOpen U0 :=
      (isOpen_extChartAt_source (I := I) y₀).inter hx₀_base_open
    have hy₀_U0 : y₀ ∈ U0 := ⟨hy₀_src, hy₀_base⟩
    set ψ : ℝ × E → ℝ := fun p : ℝ × E =>
      chartGramMatrix (I := I) (gFam p.1) x₀ (ec0.symm p.2) i j
    set eU0 : Set E := ec0 '' U0
    have hpair : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, ec0.symm q.2)) (Set.univ ×ˢ ec0.target) := by
      refine ContMDiffOn.prodMk contMDiffOn_fst ?_
      refine (contMDiffOn_extChartAt_symm (I := I) y₀).comp contMDiffOn_snd ?_
      intro q hq; exact hq.2
    have hpair_restrict : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
        (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, ec0.symm q.2)) (Set.univ ×ˢ eU0) := by
      refine hpair.mono ?_
      intro q hq
      refine ⟨Set.mem_univ _, ?_⟩
      obtain ⟨_, ⟨y, hyU, hy_eq⟩⟩ := hq
      rw [← hy_eq]
      exact ec0.map_source hyU.1
    have hmaps : Set.MapsTo (fun q : ℝ × E => (q.1, ec0.symm q.2))
        (Set.univ ×ˢ eU0)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro q hq
      refine ⟨Set.mem_univ _, ?_⟩
      obtain ⟨_, ⟨y, hyU, hy_eq⟩⟩ := hq
      have h_symm_eq : ec0.symm (ec0 y) = y := ec0.left_inv hyU.1
      change ec0.symm q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet
      rw [← hy_eq, h_symm_eq]
      exact hyU.2
    have hψ_mdiff : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ ψ
        (Set.univ ×ˢ eU0) :=
      (gFam.contMDiffOn_chartGramMatrix_entry x₀ i j).comp hpair_restrict hmaps
    have heU0_open : IsOpen eU0 := by
      have h_eq : eU0 = ec0.target ∩ ec0.symm ⁻¹' U0 := by
        ext y
        constructor
        · rintro ⟨x, hxU, hx_eq⟩
          refine ⟨?_, ?_⟩
          · rw [← hx_eq]; exact ec0.map_source hxU.1
          · rw [Set.mem_preimage, ← hx_eq]; rw [ec0.left_inv hxU.1]; exact hxU
        · rintro ⟨hytgt, hysU⟩
          refine ⟨ec0.symm y, hysU, ?_⟩; exact ec0.right_inv hytgt
      rw [h_eq]
      exact (continuousOn_extChartAt_symm (I := I) y₀).isOpen_inter_preimage
        hec0_tgt_open hU0_open
    have hψ_cdon : ContDiffOn ℝ ∞ ψ (Set.univ ×ˢ eU0) := by
      intro q hq
      have h_at : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ ψ q := by
        refine (hψ_mdiff q hq).contMDiffAt ?_
        exact (isOpen_univ.prod heU0_open).mem_nhds hq
      have : ContDiffAt ℝ ∞ ψ q := by
        rw [show (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E) : ModelWithCorners ℝ (ℝ × E) (ℝ × E))
            = 𝓘(ℝ, ℝ × E) from modelWithCornersSelf_prod.symm,
            chartedSpaceSelf_prod (H := ℝ) (H' := E)] at h_at
        exact h_at.contDiffAt
      exact this.contDiffWithinAt
    have hopen0 : IsOpen (Set.univ ×ˢ eU0 : Set (ℝ × E)) := isOpen_univ.prod heU0_open
    have hcda0 : ∀ q ∈ (Set.univ ×ˢ eU0 : Set (ℝ × E)), ContDiffAt ℝ ∞ ψ q :=
      fun q hq => hψ_cdon.contDiffAt (hopen0.mem_nhds hq)
    have hpoint_eq : ∀ r : ℝ, ∀ y ∈ U0,
        deriv (fun s : ℝ => chartGramMatrix (I := I) (gFam s) x₀ y i j) r
          = (fderiv ℝ ψ (r, ec0 y) : ℝ × E → ℝ) ((1 : ℝ), (0 : E)) := by
      intro r y hy
      have h_symm_eq : ec0.symm (ec0 y) = y := ec0.left_inv hy.1
      have hey_mem : ec0 y ∈ eU0 := ⟨y, hy, rfl⟩
      have hda : ContDiffAt ℝ ∞ ψ (r, ec0 y) :=
        hcda0 (r, ec0 y) (by exact ⟨Set.mem_univ _, hey_mem⟩)
      have hdif : DifferentiableAt ℝ ψ (r, ec0 y) :=
        hda.differentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
      have hfd : HasFDerivAt ψ (fderiv ℝ ψ (r, ec0 y)) (r, ec0 y) := hdif.hasFDerivAt
      have hslice :
          HasDerivAt (fun s : ℝ => ψ (s, ec0 y))
            ((fderiv ℝ ψ (r, ec0 y) : ℝ × E → ℝ) ((1 : ℝ), (0 : E))) r := by
        have h_incl : HasFDerivAt (fun s : ℝ => (s, ec0 y))
            ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] E)) r :=
          (hasFDerivAt_id r).prodMk (hasFDerivAt_const (ec0 y) r)
        have := hfd.comp r h_incl
        have hdd := this.hasDerivAt
        convert hdd using 1
      have hfn_eq :
          (fun s : ℝ => ψ (s, ec0 y))
            = fun s : ℝ => chartGramMatrix (I := I) (gFam s) x₀ y i j := by
        funext s
        change chartGramMatrix (I := I) (gFam s) x₀ (ec0.symm (ec0 y)) i j
          = chartGramMatrix (I := I) (gFam s) x₀ y i j
        rw [h_symm_eq]
      rw [hfn_eq] at hslice
      exact hslice.deriv
    have hcda_q₀ : ContDiffAt ℝ ∞ ψ (r₀, ec0 y₀) := by
      have hey : ec0 y₀ ∈ eU0 := ⟨y₀, hy₀_U0, rfl⟩
      exact hcda0 (r₀, ec0 y₀) (by exact ⟨Set.mem_univ _, hey⟩)
    have hfderiv_cda : ContDiffAt ℝ 0 (fun q : ℝ × E => fderiv ℝ ψ q) (r₀, ec0 y₀) := by
      have hstep : ContDiffAt ℝ (0 + 1) ψ (r₀, ec0 y₀) := by
        refine hcda_q₀.of_le ?_
        norm_num
      exact hstep.fderiv_right (m := 0) le_rfl
    have hfderiv_cont_at :
        ContinuousAt (fun q : ℝ × E => fderiv ℝ ψ q) (r₀, ec0 y₀) :=
      hfderiv_cda.continuousAt
    have hevalCont :
        Continuous (fun L : (ℝ × E) →L[ℝ] ℝ => L ((1 : ℝ), (0 : E))) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).continuous
    have hfderiv_apply_cont :
        ContinuousAt (fun q : ℝ × E => (fderiv ℝ ψ q : ℝ × E → ℝ)
          ((1 : ℝ), (0 : E))) (r₀, ec0 y₀) :=
      hevalCont.continuousAt.comp hfderiv_cont_at
    have hecCont : ContinuousAt (fun x : M => ec0 x) y₀ := by
      have := (continuousOn_extChartAt (I := I) y₀).continuousAt
        ((isOpen_extChartAt_source (I := I) y₀).mem_nhds hy₀_src)
      exact this
    have h_fst_cont : ContinuousAt (Prod.fst : ℝ × M → ℝ) q₀.val :=
      continuous_fst.continuousAt
    have h_snd_cont : ContinuousAt (fun p : ℝ × M => ec0 p.2) q₀.val :=
      hecCont.comp continuous_snd.continuousAt
    have hpairM_cont : ContinuousAt
        (fun p : ℝ × M => ((p.1, ec0 p.2) : ℝ × E)) (q₀.val) :=
      h_fst_cont.prodMk h_snd_cont
    have hev_ambient : (fun p : ℝ × M =>
        deriv (fun s : ℝ => chartGramMatrix (I := I) (gFam s) x₀ p.2 i j) p.1)
          =ᶠ[𝓝 q₀.val]
        (fun p : ℝ × M =>
          (fderiv ℝ ψ (p.1, ec0 p.2) : ℝ × E → ℝ) ((1 : ℝ), (0 : E))) := by
      have hnbhd : (Set.univ ×ˢ U0 : Set (ℝ × M)) ∈ 𝓝 q₀.val :=
        (isOpen_univ.prod hU0_open).mem_nhds ⟨Set.mem_univ _, hy₀_U0⟩
      filter_upwards [hnbhd] with p hp
      have hp2U : p.2 ∈ U0 := hp.2
      exact hpoint_eq p.1 p.2 hp2U
    have hcont_ambient : ContinuousAt
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => chartGramMatrix (I := I) (gFam s) x₀ p.2 i j) p.1)
        q₀.val := by
      refine ContinuousAt.congr ?_ hev_ambient.symm
      exact hfderiv_apply_cont.comp (x := q₀.val) hpairM_cont
    exact hcont_ambient.comp continuousAt_subtype_val

/-- From a jointly `C^∞` function `(t, x) ↦ f t x`, extract the minimum
pointwise regularity interface for a scalar integrand at any base time.

The hypothesis `[I.Boundaryless]` is required by the current proof, which
pulls `f` back to a function on a Euclidean domain via the chart and
computes the time-derivative via `fderiv`; this chart-image-as-Euclidean-open
argument requires the chart target to be open in `E`. The pointwise
regularity interface `FunctionRegularAt` itself is boundary-tolerant; users
on a manifold with boundary may construct it directly from their joint
smoothness assumption without invoking this packaging lemma. -/
theorem functionRegularAt_of_jointContMDiff
    [I.Boundaryless]
    {f : ℝ → M → ℝ} (t₀ : ℝ)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => f p.1 p.2)) :
    FunctionRegularAt f t₀ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Pointwise `HasDerivAt` at every time from time-slice smoothness.
    intro x t
    have hincl : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun r : ℝ => (r, x)) :=
      contMDiff_id.prodMk contMDiff_const
    have hcomp := hf.comp hincl
    rw [contMDiff_iff_contDiff] at hcomp
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
    exact (hcomp.differentiable hne).differentiableAt.hasDerivAt
  · -- Joint continuity of `f` on `ℝ × M`.
    exact hf.continuous
  · -- Joint continuity of the pointwise time-derivative.
    refine continuous_iff_continuousAt.mpr (fun p₀ => ?_)
    set α' : M := p₀.2
    set ec : PartialEquiv M E := extChartAt I α'
    have hsrc_open : IsOpen ec.source := isOpen_extChartAt_source (I := I) α'
    have hx_src : p₀.2 ∈ ec.source := mem_extChartAt_source (I := I) p₀.2
    have htgt_open : IsOpen ec.target := isOpen_extChartAt_target (I := I) α'
    set g : ℝ × E → ℝ := fun q : ℝ × E => f q.1 (ec.symm q.2)
    have hpair_mdiff : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, ec.symm q.2)) (Set.univ ×ˢ ec.target) := by
      refine ContMDiffOn.prodMk contMDiffOn_fst ?_
      refine (contMDiffOn_extChartAt_symm (I := I) α').comp contMDiffOn_snd ?_
      intro q hq
      exact hq.2
    have hg_mdiff : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ g
        (Set.univ ×ˢ ec.target) := by
      have : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => f p.1 p.2) Set.univ := hf.contMDiffOn
      exact this.comp (t := Set.univ) hpair_mdiff (fun q _ => Set.mem_univ _)
    have hg_cdon : ContDiffOn ℝ ∞ g (Set.univ ×ˢ ec.target) := by
      intro q hq
      have h_at : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ g q := by
        refine (hg_mdiff q hq).contMDiffAt ?_
        exact (isOpen_univ.prod htgt_open).mem_nhds hq
      have : ContDiffAt ℝ ∞ g q := by
        rw [show (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E) : ModelWithCorners ℝ (ℝ × E) (ℝ × E))
            = 𝓘(ℝ, ℝ × E) from modelWithCornersSelf_prod.symm,
            chartedSpaceSelf_prod (H := ℝ) (H' := E)] at h_at
        exact h_at.contDiffAt
      exact this.contDiffWithinAt
    have hopen : IsOpen (Set.univ ×ˢ ec.target : Set (ℝ × E)) :=
      isOpen_univ.prod htgt_open
    have hcda : ∀ q ∈ (Set.univ ×ˢ ec.target : Set (ℝ × E)), ContDiffAt ℝ ∞ g q :=
      fun q hq => hg_cdon.contDiffAt (hopen.mem_nhds hq)
    have hpoint : ∀ r : ℝ, ∀ y ∈ ec.source,
        deriv (fun s : ℝ => f s y) r
          = (fderiv ℝ g (r, ec y) : ℝ × E → ℝ) ((1 : ℝ), (0 : E)) := by
      intro r y hy
      have heqsymm : ec.symm (ec y) = y := ec.left_inv hy
      have hey_tgt : ec y ∈ ec.target := ec.map_source hy
      have hcda_at : ContDiffAt ℝ ∞ g (r, ec y) :=
        hcda (r, ec y) (by exact ⟨Set.mem_univ _, hey_tgt⟩)
      have hdif : DifferentiableAt ℝ g (r, ec y) :=
        hcda_at.differentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
      have hfd : HasFDerivAt g (fderiv ℝ g (r, ec y)) (r, ec y) := hdif.hasFDerivAt
      have hslice :
          HasDerivAt (fun s : ℝ => g (s, ec y))
            ((fderiv ℝ g (r, ec y) : ℝ × E → ℝ) ((1 : ℝ), (0 : E))) r := by
        have h_incl : HasFDerivAt (fun s : ℝ => (s, ec y))
            ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] E)) r :=
          (hasFDerivAt_id r).prodMk (hasFDerivAt_const (ec y) r)
        have := hfd.comp r h_incl
        have hdd := this.hasDerivAt
        convert hdd using 1
      have hfn_eq :
          (fun s : ℝ => g (s, ec y)) = fun s : ℝ => f s y := by
        funext s
        change f s (ec.symm (ec y)) = f s y
        rw [heqsymm]
      rw [hfn_eq] at hslice
      exact hslice.deriv
    have hcda_p₀ : ContDiffAt ℝ ∞ g (p₀.1, ec p₀.2) := by
      have : ec p₀.2 ∈ ec.target := ec.map_source hx_src
      exact hcda (p₀.1, ec p₀.2) (by exact ⟨Set.mem_univ _, this⟩)
    have hfderiv_cda : ContDiffAt ℝ 0 (fun q : ℝ × E => fderiv ℝ g q)
        (p₀.1, ec p₀.2) := by
      have hstep : ContDiffAt ℝ (0 + 1) g (p₀.1, ec p₀.2) := by
        refine hcda_p₀.of_le ?_
        norm_num
      exact hstep.fderiv_right (m := 0) le_rfl
    have hfderiv_cont_at : ContinuousAt (fun q : ℝ × E => fderiv ℝ g q)
        (p₀.1, ec p₀.2) := hfderiv_cda.continuousAt
    have hevalCont :
        Continuous (fun L : (ℝ × E) →L[ℝ] ℝ => L ((1 : ℝ), (0 : E))) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).continuous
    have hecCont : ContinuousAt (fun y : M => ec y) p₀.2 := by
      exact (continuousOn_extChartAt (I := I) α').continuousAt
        (hsrc_open.mem_nhds hx_src)
    have hfderiv_apply_cont :
        ContinuousAt (fun q : ℝ × E => (fderiv ℝ g q : ℝ × E → ℝ)
          ((1 : ℝ), (0 : E))) (p₀.1, ec p₀.2) :=
      (hevalCont.continuousAt).comp hfderiv_cont_at
    have hev : (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) =ᶠ[𝓝 p₀]
        (fun p : ℝ × M =>
          (fderiv ℝ g (p.1, ec p.2) : ℝ × E → ℝ) ((1 : ℝ), (0 : E))) := by
      have hnbhd : ((Set.univ ×ˢ ec.source) : Set (ℝ × M)) ∈ 𝓝 p₀ :=
        IsOpen.mem_nhds (isOpen_univ.prod hsrc_open) ⟨Set.mem_univ _, hx_src⟩
      filter_upwards [hnbhd] with p hp
      exact hpoint p.1 p.2 hp.2
    refine ContinuousAt.congr ?_ hev.symm
    have h_fst_cont : ContinuousAt (Prod.fst : ℝ × M → ℝ) p₀ := continuous_fst.continuousAt
    have h_snd_cont : ContinuousAt (fun p : ℝ × M => ec p.2) p₀ :=
      hecCont.comp continuous_snd.continuousAt
    have h_pair : ContinuousAt (fun p : ℝ × M => ((p.1, ec p.2) : ℝ × E)) p₀ :=
      h_fst_cont.prodMk h_snd_cont
    exact hfderiv_apply_cont.comp (x := p₀) h_pair

end Measure
end Integral
end DifferentialGeometry
