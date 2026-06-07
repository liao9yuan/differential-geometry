import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartEntryJointSmoothness
import DifferentialGeometry.Bundle.Equiv

/-!
# Joint `(t, x)`-`C∞` of a realized bilinear `Hom`-section from a Sobolev time-tower

This file isolates a single, reusable, manifold-side analysis principle:

> a one-parameter family of smooth compactly-supported `(0, 2)`-tensor sections that is
> `C^k`-in-time into every supercritical spatial Sobolev space `H^{2m}` (for all `k` and
> all `m`) realizes a bilinear bundle `Hom`-section that is **jointly** `(t, x)`-`C∞`.

It is the "anisotropic Sobolev time-tower ⟹ joint smoothness" upgrade missing from both
Mathlib and this library — the *separate-variable → joint-smoothness wall* recorded in
`InteriorChartRegularityBridge.chartGram_realizedMetric_jointContMDiffOn` (continuity in
time into each `Hˢ` plus the spatial `Hˢ ↪ C^m` embedding gives only an anisotropic
tensor-product regularity).  The crucial strengthening here over that wall is that the
hypothesis controls **time-derivatives of every order**, not merely continuity in time:
each iterated time-derivative `∂_t^k` of the family lands, continuously, in `H^{2m}`, hence
(via `H^{2m} ↪ C^{m'}` for `m'` large) in `C^{m'}` of the section; so every mixed partial
`∂_t^k ∂_x^α` exists and is continuous, which is exactly joint `C∞`.

## Main result

* `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower` — from the Sobolev time-tower
  `∀ k m, ContDiffOn ℝ k (fun t => (T_s t).toHs (2 * m)) (Icc 0 T)` the symmetrized
  bilinear `Hom`-section `(t, x) ↦ ccTensorBilinSymm g (T_s t) x` is jointly `(t, x)`-`C∞`
  over the product model `𝓘(ℝ, ℝ).prod I` on the closed slab `Icc 0 T ×ˢ univ`.

## Why this is not hypothesis-packaging, and why it rejects the kink families

The hypothesis is a *time-regularity-into-Sobolev* statement about the **scalar Hilbert
elements** `t ↦ (T_s t).toHs (2 * m)` (a `ContDiffOn ℝ k` of a Banach-valued function of one
real variable); the conclusion is the joint `(t, x)`-smoothness of a **bundle `Hom`-section
over `M`** — a `ContMDiffOn` of a section of `Hom(TM, Hom(TM, ℝ))`.  These are different
objects (one lives in a Hilbert space of one real variable, the other on `ℝ × M`), so the
conclusion is never assumed.

The `C¹`-not-`C²` kink `T_s t := (t − t₀)|t − t₀| · S₀` is rejected at the hypothesis: it is
only once differentiable in `t`, so `t ↦ (T_s t).toHs (2 * m)` is not `ContDiffOn ℝ 2`, and
the tower `∀ k, …` already fails at `k = 2`.  (The `C⁰`-kink `|t − t₀| · S₀` fails even at
`k = 1`.)  The hypothesis is precisely the smoothness that a genuine parabolic carrier
supplies and a kink does not. -/

noncomputable section

open Set Filter Topology Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **`ContMDiffWithinAt` analogue of `contMDiffAt_clm_of_pointwise`.**  Pointwise smoothness
(within a set) of a continuous-linear-map-valued map `A : X → (F₁ →L[ℝ] F₂)` into a *fixed
finite-dimensional* operator space lifts to operator-valued smoothness, by embedding
`F₁ →L[ℝ] F₂ ↪ Fin (rank F₁) → F₂` via evaluation on a basis and a continuous linear left
inverse (the within-a-set version of the proof in `Bundle/Equiv.lean`). -/
private lemma contMDiffWithinAt_clm_of_pointwise
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {n : ℕ∞} {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd ℝ H) X]
    {A : X → (F₁ →L[ℝ] F₂)} {s : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F₂) (n : ℕ∞)
      (fun q => A q v) s x) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F₁ →L[ℝ] F₂) (n : ℕ∞) A s x := by
  haveI : FiniteDimensional ℝ (F₁ →L[ℝ] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis ℝ F₁
  let evalBasis : (F₁ →L[ℝ] F₂) →L[ℝ] (Fin (Module.finrank ℝ F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let g : (Fin (Module.finrank ℝ F₁) → F₂) →L[ℝ] (F₁ →L[ℝ] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, g (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, Fin _ → F₂) (n : ℕ∞)
      (evalBasis ∘ A) s x :=
    contMDiffWithinAt_pi_space.mpr fun i => h (bF₁ i)
  have hAeq : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hAeq]
  have hgsm : ContMDiffWithinAt 𝓘(ℝ, Fin (Module.finrank ℝ F₁) → F₂)
      𝓘(ℝ, F₁ →L[ℝ] F₂) (n : ℕ∞) (⇑g) Set.univ (evalBasis (A x)) :=
    (ContinuousLinearMap.contMDiff (n := (n : ℕ∞)) g).contMDiffAt.contMDiffWithinAt
  exact hgsm.comp x hEA (Set.mapsTo_univ _ _)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Single-chart `baseSet` joint `(t, x)`-`C∞` of the realized symmetrized bilinear
`Hom`-section from a Sobolev time-tower (the genuine anisotropic-Sobolev ⟹ joint-smoothness
analytic core).**

The same data as `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower`, but the joint
`(t, x)`-`C∞` conclusion is asserted over the closed slab `Icc 0 T ×ˢ (trivializationAt E
(TangentSpace I) α).baseSet` of a *single* chart centred at `α`.  This is the genuine analytic
content — the chart-local "Sobolev time-tower ⟹ joint smoothness" upgrade through the missing
mixed-partials reconstruction (the documented jet wall of `InteriorChartRegularityBridge`):
each iterated time-derivative `∂_t^k` of the section lands, via the supercritical Sobolev
embedding `H^{2m} ↪ C^{m'}` (`tensorPouSobolevHilbert_embedding_Ck`, with the chart-local
extraction `tensorHsToC0`-family and the fibre op-norm control
`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`), in `C^{m'}` of the chart-`α` representative,
so every mixed partial `∂_t^k ∂_x^α` of the chart-local representative exists and is continuous
on the closed slab, and the chart-frame matrix entries reconstruct the bundle `Hom`-section
over the chart base set (`contMDiffWithinAt_hom_bundle` / `ContinuousLinearMap.inCoordinates`).

The supercritical order is supplied per spatial-jet order `α` by reading `m` with `2m > dim
M + |α|` from the `∀ m` quantifier of `htower`, and the up-to-`0` boundary jet is the honest
one-sided derivative on `Icc 0 T` (uniquely differentiable, `uniqueDiffOn_Icc`).

The hypothesis is a time-regularity-into-Sobolev statement about the scalar Hilbert elements
`t ↦ (T_s t).toHs (2 * m)`; the conclusion is the joint smoothness of a bundle `Hom`-section on
`M` over the chart base set — a different object — so no packaging.  The `C¹`-not-`C²` kink
`T_s t := (t − t₀)|t − t₀| · S₀` is rejected already at `k = 2` of the tower (its `t ↦
(T_s t).toHs (2m)` is not `ContDiffOn ℝ 2`), exactly as for the global form.

This is the genuine missing analytic theorem isolated as the sole `sorry` leaf; the global-over-
`univ` form `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower` is sorry-free glue over
it (each base point uses its own chart). -/
theorem jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower_baseSet
    (g : SmoothRiemannianMetric I M) (α : M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) {T : ℝ}
    (htower : ∀ (k m : ℕ),
      ContDiffOn ℝ (k : ℕ∞)
        (fun t : ℝ =>
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
        (Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set s : Set (ℝ × M) := Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
    with hs_def
  set e₁ := trivializationAt E (TangentSpace I) α with he₁_def
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  -- The per-basis-pair chart-frame scalar entries are jointly smooth (the jet-wall child).
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M =>
          ccTensorBilinSymm (I := I) g (T_s q.1) q.2
            (chartBasisVecFiber (I := I) α i q.2)
            (chartBasisVecFiber (I := I) α j q.2)) s := fun i j =>
    jointContMDiffOn_ccTensorBilinSymm_chartEntry_baseSet (I := I) (M := M) g α i j T_s htower
  -- For arbitrary model vectors `v, w`, the scalar entry against the chart-`α` frame images of
  -- `v, w` is jointly smooth on `s`: expand `v, w` in the basis `b` and use bilinearity.
  have hscalar : ∀ (v w : E) (q₀ : ℝ × M), q₀ ∈ s →
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M =>
          ccTensorBilinSymm (I := I) g (T_s q.1) q.2
            (e₁.symm q.2 v) (e₁.symm q.2 w)) s q₀ := by
    intro v w q₀ hq₀
    have hbase : ∀ q : ℝ × M, q ∈ s → q.2 ∈ e₁.baseSet := fun q hq => hq.2
    -- On `s` the entry is the double sum over basis pairs of smooth coefficient × child entry.
    have heqOn : Set.EqOn
        (fun q : ℝ × M =>
          ccTensorBilinSymm (I := I) g (T_s q.1) q.2 (e₁.symm q.2 v) (e₁.symm q.2 w))
        (fun q : ℝ × M =>
          ∑ i, ∑ j, (b.repr v i * b.repr w j) •
            ccTensorBilinSymm (I := I) g (T_s q.1) q.2
              (chartBasisVecFiber (I := I) α i q.2)
              (chartBasisVecFiber (I := I) α j q.2)) s := by
      intro q hq
      have hbq : q.2 ∈ e₁.baseSet := hbase q hq
      have hframe : ∀ i : Fin (Module.finrank ℝ E),
          e₁.symmL ℝ q.2 (b i) = chartBasisVecFiber (I := I) α i q.2 := by
        intro i
        have hsnd : (e₁ ⟨q.2, chartBasisVecFiber (I := I) α i q.2⟩).2 = b i := by
          rw [hb_def]
          exact trivializationAt_chartBasisVec_snd (I := I) α i hbq
        rw [Trivialization.symmL_apply, ← hsnd,
          Trivialization.symm_apply_apply_mk e₁ hbq (chartBasisVecFiber (I := I) α i q.2)]
      have hv : e₁.symm q.2 v = ∑ i, b.repr v i • chartBasisVecFiber (I := I) α i q.2 := by
        rw [show e₁.symm q.2 v = e₁.symmL ℝ q.2 v from rfl]
        conv_lhs => rw [← b.sum_repr v]
        rw [map_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, hframe i]
      have hw : e₁.symm q.2 w = ∑ j, b.repr w j • chartBasisVecFiber (I := I) α j q.2 := by
        rw [show e₁.symm q.2 w = e₁.symmL ℝ q.2 w from rfl]
        conv_lhs => rw [← b.sum_repr w]
        rw [map_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul, hframe j]
      change ccTensorBilinSymm (I := I) g (T_s q.1) q.2 (e₁.symm q.2 v) (e₁.symm q.2 w) = _
      rw [hv, hw]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hsum : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M =>
          ∑ i, ∑ j, (b.repr v i * b.repr w j) •
            ccTensorBilinSymm (I := I) g (T_s q.1) q.2
              (chartBasisVecFiber (I := I) α i q.2)
              (chartBasisVecFiber (I := I) α j q.2)) s q₀ := by
      refine contMDiffWithinAt_finset_sum (fun i _ => ?_)
      refine contMDiffWithinAt_finset_sum (fun j _ => ?_)
      exact (contMDiffWithinAt_const).smul ((hentry i j) q₀ hq₀)
    refine hsum.congr_of_eventuallyEq ?_ (heqOn hq₀)
    filter_upwards [self_mem_nhdsWithin] with q hq using heqOn hq
  -- Reconstruct the `Hom`-section pointwise via the fixed chart-`α` trivialization.
  intro q₀ hq₀
  have hq₀base : q₀.2 ∈ e₁.baseSet := hq₀.2
  -- The base projection of the section is `q ↦ q.2`, smooth.
  have hproj : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2)).proj) s q₀ :=
    contMDiffWithinAt_snd
  -- Membership of the section value in the chart-`α` and chart-`q₀.2` `Hom`-trivialisations.
  have hmemα : ∀ q : ℝ × M, q ∈ s →
      (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2)) ∈
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) α).source := by
    intro q hq
    rw [Trivialization.mem_source]
    change q.2 ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) α).baseSet
    rw [hom_trivializationAt_baseSet, hom_trivializationAt_baseSet]
    exact ⟨hq.2, hq.2, Set.mem_univ _⟩
  have hmemq₀ : (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q₀.2 (ccTensorBilinSymm (I := I) g (T_s q₀.1) q₀.2)) ∈
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q₀.2).source := by
    rw [Trivialization.mem_source]
    change q₀.2 ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q₀.2).baseSet
    rw [hom_trivializationAt_baseSet, hom_trivializationAt_baseSet]
    refine ⟨?_, ?_, Set.mem_univ _⟩ <;>
      exact FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) q₀.2
  -- It suffices to prove the chart-`α` trivialised fibre value smooth; transport to the
  -- canonical chart-`q₀.2` trivialisation that `contMDiffWithinAt_totalSpace` consumes.
  refine Bundle.contMDiffWithinAt_totalSpace.mpr ⟨hproj, ?_⟩
  refine ContMDiffWithinAt.change_section_trivialization
    (e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) α)
    hproj ?_ (hmemα q₀ hq₀) hmemq₀
  -- The chart-`α` trivialised fibre value is `inCoordinates` at the chart-`α` frame.
  have htriv_eq : ∀ q : ℝ × M,
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) α
        (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2))).2 =
        ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] ℝ) α q.2 α q.2
          (ccTensorBilinSymm (I := I) g (T_s q.1) q.2) := by
    intro q; rw [hom_trivializationAt_apply]
  simp only [htriv_eq]
  -- Reduce the operator-valued map to its scalar evaluations against arbitrary `v, w`.
  refine contMDiffWithinAt_clm_of_pointwise (I := I) (fun v => ?_)
  refine contMDiffWithinAt_clm_of_pointwise (I := I) (fun w => ?_)
  -- Each scalar evaluation is the chart-`α`-frame entry (`inCoordinates_apply_eq₂`).
  have hscalar_eqOn : Set.EqOn
      (fun q : ℝ × M =>
        ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] ℝ) α q.2 α q.2
          (ccTensorBilinSymm (I := I) g (T_s q.1) q.2) v w)
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_s q.1) q.2 (e₁.symm q.2 v) (e₁.symm q.2 w)) s := by
    intro q hq
    have hbq : q.2 ∈ e₁.baseSet := hq.2
    have hbqℝ : q.2 ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := Set.mem_univ _
    change ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) α q.2 α q.2
        (ccTensorBilinSymm (I := I) g (T_s q.1) q.2) v w = _
    rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun y : M => TangentSpace I y) (E₂ := fun y : M => TangentSpace I y)
      (E₃ := Bundle.Trivial M ℝ)
      (x₀ := α) (x := q.2)
      (ϕ := ccTensorBilinSymm (I := I) g (T_s q.1) q.2)
      (v := v) (w := w) hbq hbq hbqℝ]
    have h_lm_id : (trivializationAt ℝ (Bundle.Trivial M ℝ) α).linearMapAt ℝ q.2
        (ccTensorBilinSymm (I := I) g (T_s q.1) q.2 (e₁.symm q.2 v) (e₁.symm q.2 w)) =
        ccTensorBilinSymm (I := I) g (T_s q.1) q.2 (e₁.symm q.2 v) (e₁.symm q.2 w) := by
      rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hbqℝ]
      rfl
    exact h_lm_id
  refine (hscalar v w q₀ hq₀).congr_of_eventuallyEq ?_ (hscalar_eqOn hq₀)
  filter_upwards [self_mem_nhdsWithin] with q hq using hscalar_eqOn hq

/-- **Joint `(t, x)`-`C∞` of the realized symmetrized bilinear `Hom`-section from a Sobolev
time-tower (the reusable anisotropic-Sobolev ⟹ joint-smoothness principle).**

Let `g` be a closed-manifold smooth Riemannian metric and `T_s : ℝ → SmoothCcTensor g 0 2` a
one-parameter family of smooth compactly-supported `(0, 2)`-tensor sections such that, for
every order `k` of time-differentiation and every spatial Sobolev exponent `2 * m`, the
Banach-valued path `t ↦ (T_s t).toHs (2 * m)` is `C^k` on the closed slab `Icc 0 T`
(`htower`).  Then the symmetrized bilinear bundle `Hom`-section
`(t, x) ↦ ccTensorBilinSymm g (T_s t) x` is jointly `(t, x)`-`C∞` over the product model
`𝓘(ℝ, ℝ).prod I` on the closed slab `Icc 0 T ×ˢ univ`.

The genuine content (the parabolic up-to-boundary classical regularity, Chow–Knopf) is the
chart-local analytic core `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower_baseSet`:
the Sobolev *time-tower* — every iterated time-derivative continuous into every spatial Sobolev
space — upgrades to joint `(t, x)`-smoothness on each chart base set, through the supercritical
Sobolev embedding `H^{2m} ↪ C^{m'}` (`tensorPouSobolevHilbert_embedding_Ck`) and the fibre
op-norm control `gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`, so every mixed partial
`∂_t^k ∂_x^α` exists and is continuous.  This node is the sorry-free *globalisation* glue over
that chart-local core: joint smoothness is a local statement, so at each base point `q₀` it
suffices to work in the chart centred at `q₀.2`, whose base set is an open neighbourhood of
`q₀.2`; restricting the chart-local datum to that neighbourhood
(`ContMDiffWithinAt.mono_of_mem_nhdsWithin`) yields the within-`univ` smoothness there.

The hypothesis is a time-regularity-into-Sobolev statement about scalar Hilbert elements; the
conclusion is the joint smoothness of a bundle section on `M` — a different object — so no
packaging; and the `C¹`-not-`C²` kink is rejected already at `k = 2` of the tower.  The body is
glue over the chart-local core whose body is `sorry`, so consumers transitively depend on
`sorryAx`. -/
theorem jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower
    (g : SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) {T : ℝ}
    (htower : ∀ (k m : ℕ),
      ContDiffOn ℝ (k : ℕ∞)
        (fun t : ℝ =>
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
        (Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  intro q₀ hq₀
  set α : M := q₀.2 with hα
  have hbase_mem : q₀.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) q₀.2
  have hchart :=
    jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower_baseSet (I := I) (M := M)
      g α T_s htower
  have hq₀_chart : q₀ ∈ Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet :=
    ⟨hq₀.1, hbase_mem⟩
  have hwithin := hchart q₀ hq₀_chart
  refine hwithin.mono_of_mem_nhdsWithin ?_
  rw [nhdsWithin_prod_eq]
  refine Filter.prod_mem_prod self_mem_nhdsWithin ?_
  rw [nhdsWithin_univ]
  exact (trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hbase_mem

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
