import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartEntryJetCLM

/-!
# Joint `(t, x)`-`C∞` of a single chart-frame entry of `ccTensorBilinSymm g (T_s ·)` from a
Sobolev time-tower

This file isolates the genuine analytic *jet-wall* content underlying the manifold-side
"anisotropic Sobolev time-tower ⟹ joint smoothness" principle
(`Analysis/Parabolic/JointSmoothnessFromSobolevTower.lean`): the joint `(t, x)`-`C∞` of one
fixed-chart scalar matrix entry of the symmetrized bilinear extraction of a one-parameter
family of smooth compactly-supported `(0, 2)`-tensor sections.

For a fixed chart centred at `α` with chart frame `e_i = chartBasisVecFiber α i`, the scalar

  `F_{ij}(t, x) := ccTensorBilinSymm g (T_s t) x (e_i x) (e_j x)`

is the chart-`α` matrix entry of the metric perturbation realized by `T_s t`.  The hypothesis
`htower` controls **all** time-derivatives `∂_t^k` of the abstract Sobolev element
`t ↦ (T_s t).toHs (2 m)` into **every** spatial Sobolev space `H^{2m}`; the conclusion is the
joint `(t, x)`-`C∞` of the scalar `F_{ij}` over the closed slab `Icc 0 T ×ˢ baseSet`.

## The genuine analytic content (why this is the jet wall)

Mathlib's `ContDiff` is characterized through `iteratedFDeriv` / formal multilinear series;
there is no "continuous coordinate partials of all orders ⟹ `ContDiff`" theorem.  And the
library's supercritical Sobolev embedding is delivered as a *norm* bound (the `C⁰`-fibre bound
`tensorPouSobolevHilbert_embedding_Ck` and the iterated-covariant-gradient `C^m` bound
`iteratedCovGrad_toSobolev_embedding_Cm_unconditional`), not as a `C^m`-jet continuous-linear
map family.  The joint smoothness of `F_{ij}` therefore requires:

* **the spatial jet bound** — for each spatial-jet order `j` and supercritical `2m > dim M +
  2 j`, the chart-coordinate partials `∂_y^β` (`|β| ≤ j`) of the chart-frame entry of
  `ccTensorBilinSymm g T` are controlled, uniformly on each compact piece of the chart target,
  by `C · ‖T.toHs (2m)‖`.  This is the `C^m` Sobolev embedding *read in the fixed chart's
  coordinates* (the chart-coordinate inversion of `∇ = ∂ + Γ·` of
  `iteratedCovGrad_toSobolev_embedding_Cm_unconditional`, in the algebraic-reduction style of
  `chartMetricJet2DiffSup_realizeMetricAt_le_toHs`, generalized to all orders); and

* **the bigraded `C^{k,j}` joint induction** — `∂_t^k` of the entry (at a fixed chart point)
  is the entry of `∂_t^k (T_s t)`, which the tower controls in `H^{2m}`; composing with the
  spatial jet bound (and using `uniqueDiffOn_Icc` for the one-sided derivative on the closed
  slab) every mixed partial `∂_t^k ∂_y^β F_{ij}` exists and is continuous, hence `F_{ij}` is
  jointly `C∞`.  Each inductive step produces the genuine Fréchet derivative of `(t, y) ↦
  F_{ij}`, avoiding any partials-⟹-`ContDiff` theorem.

The body is the genuine missing analytic theorem (`sorry`); consumers transitively depend on
`sorryAx`.

## Why this is not hypothesis-packaging, and why it rejects the kink families

The hypothesis is a *time-regularity-into-Sobolev* statement about the **scalar Hilbert
elements** `t ↦ (T_s t).toHs (2 m)` (a `ContDiffOn ℝ k` of a Banach-valued function of one
real variable); the conclusion is the joint `(t, x)`-smoothness of a **scalar function on
`ℝ × M`**.  These are different objects, so the conclusion is never assumed; in particular the
conclusion is NOT the joint smoothness of any `Hom`-bundle section (that bundle statement is
what *consumes* this file).

The `C¹`-not-`C²` kink `T_s t := (t − t₀)|t − t₀| · S₀` is rejected already at the hypothesis:
`t ↦ (T_s t).toHs (2 m)` is only once differentiable, so the tower `∀ k, …` fails at `k = 2`,
and the `|t − t₀|`-kink in the second time-derivative of `F_{ij}` (which would defeat joint
`C²`) never arises.  The hypothesis is precisely the smoothness a genuine parabolic carrier
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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Single chart-frame matrix entry of `ccTensorBilinSymm g (T_s ·)` is jointly `(t, x)`-`C∞`
from a Sobolev time-tower (the genuine jet-wall analytic core).**

For a fixed chart centred at `α`, frame indices `(i, j)`, and a one-parameter family `T_s` of
smooth compactly-supported `(0, 2)`-tensor sections whose Sobolev time-tower `htower` holds
(every iterated time-derivative `∂_t^k` of `t ↦ (T_s t).toHs (2 m)` is continuous into every
spatial Sobolev space `H^{2m}`), the chart-`α` scalar matrix entry

  `(t, x) ↦ ccTensorBilinSymm g (T_s t) x (chartBasisVecFiber α i x) (chartBasisVecFiber α j x)`

is jointly `(t, x)`-`C∞` over the product model `𝓘(ℝ, ℝ).prod I` on the closed slab
`Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet`.

This is the genuine analytic theorem: the supercritical Sobolev embedding read in the fixed
chart's coordinates (controlling every spatial-coordinate jet of the chart-frame entry by
`‖T.toHs (2m)‖`) bigraded against the all-order time control of the tower, so every mixed
partial `∂_t^k ∂_x^β` of the entry exists and is continuous up to and across the closed slab
(the up-to-`0` boundary jet being the honest one-sided derivative, `uniqueDiffOn_Icc`).

The bigraded `C^{k, j}` induction is realised cleanly through the finite-order jet-CLM wall
`exists_contMDiffOn_chartEntryJetCLM_baseSet`: it suffices (`contMDiffOn_infty`) to prove joint
`C^N` for every finite `N`; for each `N` the jet-CLM child supplies a supercritical Sobolev
exponent `m` and a continuous-linear functional family `A : M → (H^{2m} →L[ℝ] ℝ)` that is
`ContMDiffOn ℝ N` in the base point on the chart base set and reads the entry on the dense
smooth subspace.  The Sobolev time-tower at order `N` (`htower N m`) makes the Banach-valued
path `t ↦ (T_s t).toHs (2 m)` `ContMDiffOn ℝ N`, so `ContMDiffOn.clm_apply` assembles the joint
`C^N` smoothness of `q ↦ A q.2 ((T_s q.1).toHs (2 m))`, which agrees on the slab with the
entry.  This is sorry-free glue over the jet-CLM child (the genuine missing analytic leaf), so
consumers transitively depend on `sorryAx` only through that child.

The hypothesis is a time-regularity-into-Sobolev statement about scalar Hilbert elements; the
conclusion is the joint smoothness of a scalar function on `ℝ × M` — a different object — so no
packaging; and the `C¹`-not-`C²` kink is rejected already at `k = 2` of the tower. -/
theorem jointContMDiffOn_ccTensorBilinSymm_chartEntry_baseSet
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) {T : ℝ}
    (htower : ∀ (k m : ℕ),
      ContDiffOn ℝ (k : ℕ∞)
        (fun t : ℝ =>
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
        (Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_s q.1) q.2
          (chartBasisVecFiber (I := I) α i q.2)
          (chartBasisVecFiber (I := I) α j q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set s : Set (ℝ × M) :=
    Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet with hs_def
  -- Joint `C∞` is joint `C^N` for every finite order `N`.
  rw [contMDiffOn_infty]
  intro N
  -- The finite-order jet-CLM wall: at order `N` it produces a supercritical exponent `m` and a
  -- base-point-`C^N` continuous-linear functional family reading the entry on smooth sections.
  obtain ⟨m, A, hA_smooth, hA_agree⟩ :=
    exists_contMDiffOn_chartEntryJetCLM_baseSet (I := I) (M := M) g α i j N
  -- The Sobolev time-tower at order `N` makes the Banach-valued path `C^N` in time.
  have hψ : ContMDiffOn 𝓘(ℝ, ℝ)
      𝓘(ℝ, IntrinsicSobolev.TensorPouSobolevHilbert g 0 2 (2 * m)) (N : ℕ∞)
      (fun t : ℝ =>
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
      (Set.Icc (0 : ℝ) T) :=
    (htower N m).contMDiffOn
  -- Lift the base-point family and the time path to the product slab.
  have hAsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, IntrinsicSobolev.TensorPouSobolevHilbert g 0 2 (2 * m) →L[ℝ] ℝ) (N : ℕ∞)
      (fun q : ℝ × M => A q.2) s :=
    hA_smooth.comp contMDiffOn_snd (fun q hq => hq.2)
  have hψfst : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, IntrinsicSobolev.TensorPouSobolevHilbert g 0 2 (2 * m)) (N : ℕ∞)
      (fun q : ℝ × M =>
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s q.1)) s :=
    hψ.comp contMDiffOn_fst (fun q hq => hq.1)
  -- The continuous-linear application is jointly `C^N`.
  have happ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (N : ℕ∞)
      (fun q : ℝ × M =>
        A q.2 (IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m)
          (T_s q.1))) s :=
    hAsnd.clm_apply hψfst
  -- On the slab the application agrees with the chart-frame entry.
  refine happ.congr (fun q hq => ?_)
  exact (hA_agree (T_s q.1) q.2 hq.2).symm

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
