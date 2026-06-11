import DifferentialGeometry.Geometry.Connection.DeTurckVFCovGradTopRestSplit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciSectionIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction

/-! # The intrinsic covariant top/rest expansion of the sealed Ricci–DeTurck Lie difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file is the **intrinsic bridge** discharging the sealed Lie-summand
difference's covariant top/rest split — the gauge primitive
`lieDerivDiff_connLevel_topRestSplit` — through the **Cartan-formula route**, with no chart read.

The bridge composes two ingredients:

* **(P1a — the section-level Cartan identity)** `lieDerivRetagG0_eq_symLoweredRetagG0`
  (`Geometry/Flow/RicciFlow/Pullback/Cartan/LieDerivSectionCartan.lean`): the sealed `g₀`-retagged
  Lie summand `lieDerivRetagG0 g₀ g_bg g₁` equals the `g₀`-retagged symmetrised covariant lowering of
  the DeTurck vector field `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg`.  Lifted pointwise from the
  axiom-clean Cartan formula `cartan_formula_for_lie_deriv_metric`, it re-expresses the opaque
  algebraic-complement Lie section as the manifestly `∇W`-built intrinsic section — the form whose
  covariant top/rest split is amenable to the metric-contraction engine.  Applied to each of `g₁, g₂`,
  it rewrites the sealed Lie difference into the symmetrised-lowered DeTurck-field difference (the
  section-level telescope: each metric's Lie summand IS its `∇W`-lowering, so the difference is the
  difference of the `∇W`-lowerings, `lieDerivRetagG0_sub_eq_symLoweredRetagG0_sub`).

* **(P1b — the deep gauge top/rest split)** `symLoweredDeTurckVF_iteratedCovGrad_topRest_split`
  (`Geometry/Connection/DeTurckVFCovGradTopRestSplit.lean`): the genuine deep covariant-Leibniz
  top/rest split of the symmetrised-lowered DeTurck-field difference, riding the sorry-free
  `DiffBilinOp` / `RfnsBilinearProduct` engine, the gauge analogue (parity-depth) of the curvature
  half's posited `crossCorrectionSection_iteratedCovGrad_topRest_split`.

The expansion `lieDerivDiff_intrinsic_covFdB_section_expansion` is the leaf-shaped Top/Rest split of
the sealed Lie difference, obtained by rewriting through P1a and applying P1b.  It transits `sorryAx`
only through the single genuine deep gauge primitive `symLoweredDeTurckVF_iteratedCovGrad_topRest_split`
(the chart-free, intrinsic replacement of the banned chart-witness route). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The sealed Lie difference equals the symmetrised-lowered DeTurck-field difference.**  The
section-level Cartan telescope: applying the retagged section-level Cartan identity
`lieDerivRetagG0_eq_symLoweredRetagG0` to each of `g₁, g₂`, the sealed `g₀`-retagged Lie-summand
difference equals the difference of the two metrics' `g₀`-retagged symmetrised covariant lowerings of
the DeTurck vector field. -/
theorem lieDerivRetagG0_sub_eq_symLoweredRetagG0_sub
    (g₀ g_bg g₁ g₂ : SmoothRiemannianMetric I M) :
    lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ =
      symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
        - symLoweredDeTurckVFRetagG0 (I := I) g₀ g₂ g_bg := by
  rw [lieDerivRetagG0_eq_symLoweredRetagG0 (I := I) g₀ g₁ g_bg,
    lieDerivRetagG0_eq_symLoweredRetagG0 (I := I) g₀ g₂ g_bg]

/-- **(BRIDGE — the intrinsic INTEGRATED two-arm `L²` bound of the sealed Lie-summand difference.)**

The chart-free, Cartan-route discharge of the sealed Lie difference's integrated covariant two-arm
bound: the leaf-shaped integrated `L²` bound of the `g₀`-retagged Lie-summand difference
`diff := lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂`, with the **0-jet-inclusive** `w`-jet
difference arm `w := realizeSymmCcTensor g₀ (T₁ − T₂)` and the fixed-pair `(1/4)`-cross arm.

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a
uniform `H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative constant
`Cd` (uniform over the gradient order `j` and the perturbation family) such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics
`g₁, g₂` of `T₁, T₂`,
```
‖∇^j diff‖² ≤ Cd · ∑_{i ≤ j+2} ‖∇^i w‖²
            + (1/4) · (∑_{i ≤ j+2} (‖∇^i T₁‖² + ‖∇^i T₂‖²)) · ‖(T₁ − T₂).toHs a‖².
```

**Derivation.**  Rewrite the sealed Lie difference into the symmetrised-lowered DeTurck-field
difference by the section-level Cartan telescope `lieDerivRetagG0_sub_eq_symLoweredRetagG0_sub` (P1a
applied to each metric), then apply the deep gauge integrated two-arm bound
`symLoweredDeTurckVF_iteratedCovGrad_topRest_split` (P1b).  The genuine deep covariant-gauge content
lives in P1b; P1a is the axiom-clean Cartan re-expression and the bridge is the honest composition.

**Why INTEGRATED.**  The pointwise per-`x` top/rest form is false for the middle covariant-Leibniz
terms at high frequency (Gagliardo–Nirenberg interpolation content); the honest bound is at the
integrated `L²`-norm-squared level, the form the single integration consumer reads.  Inherited from
P1b.

**Non-vacuity.**  Inherited from P1b (the difference arm carries the high derivative `‖∇^{j+2} w‖²` and
the order-`0` value jet, the cross arm both fixed-pair endpoints).  At `g₁ = g₂` the difference
vanishes and the bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, NO Weyl dependence. -/
theorem lieDerivDiff_intrinsic_covFdB_section_expansion (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ (j : ℕ),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (lieDerivRetagG0 (I := I) g₀ g_bg g₁
                    - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hsplit⟩ :=
    symLoweredDeTurckVF_iteratedCovGrad_topRest_split (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨Cd, hCd0, fun T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j => ?_⟩
  -- Rewrite the sealed Lie difference into the symmetrised-lowered DeTurck-field difference (P1a
  -- applied to each metric), then apply the deep gauge integrated two-arm bound P1b.
  rw [lieDerivRetagG0_sub_eq_symLoweredRetagG0_sub (I := I) g₀ g_bg g₁ g₂]
  exact hsplit T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
