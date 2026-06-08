import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge

/-! # The curvature-trace covariant-jet reduction of the sealed Ricci–DeTurck curvature difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **curvature-trace covariant-jet reduction** beneath the
curvature difference-arm Core-II covariant-jet leaf of the Ricci–DeTurck right-hand-side expansion
(`SegmentMetricRHSCovJetExpansion.lean`).

The sealed curvature nonlinearity `-2 • Ric(g)` is the trace of the Levi-Civita curvature operator
(`RicciConnection.lean`).  Its segment difference normalises (at order zero,
`SegmentMetricCurvatureDifferenceOpDecomposition.lean`) into the concrete linear-in-difference section
`linearSection g₀ g₁ g₂`, whose fibre value is the model-basis trace of the linear (`∇₀ D`) order of
the per-metric Ricci difference (`D = connDiff gₖ g₀` the connection difference,
`ricciNeg2SectionDiffLinearEval`).  By the connection-difference cocycle
`connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` the linear part carries the single difference factor
`connDiff g₁ g₂`, whose metrically-lowered Koszul form is the realized covariant derivative
`covDerivRealizeEval g₀ (T₁ − T₂)` of the perturbation difference
(`connDiffDiff_g0_lowered_koszul_diffFactor`) — i.e. the connection-level first covariant gradient
`R := covGrad g₀ 0 2 w` of the realized difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`.

The genuine covariant-Faà-di-Bruno content beneath the difference-arm leaf is the **curvature-trace
covariant-Leibniz reduction**: the rank-`2` order-`j` covariant jet of `linearSection` is dominated by
the rank-`3` order-`≤ j + 1` covariant jets of the connection-level realized covariant gradient `R`
(the trace, the cocycle, and the metric-built `≤2`-jet coefficient folded into a family-uniform
constant `Cd`).  This is the connection-difference covariant-jet machinery of
`ConnectionDifferenceFieldJets.lean` (`koszulCombSection_iteratedCovGrad_rfns_le`,
`loweredConnDiffSection`) lifted through the curvature trace and the two-metric cocycle; that lift — the
curvature-trace covariant-Leibniz reduction of the difference-normal-form section to the connection
level — is genuinely absent on disk for the *difference* curvature (the connection-level file is
single-metric, rank-`3`).  Per the project's assume-and-recurse discipline, the reduction
`ricciLinearSection_covGrad_traceReduction_rfns_le` posits exactly this genuinely-missing covariant-FdB
content as the honest atomic boundary just below the leaf.

The reduction is **structurally distinct** from, and **strictly smaller** than, the consumer leaf: its
right-hand side is the **connection-level** `∇^{≤ j+1} R` jet sum (rank `3`, the `∇w`-level), not the
leaf's `∇^{≤ j+2} w` jet sum; the difference-arm leaf is then proved by composing this reduction with
the **sorry-free** rank-shift `rfns(∇^p R) = rfns(∇^{p+1} w)` (the front-commutation
`iteratedCovGrad_covGrad_comm_heq`, `R = covGrad g₀ 0 2 w`) and the window inclusion
`∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)`.  The reduction is **non-vacuous** (it carries
the connection-level high derivative `∇^{j+1} R`, so a zero constant falsifies it whenever the linear
part is genuinely present — `linearSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and
carries no value-bounded `Φ.op 0 2 w` shape (the refuted structural split), NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, and NO Weyl dependence. -/

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
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **(POSIT — the connection-level curvature-trace covariant-jet two-arm reduction.)**  The genuine
deep curvature-trace covariant-Leibniz content beneath the difference-arm curvature leaf: the intrinsic
squared fibre norm of the order-`j` covariant gradient of the concrete linear-in-difference curvature
section `linearSection g₀ g₁ g₂` (a rank-`2` section) is dominated by the **Hamilton/Moser two-arm sum**
whose difference arm is the **connection-level** (rank-`3`) order-`≤ j+1` covariant jet sum of the
once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)`, plus the same fixed-pair cross piece carrying the endpoint jets against the difference's
order-`a` chart-Sobolev `C⁰` mass — with a nonnegative constant `Cd` **uniform** over the supercritical
`H^{a+2}`-bounded perturbation family:
```
rfns(∇^j linearSection)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                           + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the curvature-trace covariant-Leibniz reduction of the difference-normal-form `(0,2)`-section
`linearSection` to the **connection level** (rank-`3`), the genuinely-missing covariant-Faà-di-Bruno
content for the *difference* curvature (the connection-difference covariant-jet machinery of
`ConnectionDifferenceFieldJets.lean` is single-metric, rank-`3`; this is its lift through the curvature
trace and the two-metric cocycle).  `linearSection`'s fibre value is the `−2` model-basis Ricci trace of
the antisymmetrised `∇₀`-of-connection-difference summand difference
(`ricciNeg2SectionDiffLinearEval`, `SegmentMetricCurvatureDifferenceOpDecomposition.lean`); its
`g₀`-lowered Koszul form (`connDiffDiff_g0_lowered_koszul_diffFactor`) is the clean realized
covariant-derivative combination `covDerivRealizeEval g₀ (T₁ − T₂)` — the three slot readings of
`R = ∇₀ w` (the difference arm) — **minus** the nonlinear fixed-pair cross correction
`2(h₁ ⌟ connDiff g₁ g₀ − h₂ ⌟ connDiff g₂ g₀)` (`h_k = ccTensorBilinSymm g₀ T_k`), which does **not**
cancel pointwise and rides on the **fixed pair** `T₁, T₂` (the cross arm).  The model-basis Ricci trace
is a parallel rank-reducing `(0,3) → (0,2)` contraction (`ParallelRankReducingContraction`), and the
order-`j` jet of the trace folds the metric-built `≤ 2`-jet trace coefficient into `Cd` over the window
`j + 1` (one extra `∇₀` from the `∇₀ D` linear summand shifts the rank-`3` window to `j + 1`).

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries the connection-level high
derivative `∇^{j+1} R` (a zero `Cd` falsifies it whenever the linear part is genuinely present, since
`linearSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and the cross arm carries **both**
fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so `T₁ = T₂` realized) the linear section vanishes and the
bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep curvature-trace
covariant-Leibniz reduction to the connection level. -/
theorem ricciLinearSection_covGrad_traceReductionConn_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT — the curvature-trace covariant-jet two-arm bound of the linear difference section.)**
The intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete
linear-in-difference curvature section `linearSection g₀ g₁ g₂` is dominated by the **Hamilton/Moser
two-arm sum** — a difference-arm piece carrying the single high derivative on the difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, plus a fixed-pair cross piece carrying the
endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass — with a nonnegative constant
`Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j linearSection)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x)
                           + (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖².
```

This is the **corrected** (two-arm) curvature-trace content of the linear difference section.  The
order-zero linear/quadratic split (`linearSection` / `crossSection`) does **not** coincide with the
analytic difference-arm/fixed-pair-cross split: `linearSection`'s `g₀`-lowered Koszul form
(`connDiff_diff_koszul_realize_diffFactor`) is the clean realized covariant-derivative combination
`covDerivRealizeEval g₀ (T₁ − T₂)` (the difference arm, carrying the single difference factor `w`)
**minus** a nonlinear quadratic correction `2(h₁ ⌟ connDiff g₁ g₀ − h₂ ⌟ connDiff g₂ g₀)`
(`h_k = ccTensorBilinSymm g₀ T_k`), which does **not** cancel pointwise and rides on the **fixed pair**
`T₁, T₂` — exactly a fixed-pair-high × diff-low cross term.  So the linear section genuinely carries
**both** arms.  The difference arm is the realized-jet domination of the clean combination
(`koszulCombSection_iteratedCovGrad_rfns_le`, the realization gains no derivatives) summed over the
curvature trace; the cross arm is the fibre-small-gated cross-correction jet bound
(`crossCorrectionSection_iteratedCovGrad_rfns_le`) of the two `crossCorrectionSection g_k g₀ T_k` terms,
the top coefficient jet kept on the fixed pair against the difference's `C⁰` mass via the supercritical
Sobolev embedding (`ha`).  The metric-built `≤2`-jet curvature-trace coefficient is folded into the
family-uniform `Cd` over the window `j + 2`.

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries `∇^{j+2}w` (a zero `Cd`
falsifies it whenever the linear part is genuinely present, `linearSection_self_toModel`), and the cross
arm carries **both** fixed-pair endpoints.  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition.**  The two-arm bound is proved by composing the genuinely-deep **connection-level**
curvature-trace reduction `ricciLinearSection_covGrad_traceReductionConn_rfns_le` (below — its difference
arm is the *connection-level* `∑_{p ≤ j+1} rfns(∇^p R)` jet sum at rank `3`, `R := covGrad g₀ 0 2 w` the
once-differentiated realized difference factor) with the **sorry-free** rank-shift
`rfns(∇^p R) = rfns(∇^{p+1} w)` (the front/back commutation `iteratedCovGrad_covGrad_comm_heq`, since
`R = covGrad g₀ 0 2 w`) and the window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)`
(`Finset.sum_range_succ'`, the dropped `∇^0 w` term being nonnegative).  The cross arm is carried in
target form by the connection-level reduction unchanged.  This is precisely the composition the curvature
difference-arm leaf is documented to use; the only remaining genuine content is the connection-level
reduction itself. -/
theorem ricciLinearSection_covGrad_traceReduction_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hCd⟩ :=
    ricciLinearSection_covGrad_traceReductionConn_rfns_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j
  refine ⟨Cd, hCd0, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- The connection-level reduction, with `R := covGrad g₀ 0 2 (realizeSymm (T₁ − T₂))`.
  have hconn := hCd T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2 w with hR
  -- Rank-shift: the order-`p` jet of `R = ∇₀ w` is the order-`(p+1)` jet of `w` (front/back commutation).
  have hRshift : ∀ p : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x) := by
    intro p
    rw [hR]
    exact DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
      (by omega : (3 : ℕ) + p = 2 + (p + 1))
      (DifferentialGeometry.PDE.DeTurck.iteratedCovGrad_covGrad_comm_heq_local
        (I := I) (M := M) g₀ 2 p w) x
  -- The connection-level difference-arm sum, rewritten termwise into the `w`-jet sum.
  have hsumR : (∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x)) =
      ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x) :=
    Finset.sum_congr rfl fun p _ => hRshift p
  -- Window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)` (drop the nonneg `∇^0 w`).
  have hwindow : (∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x)) ≤
      ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [Finset.sum_range_succ' (n := j + 1 + 1)
      (f := fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x))]
    exact le_add_of_nonneg_right (riemannianFiberNormSq_nonneg _ _ _ _ _)
  -- The connection-level difference arm dominates the target `w`-jet difference arm.
  have hCdnn_term : (0 : ℝ) ≤ Cd := hCd0
  have harm : Cd * ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) ≤
      Cd * ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [hsumR]
    exact mul_le_mul_of_nonneg_left hwindow hCdnn_term
  -- Compose: connection-level reduction, then arm domination; the cross arm is unchanged.
  refine le_trans hconn ?_
  linarith [harm]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
