import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceQuadraticTraceProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParallelRankReducingContractionGrid

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

/-- **The connection-level rank-`3` Koszul triple of the realized difference factor.**  The clean
permuted-`covGrad` combination `R + permute (swap 0 1) R − permute c[0,2,1] R` on the once-differentiated
realized difference factor `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))`, i.e. the three slot
readings of `covDerivRealizeEval g₀ (T₁ − T₂)` (the difference-arm building block of the `g₀`-lowered
Koszul connection-difference combination, `loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`).
A `(0, 3)`-section, the input of the model-basis Ricci trace's difference arm. -/
private def koszulTripleDiff (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 3 :=
  Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))
    + DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))
    - DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1]
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))

/-- **The connection-level rank-`3` cross-correction difference.**  The fixed-pair cross piece
`2·crossCorrectionSection g₁ g₀ T₁ − 2·crossCorrectionSection g₂ g₀ T₂` of the `g₀`-lowered Koszul
connection-difference combination (`loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`),
the nonlinear correction that rides on the fixed pair `T₁, T₂` and does not cancel pointwise. A
`(0, 3)`-section, the input of the model-basis Ricci trace's cross arm. -/
private def crossCorrTripleDiff (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 3 :=
  (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
    - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂

/-- **(POSIT — the curvature-trace section identity: `linearSection` as a parallel model-basis Ricci
trace of the connection-difference Koszul combination.)**  The genuinely-missing section-level identity
lifting the pointwise lowered-Koszul form (`connDiffDiff_g0_lowered_koszul_diffFactor`) through the
model-basis Ricci trace: there is a **parallel rank-reducing `(0, 3) → (0, 2)` contraction** `Φ` (the
`−2` model-basis Ricci trace `g^{ij}·`, parallel because `∇₀ g₀⁻¹ = 0`, value-local because it reads
only the fibre), **fibrewise `ℝ`-linear** (so it distributes over the section difference), with the
linear-in-difference curvature section `linearSection g₀ g₁ g₂` equal to the trace of the connection-
difference Koszul **difference arm** minus the trace of the **cross arm**:
```
linearSection g₀ g₁ g₂ = Φ.op 0 (koszulTripleDiff) − Φ.op 0 (crossCorrTripleDiff),
```
where `koszulTripleDiff = R + permute (swap 0 1) R − permute c[0,2,1] R`,
`R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))`, and
`crossCorrTripleDiff = 2·crossCorrectionSection g₁ g₀ T₁ − 2·crossCorrectionSection g₂ g₀ T₂`.

`linearSection`'s fibre value is the `−2` model-basis Ricci trace of the antisymmetrised
`∇₀`-of-connection-difference summand difference (`ricciNeg2SectionDiffLinearEval`); by the
two-metric cocycle and the M1/M2 lowered-Koszul form (`connDiffDiff_g0_lowered_koszul_diffFactor`) its
`g₀`-lowered Koszul value is the `covDerivRealizeEval g₀ (T₁ − T₂)` combination (the difference arm)
minus the cross-correction value (the cross arm), and child A
(`loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`) packages exactly this as the
`(0, 3)`-section equality `2·lowered g₁ − 2·lowered g₂ = koszulTripleDiff − crossCorrTripleDiff`.  This
node posits the genuinely-missing piece: that the rank-`2` `linearSection` is the model-basis Ricci
trace `op 0` of that rank-`3` difference, as a **linear** parallel rank-reducing contraction.

The contraction `Φ` is the `−2` model-basis Ricci trace, depending **only on the background `g₀`**
(`g₀^{ij}·`); the section identity holds for **every** realizing pair `g₁, g₂` of perturbations
`T₁, T₂` over `g₀`.

**Non-vacuity.**  `Φ` is a *genuine* parallel contraction (its `kappa` envelope rejects the degenerate
zero witness whenever `op a R ≠ 0`); `linearSection` genuinely vanishes only at `g₁ = g₂`
(`linearSection_self_toModel`).  Its body is `sorry`: the genuine curvature-trace covariant section
identity (the parallel model-basis Ricci-trace `(0, 3) → (0, 2)` contraction and the lift of the
pointwise lowered-Koszul form to the section trace). -/
theorem exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Φ : Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 3 2,
      (∀ (a : ℕ) (A B : Integral.L2.SmoothCcTensor g₀ 0 (3 + a)),
          Φ.op a (A - B) = Φ.op a A - Φ.op a B) ∧
        ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
          (g₁ g₂ : SmoothRiemannianMetric I M),
          (∀ (x : M) (v w : TangentSpace I x),
            g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
          (∀ (x : M) (v w : TangentSpace I x),
            g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
          linearSection (I := I) g₀ g₁ g₂ =
            Φ.op 0 (koszulTripleDiff (I := I) g₀ T₁ T₂)
              - Φ.op 0 (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂) :=
  sorry

/-- **(POSIT — the post-trace connection-level cross-correction-difference covariant-jet bound,
`(1/8)`-cross arm.)**  For any parallel rank-reducing `(0, 3) → (0, 2)` contraction `Φ` (the model-basis
Ricci trace), the intrinsic squared fibre norm of the order-`j` covariant gradient of the **traced**
cross-correction difference `Φ.op 0 (crossCorrTripleDiff)` is dominated by the **connection-level**
Hamilton/Moser two-arm sum: a difference arm carried by the order-`≤ j+1` covariant jets of the
once-differentiated realized difference factor `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))`
(rank `3`), plus the fixed-pair cross piece carrying the endpoint jets against the difference's order-`a`
chart-Sobolev `C⁰` mass with the explicit coefficient `(1/8)`, uniformly over the supercritical
`H^{a+2}`-bounded fibre-small perturbation family:
```
rfns(∇^j (Φ.op 0 crossCorrTripleDiff))(x)
  ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
    + (1/8) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖².
```

This is the **connection-level** (rank-`3`, `∇w`-level) form of the cross-correction-difference bound:
it sits *strictly below* the consumer-level child
`crossCorrectionDiff_iteratedCovGrad_topRest_split` (whose difference arm is the `w`-jet sum
`∑_{i ≤ j+2} rfns(∇^i w)`, carrying the extra `∇^0 w` term), because the model-basis Ricci trace `Φ.op`
is value-local (its grid is the single-value `rfns(Φ.op 0 ·) ≤ kappa · rfns(·)`) and the
cross-correction-difference jet, *after* the trace, is controlled by the connection-level `R = ∇₀ w`
jets, not the `w` jets.  The `(1/8)` coefficient is the per-trace share so that the doubled cross arm
of the `linearSection` two-section split (the `2·rfns` subadditivity of
`riemannianFiberNormSq_sub_le`) re-collects to the target's `(1/4)` cross coefficient.

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries the connection-level high
derivative `∇^{j+1} R`, and the cross arm carries **both** fixed-pair endpoints `T₁, T₂`.  At
`T₁ = T₂` the cross-correction difference vanishes (`ccTensorBilinSymm g₀ 0 = 0`), so
`crossCorrTripleDiff = 0` and the bound is `0 ≤ 0`.  NO value-bounded operator shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the
genuine deep post-trace connection-level cross-correction-difference covariant-Leibniz content. -/
theorem parallelTrace_crossCorrTripleDiff_iteratedCovGrad_connLevel_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ)
    (Φ : Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 3 2) :
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
                  (Φ.op 0 (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂))).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 8 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

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
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  -- The model-basis Ricci trace `Φ` (parallel, rank-reducing `(0,3) → (0,2)`, fibrewise-linear) and
  -- the section identity `linearSection = Φ.op 0 (koszulTripleDiff) − Φ.op 0 (crossCorrTripleDiff)`.
  obtain ⟨Φ, hΦlin, hΦid⟩ :=
    exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple (I := I) g₀
  -- The post-trace connection-level cross-correction-difference jet bound (`(1/8)`-cross arm).
  obtain ⟨CdQ, hCdQ0, hCdQ⟩ :=
    parallelTrace_crossCorrTripleDiff_iteratedCovGrad_connLevel_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j Φ
  refine ⟨2 * Φ.kappa * 18 + 2 * CdQ, by have := Φ.kappa_nonneg; positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- Abbreviate `R := covGrad g₀ 0 2 w`, the difference-arm jet sum `SR`, and the cross arm `ST·P`.
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) with hR
  set SR := ∑ p ∈ Finset.range (j + 1 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) with hSR
  have hSRnn : 0 ≤ SR :=
    Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
  set ST := ∑ i ∈ Finset.range (j + 2 + 1),
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)) with hST
  have hSTnn : 0 ≤ ST :=
    Finset.sum_nonneg fun i _ =>
      add_nonneg (riemannianFiberNormSq_nonneg _ _ _ _ _) (riemannianFiberNormSq_nonneg _ _ _ _ _)
  set P := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 with hP
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  -- The trace identity, specialized to this realizing pair.
  have hid := hΦid T₁ T₂ g₁ g₂ hr1 hr2
  -- Split the squared fibre norm of `∇^j linearSection` over the trace difference identity.
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (Φ.op 0 (koszulTripleDiff (I := I) g₀ T₁ T₂))).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (Φ.op 0 (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂))).toSection x) := by
    rw [hid, PDE.RicciFlow.iteratedCovGrad_sub, Integral.L2.SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_sub, Pi.sub_apply]
    exact riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (2 + j) x _ _
  -- **Difference arm.**  The trace grid bounds `∇^j (Φ.op 0 koszulTripleDiff)` by `kappa · ∇^j koszul`.
  have htrace : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (Φ.op 0 (koszulTripleDiff (I := I) g₀ T₁ T₂))).toSection x) ≤
      Φ.kappa * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j
            (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) :=
    Φ.rfns_iteratedCovGrad_le j 0 (koszulTripleDiff (I := I) g₀ T₁ T₂) x
  -- The order-`j` jet of `koszulTripleDiff = R + perm₁ R − perm₂ R` is dominated by `18 · rfns(∇^j R)`,
  -- since the two slot permutations preserve the jet fibre norm (`permuteCcTensor`-invariance).
  set LR := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j R).toSection x) with hLR
  have hLRnn : 0 ≤ LR := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hP1eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j
        (DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x) = LR := by
    rw [hLR]
    exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
      (Equiv.swap (0 : Fin 3) 1) R j x
  have hP2eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j
        (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R)).toSection x) = LR := by
    rw [hLR]
    exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
      c[(0 : Fin 3), 2, 1] R j x
  have hkoszul : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j
            (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) ≤ 18 * LR := by
    rw [koszulTripleDiff, ← hR, PDE.RicciFlow.iteratedCovGrad_sub, PDE.RicciFlow.iteratedCovGrad_add,
      Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + j) x _ _) ?_
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + j) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j R).toSection x)
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j
        (DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x)
    rw [hP1eq] at hadd
    rw [hP2eq]
    nlinarith [hadd, hLRnn]
  -- `rfns(∇^j R) = LR` is the `p = j` term of `SR`, hence `LR ≤ SR` (the dropped terms are nonneg).
  have hLR_le_SR : LR ≤ SR := by
    rw [hLR, hSR]
    refine Finset.single_le_sum (f := fun p => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x))
      (fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _) ?_
    exact Finset.mem_range.mpr (by omega)
  -- The difference arm: `rfns(∇^j (Φ.op 0 koszul)) ≤ kappa · 18 · SR`.
  have hdiffarm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (Φ.op 0 (koszulTripleDiff (I := I) g₀ T₁ T₂))).toSection x) ≤
      Φ.kappa * 18 * SR := by
    refine le_trans htrace ?_
    have hk : (0 : ℝ) ≤ Φ.kappa := Φ.kappa_nonneg
    nlinarith [hkoszul, hLR_le_SR, hLRnn, hk, hSRnn]
  -- **Cross arm.**  The post-trace connection-level cross bound (`(1/8)`-cross arm).
  have hcrossarm := hCdQ T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  rw [← hR, ← hSR, ← hST, ← hP] at hcrossarm
  -- Re-collect: `2·(diff) + 2·(cross) ≤ (2·kappa·18 + 2·CdQ)·SR + (1/4)·ST·P`.
  refine le_trans hsplit ?_
  nlinarith [hdiffarm, hcrossarm, hSRnn, hSTnn, hPnn, Φ.kappa_nonneg, hCdQ0, mul_nonneg hSTnn hPnn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (Φ.op 0 (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂))).toSection x)]

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

/-! ### The curvature-trace covariant-jet reduction of the *quadratic* Cross section

The quadratic-half analogue of the linear difference-arm reduction above.  The Cross section
`crossSection g₀ g₁ g₂`'s fibre value is the `−2` model-basis trace of the quadratic
`connDiffField ∧ connDiffField` summand difference (`ricciNeg2SectionDiffCrossEval`,
`ricciDiffQuad_modelTrace_eq_crossEndoTrace`).  Differenced along the segment, the quadratic product of
two endomorphism fields `D_k = connDiffField g_k g₀` splits by the bilinear identity
`D₁ ∘ D₁ − D₂ ∘ D₂ = (D₁ − D₂) ∘ D₁ + D₂ ∘ (D₁ − D₂)`, and the connection-difference cocycle
`D₁ − D₂ = connDiffField g₁ g₂` carries the single difference factor, whose metrically-lowered Koszul
form is the realized covariant derivative `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)` (the connection-level once-differentiated realized difference factor — exactly as for the
linear half).  The rank-reducing curvature trace (`(0, 3) → (0, 2)`) then folds the metric-built
`≤ 2`-jet trace coefficient and the *fixed* factor `D₁`, resp. `D₂`, sup into a family-uniform constant
`Cd` over the connection-level window `j + 1`. -/

/-- **(POSIT — the connection-level curvature-trace covariant-jet two-arm reduction of the quadratic
Cross section.)**  The genuine deep curvature-trace covariant-Leibniz content beneath the quadratic Cross
leaf: the intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete
quadratic-in-difference curvature Cross section `crossSection g₀ g₁ g₂` (a rank-`2` section) is dominated
by the **Hamilton/Moser two-arm sum** whose difference arm is the **connection-level** (rank-`3`)
order-`≤ j+1` covariant jet sum of the once-differentiated realized difference factor `R := covGrad g₀
0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus the same fixed-pair cross piece carrying the
endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass — with a nonnegative constant
`Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j crossSection)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                          + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the curvature-trace covariant-Leibniz reduction of the quadratic Cross `(0, 2)`-section to the
**connection level** (rank-`3`), structurally distinct from and strictly smaller than the consumer leaf:
its difference-arm right-hand side is the **connection-level** `∑_{p ≤ j+1} rfns(∇^p R)` jet sum (rank
`3`, the `∇w`-level), not the leaf's `∇^{≤ j+2} w` jet sum.  `crossSection`'s fibre value is the `−2`
model-basis trace of the quadratic `connDiffField ∧ connDiffField` summand difference (the genuine
second-order remainder, vanishing to second order in the difference, `crossSection_self_toModel`).  The
quadratic difference `D₁ ∘ D₁ − D₂ ∘ D₂ = (D₁ − D₂) ∘ D₁ + D₂ ∘ (D₁ − D₂)` puts the single high
derivative on the difference factor `D₁ − D₂ = connDiffField g₁ g₂` (the cocycle), whose `g₀`-lowered
Koszul form is `R = ∇₀ w` (the difference arm), while the *fixed* factor `D₁` / `D₂` and the metric-built
`≤ 2`-jet trace coefficient fold into the family-uniform `Cd` (the bilinear two-section covariant-Leibniz
grid `RfnsBilinearProduct` keeps the top coefficient jet of the fixed factor on the fixed pair `T₁, T₂`
against the difference's `C⁰` mass, which the supercritical Sobolev embedding `ha` bounds).

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries the connection-level high
derivative `∇^{j+1} R` (a zero `Cd` falsifies it whenever the Cross part is genuinely present, since
`crossSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and the cross arm carries **both**
fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so `T₁ = T₂` realized) the Cross section vanishes and the
bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep curvature-trace
covariant-Leibniz reduction of the quadratic Cross to the connection level. -/
theorem ricciCrossSection_covGrad_traceReductionConn_rfns_le
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
                  (crossSection (I := I) g₀ g₁ g₂)).toSection x) ≤
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

/-- **(POSIT-DERIVED — the curvature-trace covariant-jet two-arm bound of the quadratic Cross section.)**
The intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete
quadratic-in-difference curvature Cross section `crossSection g₀ g₁ g₂` is dominated by the
**Hamilton/Moser two-arm sum** — a difference-arm piece carrying the single high derivative on the
difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, plus a fixed-pair cross piece
carrying the endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass — with a
nonnegative constant `Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j crossSection)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x)
                          + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the **corrected** (two-arm) curvature-trace content of the quadratic Cross section.  The Cross
section is the genuine quadratic remainder (`crossSection_self_toModel`); its differenced operator-trace
fibre value (`D₁ ∘ D₁ − D₂ ∘ D₂`, `D_k = connDiffField g_k g₀`) carries **both** a diff-high × fixed-low
arm and a fixed-high × diff-low arm (the connection-difference bilinear product of two independently
varying endomorphism fields), arising from the parallel two-section bilinear product `RfnsBilinearProduct`
grid where the high derivative may land on either factor.  The difference arm carries the single high
derivative on the difference factor `w`; the cross arm keeps the top coefficient jet on the fixed pair.

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries `∇^{j+2}w` (a zero `Cd`
falsifies it whenever the Cross part is genuinely present, `crossSection_self_toModel`), and the cross arm
carries **both** fixed-pair endpoints.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition.**  The two-arm bound is proved by composing the genuinely-deep **connection-level**
curvature-trace reduction `ricciCrossSection_covGrad_traceReductionConn_rfns_le` (whose difference arm is
the *connection-level* `∑_{p ≤ j+1} rfns(∇^p R)` jet sum at rank `3`, `R := covGrad g₀ 0 2 w` the
once-differentiated realized difference factor) with the **sorry-free** rank-shift
`rfns(∇^p R) = rfns(∇^{p+1} w)` (the front/back commutation `iteratedCovGrad_covGrad_comm_heq_local`,
since `R = covGrad g₀ 0 2 w`) and the window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2}
rfns(∇^i w)` (`Finset.sum_range_succ'`, the dropped `∇^0 w` term being nonnegative).  The cross arm is
carried in target form by the connection-level reduction unchanged.  This is exactly the composition the
linear difference-arm half (`ricciLinearSection_covGrad_traceReduction_rfns_le`) uses; the only remaining
genuine content is the connection-level quadratic-Cross reduction itself. -/
theorem ricciCrossSection_covGrad_traceReduction_rfns_le
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
                  (crossSection (I := I) g₀ g₁ g₂)).toSection x) ≤
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
    ricciCrossSection_covGrad_traceReductionConn_rfns_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j
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
  have harm : Cd * ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) ≤
      Cd * ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [hsumR]
    exact mul_le_mul_of_nonneg_left hwindow hCd0
  -- Compose: connection-level reduction, then arm domination; the cross arm is unchanged.
  refine le_trans hconn ?_
  linarith [harm]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
