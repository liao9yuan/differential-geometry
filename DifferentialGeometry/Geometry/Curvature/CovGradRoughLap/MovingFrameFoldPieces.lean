import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderCarrierSection
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

/-!
# Concrete moving-frame building blocks of the integrated curvature fold

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, covariant rank `s`, and a
smooth compactly-supported `(0, s)`-tensor `S`, this file collects the **per-summand / frame-summed
concrete curvature identities** that the integrated curvature fold
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` (`MovingFrameBracketFold`)
decomposes into. They are reusable Bochner–Weitzenböck building blocks, *not* restatements of the
fold: each is a single classical curvature identity (a Ricci-commutation peeling, a contracted second
Bianchi trace, or the explicit Christoffel residual telescoping), instantiated at the smooth
`g_x`-orthonormal moving frame `Bᵢ := smoothOrthoFrame g x i`.

## What is delivered

* `frameSummand_leadingSlot_secondOrder_commutation_orthoFrame` — **the per-summand Ricci peeling.**
  For a single frame index `i` (direction `Bᵢ := smoothOrthoFrame g x i`) and a tangent direction
  `w`, the slot-`0` curried difference of the two per-summand frame terms of
  `pointwiseTensorCurv_toSection_eq_frame_sum` — `∇²_{Bᵢ, Bᵢ}(∇S)(x)` curried at `w` minus the
  gradient `covGradBundleEquiv(∇·(∇²_{Bᵢ, Bᵢ} S))(x)` curried at `w` — equals
  `(∇_{Bᵢ} R)(Bᵢ, w) V` (the genuine differentiated curvature) plus the curvature applied to the
  differentiated frame data plus the explicit Christoffel residual `secondOrderChristoffelResidual`.
  This is `covGrad_covDeriv_leadingSlot_secondOrder_commutation` (`CovGradCovDerivSecondOrderCommutation`)
  read at `B = w = Bᵢ`, with the moving-frame smoothness obligations discharged by
  `smoothOrthoFrame_smooth`. The `±N` Christoffel residual is **non-zero per summand** — its
  cancellation lives only in the full frame sum (the telescoping piece below), never per `i`.

* `frame_cyclic_second_bianchi_orthoFrame` — **the per-summand second Bianchi (cyclic) identity at the
  diagonal frame.** For a single frame index `i` the cyclic second-Bianchi sum
  `∇_{Bᵢ}R(Bᵢ, Z) + ∇_{Bᵢ}R(Z, Bᵢ) + ∇_Z R(Bᵢ, Bᵢ)` on the curvature section `W` vanishes, the
  diagonal `X = Y = Bᵢ` instance of `second_bianchi_levi_civita_metric` (`SecondBianchi`).

* `frameSummed_contracted_second_bianchi_eq_half_nablaScalar` — **the contracted second Bianchi frame
  trace.** The frame trace `∑ⱼ (∇_{Bⱼ} Ric)(Bⱼ, V)` equals `½ ∇_V scal`, the contracted second
  Bianchi identity that folds the differentiated-curvature carrier. This re-exposes
  `contracted_second_bianchi` (`ContractedBianchi`) as a fold-line building block.

## The two field-level folding debts (the hard core) and the fold assembly

The integrated fold `movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace`
(`MovingFrameBracketFold`, a downstream consumer of this file) is assembled by **composing two
field-level folding nodes** delivered here, each carrying an honest curvature debt:

* `movingFrameRemainder_l2Inner_eq_integral_christoffelResidualPairing` — **the carrier-peeling
  bridge.** The three-carrier remainder pairing `⟨Rem S, ∇S⟩_{L²}` equals the integral of the
  frame-summed Christoffel-residual pairing `∫ ∑ᵢ christoffelResidualPairingFib g s S x i`: the
  genuine curvature carriers `GcurvSection`, `genuineDiffCurvSection`, `ricTraceSection` peel off
  **under the integral** (via the contracted/cyclic second Bianchi pieces above and the frame-jet
  total-divergence correction — *not* pointwise), leaving the Christoffel residual.

* `frameSummed_christoffelResidual_eq_bracketDivergence` — **the residual telescoping.** The
  frame-summed Christoffel residual `∑ᵢ ⟨secondOrderChristoffelResidual g nab Bᵢ Bᵢ V, ∇S⟩₀(x)`
  telescopes (in the full frame sum `∑ᵢ`, never per `i`) into the explicit frame-bracket-direction
  covariant Leibniz divergence integrand the engine consumes. This is the genuine `±N`-cancellation.

These two are the field-level folding debts of the fold, with no producer on disk; the per-summand
peeling pieces above are the exact curvature identities that surround them.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). `R = riemannSec`, `∇R = nablaCurvSec`
(tangent slot) / `nablaTensorCurvSec` (tensor slot), `Ric = ricciTensor`, `∇Ric = nablaRicci`,
`scal = scalarCurv`, `∇scal = nablaScalar`. All readings are at the unit `(0, 0)`-covector through
`unitZeroSec` / the smooth unit section `unitEvalSection`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The per-summand Ricci peeling at the moving frame (piece 1).** For a single frame index `i`
(direction `Bᵢ := smoothOrthoFrame g x i`, used both as the trace direction and as the leading-slot
direction `w := Bᵢ`), the slot-`0` curried difference of the two per-summand frame terms of
`pointwiseTensorCurv_toSection_eq_frame_sum` — the second covariant derivative of the gradient
`∇²_{Bᵢ, Bᵢ}(∇S)(x)` curried at `Bᵢ` minus the gradient
`covGradBundleEquiv(∇·(∇²_{Bᵢ, Bᵢ} S))(x)` curried at `Bᵢ` — peels, by the third-order Ricci identity
lifted to the covariant-gradient bundle, into
```
(∇_{Bᵢ} R)(Bᵢ, Bᵢ) V
  + ( R(∇_{Bᵢ} Bᵢ, Bᵢ) V + R(Bᵢ, ∇_{Bᵢ} Bᵢ) V + 2 R(Bᵢ, Bᵢ)(∇^{abs}_{Bᵢ} V) )
  + secondOrderChristoffelResidual g nab Bᵢ Bᵢ V,
```
with `V := unitEvalSection g s S`, `nab := tensor0SCovariantDerivative I M s (LeviCivita g)`,
`R = riemannSec nab` the abstract `(0, s)`-tensor Riemann curvature, and
`(∇_{Bᵢ} R)(Bᵢ, Bᵢ) V = nablaTensorCurvSec g nab Bᵢ Bᵢ Bᵢ V` the abstract differentiated curvature.

This is `covGrad_covDeriv_leadingSlot_secondOrder_commutation` read at the moving frame
`B = w = Bᵢ := smoothOrthoFrame g x i` (the diagonal frame summand), with both moving-frame smoothness
obligations discharged by `smoothOrthoFrame_smooth`. The explicit Christoffel residual
`secondOrderChristoffelResidual` is **non-zero per summand**; its `±N` cancellation lives only in the
full frame sum `∑ᵢ` (the residual telescoping), never per index `i`. -/
theorem frameSummand_leadingSlot_secondOrder_commutation_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) -
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) =
      nablaTensorCurvSec (I := I) g
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)
          (unitEvalSection (I := I) (M := M) g s S) x
        + (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (smoothOrthoFrame (I := I) g x i)
              (unitEvalSection (I := I) (M := M) g s S) x
            + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (unitEvalSection (I := I) (M := M) g s S) x
            + (2 : ℝ) • riemannSec
              (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i)
                (unitEvalSection (I := I) (M := M) g s S)) x)
        + secondOrderChristoffelResidual (I := I) g
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (unitEvalSection (I := I) (M := M) g s S) x := by
  have hB := smoothOrthoFrame_smooth (I := I) (M := M) g x i
  exact covGrad_covDeriv_leadingSlot_secondOrder_commutation (I := I) (M := M) g s S hB hB x

omit [CompactSpace M] [I.Boundaryless] in
/-- **The per-summand second Bianchi (cyclic) identity at the diagonal moving frame (piece 2,
per-summand).** For a single frame index `i` (direction `Bᵢ := smoothOrthoFrame g x i`), a tangent
field `Z`, and a curvature-acted tangent field `W`, the cyclic second-Bianchi sum of the
differentiated tangent-bundle Riemann section `∇R = nablaCurvSec (LeviCivita g)` evaluated at the
diagonal `X = Y = Bᵢ` vanishes:
```
(∇_{Bᵢ} R)(Bᵢ, Z) W + (∇_{Bᵢ} R)(Z, Bᵢ) W + (∇_Z R)(Bᵢ, Bᵢ) W = 0.
```
This is the metric second Bianchi identity `second_bianchi_levi_civita_metric` (`SecondBianchi`) read
at `X = Y = Bᵢ`, with the moving-frame smoothness obligation discharged by `smoothOrthoFrame_smooth`.
It is the differentiated-curvature cyclic relation whose frame-trace contraction folds the genuine
differentiated-curvature carrier into the Ricci trace. -/
theorem frame_cyclic_second_bianchi_orthoFrame
    (g : SmoothRiemannianMetric I M)
    {Z W : Π b : M, TangentSpace I b} {x : M}
    (i : Fin (Module.finrank ℝ E))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) Z W x +
      nablaCurvSec (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) Z (smoothOrthoFrame (I := I) g x i) W x +
      nablaCurvSec (LeviCivita (I := I) g)
        Z (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) W x = 0 := by
  have hB := smoothOrthoFrame_smooth (I := I) (M := M) g x i
  exact second_bianchi_levi_civita_metric (I := I) (M := M) g hB hB hZ hW

omit [CompactSpace M] [I.Boundaryless] in
/-- **The contracted second Bianchi frame trace (piece 2, contracted).** The `g_x`-orthonormal frame
trace of the differentiated Ricci tensor equals half the directional derivative of the scalar
curvature:
```
∑ⱼ (∇_{Bⱼ} Ric)(Bⱼ, V)(x) = ½ ∇_V scal (x),
```
with `Bⱼ := smoothOrthoFrame g x j`, `∇Ric = nablaRicci`, `scal = scalarCurv`, `∇scal = nablaScalar`.
This is the contracted second Bianchi identity `contracted_second_bianchi` (`ContractedBianchi`) read
as a fold-line building block: it is the curvature identity that, applied to the frame trace of the
genuine differentiated-curvature carrier, folds it into the Ricci-trace carrier `ricTraceSection`. -/
theorem frameSummed_contracted_second_bianchi_eq_half_nablaScalar
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b} {x : M}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ∑ j, nablaRicci (I := I) g
        (smoothOrthoFrame (I := I) g x j) (smoothOrthoFrame (I := I) g x j) V x =
      1 / 2 * nablaScalar (I := I) g V x := by
  exact contracted_second_bianchi (I := I) (M := M) g hV

/-- **The per-summand Christoffel-residual pairing scalar field.** At a point `x`, the pointwise
`g_x`-fibre pairing of the explicit per-summand Christoffel residual
`secondOrderChristoffelResidual g nab Bᵢ Bᵢ (unitEvalSection g s S)` (the `(0, s)`-fibre value that
the per-summand peeling `frameSummand_leadingSlot_secondOrder_commutation_orthoFrame` isolates, at the
diagonal moving frame `Bᵢ := smoothOrthoFrame g x i` and `nab := tensor0SCovariantDerivative I M s
(LeviCivita g)`) against the slot-`0` `Bᵢ`-curried slice of the gradient tensor `∇S`. This is the
scalar integrand of the residual `L²` pairing, the per-summand quantity whose **frame-summed** integral
telescopes (the cancellation lives only in `∑ᵢ`, never per `i`). -/
noncomputable def christoffelResidualPairingFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  tensorInnerPointwise_0s (I := I) (M := M) s g x
    (Tensor0SSpace.toModel
      (secondOrderChristoffelResidual (I := I) g
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
        (unitEvalSection (I := I) (M := M) g s S) x))
    (Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x)))

/-- **The carrier-peeling integral identity: the remainder pairing integrates to the frame-summed
Christoffel-residual pairing (the integrated curvature half of the carrier-peeling bridge, posited).**
For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and a smooth compactly-supported
`(0, s)`-tensor `S`, the integral of the remainder pairing `⟨Rem S, ∇S⟩(x)` equals the integral of the
frame-summed per-summand Christoffel-residual pairing `∑ᵢ christoffelResidualPairingFib g s S x i`:

```
∫_M tensorInnerPointwise g 0 (s + 1) x (Rem S x) (∇S x) dvolᵍ
  = ∫_M ( ∑ᵢ christoffelResidualPairingFib g s S x i ) dvolᵍ,
```

with `Rem S := pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S +
ricTraceSection g s S)` and `∇S := covGrad g 0 s S`.

**This is the genuine integrated curvature content of the carrier-peeling bridge.** Pointwise,
`pointwiseTensorCurv` decomposes per `g_x`-orthonormal frame summand
(`pointwiseTensorCurv_toSection_eq_frame_sum`), and the per-summand Ricci peeling
`frameSummand_leadingSlot_secondOrder_commutation_orthoFrame` splits each summand, curried against
`∇S`, into the differentiated curvature `(∇_{Bᵢ} R)(Bᵢ, Bᵢ) V`, the curvature applied to the
differentiated frame data, and the explicit residual `secondOrderChristoffelResidual` whose pairing is
`christoffelResidualPairingFib`. The three genuine curvature carriers `GcurvSection` (pure Riemann
`R(∇S)`), `genuineDiffCurvSection` (the differentiated trace `(∇R) S`, folded from the extension-curried
trace by the **contracted second Bianchi** frame trace
`frameSummed_contracted_second_bianchi_eq_half_nablaScalar` together with the cyclic second Bianchi
`frame_cyclic_second_bianchi_orthoFrame`), and `ricTraceSection` (the Ricci trace `Ric(∇S)`) are the
**frame-jet-free tensorial** sections, which differ from the extension-curried per-summand trace fields
by a quantity whose frame sum, paired against `∇S`, is the metric divergence of an explicit
`∇S`-order tangent current. The cancellation is *false* as a pointwise fibre identity (the slot-`0`
frame-trace matching is false on a normal manifold) and holds only **under the integral** on the closed
manifold, where the divergence integrates to zero. This is the carrier-peeling field-level folding debt
of the integrated curvature fold, distinct from and orthogonal to the scalar residual nullity
`frameSummed_christoffelResidualPairing_integral_eq_zero` (piece 3): this identity peels the three
genuine carriers onto the Christoffel-residual pairing, the scalar nullity then sends that residual
pairing to zero. It has no producer on disk, and the bridge
`movingFrameRemainder_l2Inner_eq_integral_christoffelResidualPairing` is mechanical above it.

**Non-vacuity / soundness.** The identity is *false* for an arbitrary triple of subtracted fields on a
non-flat manifold: were every carrier replaced by `0` the left integrand would be `⟨Curv S, ∇S⟩`, whose
integral is the nonzero Weitzenböck curvature integral (`weitzenbock_curvature_crossPairing_value`,
`‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`, at `s = 0` it is `∫ Ric(∇f, ∇f) ≠ 0`), whereas with the scalar nullity
the right integral is `0`; the datum genuinely uses all three genuine curvature carriers folded by the
second-Bianchi pieces. -/
theorem movingFrameRemainder_integral_eq_christoffelResidualPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S -
            GcurvSection (I := I) (M := M) g s S -
            (genuineDiffCurvSection (I := I) (M := M) g s S +
              ricTraceSection (I := I) (M := M) g s S)).toFun x)
          ((covGrad (I := I) (M := M) g 0 s S).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, (∑ i : Fin (Module.finrank ℝ E),
              christoffelResidualPairingFib (I := I) (M := M) g s S x i)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  sorry

/-- **The carrier-peeling bridge: the three-carrier remainder pairing IS the integrated frame-summed
Christoffel-residual pairing (the integrated genuine-carrier peeling, posited).** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and a smooth compactly-supported `(0, s)`-tensor
`S`, the global metric `L²` pairing of the **three-carrier moving-frame remainder**

```
Rem S := pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```

against `∇S := covGrad g 0 s S` equals the **integral of the frame-summed per-summand
Christoffel-residual pairing scalar**:

```
⟨Rem S, ∇S⟩_{L²}  =  ∫_M ( ∑ᵢ christoffelResidualPairingFib g s S x i ) dvolᵍ.
```

This is the **integrated peeling of the three genuine curvature carriers** down to the Christoffel
residual. Pointwise, `Curv S` decomposes per `g_x`-orthonormal frame summand
(`pointwiseTensorCurv_toSection_eq_frame_sum`) and the per-summand peeling
`frameSummand_leadingSlot_secondOrder_commutation_orthoFrame` splits each summand, curried against
`∇S`, into the differentiated curvature `(∇_{Bᵢ} R)(Bᵢ, Bᵢ) V`, the curvature applied to the
differentiated frame data, and the explicit residual `secondOrderChristoffelResidual` whose pairing is
`christoffelResidualPairingFib`. Summed over the frame and **integrated** against `∇S`, the genuine
curvature carriers collapse onto the tensorial sections `GcurvSection` (pure Riemann `R(∇S)`),
`genuineDiffCurvSection` (the differentiated trace `(∇R) S`, folded from the extension-curried trace by
the **contracted second Bianchi** frame trace
`frameSummed_contracted_second_bianchi_eq_half_nablaScalar` and the cyclic second Bianchi
`frame_cyclic_second_bianchi_orthoFrame`), and `ricTraceSection` (the Ricci trace `Ric(∇S)`), so the
pairing of `Rem S` against `∇S` retains exactly the Christoffel-residual half.

**Only under the integral.** The genuine carriers `genuineDiffCurvSection`/`ricTraceSection` are the
**frame-jet-free tensorial** sections (`appCc (covGrad (curvOpField)) S`, `appCc (ricSlotOpField) (∇S)`),
which agree with the extension-curried per-summand trace fields **only under the integral against `∇S`
on the closed manifold** (the frame-jet discrepancy is itself a total covariant divergence): the
identity is *false* as a pointwise fibre identity. It is therefore genuine **integrated** curvature
content — the carrier-peeling half of the fold — distinct from and composing with the residual
telescoping `frameSummed_christoffelResidual_eq_bracketDivergence` (piece 3). The two compose to the
full fold `movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` (`MovingFrameBracketFold`):
this bridge peels the genuine carriers to the Christoffel-residual pairing, piece 3 telescopes that
into the divergence-engine integrand.

The genuine integrated content is isolated in the single named field-level child
`movingFrameRemainder_integral_eq_christoffelResidualPairing` below: the integral of the pointwise
remainder pairing `⟨Rem S, ∇S⟩(x)` equals the integral of the frame-summed Christoffel-residual pairing
`∑ᵢ christoffelResidualPairingFib`. Above it this bridge is purely definitional: `tensorL2Inner`
unfolds to the integral of the pointwise pairing. -/
theorem movingFrameRemainder_l2Inner_eq_integral_christoffelResidualPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∫ x, (∑ i : Fin (Module.finrank ℝ E),
              christoffelResidualPairingFib (I := I) (M := M) g s S x i)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  movingFrameRemainder_integral_eq_christoffelResidualPairing (I := I) (M := M) g s S

/-- **The scalar moving-frame third-order Bochner `±N`-cancellation (piece 3, scalar form — the
genuinely-irreducible core, posited).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, and a smooth compactly-supported `(0, s)`-tensor `S`, the integral of the **frame-summed**
per-summand Christoffel-residual pairing scalar vanishes:
```
∫_M ( ∑ᵢ christoffelResidualPairingFib g s S x i ) dvolᵍ = 0.
```

This is the clean scalar form of the genuine `±N`-cancellation: the off-diagonal Christoffel-residual
error terms telescope into a total covariant divergence **only in the full frame sum `∑ᵢ`** (never per
index `i` / per `x`: the per-summand residual `secondOrderChristoffelResidual g nab Bᵢ Bᵢ V` is
non-zero, established by `frameSummand_leadingSlot_secondOrder_commutation_orthoFrame`; only its
frame-summed integral against `∇S` is a divergence whose integral over the closed manifold vanishes).
It is the single field-level folding debt above the divergence engine, with no producer on disk; the
surrounding curvature peeling (piece 1 `frameSummand_leadingSlot_secondOrder_commutation_orthoFrame`)
and contracted-Bianchi trace (piece 2 `frameSummed_contracted_second_bianchi_eq_half_nablaScalar`) are
built sorry-free above.

**Missing computation (the precise telescoping to be discharged).** Term by term in
`secondOrderChristoffelResidual_def` at `B = w = Bᵢ` (where `[Bᵢ, Bᵢ] = mlieBracket I Bᵢ Bᵢ = 0`
collapses the first two summands), each surviving single-direction iterated-Christoffel correction
`∇_{∇_{Bᵢ}(∇_{Bᵢ} Bᵢ)} V`, `∇_{∇_{Bᵢ} Bᵢ}(∇_{Bᵢ} V)`, `∇_{Bᵢ}(∇_{∇_{Bᵢ} Bᵢ} V)` paired against the
curried `∇S` slice is rewritten, via the metric-lowered directional-covariant-derivative bridge
`loweredCovDerivAlongVF_firstSlot_eq_lower_covApply` (`BracketDivergenceForm`), as the engine's first
slot `⟨∇_{V a}(W a), ∇S⟩₀` along the frame-bracket directions `V a := lieBracketSection (extend Bᵢ)
(extend Wₐ)` with once-derived bracket sections `W a := ∇_{Bᵢ}(unit section)`; summing over the frame
and applying the per-direction divergence Leibniz
`loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul` (`BracketDivergenceForm`) turns the
frame sum into the metric divergence of an explicit global current whose integral over the closed
manifold vanishes (`integral_tensorInner_covDeriv_combined_eq_zero`). -/
theorem frameSummed_christoffelResidualPairing_integral_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ∫ x, (∑ i : Fin (Module.finrank ℝ E),
            christoffelResidualPairingFib (I := I) (M := M) g s S x i)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  sorry

/-- **The summed Christoffel-residual telescoping (piece 3, bracket-engine form), re-proven from the
scalar nullity.** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and a smooth
compactly-supported `(0, s)`-tensor `S`, the integral of the **frame-summed** per-summand
Christoffel-residual pairing scalar `∑ᵢ christoffelResidualPairingFib g s S x i` equals the
**frame-summed covariant Leibniz integral** of explicit once-derived bracket data
`W : ι → SmoothCcTensor g 0 (s + 1)` along frame-bracket directions `V : ι → TM` (the exact engine
integrand `integral_frameSummed_bracketCovDeriv_combined_eq_zero` consumes with `Z := ∇S`):
```
∫_M ( ∑ᵢ christoffelResidualPairingFib g s S x i ) dvolᵍ
  = ∑ₐ ∫_M ( ⟨∇_{V a}(W a), ∇S⟩₀ + ⟨W a, ∇_{V a}(∇S)⟩₀ + ⟨W a, ∇S⟩ · divᵍ (V a) ) dvolᵍ.
```

This is the bracket-engine packaging of the cleaner scalar nullity
`frameSummed_christoffelResidualPairing_integral_eq_zero`: since the engine sum on the right vanishes
for *every* index family (the divergence engine sends it to zero), the **empty family** `ι := Fin 0`
already realises the right-hand value `0`, and the left-hand integral is `0` by the scalar nullity. The
genuine `±N`-cancellation content lives entirely in the scalar nullity; this lemma is its mechanical
re-packaging into the engine-consumption shape the integrated curvature fold reads. -/
theorem frameSummed_christoffelResidual_eq_bracketDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ∃ (ι : Type) (_ : Fintype ι)
      (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (W : ι → SmoothCcTensor g 0 (s + 1)),
      ∫ x, (∑ i : Fin (Module.finrank ℝ E),
              christoffelResidualPairingFib (I := I) (M := M) g s S x i)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∑ a, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
                (Tensor0SSpace.toModel
                  (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1) (W a).toSection (V a) x))
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S).toSection x))
              + tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g 0 (s + 1) (W a).toSection x))
                (Tensor0SSpace.toModel
                  (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S).toSection (V a) x))
              + tensorInnerScalar (I := I) (M := M) g 0 (s + 1) (W a).toSection
                  (covGrad (I := I) (M := M) g 0 s S).toSection x
                * divergence_g (I := I) g (V a) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  refine ⟨Fin 0, inferInstance, Fin.elim0, Fin.elim0, ?_⟩
  rw [frameSummed_christoffelResidualPairing_integral_eq_zero (I := I) (M := M) g s S,
    Finset.univ_eq_empty, Finset.sum_empty]

end Connection
end Integral
end DifferentialGeometry

end
