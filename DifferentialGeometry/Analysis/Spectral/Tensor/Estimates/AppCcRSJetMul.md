# AppCcRSJetMul.lean — TK1, the all-order `appCcRS` product jet estimate

Status: **GREEN, zero `sorry`, all three declarations axiom-clean**
(`propext, Classical.choice, Quot.sound`), 2026-08-03.  Focused check clean
(no warnings); targeted module build of
`DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.AppCcRSJetMul` clean.
No `set_option maxHeartbeats` at all — the file needs none.

Brick: TK1 of the `topKer_jet` sequence (planner ruling No. 104,
`ShortTime/UNIF_EXISTENCE_PLAN3.md`).  Entry points:
`ShortTime/F6_ESTIMATE_RECON.md` §5.1f, `DeTurck/LowRegC2JetTower.md`.

## Headline: this was a stocked wall, again (instance thirteen)

The brick was scoped as "its own multi-session estimate brick, not an API gap".
It is neither.  **Every ingredient existed already, order-generic and
arity-generic**; TK1 is a ~200-line composition that adds no tensor calculus.

The three stocked pieces:

| piece | where | generic in |
|---|---|---|
| covariant Leibniz for `appCcRS` at order `i` | `iteratedCovGrad_appCcRS_eq`, `CovGrad/IteratedAppCcLeibniz.lean:90` | order + arity |
| pointwise diagonal product grid, arbitrary contravariant rank | `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`, `Sobolev/TensorHilbert/MetricArmCoeffJetTower.lean:2361` | order + arity |
| integrated Gagliardo–Nirenberg two-arm companion for that grid | `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`, `Sobolev/TensorHilbert/RemainderCoeffPerOrderJetEnvelopes.lean:862` | order + arity |
| sharp `C0` jet-sum Sobolev window | `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`, `Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717` | arity |

The decisive observation is about `appRS_h2_h2_h2`
(`Estimates/H1H2AppCcRS.lean:769`), the fixed-order-two member TK1 replaces:
**its proof is already order-generic.**  Its internal `hterm` is proved for an
arbitrary `i`; the `hi : i < 3` hypothesis is consumed only by
`Finset.range_mono` to shrink the per-cell jet window into the fixed one.  The
`Finset.range 3` in the *statement* is the only thing that is order-two.
Replacing the fixed window `range 3` by the running window `range (n+1)` is the
whole content of TK1.

So the lesson is the same one the campaign has now hit thirteen times: **grep the
order-generic layer, and read the fixed-order member's proof, before believing a
per-order claim.**  Here the fixed-order member's *proof* was the general theorem
in disguise.

## What is proved

Three declarations, `Analysis/Spectral/Tensor/Estimates/AppCcRSJetMul.lean`,
all in `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral`, all generic in the
valences `(p, r, c)` — i.e. `Φ : SmoothCcTensor g r c`, `W : SmoothCcTensor g p r`,
`appCcRS g p r c Φ W : SmoothCcTensor g p c`.  Write
`Sₙ X := ∑_{j ∈ range (n+1)} ‖iteratedCovGrad g _ _ j X‖²` (this is `lowJetSq g n X`
unfolded; `lowJetSq` itself is not importable at this layer — it is defined in the
downstream `DeTurckRemainderLowBaseAction.lean` — so the sums are spelled out, exactly
as `appRS_h2_h2_h2` does, and `simpa only [lowJetSq]` bridges at the call site).

### `appRS_hn_sup` (`:83`) — the engine, Moser pairing

```
∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ n Φ W A B, 0 ≤ A → 0 ≤ B →
  (∀ x, rfns g r c x (Φ x) ≤ A²) → (∀ x, rfns g p r x (W x) ≤ B²) →
    Sₙ (appCcRS g p r c Φ W) ≤ C n * (B² * Sₙ Φ + A² * Sₙ W)
```

`C n := ∑_{j ≤ n} appCcGdiag j * G j`, with `appCcGdiag j = (2(finrank+1))^j` the
Leibniz grid weight and `G j` the GN two-arm constant.  Exponential in `n`; no
`n`-uniformity is claimed, and none is needed (`Kk i` in `topKer_jet` is
`i`-dependent).

Properties worth keeping: **no dimension hypothesis, no order gate, and sharp in
the jet order** — order `n` on the right for order `n` on the left, no Sobolev
loss.  Each arm's `L∞` bound multiplies the *other* arm's full `L²` jet.  This is
literally the Moser/GN pairing the planner ratified for the ball-free route
("a monomial `∇^{j₁}T ⋯ ∇^{jₚ}T` is `L²`-controlled by `‖T‖_{L^∞}^{p−1}‖∇ⁱT‖_{L²}`").

### `appCcRS_jet_mul` (`:196`) — the product form asked for

```
∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ n, finrank ℝ E / 2 + 1 ≤ n → ∀ Φ W,
  Sₙ (appCcRS g p r c Φ W) ≤ C n * Sₙ Φ * Sₙ W
```

i.e. the covariant `H^n` jet is an algebra for the operator-field action.  This
is the general-`i` replacement for the private fixed-order `app_h2_mul`
(`DeTurckRemainderLowBaseAction.lean:3233`), which is its `n = 2` case in dim 3.

### `appRS_hn_hn_hn` (`:266`) — envelope form, dim 3

The family's `(A, B)` envelope shape, `2 ≤ n`:
`Sₙ Φ ≤ A² → Sₙ W ≤ B² → Sₙ (appCcRS g p r c Φ W) ≤ (C n * A * B)²`.
At `n = 2` this *is* `appRS_h2_h2_h2`.

## The gate is mathematically necessary — do not try to remove it

`appCcRS_jet_mul` carries `finrank ℝ E / 2 + 1 ≤ n` (dim 3: `2 ≤ n`).  This is
**not** a technical artifact of the route and no amount of cleverness removes it:
at `n = 0` the claim reads `‖ΦW‖²_{L²} ≤ C ‖Φ‖²_{L²}‖W‖²_{L²}`, which is false
(concentrate a bump: `‖f²‖_{L²} = ‖f‖²_{L⁴}` is unbounded on the `L²` unit
sphere).  `H¹` in dim 3 is not an algebra either, so `n = 1` fails too.  The gate
is exactly the Sobolev supercriticality threshold at which
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical` starts to
convert the jet sum into a pointwise fibre bound; its window is
`range (finrank ℝ E / 2 + 2)`, and the gate is precisely
`range (finrank ℝ E / 2 + 2) ⊆ range (n + 1)`.

**Consequence for TK3, worth flagging now.**  If TK3 needs the product form at
`i ∈ {0, 1}` it must either route through `appRS_hn_sup` (gate-free, but then it
must supply an `L∞` bound for one arm — which for the `T` arm is free, since
`hδg : gFibreOpBound g (ccTensorBilinSymm g T) δ` with `δ ≤ 1/3` *is* that
bound), or accept `S₂` on the right at those two orders.  The engine is the right
door for the `topKer_jet` assembly: it is gate-free, it is sharp in the jet order,
and its `L∞` slot is exactly what `δ ≤ 1/3` delivers.  Going through
`appCcRS_jet_mul` instead would cost jet orders that `topKer_jet`'s
`∑_{j < i+2}‖∇ʲT‖²` budget does not have at `i = 0`.

## Arity coverage vs `topKernel_eq`

`topKernel_eq` (`DeTurckRemainderLowBaseAction.lean:3769`) splits into
`lieRefold2 + (Φmet(gm) − Φmet(g)) + (−2s)·ricciTop g gm T`, and
`ricciTop = appCcRS g 4 4 2 (daTrans g gm T) (dagTopOp g gm)`
(`…LowBaseAction.lean:3514`) — valences `(p, r, c) = (4, 4, 2)`.  All three
statements here are universally quantified over `(p, r, c)`, so coverage is
total: the ~20 distinct `appCcRS` arities appearing in `…LowBaseAction.lean`
(`0 2 2`, `2 2 2`, `2 3 3`, `2 3 4`, `2 4 2`, `2 4 4`, `3 3 3`, `4 4 2`,
`4 6 2`, `6 4 2`, `6 6 4`, …) are all instances.  Verified by probe at
`4 4 2` and `0 2 2`, with the gate discharged by `rw [hDim]` alone.

## Verified consumer shape

A scratch probe (not committed) confirms the `lowJetSq` drop-in is a one-liner
from `appCcRS_jet_mul`:

```
lowJetSq g n (appCcRS g p r c Φ W) ≤ C n * lowJetSq g n Φ * lowJetSq g n W
```
for `2 ≤ n` under `hDim : finrank ℝ E = 3`, closed by
`simpa only [lowJetSq] using hKle n hgate Φ W`.  So TK2/TK3 pay nothing to
translate into the F6 lane's vocabulary.

## Home

`Analysis/Spectral/Tensor/Estimates/` is the canonical home of the `appCc`/`appRS`
estimate family (`H1H2AppCcRS.lean` holds `appRS_h1_h2_h1`, `appRS_h2_h1_h1`,
`appRS_h2_h2_h2`; `AppCcSplitEnvelope.lean`, `AppCcLpProduct.lean`, `H2H3Principal.lean`,
… are siblings).  A **new file** importing `H1H2AppCcRS.lean` was used rather than
appending to it: `H1H2AppCcRS.lean` sits directly under the 13.8k-line
other-lane-claimed `DeTurckRemainderLowBaseAction.lean`, so editing it would stale
that lane's module for no benefit.  The new file inherits the entire needed import
set from `H1H2AppCcRS.lean` and needs no import of its own beyond it.

Not registered in the root `DifferentialGeometry.lean` umbrella — matching the
in-flight convention of the campaign's other new files in this directory
(`AppCcSplitEnvelope.lean` is likewise unregistered).

## Lean notes

* The preamble must mirror `H1H2AppCcRS.lean` exactly, including the three
  `private local instance`s (`CompleteSpace E`, `MeasurableSpace M := borel M`,
  `BorelSpace M`).  `riemannianVolumeMeasure` needs the measurable structure, and
  taking it from a different route risks an instance mismatch against
  `normSq_le_integral_of_pointwise_fiberNormSq_le_rs`.
* `set grid : M → ℝ := … with hgrid_def` then `simpa only [hgrid_def]` is what
  makes the grid opaque to the arithmetic while still matching the two producers'
  literal grid expression.  Both producers spell the grid identically
  (`∑_{m ≤ j} rfns(∇^m Φ) * ∑_{l ≤ j−m} rfns(∇^l W)`), which is why the
  composition needs no rewriting at all — this is the load-bearing coincidence
  and it is not accidental: the integrated companion was written against this grid.
* Argument order of the integrated companion is `g r₁ r₂ s₁ s₂ k`, so the call is
  `… g r p c r j` (S := `Φ : SmoothCcTensor g r c`, T := `W : SmoothCcTensor g p r`).
  Getting this backwards typechecks nowhere useful, so it fails loudly.
* `Finset.range_mono hjn` with `hjn : j + 1 ≤ n + 1` beats `by omega` inside the
  window-shrinking steps; for the Sobolev window,
  `hwin : finrank ℝ E / 2 + 2 ≤ n + 1` is discharged by `omega` from the gate
  (omega handles the literal `/ 2`).
* No `maxHeartbeats` bump was needed anywhere, including in the `positivity` and
  `ring` steps.  If a future edit makes one necessary, that is a signal the
  composition drifted, not that the file needs more budget.
