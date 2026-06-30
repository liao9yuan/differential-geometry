# GoodCoveringItem3.lean — `lbl383` item 3 net-level wiring (B5)

Verification passed, sorry-free (2026-06-13). The B5 layer-bridge from the Step A net
(over `PointedRiemannianManifold`s) to the unconditional exp ball diffeomorphism
(`ExpBallDiffeo.exists_expBall_diffeo_of_lt`, item 3a).

## What's here

- **`PointedRiemannianManifold.exists_expBall_diffeo`** — the layer bridge: for a bundled
  pointed manifold `Y`, center `c`, radius `ρ ≤ expMapC2Radius Y.metric c` with
  `ofReal ρ < injRadius Y.metric c`, exp is a `C^1` partial diffeomorphism on `ball 0 ρ`.
  Installs `Y`'s stored instances (`Y.topology`…`Y.t2TangentBundle`) via `letI` (the
  `MetricComplete` pattern), then calls `exists_expBall_diffeo_of_lt`.
- **`Item3RadiusInput`** (honest-input) — the book's "`D` large enough" (`lbl391`/`lbl392`)
  scale choice: at each live net center the item-3 radius `ρ k α` is below the `C²`/inj
  radius of `(X.obj k).metric`. Inj part follows from `InjRadiusDecayInput.decay` (`D>1`);
  `C²` part is the §5/`lbl413` curvature-comparison boundary. `ProperMetricOn.realizes`
  identifies net `ms`-distances with the Riemannian ones across the layer.
- **`exists_seqItem3Diffeo`** — the net-level `lbl383` item 3: every live center
  `c ∈ seqCenter hd D P k α` carries the exp ball diffeomorphism, via the bridge.

## Status

Item 3 COMPLETE at the brick level: 3a = `exists_expBall_diffeo_of_lt` (unconditional);
3b = `ConvexBalls.isConvexWith_smallNormalBall` (modulo §5 honest-inputs); net wiring =
`exists_seqItem3Diffeo` (modulo the §5 radius honest-input; `ProperMetricOn` is now produced
by the intrinsic Hopf--Rinow adapter rather than a deferred black box). Optional follow-up:
fold `exists_seqItem3Diffeo` in as a field of the capstone `GoodCoveringSeq.exists_stableNetData`
(which intentionally omitted item 3) — a presentation choice; the math is done.

Targeted build of `GoodCoveringItem3` passed after the Hopf--Rinow proper-realization
replacement, confirming the new `properMetricOn` producer assumptions do not affect this
packaged-data consumer.

## Lean gotchas

- The `𝓘(ℝ, E)` model-with-corners notation needs `open scoped Manifold`; without it,
  `𝓘(Real, E)` is a parse error (`𝓘` read as a function applied to a pair).
- Bundle instances are `letI`'d from `Y`'s fields BOTH in the statement (so `injRadius`/
  `expMapC2Radius`/`PartialDiffeomorph` elaborate) and re-`letI`'d in the proof body.
- No ProperMetricOn-vs-manifold topology diamond bites here: the net center is just an
  element of `Y.M`; only `realizes` is needed to relate the radius scales (absorbed into
  the honest-input).
