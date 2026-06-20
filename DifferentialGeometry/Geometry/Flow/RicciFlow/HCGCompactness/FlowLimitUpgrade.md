# FlowLimitUpgrade.lean — P4 assembly skeleton (MSM135 Thm 3.10 upgrade)

Plan: `C:\Users\liao9\.claude\plans\fluffy-coalescing-leaf.md`.

## Landed + verified (2026-06-17, axiom-clean, build green 3789 jobs)

- `FlowLimitData X mc` — bundles the P4 frontier ingredients given the time-zero
  conclusion `mc : MetricCompactnessConclusion (X.atZero)`: `L` (Brick A, limit
  flow), `maps` (Brick B), `scalar` (Brick E), `hσsrc`/`hσtgt`/`refMetric`
  (Brick C inputs), `conv` (Brick D, the window norm-bridge output).
- `flowLimit_upgrade` — PROVES the upgrade arrow: assembles `FlowLimitData`
  through the already-built `SmoothCGHConverges.ofRestrictPullback` →
  `CompactnessConclusion X`. **Brick F's core (correctly feeding the keystone
  constructor) is DONE.**
- `smoothFlowLimitInput_of_flowLimitData` — produces the theorem-facing
  `SmoothFlowLimitInput X` (previously assumed at 4 sites, never produced) from a
  per-`mc` `FlowLimitData` builder.

So the P4 assembly is verified; the previously-opaque `upgrade` is now a proved
theorem modulo the explicit honest frontier fields.

## Remaining — discharge the `FlowLimitData` fields (the per-brick work)

- **Brick A** (`L`): the limit Ricci flow on `mc.limit.M` with metric `gInf`
  (Lemma 3.11 output) + `IsSolutionOn` (limit-is-a-solution — HARD).
- **Brick B** (`maps`): transport `mc.maps : PointedRiemannianCGMaps` (time-0) →
  `PointedCGHMaps` (time-independent diffeos; manifold-type identification
  `L.M = mc.limit.M`, `(X.term k).M = (X.atZero.obj k).M`).
- **Brick C** (`hσsrc`/`hσtgt`/`refMetric`): σ-compactness of the open
  source/target + a reference metric. Mechanical.
- **Brick D** (`conv`): apply `winGInfOfSol` to the pulled-back flows `Φ_k* g_k`,
  bridge the source-domain `derivNormSupOn` to Lemma 3.11's `metricDerivNormSupOn`
  on `M_∞`. The keystone bridge; consumes `hShi` (honest input).
- **Brick E** (`scalar`): `ScalarPullbackTendsto` from `C^∞` metric convergence.

## Design notes

- `FlowLimitData` is parameterized by `mc` because `maps`/`conv`/`refMetric` all
  reference the limit manifold + subseq from `mc`. The fields use the
  `letI : … := L.topology / sourceDomTop maps k` instance pattern mirroring
  `SourceDomainMetricData.ofRestrictPullback`.
- Per the approved plan (scope = "frontiers as inputs"), `hShi` and the Thm-3.9
  conclusion stay honest inputs (`mc` is the Thm-3.9 conclusion; `hShi` enters
  Brick D's `winGInfOfSol` application).
- The user chose to EXPAND `SmoothFlowLimitInput` (vs the producer route); the
  full expand+rewire of `SolutionCompactness.lean`'s structure + 4 consumers is
  Brick F-final. For now `smoothFlowLimitInput_of_flowLimitData` bridges to the
  existing structure without touching consumers.
