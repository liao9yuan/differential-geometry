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

## The `FlowLimitData` builder (2026-06-21, axiom-clean, build green 3789 jobs)

`cghMaps_of_hL0 X mc L hL0 : PointedCGHMaps X L mc.subseq` — the **Brick-A →
Brick-B handoff** and the last missing producer of the `maps` field. Given the
limit flow `L` with `hL0 : L.atTime 0 = mc.limit` (Brick A's output contract),
the time-zero comparison maps `mc.maps` transport along `hL0.symm` to
`PointedRiemannianCGMaps (X.atZero) (L.atTime 0) mc.subseq`, which
`pointedCGHMaps_of_atZero` (Brick B) carries to the spacetime maps. The `▸`
transport is over the `L`-index of `PointedRiemannianCGMaps`; it introduces **no
axiom** (`#print axioms cghMaps_of_hL0 = [propext, Classical.choice,
Quot.sound]`, no `sorryAx`).

**Design decision (item #3 of the work list).** No verbose re-typed
`flowLimitData_of_…` wrapper was added. With `cghMaps_of_hL0` in hand,
`FlowLimitData`'s **own anonymous constructor IS the builder** — the structure-
instance syntax infers the frontier field types from the supplied `maps`:

```lean
flowLimit_upgrade X mc
  { L := L
    maps := cghMaps_of_hL0 X mc L hL0   -- Brick A+B, the only non-frontier field
    scalar := …      -- Brick E (honest frontier input)
    hσsrc := …; hσtgt := …; refMetric := …   -- Brick C inputs
    conv := … }      -- Brick D (honest frontier input, consumes hShi)
  : CompactnessConclusion X
```

A positional 5-argument builder would only restate the verbose field types and
duplicate `cghMaps_of_hL0 X mc L hL0` five times (CLAUDE.md: shortest correct
implementation, no redundant adapters). The honest frontier fields stay as
`FlowLimitData` fields (item #4), so the structure itself is the intended input
interface; `cghMaps_of_hL0` is the producer that makes it constructible.

## Remaining — discharge the `FlowLimitData` fields (the per-brick work)

- **Brick A** (`L`): the limit Ricci flow on `mc.limit.M` with metric `gInf`
  (Lemma 3.11 output) + `IsSolutionOn` (limit-is-a-solution — HARD). Build `L`
  so that `L.atTime 0 = mc.limit` (then Brick B's `rmaps := hL0 ▸ mc.maps`).
- **Brick B** (`maps`): ✅ DONE — `pointedCGHMaps_of_atZero` (2026-06-21, build
  green). **The feared manifold-type-identification wall does NOT exist**:
  `PointedFlowData.atTime` preserves `M`/topology/charted/basepoint
  *definitionally* (Basic.lean:72, only `metric` changes), so the time-0
  `PointedRiemannianCGMaps` over `L.atTime 0` transport field-for-field to
  `PointedCGHMaps X L subseq` by defeq — a 4-field copy, no casts. Consume it
  with `rmaps := hL0 ▸ mc.maps` where `hL0 : L.atTime 0 = mc.limit` (Brick A).
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
