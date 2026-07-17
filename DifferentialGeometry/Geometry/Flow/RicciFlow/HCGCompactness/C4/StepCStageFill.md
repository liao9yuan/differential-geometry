# StepCStageFill

## Route

This file implements Route A's smooth two-bump safety-totalization layer.  A
fixed safety clamp globalizes the reverse transition, and a fixed activity
cutoff interpolates between that target and the source point.  No pointwise
chart selector or equality-test `activeFill` occurs in the smooth map.

## Status

- `safeFill`, `safeFill_smooth`, and `safeFill_diag` implement the generic
  smooth filler and its reindexed `C^∞` diagonal convergence.
- `activityBump` and `safetyBump` implement the fixed `6/7` and `7/8` radius
  gaps.  `stageClamp_mapsTo` is the global target-domain safety statement and
  `stageFill_eq_raw` is the exact active-region readout.
- `stageTotal` totalizes only over the fixed finite slot index, retaining the
  old `InterSlot L ... alpha`; there is no pointwise chart selector or old/new
  subtype equivalence.
- `stageWeightSub`, `stagePtsSub`, and `stageCfgSub` are the actual refined
  finite-stage configuration.  `HasSuppConvData.cfgSub_conv` proves its full
  all-reindexing `MapCInfConvOnCompacts` convergence to the diagonal
  configuration on every source patch.
- `stagePtsSub_eq_ne` proves that a nonzero actual weight at a retained
  interacting target makes the smooth filler exactly the raw two-transition
  target.
- `HasSuppConvData.pts_eq_ne` takes one finite common tail and proves that every
  arbitrary nonzero actual slot selects such an old `InterSlot`, then applies
  the exact raw-target readout.  Stable-disjoint slots are therefore vacuous on
  the same tail.
- `HasSuppConvData` now retains the all-stage two-sided transition smoothness
  already produced by the common finite-pair tail; this is producer output,
  not a new compactness input.

Focused verification passed for `StepCStageFill`, the strengthened upstream
`StepCProducers`, `StepCSupportCapstone`, and `StepB1RawProducer`; the two
explicit producer modules were refreshed successfully.

The Route-A filler/configuration subphase is checked (100%).  The first
genuinely new analytic frontier is common-domain center-equation convergence and a
moving implicit-root family with one parameter neighborhood.  The concrete
`StepB1RawInput` producer and textbook Step B1 theorem remain theorem-level
0%.  Rounded machinery estimates are about 95% for Step-B/B1, 87% for Chapter
4, and 57% for the whole HCG project.

## 2026-07-16 buffered-cover compatibility

The four direct `HasSuppConvData` decompositions now retain and ignore, where
appropriate, the new convexity, origin, and uniform closed-ball buffer fields
before reading the existing core-cover, geometry, weight, and transition
fields.  No stage-filler statement or radius was changed.  Focused verification
passed after this projection-only migration.

`StepB1RawInput` and textbook B1 remain theorem-level 0%.  Dedicated Step-B/B1
machinery is roughly 98%, Chapter-4 machinery roughly 90%, and whole-HCG
machinery roughly 60%.
