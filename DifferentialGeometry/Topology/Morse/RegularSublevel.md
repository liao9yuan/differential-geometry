# RegularSublevel universe generalization

## Mathematical route

The regular-level and regular-sublevel constructions are universe-polymorphic: their topology,
charted-space, model-with-corners, and smoothness arguments do not require the ambient manifold,
model target, or auxiliary source manifold to live in `Type 0`. The existing declarations and
proofs are retained unchanged; only their explicit type binders are generalized from `Type` to
`Type*`.

This applies in particular to the level-set charted-space and manifold instances, the smooth
level-set inclusion, and the smooth factorization through a regular level set. The latter now
accepts auxiliary model and source-manifold types in arbitrary universes. The analogous local and
global sublevel-corestriction helpers are generalized for consistency because they feed the same
regular-sublevel API.

The regular-level chart, manifold, inclusion, and factorization chain requires only the project's
smooth grade `((⊤ : ℕ∞) : WithTop ℕ∞)`. Its former ambient
`IsManifold I (⊤ : WithTop ℕ∞) M` assumptions asked for the strictly stronger outer-top analytic
grade even though every chart, cutoff, transition, and chain-rule call in the dependency closure is
made at smooth grade. The affected ambient instances have therefore been lowered through exactly
that producer closure, ending at `manifoldLevelSetChartedSpace`,
`manifoldLevelSetIsManifold`, `contMDiff_levelSetInclusion`, and
`contMDiff_levelSet_factor`. No function-smoothness assumption or conclusion was changed.

## Reuse and scope

- Reused the existing `LevelSetSpace`, `manifoldLevelSetChartedSpace`, and regular-sublevel proofs.
- No declaration names, conclusions, proof bodies, imports, instances, or hierarchy were changed.
  The only hypothesis change is the removal of the unnecessary outer-top manifold grade described
  above.
- The change is infrastructure for the P1c smooth zero-level/product route; it does not complete a
  Cheeger--Gromoll splitting endpoint. That endpoint remains unstated/unproved here (0%).

## Verification status and risk

The universe-polymorphic, smooth-grade source passed a warning-free focused check and an explicit
named module refresh. The existing long proof bodies therefore elaborate under both the widened
universes and the weakened ambient manifold grade, and the regular-level exports are fresh for the
P1c Product consumer. No mathematical or API blocker remains in this module.
