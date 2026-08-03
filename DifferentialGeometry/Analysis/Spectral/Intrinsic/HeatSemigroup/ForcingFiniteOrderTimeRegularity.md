# ForcingFiniteOrderTimeRegularity.lean — notes

## 2026-08-03 — F1 (FORCEJETMASS_PLAN §9): `ha_super` deleted; the finite-order jet layer is order-free — GREEN

**Outcome: GREEN.**  Same deletion-only surgery as in
`SmoothCoordinateJetPreservation.md`, at the finite-order (`k`-truncated) tier:

* `deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection` (private) — dropped
  **both** `(a : ℕ)` and `ha_super : 2 * Module.finrank ℝ E + 10 ≤ a`.
* `deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` — dropped `ha_super` only;
  `(a : ℕ)` stays because the conclusion names `deTurckSmoothN g₀ g_bg a (F t) …`.
* Two in-file call sites updated by argument removal only.

`deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving` and
`deTurckForcing_finiteOrderSmoothDriver` keep their `ha_super`: theirs feeds
`deTurckRealizabilityRadius` / `deTurckSobolevNHa2_exists_of_super`, which are genuine
consumers of supercriticality.  That is the clean boundary this brick establishes —
**the completed-operator realizability layer is order-gated; the smooth-core jet layer
above it is not.**

Focused check passed (the file is ~5.5k lines; it is slow but not fragile).  Targeted
module build passed.  No `sorry`/`admit`/`axiom`; no heartbeat option changed.  Only
pre-existing `unusedSectionVars` warnings, all far above the edited region and none
introduced here — deliberately left alone rather than swept.

**Risk 1 of the plan is refuted, and here is why it never had teeth.**  The register
feared that the ~30 `private` `anisoOn_*` / `spectralPathFO_*` lemmas (`:1116`–`:4527`),
written inside the supercritical section, might carry `a` in their own statements.  They
do not: the entire block contains **zero** occurrences of `ha_super`.  Those lemmas are
about chart-level anisotropic regularity of a *given* smooth path — Christoffel symbols,
Gram determinant/adjugate/inverse, chart Ricci, the DeTurck vector field, the pushed
`connLapIter` — and every one of them is a statement about a smooth object, so the
Sobolev exponent that guarantees smoothness cannot appear downstream of it.

**Consequence for the campaign.**  All four declarations are now available at `a = 2`.
Front 2's frontier is no longer "all-order time-regularity of a self-referential
forcing"; it collapses to the single spatial statement (S1₂) of `FORCEJETMASS_PLAN` §4,
i.e. the per-scale Galerkin dissipation closure at base order 2 (brick F6).  The plan's
§8 stop-signal requires F1 **and** F6 to fail; F1 has now passed, so that conjunction is
closed permanently and the route error R-c cannot return by this door.

**Reusable lesson.**  Grep the *gate symbol itself* over the private helper block before
believing a "transitive order dependence" story.  Here a single `grep -n ha_super` over
`:1116`–`:4527` returning nothing was decisive evidence hours before the build confirmed
it — the same "grep the object's own producer before declaring a wall" discipline that
dissolved the earlier false walls in this project.
