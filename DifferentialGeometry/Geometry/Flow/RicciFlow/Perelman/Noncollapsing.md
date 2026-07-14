# Noncollapsing

## 2026-07-09 canonical geometry refactor

`FlowMetricBall S t` is now the canonical ball object.  The time is a
`RealTimeInterval.FlowTime`, and the structure stores only a center and positive
radius.  Its carrier `setAt`, distinguished-time `set`, Riemannian `volume`,
backward-parabolic `IsRmControlled`, and model-dimensional
`IsKappaNoncollapsed` predicates are all derived from the actual solution
metric and canonical `rm04` tensor.

`Nested` is genuine same-time set inclusion, so `volume_mono` follows from
measure monotonicity.  The carrier has the same intrinsic-distance shape as the
existing `smallNormalBall`; a future `Metric.ball` adapter belongs in the
comparison/HCG layer rather than this low Perelman layer.

The zero-callsite `ScaleControlledBall` hierarchy and generic
`hypothesis -> conclusion` proposition aliases were deleted after final audit;
they could otherwise serve as a fake-geometric bypass despite a legacy label.
Hamilton Section 12 has migrated: `ham3RescaledBall` is a genuine
`FlowMetricBall` for the actual `paraSolution`, and `Ham3Noncollapse` uses its
`IsRmControlled` and `IsKappaNoncollapsed` predicates.

Verification passed.  The Hamilton rescaled-source realization and its
`ham3_rm_control` theorem are checked.  The genuine remaining theorem is
Perelman's no-local-collapsing producer (`ham3_noncollapse` remains 0%); further
volume/ball scaling lemmas belong below that producer rather than in a fake
numeric-volume wrapper.

## 2026-07-09 W-route start

`Entropy/ConjugateHeat.lean` now checks the local and interval forms of total
mass conservation for smooth solutions of `∂ₜu = -Δu + Ru`.  This is the first
new analytic producer on the Perelman route.  The moving-metric conjugate-heat
existence theorem remains 0%.

The checked supporting chain now also contains the interval-local
`IsHeatPotOn` / `IsConjHeatOn` interfaces and time reversal,
`heat_pot_nonneg`, the time-operator lift, the abstract
`nonaut_strong_exists` fixed-point theorem, and the local moving-volume
first-variation theorem `first_var_local`.  The scalar Laplacian bridge now has
a successful targeted build.  The genuine short-time non-autonomous inputs are
also complete: `lapDiffA20_short` supplies the support-independent moving
Laplacian difference `A2`, while `conjA1_short` supplies the scalar-curvature
potential `A1`.  `conj_strong_exists` completes their specialized spectral
strong-solution assembly.  The strong-to-classical regularity bridge remains
open.

The geometric scale-transfer lane is now complete.  The canonical volume law
is in `Analysis/Integration/Measure/Scaling.lean`; `Metric/DistanceScaling.lean`
proves distance and ball-carrier scaling and is used directly by `setAt`;
`ScaleTransfer.lean` proves two-way transfer of ball carriers, volume,
`IsRmControlled`, `IsKappaNoncollapsed`, the below-scale predicate, and
`NoLocalCollapsing`.  Hamilton's checked `ham3_noncollapse_of` now reduces the
fixed rescaled-ball conclusion to a genuine original-flow
`NoLocalCollapsing` producer.

Consequently the scale-transfer sublane is 100%, but the analytic
no-local-collapsing theorem and `ham3_noncollapse` remain theorem-level 0%.
Dedicated analytic machinery is about 32%; whole HCG machinery remains about
45% with endpoint theorems at 0%.

## 2026-07-13 scalar weak equation

The Pro-consulted selector-free route has now completed its first three
interfaces: the applied A2 graph closure, the exact A1 scalar graph test, and
`Entropy.conj_weak_ae`, which threads both into the actual maximal-regularity
solution almost everywhere in time.  This is real geometric weak-equation
machinery; it is not the classical moving conjugate-heat theorem and does not
prove noncollapsing.

The precise next analytic frontier is a genuine second-order non-autonomous
interior bootstrap for this scalar weak equation.  The existing first-order
`solField_into_all_tensorHs_interior` theorem cannot absorb A2's two-derivative
loss.  After that bootstrap, joint spacetime smooth reconstruction and the
pointwise derivative bridge remain before `IsHeatPotOn` can be produced.

The smallest first producer is `scalar_crit_tame` in the low Gårding layer: at
every Sobolev order it must split the moving scalar operator into a uniformly
small two-derivative principal arm and an order-dependent one-derivative
remainder.  Existing DeTurck critical-tame/Galerkin theorems are `(0,2)`-tensor
specializations and cannot be called directly.  This is a substantial analytic
producer, not a local elaboration or typeclass gap, and no assumption-shaped
wrapper was added around it.

Honest accounting: `heatpot_of_maxreg` is still unstated/unproved (0%) with
about 30% dedicated reusable machinery; the classical moving conjugate-heat
theorem remains 0% with about 75% dedicated machinery; Perelman
no-local-collapsing and `ham3_noncollapse` remain 0% with about 34% dedicated
analytic machinery.  Whole HCG machinery remains about 45%, with its endpoint
theorems at 0%.

## 2026-07-13 second-order bootstrap stop

The invariant scalar coefficient decomposition has advanced: the moving
cometric trace and traced connection-difference are now genuine fixed-tag
`SmoothCcTensor` fields with fully applied scalar read-off theorems.  Generic
`appCc` jet control, rank-generic spectral-to-jet and jet-to-spectral bounds,
and rank-generic Galerkin energy infrastructure are also checked producers.
This is machinery progress only; `scalar_crit_tame`, `heatpot_of_maxreg`, and
the no-local-collapsing endpoint remain 0% as theorems.

The bootstrap audit has now reached five genuinely distinct failed routes:

1. the existing interior theorem loses only one derivative;
2. the pre-refactor DeTurck critical tame was tied to `(0,2)` and a special
   resolvent-iterate family;
3. fixed-background Gårding alone did not isolate the small moving principal
   coefficient;
4. the base `H2 -> H0` bound and weak equation do not commute a moving operator
   through Galerkin projection at high order;
5. the new coefficient-jet route closes each fixed order with a top constant
   `A(k)`, but the live Galerkin consumer requires one coefficient below `2`
   for all orders simultaneously.

The fifth problem is the current analytic stop frontier.  The next consultation
should choose a direct energy/commutator normal form in which only order-zero
ellipticity enters the top term, or another bootstrap that proves all orders on
one fixed shorter interval.  A fixed-order tame theorem alone must not be wired
to the existing all-order consumer.

There is also a shared-worktree verification conflict: the new public
`metricCcTensor_apply` source checks, but its object-file refresh is blocked by
an independently claimed upstream curvature file with a parse error.  That
lane was not modified or force-released here.

Honest accounting: Perelman no-local-collapsing and `ham3_noncollapse` remain
0%; their dedicated analytic machinery is about 40%.  The classical moving
conjugate-heat theorem remains 0% with about 77% dedicated machinery;
`heatpot_of_maxreg` remains 0% with about 35% directly reusable machinery; whole
HCG machinery remains about 53%, with its endpoints at 0%.

## 2026-07-13 direct dissipation consult

The completed Pro consultation is recorded at
<https://chatgpt.com/g/g-p-6a05f8e7fb0881918ae46beec6dcd123-lean-pro-consult-handoff/c/6a55679f-4250-83e8-9f44-f3b67243e7ff>.
It explicitly searched the GitHub page for
`liao9yuan/differential-geometry`, branch `short-time-existence`.  The public
non-autonomous engine was available there, while the post-merge DeTurck,
pairing, and commutator files were not; the latter were verified only against
the live post-merge worktree.

The consultation corrected its initial commutator claim.  The raw operator
`[1 - Delta, A^{ij} nabla_i nabla_j]` has a third-order
`(nabla A) * nabla^3 u` term.  The direct route closes only after converting
the scalar principal arm to divergence form and treating the commutator as a
balanced bilinear expression of total odd order.  This rules out starting with
a one-step pointwise commutator theorem.

The chosen chain is now exact:

1. prove the coefficient-to-flux identity and `scalar_flux_split`;
2. prove `cc_principal_pair` with the order-zero metric smallness as the only
   top coefficient;
3. prove the support-independent balanced estimate `cc_comm_pair`;
4. assemble `cc_energy_diss`, using the generic coefficient-one Dirichlet gap
   only at the final step;
5. feed that dissipation into the second-order bootstrap, then joint smooth
   reconstruction and the classical heat-potential interface.

The lower-layer `appCc_assoc` producer and the generic `covDiv_appCc` rule are
focused-verified.  Reusing `appCc_assoc` is essential to the cheap proof normal
form: repeating whole-Hom composition extensionality in the divergence
consumer caused a deterministic kernel timeout.  The current frontier is the
fully scalar metric/cometric trace identity `trace_slot_flat`, valid for an
arbitrary covariant rank-two tensor.  No consumer assumption,
`HasLocallyConstantChartAt`, wrapper black box, Hessian-symmetry hypothesis, or
spectral-support-dependent constant was added.

Honest accounting: Perelman no-local-collapsing and `ham3_noncollapse` remain
0% as endpoint theorems, with about 40% dedicated analytic machinery.  The
classical moving conjugate-heat theorem remains 0% with about 77% dedicated
machinery; `heatpot_of_maxreg` remains 0% with about 35% directly reusable
machinery.  Whole HCG machinery remains about 53%, with endpoint theorems at
0%.
