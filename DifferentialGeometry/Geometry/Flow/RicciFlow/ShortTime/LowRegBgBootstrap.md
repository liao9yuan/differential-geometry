# LowRegBgBootstrap.lean — fixed-background same-horizon endpoint

Status 2026-08-07: the direct same-horizon adapter is now proved.
`bg_packet_of_mass` turns `IsLowSolveBg` plus exactly the all-order spatial
mass output into `BgSmoothPacket`; it reuses the two-metric
`direct_jet_of_mass` and introduces no lift or horizon shrink.  One old
proof-body `sorry` remains in `bg_packet_of_solve`; that statement is still too
strong because a bare solve does not supply the adapted rung/mass package.
The production replacement `bg_packet_of_adapt` is now present as a thin
metricwise composition.  It passes focused verification and the direct module
refresh after `LowRegBgAllMass` became fresh.

**ROUTE STATUS (2026-08-07, user ruling — supersedes §"The remaining
producer and interface correction" below):** `bg_packet_of_solve` will be
discharged by **route (c), direct smoothing** (ledger
`UNIF_EXISTENCE_PLAN7.md` №225–227): widen the diagonal
adapted-solve/rung/gate chain (`IsLowSolveAt`/`IsAdaptedLowSolve` → rungs →
`lowreg_loMass`) from `(g, g)` to `(g, g_bg)`, then synthesize the order-two
carrier directly from the all-order mass (no `IsRealizedTwo`, no
adjacent-scale lift, no lift-horizon certificate).  The ladder adds no
horizon constraint.  Interface decision (C1, Pro overall ruling,
ledger №235): `bg_packet_of_solve` is unprovable as posed — the
absorption inequality `A·(δ/(1−δ)²) + B·stateRad + ε < 1` is not
derivable from arbitrary `IsLowBoundsAt K` (`lowreg_adapt_open`
calibrates BEFORE solving; adaptation is not a free post-certificate).
The frontier will be RESTATED as `bg_packet_of_adapt` taking
`ha : IsAdaptedLowBg g g_bg K hK hT hT1 u gforce` (solve + rung
certificates + absorption budget), and a class-first producer
`lowreg_adapt_unif` chooses uniform gate bounds/threshold/state cap and
a literal common `K` BEFORE `g`.  (N)'s statement and
`lowreg_dt_unif`'s THEOREM STATEMENT stay unchanged; `lowreg_dt_unif`'s
PROOF BODY rethreads (uniform solve → uniform adapted solve).  This
replaces the much heavier lift-data interface correction described
below (which also demanded a shortened horizon).  The lift layer stays
in place, unused, until the (c) synthesis lands (rollback point).  The
lower section is kept as the historical record of the superseded lift
route; its analysis of WHY the lift cannot serve the current statement
remains correct.

## Verified interface

`BgSmoothPacket g g_bg K T` records exactly the order-two closed-slab data
consumed by the existing joint-smoothness theorem: an order-two maximal-
regularity carrier, zero trace, smooth forcing modes with all-order weighted
majorants, the closed-slab Duhamel coefficient identity, a state bound at the
class-first solver radius, a full-slab realization bound, and the forcing-
coordinate identity for the independent DeTurck background `g_bg`.

`dt_of_bg_packet` is proved.  It constructs the explicit global `H²` fibre
constant from `K.realize`, converts the packet through
`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`, and obtains
a Ricci--DeTurck metric family with `JointChartGramSmooth` on exactly `T`.
There is no horizon shrink and no opaque metricwise `choose` in this adapter.

`bg_packet_of_mass` is also proved.  Its inputs are the canonical
`IsLowBoundsAt`/`IsLowSolveBg` pair and the exact conclusion expected from
`lowreg_loMassBg`.  All forcing background dependence is handled by
`direct_jet_of_mass`; spectral promotion, Duhamel mode pinning, the closed-slab
state bound, and the realization radius are shared with the diagonal route.

`bg_packet_of_adapt` consumes one already-constructed
`IsAdaptedLowSolveBg`, obtains the every-exponent mass through
`lowreg_loMassBg`, and passes that mass together with the stored
`IsLowBoundsAt`/`IsLowSolveBg` projections to `bg_packet_of_mass`.  It makes no
class-first choice and leaves the obsolete bare-solve frontier visible.

`lowreg_dt_of_solve` and `lowreg_dt_unif` remain checked conditional consumers
through the old `bg_packet_of_solve` frontier.  Their statements keep the
class-first quantifier order and the fixed class background, but their current
proof path still inherits that frontier's `sorry`.

## The remaining producer and interface correction

The current `bg_packet_of_solve` statement asks an arbitrary
`IsLowSolveBg g g_bg K` on every supplied `T ≤ 1` to produce the packet on that
same horizon.  The implemented adjacent-scale contraction instead requires a
separate high/low action package and the explicit bound
`T ≤ lowregLiftHorizon' c Z`.  `IsLowSolveBg` stores neither `c`, `Z`, `L` nor
this lift-horizon certificate.  Therefore the current frontier statement must
not be treated as a settled interface.

The corrected route is to add explicit background-aware lift data, choose the
class-first time below both the order-one solve horizon and the lift horizon,
and separate two implications:

- a low solve plus the lift data and horizon certificate produces a genuine
  background-aware order-two realization package;
- that realization package produces `BgSmoothPacket` by the all-order
  one-sided bootstrap.

The explicit package must contain the full arbitrary-background high/low `A1`
maps and affine bounds, the arbitrary-background `A2` contraction constants,
the realization radius, and the force-margin inequality.  It must not be a
wrapper whose constructor merely assumes `BgSmoothPacket`.

`lowSolve_cross` now exports the existing `duhamelCross` / `crossRepr_ball`
route as a reusable producer from `IsLowSolveBg`.  It gives a canonical same-
horizon `H²` representative, identifies its lower carrier with the supplied
order-one solution, and proves the state bound `lowregStateRad` at every time
of the closed slab.  Its focused check passes with one Lean thread and the
6 GB cap, without adding any axiom or new hypothesis.

This does not supply an order-two maximal-regularity carrier.  The first honest
analytic producer is the full arbitrary-background `A1` affine packet.  Its
missing order-zero correction is the time integral of the exact background
correction.  `amixBg_pair_h2` now closes the mixed arm of its pointwise `H2`
pair estimate; the `DLa` and `DLb + Insert` arms remain.  After the lift, the
self-background all-order mass/jet assembly still has to be made
background-aware.

The settled local `lowreg_allOrderJet` proves precisely this kind of endpoint
for the richer `IsRealizedTwo` package, but that package and its entire rung
producer are self-background `(g,g)`.  They cannot be applied to the class-
first fixed-background solution `(g,gBase)` without a new background-aware
adjacent-scale bridge.

## Collaborator repository audit

The qinz short-time-existence route really does prove smoothness up to the
initial edge: `JointChartGramSmooth` is joint smoothness on the closed slab
`Icc 0 T`, and the final Ricci-flow theorem consumes it after gauge removal.
That source theorem nevertheless has per-metric quantifiers `∀ g₀, ∃ T` and
its construction may shrink time after the initial metric and solution are
known.  It validates the packet fields and the one-sided endpoint mechanism,
but it is not a class-first producer for the preselected uniform horizon.

## Verification and accounting

The file passes focused verification and its direct module refresh is green.
The only reported `sorry` is the pre-existing `bg_packet_of_solve`;
`bg_packet_of_mass` and the new `bg_packet_of_adapt` are complete.  The final
Ricci-flow endpoint and `MaximalTime` consumer remain conditional consumers.

- packet-to-DeTurck endpoint: 100%;
- `bg_packet_of_mass`: 100%;
- `bg_packet_of_adapt`: 100%;
- shared two-metric direct-jet core: 100%;
- gauge and final consumer assembly: 100%;
- same-horizon `H²` cross representative: 100%;
- arbitrary-background mixed order-zero `H2` pair arm: 100%;
- metricwise background mass/rung producer through `lowreg_loMassBg`: 100%;
- class-first adapted-solve producer and final rethreading: 0%;
- `bg_packet_of_solve`: 0% theorem completion and intentionally superseded by
  the adapted-solve route;
- `ricci_flow_unif_existence`: 0% until the inherited `sorryAx` disappears;
- whole HCG project: approximately 3%.
