# LowRegBgBootstrap.lean — fixed-background same-horizon endpoint

Status 2026-08-07: the endpoint packet and every downstream consumer are
verified conditionally.  One intentional proof-body `sorry` remains in
`bg_packet_of_solve`, and the present same-horizon statement is stronger than
the adjacent-scale lift interface currently proved in the repository.

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

`lowreg_dt_of_solve` and `lowreg_dt_unif` are proved compositions.  The latter
keeps the class-first quantifier order and the fixed class background.

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

The file passes focused verification and its direct module refresh.  The final
Ricci-flow endpoint and `MaximalTime` consumer also pass focused verification.
The only textual `sorry` in this direct chain is `bg_packet_of_solve`.

- packet-to-DeTurck endpoint: 100%;
- gauge and final consumer assembly: 100%;
- same-horizon `H²` cross representative: 100%;
- arbitrary-background mixed order-zero `H2` pair arm: 100%;
- `bg_packet_of_solve`: 0% theorem completion; its current interface requires
  correction by explicit lift data and a lift-horizon certificate;
- `ricci_flow_unif_existence`: 0% until the inherited `sorryAx` disappears;
- whole HCG project: approximately 3%.
