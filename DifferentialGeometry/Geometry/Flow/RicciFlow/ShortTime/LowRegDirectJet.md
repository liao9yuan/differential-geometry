# LowRegDirectJet

## Role

This module is Brick 0 of route (c), the fixed-metric feasibility gate for
direct same-horizon smoothing.  It starts from the existing diagonal
`IsAdaptedLowSolve` and produces the complete order-two forcing/carrier packet
consumed by the joint-smoothing endpoint.

## Verified result

`direct_jet_of_mass` and its diagonal compatibility wrapper
`lowreg_directJet` are proved and focused verification passes.  The earlier
axiom audit of the diagonal endpoint is exactly the expected
`[propext, Classical.choice, Quot.sound]`.
The focused check also passes under the project default heartbeat setting; no
local heartbeat override is retained.

The proof contains no occurrence of:

- `IsRealizedTwo`;
- `liftForceHi`;
- `liftHiN`;
- `lowregLiftHorizon'`;
- the equivalent high-scale certificates `hbridge`, `hFComm`, or `hA2sq`.

Thus the consult's Brick-0 stop condition did not fire: direct smoothing is a
real route, not a disguised adjacent-scale lift.

`direct_jet_of_mass` is the reusable fixed-background seam.  It takes primitive
two-metric solve data and an all-order spatial-mass hypothesis; dimension three
appears only in producers of that hypothesis.  The diagonal theorem is now a
thin wrapper using `lowreg_loMass`.

## Proof route

1. `force_step_one` and `force_driver_one` run the finite-order forcing driver
   directly at order one.  The dense forcing identity is supplied by
   `lowReg_force_smooth`.
2. `lowreg_forceJet1` combines that driver with `lowreg_loMass` and produces a
   globally smooth coordinate family with all time-jet/spatial masses.
3. `force_promote_two` synthesizes an order-two time-`L²` forcing from those
   coordinates by a spectral majorant and the higher-mass continuity theorem.
4. `duhamel_mode_pin` identifies the promoted order-two carrier with the
   Lions--Magenes order-two representative of the original order-one Duhamel
   field.
5. `direct_state_bound` transfers the original state radius to every time of
   the closed slab.
6. `direct_force_coeff` cuts a pinned smooth family off outside the slab,
   obtains its order-three a.e. pin from `duhRepr_field_ae`, applies
   `lowReg_force_smooth`, and upgrades the resulting forcing-coordinate
   identity from a.e. to every point of `Ico`.
7. `direct_radius` supplies the endpoint's order-four realization radius from
   the all-order forcing mass.

The only upstream API change is that `carrier_coeff_pmConv` in
`LowRegAllOrderJet.lean` is now public; the proof body and statement are
unchanged.

## Fixed-background adapter and next dependency

`LowRegBgBootstrap.bg_packet_of_mass` is proved.  It combines
`IsLowSolveBg`, `IsLowBoundsAt`, and exactly the all-order spatial-mass output
with `direct_jet_of_mass`, producing `BgSmoothPacket` on the same horizon.
Therefore the sole remaining input to the direct endpoint is the
background-aware low-mass/rung producer.  Do not reintroduce the old A1/A2
adjacent-scale completion lane.

## Progress accounting

- theorem `lowreg_directJet`: **100%**;
- theorem `direct_jet_of_mass`: **100%**;
- adapter `bg_packet_of_mass`: **100%**;
- route-(c) Brick 0: **100%**;
- route-(c) background/adapted endpoint lane: approximately **40%** (the
  background mass/rung chain and uniform absorption remain; final packet
  assembly is now proved conditional on mass);
- headline theorem `ricci_flow_unif_existence`: **0%** until its proof no
  longer transitively uses `sorryAx`; its broader dedicated uniform-existence
  infrastructure remains approximately **80%**.
