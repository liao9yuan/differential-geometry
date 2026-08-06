# LowRegUnifBounds.lean

## 2026-08-05 — explicit common-horizon package

`IsLowBoundsUnif gBase Λ K` records the honest `exists`-before-`forall`
boundary for the low fixed-point lifetime: one certified `LowRegBoundData`
packet is fixed first, while each class member supplies its own
`IsLowBoundsAt g gBase K` proof in its own spectral spaces.

`unif_solve_of_bounds` is the assembly theorem.  It proves positivity of the
single closed `lowregHorizon` and runs `lowreg_sol_of_data` for every class
member and every smaller positive time.  It does not claim that the uniform
bound packet has been produced, and it carries no all-rung comparison data.

The preferred weakest interface is `IsLowBoundsCap gBase Λ U`: the common
`LowRegHorizonData` gives upper caps for `Ctop/B0/B1/D` and lower floors for
`ρ/P`, while every metric may use a different exact `LowRegBoundData`.
`unif_solve_of_caps` transports the common horizon through
`horizon_le_of_cap` and retains both the exact packet and its solve output.
`IsLowBoundsUnif.toCaps` shows that literal packet uniformity is only a stronger
special case.

This separation is necessary: the rung-five H6 comparison in
`IsLowGateUnif` needs curvature/metric jets beyond the order-three class and
therefore cannot be a prerequisite for the common lifetime.  Higher
regularity remains a separate qualitative bootstrap.

Focused verification passed without warnings.  The actual class-envelope
producer remains the next analytic frontier.
