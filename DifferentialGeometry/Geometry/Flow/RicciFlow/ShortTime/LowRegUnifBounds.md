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

At that checkpoint the interfaces were focused-check green, while the actual
class-envelope producer remained the next analytic frontier.

## 2026-08-06 — class-first producer closed in dimension three

`exists_lowBounds` now constructs one literal `LowRegBoundData` before the
class metric varies.  It combines `exists_lowRealize`, `exists_lowZero`, and
`lowRegN_outer_unif`, freezes the affine coefficients at `lowregOuterRad`, and
restricts the dense tame packet to `lowregStateRad`.  The DeTurck background
remains the fixed `gBase`, and the class hypotheses stop at metric jets through
order three.

`lowreg_bounds_unif` projects the literal packet through
`IsLowBoundsUnif.toCaps`, closing the previously requested common-envelope
producer.  The focused file check and direct module export pass, and both new
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

Progress accounting: `exists_lowBounds` and `lowreg_bounds_unif` are 100%
verified.  The downstream `lowreg_dt_unif` and
`ricci_flow_unif_existence` endpoints remain unstated/unproved here (0%);
whole HCG theorem closure remains approximately 3%.

`lowreg_solve_unif` now performs the unconditional next composition: it chooses
the common horizon packet and returns a background-aware low fixed-point solve
for every class metric and every smaller positive time.  Its focused check,
direct export, and axiom audit pass.  This theorem is 100%; it is deliberately
not named `lowreg_dt_unif`, because converting `IsLowSolveBg` into a smooth
geometric DeTurck solution on the same horizon remains a genuine bootstrap
frontier.

## 2026-08-06 — consumed by the smooth endpoint assembly

`lowreg_solve_unif` now feeds `lowreg_dt_unif` through the new
`BgSmoothPacket` interface.  The common horizon, fixed background, and
order-three class quantifiers are unchanged.  The packet-to-DeTurck conversion
and the final gauge-removal consumer are verified; their only inherited
`sorryAx` is the single producer `bg_packet_of_solve`.

Honest accounting: the class-first bounds and low solve are 100%.  The final
consumer/gauge assembly is 100%.  The theorem-level uniform existence result
remains 0% until `bg_packet_of_solve` is proved; that missing theorem is a
substantial background-aware same-horizon regularity bootstrap, not another
scalar-bound or fixed-point lemma.
