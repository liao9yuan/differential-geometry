# EdgeRateBound

## Current source state

`EdgeRateBound.lean` is focused-green without a local diagnostic for the
fixed-time principal, formal-partner, and combined pairing estimates.  It has
no `sorry`, `admit`, axiom, `whnf`, trace, or opaque replacement.  Its exact
artifact refresh is also green.

The file exports:

- `edgeRate0` and `edgeRate1`, the exact visible order-zero and order-one
  fields after the Palatini--DeTurck refold;
- `exists_edgePairRef`, which reconstructs the existing refold package while
  retaining `qA`, `qB`, `q`, and `epsilon`.  Those data are essential inputs
  to `edgeTop_zero` and `edgeTop_one`; `exists_edgeSlopeRef` hides them;
- `edgeCore_path_le`, which correctly applies `edgeCore_pair_le` to `s • W`
  and cancels the positive factor `s ^ 2`.  The tempting direct application
  to `W` is invalid because the slope metric is `g + s W`, not `g + W`;
- `edgeTop_pair_le`, which combines `edgeTop_green`, `edgeTop_zero`,
  `edgeTop_one`, and
  `exists_iteratedCovGrad_covDivergence_l2_le`.  It chooses a positive radius
  internally and proves
  `topPair <= (1/4) * ||nabla W||^2 + K * ||W||^2`; and
- `edgePair_pair_le`, which conditionally cancels that positive quarter
  against the negative quarter in `edgeCore_path_le` once pointwise bounds for
  the *entire supplied* `C0` and `C1` fields are already available.  It is
  generic refold glue; it does not produce such bounds for the concrete
  `edgeRate0` and `edgeRate1`.

## Mathematically valid part of the route

The top refold has the required sharp zero.  If `P_s` is the explicit
rank-four formal partner, the existing pointwise producers give

`|P_s|^2 <= C0 * delta^2 * |W|^2`,

`|nabla P_s|^2 <= C1 * delta^2 * |nabla W|^2`.

The public divergence estimate at order zero therefore controls
`||div P_s||` by the sum of these two norms.  Cauchy--Schwarz and Young's
inequality absorb the resulting gradient term after shrinking `delta`; no
`H2` norm of the arbitrary edge tensor is introduced.

The principal route is also faithful.  At slope `s`, the realization theorem
ties the metric to `s • W`.  Homogeneity of the rough Laplacian, principal
arm, lower arm, covariant derivative, and Hilbert pairing gives an exact
factor `s^2`, which is cancellable for `s in (0,1)`.

The moving inverse-metric and volume reactions are not a mathematical gap:
`movingReactVol_le` already provides the required pointwise multiple of the
moving difference norm, and `carrierEdge_bounds` supplies one carrier-speed
constant on a closed slab.

## Durable failed routes

- A standalone bound on the returned `C2` coefficient loses the small
  undifferentiated metric difference.  The exact formal-partner and Green
  route is required and is now implemented.
- The older `exists_edgeSlopeRef` hides the permutations and signs required
  by the sharp partner bounds.  `exists_edgePairRef` is the consumer-shaped
  producer which retains them.
- Generic smooth-family suprema depending on arbitrarily high jets of `W`
  cannot supply a closed-edge uniform constant.  Any concrete coefficient
  bound must use the low-regularity `C0/C1` arms and the available finite
  Sobolev control, not a high-jet radius for the arbitrary edge solution.

## Exact remaining producer

The earlier proposal to instantiate `edgePair_pair_le` with pointwise bounds
for the complete concrete `edgeRate0` and `edgeRate1` is rejected.  The
Ricci DA part of `edgeRate0` contains a derivative of the connection
difference, so such a bound either asks for an inadmissible high derivative
of the arbitrary edge tensor or hides the real integration-by-parts step.

The Ricci contribution is now handled at pairing level by exact-current
`ricciDA_path_le`, `ricciAA_path_le`, and `ricci1_path_le`, after the
Riemann--Palatini cancellation.  The next theorem must isolate and estimate
only the remaining non-Ricci DeTurck lower arms, keeping their exact joint
path structure.  Its constants may depend on carrier/background slab data
and the low-regularity ball, but not on nonsmall higher jets of the arbitrary
difference tensor.

After that producer, the remaining packaging step is to combine the slope
path identity with the spatial `L2` pairing and feed the resulting uniform
rate into `movingEnergy_zero`.  This packaging is not allowed to reintroduce
a coarse `C2` estimate; the top term must remain discharged by
`edgeTop_pair_le`.

This fixed-time result is supporting machinery.  The already completed
`ricci_flow_forward_unique` endpoint does not need to be reproved.  For black
box `(N)`, the independent remaining construction frontiers are still
`rhsRefold0` H2/time-L2 control, the same-horizon order-two bootstrap,
all-order smoothing and geometric realization, and the uniform common-horizon
assembly.

## Honest progress

- `EdgeRateBound` public theorems: **100% as stated under focused and exact
  verification**.  Direct axiom audits of its four principal public theorems
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Concrete uniform nonlinear rate theorem: **0%**, because it is not yet
  stated and proved.  Its dedicated fixed-time/refold/energy machinery is
  approximately **85--90%**.
- `(N) ricci_flow_unif_existence`: **0% as a theorem**; its dedicated
  machinery remains conservatively **84--87%**.
- `ricci_flow_forward_unique`: complete in the post-merge tree; this file does
  not change that endpoint.
