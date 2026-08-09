# EdgeCenterNormal

## Target

`edge_center_s_nf` is the fixed-path-parameter exact normal form for the
carrier-centered joint zero/top block.  It uses the diagonal refold only when
the path state and acted tensor are both `T`; the two off-diagonal raw pair
terms remain explicit in `Cross`.

The normalized right-hand side is

`L(E0 T) + (L(Ds T) - Ds (L T)) - (Ks - K0)(L T) - Cross`,

where `E0 = edgeCarry0 + edgeQuad0` and `Ds` is the variable-cometric
principal arm at the realized metric.  This is the cancellation-safe form:
the complete order-zero and top blocks are never estimated separately.

## Verification and frontier

`edge_center_s_nf` passed its focused check and its direct export refresh.
The source is warning-free and contains no `sorry`.

`edge_q_six` is now the verified coefficient-level six-monomial reduction for
the canonical arrays.  Four local `Equiv.ext` facts identify the cancelling
pairs `qB 0 = q 0`, `qA 0 = (q 0).trans swap01`, `qA 2 = q 2`, and
`qB 2 = (q 2).trans swap01`; each is proved from the existing swap/composition
definitions by `fin_cases`, with no numeric permutation aliases.  Expanding
the two Palatini kernels and the three-term Lie sum then leaves precisely the
output codes `0321`, `1320`, `0123`, `1023`, `3012`, and `3102` with signs
`++----`.  Its focused check passed; no downstream refresh was needed because
there is not yet a consumer of this new declaration.

`edge_arg2_nf` is now focused-verified for arbitrary complete permutation and
weight arrays.  It rewrites the exact rank-four raw-Laplacian argument

`edgeTopPairG_s (Delta (nabla^2 U))`

as `edgeTopPairG_s` applied to

`nabla^2 (Delta U) + nabla(pointwiseTensorCurv g 2 U)
  + pointwiseTensorCurv g 3 (nabla U)`.

Thus the first summand is definitionally the `edgeTopPairBi_s (Delta U)` core,
while the remaining two displayed summands are the exact counterterm.  In
particular, differentiating `pointwiseTensorCurv` exposes the unavoidable
`(nabla^2 Rm(g)) * U` cell.  This theorem deliberately normalizes the already
isolated argument cell; it does not claim the still-missing mixed-rank
Leibniz/trace theorem identifying that cell inside the raw Laplacian of every
`edgePairMono`.

The adjacent generalized action producer `edgeTopG_apply` is now
focused-verified in `EdgeRefoldPairing`.  Specializing its arrays to
`ricciRefoldQA/QB` and `lieRefoldQ/Eps` identifies the raw pair acting on `T`
with `rhsRefold2` acting on an arbitrary rank-four `G`.  This closes the
orientation/API question without asserting an arbitrary passenger.  At the
curvature-defect argument

`G = nabla(pointwiseTensorCurv g 2 T)
  + pointwiseTensorCurv g 3 (nabla T)`,

the complete coefficient algebra instead leaves the transparent block

`(lieRefold2 + (Phi_s - Phi_0) - 2s * ricciTop) G`.

It is generally not zero.  This is no longer expected to be a cancellation
theorem: its `(nabla^2 Rm(g)) * T` part is a fixed-metric lower coefficient,
not automatically a forbidden principal coefficient.

`phiMet_fold_comm` is also focused-verified.  It applies the exact
`phiMet_curv_fold` to both `S` and `L S`, replacing the whole commutator of the
folded curvature coefficient `K` by the commutator of the non-pure top
coefficient before any spatial derivative of `K` is expanded.  Consequently
`Tr_g ((nabla^2 K) · S)` is no longer a cell that should be estimated on its
own.  The theorem does not identify the canonical raw `q` block with that
non-pure top block, so it sharpens rather than closes the joint frontier.

A subsequently attempted Green-form lower-curvature theorem was rejected and
deleted.  Its right-hand side contained `covGrad V`; at the intended
specialization `V = L^2 T` this is an `H^5` demand, so it cannot be a producer
for the binding `H^4` route.

The exact complete-edge gate is now closed by the sibling
`EdgeCenterCommutator.edge_center_peel`.  It is a **complete-edge non-Green
peel**, not a zero identity, a norm wrapper, or a separate estimate of the
order-zero and top blocks.  At fixed `s`, it expands the joint high block

`L(edgeQuad0_s T) + (L(Ds T) - Ds (L T)) - (Ks - K0)(L T)`

as the two directed raw Cross orientations plus explicit `2+0` and `1+1`
Leibniz corners, the curvature-defect argument, and lower carrier terms.  The
only fourth-order state input allowed is the explicit uniformly-small
principal head `nabla^2(LT)`; all other literal D4 orientations must cancel
against the exact Cross assembly.  No derivative may land on the test tensor.
In the equivalent transparent self-refold currency, the joint second-order
coefficient is

`lieRefold2 + (deTurckPhiMetTotal_s - deTurckPhiMetTotal_0) - 2s * ricciTop`.

The existing generic Hessian/Laplacian commutator is not by itself the final
estimate, but its differentiated-curvature term is not a STOP condition merely
because it reads `nabla^2 Rm(g)`.  Since `G_g` is selected after the fixed
smooth `g`, this jet may enter the lower coefficient when the term contains at
most one `H4` factor and at least one actual lower state norm.  The existing
Green identities remain inadmissible because they differentiate the test
tensor and demand `H5`.

The first two representation gaps on the route from
`iteratedCovGrad_appCcRS_eq_argCorner_add_lower` to the isolated complete-edge
cell are now closed: public `appCcPsi_diag` identifies the top Leibniz corner,
and public `cometricTrace_appCcRS` transports its double trace at arbitrary
contravariant valence.  Exact raw-Laplacian naturality for the remaining
`slotExtend` and `rsDomDomCongrSection` terms is still absent as a reusable
generic API, but it is no longer a frontier on the selected route.  This file
alone does not package the exact centered expression as a
principal-head-isolating explicit peel; the sibling
`EdgeCenterCommutator.edge_center_peel` supplies that verified package while
retaining the nonzero curvature defect rather than asserting that it vanishes.

## Honest progress

- `edge_center_s_nf`: 100% complete and verified.
- `edge_q_six`: 100% complete and verified; this is the first finite algebraic
  brick for the complete polarized expansion, not that expansion itself.
- `edgeTopPairG` and `edge_arg2_nf`: 100% complete and focused-verified as
  stated; they expose, but do not cancel, the full curvature counterterm.
- `edgeTopG_apply`: 100% complete and focused-verified as an orientation/action
  theorem; no zero cancellation is claimed.
- Complete-edge non-Green peel `edge_center_peel`: 100% complete,
  focused-verified, and directly refreshed in `EdgeCenterCommutator`.
- `edge_center_h4_unif`: not yet stated or proved, therefore 0%.
- The downstream full low-base uniform estimate and the final uniform
  short-time existence endpoint remain unstated/unproved on this route,
  therefore 0% each.  This exact normal-form lemma does not change those
  endpoint percentages.
