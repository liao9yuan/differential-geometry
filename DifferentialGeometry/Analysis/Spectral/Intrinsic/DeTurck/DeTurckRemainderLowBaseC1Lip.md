# DeTurckRemainderLowBaseC1Lip

## Role

This sibling contains the canonical fixed-order pairwise estimates for the
complete order-one Ricci--DeTurck coefficient, together with the
background-lowered connection estimates used by its Ricci and Lie pieces.

## Implemented result

`wXi_sub_h2` proves radius-free `H2` Lipschitz control of the two-endpoint
`wXi` difference in dimension three:

- the metric difference is linear at the squared `H3`-jet level;
- endpoint sizes enter only through the polynomial factor
  `(1 + J3(T)) * (1 + J3(U))`;
- only a common fibre-small neighborhood is assumed;
- there is no `H3` or `H4` smallness assumption.

The exact route lowers the connection pair by the `gU` endpoint, uses the
moving-lowering correction cocycle, and raises the last slot back with the
same endpoint inverse. This avoids a duplicated two-endpoint inverse
resolvent proof and keeps the passenger derivative at order three.

`wXi_sub_tame` sharpens the same exact decomposition to the critical
two-arm form needed by the low-regularity fixed-point consumer.  After
freezing an endpoint `H2` radius, the `H3(T-U)` arm has a coefficient
depending only on that radius.  Endpoint `H3` size occurs only in the
separate term multiplying `H2(T-U)`.  In particular, the coarser polynomial
high-size factor from `wXi_sub_h2` is not used as the final tame endpoint.

`ricci1_pair_h2` and `lie1_pair_h2` separately prove the fixed-order
two-endpoint estimates for the Ricci connection-difference arm and the full
fourteen-piece DeTurck Lie arm. Their common public endpoint `rhs1_pair_h2`
gives the critical modulus

`B0 * D3 + B1 * D2 + B1 * A * D2`.

Here `A` controls only the base-point `H3` jet, `D3` the `H3` difference, and
`D2` the spectral `H2` difference. No all-order ball or fourth state
derivative enters this coefficient estimate.

The narrow `LowBaseInternal` interface now also exposes `mcd_pair_h2` and
`mcd_h2_bdd`. These are the fixed-order pair and one-state `H2` estimates for
the background-lowered metric connection difference; they are shared
producers for the remaining zero-coefficient refolds and introduce no new
public action-level API.

The same internal interface now exposes `revSlot_pair_h2` and
`revSlot_bdd_h2` for the reverse raised-endomorphism factor used in the
covariant Lie residual.  The tied-metric identity makes this factor
`id + symmRaiseEndo P`; hence its difference is exactly linear in `T - U`
and its bound uses only the endpoint `H2` radius.  No inverse denominator or
`H3` smallness enters these estimates.

## Verification

Focused verification and the targeted public-module refresh passed. The file
contains no `sorry`, `admit`, `axiom`, `whnf`, or trace debugging.

## Project accounting

- `wXi_sub_h2` and its consumer-shaped sharpening `wXi_sub_tame`: complete
  (100%).
- Complete pairwise order-one Ricci--DeTurck coefficient estimate:
  complete (100%).
- Path-integrated `C1` estimate and the remaining pairwise `C0`/action
  assembly belong to `DeTurckRemainderLowBaseLip`; the coefficient producer
  needed for that integration is now complete.  The next direct consumer is
  the `lcvOmega` product telescope in that module.
- Uniform low-regularity Ricci--DeTurck existence theorem: still unstated and
  unproved (0%); the dedicated low-base machinery is approximately 98--99%
  complete, pending the path-integrated pairwise `A1` assembly and downstream
  fixed-point completion wiring.

## 2026-07-26 session (A+ lane resume)

Public H1 layer (`wXi_pair_h1`, `connSec_pair_h1`, `metricCorr_pair_h1`) is
focused GREEN and the exact targeted refresh of this module has been done
(9574/9574).  `metricCorr_pair_h1` allocation:
`J1(metricCorr_T - metricCorr_U) <= C*(J2(T-U)*J1(wXi_T) + J2(U)*J1(wXi_T-wXi_U))`.
No re-refresh needed unless the public surface changes again.
