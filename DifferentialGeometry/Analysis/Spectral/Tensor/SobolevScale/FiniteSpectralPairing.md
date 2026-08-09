# Finite spectral pairing

## 2026-07-14 finite-core Parseval bridge

The rank-generic finite spectral pairing bridge is complete.  The public chain
is `cc_iter_coeff`, `cc_l2_pair_tsum`, `cc_pair_tsum`, and `finite_cc_pair`.
The final theorem identifies the finite weighted coefficient pairing of a
finitely supported `tensorHs` element with the intrinsic `L²` pairing of its
canonical smooth representative against `(1 - Δ)^n`.

The constant-free identity is independent of the size and location of the
spectral support.  It reuses `tensorHsSmoothRepr` and does not introduce a
second finite-combination representation.  Focused verification and the named
module build passed, with no new `sorry`.

This bridge itself is complete (100%).  It is machinery for the scalar
critical-tame/Galerkin route, not a conjugate-heat or noncollapsing endpoint.

## 2026-07-14 finite representative energy

`finite_repr_norm` factors the repeatedly used identification between the
spectral Sobolev norm of `tensorHsSmoothRepr` and the finite weighted
coefficient energy.  It is a projection lemma in this rank-generic finite-core
layer, rather than a consumer-local rewrite.

Focused verification now passes.  The initial named-module refresh exposed a
local rewrite-normal-form failure at the whole summation; scalarizing it to a
`tsum_congr` proof closed the issue without changing the statement.  The
`finite_repr_norm` theorem and its dedicated projection machinery are complete
(100%); downstream critical-tame and Galerkin endpoint theorems are accounted
for separately.

## 2026-08-08 complementary iterate split

`cc_pair_tsum_split` now splits an integer spectral weight `a + b` between
`b` iterates of `1 - Δ∇` on the state and `a` iterates on the test tensor.
The proof stays in the finite spectral layer: Parseval plus the existing
per-mode iterate coefficient identity are sufficient, so no higher Gårding or
DeTurck import is needed.

`finite_pair_split` is the direct rank-`(0,2)` adapter for a mode set `F` and
coefficient family `c`.  It converts the finite weighted sum to the intrinsic
`L²` pairing without introducing a support witness or changing the Galerkin
mode set.  At Rung 3, choosing `a = 1` and `b = 2` yields the required
`L²` pairing of two state-side iterates with one force-side iterate.

Focused verification passed with no new `sorry`.  Both pairing identities are
complete (100%); the signed C2 Gårding estimate that will consume them remains
a separate theorem frontier.

## 2026-08-08 symmetric scaled finite pairing

`finite_symm_scale` is the rank-`(0,2)` adapter needed when the finite spectral
state is first symmetrized and scaled, while the test tensor is already fixed by
`symmS`. It keeps the exact finite mode set and complementary iterate split of
`finite_pair_split` and places
`θ • symmS (finiteEigenCombo g F c)` in the first `L²` slot.

The proof uses only two private algebraic facts local to this file: real scalar
linearity of `oneMinusConnLapSmoothIter`, and commutation of that iterate with
`symmS`. Their producers are the existing linear raw connection Laplacian,
slot-swap equivariance of the raw Laplacian, and self-adjointness of the slot
swap in the smooth `L²` inner product. No new foundational public API or
frontier assumption was introduced.

Focused verification passed with no new `sorry`. `finite_symm_scale` and its
dedicated local machinery are complete (100%). This closes the routine finite
spectral pairing adapter, but not the signed C2 Gårding estimate that consumes
it: that estimate remains a separate theorem frontier (0% as a proved theorem).
Within the current Route (c) redesign this adapter is a small producer brick
(about 2% of the route); it does not change the overall uniform short-time
existence endpoint, which remains unproved (0%).
