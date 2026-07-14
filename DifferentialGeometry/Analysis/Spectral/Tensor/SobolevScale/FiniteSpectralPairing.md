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

Its focused verification is pending because the shared build tree currently
lacks a generated upstream coordinate-tensor object file; no local theorem
error has yet been reported.
