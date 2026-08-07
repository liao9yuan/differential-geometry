# LowRegBgC0PairH2

## Role

This sibling keeps the arbitrary-background order-zero `H2` pair work out of
the already oversized `LowRegBgC0Pair.lean`.  The route is three-dimensional
and targets the critical `H3 → H2` two-state currency used by the one-sided
smooth bootstrap.

## 2026-08-07 mixed arm

The public `amixBg_pair_h2` is complete.  It refolds the exact background
subtraction before estimating, uses the public linear `pbLow_h2_mul` producer
for the background connection factor, and uses exact Koszul cancellation for
the self-background factor.  Its output has the same
`B0 * D3 + B1 * N + B1 * A * N` currency as `c1_bg_pair_h2`, where `N` is the
spectral `H2` distance of the two states.

Focused verification passed after removing the unnecessary dependency on the
older `LowRegBgC0Pair` H1 module.

## 2026-08-07 DLa arm

The public `dlaBg_pair_h2` is complete and focused verification is clean.  Its
proof is fully background-aware and uses only the common three-dimensional
spectral ball plus the prescribed intrinsic radii.  The chain now contains:

- the low Palatini two-state estimate and its single-state affine bound;
- slot-three raised-factor pair and radius bounds;
- the full `lieBgCore` pair estimate in
  `D3 + D2 + A * D2` currency and its `C0(R) + C1(R) * A` single-state bound;
- the two-slot pass transport, moving pair-trace estimates, and exact `DLa`
  refold.

The final public scale is
`D3 + D2 + A * D2 + N + A * N`, with
`N = ||Hs2(T-U)||`.  In particular, no `A^2 * N` passenger was introduced.

## 2026-08-07 complete order-zero pair

The sibling `LowRegDlbInsH2` now provides the cancellation-preserving
`dlbIns_pair_h2` bound in the sharper
`D3 + D2 + A * D2` currency.  The public `lie0_bg_pair_h2` combines it with
`dlaBg_pair_h2` and `amixBg_pair_h2` after the exact `lie0` background split.
It uses a common fibre cap for the two endpoints, both endpoint `H3` caps, and
one spectral `H2` ball selected before the states vary.  Its final root is

`B0(R) * D3 + B1(R) * D2 + B1(R) * A * D2 + B1(R) * N + B1(R) * A * N`.

The completion required an honest domination step: the common `B1` also
absorbs the nonnegative `AMix` `D2/A*D2` passengers and the `DLb` `N/A*N`
passengers that are absent from the sharper individual arms.  Focused
verification passed cleanly with no local warnings.

The next metricwise producer is the path-integrated background `C0` `H2` pair;
after that come the actual background `C0`, high `A1`, and radial completion
adapters.  The later class-first radius/affine producer remains analytically
separate.

## Accounting

- `amixBg_pair_h2`: theorem 100% complete.
- `dlaBg_pair_h2`: theorem 100% complete.
- `dlbIns_pair_h2`: theorem 100% complete in its sibling module.
- `lie0_bg_pair_h2`: theorem 100% complete; the entire pointwise order-zero
  `H2` pair is closed.
- full arbitrary-background high `A1` producer: endpoint unstated (0%); its
  remaining metricwise path/refold/radial assembly is routine, while the later
  class-first actual-core radius and affine bound is still a genuine producer.
- `ricci_flow_unif_existence`: still 0%; conditional consumers remain separate
  from this producer work.
