# DeTurckRemainderLowBaseAction

## Role

This is the intrinsic smooth-core action module for the uniform
low-regularity Ricci--DeTurck remainder.  It performs the dangerous
zero-head self-action refold before differentiation and keeps the small
second-order arm separate from the true first-order action.

## Verified state

Focused verification and the targeted exact module refresh are GREEN for the
current source.  The source contains no `sorry`, `admit`, axiom declaration,
`whnf`, or trace command.  Existing style warnings in older proof blocks
remain local and do not affect elaboration.

The public surface now includes:

- `lowJetSq`;
- `LowBaseActionData` and its `a1` and `a2` actions;
- `lowBaseData`, the deterministic canonical producer used by the split;
- `lowData_split`, the exact zero-based action identity and fibre-small `C2`
  bound for an arbitrary fixed DeTurck background;
- `lowData_a1_coeff`, which names that producer directly and bounds the
  combined two-jet window of its `C0` and `C1` coefficients by the state
  through order three;
- `a1_h3_h2` and `a1_h2_h1` for arbitrary smooth passengers;
- `c2_h2_small`, which proves that the complete canonical `C2` coefficient is
  simultaneously pointwise and two-jet `O(R)` on a sufficiently small
  spectral `H2` state ball;
- `remainder_low_split`, the same-background zero-based split with the
  fibre-small complete `C2` arm;
- `remainder_diag_h2`, which names `lowBaseData` directly and proves
  `J2 (A.a1 T) <= (D R * (A + A^2))^2` under `J2 T <= R^2` and
  `J3 T <= A^2`.

The implementation namespace `LowBaseInternal` now exposes the exact,
transparent finite product trees needed by the sibling pairwise proofs.  In
addition to the connection/Ricci top factors, self-top path integral,
canonical `C2` projection, and two-trace curvature-monomial factorization, it
contains the low Ricci product tree, the zero-arm self-action integrand and
integral, its exact rewrite to the genuinely first-order `ricciGoodLow`
coefficient on the symmetric realized segment, and canonical `C0`/`C1`
read-offs.  These are implementation bridges for the canonical producer, not
a second user-facing action hierarchy.  In particular, the `C0` read-off no
longer strands the pairwise telescope behind inaccessible private constants.
The public diagonal `self_refold` projection and `daTrans_cap` fibre bridge
reuse the verified private diagonal calculations; neither is generalized to
an independent acted field.

The diagonal estimate is radius-free in the high norm: `D` depends only on
the lower `H2` radius.  Its proof treats the complete `C0` self-action before
path integration and uses the affine Ricci/Lie order-one coefficient
producers for `C1`.  The highest state derivative is therefore order three;
no separate order-four state term or `H3` smallness enters.

## Current frontier

The public `LowBaseInternal.self_refold` projection is intrinsically diagonal.
It reuses the already verified private `rhsSelf_refold` proof without changing
its mathematical content.  Its lower Ricci refold accepts independent
coefficient and passenger tensors internally,
but the resulting top term has the cross orientation
`ricciTop(..., U) (nabla^2 P)`; the public kernel identity likewise gives
`curvatureKernel(U) (nabla^2 P)`.  The proof specializes `P` and `U` to the
same state before rewriting scalar factors.  It therefore must not be
generalized or restated as the false pointwise identity with
`ricciTop(..., P) (nabla^2 U)`.  Moving between those orientations requires a
pairing-level integration by parts and produces first-order cross terms.

The intrinsic smooth-core A+ action split, its canonical producer, and the
fixed `H2` smallness of the complete `C2` coefficient are complete.  The
coefficient proof first estimates the exact three-term top integrand

`lieRefold2 + (deTurckPhiMetTotal(g_s) - deTurckPhiMetTotal(g)) +
(-2s) • ricciTop`

and only then integrates it.  The private `lieRefold2_h2` estimate extracts
the fixed-order curvature monomial factorization, while `ricciTop_h2` follows
the finite product chain `daWeight -> daTrans -> dagTopOp -> ricciTop`.  Both
use only an `H2` state radius; neither invokes a high-order ball or `H3`/`H4`
smallness.

The next frontier is time realization:

1. prove the pairwise coefficient estimate for
   `lowBaseData(T).C2 - lowBaseData(T').C2` on a common spectral `H2` ball;
   this is the geometric producer consumed by the already available
   `LowBaseA2.a2_diff`;
2. combine that result with the first-order pairwise producer and realize the
   deterministic complete action as a strongly measurable operator family;
3. prove its time-integrable norm bound and feed `nonautL2_forced`.

The complete canonical `lowBaseData.a2` is the sole `A2` in the final
decomposition.  `lowRegPrincipal` is only an internal comparison/subtraction
reference and must never be added to `lowBaseData.a2`, because doing so would
double-count its principal part.  Nonprincipal second-order material remains
inside `lowBaseData.C2`; it is not moved into `A1` or a lower passenger.
Pairwise core continuity, not an existential selector or a diagonal estimate
alone, remains the visible completion/measurability obligation.  The A2 pair
producer already accepts an arbitrary fixed DeTurck background.  The remaining
background-migration frontier is the pairwise C0/C1 modulus for A1; the static
general-background coefficient and action bounds live in `LowRegBgH2.lean`.

## Progress accounting

- exact zero-based smooth-core action split for arbitrary fixed background:
  100%;
- complete small second-order coefficient: 100%;
- fixed spectral-`H2` pointwise/two-jet smallness of that coefficient: 100%;
- arbitrary-passenger high/low action estimates and static compatibility:
  100%;
- diagonal time-integrable growth estimate: 100% at smooth-core level;
- pairwise `C2` coefficient Lipschitz theorem: unstated/unproved, 0%; its
  inverse/principal coefficient Lipschitz submachinery and the exact Action
  product bridge are now verified, and its downstream high/low
  action-difference consumer is already available;
- measurable complete time operator packaging: 0% as a stated theorem, with
  generic analytic infrastructure mostly available;
- `ricci_flow_unif_existence`: unstated/unproved, 0%;
- this intrinsic action layer: complete for its stated smooth-core duties;
- whole dedicated uniform-existence machinery: approximately 73--75%.

The source is temporarily above the normal line budget under the explicit
session ruling.  It must be split by abstraction boundary after the proof
chain closes.
