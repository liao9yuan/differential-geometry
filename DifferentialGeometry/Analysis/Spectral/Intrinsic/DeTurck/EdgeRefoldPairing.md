# EdgeRefoldPairing

## Current state

`EdgeRefoldPairing.lean` is focused-GREEN with no local warning. On 2026-08-08
the checked source was extended with the polarized monomial API separating
coefficient state `P`, acted tensor `U`, and test tensor `V`. The complete
checked artifact contains the diagonal and polarized pointwise pair-trace
calculation, the global formal-adjoint identities, the Green steps, and both
existential assembly theorems. A prior direct axiom audit of `edgePair_l2`,
`edgePair_inner`,
`edgeTop_inner`, `edgeTop_green`, `exists_edgeRefold`, and `exists_edgeSlopeRef`
reported exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The file contains no proof placeholder or new axiom.  Its public source-level
producers are:

- `edgeRicciHalf`, the exact Ricci half-combination left after adding and
  subtracting one Riemann coefficient;
- `edgeFold0`, the explicit lower residual after separating the DeTurck
  covariant-derivative arm from its endomorphism arm;
- `edgeZeroBoundAt` and `edgeMetric_bal`, which let the equal-radius public
  refold packages be used on the sharp-zero closed-edge path; and
- `edgeMvTrace`, which reconstructs through public APIs the exact identity
  between a moving-metric double trace and a fixed-background trace with one
  `fullRaisedEndoField` insertion;
- `edgePairMono` and `edgeMonoRefold`, which reconstruct the private
  pair-trace/Palatini monomial identity using the public `mvPairTraceOp` and
  `mvPairTrace_apply`;
- `edgeLiePairFam`, `edgeRiemPairFam`, and `edgeTopPair`, together with their
  exact action theorems, which package the full returned `C2` coefficient as a
  rank-two pair-trace field acting on `W`; and
- `edgeSlot2`, `edgeRaise2`, `edgeProd4`, and `edgePairPartner`, the explicit
  smooth rank-four formal-partner carrier for one moving monomial;
- `edgeTopPairBi` and `edgeTopPartnerBi`, the complete raw Riemann--Lie top
  family with independent path state `T`, Hessian state `U`, coefficient
  passenger `P`, and test tensor `V`; and
- `edgeTopPairG`, the same complete raw top family with an arbitrary rank-four
  Hessian-slot field `G`; `edgeTopPairBi` is now its definitionally exact
  Hessian specialization, exposed by `edgeTopPairBi_eq_G`; and
- `edgeTopG_apply`, the arbitrary-`G` action theorem.  It keeps the path state
  and coefficient passenger equal to `T` and identifies the complete pair with
  the corresponding Ricci--Palatini plus DeTurck refold coefficient acting on
  `G`; it does not assert the rejected arbitrary-passenger low-base identity;
  and
- `edgeTop_point_bi` and `edgeTop_inner_bi`, the pointwise and global exact
  formal-partner identities for that complete polarized family.
- `edgePairPartnerBi`, whose raised pair contains the coefficient state `P`
  while its unraised pair contains the independent test tensor `V`, together
  with `edgePartnerBi_self` and `edgePartnerBi_eval`;
- `edgeSlot2_eval`, `edgeRaise2_eval`, `edgeProd4_eval`, and
  `edgePartner_eval`, which expose that carrier componentwise;
- `edgeMono_eval`, `edgePair_l2`, and `edgePair_inner`, which source-assemble
  the exact pointwise and global formal-adjoint identity for one public
  moving pair-trace monomial;
- `edgePair_l2_bi`, `edgePair_inner_bi`, and `edgePair_green_bi`, the
  corresponding polarized monomial identities; `edgePair_green_bi` specializes
  the acted rank-four tensor to `nabla² U` and moves exactly one derivative to
  give the single term `-<covDivergence partner(P,V), nabla U>`. The original
  diagonal declarations are now specializations of the first two declarations
  in source;
- `edgeLiePartner`, `edgeKernelPartner`, `edgeRiemPartner`, and
  `edgeTopPartner`, culminating in `edgeTop_inner`, the corresponding exact
  formal-partner identity for the complete top coefficient;
- `edgeTop_green`, which applies the closed-manifold covariant Green identity
  to that complete partner and moves the second derivative of `W` exactly onto
  `covDivergence edgeTopPartner`; and
- `exists_edgeRefold`, which directly consumes
  `exists_riemannPalatini_refold_identity_data` and
  `exists_deTurckLieCovDerivArm_refold_identity_data`;
- `exists_edgeSlopeRef`, which composes that producer with `edgeSlope_split`
  and exports the complete consumer-shaped `rhsSumSlope` normal form.

For every fixed smooth symmetric metric difference `W` with nonnegative
`delta <= 1/2`, `exists_edgeRefold` constructs its finite jet radius internally
and returns coefficient families `C0`, `C2` on the entire slope segment.  It
records all of the following in one producer:

1. the exact full tensor identity for `edgeQuadArm`;
2. a uniform pointwise bound for `C0`;
3. an explicit pointwise `O(delta)` bound for `C2`; and
4. the corresponding full Hilbert/L2 pairing identity.

No derivative bound on an arbitrary edge-path metric is an assumption of this
statement.  The internally chosen finite jet radius only instantiates exact
identities for the already smooth fixed tensor; it is not used as the final
closed-edge energy coefficient.

## Exact remaining energy producer

The refold deliberately leaves three structurally low-order terms visible:

- `edgeRicciHalf`, whose top connection derivative cancels in the Ricci
  half-combination;
- `edgeFold0`, consisting of the DeTurck endomorphism arm, `lieCorr0`, the
  curvature fold, and the fixed-carrier subtraction; and
- `edgeQuad1` acting on `nabla W`.

The next smallest mathematical producer is the joint closed-edge estimate

`<W, -2 edgeRicciHalf(W) + edgeFold0(W) + edgeQuad1(nabla W)
      + C2(nabla^2 W)>`

`<= c * delta * ||nabla W||_2^2 + K * ||W||_2^2`,

with `c * delta` small enough for the remaining principal absorption.  The
`C2` term must be integrated by parts in its Palatini/refold form; replacing it
by a standalone coefficient norm followed by a coarse H2 estimate would lose
the closed-edge argument.  Likewise, separately bounding `edgeRicciHalf` as a
generic order-zero coefficient would reintroduce an inadmissible dependence on
spatial derivatives of the arbitrary edge solution.

The diagonal pair-trace obstruction and its algebraic formal-adjoint step are
focused-verified: `edgeMonoRefold` is the public reconstruction, `edgePair_l2`
moves one monomial onto its rank-four partner, and `edgeTop_inner` reaches the
complete diagonal `C2` returned by `exists_edgeRefold`. The new polarized
monomial identity reuses that same component proof with inner coefficient
occurrences changed to `P` and outer test occurrences changed to `V`; it has
now been focused-verified. The pair-trace implementation lives in the small
`MovingPairTrace.lean` module; that module and its generic output-slot
permutation dependency are exact-current.

The covariant Green step is now present at source level as `edgeTop_green`; it
turns

`<W, appCc C2 (nabla^2 W)>`

into the first-order pairing of `nabla W` against the divergence of
`edgeTopPartner`.  The exact movement of both relative inverse-metric
insertions onto the two `W` factors is now represented by `edgePair_l2` and
`edgeTop_inner`.  Differentiating that explicit partner produces only products
containing one undifferentiated `W`, hence the required
`O(delta) * |nabla W|^2` bound.  This is materially different from estimating
`nabla C2` as a generic coefficient jet, which would destroy the sharp zero at
`W = 0` and introduce an inadmissible additive source.

The older claim that the diagonal structural divergence bound was still the
remaining producer is stale. `EdgePartnerBound.lean` now proves
`edgeTop_zero` and `edgeTop_one`, and `EdgeRateBound.lean` consumes them in
`edgeTop_pair_le` via
`exists_iteratedCovGrad_covDivergence_l2_le`. The live Route (c) gap is instead
polarized: differentiating `edgePairPartnerBi P V` naturally produces both
`|nabla P| |V|` and `|P| |nabla V|` contributions. Controlling those terms in
the required spectral pairing is a new structural estimate, not merely the
routine algebra and one exact integration by parts proved by `edgePair_l2_bi`
and `edgePair_green_bi`. The Green theorem itself introduces no second term:
all dependence on acted tensor `U` is confined to `nabla² U` before Green and
`nabla U` afterward.

A top-level polarized *raw* family is now present as `edgeTopPairBi`, with the
corresponding explicit partner `edgeTopPartnerBi`.  This is deliberately not an
arbitrary-passenger identity for the whole low-base operator: it only polarizes
the canonical raw Riemann--Lie pair before path integration.  The full low-base
`C2` kernel is still not definitionally just the old diagonal `edgeTopPair`, so
the bridge to the combined `C0+C2` residual remains at the actual consumer
layer.

The subsequent arbitrary-passenger audit shows that a pointwise frozen wrapper
would be mathematically false, not merely absent.  The exact Ricci and
Palatini identities have cross orientation: the independent passenger enters
the rank-four coefficient while `nabla^2` remains on the path state.  Reversing
those roles is valid only on the diagonal or after a paired integration by
parts with additional first-order terms.  Existing `edgeRiem_cancel` already
handles arbitrary passengers once given a correctly oriented refold, so a
conditional `_bi` alias would add no content.

The arbitrary-Hessian definition and specialization are focused-verified and
their direct export was refreshed.  The subsequent `edgeTopG_apply` action
theorem is also focused-verified; no new downstream consumer yet required an
export refresh for that declaration.  It does not assert that the raw Laplacian of the complete pair
has already been decomposed into its Leibniz argument corner: that separate
mixed-rank trace/permutation naturality bridge remains outside this file.

The exact algebraic declarations `edgeRicciHalf`, `edgePairMono`,
`edgeMonoRefold`, `edgeLiePairFam`, and `edgeLiePair_apply` live in
`RefoldPairingCore.lean`.  This file imports that exact-current module and
retains the energy, formal-partner, L2, and Green layers.  The move preserves
the public names and removes the low-regularity consumer's dependency on this
energy module.

## Progress accounting

- Exact endpoint `ricci_flow_unif_existence`: **0%**; its theorem has not been
  proved.  Dedicated fixed-background Route-(c) machinery is approximately
  **94%** under the revised binding `ROUTE_C_PLAN.md` denominator: the
  arbitrary-passenger audit replaced a presumed routine frozen adapter by a
  genuine paired cross-orientation redesign.  The refold artifact
  is exact-current and axiom-clean; the homogeneous Rung-3 Gårding producer and
  final contraction/existence assembly remain outstanding.
- `exists_edgeRefold` and `exists_edgeSlopeRef`: **100% as stated**,
  focused-GREEN, exact-current, and axiom-clean.  This does not by itself prove
  the closed-edge contraction or the uniform existence endpoint.
- Polarized monomial partner machinery: **100% as stated and focused-GREEN**.
  The complete raw polarized top family and its pointwise/global formal-partner
  identities are also focused-GREEN and target-refreshed.  No complete-top
  Green wrapper was retained: the intended test is `L² T`, and applying Green
  there would introduce an inadmissible `H5` charge.
- The monomial `P`/acted-`U`/test-`V` API remains reusable, but exact source
  audit still requires the binding Route-(c) consumer to recombine the
  `C0+C2` whole slope without asserting a false arbitrary-`U` low-base
  identity.  `EdgePathPairing` integrates the raw Q/Z pair in formal-partner
  form; the remaining producer is the quantitative combined B02 estimate.
  The uniform contraction, solution
  construction, and lifetime-uniformization theorem remain separate endpoint
  work.
- The Hamilton positive-Ricci endpoint is unchanged until the independent
  uniform-existence and maximal-flow inputs are genuinely proved.
