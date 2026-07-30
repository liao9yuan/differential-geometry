# DeTurckRemainderLowBaseLip

## Role

This module isolates the exact pairwise algebra of the full-A2-subtracted
low-base residual.  It deliberately does not claim that the principal-only
residual maps H3 to H2.

## Current state

- `LowBaseActionData.a1Sub` is the genuine difference of the C0 and C1
  coefficients, with zero C2 coefficient.
- `lowBaseDiff` specializes this bundle to the canonical zero-based producers
  at two perturbations.
- `rhsLow1_sub` splits the pointwise order-one family difference into the
  Ricci connection-difference and DeTurck--Lie coefficient arms.
- `lowC1Diff` is the path integral of the pointwise difference of the two
  radial order-one coefficient families.
- `lowC1_sub` identifies that explicit path producer with the `C1` projection
  of `lowBaseDiff`; no ball or high-order hypothesis is introduced.
- `lowBaseDiff_c1` records the same identity directly on the canonical
  pairwise bundle consumed by `a1_diff`.
- `lowC0Diff` is the path integral of the difference of the two transparent
  zero-arm self-action families.  `lowC0_sub` and `lowBaseDiff_c0` identify it
  exactly with the canonical `C0` difference; the fixed curvature coefficient
  cancels.
- The private `selfLow_parts` identity exposes the complete same-background
  integrand as the RicciGood, Lie-covariant/edge, VB, AMix, and Riem pieces.
  It uses no Sobolev ball or all-order wrapper.
- `metricCorr_sub_h2` proves the radius-free H2 difference estimate in the
  explicit perturbation slot of `metricLowerCorr`, using the native exact
  linearity theorem and `metricCorr_h2_mul`.
- `metricCorr_tel` splits the full two-state `metricLowerCorr` difference into
  that controlled perturbation-slot arm and the remaining moving-metric arm.
- `wXi_sub` cancels the fixed DeTurck background from that moving-metric arm,
  leaving only the difference of the two background-lowered connection
  coefficients.
- `metricCorr_pair` combines both telescope arms into a full radius-free H2
  two-state bound.
- `metricCorr_tame`, using the public `wXi_sub_tame` producer, has the critical
  modulus
  `B0(R) D3 + B1(R) D2 + B1(R) A D2`; no `U`-H3 input is used.
- `a1_sub_comm` proves that the difference of any two completed first-order
  actions preserves the H3-to-H2 / H2-to-H1 commuting square.  This completion
  fact is now independent of the remaining geometric estimate.
- `lowResidual_sub` rewrites the lower-residual difference as the frozen
  first-order action on the perturbation difference plus the canonical
  coefficient-difference action.

## Remaining frontier

The public `lowA1_pair_tame` endpoint is not yet stated or proved (0%).  Its
smallest missing producers are fixed-order critical H2 pair estimates for:

1. the complete RicciGood plus Lie-edge combination in `selfLow_parts`; and
2. the pointwise `rhsLow1Coeff` difference underlying `lowC1Diff`.

The target orientation is fixed:

`B0(R) D3 + B1(R) D2 + B1(R) A D2`.

It uses a common H2 radius, the H3 size of `T`, and H2/H3 sizes of `T-U`; it
must not introduce a separate H3 hypothesis on `U`.

Three routes were checked:

1. The fixed-order intrinsic action module keeps the self-refold coefficient
   estimates private, so it has no canonical pairwise C0/C1 estimate to reuse.
2. The older all-order Lipschitz machinery requires a supercritical order and
   a high Sobolev ball, which is not a low-base endpoint.
3. The chart/`LowRegCoeff` route proves the full right-hand side only from H3
   to H1 and does not realize the required full-A2-subtracted intrinsic H2
   coefficient difference.

### Direct two-endpoint path audit

A fourth, algebraically different route was checked: refold the original
`T`-to-`U` path directly with velocity `W = T - U`.

The low-level pointwise algebra is not intrinsically diagonal:

- the private `ricciConn_refold` and `safeLow_action` accept an arbitrary
  metric perturbation `P` and an independent symmetric passenger `W`;
- the public
  `ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient`
  has the same general `P, W` shape;
- `edgeMonoRefold` also accepts independent tensors in its coefficient and
  second-gradient slots.

The first family-level blocker is nevertheless exact and concrete.  The
available `rhsSelfLow`, `rhsSelfTop`, `rhsSelf_refold`, `selfLowInt`,
`selfTopInt`, and `refold0_self` all hard-code the radial path `T` to zero,
the identity `P = s • T`, and passenger `T`.  Likewise,
`riemannPalatiniRefoldC2Family` and `edgeLiePairFam` are radial/self-action
families rather than general two-endpoint families.

Naively substituting `P(s) = U + s • (T - U)` in the low-level identity
produces the second-order term

`C2(T - U) (nabla^2 P(s))`,

not a coefficient acting only on `nabla^2 (T - U)`.  Its `nabla^2 U` part
would recreate the forbidden high-state leak.  Thus the smallest missing
exact lemma for this route is a cross-head cancellation between this
general-path refold and the difference of the canonical full A2 actions.
No public family identity currently performs that cancellation.  Merely
generalizing the radial family definitions would therefore not close the
H3-to-H2 estimate.

The exact algebraic producer is expected to be routine once that analytic
coefficient-difference lemma exists.  The missing estimate itself is a
substantial producer extraction, not a coercion or elaboration issue.

### Completed metric-lowering telescope

The refolded `C0` expansion contains `metricLowerCorr`.  Holding its moving
metric fixed, the native theorem `metricCorr_sub` exposes linearity in its
explicit perturbation slot.  `metricCorr_sub_h2` combines that identity with
`metricCorr_h2_mul`, giving the first genuine radius-free pairwise H2
coefficient estimate in this lane.

Both telescope arms and the moving-metric `wXi` estimate are now assembled in
`metricCorr_tame`.  This is one genuine C0 pair component, but it is not the
full `selfLow_parts` estimate.

### Next coefficient brick

The next implementation brick is the C1 trace/kernel telescope.  It rewrites
`linearizedRicciConnDiffOrder1CoeffField` as moving trace applied to the
connection kernel, orients the product as endpoint-`U` trace times the kernel
difference plus trace difference times endpoint-`T` kernel, and therefore
avoids a `U`-H3 hypothesis.  The required inverse-trace and lowered-connection
pair bounds are being factored as fixed-order public internal helpers rather
than copied from the all-order hierarchy.

## Verification

Focused verification is green.  No exact refresh has been requested for this
module yet.

## Progress

- `lowA1_pair_tame`: not yet stated or proved (0%).
- Exact pairwise coefficient-difference and completion machinery: about 95%.
- Critical C0/C1 pair-estimate machinery: about 35%.
- Dedicated uniform-existence machinery: about 90%.
- Final uniform existence theorem: 0%.

## 2026-07-26 session (A+ lane resume, Fable direct)

New GREEN this session (focused check 38-92 s, zero diagnostics):

* `metricCorr_tame_h1` (~:2398 pre-insert): `J1(metricLowerCorr_T -
  metricLowerCorr_U) <= (B0 R * D2 + B1 R * A * D2)^2` — only `D2`, no `D3`.
* `app_h21_mul_lip` / `dom_h1_lip` (private): fixed-order H2*H1->H1
  application bound (via public `appRS_h2_h1_h1`) and order-1 slot-permutation
  jet invariance — minimal migrations of the C1 privates.
* `omega_pair_h1` (private): the H2-coefficient x H1-connection telescope for
  `lipOmega`, mirroring `omega_pair` one order down.
* `lieOmega_pair_h1` (PUBLIC): `J1(lipOmega_T - lipOmega_U) <=
  (B0 R * D2 + B1 R * A * D2)^2` with `B0 = Hc*P*W0`, `B1 = Hc*(P*W1 + Q)`;
  the final constant identity is exact (`ring`), no slack term and no `D3`.
  Consumes `revSlot_bdd_h2`/`revSlot_pair_h2` (J2 coefficients),
  `wXi_self_tame` lowered by `jet_mono_lip`, `wXi_pair_h1` (C1, delta0 = 1/3).
* `riem_pair_h1` (PUBLIC): narrow `jet_mono_lip` corollary of `riem_pair_h2`
  (NOTE: must live AFTER `jet_mono_lip` in the file; first placement above it
  failed the check — declaration order matters for the private helpers).

Exact refresh of this module NOT yet run (deliberate): run it once after the
C0 H1 chain lands.

### Current C0 H1 frontier (the next brick)

Bound `J1` of the two-state difference of each `selfLow_parts` class at
`gm_T(s)` vs `gm_U(s)`, then path-integrate (`lowC0Diff` shape via
`lowC0_sub`):
1. `(-2) . ricciGoodLow g gm (s.T)`
2. `deTurckLieCovDerivArmField - edgeLiePairFam`
3. `lc0VB`   4. `lc0AMix`   5. `lc0Riem` (use new `riem_pair_h1`)
Reuse `lieArm2_pair_h1`, `metricCorr_tame_h1`, `lieOmega_pair_h1`, and the
`LowBaseInternal` H2 pair/bdd family.  All outputs H1-only; any step
demanding C0-H2, `D3` or `nabla^4 T` = wrong allocation, fall back to
H2xH1->H1 product form.  After the C0 chain: hook into Pair's existing
`a1Lo_diff` (do NOT rebuild the geometric decomposition), then ONE exact
refresh of this module, then refresh Pair only when a downstream reader
lands.

### Producer inventory for the five-class C0 H1 telescope (2026-07-26 scout)

Existing public factor-pair producers: `trace2_pair_h2` (C2Lip:4633),
`mcd_pair_h2` (C1Lip:4603), `lieArm2_pair_h1`, `riem_pair_h1` (class 5 DONE),
`metricCorr_tame_h1`, `lieOmega_pair_h1`, `wXi_pair_h1`, `connSec_pair_h1`,
`metricCorr_pair_h1`.

MISSING factor pairs (to build in LowBaseLip, referencing the PRIVATE
single-state tame lemmas in DeTurckRemainderLowBaseAction.lean as read-only
patterns — that file is NOT in this lane's claims):
* class 1 `ricciGoodLow`: two arms — `ricciAA_act_tame` / `ricciDA_act_tame`
  (Action ~:6961); need their pair versions, then the 2-arm telescope
  (`ricciGood_act_tame` :6932 is the assembly pattern).
* class 3 `lc0VB` (`lc0VB_h2_tame` :7996): composite
  riemLive x (vbMcd . mcd) x (ip . wOmega) via `app_h2_mul`; need
  `wOmega_pair`, `vbMcd_pair`, `ip_pair` (or telescope at the composite
  level with one-side bdd + other-side pair, H2xH1->H1).
* class 4 `lc0AMix` (`lc0AMix_h2_tame` :8366): same style; reuse
  `metricCorr_tame_h1` + `lieOmega_pair_h1` where the factors match.
* class 2 `deTurckLieCovDerivArmField - edgeLiePairFam`: arm part =
  `lieArm2_pair_h1`; the `edgeLiePairFam` difference needs its own lemma
  (it is T-indexed data, not a gm-composite — check its s-family definition).

Assembly: `selfLow_parts` (:225) five-way split at gm_T(s) vs gm_U(s) +
`realizedFam` pair modulus, then `lowC0_sub` path-integral (:294) with
`jointContMDiff_toModel_continuous_slice` integrability, minkowski over the
five classes.  ALL at J1, product allocation H2xH1->H1; no D3.

ORDER RULING (cost-ranked): class 2 first (arm done, only edgeLiePairFam
diff new) -> class 4 (factors metricCorr_tame_h1/lieOmega_pair_h1 exist) ->
class 3 (needs wOmega/vbMcd/ip pairs) -> class 1 LAST (deep private
ricciAA/DA plumbing in Action, heaviest replication).

CLASS-2 ALLOCATION WARNING (2026-07-26 scout): edgeLiePairFam
(RefoldPairingCore.lean:185) = s . sum_i eps_i . (edgePairMono g
(realizedFam T s) (nabla^2 T) q_i + swap); a naive T/U telescope puts the
difference in the nabla^2-slot => J1 needs D3 = FORBIDDEN.  The arm-minus-
edge COMBINATION is the D2-safe object (edgeLiePair_apply :204 shows the
edge term IS the extracted second-order part of the arm).  Route: find the
existing rewrite of `deTurckLieCovDerivArmField g gm g - edgeLiePairFam ...` 
into its lower-order remainder form in DeTurckRemainderLowBaseAction.lean
(the Q-appearances :2209-2550, selfLow_good chain) and pair-bound THAT.
Self-side slots carry A (J1(nabla^2 T) <= J3(T) = A^2); difference stays in
the realizedFam/coefficient slots at D2.

NEXT-WINDOW ENTRY POINT (class 2 continuation): the arm-minus-edge unit
`(deTurckLieCovDerivArmField g gm g_bg - edgeLiePairFam ... s)` appears as a
unit in Action's `selfLow_decomp` (:2306) and again near :3536 and :10558.
Its single-state bound = `lieCov_h2_tame` (RESOLVED): J2(armField(realizedFam T s) - edgeLiePairFam T s) <= (Bl R*(A+A^2))^2; class-2 brick = mirror it as `lieCov_pair_h1` — search by OBJECT:
`grep -n "CovDerivArmField" DeTurckRemainderLowBaseAction.lean` sections
after :3536, and the C0-action assembly around :10558, to find how the C0
H2-action chain bounded this unit; mirror that shape one order down
(H2 coefficients x H1 argument), with the difference confined to the
realizedFam/coefficient slots (D2) and the self side carrying A.
Then: class 4 (metricCorr_tame_h1 + lieOmega_pair_h1 factors), class 3
(build wOmega/vbMcd/ip pairs via app_h21_mul_lip), class 1 (ricciAA/DA
arm pairs), master five-way J1 telescope at fixed s, path-integrate via
lowC0_sub + jointContMDiff slice integrability, hook a1Lo_diff (Pair),
ONE exact refresh of LowBaseLip, focused-only until then.

CLASS-2 INTERNALS (lieCov_h2_tame, Action:10686): the unit =
appCc-composite of `lieCovPair g gm` (coefficient; H2-bounded by
`lcvPair_h2_low`, arg = convexPerturbation P = s.T with realizedFam ties)
and `lieCovR4 g T hd hdZ s` (the (A+A^2)-carrier; `lcvR4_h2_tame`,
rewritten by `lcvR4_eq`), composed through the H2Poly framework
(`hp_slot2` -> `hp_rsperm` (lieCovSigma) -> `hp_app_of` with
app_h2_mul g 2 6 2, then a negation step).  `lieCov_pair_h1` = telescope
over the two factors: [Pair_T - Pair_U](R4_T) + Pair_U([R4_T - R4_U]),
coefficient diff at H2/D2 (needs an `lcvPair` pair lemma — check
lcvPair_h2_low's file for an existing pair sibling), R4 diff at H1/D2
(needs `lcvR4` pair — its T-dependence is BOTH explicit (T-slots) and via
realizedFam; check whether the T-slot occurrences are at <=2 derivatives
so the difference stays D2).  An H1Poly analogue of the H2Poly plumbing
may be needed — mirror hp_slot2/hp_rsperm/hp_app_of one order down using
app_h21_mul_lip; keep them private in LowBaseLip.

SCOUT PHASE COMPLETE (2026-07-26).  `lieCovR4` (and likely `lieCovPair`)
are DEFINED in Analysis/Parabolic/RicciLinearization/
RiemannCoefficientPalatiniRefold.lean — which IS in this lane's claim set
(Palatini token).  Construction order for class 2:
(1) read lieCovR4's def in Palatini; verify its T-slots carry <= 2
    derivatives so the T/U difference is D2-safe at H1;
(2) build `lcvR4_pair_h1` (home: LowBaseLip preferred; Palatini only if
    the proof needs its privates);
(3) build the `lcvPair` pair lemma (H2/D2, mirroring lcvPair_h2_low
    Action:9138 — private, so re-derive from its public inputs);
(4) H1Poly mini-plumbing (hp_slot/hp_rsperm/hp_app one order down via
    app_h21_mul_lip, private in LowBaseLip);
(5) assemble `lieCov_pair_h1`.
Then classes 4 -> 3 -> 1 per the order ruling, master telescope,
path-integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CLASS-2 D2-SAFETY CRUX (the mathematical decision point): `lrSummand`
(Palatini:8399) shows lieCovR4's kernel contains EXPLICIT s.(1/2).
unitModel(iteratedCovGrad 2 T) terms alongside dLaCovKernel(realizedFam)
terms.  A naive J1 bound of R4_T - R4_U would need nabla^3(T-U) = D3 =
FORBIDDEN.  Resolution candidates, in order of evidence:
(a) STRONG (C1 precedent): re-express the class-2 difference through
    CONNECTION currency (connDiffLoweredCc / wXi / lipOmega differences
    carry only 1 derivative of T-U, so J1 of their difference is D2-safe)
    — exactly how the whole C1 chain (wXi_pair_h1 -> connSec_pair_h1 ->
    metricCorr_pair_h1) achieved D2-only, and what `lieOmega_pair_h1`
    already covers.  The explicit nabla^2-slots should cancel/refold
    against the edge subtraction (that is WHY the edge term exists) —
    look for the refolded form of the arm-edge unit in
    RefoldPairingCore/Palatini rather than pairing the raw lrR4.
(b) fallback: allocate the nabla^2(T-U)-slot at L^2 only (J0) and carry
    the derivative on the coefficient side — needs an app bound of shape
    J1(app) <= C * J2+(coeff) * J0(arg) + J1-part; check whether such a
    mixed-order app lemma exists before building.
If neither closes without D3, STOP per the allocation tripwire and
re-consult — do not fake it with H3/H4 smallness.

ARM-EQUATION ANCHORS for candidate (a): `covDerivArmField_eq_dLaCoeffField`
(Palatini, used ~:6562) identifies the arm with the dLa-coefficient field;
Palatini:1214 and :100 (`_toSection`) are the arm's defining equations; the
dLaCovKernel(realizedFam, g0) representation is the connection-currency
form.  The Palatini :6540-:6584 region is the OLD g_bg all-order family
(`a`/`ha_super` style) — reference ONLY, do not export or imitate its
wrapper shape (banned by the lane ruling).  Class-2 construction resumes:
read Palatini:1214 arm equation -> express the T/U arm-edge difference in
dLa/connection currency -> check the nabla^2-slots cancel against the edge
subtraction -> then lcvR4/lcvPair pair lemmas only for what survives.

D2-SAFETY MECHANISM HYPOTHESIS (final scout item, to VERIFY first next
window): `covDerivArmField_eq_dLaCoeffField` is rfl (Palatini:1212), so the
unit lives in dLa/connection currency; its gm-dependence differences are
D2-safe (kernel = 1 derivative of the metric difference).  The explicit
s.nabla^2 T slots in `lrSummand` (Palatini:8399) appear in the combination
unitModel(icg 2 T)[v0,v1,p,q] + [v0,v1,q,p] MINUS a swapped pair — if that
combination is the ANTISYMMETRIZED second covariant derivative, the Ricci
identity turns it into curvature x T (ZERO derivatives of T), making the
T/U difference D2-trivially safe.  VERIFY by reading lrSummand's full RHS
(:8406-8450) and the surrounding lrR4 lemmas; if confirmed, class 2 =
(i) dLa-kernel pair lemma (connection currency, reuse lieOmega/wXi
machinery) + (ii) the curvature-term pair (zeroth order, reuse
riem/trace2 pair machinery) — NO new D3-risk anywhere.  If refuted, fall
back to candidate (b) or STOP per the tripwire.

MECHANISM CONFIRMED (Palatini:8429-8465): `lrR4 = -(s/2).lrCurvF(T)
- lrQuadF(realizedFam(s))` — the nabla^2 T combinations reduce via
`lrICG2_argswap` + `lrRIC` (Ricci identity) to curvature-contracted T
(lrCurvF, LINEAR in T, low order) plus a QUADRATIC in
`PDE.DeTurck.connDiff(realizedFam, g0)` (lrQuadF; connDiff_symm
manipulations).  NO D3 anywhere.  Class-2 pair brick therefore =
(i) `lrCurvF` pair (linear in T; J1 diff <= D2 via curvature-contraction
    machinery — riem/trace2 pair style);
(ii) `lrQuadF` pair (two-factor connDiff telescope, J2-bdd x J1-pair via
    app_h21_mul_lip; the connection-difference J1 pair modulus is
    connSec_pair_h1 currency);
(iii) lcvPair coefficient pair (H2/D2, re-derive from lcvPair_h2_low's
    public inputs since it is private);
(iv) H1Poly mini-plumbing + assembly into `lieCov_pair_h1`.
This is the verified, allocation-clean route.  Everything above this line
in the note = complete durable state for the construction.

HOME RULING for class-2 factors: lrQuadF (:7530) / lrCurvF (:7793) /
lrR4 (:8378) are PRIVATE in Palatini — and Palatini IS in this lane's
claims.  Build the factor pair lemmas INSIDE
RiemannCoefficientPalatiniRefold.lean (private, beside the defs), export
ONE public composed result (suggested `lcvR4_pair_h1`-shape: J1(lrR4_T(s)
- lrR4_U(s)) <= canonical (B0 R*D2 + B1 R*A*D2)^2-type modulus, s in
Icc 0 1, both-state delta hypotheses) + if needed a public lcvPair pair.
AFTER adding the public export and BEFORE LowBaseLip reads it: one
single-module refresh `build -NoLakeLock
+DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold`
per the lane build discipline.  Then LowBaseLip's `lieCov_pair_h1`
consumes it with the lcvPair coefficient pair + H1Poly plumbing.

lrQuadF STRUCTURE (:7530): sum of 6 domDomCongr copies of lrQA/lrQB; the
unitModel form (:7540) shows each block = gm.inner( connDiff(gm,g0) ... ,
connDiff(gm,g0) ...) — THREE gm-dependencies per block (two connDiff slots
+ the inner).  Pair telescope per block = 3 summands, each difference in
connection or metric currency (D2-safe).  Need: Palatini-local dom-jet
permutation invariance at J1 (mirror dom_h1_lip — check whether Palatini
already has a dom/jet lemma family before adding), a connDiff pair modulus
in Palatini currency (or import the C1 public `connSec_pair_h1` shape —
check import direction: Palatini is UPSTREAM of C1Lip, so C1 publics are
NOT visible there; the connDiff pair must be re-derived Palatini-locally
from ITS OWN building blocks, or the composed export moves DOWN into
LowBaseLip where C1 publics are visible — RESOLVE by checking what
lrQuadF-pair actually needs: if only jet algebra + connDiff bilinearity,
Palatini-local is fine; if it needs wXi machinery, put the pair lemma in
LowBaseLip against the PUBLIC lrR4 equation instead — in that case export
from Palatini ONLY the lrR4 = -(s/2)CurvF - QuadF decomposition as a
public equation (cheapest possible export) and keep all pair work in
LowBaseLip.)  <- PREFERRED: minimal public export = the decomposition
equation `lrR4_eq_decomp`; everything else stays in LowBaseLip.
