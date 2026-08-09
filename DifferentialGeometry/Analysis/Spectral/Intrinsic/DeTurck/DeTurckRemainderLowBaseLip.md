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

BREAKTHROUGH (class-2 workload collapse): `lrOmegaHat g0 gm`
(Palatini:7326) is DEFINITIONALLY IDENTICAL to LowBaseLip's private
`lipOmega g gm` (:1860) — same appCcRS(slotInsertEndoCc 2
(fullRaisedEndoField gm g), domDomCongr (finRotate 3)
(connDiffLoweredCc g gm)).  Hence its J1 pair modulus IS
`lieOmega_pair_h1` (already proved) and its bdd is `lieOmega_bdd_h2` +
jet_mono.  `bdConnPair g0 gc = connDiff endo` (rfl apply :4354);
the armSlotEndoCc(bdConnPair) J2 coefficient moduli =
`LowBaseInternal.connLow_pair_h2` / `connLow_h2_bdd` (the prompt's reuse
list).  PALATINI EXPORT BAND (this session, all now public):
lrRiemW1/W2, lrCurvF(+unitModel), lrQuadF(+unitModel), lrQA/lrQB
(+unitModels), lrOmegaHat(+unitModel), bdConnPair(+apply), lieCovR4_eq
(rfl decomposition).  Remaining class-2 construction, ALL in LowBaseLip:
(1) `lipOmega_eq_hat : lipOmega g gm = lrOmegaHat g gm := rfl`;
(2) lrQA/lrQB pair at J1 = omega_pair_h1-pattern telescope (coeff J2 via
    connLow pair/bdd, arg J1 via lieOmega_pair_h1-internals);
(3) lrQuadF pair = 6-fold dom_h1_lip + jet_add over (2);
(4) lrCurvF pair = linear app_h21_mul_lip one-liner (T-U slot);
(5) `lcvR4_pair_h1` via lieCovR4_eq;
(6) lcvPair coefficient pair (H2) + H1Poly plumbing -> `lieCov_pair_h1`.

CLASS-2 CONSTRUCTION LOG (this session, all focused GREEN in LowBaseLip):
* `hat_eq_lip` (rfl: lrOmegaHat = lipOmega), `curvF_pair_h1` (linear
  J1<=C*J2(T-U)), `quadB_tel`/`quadA_tel` (two-slot app telescopes),
  `quad_pair_h1` (six-block lrQuadF telescope, abstract product form),
  `r4_pair_h1` (lieCovR4 pair via the public `lieCovR4_eq`, s in Icc01,
  conclusion C*(J2(T-U) + [J2(cU)*J1(hatD) + J2(cD)*J1(hatT)] at
  realizedFam metrics)).
* PALATINI EXPORTS this session: + lrPermA/B/C (the perms appear in
  lrQuadF's body and must be nameable downstream).  Palatini re-checked
  green + refreshed after each export batch.
* NEW DURABLE LESSON (cured a hard whnf wall at 1.6M heartbeats): in this
  file (respectTransparency false), the jet-chain arithmetic over tensor
  atoms MUST be closed by `linarith [explicit jet_add_lip applications +
  dom equations + prior bounds]` — `exact add_le_add_left ... _`,
  `gcongr`, and goal-side `nlinarith` all whnf-explode on the tensor
  atoms.  Fold every jet value with `set ... with h` and do the final
  numeric step on the folded real variables.
REMAINING for class 2: (iii) lcvPair coefficient pair at H2 (lieCovPair
is PUBLIC Palatini:3627; mirror the private lcvPair_h2_low Action:9138
from its public inputs), (iv) H1Poly mini-plumbing + `lieCov_pair_h1`
assembly plugging the concrete moduli (connLow pair/bdd for the
b-slots, lieOmega machinery via hat_eq_lip for the hat slots).

CLASS-2 FINAL ASSEMBLY MAP (all bridges verified):
* unit equation: `edgePair_eq` is rfl (Action-private but rfl —
  restate in Lip); `lieCov_residual` PUBLIC (Palatini:9033):
  armField(gm_s) - RefoldPairTraceFamily(q,eps,s) = (-1) . appCcRS 2 6 2
  (lieCovPair gm_s) (rsDom lieCovSigma (slotExtendIter 2 (lieCovR4 T s))),
  hyps = hTsymm + hs in Icc01 + hdelta_lt.
* Telescope: unitT - unitU = (-1).[app(PairDiff, X_T) + app(Pair gmU,
  X_T - X_U)], X_S = rsDom lieCovSigma (Ext^2 (lieCovR4 S s)).
* NEW GREEN this stretch: trace4_pair_h2 + trace4_h2_bdd (C2Lip, public,
  .2-projection of trace24_h2_lip + zero-state trick; C2Lip refreshed),
  lcvPair_eq_lip (rfl) + lcvPair_pair_h2 (Lip; telescope over
  trace2/trace4 pair+bdd via app_h2_mul_lip 6 4 2; NOTE trace producers
  are LowBaseInternal.* qualified).
* STILL TO BUILD (patterned): slot_h1_lip / rsperm_h1_lip (+ their _l2
  bases — mirror Action-private slot_l2 / rsperm_l2_sq, order-agnostic);
  lcvPair_h2_bdd (from trace bdds); H1 single-state bdds for
  CurvF/QuadF/lieCovR4 (via lieCovR4_eq; hat-bdd = lieOmega_bdd_h2 +
  jet_mono; coeff-bdd = LowBaseInternal.connLow_h2_bdd — VERIFY it
  matches armSlotEndoCc(bdConnPair)); realizedFam tie plumbing block
  (mirror lieCov_h2_tame's hδP/hcP/hP/hP2); then `lieCov_pair_h1`.
* Lean fixes this stretch: rw-first-occurrence hit LHS -> use conv_rhs;
  nlinarith product-monotonicity unreliable -> explicit mul_le_mul
  chains; trace producers need LowBaseInternal qualification.

GREEN TALLY (this session, LowBaseLip/C2Lip/Palatini):
lieOmega_pair_h1 (+app_h21_mul_lip/dom_h1_lip/omega_pair_h1),
riem_pair_h1, hat_eq_lip, curvF_pair_h1, quadB_tel, quadA_tel,
quad_pair_h1, r4_pair_h1, trace4_pair_h2, trace4_h2_bdd,
lcvPair_eq_lip, lcvPair_pair_h2, slot_l2_lip/slot_h1_lip,
rsperm_l2_lip/rsperm_h1_lip, lcvPair_h2_bdd — 14 public/private
declarations, every one focused GREEN; Palatini export band + 2
refreshes; C2Lip export + refresh.  NEXT (the class-2 capstone
`lieCov_pair_h1`): (a) H1 single-state bdds — CurvF (linear, trivial),
QuadF (six blocks; coeff J2 bdd = LowBaseInternal.connLow_h2_bdd
[VERIFY statement matches armSlotEndoCc(bdConnPair)], hat J1 bdd =
lieOmega_bdd_h2 + jet_mono via hat_eq_lip), R4 (via lieCovR4_eq);
(b) realizedFam tie plumbing (mirror lieCov_h2_tame's
hδP/hcP/hP/hP2 block, Action:10724-10760); (c) final telescope via
edgePair_eq (restate as rfl in Lip) + lieCov_residual (PUBLIC) +
app_h21_mul_lip 2 6 2 + slot_h1_lip x2 + rsperm_h1_lip + the pair/bdd
family.  Then classes 4 -> 3 -> 1, master telescope, lowC0_sub
integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CORRECTION (coefficient moduli for QuadF): `connLow_h2_bdd` bounds the
RANK-(3,3) `connLowOp` (public, Action:3388) — NOT the rank-(3,4)
`armSlotEndoCc 2 (bdConnPair g gm)` that lrQA/lrQB carry.  The QuadF
coefficient needs its own J2 pair/bdd: search Action for an
armSlotEndoCc jet-transfer (`armSlot.*h2|armSlot.*jet|EndoCc.*jet`) and
for how lcvPair_h2_low's siblings bounded arm-slot endo coefficients;
the revSlot pattern (`revSlot_bdd_h2`/`revSlot_pair_h2` for
slotInsertEndoCc(fullRaisedEndoField)) is the shape template — a
bdConnPair analogue (`armConn_bdd_h2`/`armConn_pair_h2`) may need
building from the connDiff H2 machinery (C1/C2 connSec/connLow family)
plus an endo-slot jet transfer.

QUADF-COEFFICIENT MODULI (the one genuinely new sub-brick left for the
class-2 capstone): J2 pair/bdd of `armSlotEndoCc 2 (bdConnPair g gm)`
(def MetricArmCoeffJetTower:1959, public) never existed — the H2 route
bounded the OUTER (6,2) lieCovPair only.  Build order: (1) grep C1/C2
for an H2 connDiffSection pair (`connSec_pair_h2`?) or derive from
`connLow_pair_h2` shapes; (2) the endo-slot jet transfer: mirror the
INTERNALS of `LowBaseInternal.revSlot_bdd_h2`/`revSlot_pair_h2` (they
bound slotInsertEndoCc 2 (fullRaisedEndoField) — same TYPE pattern,
different endo content); Palatini:4359
`bdConnDiffSection_eq_armSlotEndoCc_zero` is the s=0 endo/section
bridge (private, rfl-adjacent — check for an s=2 sibling or re-derive);
(3) useful splitters in Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound
(READ-ONLY): `connDiff_cocycle` (:91), `dLaCovKernel_backgroundSplit`
(:248).  Then assemble `lieCov_pair_h1` per the FINAL ASSEMBLY MAP.

ARMCONN MODULI ROUTE (refined): the two-state difference
bdConnPair(gmT) - bdConnPair(gmU) = connDiff(gmT,g) - connDiff(gmU,g)
collapses by `connDiff_cocycle` (DeTurckLieKernelL2JetBound:91, public,
READ-ONLY file) to a single connDiff(gmT,gmU)-type object; its H2 jet
is reachable through the connLowOp packaging: `connLow_pair_h2`
(PUBLIC, C2:4752) gives J2(connLowOp gT - connLowOp gU) <= (C*|T-U|)^2,
and the bridge connDiffSection <-> connLowOp lives in the
`connSec_eq_raise` (C1:892) / `connLower_unit` (Action:171, private —
re-derive if needed) family.  The armSlot jet transfer mirrors
`revSlot_bdd_h2`'s internals (C1:4501: bdd = pair vs base-state +
fr^2-factor; the pair's engine is `revSlot_pair_h2` nearby).  BDD:
zero-state trick as in revSlot_bdd_h2.  All pieces are in claimed or
read-only files; nothing blocks.

REVSLOT ENGINE DISSECTED (C1:4452): pair = `slotInsertEndoCc_sub`
(linearity) + `fullRev_sub` (endo diff = symmRaiseEndo(T-U)) +
`endo_slot_h2` (J2(slotInsert s=2 endo) <= fr^2 * J2(slotInsert 0 endo))
+ s=0 base identification.  For armConn: find/mirror the ARM-version
transfer (`armSlotEndoCc` vs `slotInsertEndoCc` are different
constructors — grep MetricArmCoeffJetTower's public surface for
`arm.*slot.*h2|armSlotEndoCc_sub|arm.*jet` and an endo-difference
linearity `armSlotEndoCc_sub`); the endo DIFFERENCE
bdConnPair(gmT)-bdConnPair(gmU) needs its own `fullRev_sub` analogue
(via connDiff_cocycle).  Everything else for `lieCov_pair_h1` is
assembled and green.  NEXT WINDOW: (1) grep the arm transfer; (2) write
armConn_pair/bdd; (3) H1 bdds (CurvF/QuadF/R4); (4) realizedFam ties;
(5) `lieCov_pair_h1`; then classes 4 -> 3 -> 1, master telescope,
lowC0_sub integral, a1Lo_diff hookup, exact refresh, notes, release
claims.

ARM JET TRANSFER — FINAL DEPTH (the ONE new pointwise lemma left for the
class-2 capstone): the endo_slot chain bottoms out at
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (pointwise fiber-norm
bound under iterated covariant gradients, single-endo slotInsert).  The
arm version `rfns_iteratedCovGrad_armSlotEndoCc_le_*` does not exist;
mirror the slotInsert one (locate + read its proof; likely in the
JetTower/NablaOnTensors layer) with the bilinear endo's extra slot paid
by a v0-basis expansion (one extra fr factor).  Wrappers after it are
mechanical (arm_slot_l2 -> arm_h1/h2, mirroring endo_slot_l2/h2 which
are fully dissected above).  `armSlot_sub_lip` is GREEN (15th this
session; proof pattern = rs-rank ext + fib-level hfib via
armSlotFib_apply_eval + slotInsertEndoFib_sub_left + dsimp-only for the
beta-redex; synthInstance+maxHeartbeats bumps needed).

ARM TRANSFER — COMPLETE IMPLEMENTATION SCRIPT (all proofs dissected):
(1) `armSlot_succ_eq` (new, ~60-80 lines, Lip-private): the arm analogue
    of `slotInsertEndoCc_succ_eq_reindex_slotExtend` (JetTower:2725,
    private — read its proof as template): armSlotEndoCc (s+1) Arm =
    rsDomDomCongr-reindex of slotExtend (armSlotEndoCc s Arm); prove at
    unitModel level via armSlotFib_apply_eval on both sides (the same
    ext+dsimp pattern that landed armSlot_sub_lip).
(2) `rfns_icg_armSlot_le` (new, ~50 lines): VERBATIM mirror of
    `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (JetTower:2795,
    PUBLIC — its induction consumes only the succ-equation +
    `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (public) +
    `rfns_iteratedCovGrad_slotExtend_le` (public)), with base case s=0.
(3) `arm_l2_lip` / `arm_h1_lip` / `arm_h2_lip` wrappers (~40 lines,
    mirror endo_slot_l2/endo_slot_h2 which are fully dissected).
(4) The s=0 base: armSlotEndoCc 0 (bdConnPair g gm) vs
    connDiffSection gm g — `bdConnDiffSection_eq_armSlotEndoCc_zero`
    (JetTower:4359, private, rfl-adjacent — restate in Lip).
(5) armConn moduli: pair via armSlot_sub_lip + connDiff_cocycle +
    transfer to s=0 + connSec H1/H2 machinery; bdd via zero-state trick.
Then `lieCov_pair_h1` per the FINAL ASSEMBLY MAP, classes 4/3/1, master
telescope, integral, a1Lo hookup, exact refresh.

ARM SUCC-EQUATION DERIVATION NOTE: the slotInsert succ template
(JetTower:2725-2792, full text dissected) proves the Cc equation by
ext-chain + `slotInsertEndoFib_apply_eval` + slotExtendFib_apply_eval +
explicit Fin.cases permutation bookkeeping (swap01 on both r and s
sides).  For the ARM version the constructor is NON-square
(g (s+1) (s+2)); derive the correct reindex/rsDom permutations at the
MODEL level from `armSlotFib_apply_eval` (arm s = sIEF (s+1) 0 at
(Arm v0) with vecTail) vs slotExtend-of-arm-s — write the candidate
equation first at unitModel on explicit vectors, read off the two
permutations, then run the ext-chain.  CAUTION: do this with a fresh
context and the :2725 template open side-by-side; the Fin.cases block
is unforgiving.  After it: the rfns mirror induction, the l2/h1/h2
wrappers, then armConn moduli and the capstone — all dissected above.

ARM SUCC-EQUATION — MODEL-LEVEL DERIVATION (s-side DONE):
`slotExtendFib_apply_eval` (OperatorFieldCovariantCalculus:293):
toModel(slotExtendFib A D)(cons v0 vs) = toModel(A (curry D v0)) vs —
the new slot SLICES D first.  Hence
slotExt(armFib s Arm) D' [w0,w1,w2,w3..] = D'[w0, Arm w1 w2, w3, ...]
vs armFib (s+1) Arm D' [v0,v1,v2,v3..] = D'[Arm v0 v1, v2, v3, ...].
Identification (v0,v1)=(w1,w2), v2=w0, rest equal: the INPUT-side
(Fin (s+3)) permutation is the 3-cycle sigma = (swap 0 1).trans
(swap 1 2)  [check: 0->1->2, 1->0->0, 2->2->1 — i.e. w = v after sigma]
— one order deeper than the template's swap01 because the arm eats TWO
slots.  The D'-slot (rsDom) permutation: ArmRes at 0 vs at 1 => swap01
(same as template).  REMAINING: derive the r-side (reindexCoeffGen rho,
Fin (s+2)) by the same model calc on the OPERATOR-as-tensor encoding
(check how reindexCoeffGen acts in the template's :2757 step), then run
the ext-chain with the :2725 template's Fin.cases style (expect one
extra case layer from the 3-cycle).

R-SIDE PINNED: `reindexCoeffFibGen_apply`
(Tensor/CovGrad/RicciDeTurckSectionDifference.lean:4036, PUBLIC):
reindexCoeffFibGen r s rho x A D = A (ofModel (domDomCongr rho
(toModel D))) — the r-side perm acts on the OPERATOR'S ARGUMENT D by
model domDomCongr.  So in the arm succ-equation the rho on Fin (s+2)
(the D'-side) is the swap01 moving the sliced/passthrough D'-slot past
the Arm-output slot (same role as the template's rsDom swap01), and the
sigma on Fin (s+3) (the v-side) is the derived 3-cycle
(swap 0 1).trans (swap 1 2).  ALL permutations for the arm
succ-equation are now determined; write the equation with these and run
the :2725-template ext-chain (expect one extra Fin.cases layer).
Estimated remaining to (N): class-2 capstone ~550 lines; classes 4/3/1
~800-1100; master telescope + integral ~250-400; a1Lo hookup ~100-200;
refreshes/notes/claims; then the endpoint wiring session.

ARM JET TRANSFER — COMPLETE (session count 20 greens): armSlot_sub_lip,
armSlot_succ_lip (perms: rho = swap01 on Fin (s+2), sigma =
(swap 0 1).trans (swap 1 2) on Fin (s+3); after the simp-normalization
chain [TensorMultilinear.tensor0S_curry_apply_eval — NOTE the namespace
qualifier, unknown-identifier was the root cause of 4 failed rw
attempts — , toModel_ofModel, domDomCongr_apply] the three Fin.cases
branches closed by rfl), rfns_arm_le_lip (mirror induction via
both_eq + slotExtend_le), arm_l2/h1/h2_lip wrappers.  NEXT: restate
the s=0 base `bdConnDiffSection_eq_armSlotEndoCc_zero` (JetTower:4359
private) in Lip, then armConn pair/bdd moduli, H1 bdds, ties, capstone.

ALLOCATION-FLIP DECISION (armConn moduli, final): with
`bdConnDiffSection_eq_armSlotEndoCc_zero` now PUBLIC (Palatini:4359,
one more export -> re-check + refresh Palatini) and arm_h1/h2_lip green,
the QuadF telescope second term flips allocation: cD at J1 (via
armSlot_sub_lip + arm_h1_lip + base-eq -> J1(connDiffSection diff) =
`connSec_pair_h1` C1-public, D2-safe) x hatT at J2-bdd
(`lieOmega_bdd_h2`).  Needs `app_h12_mul_lip` (mirror app_h21_mul_lip
using PUBLIC `appRS_h1_h2_h1` H1H2AppCcRS:390).  First term unchanged:
cU at J2-bdd x hatD at J1-pair; cU J2-bdd = arm_h2_lip + base-eq +
a connDiffSection J2 single-state bdd (check C1 for `connSec`-bdd at
H2; if only H1 exists, flip term 1 too: cU at J1-bdd x hatD at J2-pair
is FORBIDDEN (lieOmega_pair_h2 carries D3) -> so term 1 needs the
connSec H2 BDD (single-state, no pair) — much cheaper than a pair;
build from connSec_eq_raise + raise jet bdd if missing.)
REVISION NEEDED: quad_pair_h1's statement (already green) has both
c-slots at J2 — either keep it and supply the J2 moduli, or restate
with the flipped allocation; DECIDE when the moduli inventory is
complete.

SESSION UPDATE (allocation flip + armConn moduli, in flight):
- `app_h12_mul_lip` GREEN (mirror of app_h21 via public appRS_h1_h2_h1).
- FLIP EXECUTED: `quad_pair_h1` + `r4_pair_h1` RESTATED with cD at J1 x
  hatT at J2 (D3-free: cD@J2 would need wXi_sub_tame H2 which carries D3).
  Both GREEN post-flip (needed explicit (m := k) levels in the
  jet_nonneg_lip linarith hints -- implicit-level hints produce
  metavariable atoms linarith cannot match).
- dom_h2_lip ALREADY EXISTED at Lip:1815 (do not re-add).
- Palatini `bdConnDiffSection_eq_armSlotEndoCc_zero` now PUBLIC,
  refreshed. C1 `connSec_self_h2` (J2 connSec = J2 wXi) now PUBLIC,
  focused-check green; +C1 refresh in flight.
- INSERTED (pending check): `armU_bdd_h2` (arm@J2 single-state via
  arm_h2_lip + base-eq + connSec_self_h2 + wXi_self_tame; modulus
  (fr*Bs R*A)^2), `armD_pair_h1` (arm@J1 two-state via armSlot_sub +
  arm_h1_lip + base-eq x2 + connSec_pair_h1; modulus
  (fr*B0R*D2 + fr*B1R*A*D2)^2), `hat_bdd_h2` (J2 lrOmegaHat via
  hat_eq_lip + lieOmega_bdd_h2).
- NEXT after these check: CurvF single-state H1 bdd (linear in T-U =
  use curvF_pair_h1 with U := 0? CurvF is linear in T: curvF_pair
  bounds J1(CF_T - CF_U) by J2(T-U); single-state = pair with U=0 IF
  lrCurvF g 0 = 0 -- check; else direct), then the class-2 capstone
  `lieCov_pair_h1` assembly per FINAL ASSEMBLY MAP.

CAPSTONE PLAN (lieCov_pair_h1, all ingredients verified):
- Unit: class2(T) := armField(gm_s) - edgeLiePairFam(T,lieRefoldQ,lieRefoldEps,s)
  = residual(T) by edgePair_eq (Action-private rfl -> RESTATE in Lip as rfl)
  + lieCov_residual (Palatini PUBLIC; hyps hδ_lt/hδ/hδZ/hTsymm/hs).
  residual(T) = (-1)•app 2 6 2 (Pair gm_s) (X_T), X_T = rsDom 2 6 lieCovSigma
  (slotExtendIter 0 4 2 R4_T); slotExtendIter 2 = slotExtend∘slotExtend RFL.
- Telescope: res_T - res_U = (-1)•[app(PairDiff, X_T) + app(Pair_U, Xdiff)].
- J1 bounds: jet_smul ((-1)²) + jet_add; term1 app_h21 2 6 2:
  J2(PairDiff)=lcvPair_pair_h2 (ρ-ball hyp, Hs-norm currency) ×
  J1(X_T) ≤ fr²·J1(R4_T) [rsperm_h1= + slot_h1×2] ≤ fr²(DrR(A+A²))² [r4_bdd_h1];
  term2: J2(Pair_U)=lcvPair_h2_bdd (ρ-ball) × J1(Xdiff) ≤ fr²·J1(R4diff)
  [same transfers via armSlot? NO — Xdiff transfers termwise: rsDom/slotExt are
  LINEAR: Xdiff = rsDom(Ext²(R4_T − R4_U)) needs slotExtend_sub + rsDom_sub
  (grep or prove rfl/ext) then ≤ fr²·(r4_pair_h1 RHS, discharged by
  armU_bdd+armD_pair+hat_bdd+lieOmega_pair moduli at P/Q].
- Currency: conclusion (B R * (1 + A + A ^ 2) ^ 2 * D2) ^ 2; all products
  folded by nlinarith on set-folded reals with explicit product-nonneg hints
  (REMEMBER (m := k) explicit levels in jet_nonneg_lip hints).
- Plumbing ×2 (P=s•T, Q=s•U) verbatim from Lip:588-652 idiom.
- MISSING-CHECK LIST before writing: slotExtend_sub / rsDomDomCongrSection_sub
  linearity lemmas; lcvPair_pair_h2 full conclusion tail; r4_pair_h1 arm/hat
  term discharge order.

X-TRANSFER GREEN (covX_bdd_h1 + covX_pair_h1) + armU/armD/hat + A/B/C
(curvF_zero/curvF_bdd/quadF_bdd/r4_bdd) + edgePair_eq_lip + rsperm_sub_lip
ALL GREEN.  Lessons: (1) hat_bdd/quadF placement must be AFTER
lieOmega_bdd_h2 (:~4300) -- forward-ref moved wholesale; (2) armD needs
synthInstance.maxHeartbeats 1000000 (armSlot_sub ContinuousAdd synth);
(3) THE whnf-timeout culprit in big folds = final-calc `nlinarith` over
composite scalar monomials -- fix = explicit `hsum` linarith combination
+ `le_of_eq ... ring` factoring split (same lesson as quad_pair, now
confirmed twice); (4) rsperm_sub_lip closes by simp only [rsDomDomCongr]
+ rfl (comp_sub unused); (5) sqrt-constant ring tails need `show`-cast
to isolate sqrt^2 before rw [Real.sq_sqrt].
NEXT: capstone lieCov_pair_h1 assembly (short now): units via
edgePair_eq_lip + lieCov_residual (rw [<- hgmT] at hUT to match
set-folded goal), telescope via appCcRS_sub_left/right + module,
app_h21_mul_lip 2 6 2, lcvPair_pair/bdd at (P,Q,gmT,gmU) with Hs-ball
plumbing (:653 idiom), covX pair/bdd, fold to
B R * ((1+A+A^2)^4 * (D2^2 + N^2)).

*** CLASS-2 CAPSTONE `lieCov_pair_h1` GREEN (first try, 126.5s) ***
Conclusion: J1(class2diff @ fixed s) <= B R * ((1+A+A^2)^4 * (D2^2+N^2))
(two-currency: D2 = jet H2 difference, N = Hs2 spectral difference norm;
sizes R/A symmetric both states incl. hU3; rho-ball = min(rho_pair,
rho_bdd) on Hs2 T/U).  Whole chain green: unit (edgePair_eq_lip rfl +
lieCov_residual public) -> telescope (appCcRS_sub_left/right + module)
-> app_h21 2 6 2 -> lcvPair pair/bdd + covX pair/bdd.
CLASS 2 OF 5 DONE.  Ordering ruling: next 4 (lc0AMix) -> 3 (lc0VB) ->
1 (ricciGoodLow) -> master telescope (selfLow_parts, 5-term jet_add
ladder at fixed s) -> path integral (lowC0Diff via
iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame
:517) -> a1Lo_diff hookup (Pair).

CLASS-4 (lc0AMix) PLAN — skeleton verified from LieCorr0AMixRefold:
- `amix_refold_rf` PUBLIC: lc0AMix = lc0AMixFormRF = 2•(Half(perm2) +
  Half(swap*perm2)); Half(σ) = app 2 4 2 (Tr2 σ) (app 2 6 4 (Tr4 perm1)
  (app 2 3 6 (Ext³ mcd) (app 2 5 3 (Tr3 permQ) (Ext² mcd)))) where
  Tr_p(σ) = reindexCoeffGen (pureTrace g gm p) σ (MOVING cometric,
  gm-dep!), mcd = metricConnDiffLoweredCc g gm g (both slots coincide at
  gB=g₀=g).
- mcd_pair_h1 DONE GREEN in C1 (D2-only modulus (B0R·D2+B1R·A·D2)²;
  via mcd_sub_eq + wXi_pair_h1 + metricCorr_pair_h1 [pre-existing
  PUBLIC!] + wXi_h2_low + jet folding; 140.9s).  mcd_pair_h2 is
  D3-infected — never use in C0 lane.
- Telescope: 5 moving factors per half → 5 difference terms; allocation
  per term: difference factor at its level (traces at J2-pair D2-safe;
  mcd at J1-pair via mcd_pair_h1 when innermost, else J2?? NO — mcd at
  J2-pair is D3 ⟹ mcd-difference must always sit in the J1 slot of an
  h21 app; traces-diff can sit at J2 (h21 outer slot).  Nesting: outer
  app J1 conclusion via app_h21 (Φ@J2 × W@J1): put ALL trace-diffs in
  Φ-slots (J2-pair) and mcd-diffs inside W-chains at J1.  The two
  mcd-slot diff terms need J1(app-chain diff) recursion: inner app 2 5 3
  (Tr3, Ext²mcd): diff in mcd → J1 via app_h12?? app 2 5 3 with W=Ext²
  mcdDiff at J2?? — NO: use app_h21 with Φ=Tr3@J2-bdd × W=Ext²(mcdDiff)
  @J1 [slot transfer + mcd_pair_h1] ✓; diff in Tr3 → Φ=Tr3Diff@J2-pair ×
  W=Ext²(mcd_U)@J1-bdd ✓.
- INVENTORY TO CHECK/BUILD: trace3_pair_h2 + trace3_h2_bdd (trace2/4
  exist); J2 slot transfer (slot_h2_lip) for Ext²/Ext³; reindexCoeffGen
  jet transfer (Tr_p = reindex(pureTrace p, σ) — need jet equality or
  transfer under reindexCoeffGen at J1/J2 — check JetTower rfns
  machinery); mcd J1/J2 single bdd (mcd_h2_bdd C1 public — check shape);
  then 5-term telescope + (1+A+A²)-currency fold; conclusion target
  J1(lc0AMix g gmT g − lc0AMix g gmU g) ≤ B R·((1+A+A²)^k·D2²)-form
  (no N-term — amix has no Hs-ball currency unless trace moduli demand
  ρ-balls — trace2/4 moduli DO carry ρ (Hs-ball) → conclusion carries
  ρ-ball hyps like class 2).

*** CLASS-4 (lc0AMix) COMPLETE ***: mcd_pair_h1 (C1) + trace3 family
(C2: insert4_jet_c2/trace3_h2_lip/trace3_pair_h2/trace3_h2_bdd) +
slot_h2_lip/reindex_jet_lip/reindex_sub_lip/trPair_sub_lip/trPair_jet_lip
+ amixHalf_pair_h1 (five-level telescope, 328.6s) + amix_pair_h1
(FormRF wrapper, 16*Bh constant, 299.2s) ALL GREEN.  Currency:
B R * ((1+A+A^2)^4 * (D2^2+N^2)) — same as class 2.
Lessons: perms are LieCorr0Core.* (TameLipschitz's copies are private);
`simp only [K]` can close goals fully (drop trailing ring on "No goals");
S4b needed DUAL constants (Ca4-J1 vs Ca4b-J2 chains).
STATE: classes 2/4/5? green; 3 (lc0VB) + 1 (ricciGoodLow) recon+draft
DISPATCHED TO OPUS subagents (drafts land in scratchpad opus_vb/ and
opus_good/); NEXT after integration = master five-class telescope at
fixed s (selfLow_parts), lowC0Diff path integral
(iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame),
a1Lo_diff hookup (Pair file).

MULTI-AGENT PHASE (user upgraded to ultra; Opus dispatch authorized):
- GREEN so far this phase: selfLow_sub_parts (master telescope EQUATION,
  module not abel for (-2:ℝ)•), vb safe helpers
  (rsperm_h2_lip/ipHead/ip_form_lip/ip_sub_lip).
- OPUS RECON DONE: class-3 (vb): refold vb_refold_rf PUBLIC
  (LieCorr0VBRefold.lean:120), 3-term telescope, budget (1+A+A²)⁴ EXACT;
  draft at scratchpad opus_vb/vb_pair_h1_draft.lean (811 lines);
  prerequisites M1/M2 = trace1_pair_h2/trace1_h2_bdd (C2) + M3 =
  vbmcd_perm_eq (vbMcdArm = rsDom(VBPerm)(Ext(mcd)); the in-tree
  vbMcdArm_rel + vbPK_eq_slotExt are PRIVATE in READ-ONLY
  LieCorr0CoeffL2JetBound.lean:1082 — must re-derive at model level in
  C1 (public) using tensor0SProdKappaFib/slotExtendFib_apply_eval).
- class-1 (good): ricciGoodLow = ccInputSymm(AA + DA); (s•T)-slot enters
  ONLY via covGrad in DA (one D2-term); AA = connSec-insertions
  (connDiffContrInsertionField_eq_reindex_slotExtend_two etc. PUBLIC) ×
  trace2; missing: dagLow_bdd_h2 (recommend claiming Action +
  publicizing dagLow_h2_rf + connLow_h3_rf), fullSlot_bdd_h2 +
  fullSlot_pair_h1 (Opus building in C1 now; check gInvDiffRaisedEndoField
  relation); draft at opus_good/good_pair_h1_draft.lean (~1180 lines,
  AA arm + capstone complete, gaps marked sorry).
- BUILDERS IN FLIGHT: Opus@C2 trace1 family (token 99f2...), Opus@C1
  fullSlot bricks (token e2aa...).  QUEUED: Opus@C1 vbmcd_perm_eq
  re-derivation (after fullSlot agent frees C1).
- INTEGRATION ORDER: trace1 lands -> I insert vb body (minus
  vbmcd-dependents until bridge) into Lip; fullSlot+dagLow land ->
  good_pair_h1; then master five-class J1 bound at fixed s (uses
  selfLow_sub_parts + 5 class moduli), c0Diff_tame (mirror c1Diff_tame
  :517-746, engine path_jetL2_le g 2 2 1), lowBaseDiff_c0 already wired,
  final a1Lo_diff-style Pair endpoint.

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

BREAKTHROUGH (class-2 workload collapse): `lrOmegaHat g0 gm`
(Palatini:7326) is DEFINITIONALLY IDENTICAL to LowBaseLip's private
`lipOmega g gm` (:1860) — same appCcRS(slotInsertEndoCc 2
(fullRaisedEndoField gm g), domDomCongr (finRotate 3)
(connDiffLoweredCc g gm)).  Hence its J1 pair modulus IS
`lieOmega_pair_h1` (already proved) and its bdd is `lieOmega_bdd_h2` +
jet_mono.  `bdConnPair g0 gc = connDiff endo` (rfl apply :4354);
the armSlotEndoCc(bdConnPair) J2 coefficient moduli =
`LowBaseInternal.connLow_pair_h2` / `connLow_h2_bdd` (the prompt's reuse
list).  PALATINI EXPORT BAND (this session, all now public):
lrRiemW1/W2, lrCurvF(+unitModel), lrQuadF(+unitModel), lrQA/lrQB
(+unitModels), lrOmegaHat(+unitModel), bdConnPair(+apply), lieCovR4_eq
(rfl decomposition).  Remaining class-2 construction, ALL in LowBaseLip:
(1) `lipOmega_eq_hat : lipOmega g gm = lrOmegaHat g gm := rfl`;
(2) lrQA/lrQB pair at J1 = omega_pair_h1-pattern telescope (coeff J2 via
    connLow pair/bdd, arg J1 via lieOmega_pair_h1-internals);
(3) lrQuadF pair = 6-fold dom_h1_lip + jet_add over (2);
(4) lrCurvF pair = linear app_h21_mul_lip one-liner (T-U slot);
(5) `lcvR4_pair_h1` via lieCovR4_eq;
(6) lcvPair coefficient pair (H2) + H1Poly plumbing -> `lieCov_pair_h1`.

CLASS-2 CONSTRUCTION LOG (this session, all focused GREEN in LowBaseLip):
* `hat_eq_lip` (rfl: lrOmegaHat = lipOmega), `curvF_pair_h1` (linear
  J1<=C*J2(T-U)), `quadB_tel`/`quadA_tel` (two-slot app telescopes),
  `quad_pair_h1` (six-block lrQuadF telescope, abstract product form),
  `r4_pair_h1` (lieCovR4 pair via the public `lieCovR4_eq`, s in Icc01,
  conclusion C*(J2(T-U) + [J2(cU)*J1(hatD) + J2(cD)*J1(hatT)] at
  realizedFam metrics)).
* PALATINI EXPORTS this session: + lrPermA/B/C (the perms appear in
  lrQuadF's body and must be nameable downstream).  Palatini re-checked
  green + refreshed after each export batch.
* NEW DURABLE LESSON (cured a hard whnf wall at 1.6M heartbeats): in this
  file (respectTransparency false), the jet-chain arithmetic over tensor
  atoms MUST be closed by `linarith [explicit jet_add_lip applications +
  dom equations + prior bounds]` — `exact add_le_add_left ... _`,
  `gcongr`, and goal-side `nlinarith` all whnf-explode on the tensor
  atoms.  Fold every jet value with `set ... with h` and do the final
  numeric step on the folded real variables.
REMAINING for class 2: (iii) lcvPair coefficient pair at H2 (lieCovPair
is PUBLIC Palatini:3627; mirror the private lcvPair_h2_low Action:9138
from its public inputs), (iv) H1Poly mini-plumbing + `lieCov_pair_h1`
assembly plugging the concrete moduli (connLow pair/bdd for the
b-slots, lieOmega machinery via hat_eq_lip for the hat slots).

CLASS-2 FINAL ASSEMBLY MAP (all bridges verified):
* unit equation: `edgePair_eq` is rfl (Action-private but rfl —
  restate in Lip); `lieCov_residual` PUBLIC (Palatini:9033):
  armField(gm_s) - RefoldPairTraceFamily(q,eps,s) = (-1) . appCcRS 2 6 2
  (lieCovPair gm_s) (rsDom lieCovSigma (slotExtendIter 2 (lieCovR4 T s))),
  hyps = hTsymm + hs in Icc01 + hdelta_lt.
* Telescope: unitT - unitU = (-1).[app(PairDiff, X_T) + app(Pair gmU,
  X_T - X_U)], X_S = rsDom lieCovSigma (Ext^2 (lieCovR4 S s)).
* NEW GREEN this stretch: trace4_pair_h2 + trace4_h2_bdd (C2Lip, public,
  .2-projection of trace24_h2_lip + zero-state trick; C2Lip refreshed),
  lcvPair_eq_lip (rfl) + lcvPair_pair_h2 (Lip; telescope over
  trace2/trace4 pair+bdd via app_h2_mul_lip 6 4 2; NOTE trace producers
  are LowBaseInternal.* qualified).
* STILL TO BUILD (patterned): slot_h1_lip / rsperm_h1_lip (+ their _l2
  bases — mirror Action-private slot_l2 / rsperm_l2_sq, order-agnostic);
  lcvPair_h2_bdd (from trace bdds); H1 single-state bdds for
  CurvF/QuadF/lieCovR4 (via lieCovR4_eq; hat-bdd = lieOmega_bdd_h2 +
  jet_mono; coeff-bdd = LowBaseInternal.connLow_h2_bdd — VERIFY it
  matches armSlotEndoCc(bdConnPair)); realizedFam tie plumbing block
  (mirror lieCov_h2_tame's hδP/hcP/hP/hP2); then `lieCov_pair_h1`.
* Lean fixes this stretch: rw-first-occurrence hit LHS -> use conv_rhs;
  nlinarith product-monotonicity unreliable -> explicit mul_le_mul
  chains; trace producers need LowBaseInternal qualification.

GREEN TALLY (this session, LowBaseLip/C2Lip/Palatini):
lieOmega_pair_h1 (+app_h21_mul_lip/dom_h1_lip/omega_pair_h1),
riem_pair_h1, hat_eq_lip, curvF_pair_h1, quadB_tel, quadA_tel,
quad_pair_h1, r4_pair_h1, trace4_pair_h2, trace4_h2_bdd,
lcvPair_eq_lip, lcvPair_pair_h2, slot_l2_lip/slot_h1_lip,
rsperm_l2_lip/rsperm_h1_lip, lcvPair_h2_bdd — 14 public/private
declarations, every one focused GREEN; Palatini export band + 2
refreshes; C2Lip export + refresh.  NEXT (the class-2 capstone
`lieCov_pair_h1`): (a) H1 single-state bdds — CurvF (linear, trivial),
QuadF (six blocks; coeff J2 bdd = LowBaseInternal.connLow_h2_bdd
[VERIFY statement matches armSlotEndoCc(bdConnPair)], hat J1 bdd =
lieOmega_bdd_h2 + jet_mono via hat_eq_lip), R4 (via lieCovR4_eq);
(b) realizedFam tie plumbing (mirror lieCov_h2_tame's
hδP/hcP/hP/hP2 block, Action:10724-10760); (c) final telescope via
edgePair_eq (restate as rfl in Lip) + lieCov_residual (PUBLIC) +
app_h21_mul_lip 2 6 2 + slot_h1_lip x2 + rsperm_h1_lip + the pair/bdd
family.  Then classes 4 -> 3 -> 1, master telescope, lowC0_sub
integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CORRECTION (coefficient moduli for QuadF): `connLow_h2_bdd` bounds the
RANK-(3,3) `connLowOp` (public, Action:3388) — NOT the rank-(3,4)
`armSlotEndoCc 2 (bdConnPair g gm)` that lrQA/lrQB carry.  The QuadF
coefficient needs its own J2 pair/bdd: search Action for an
armSlotEndoCc jet-transfer (`armSlot.*h2|armSlot.*jet|EndoCc.*jet`) and
for how lcvPair_h2_low's siblings bounded arm-slot endo coefficients;
the revSlot pattern (`revSlot_bdd_h2`/`revSlot_pair_h2` for
slotInsertEndoCc(fullRaisedEndoField)) is the shape template — a
bdConnPair analogue (`armConn_bdd_h2`/`armConn_pair_h2`) may need
building from the connDiff H2 machinery (C1/C2 connSec/connLow family)
plus an endo-slot jet transfer.

QUADF-COEFFICIENT MODULI (the one genuinely new sub-brick left for the
class-2 capstone): J2 pair/bdd of `armSlotEndoCc 2 (bdConnPair g gm)`
(def MetricArmCoeffJetTower:1959, public) never existed — the H2 route
bounded the OUTER (6,2) lieCovPair only.  Build order: (1) grep C1/C2
for an H2 connDiffSection pair (`connSec_pair_h2`?) or derive from
`connLow_pair_h2` shapes; (2) the endo-slot jet transfer: mirror the
INTERNALS of `LowBaseInternal.revSlot_bdd_h2`/`revSlot_pair_h2` (they
bound slotInsertEndoCc 2 (fullRaisedEndoField) — same TYPE pattern,
different endo content); Palatini:4359
`bdConnDiffSection_eq_armSlotEndoCc_zero` is the s=0 endo/section
bridge (private, rfl-adjacent — check for an s=2 sibling or re-derive);
(3) useful splitters in Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound
(READ-ONLY): `connDiff_cocycle` (:91), `dLaCovKernel_backgroundSplit`
(:248).  Then assemble `lieCov_pair_h1` per the FINAL ASSEMBLY MAP.

ARMCONN MODULI ROUTE (refined): the two-state difference
bdConnPair(gmT) - bdConnPair(gmU) = connDiff(gmT,g) - connDiff(gmU,g)
collapses by `connDiff_cocycle` (DeTurckLieKernelL2JetBound:91, public,
READ-ONLY file) to a single connDiff(gmT,gmU)-type object; its H2 jet
is reachable through the connLowOp packaging: `connLow_pair_h2`
(PUBLIC, C2:4752) gives J2(connLowOp gT - connLowOp gU) <= (C*|T-U|)^2,
and the bridge connDiffSection <-> connLowOp lives in the
`connSec_eq_raise` (C1:892) / `connLower_unit` (Action:171, private —
re-derive if needed) family.  The armSlot jet transfer mirrors
`revSlot_bdd_h2`'s internals (C1:4501: bdd = pair vs base-state +
fr^2-factor; the pair's engine is `revSlot_pair_h2` nearby).  BDD:
zero-state trick as in revSlot_bdd_h2.  All pieces are in claimed or
read-only files; nothing blocks.

REVSLOT ENGINE DISSECTED (C1:4452): pair = `slotInsertEndoCc_sub`
(linearity) + `fullRev_sub` (endo diff = symmRaiseEndo(T-U)) +
`endo_slot_h2` (J2(slotInsert s=2 endo) <= fr^2 * J2(slotInsert 0 endo))
+ s=0 base identification.  For armConn: find/mirror the ARM-version
transfer (`armSlotEndoCc` vs `slotInsertEndoCc` are different
constructors — grep MetricArmCoeffJetTower's public surface for
`arm.*slot.*h2|armSlotEndoCc_sub|arm.*jet` and an endo-difference
linearity `armSlotEndoCc_sub`); the endo DIFFERENCE
bdConnPair(gmT)-bdConnPair(gmU) needs its own `fullRev_sub` analogue
(via connDiff_cocycle).  Everything else for `lieCov_pair_h1` is
assembled and green.  NEXT WINDOW: (1) grep the arm transfer; (2) write
armConn_pair/bdd; (3) H1 bdds (CurvF/QuadF/R4); (4) realizedFam ties;
(5) `lieCov_pair_h1`; then classes 4 -> 3 -> 1, master telescope,
lowC0_sub integral, a1Lo_diff hookup, exact refresh, notes, release
claims.

ARM JET TRANSFER — FINAL DEPTH (the ONE new pointwise lemma left for the
class-2 capstone): the endo_slot chain bottoms out at
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (pointwise fiber-norm
bound under iterated covariant gradients, single-endo slotInsert).  The
arm version `rfns_iteratedCovGrad_armSlotEndoCc_le_*` does not exist;
mirror the slotInsert one (locate + read its proof; likely in the
JetTower/NablaOnTensors layer) with the bilinear endo's extra slot paid
by a v0-basis expansion (one extra fr factor).  Wrappers after it are
mechanical (arm_slot_l2 -> arm_h1/h2, mirroring endo_slot_l2/h2 which
are fully dissected above).  `armSlot_sub_lip` is GREEN (15th this
session; proof pattern = rs-rank ext + fib-level hfib via
armSlotFib_apply_eval + slotInsertEndoFib_sub_left + dsimp-only for the
beta-redex; synthInstance+maxHeartbeats bumps needed).

ARM TRANSFER — COMPLETE IMPLEMENTATION SCRIPT (all proofs dissected):
(1) `armSlot_succ_eq` (new, ~60-80 lines, Lip-private): the arm analogue
    of `slotInsertEndoCc_succ_eq_reindex_slotExtend` (JetTower:2725,
    private — read its proof as template): armSlotEndoCc (s+1) Arm =
    rsDomDomCongr-reindex of slotExtend (armSlotEndoCc s Arm); prove at
    unitModel level via armSlotFib_apply_eval on both sides (the same
    ext+dsimp pattern that landed armSlot_sub_lip).
(2) `rfns_icg_armSlot_le` (new, ~50 lines): VERBATIM mirror of
    `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (JetTower:2795,
    PUBLIC — its induction consumes only the succ-equation +
    `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (public) +
    `rfns_iteratedCovGrad_slotExtend_le` (public)), with base case s=0.
(3) `arm_l2_lip` / `arm_h1_lip` / `arm_h2_lip` wrappers (~40 lines,
    mirror endo_slot_l2/endo_slot_h2 which are fully dissected).
(4) The s=0 base: armSlotEndoCc 0 (bdConnPair g gm) vs
    connDiffSection gm g — `bdConnDiffSection_eq_armSlotEndoCc_zero`
    (JetTower:4359, private, rfl-adjacent — restate in Lip).
(5) armConn moduli: pair via armSlot_sub_lip + connDiff_cocycle +
    transfer to s=0 + connSec H1/H2 machinery; bdd via zero-state trick.
Then `lieCov_pair_h1` per the FINAL ASSEMBLY MAP, classes 4/3/1, master
telescope, integral, a1Lo hookup, exact refresh.

ARM SUCC-EQUATION DERIVATION NOTE: the slotInsert succ template
(JetTower:2725-2792, full text dissected) proves the Cc equation by
ext-chain + `slotInsertEndoFib_apply_eval` + slotExtendFib_apply_eval +
explicit Fin.cases permutation bookkeeping (swap01 on both r and s
sides).  For the ARM version the constructor is NON-square
(g (s+1) (s+2)); derive the correct reindex/rsDom permutations at the
MODEL level from `armSlotFib_apply_eval` (arm s = sIEF (s+1) 0 at
(Arm v0) with vecTail) vs slotExtend-of-arm-s — write the candidate
equation first at unitModel on explicit vectors, read off the two
permutations, then run the ext-chain.  CAUTION: do this with a fresh
context and the :2725 template open side-by-side; the Fin.cases block
is unforgiving.  After it: the rfns mirror induction, the l2/h1/h2
wrappers, then armConn moduli and the capstone — all dissected above.

ARM SUCC-EQUATION — MODEL-LEVEL DERIVATION (s-side DONE):
`slotExtendFib_apply_eval` (OperatorFieldCovariantCalculus:293):
toModel(slotExtendFib A D)(cons v0 vs) = toModel(A (curry D v0)) vs —
the new slot SLICES D first.  Hence
slotExt(armFib s Arm) D' [w0,w1,w2,w3..] = D'[w0, Arm w1 w2, w3, ...]
vs armFib (s+1) Arm D' [v0,v1,v2,v3..] = D'[Arm v0 v1, v2, v3, ...].
Identification (v0,v1)=(w1,w2), v2=w0, rest equal: the INPUT-side
(Fin (s+3)) permutation is the 3-cycle sigma = (swap 0 1).trans
(swap 1 2)  [check: 0->1->2, 1->0->0, 2->2->1 — i.e. w = v after sigma]
— one order deeper than the template's swap01 because the arm eats TWO
slots.  The D'-slot (rsDom) permutation: ArmRes at 0 vs at 1 => swap01
(same as template).  REMAINING: derive the r-side (reindexCoeffGen rho,
Fin (s+2)) by the same model calc on the OPERATOR-as-tensor encoding
(check how reindexCoeffGen acts in the template's :2757 step), then run
the ext-chain with the :2725 template's Fin.cases style (expect one
extra case layer from the 3-cycle).

R-SIDE PINNED: `reindexCoeffFibGen_apply`
(Tensor/CovGrad/RicciDeTurckSectionDifference.lean:4036, PUBLIC):
reindexCoeffFibGen r s rho x A D = A (ofModel (domDomCongr rho
(toModel D))) — the r-side perm acts on the OPERATOR'S ARGUMENT D by
model domDomCongr.  So in the arm succ-equation the rho on Fin (s+2)
(the D'-side) is the swap01 moving the sliced/passthrough D'-slot past
the Arm-output slot (same role as the template's rsDom swap01), and the
sigma on Fin (s+3) (the v-side) is the derived 3-cycle
(swap 0 1).trans (swap 1 2).  ALL permutations for the arm
succ-equation are now determined; write the equation with these and run
the :2725-template ext-chain (expect one extra Fin.cases layer).
Estimated remaining to (N): class-2 capstone ~550 lines; classes 4/3/1
~800-1100; master telescope + integral ~250-400; a1Lo hookup ~100-200;
refreshes/notes/claims; then the endpoint wiring session.

ARM JET TRANSFER — COMPLETE (session count 20 greens): armSlot_sub_lip,
armSlot_succ_lip (perms: rho = swap01 on Fin (s+2), sigma =
(swap 0 1).trans (swap 1 2) on Fin (s+3); after the simp-normalization
chain [TensorMultilinear.tensor0S_curry_apply_eval — NOTE the namespace
qualifier, unknown-identifier was the root cause of 4 failed rw
attempts — , toModel_ofModel, domDomCongr_apply] the three Fin.cases
branches closed by rfl), rfns_arm_le_lip (mirror induction via
both_eq + slotExtend_le), arm_l2/h1/h2_lip wrappers.  NEXT: restate
the s=0 base `bdConnDiffSection_eq_armSlotEndoCc_zero` (JetTower:4359
private) in Lip, then armConn pair/bdd moduli, H1 bdds, ties, capstone.

SESSION UPDATE (allocation flip + armConn moduli, in flight):
- `app_h12_mul_lip` GREEN (mirror of app_h21 via public appRS_h1_h2_h1).
- FLIP EXECUTED: `quad_pair_h1` + `r4_pair_h1` RESTATED with cD at J1 x
  hatT at J2 (D3-free: cD@J2 would need wXi_sub_tame H2 which carries D3).
  Both GREEN post-flip (needed explicit (m := k) levels in the
  jet_nonneg_lip linarith hints -- implicit-level hints produce
  metavariable atoms linarith cannot match).
- dom_h2_lip ALREADY EXISTED at Lip:1815 (do not re-add).
- Palatini `bdConnDiffSection_eq_armSlotEndoCc_zero` now PUBLIC,
  refreshed. C1 `connSec_self_h2` (J2 connSec = J2 wXi) now PUBLIC,
  focused-check green; +C1 refresh in flight.
- INSERTED (pending check): `armU_bdd_h2` (arm@J2 single-state via
  arm_h2_lip + base-eq + connSec_self_h2 + wXi_self_tame; modulus
  (fr*Bs R*A)^2), `armD_pair_h1` (arm@J1 two-state via armSlot_sub +
  arm_h1_lip + base-eq x2 + connSec_pair_h1; modulus
  (fr*B0R*D2 + fr*B1R*A*D2)^2), `hat_bdd_h2` (J2 lrOmegaHat via
  hat_eq_lip + lieOmega_bdd_h2).
- NEXT after these check: CurvF single-state H1 bdd (linear in T-U =
  use curvF_pair_h1 with U := 0? CurvF is linear in T: curvF_pair
  bounds J1(CF_T - CF_U) by J2(T-U); single-state = pair with U=0 IF
  lrCurvF g 0 = 0 -- check; else direct), then the class-2 capstone
  `lieCov_pair_h1` assembly per FINAL ASSEMBLY MAP.

CAPSTONE PLAN (lieCov_pair_h1, all ingredients verified):
- Unit: class2(T) := armField(gm_s) - edgeLiePairFam(T,lieRefoldQ,lieRefoldEps,s)
  = residual(T) by edgePair_eq (Action-private rfl -> RESTATE in Lip as rfl)
  + lieCov_residual (Palatini PUBLIC; hyps hδ_lt/hδ/hδZ/hTsymm/hs).
  residual(T) = (-1)•app 2 6 2 (Pair gm_s) (X_T), X_T = rsDom 2 6 lieCovSigma
  (slotExtendIter 0 4 2 R4_T); slotExtendIter 2 = slotExtend∘slotExtend RFL.
- Telescope: res_T - res_U = (-1)•[app(PairDiff, X_T) + app(Pair_U, Xdiff)].
- J1 bounds: jet_smul ((-1)²) + jet_add; term1 app_h21 2 6 2:
  J2(PairDiff)=lcvPair_pair_h2 (ρ-ball hyp, Hs-norm currency) ×
  J1(X_T) ≤ fr²·J1(R4_T) [rsperm_h1= + slot_h1×2] ≤ fr²(DrR(A+A²))² [r4_bdd_h1];
  term2: J2(Pair_U)=lcvPair_h2_bdd (ρ-ball) × J1(Xdiff) ≤ fr²·J1(R4diff)
  [same transfers via armSlot? NO — Xdiff transfers termwise: rsDom/slotExt are
  LINEAR: Xdiff = rsDom(Ext²(R4_T − R4_U)) needs slotExtend_sub + rsDom_sub
  (grep or prove rfl/ext) then ≤ fr²·(r4_pair_h1 RHS, discharged by
  armU_bdd+armD_pair+hat_bdd+lieOmega_pair moduli at P/Q].
- Currency: conclusion (B R * (1 + A + A ^ 2) ^ 2 * D2) ^ 2; all products
  folded by nlinarith on set-folded reals with explicit product-nonneg hints
  (REMEMBER (m := k) explicit levels in jet_nonneg_lip hints).
- Plumbing ×2 (P=s•T, Q=s•U) verbatim from Lip:588-652 idiom.
- MISSING-CHECK LIST before writing: slotExtend_sub / rsDomDomCongrSection_sub
  linearity lemmas; lcvPair_pair_h2 full conclusion tail; r4_pair_h1 arm/hat
  term discharge order.

X-TRANSFER GREEN (covX_bdd_h1 + covX_pair_h1) + armU/armD/hat + A/B/C
(curvF_zero/curvF_bdd/quadF_bdd/r4_bdd) + edgePair_eq_lip + rsperm_sub_lip
ALL GREEN.  Lessons: (1) hat_bdd/quadF placement must be AFTER
lieOmega_bdd_h2 (:~4300) -- forward-ref moved wholesale; (2) armD needs
synthInstance.maxHeartbeats 1000000 (armSlot_sub ContinuousAdd synth);
(3) THE whnf-timeout culprit in big folds = final-calc `nlinarith` over
composite scalar monomials -- fix = explicit `hsum` linarith combination
+ `le_of_eq ... ring` factoring split (same lesson as quad_pair, now
confirmed twice); (4) rsperm_sub_lip closes by simp only [rsDomDomCongr]
+ rfl (comp_sub unused); (5) sqrt-constant ring tails need `show`-cast
to isolate sqrt^2 before rw [Real.sq_sqrt].
NEXT: capstone lieCov_pair_h1 assembly (short now): units via
edgePair_eq_lip + lieCov_residual (rw [<- hgmT] at hUT to match
set-folded goal), telescope via appCcRS_sub_left/right + module,
app_h21_mul_lip 2 6 2, lcvPair_pair/bdd at (P,Q,gmT,gmU) with Hs-ball
plumbing (:653 idiom), covX pair/bdd, fold to
B R * ((1+A+A^2)^4 * (D2^2 + N^2)).

*** CLASS-2 CAPSTONE `lieCov_pair_h1` GREEN (first try, 126.5s) ***
Conclusion: J1(class2diff @ fixed s) <= B R * ((1+A+A^2)^4 * (D2^2+N^2))
(two-currency: D2 = jet H2 difference, N = Hs2 spectral difference norm;
sizes R/A symmetric both states incl. hU3; rho-ball = min(rho_pair,
rho_bdd) on Hs2 T/U).  Whole chain green: unit (edgePair_eq_lip rfl +
lieCov_residual public) -> telescope (appCcRS_sub_left/right + module)
-> app_h21 2 6 2 -> lcvPair pair/bdd + covX pair/bdd.
CLASS 2 OF 5 DONE.  Ordering ruling: next 4 (lc0AMix) -> 3 (lc0VB) ->
1 (ricciGoodLow) -> master telescope (selfLow_parts, 5-term jet_add
ladder at fixed s) -> path integral (lowC0Diff via
iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame
:517) -> a1Lo_diff hookup (Pair).

CLASS-4 (lc0AMix) PLAN — skeleton verified from LieCorr0AMixRefold:
- `amix_refold_rf` PUBLIC: lc0AMix = lc0AMixFormRF = 2•(Half(perm2) +
  Half(swap*perm2)); Half(σ) = app 2 4 2 (Tr2 σ) (app 2 6 4 (Tr4 perm1)
  (app 2 3 6 (Ext³ mcd) (app 2 5 3 (Tr3 permQ) (Ext² mcd)))) where
  Tr_p(σ) = reindexCoeffGen (pureTrace g gm p) σ (MOVING cometric,
  gm-dep!), mcd = metricConnDiffLoweredCc g gm g (both slots coincide at
  gB=g₀=g).
- mcd_pair_h1 DONE GREEN in C1 (D2-only modulus (B0R·D2+B1R·A·D2)²;
  via mcd_sub_eq + wXi_pair_h1 + metricCorr_pair_h1 [pre-existing
  PUBLIC!] + wXi_h2_low + jet folding; 140.9s).  mcd_pair_h2 is
  D3-infected — never use in C0 lane.
- Telescope: 5 moving factors per half → 5 difference terms; allocation
  per term: difference factor at its level (traces at J2-pair D2-safe;
  mcd at J1-pair via mcd_pair_h1 when innermost, else J2?? NO — mcd at
  J2-pair is D3 ⟹ mcd-difference must always sit in the J1 slot of an
  h21 app; traces-diff can sit at J2 (h21 outer slot).  Nesting: outer
  app J1 conclusion via app_h21 (Φ@J2 × W@J1): put ALL trace-diffs in
  Φ-slots (J2-pair) and mcd-diffs inside W-chains at J1.  The two
  mcd-slot diff terms need J1(app-chain diff) recursion: inner app 2 5 3
  (Tr3, Ext²mcd): diff in mcd → J1 via app_h12?? app 2 5 3 with W=Ext²
  mcdDiff at J2?? — NO: use app_h21 with Φ=Tr3@J2-bdd × W=Ext²(mcdDiff)
  @J1 [slot transfer + mcd_pair_h1] ✓; diff in Tr3 → Φ=Tr3Diff@J2-pair ×
  W=Ext²(mcd_U)@J1-bdd ✓.
- INVENTORY TO CHECK/BUILD: trace3_pair_h2 + trace3_h2_bdd (trace2/4
  exist); J2 slot transfer (slot_h2_lip) for Ext²/Ext³; reindexCoeffGen
  jet transfer (Tr_p = reindex(pureTrace p, σ) — need jet equality or
  transfer under reindexCoeffGen at J1/J2 — check JetTower rfns
  machinery); mcd J1/J2 single bdd (mcd_h2_bdd C1 public — check shape);
  then 5-term telescope + (1+A+A²)-currency fold; conclusion target
  J1(lc0AMix g gmT g − lc0AMix g gmU g) ≤ B R·((1+A+A²)^k·D2²)-form
  (no N-term — amix has no Hs-ball currency unless trace moduli demand
  ρ-balls — trace2/4 moduli DO carry ρ (Hs-ball) → conclusion carries
  ρ-ball hyps like class 2).

*** CLASS-4 (lc0AMix) COMPLETE ***: mcd_pair_h1 (C1) + trace3 family
(C2: insert4_jet_c2/trace3_h2_lip/trace3_pair_h2/trace3_h2_bdd) +
slot_h2_lip/reindex_jet_lip/reindex_sub_lip/trPair_sub_lip/trPair_jet_lip
+ amixHalf_pair_h1 (five-level telescope, 328.6s) + amix_pair_h1
(FormRF wrapper, 16*Bh constant, 299.2s) ALL GREEN.  Currency:
B R * ((1+A+A^2)^4 * (D2^2+N^2)) — same as class 2.
Lessons: perms are LieCorr0Core.* (TameLipschitz's copies are private);
`simp only [K]` can close goals fully (drop trailing ring on "No goals");
S4b needed DUAL constants (Ca4-J1 vs Ca4b-J2 chains).
STATE: classes 2/4/5? green; 3 (lc0VB) + 1 (ricciGoodLow) recon+draft
DISPATCHED TO OPUS subagents (drafts land in scratchpad opus_vb/ and
opus_good/); NEXT after integration = master five-class telescope at
fixed s (selfLow_parts), lowC0Diff path integral
(iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame),
a1Lo_diff hookup (Pair file).

MULTI-AGENT PHASE (user upgraded to ultra; Opus dispatch authorized):
- GREEN so far this phase: selfLow_sub_parts (master telescope EQUATION,
  module not abel for (-2:ℝ)•), vb safe helpers
  (rsperm_h2_lip/ipHead/ip_form_lip/ip_sub_lip).
- OPUS RECON DONE: class-3 (vb): refold vb_refold_rf PUBLIC
  (LieCorr0VBRefold.lean:120), 3-term telescope, budget (1+A+A²)⁴ EXACT;
  draft at scratchpad opus_vb/vb_pair_h1_draft.lean (811 lines);
  prerequisites M1/M2 = trace1_pair_h2/trace1_h2_bdd (C2) + M3 =
  vbmcd_perm_eq (vbMcdArm = rsDom(VBPerm)(Ext(mcd)); the in-tree
  vbMcdArm_rel + vbPK_eq_slotExt are PRIVATE in READ-ONLY
  LieCorr0CoeffL2JetBound.lean:1082 — must re-derive at model level in
  C1 (public) using tensor0SProdKappaFib/slotExtendFib_apply_eval).
- class-1 (good): ricciGoodLow = ccInputSymm(AA + DA); (s•T)-slot enters
  ONLY via covGrad in DA (one D2-term); AA = connSec-insertions
  (connDiffContrInsertionField_eq_reindex_slotExtend_two etc. PUBLIC) ×
  trace2; missing: dagLow_bdd_h2 (recommend claiming Action +
  publicizing dagLow_h2_rf + connLow_h3_rf), fullSlot_bdd_h2 +
  fullSlot_pair_h1 (Opus building in C1 now; check gInvDiffRaisedEndoField
  relation); draft at opus_good/good_pair_h1_draft.lean (~1180 lines,
  AA arm + capstone complete, gaps marked sorry).
- BUILDERS IN FLIGHT: Opus@C2 trace1 family (token 99f2...), Opus@C1
  fullSlot bricks (token e2aa...).  QUEUED: Opus@C1 vbmcd_perm_eq
  re-derivation (after fullSlot agent frees C1).
- INTEGRATION ORDER: trace1 lands -> I insert vb body (minus
  vbmcd-dependents until bridge) into Lip; fullSlot+dagLow land ->
  good_pair_h1; then master five-class J1 bound at fixed s (uses
  selfLow_sub_parts + 5 class moduli), c0Diff_tame (mirror c1Diff_tame
  :517-746, engine path_jetL2_le g 2 2 1), lowBaseDiff_c0 already wired,
  final a1Lo_diff-style Pair endpoint.

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

BREAKTHROUGH (class-2 workload collapse): `lrOmegaHat g0 gm`
(Palatini:7326) is DEFINITIONALLY IDENTICAL to LowBaseLip's private
`lipOmega g gm` (:1860) — same appCcRS(slotInsertEndoCc 2
(fullRaisedEndoField gm g), domDomCongr (finRotate 3)
(connDiffLoweredCc g gm)).  Hence its J1 pair modulus IS
`lieOmega_pair_h1` (already proved) and its bdd is `lieOmega_bdd_h2` +
jet_mono.  `bdConnPair g0 gc = connDiff endo` (rfl apply :4354);
the armSlotEndoCc(bdConnPair) J2 coefficient moduli =
`LowBaseInternal.connLow_pair_h2` / `connLow_h2_bdd` (the prompt's reuse
list).  PALATINI EXPORT BAND (this session, all now public):
lrRiemW1/W2, lrCurvF(+unitModel), lrQuadF(+unitModel), lrQA/lrQB
(+unitModels), lrOmegaHat(+unitModel), bdConnPair(+apply), lieCovR4_eq
(rfl decomposition).  Remaining class-2 construction, ALL in LowBaseLip:
(1) `lipOmega_eq_hat : lipOmega g gm = lrOmegaHat g gm := rfl`;
(2) lrQA/lrQB pair at J1 = omega_pair_h1-pattern telescope (coeff J2 via
    connLow pair/bdd, arg J1 via lieOmega_pair_h1-internals);
(3) lrQuadF pair = 6-fold dom_h1_lip + jet_add over (2);
(4) lrCurvF pair = linear app_h21_mul_lip one-liner (T-U slot);
(5) `lcvR4_pair_h1` via lieCovR4_eq;
(6) lcvPair coefficient pair (H2) + H1Poly plumbing -> `lieCov_pair_h1`.

CLASS-2 CONSTRUCTION LOG (this session, all focused GREEN in LowBaseLip):
* `hat_eq_lip` (rfl: lrOmegaHat = lipOmega), `curvF_pair_h1` (linear
  J1<=C*J2(T-U)), `quadB_tel`/`quadA_tel` (two-slot app telescopes),
  `quad_pair_h1` (six-block lrQuadF telescope, abstract product form),
  `r4_pair_h1` (lieCovR4 pair via the public `lieCovR4_eq`, s in Icc01,
  conclusion C*(J2(T-U) + [J2(cU)*J1(hatD) + J2(cD)*J1(hatT)] at
  realizedFam metrics)).
* PALATINI EXPORTS this session: + lrPermA/B/C (the perms appear in
  lrQuadF's body and must be nameable downstream).  Palatini re-checked
  green + refreshed after each export batch.
* NEW DURABLE LESSON (cured a hard whnf wall at 1.6M heartbeats): in this
  file (respectTransparency false), the jet-chain arithmetic over tensor
  atoms MUST be closed by `linarith [explicit jet_add_lip applications +
  dom equations + prior bounds]` — `exact add_le_add_left ... _`,
  `gcongr`, and goal-side `nlinarith` all whnf-explode on the tensor
  atoms.  Fold every jet value with `set ... with h` and do the final
  numeric step on the folded real variables.
REMAINING for class 2: (iii) lcvPair coefficient pair at H2 (lieCovPair
is PUBLIC Palatini:3627; mirror the private lcvPair_h2_low Action:9138
from its public inputs), (iv) H1Poly mini-plumbing + `lieCov_pair_h1`
assembly plugging the concrete moduli (connLow pair/bdd for the
b-slots, lieOmega machinery via hat_eq_lip for the hat slots).

CLASS-2 FINAL ASSEMBLY MAP (all bridges verified):
* unit equation: `edgePair_eq` is rfl (Action-private but rfl —
  restate in Lip); `lieCov_residual` PUBLIC (Palatini:9033):
  armField(gm_s) - RefoldPairTraceFamily(q,eps,s) = (-1) . appCcRS 2 6 2
  (lieCovPair gm_s) (rsDom lieCovSigma (slotExtendIter 2 (lieCovR4 T s))),
  hyps = hTsymm + hs in Icc01 + hdelta_lt.
* Telescope: unitT - unitU = (-1).[app(PairDiff, X_T) + app(Pair gmU,
  X_T - X_U)], X_S = rsDom lieCovSigma (Ext^2 (lieCovR4 S s)).
* NEW GREEN this stretch: trace4_pair_h2 + trace4_h2_bdd (C2Lip, public,
  .2-projection of trace24_h2_lip + zero-state trick; C2Lip refreshed),
  lcvPair_eq_lip (rfl) + lcvPair_pair_h2 (Lip; telescope over
  trace2/trace4 pair+bdd via app_h2_mul_lip 6 4 2; NOTE trace producers
  are LowBaseInternal.* qualified).
* STILL TO BUILD (patterned): slot_h1_lip / rsperm_h1_lip (+ their _l2
  bases — mirror Action-private slot_l2 / rsperm_l2_sq, order-agnostic);
  lcvPair_h2_bdd (from trace bdds); H1 single-state bdds for
  CurvF/QuadF/lieCovR4 (via lieCovR4_eq; hat-bdd = lieOmega_bdd_h2 +
  jet_mono; coeff-bdd = LowBaseInternal.connLow_h2_bdd — VERIFY it
  matches armSlotEndoCc(bdConnPair)); realizedFam tie plumbing block
  (mirror lieCov_h2_tame's hδP/hcP/hP/hP2); then `lieCov_pair_h1`.
* Lean fixes this stretch: rw-first-occurrence hit LHS -> use conv_rhs;
  nlinarith product-monotonicity unreliable -> explicit mul_le_mul
  chains; trace producers need LowBaseInternal qualification.

GREEN TALLY (this session, LowBaseLip/C2Lip/Palatini):
lieOmega_pair_h1 (+app_h21_mul_lip/dom_h1_lip/omega_pair_h1),
riem_pair_h1, hat_eq_lip, curvF_pair_h1, quadB_tel, quadA_tel,
quad_pair_h1, r4_pair_h1, trace4_pair_h2, trace4_h2_bdd,
lcvPair_eq_lip, lcvPair_pair_h2, slot_l2_lip/slot_h1_lip,
rsperm_l2_lip/rsperm_h1_lip, lcvPair_h2_bdd — 14 public/private
declarations, every one focused GREEN; Palatini export band + 2
refreshes; C2Lip export + refresh.  NEXT (the class-2 capstone
`lieCov_pair_h1`): (a) H1 single-state bdds — CurvF (linear, trivial),
QuadF (six blocks; coeff J2 bdd = LowBaseInternal.connLow_h2_bdd
[VERIFY statement matches armSlotEndoCc(bdConnPair)], hat J1 bdd =
lieOmega_bdd_h2 + jet_mono via hat_eq_lip), R4 (via lieCovR4_eq);
(b) realizedFam tie plumbing (mirror lieCov_h2_tame's
hδP/hcP/hP/hP2 block, Action:10724-10760); (c) final telescope via
edgePair_eq (restate as rfl in Lip) + lieCov_residual (PUBLIC) +
app_h21_mul_lip 2 6 2 + slot_h1_lip x2 + rsperm_h1_lip + the pair/bdd
family.  Then classes 4 -> 3 -> 1, master telescope, lowC0_sub
integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CORRECTION (coefficient moduli for QuadF): `connLow_h2_bdd` bounds the
RANK-(3,3) `connLowOp` (public, Action:3388) — NOT the rank-(3,4)
`armSlotEndoCc 2 (bdConnPair g gm)` that lrQA/lrQB carry.  The QuadF
coefficient needs its own J2 pair/bdd: search Action for an
armSlotEndoCc jet-transfer (`armSlot.*h2|armSlot.*jet|EndoCc.*jet`) and
for how lcvPair_h2_low's siblings bounded arm-slot endo coefficients;
the revSlot pattern (`revSlot_bdd_h2`/`revSlot_pair_h2` for
slotInsertEndoCc(fullRaisedEndoField)) is the shape template — a
bdConnPair analogue (`armConn_bdd_h2`/`armConn_pair_h2`) may need
building from the connDiff H2 machinery (C1/C2 connSec/connLow family)
plus an endo-slot jet transfer.

QUADF-COEFFICIENT MODULI (the one genuinely new sub-brick left for the
class-2 capstone): J2 pair/bdd of `armSlotEndoCc 2 (bdConnPair g gm)`
(def MetricArmCoeffJetTower:1959, public) never existed — the H2 route
bounded the OUTER (6,2) lieCovPair only.  Build order: (1) grep C1/C2
for an H2 connDiffSection pair (`connSec_pair_h2`?) or derive from
`connLow_pair_h2` shapes; (2) the endo-slot jet transfer: mirror the
INTERNALS of `LowBaseInternal.revSlot_bdd_h2`/`revSlot_pair_h2` (they
bound slotInsertEndoCc 2 (fullRaisedEndoField) — same TYPE pattern,
different endo content); Palatini:4359
`bdConnDiffSection_eq_armSlotEndoCc_zero` is the s=0 endo/section
bridge (private, rfl-adjacent — check for an s=2 sibling or re-derive);
(3) useful splitters in Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound
(READ-ONLY): `connDiff_cocycle` (:91), `dLaCovKernel_backgroundSplit`
(:248).  Then assemble `lieCov_pair_h1` per the FINAL ASSEMBLY MAP.

ARMCONN MODULI ROUTE (refined): the two-state difference
bdConnPair(gmT) - bdConnPair(gmU) = connDiff(gmT,g) - connDiff(gmU,g)
collapses by `connDiff_cocycle` (DeTurckLieKernelL2JetBound:91, public,
READ-ONLY file) to a single connDiff(gmT,gmU)-type object; its H2 jet
is reachable through the connLowOp packaging: `connLow_pair_h2`
(PUBLIC, C2:4752) gives J2(connLowOp gT - connLowOp gU) <= (C*|T-U|)^2,
and the bridge connDiffSection <-> connLowOp lives in the
`connSec_eq_raise` (C1:892) / `connLower_unit` (Action:171, private —
re-derive if needed) family.  The armSlot jet transfer mirrors
`revSlot_bdd_h2`'s internals (C1:4501: bdd = pair vs base-state +
fr^2-factor; the pair's engine is `revSlot_pair_h2` nearby).  BDD:
zero-state trick as in revSlot_bdd_h2.  All pieces are in claimed or
read-only files; nothing blocks.

REVSLOT ENGINE DISSECTED (C1:4452): pair = `slotInsertEndoCc_sub`
(linearity) + `fullRev_sub` (endo diff = symmRaiseEndo(T-U)) +
`endo_slot_h2` (J2(slotInsert s=2 endo) <= fr^2 * J2(slotInsert 0 endo))
+ s=0 base identification.  For armConn: find/mirror the ARM-version
transfer (`armSlotEndoCc` vs `slotInsertEndoCc` are different
constructors — grep MetricArmCoeffJetTower's public surface for
`arm.*slot.*h2|armSlotEndoCc_sub|arm.*jet` and an endo-difference
linearity `armSlotEndoCc_sub`); the endo DIFFERENCE
bdConnPair(gmT)-bdConnPair(gmU) needs its own `fullRev_sub` analogue
(via connDiff_cocycle).  Everything else for `lieCov_pair_h1` is
assembled and green.  NEXT WINDOW: (1) grep the arm transfer; (2) write
armConn_pair/bdd; (3) H1 bdds (CurvF/QuadF/R4); (4) realizedFam ties;
(5) `lieCov_pair_h1`; then classes 4 -> 3 -> 1, master telescope,
lowC0_sub integral, a1Lo_diff hookup, exact refresh, notes, release
claims.

ARM JET TRANSFER — FINAL DEPTH (the ONE new pointwise lemma left for the
class-2 capstone): the endo_slot chain bottoms out at
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (pointwise fiber-norm
bound under iterated covariant gradients, single-endo slotInsert).  The
arm version `rfns_iteratedCovGrad_armSlotEndoCc_le_*` does not exist;
mirror the slotInsert one (locate + read its proof; likely in the
JetTower/NablaOnTensors layer) with the bilinear endo's extra slot paid
by a v0-basis expansion (one extra fr factor).  Wrappers after it are
mechanical (arm_slot_l2 -> arm_h1/h2, mirroring endo_slot_l2/h2 which
are fully dissected above).  `armSlot_sub_lip` is GREEN (15th this
session; proof pattern = rs-rank ext + fib-level hfib via
armSlotFib_apply_eval + slotInsertEndoFib_sub_left + dsimp-only for the
beta-redex; synthInstance+maxHeartbeats bumps needed).

ARM TRANSFER — COMPLETE IMPLEMENTATION SCRIPT (all proofs dissected):
(1) `armSlot_succ_eq` (new, ~60-80 lines, Lip-private): the arm analogue
    of `slotInsertEndoCc_succ_eq_reindex_slotExtend` (JetTower:2725,
    private — read its proof as template): armSlotEndoCc (s+1) Arm =
    rsDomDomCongr-reindex of slotExtend (armSlotEndoCc s Arm); prove at
    unitModel level via armSlotFib_apply_eval on both sides (the same
    ext+dsimp pattern that landed armSlot_sub_lip).
(2) `rfns_icg_armSlot_le` (new, ~50 lines): VERBATIM mirror of
    `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (JetTower:2795,
    PUBLIC — its induction consumes only the succ-equation +
    `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (public) +
    `rfns_iteratedCovGrad_slotExtend_le` (public)), with base case s=0.
(3) `arm_l2_lip` / `arm_h1_lip` / `arm_h2_lip` wrappers (~40 lines,
    mirror endo_slot_l2/endo_slot_h2 which are fully dissected).
(4) The s=0 base: armSlotEndoCc 0 (bdConnPair g gm) vs
    connDiffSection gm g — `bdConnDiffSection_eq_armSlotEndoCc_zero`
    (JetTower:4359, private, rfl-adjacent — restate in Lip).
(5) armConn moduli: pair via armSlot_sub_lip + connDiff_cocycle +
    transfer to s=0 + connSec H1/H2 machinery; bdd via zero-state trick.
Then `lieCov_pair_h1` per the FINAL ASSEMBLY MAP, classes 4/3/1, master
telescope, integral, a1Lo hookup, exact refresh.

ARM SUCC-EQUATION DERIVATION NOTE: the slotInsert succ template
(JetTower:2725-2792, full text dissected) proves the Cc equation by
ext-chain + `slotInsertEndoFib_apply_eval` + slotExtendFib_apply_eval +
explicit Fin.cases permutation bookkeeping (swap01 on both r and s
sides).  For the ARM version the constructor is NON-square
(g (s+1) (s+2)); derive the correct reindex/rsDom permutations at the
MODEL level from `armSlotFib_apply_eval` (arm s = sIEF (s+1) 0 at
(Arm v0) with vecTail) vs slotExtend-of-arm-s — write the candidate
equation first at unitModel on explicit vectors, read off the two
permutations, then run the ext-chain.  CAUTION: do this with a fresh
context and the :2725 template open side-by-side; the Fin.cases block
is unforgiving.  After it: the rfns mirror induction, the l2/h1/h2
wrappers, then armConn moduli and the capstone — all dissected above.

ARM SUCC-EQUATION — MODEL-LEVEL DERIVATION (s-side DONE):
`slotExtendFib_apply_eval` (OperatorFieldCovariantCalculus:293):
toModel(slotExtendFib A D)(cons v0 vs) = toModel(A (curry D v0)) vs —
the new slot SLICES D first.  Hence
slotExt(armFib s Arm) D' [w0,w1,w2,w3..] = D'[w0, Arm w1 w2, w3, ...]
vs armFib (s+1) Arm D' [v0,v1,v2,v3..] = D'[Arm v0 v1, v2, v3, ...].
Identification (v0,v1)=(w1,w2), v2=w0, rest equal: the INPUT-side
(Fin (s+3)) permutation is the 3-cycle sigma = (swap 0 1).trans
(swap 1 2)  [check: 0->1->2, 1->0->0, 2->2->1 — i.e. w = v after sigma]
— one order deeper than the template's swap01 because the arm eats TWO
slots.  The D'-slot (rsDom) permutation: ArmRes at 0 vs at 1 => swap01
(same as template).  REMAINING: derive the r-side (reindexCoeffGen rho,
Fin (s+2)) by the same model calc on the OPERATOR-as-tensor encoding
(check how reindexCoeffGen acts in the template's :2757 step), then run
the ext-chain with the :2725 template's Fin.cases style (expect one
extra case layer from the 3-cycle).

R-SIDE PINNED: `reindexCoeffFibGen_apply`
(Tensor/CovGrad/RicciDeTurckSectionDifference.lean:4036, PUBLIC):
reindexCoeffFibGen r s rho x A D = A (ofModel (domDomCongr rho
(toModel D))) — the r-side perm acts on the OPERATOR'S ARGUMENT D by
model domDomCongr.  So in the arm succ-equation the rho on Fin (s+2)
(the D'-side) is the swap01 moving the sliced/passthrough D'-slot past
the Arm-output slot (same role as the template's rsDom swap01), and the
sigma on Fin (s+3) (the v-side) is the derived 3-cycle
(swap 0 1).trans (swap 1 2).  ALL permutations for the arm
succ-equation are now determined; write the equation with these and run
the :2725-template ext-chain (expect one extra Fin.cases layer).
Estimated remaining to (N): class-2 capstone ~550 lines; classes 4/3/1
~800-1100; master telescope + integral ~250-400; a1Lo hookup ~100-200;
refreshes/notes/claims; then the endpoint wiring session.

ARM JET TRANSFER — COMPLETE (session count 20 greens): armSlot_sub_lip,
armSlot_succ_lip (perms: rho = swap01 on Fin (s+2), sigma =
(swap 0 1).trans (swap 1 2) on Fin (s+3); after the simp-normalization
chain [TensorMultilinear.tensor0S_curry_apply_eval — NOTE the namespace
qualifier, unknown-identifier was the root cause of 4 failed rw
attempts — , toModel_ofModel, domDomCongr_apply] the three Fin.cases
branches closed by rfl), rfns_arm_le_lip (mirror induction via
both_eq + slotExtend_le), arm_l2/h1/h2_lip wrappers.  NEXT: restate
the s=0 base `bdConnDiffSection_eq_armSlotEndoCc_zero` (JetTower:4359
private) in Lip, then armConn pair/bdd moduli, H1 bdds, ties, capstone.

SESSION UPDATE (allocation flip + armConn moduli, in flight):
- `app_h12_mul_lip` GREEN (mirror of app_h21 via public appRS_h1_h2_h1).
- FLIP EXECUTED: `quad_pair_h1` + `r4_pair_h1` RESTATED with cD at J1 x
  hatT at J2 (D3-free: cD@J2 would need wXi_sub_tame H2 which carries D3).
  Both GREEN post-flip (needed explicit (m := k) levels in the
  jet_nonneg_lip linarith hints -- implicit-level hints produce
  metavariable atoms linarith cannot match).
- dom_h2_lip ALREADY EXISTED at Lip:1815 (do not re-add).
- Palatini `bdConnDiffSection_eq_armSlotEndoCc_zero` now PUBLIC,
  refreshed. C1 `connSec_self_h2` (J2 connSec = J2 wXi) now PUBLIC,
  focused-check green; +C1 refresh in flight.
- INSERTED (pending check): `armU_bdd_h2` (arm@J2 single-state via
  arm_h2_lip + base-eq + connSec_self_h2 + wXi_self_tame; modulus
  (fr*Bs R*A)^2), `armD_pair_h1` (arm@J1 two-state via armSlot_sub +
  arm_h1_lip + base-eq x2 + connSec_pair_h1; modulus
  (fr*B0R*D2 + fr*B1R*A*D2)^2), `hat_bdd_h2` (J2 lrOmegaHat via
  hat_eq_lip + lieOmega_bdd_h2).
- NEXT after these check: CurvF single-state H1 bdd (linear in T-U =
  use curvF_pair_h1 with U := 0? CurvF is linear in T: curvF_pair
  bounds J1(CF_T - CF_U) by J2(T-U); single-state = pair with U=0 IF
  lrCurvF g 0 = 0 -- check; else direct), then the class-2 capstone
  `lieCov_pair_h1` assembly per FINAL ASSEMBLY MAP.

CAPSTONE PLAN (lieCov_pair_h1, all ingredients verified):
- Unit: class2(T) := armField(gm_s) - edgeLiePairFam(T,lieRefoldQ,lieRefoldEps,s)
  = residual(T) by edgePair_eq (Action-private rfl -> RESTATE in Lip as rfl)
  + lieCov_residual (Palatini PUBLIC; hyps hδ_lt/hδ/hδZ/hTsymm/hs).
  residual(T) = (-1)•app 2 6 2 (Pair gm_s) (X_T), X_T = rsDom 2 6 lieCovSigma
  (slotExtendIter 0 4 2 R4_T); slotExtendIter 2 = slotExtend∘slotExtend RFL.
- Telescope: res_T - res_U = (-1)•[app(PairDiff, X_T) + app(Pair_U, Xdiff)].
- J1 bounds: jet_smul ((-1)²) + jet_add; term1 app_h21 2 6 2:
  J2(PairDiff)=lcvPair_pair_h2 (ρ-ball hyp, Hs-norm currency) ×
  J1(X_T) ≤ fr²·J1(R4_T) [rsperm_h1= + slot_h1×2] ≤ fr²(DrR(A+A²))² [r4_bdd_h1];
  term2: J2(Pair_U)=lcvPair_h2_bdd (ρ-ball) × J1(Xdiff) ≤ fr²·J1(R4diff)
  [same transfers via armSlot? NO — Xdiff transfers termwise: rsDom/slotExt are
  LINEAR: Xdiff = rsDom(Ext²(R4_T − R4_U)) needs slotExtend_sub + rsDom_sub
  (grep or prove rfl/ext) then ≤ fr²·(r4_pair_h1 RHS, discharged by
  armU_bdd+armD_pair+hat_bdd+lieOmega_pair moduli at P/Q].
- Currency: conclusion (B R * (1 + A + A ^ 2) ^ 2 * D2) ^ 2; all products
  folded by nlinarith on set-folded reals with explicit product-nonneg hints
  (REMEMBER (m := k) explicit levels in jet_nonneg_lip hints).
- Plumbing ×2 (P=s•T, Q=s•U) verbatim from Lip:588-652 idiom.
- MISSING-CHECK LIST before writing: slotExtend_sub / rsDomDomCongrSection_sub
  linearity lemmas; lcvPair_pair_h2 full conclusion tail; r4_pair_h1 arm/hat
  term discharge order.

X-TRANSFER GREEN (covX_bdd_h1 + covX_pair_h1) + armU/armD/hat + A/B/C
(curvF_zero/curvF_bdd/quadF_bdd/r4_bdd) + edgePair_eq_lip + rsperm_sub_lip
ALL GREEN.  Lessons: (1) hat_bdd/quadF placement must be AFTER
lieOmega_bdd_h2 (:~4300) -- forward-ref moved wholesale; (2) armD needs
synthInstance.maxHeartbeats 1000000 (armSlot_sub ContinuousAdd synth);
(3) THE whnf-timeout culprit in big folds = final-calc `nlinarith` over
composite scalar monomials -- fix = explicit `hsum` linarith combination
+ `le_of_eq ... ring` factoring split (same lesson as quad_pair, now
confirmed twice); (4) rsperm_sub_lip closes by simp only [rsDomDomCongr]
+ rfl (comp_sub unused); (5) sqrt-constant ring tails need `show`-cast
to isolate sqrt^2 before rw [Real.sq_sqrt].
NEXT: capstone lieCov_pair_h1 assembly (short now): units via
edgePair_eq_lip + lieCov_residual (rw [<- hgmT] at hUT to match
set-folded goal), telescope via appCcRS_sub_left/right + module,
app_h21_mul_lip 2 6 2, lcvPair_pair/bdd at (P,Q,gmT,gmU) with Hs-ball
plumbing (:653 idiom), covX pair/bdd, fold to
B R * ((1+A+A^2)^4 * (D2^2 + N^2)).

*** CLASS-2 CAPSTONE `lieCov_pair_h1` GREEN (first try, 126.5s) ***
Conclusion: J1(class2diff @ fixed s) <= B R * ((1+A+A^2)^4 * (D2^2+N^2))
(two-currency: D2 = jet H2 difference, N = Hs2 spectral difference norm;
sizes R/A symmetric both states incl. hU3; rho-ball = min(rho_pair,
rho_bdd) on Hs2 T/U).  Whole chain green: unit (edgePair_eq_lip rfl +
lieCov_residual public) -> telescope (appCcRS_sub_left/right + module)
-> app_h21 2 6 2 -> lcvPair pair/bdd + covX pair/bdd.
CLASS 2 OF 5 DONE.  Ordering ruling: next 4 (lc0AMix) -> 3 (lc0VB) ->
1 (ricciGoodLow) -> master telescope (selfLow_parts, 5-term jet_add
ladder at fixed s) -> path integral (lowC0Diff via
iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame
:517) -> a1Lo_diff hookup (Pair).

CLASS-4 (lc0AMix) PLAN — skeleton verified from LieCorr0AMixRefold:
- `amix_refold_rf` PUBLIC: lc0AMix = lc0AMixFormRF = 2•(Half(perm2) +
  Half(swap*perm2)); Half(σ) = app 2 4 2 (Tr2 σ) (app 2 6 4 (Tr4 perm1)
  (app 2 3 6 (Ext³ mcd) (app 2 5 3 (Tr3 permQ) (Ext² mcd)))) where
  Tr_p(σ) = reindexCoeffGen (pureTrace g gm p) σ (MOVING cometric,
  gm-dep!), mcd = metricConnDiffLoweredCc g gm g (both slots coincide at
  gB=g₀=g).
- mcd_pair_h1 DONE GREEN in C1 (D2-only modulus (B0R·D2+B1R·A·D2)²;
  via mcd_sub_eq + wXi_pair_h1 + metricCorr_pair_h1 [pre-existing
  PUBLIC!] + wXi_h2_low + jet folding; 140.9s).  mcd_pair_h2 is
  D3-infected — never use in C0 lane.
- Telescope: 5 moving factors per half → 5 difference terms; allocation
  per term: difference factor at its level (traces at J2-pair D2-safe;
  mcd at J1-pair via mcd_pair_h1 when innermost, else J2?? NO — mcd at
  J2-pair is D3 ⟹ mcd-difference must always sit in the J1 slot of an
  h21 app; traces-diff can sit at J2 (h21 outer slot).  Nesting: outer
  app J1 conclusion via app_h21 (Φ@J2 × W@J1): put ALL trace-diffs in
  Φ-slots (J2-pair) and mcd-diffs inside W-chains at J1.  The two
  mcd-slot diff terms need J1(app-chain diff) recursion: inner app 2 5 3
  (Tr3, Ext²mcd): diff in mcd → J1 via app_h12?? app 2 5 3 with W=Ext²
  mcdDiff at J2?? — NO: use app_h21 with Φ=Tr3@J2-bdd × W=Ext²(mcdDiff)
  @J1 [slot transfer + mcd_pair_h1] ✓; diff in Tr3 → Φ=Tr3Diff@J2-pair ×
  W=Ext²(mcd_U)@J1-bdd ✓.
- INVENTORY TO CHECK/BUILD: trace3_pair_h2 + trace3_h2_bdd (trace2/4
  exist); J2 slot transfer (slot_h2_lip) for Ext²/Ext³; reindexCoeffGen
  jet transfer (Tr_p = reindex(pureTrace p, σ) — need jet equality or
  transfer under reindexCoeffGen at J1/J2 — check JetTower rfns
  machinery); mcd J1/J2 single bdd (mcd_h2_bdd C1 public — check shape);
  then 5-term telescope + (1+A+A²)-currency fold; conclusion target
  J1(lc0AMix g gmT g − lc0AMix g gmU g) ≤ B R·((1+A+A²)^k·D2²)-form
  (no N-term — amix has no Hs-ball currency unless trace moduli demand
  ρ-balls — trace2/4 moduli DO carry ρ (Hs-ball) → conclusion carries
  ρ-ball hyps like class 2).

*** CLASS-4 (lc0AMix) COMPLETE ***: mcd_pair_h1 (C1) + trace3 family
(C2: insert4_jet_c2/trace3_h2_lip/trace3_pair_h2/trace3_h2_bdd) +
slot_h2_lip/reindex_jet_lip/reindex_sub_lip/trPair_sub_lip/trPair_jet_lip
+ amixHalf_pair_h1 (five-level telescope, 328.6s) + amix_pair_h1
(FormRF wrapper, 16*Bh constant, 299.2s) ALL GREEN.  Currency:
B R * ((1+A+A^2)^4 * (D2^2+N^2)) — same as class 2.
Lessons: perms are LieCorr0Core.* (TameLipschitz's copies are private);
`simp only [K]` can close goals fully (drop trailing ring on "No goals");
S4b needed DUAL constants (Ca4-J1 vs Ca4b-J2 chains).
STATE: classes 2/4/5? green; 3 (lc0VB) + 1 (ricciGoodLow) recon+draft
DISPATCHED TO OPUS subagents (drafts land in scratchpad opus_vb/ and
opus_good/); NEXT after integration = master five-class telescope at
fixed s (selfLow_parts), lowC0Diff path integral
(iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame),
a1Lo_diff hookup (Pair file).

MULTI-AGENT PHASE (user upgraded to ultra; Opus dispatch authorized):
- GREEN so far this phase: selfLow_sub_parts (master telescope EQUATION,
  module not abel for (-2:ℝ)•), vb safe helpers
  (rsperm_h2_lip/ipHead/ip_form_lip/ip_sub_lip).
- OPUS RECON DONE: class-3 (vb): refold vb_refold_rf PUBLIC
  (LieCorr0VBRefold.lean:120), 3-term telescope, budget (1+A+A²)⁴ EXACT;
  draft at scratchpad opus_vb/vb_pair_h1_draft.lean (811 lines);
  prerequisites M1/M2 = trace1_pair_h2/trace1_h2_bdd (C2) + M3 =
  vbmcd_perm_eq (vbMcdArm = rsDom(VBPerm)(Ext(mcd)); the in-tree
  vbMcdArm_rel + vbPK_eq_slotExt are PRIVATE in READ-ONLY
  LieCorr0CoeffL2JetBound.lean:1082 — must re-derive at model level in
  C1 (public) using tensor0SProdKappaFib/slotExtendFib_apply_eval).
- class-1 (good): ricciGoodLow = ccInputSymm(AA + DA); (s•T)-slot enters
  ONLY via covGrad in DA (one D2-term); AA = connSec-insertions
  (connDiffContrInsertionField_eq_reindex_slotExtend_two etc. PUBLIC) ×
  trace2; missing: dagLow_bdd_h2 (recommend claiming Action +
  publicizing dagLow_h2_rf + connLow_h3_rf), fullSlot_bdd_h2 +
  fullSlot_pair_h1 (Opus building in C1 now; check gInvDiffRaisedEndoField
  relation); draft at opus_good/good_pair_h1_draft.lean (~1180 lines,
  AA arm + capstone complete, gaps marked sorry).
- BUILDERS IN FLIGHT: Opus@C2 trace1 family (token 99f2...), Opus@C1
  fullSlot bricks (token e2aa...).  QUEUED: Opus@C1 vbmcd_perm_eq
  re-derivation (after fullSlot agent frees C1).
- INTEGRATION ORDER: trace1 lands -> I insert vb body (minus
  vbmcd-dependents until bridge) into Lip; fullSlot+dagLow land ->
  good_pair_h1; then master five-class J1 bound at fixed s (uses
  selfLow_sub_parts + 5 class moduli), c0Diff_tame (mirror c1Diff_tame
  :517-746, engine path_jetL2_le g 2 2 1), lowBaseDiff_c0 already wired,
  final a1Lo_diff-style Pair endpoint.

CLASS-2 CONSTRUCTION LOG (this session, all focused GREEN in LowBaseLip):
* `hat_eq_lip` (rfl: lrOmegaHat = lipOmega), `curvF_pair_h1` (linear
  J1<=C*J2(T-U)), `quadB_tel`/`quadA_tel` (two-slot app telescopes),
  `quad_pair_h1` (six-block lrQuadF telescope, abstract product form),
  `r4_pair_h1` (lieCovR4 pair via the public `lieCovR4_eq`, s in Icc01,
  conclusion C*(J2(T-U) + [J2(cU)*J1(hatD) + J2(cD)*J1(hatT)] at
  realizedFam metrics)).
* PALATINI EXPORTS this session: + lrPermA/B/C (the perms appear in
  lrQuadF's body and must be nameable downstream).  Palatini re-checked
  green + refreshed after each export batch.
* NEW DURABLE LESSON (cured a hard whnf wall at 1.6M heartbeats): in this
  file (respectTransparency false), the jet-chain arithmetic over tensor
  atoms MUST be closed by `linarith [explicit jet_add_lip applications +
  dom equations + prior bounds]` — `exact add_le_add_left ... _`,
  `gcongr`, and goal-side `nlinarith` all whnf-explode on the tensor
  atoms.  Fold every jet value with `set ... with h` and do the final
  numeric step on the folded real variables.
REMAINING for class 2: (iii) lcvPair coefficient pair at H2 (lieCovPair
is PUBLIC Palatini:3627; mirror the private lcvPair_h2_low Action:9138
from its public inputs), (iv) H1Poly mini-plumbing + `lieCov_pair_h1`
assembly plugging the concrete moduli (connLow pair/bdd for the
b-slots, lieOmega machinery via hat_eq_lip for the hat slots).

CLASS-2 FINAL ASSEMBLY MAP (all bridges verified):
* unit equation: `edgePair_eq` is rfl (Action-private but rfl —
  restate in Lip); `lieCov_residual` PUBLIC (Palatini:9033):
  armField(gm_s) - RefoldPairTraceFamily(q,eps,s) = (-1) . appCcRS 2 6 2
  (lieCovPair gm_s) (rsDom lieCovSigma (slotExtendIter 2 (lieCovR4 T s))),
  hyps = hTsymm + hs in Icc01 + hdelta_lt.
* Telescope: unitT - unitU = (-1).[app(PairDiff, X_T) + app(Pair gmU,
  X_T - X_U)], X_S = rsDom lieCovSigma (Ext^2 (lieCovR4 S s)).
* NEW GREEN this stretch: trace4_pair_h2 + trace4_h2_bdd (C2Lip, public,
  .2-projection of trace24_h2_lip + zero-state trick; C2Lip refreshed),
  lcvPair_eq_lip (rfl) + lcvPair_pair_h2 (Lip; telescope over
  trace2/trace4 pair+bdd via app_h2_mul_lip 6 4 2; NOTE trace producers
  are LowBaseInternal.* qualified).
* STILL TO BUILD (patterned): slot_h1_lip / rsperm_h1_lip (+ their _l2
  bases — mirror Action-private slot_l2 / rsperm_l2_sq, order-agnostic);
  lcvPair_h2_bdd (from trace bdds); H1 single-state bdds for
  CurvF/QuadF/lieCovR4 (via lieCovR4_eq; hat-bdd = lieOmega_bdd_h2 +
  jet_mono; coeff-bdd = LowBaseInternal.connLow_h2_bdd — VERIFY it
  matches armSlotEndoCc(bdConnPair)); realizedFam tie plumbing block
  (mirror lieCov_h2_tame's hδP/hcP/hP/hP2); then `lieCov_pair_h1`.
* Lean fixes this stretch: rw-first-occurrence hit LHS -> use conv_rhs;
  nlinarith product-monotonicity unreliable -> explicit mul_le_mul
  chains; trace producers need LowBaseInternal qualification.

GREEN TALLY (this session, LowBaseLip/C2Lip/Palatini):
lieOmega_pair_h1 (+app_h21_mul_lip/dom_h1_lip/omega_pair_h1),
riem_pair_h1, hat_eq_lip, curvF_pair_h1, quadB_tel, quadA_tel,
quad_pair_h1, r4_pair_h1, trace4_pair_h2, trace4_h2_bdd,
lcvPair_eq_lip, lcvPair_pair_h2, slot_l2_lip/slot_h1_lip,
rsperm_l2_lip/rsperm_h1_lip, lcvPair_h2_bdd — 14 public/private
declarations, every one focused GREEN; Palatini export band + 2
refreshes; C2Lip export + refresh.  NEXT (the class-2 capstone
`lieCov_pair_h1`): (a) H1 single-state bdds — CurvF (linear, trivial),
QuadF (six blocks; coeff J2 bdd = LowBaseInternal.connLow_h2_bdd
[VERIFY statement matches armSlotEndoCc(bdConnPair)], hat J1 bdd =
lieOmega_bdd_h2 + jet_mono via hat_eq_lip), R4 (via lieCovR4_eq);
(b) realizedFam tie plumbing (mirror lieCov_h2_tame's
hδP/hcP/hP/hP2 block, Action:10724-10760); (c) final telescope via
edgePair_eq (restate as rfl in Lip) + lieCov_residual (PUBLIC) +
app_h21_mul_lip 2 6 2 + slot_h1_lip x2 + rsperm_h1_lip + the pair/bdd
family.  Then classes 4 -> 3 -> 1, master telescope, lowC0_sub
integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CORRECTION (coefficient moduli for QuadF): `connLow_h2_bdd` bounds the
RANK-(3,3) `connLowOp` (public, Action:3388) — NOT the rank-(3,4)
`armSlotEndoCc 2 (bdConnPair g gm)` that lrQA/lrQB carry.  The QuadF
coefficient needs its own J2 pair/bdd: search Action for an
armSlotEndoCc jet-transfer (`armSlot.*h2|armSlot.*jet|EndoCc.*jet`) and
for how lcvPair_h2_low's siblings bounded arm-slot endo coefficients;
the revSlot pattern (`revSlot_bdd_h2`/`revSlot_pair_h2` for
slotInsertEndoCc(fullRaisedEndoField)) is the shape template — a
bdConnPair analogue (`armConn_bdd_h2`/`armConn_pair_h2`) may need
building from the connDiff H2 machinery (C1/C2 connSec/connLow family)
plus an endo-slot jet transfer.

QUADF-COEFFICIENT MODULI (the one genuinely new sub-brick left for the
class-2 capstone): J2 pair/bdd of `armSlotEndoCc 2 (bdConnPair g gm)`
(def MetricArmCoeffJetTower:1959, public) never existed — the H2 route
bounded the OUTER (6,2) lieCovPair only.  Build order: (1) grep C1/C2
for an H2 connDiffSection pair (`connSec_pair_h2`?) or derive from
`connLow_pair_h2` shapes; (2) the endo-slot jet transfer: mirror the
INTERNALS of `LowBaseInternal.revSlot_bdd_h2`/`revSlot_pair_h2` (they
bound slotInsertEndoCc 2 (fullRaisedEndoField) — same TYPE pattern,
different endo content); Palatini:4359
`bdConnDiffSection_eq_armSlotEndoCc_zero` is the s=0 endo/section
bridge (private, rfl-adjacent — check for an s=2 sibling or re-derive);
(3) useful splitters in Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound
(READ-ONLY): `connDiff_cocycle` (:91), `dLaCovKernel_backgroundSplit`
(:248).  Then assemble `lieCov_pair_h1` per the FINAL ASSEMBLY MAP.

ARMCONN MODULI ROUTE (refined): the two-state difference
bdConnPair(gmT) - bdConnPair(gmU) = connDiff(gmT,g) - connDiff(gmU,g)
collapses by `connDiff_cocycle` (DeTurckLieKernelL2JetBound:91, public,
READ-ONLY file) to a single connDiff(gmT,gmU)-type object; its H2 jet
is reachable through the connLowOp packaging: `connLow_pair_h2`
(PUBLIC, C2:4752) gives J2(connLowOp gT - connLowOp gU) <= (C*|T-U|)^2,
and the bridge connDiffSection <-> connLowOp lives in the
`connSec_eq_raise` (C1:892) / `connLower_unit` (Action:171, private —
re-derive if needed) family.  The armSlot jet transfer mirrors
`revSlot_bdd_h2`'s internals (C1:4501: bdd = pair vs base-state +
fr^2-factor; the pair's engine is `revSlot_pair_h2` nearby).  BDD:
zero-state trick as in revSlot_bdd_h2.  All pieces are in claimed or
read-only files; nothing blocks.

REVSLOT ENGINE DISSECTED (C1:4452): pair = `slotInsertEndoCc_sub`
(linearity) + `fullRev_sub` (endo diff = symmRaiseEndo(T-U)) +
`endo_slot_h2` (J2(slotInsert s=2 endo) <= fr^2 * J2(slotInsert 0 endo))
+ s=0 base identification.  For armConn: find/mirror the ARM-version
transfer (`armSlotEndoCc` vs `slotInsertEndoCc` are different
constructors — grep MetricArmCoeffJetTower's public surface for
`arm.*slot.*h2|armSlotEndoCc_sub|arm.*jet` and an endo-difference
linearity `armSlotEndoCc_sub`); the endo DIFFERENCE
bdConnPair(gmT)-bdConnPair(gmU) needs its own `fullRev_sub` analogue
(via connDiff_cocycle).  Everything else for `lieCov_pair_h1` is
assembled and green.  NEXT WINDOW: (1) grep the arm transfer; (2) write
armConn_pair/bdd; (3) H1 bdds (CurvF/QuadF/R4); (4) realizedFam ties;
(5) `lieCov_pair_h1`; then classes 4 -> 3 -> 1, master telescope,
lowC0_sub integral, a1Lo_diff hookup, exact refresh, notes, release
claims.

ARM JET TRANSFER — FINAL DEPTH (the ONE new pointwise lemma left for the
class-2 capstone): the endo_slot chain bottoms out at
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (pointwise fiber-norm
bound under iterated covariant gradients, single-endo slotInsert).  The
arm version `rfns_iteratedCovGrad_armSlotEndoCc_le_*` does not exist;
mirror the slotInsert one (locate + read its proof; likely in the
JetTower/NablaOnTensors layer) with the bilinear endo's extra slot paid
by a v0-basis expansion (one extra fr factor).  Wrappers after it are
mechanical (arm_slot_l2 -> arm_h1/h2, mirroring endo_slot_l2/h2 which
are fully dissected above).  `armSlot_sub_lip` is GREEN (15th this
session; proof pattern = rs-rank ext + fib-level hfib via
armSlotFib_apply_eval + slotInsertEndoFib_sub_left + dsimp-only for the
beta-redex; synthInstance+maxHeartbeats bumps needed).

ARM TRANSFER — COMPLETE IMPLEMENTATION SCRIPT (all proofs dissected):
(1) `armSlot_succ_eq` (new, ~60-80 lines, Lip-private): the arm analogue
    of `slotInsertEndoCc_succ_eq_reindex_slotExtend` (JetTower:2725,
    private — read its proof as template): armSlotEndoCc (s+1) Arm =
    rsDomDomCongr-reindex of slotExtend (armSlotEndoCc s Arm); prove at
    unitModel level via armSlotFib_apply_eval on both sides (the same
    ext+dsimp pattern that landed armSlot_sub_lip).
(2) `rfns_icg_armSlot_le` (new, ~50 lines): VERBATIM mirror of
    `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (JetTower:2795,
    PUBLIC — its induction consumes only the succ-equation +
    `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (public) +
    `rfns_iteratedCovGrad_slotExtend_le` (public)), with base case s=0.
(3) `arm_l2_lip` / `arm_h1_lip` / `arm_h2_lip` wrappers (~40 lines,
    mirror endo_slot_l2/endo_slot_h2 which are fully dissected).
(4) The s=0 base: armSlotEndoCc 0 (bdConnPair g gm) vs
    connDiffSection gm g — `bdConnDiffSection_eq_armSlotEndoCc_zero`
    (JetTower:4359, private, rfl-adjacent — restate in Lip).
(5) armConn moduli: pair via armSlot_sub_lip + connDiff_cocycle +
    transfer to s=0 + connSec H1/H2 machinery; bdd via zero-state trick.
Then `lieCov_pair_h1` per the FINAL ASSEMBLY MAP, classes 4/3/1, master
telescope, integral, a1Lo hookup, exact refresh.

ARM SUCC-EQUATION DERIVATION NOTE: the slotInsert succ template
(JetTower:2725-2792, full text dissected) proves the Cc equation by
ext-chain + `slotInsertEndoFib_apply_eval` + slotExtendFib_apply_eval +
explicit Fin.cases permutation bookkeeping (swap01 on both r and s
sides).  For the ARM version the constructor is NON-square
(g (s+1) (s+2)); derive the correct reindex/rsDom permutations at the
MODEL level from `armSlotFib_apply_eval` (arm s = sIEF (s+1) 0 at
(Arm v0) with vecTail) vs slotExtend-of-arm-s — write the candidate
equation first at unitModel on explicit vectors, read off the two
permutations, then run the ext-chain.  CAUTION: do this with a fresh
context and the :2725 template open side-by-side; the Fin.cases block
is unforgiving.  After it: the rfns mirror induction, the l2/h1/h2
wrappers, then armConn moduli and the capstone — all dissected above.

ARM SUCC-EQUATION — MODEL-LEVEL DERIVATION (s-side DONE):
`slotExtendFib_apply_eval` (OperatorFieldCovariantCalculus:293):
toModel(slotExtendFib A D)(cons v0 vs) = toModel(A (curry D v0)) vs —
the new slot SLICES D first.  Hence
slotExt(armFib s Arm) D' [w0,w1,w2,w3..] = D'[w0, Arm w1 w2, w3, ...]
vs armFib (s+1) Arm D' [v0,v1,v2,v3..] = D'[Arm v0 v1, v2, v3, ...].
Identification (v0,v1)=(w1,w2), v2=w0, rest equal: the INPUT-side
(Fin (s+3)) permutation is the 3-cycle sigma = (swap 0 1).trans
(swap 1 2)  [check: 0->1->2, 1->0->0, 2->2->1 — i.e. w = v after sigma]
— one order deeper than the template's swap01 because the arm eats TWO
slots.  The D'-slot (rsDom) permutation: ArmRes at 0 vs at 1 => swap01
(same as template).  REMAINING: derive the r-side (reindexCoeffGen rho,
Fin (s+2)) by the same model calc on the OPERATOR-as-tensor encoding
(check how reindexCoeffGen acts in the template's :2757 step), then run
the ext-chain with the :2725 template's Fin.cases style (expect one
extra case layer from the 3-cycle).

R-SIDE PINNED: `reindexCoeffFibGen_apply`
(Tensor/CovGrad/RicciDeTurckSectionDifference.lean:4036, PUBLIC):
reindexCoeffFibGen r s rho x A D = A (ofModel (domDomCongr rho
(toModel D))) — the r-side perm acts on the OPERATOR'S ARGUMENT D by
model domDomCongr.  So in the arm succ-equation the rho on Fin (s+2)
(the D'-side) is the swap01 moving the sliced/passthrough D'-slot past
the Arm-output slot (same role as the template's rsDom swap01), and the
sigma on Fin (s+3) (the v-side) is the derived 3-cycle
(swap 0 1).trans (swap 1 2).  ALL permutations for the arm
succ-equation are now determined; write the equation with these and run
the :2725-template ext-chain (expect one extra Fin.cases layer).
Estimated remaining to (N): class-2 capstone ~550 lines; classes 4/3/1
~800-1100; master telescope + integral ~250-400; a1Lo hookup ~100-200;
refreshes/notes/claims; then the endpoint wiring session.

ARM JET TRANSFER — COMPLETE (session count 20 greens): armSlot_sub_lip,
armSlot_succ_lip (perms: rho = swap01 on Fin (s+2), sigma =
(swap 0 1).trans (swap 1 2) on Fin (s+3); after the simp-normalization
chain [TensorMultilinear.tensor0S_curry_apply_eval — NOTE the namespace
qualifier, unknown-identifier was the root cause of 4 failed rw
attempts — , toModel_ofModel, domDomCongr_apply] the three Fin.cases
branches closed by rfl), rfns_arm_le_lip (mirror induction via
both_eq + slotExtend_le), arm_l2/h1/h2_lip wrappers.  NEXT: restate
the s=0 base `bdConnDiffSection_eq_armSlotEndoCc_zero` (JetTower:4359
private) in Lip, then armConn pair/bdd moduli, H1 bdds, ties, capstone.

SESSION UPDATE (allocation flip + armConn moduli, in flight):
- `app_h12_mul_lip` GREEN (mirror of app_h21 via public appRS_h1_h2_h1).
- FLIP EXECUTED: `quad_pair_h1` + `r4_pair_h1` RESTATED with cD at J1 x
  hatT at J2 (D3-free: cD@J2 would need wXi_sub_tame H2 which carries D3).
  Both GREEN post-flip (needed explicit (m := k) levels in the
  jet_nonneg_lip linarith hints -- implicit-level hints produce
  metavariable atoms linarith cannot match).
- dom_h2_lip ALREADY EXISTED at Lip:1815 (do not re-add).
- Palatini `bdConnDiffSection_eq_armSlotEndoCc_zero` now PUBLIC,
  refreshed. C1 `connSec_self_h2` (J2 connSec = J2 wXi) now PUBLIC,
  focused-check green; +C1 refresh in flight.
- INSERTED (pending check): `armU_bdd_h2` (arm@J2 single-state via
  arm_h2_lip + base-eq + connSec_self_h2 + wXi_self_tame; modulus
  (fr*Bs R*A)^2), `armD_pair_h1` (arm@J1 two-state via armSlot_sub +
  arm_h1_lip + base-eq x2 + connSec_pair_h1; modulus
  (fr*B0R*D2 + fr*B1R*A*D2)^2), `hat_bdd_h2` (J2 lrOmegaHat via
  hat_eq_lip + lieOmega_bdd_h2).
- NEXT after these check: CurvF single-state H1 bdd (linear in T-U =
  use curvF_pair_h1 with U := 0? CurvF is linear in T: curvF_pair
  bounds J1(CF_T - CF_U) by J2(T-U); single-state = pair with U=0 IF
  lrCurvF g 0 = 0 -- check; else direct), then the class-2 capstone
  `lieCov_pair_h1` assembly per FINAL ASSEMBLY MAP.

CAPSTONE PLAN (lieCov_pair_h1, all ingredients verified):
- Unit: class2(T) := armField(gm_s) - edgeLiePairFam(T,lieRefoldQ,lieRefoldEps,s)
  = residual(T) by edgePair_eq (Action-private rfl -> RESTATE in Lip as rfl)
  + lieCov_residual (Palatini PUBLIC; hyps hδ_lt/hδ/hδZ/hTsymm/hs).
  residual(T) = (-1)•app 2 6 2 (Pair gm_s) (X_T), X_T = rsDom 2 6 lieCovSigma
  (slotExtendIter 0 4 2 R4_T); slotExtendIter 2 = slotExtend∘slotExtend RFL.
- Telescope: res_T - res_U = (-1)•[app(PairDiff, X_T) + app(Pair_U, Xdiff)].
- J1 bounds: jet_smul ((-1)²) + jet_add; term1 app_h21 2 6 2:
  J2(PairDiff)=lcvPair_pair_h2 (ρ-ball hyp, Hs-norm currency) ×
  J1(X_T) ≤ fr²·J1(R4_T) [rsperm_h1= + slot_h1×2] ≤ fr²(DrR(A+A²))² [r4_bdd_h1];
  term2: J2(Pair_U)=lcvPair_h2_bdd (ρ-ball) × J1(Xdiff) ≤ fr²·J1(R4diff)
  [same transfers via armSlot? NO — Xdiff transfers termwise: rsDom/slotExt are
  LINEAR: Xdiff = rsDom(Ext²(R4_T − R4_U)) needs slotExtend_sub + rsDom_sub
  (grep or prove rfl/ext) then ≤ fr²·(r4_pair_h1 RHS, discharged by
  armU_bdd+armD_pair+hat_bdd+lieOmega_pair moduli at P/Q].
- Currency: conclusion (B R * (1 + A + A ^ 2) ^ 2 * D2) ^ 2; all products
  folded by nlinarith on set-folded reals with explicit product-nonneg hints
  (REMEMBER (m := k) explicit levels in jet_nonneg_lip hints).
- Plumbing ×2 (P=s•T, Q=s•U) verbatim from Lip:588-652 idiom.
- MISSING-CHECK LIST before writing: slotExtend_sub / rsDomDomCongrSection_sub
  linearity lemmas; lcvPair_pair_h2 full conclusion tail; r4_pair_h1 arm/hat
  term discharge order.

X-TRANSFER GREEN (covX_bdd_h1 + covX_pair_h1) + armU/armD/hat + A/B/C
(curvF_zero/curvF_bdd/quadF_bdd/r4_bdd) + edgePair_eq_lip + rsperm_sub_lip
ALL GREEN.  Lessons: (1) hat_bdd/quadF placement must be AFTER
lieOmega_bdd_h2 (:~4300) -- forward-ref moved wholesale; (2) armD needs
synthInstance.maxHeartbeats 1000000 (armSlot_sub ContinuousAdd synth);
(3) THE whnf-timeout culprit in big folds = final-calc `nlinarith` over
composite scalar monomials -- fix = explicit `hsum` linarith combination
+ `le_of_eq ... ring` factoring split (same lesson as quad_pair, now
confirmed twice); (4) rsperm_sub_lip closes by simp only [rsDomDomCongr]
+ rfl (comp_sub unused); (5) sqrt-constant ring tails need `show`-cast
to isolate sqrt^2 before rw [Real.sq_sqrt].
NEXT: capstone lieCov_pair_h1 assembly (short now): units via
edgePair_eq_lip + lieCov_residual (rw [<- hgmT] at hUT to match
set-folded goal), telescope via appCcRS_sub_left/right + module,
app_h21_mul_lip 2 6 2, lcvPair_pair/bdd at (P,Q,gmT,gmU) with Hs-ball
plumbing (:653 idiom), covX pair/bdd, fold to
B R * ((1+A+A^2)^4 * (D2^2 + N^2)).

*** CLASS-2 CAPSTONE `lieCov_pair_h1` GREEN (first try, 126.5s) ***
Conclusion: J1(class2diff @ fixed s) <= B R * ((1+A+A^2)^4 * (D2^2+N^2))
(two-currency: D2 = jet H2 difference, N = Hs2 spectral difference norm;
sizes R/A symmetric both states incl. hU3; rho-ball = min(rho_pair,
rho_bdd) on Hs2 T/U).  Whole chain green: unit (edgePair_eq_lip rfl +
lieCov_residual public) -> telescope (appCcRS_sub_left/right + module)
-> app_h21 2 6 2 -> lcvPair pair/bdd + covX pair/bdd.
CLASS 2 OF 5 DONE.  Ordering ruling: next 4 (lc0AMix) -> 3 (lc0VB) ->
1 (ricciGoodLow) -> master telescope (selfLow_parts, 5-term jet_add
ladder at fixed s) -> path integral (lowC0Diff via
iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame
:517) -> a1Lo_diff hookup (Pair).

CLASS-4 (lc0AMix) PLAN — skeleton verified from LieCorr0AMixRefold:
- `amix_refold_rf` PUBLIC: lc0AMix = lc0AMixFormRF = 2•(Half(perm2) +
  Half(swap*perm2)); Half(σ) = app 2 4 2 (Tr2 σ) (app 2 6 4 (Tr4 perm1)
  (app 2 3 6 (Ext³ mcd) (app 2 5 3 (Tr3 permQ) (Ext² mcd)))) where
  Tr_p(σ) = reindexCoeffGen (pureTrace g gm p) σ (MOVING cometric,
  gm-dep!), mcd = metricConnDiffLoweredCc g gm g (both slots coincide at
  gB=g₀=g).
- mcd_pair_h1 DONE GREEN in C1 (D2-only modulus (B0R·D2+B1R·A·D2)²;
  via mcd_sub_eq + wXi_pair_h1 + metricCorr_pair_h1 [pre-existing
  PUBLIC!] + wXi_h2_low + jet folding; 140.9s).  mcd_pair_h2 is
  D3-infected — never use in C0 lane.
- Telescope: 5 moving factors per half → 5 difference terms; allocation
  per term: difference factor at its level (traces at J2-pair D2-safe;
  mcd at J1-pair via mcd_pair_h1 when innermost, else J2?? NO — mcd at
  J2-pair is D3 ⟹ mcd-difference must always sit in the J1 slot of an
  h21 app; traces-diff can sit at J2 (h21 outer slot).  Nesting: outer
  app J1 conclusion via app_h21 (Φ@J2 × W@J1): put ALL trace-diffs in
  Φ-slots (J2-pair) and mcd-diffs inside W-chains at J1.  The two
  mcd-slot diff terms need J1(app-chain diff) recursion: inner app 2 5 3
  (Tr3, Ext²mcd): diff in mcd → J1 via app_h12?? app 2 5 3 with W=Ext²
  mcdDiff at J2?? — NO: use app_h21 with Φ=Tr3@J2-bdd × W=Ext²(mcdDiff)
  @J1 [slot transfer + mcd_pair_h1] ✓; diff in Tr3 → Φ=Tr3Diff@J2-pair ×
  W=Ext²(mcd_U)@J1-bdd ✓.
- INVENTORY TO CHECK/BUILD: trace3_pair_h2 + trace3_h2_bdd (trace2/4
  exist); J2 slot transfer (slot_h2_lip) for Ext²/Ext³; reindexCoeffGen
  jet transfer (Tr_p = reindex(pureTrace p, σ) — need jet equality or
  transfer under reindexCoeffGen at J1/J2 — check JetTower rfns
  machinery); mcd J1/J2 single bdd (mcd_h2_bdd C1 public — check shape);
  then 5-term telescope + (1+A+A²)-currency fold; conclusion target
  J1(lc0AMix g gmT g − lc0AMix g gmU g) ≤ B R·((1+A+A²)^k·D2²)-form
  (no N-term — amix has no Hs-ball currency unless trace moduli demand
  ρ-balls — trace2/4 moduli DO carry ρ (Hs-ball) → conclusion carries
  ρ-ball hyps like class 2).

!!! INCIDENT (2026-07-30): DeTurckRemainderLowBaseLip.lean was TRUNCATED
TO 0 BYTES by a python io.open(w) whose .write raised
UnicodeEncodeError (lone surrogates from a U+1D55C escape pair in a
staging script) AFTER truncating.  No commits existed for the session
work.  RECOVERY: git HEAD (b6c85d213) holds the file through
riem_pair_h1 (3088 lines); every later edit was replayed from this
session transcript (scratchpad/replay/ holds extractor + driver).
LESSONS (PERMANENT): (1) NEVER io.open(path,'w') directly on repo
sources - write temp + os.replace() (atomic) or try-guard the write;
(2) python staging files holding surrogate-PAIR escapes become LONE
surrogates - normalize with errors='surrogatepass' before use;
(3) checkpoint commits after each multi-hundred-line GREEN milestone
would make this a non-event - ask user to lift no-commit for
checkpoints.

*** CLASS-4 (lc0AMix) COMPLETE ***: mcd_pair_h1 (C1) + trace3 family
(C2: insert4_jet_c2/trace3_h2_lip/trace3_pair_h2/trace3_h2_bdd) +
slot_h2_lip/reindex_jet_lip/reindex_sub_lip/trPair_sub_lip/trPair_jet_lip
+ amixHalf_pair_h1 (five-level telescope, 328.6s) + amix_pair_h1
(FormRF wrapper, 16*Bh constant, 299.2s) ALL GREEN.  Currency:
B R * ((1+A+A^2)^4 * (D2^2+N^2)) — same as class 2.
Lessons: perms are LieCorr0Core.* (TameLipschitz's copies are private);
`simp only [K]` can close goals fully (drop trailing ring on "No goals");
S4b needed DUAL constants (Ca4-J1 vs Ca4b-J2 chains).
STATE: classes 2/4/5? green; 3 (lc0VB) + 1 (ricciGoodLow) recon+draft
DISPATCHED TO OPUS subagents (drafts land in scratchpad opus_vb/ and
opus_good/); NEXT after integration = master five-class telescope at
fixed s (selfLow_parts), lowC0Diff path integral
(iteratedCovGrad_pathIntegralCoeffField_jetL2_le, mirror c1Diff_tame),
a1Lo_diff hookup (Pair file).

MULTI-AGENT PHASE (user upgraded to ultra; Opus dispatch authorized):
- GREEN so far this phase: selfLow_sub_parts (master telescope EQUATION,
  module not abel for (-2:ℝ)•), vb safe helpers
  (rsperm_h2_lip/ipHead/ip_form_lip/ip_sub_lip).
- OPUS RECON DONE: class-3 (vb): refold vb_refold_rf PUBLIC
  (LieCorr0VBRefold.lean:120), 3-term telescope, budget (1+A+A²)⁴ EXACT;
  draft at scratchpad opus_vb/vb_pair_h1_draft.lean (811 lines);
  prerequisites M1/M2 = trace1_pair_h2/trace1_h2_bdd (C2) + M3 =
  vbmcd_perm_eq (vbMcdArm = rsDom(VBPerm)(Ext(mcd)); the in-tree
  vbMcdArm_rel + vbPK_eq_slotExt are PRIVATE in READ-ONLY
  LieCorr0CoeffL2JetBound.lean:1082 — must re-derive at model level in
  C1 (public) using tensor0SProdKappaFib/slotExtendFib_apply_eval).
- class-1 (good): ricciGoodLow = ccInputSymm(AA + DA); (s•T)-slot enters
  ONLY via covGrad in DA (one D2-term); AA = connSec-insertions
  (connDiffContrInsertionField_eq_reindex_slotExtend_two etc. PUBLIC) ×
  trace2; missing: dagLow_bdd_h2 (recommend claiming Action +
  publicizing dagLow_h2_rf + connLow_h3_rf), fullSlot_bdd_h2 +
  fullSlot_pair_h1 (Opus building in C1 now; check gInvDiffRaisedEndoField
  relation); draft at opus_good/good_pair_h1_draft.lean (~1180 lines,
  AA arm + capstone complete, gaps marked sorry).
- BUILDERS IN FLIGHT: Opus@C2 trace1 family (token 99f2...), Opus@C1
  fullSlot bricks (token e2aa...).  QUEUED: Opus@C1 vbmcd_perm_eq
  re-derivation (after fullSlot agent frees C1).
- INTEGRATION ORDER: trace1 lands -> I insert vb body (minus
  vbmcd-dependents until bridge) into Lip; fullSlot+dagLow land ->
  good_pair_h1; then master five-class J1 bound at fixed s (uses
  selfLow_sub_parts + 5 class moduli), c0Diff_tame (mirror c1Diff_tame
  :517-746, engine path_jetL2_le g 2 2 1), lowBaseDiff_c0 already wired,
  final a1Lo_diff-style Pair endpoint.

CLASS-2 CONSTRUCTION LOG (this session, all focused GREEN in LowBaseLip):
* `hat_eq_lip` (rfl: lrOmegaHat = lipOmega), `curvF_pair_h1` (linear
  J1<=C*J2(T-U)), `quadB_tel`/`quadA_tel` (two-slot app telescopes),
  `quad_pair_h1` (six-block lrQuadF telescope, abstract product form),
  `r4_pair_h1` (lieCovR4 pair via the public `lieCovR4_eq`, s in Icc01,
  conclusion C*(J2(T-U) + [J2(cU)*J1(hatD) + J2(cD)*J1(hatT)] at
  realizedFam metrics)).
* PALATINI EXPORTS this session: + lrPermA/B/C (the perms appear in
  lrQuadF's body and must be nameable downstream).  Palatini re-checked
  green + refreshed after each export batch.
* NEW DURABLE LESSON (cured a hard whnf wall at 1.6M heartbeats): in this
  file (respectTransparency false), the jet-chain arithmetic over tensor
  atoms MUST be closed by `linarith [explicit jet_add_lip applications +
  dom equations + prior bounds]` — `exact add_le_add_left ... _`,
  `gcongr`, and goal-side `nlinarith` all whnf-explode on the tensor
  atoms.  Fold every jet value with `set ... with h` and do the final
  numeric step on the folded real variables.
REMAINING for class 2: (iii) lcvPair coefficient pair at H2 (lieCovPair
is PUBLIC Palatini:3627; mirror the private lcvPair_h2_low Action:9138
from its public inputs), (iv) H1Poly mini-plumbing + `lieCov_pair_h1`
assembly plugging the concrete moduli (connLow pair/bdd for the
b-slots, lieOmega machinery via hat_eq_lip for the hat slots).

CLASS-2 FINAL ASSEMBLY MAP (all bridges verified):
* unit equation: `edgePair_eq` is rfl (Action-private but rfl —
  restate in Lip); `lieCov_residual` PUBLIC (Palatini:9033):
  armField(gm_s) - RefoldPairTraceFamily(q,eps,s) = (-1) . appCcRS 2 6 2
  (lieCovPair gm_s) (rsDom lieCovSigma (slotExtendIter 2 (lieCovR4 T s))),
  hyps = hTsymm + hs in Icc01 + hdelta_lt.
* Telescope: unitT - unitU = (-1).[app(PairDiff, X_T) + app(Pair gmU,
  X_T - X_U)], X_S = rsDom lieCovSigma (Ext^2 (lieCovR4 S s)).
* NEW GREEN this stretch: trace4_pair_h2 + trace4_h2_bdd (C2Lip, public,
  .2-projection of trace24_h2_lip + zero-state trick; C2Lip refreshed),
  lcvPair_eq_lip (rfl) + lcvPair_pair_h2 (Lip; telescope over
  trace2/trace4 pair+bdd via app_h2_mul_lip 6 4 2; NOTE trace producers
  are LowBaseInternal.* qualified).
* STILL TO BUILD (patterned): slot_h1_lip / rsperm_h1_lip (+ their _l2
  bases — mirror Action-private slot_l2 / rsperm_l2_sq, order-agnostic);
  lcvPair_h2_bdd (from trace bdds); H1 single-state bdds for
  CurvF/QuadF/lieCovR4 (via lieCovR4_eq; hat-bdd = lieOmega_bdd_h2 +
  jet_mono; coeff-bdd = LowBaseInternal.connLow_h2_bdd — VERIFY it
  matches armSlotEndoCc(bdConnPair)); realizedFam tie plumbing block
  (mirror lieCov_h2_tame's hδP/hcP/hP/hP2); then `lieCov_pair_h1`.
* Lean fixes this stretch: rw-first-occurrence hit LHS -> use conv_rhs;
  nlinarith product-monotonicity unreliable -> explicit mul_le_mul
  chains; trace producers need LowBaseInternal qualification.

GREEN TALLY (this session, LowBaseLip/C2Lip/Palatini):
lieOmega_pair_h1 (+app_h21_mul_lip/dom_h1_lip/omega_pair_h1),
riem_pair_h1, hat_eq_lip, curvF_pair_h1, quadB_tel, quadA_tel,
quad_pair_h1, r4_pair_h1, trace4_pair_h2, trace4_h2_bdd,
lcvPair_eq_lip, lcvPair_pair_h2, slot_l2_lip/slot_h1_lip,
rsperm_l2_lip/rsperm_h1_lip, lcvPair_h2_bdd — 14 public/private
declarations, every one focused GREEN; Palatini export band + 2
refreshes; C2Lip export + refresh.  NEXT (the class-2 capstone
`lieCov_pair_h1`): (a) H1 single-state bdds — CurvF (linear, trivial),
QuadF (six blocks; coeff J2 bdd = LowBaseInternal.connLow_h2_bdd
[VERIFY statement matches armSlotEndoCc(bdConnPair)], hat J1 bdd =
lieOmega_bdd_h2 + jet_mono via hat_eq_lip), R4 (via lieCovR4_eq);
(b) realizedFam tie plumbing (mirror lieCov_h2_tame's
hδP/hcP/hP/hP2 block, Action:10724-10760); (c) final telescope via
edgePair_eq (restate as rfl in Lip) + lieCov_residual (PUBLIC) +
app_h21_mul_lip 2 6 2 + slot_h1_lip x2 + rsperm_h1_lip + the pair/bdd
family.  Then classes 4 -> 3 -> 1, master telescope, lowC0_sub
integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CORRECTION (coefficient moduli for QuadF): `connLow_h2_bdd` bounds the
RANK-(3,3) `connLowOp` (public, Action:3388) — NOT the rank-(3,4)
`armSlotEndoCc 2 (bdConnPair g gm)` that lrQA/lrQB carry.  The QuadF
coefficient needs its own J2 pair/bdd: search Action for an
armSlotEndoCc jet-transfer (`armSlot.*h2|armSlot.*jet|EndoCc.*jet`) and
for how lcvPair_h2_low's siblings bounded arm-slot endo coefficients;
the revSlot pattern (`revSlot_bdd_h2`/`revSlot_pair_h2` for
slotInsertEndoCc(fullRaisedEndoField)) is the shape template — a
bdConnPair analogue (`armConn_bdd_h2`/`armConn_pair_h2`) may need
building from the connDiff H2 machinery (C1/C2 connSec/connLow family)
plus an endo-slot jet transfer.

QUADF-COEFFICIENT MODULI (the one genuinely new sub-brick left for the
class-2 capstone): J2 pair/bdd of `armSlotEndoCc 2 (bdConnPair g gm)`
(def MetricArmCoeffJetTower:1959, public) never existed — the H2 route
bounded the OUTER (6,2) lieCovPair only.  Build order: (1) grep C1/C2
for an H2 connDiffSection pair (`connSec_pair_h2`?) or derive from
`connLow_pair_h2` shapes; (2) the endo-slot jet transfer: mirror the
INTERNALS of `LowBaseInternal.revSlot_bdd_h2`/`revSlot_pair_h2` (they
bound slotInsertEndoCc 2 (fullRaisedEndoField) — same TYPE pattern,
different endo content); Palatini:4359
`bdConnDiffSection_eq_armSlotEndoCc_zero` is the s=0 endo/section
bridge (private, rfl-adjacent — check for an s=2 sibling or re-derive);
(3) useful splitters in Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound
(READ-ONLY): `connDiff_cocycle` (:91), `dLaCovKernel_backgroundSplit`
(:248).  Then assemble `lieCov_pair_h1` per the FINAL ASSEMBLY MAP.

ARMCONN MODULI ROUTE (refined): the two-state difference
bdConnPair(gmT) - bdConnPair(gmU) = connDiff(gmT,g) - connDiff(gmU,g)
collapses by `connDiff_cocycle` (DeTurckLieKernelL2JetBound:91, public,
READ-ONLY file) to a single connDiff(gmT,gmU)-type object; its H2 jet
is reachable through the connLowOp packaging: `connLow_pair_h2`
(PUBLIC, C2:4752) gives J2(connLowOp gT - connLowOp gU) <= (C*|T-U|)^2,
and the bridge connDiffSection <-> connLowOp lives in the
`connSec_eq_raise` (C1:892) / `connLower_unit` (Action:171, private —
re-derive if needed) family.  The armSlot jet transfer mirrors
`revSlot_bdd_h2`'s internals (C1:4501: bdd = pair vs base-state +
fr^2-factor; the pair's engine is `revSlot_pair_h2` nearby).  BDD:
zero-state trick as in revSlot_bdd_h2.  All pieces are in claimed or
read-only files; nothing blocks.

REVSLOT ENGINE DISSECTED (C1:4452): pair = `slotInsertEndoCc_sub`
(linearity) + `fullRev_sub` (endo diff = symmRaiseEndo(T-U)) +
`endo_slot_h2` (J2(slotInsert s=2 endo) <= fr^2 * J2(slotInsert 0 endo))
+ s=0 base identification.  For armConn: find/mirror the ARM-version
transfer (`armSlotEndoCc` vs `slotInsertEndoCc` are different
constructors — grep MetricArmCoeffJetTower's public surface for
`arm.*slot.*h2|armSlotEndoCc_sub|arm.*jet` and an endo-difference
linearity `armSlotEndoCc_sub`); the endo DIFFERENCE
bdConnPair(gmT)-bdConnPair(gmU) needs its own `fullRev_sub` analogue
(via connDiff_cocycle).  Everything else for `lieCov_pair_h1` is
assembled and green.  NEXT WINDOW: (1) grep the arm transfer; (2) write
armConn_pair/bdd; (3) H1 bdds (CurvF/QuadF/R4); (4) realizedFam ties;
(5) `lieCov_pair_h1`; then classes 4 -> 3 -> 1, master telescope,
lowC0_sub integral, a1Lo_diff hookup, exact refresh, notes, release
claims.

ARM JET TRANSFER — FINAL DEPTH (the ONE new pointwise lemma left for the
class-2 capstone): the endo_slot chain bottoms out at
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (pointwise fiber-norm
bound under iterated covariant gradients, single-endo slotInsert).  The
arm version `rfns_iteratedCovGrad_armSlotEndoCc_le_*` does not exist;
mirror the slotInsert one (locate + read its proof; likely in the
JetTower/NablaOnTensors layer) with the bilinear endo's extra slot paid
by a v0-basis expansion (one extra fr factor).  Wrappers after it are
mechanical (arm_slot_l2 -> arm_h1/h2, mirroring endo_slot_l2/h2 which
are fully dissected above).  `armSlot_sub_lip` is GREEN (15th this
session; proof pattern = rs-rank ext + fib-level hfib via
armSlotFib_apply_eval + slotInsertEndoFib_sub_left + dsimp-only for the
beta-redex; synthInstance+maxHeartbeats bumps needed).

ARM TRANSFER — COMPLETE IMPLEMENTATION SCRIPT (all proofs dissected):
(1) `armSlot_succ_eq` (new, ~60-80 lines, Lip-private): the arm analogue
    of `slotInsertEndoCc_succ_eq_reindex_slotExtend` (JetTower:2725,
    private — read its proof as template): armSlotEndoCc (s+1) Arm =
    rsDomDomCongr-reindex of slotExtend (armSlotEndoCc s Arm); prove at
    unitModel level via armSlotFib_apply_eval on both sides (the same
    ext+dsimp pattern that landed armSlot_sub_lip).
(2) `rfns_icg_armSlot_le` (new, ~50 lines): VERBATIM mirror of
    `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (JetTower:2795,
    PUBLIC — its induction consumes only the succ-equation +
    `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (public) +
    `rfns_iteratedCovGrad_slotExtend_le` (public)), with base case s=0.
(3) `arm_l2_lip` / `arm_h1_lip` / `arm_h2_lip` wrappers (~40 lines,
    mirror endo_slot_l2/endo_slot_h2 which are fully dissected).
(4) The s=0 base: armSlotEndoCc 0 (bdConnPair g gm) vs
    connDiffSection gm g — `bdConnDiffSection_eq_armSlotEndoCc_zero`
    (JetTower:4359, private, rfl-adjacent — restate in Lip).
(5) armConn moduli: pair via armSlot_sub_lip + connDiff_cocycle +
    transfer to s=0 + connSec H1/H2 machinery; bdd via zero-state trick.
Then `lieCov_pair_h1` per the FINAL ASSEMBLY MAP, classes 4/3/1, master
telescope, integral, a1Lo hookup, exact refresh.

ARM SUCC-EQUATION DERIVATION NOTE: the slotInsert succ template
(JetTower:2725-2792, full text dissected) proves the Cc equation by
ext-chain + `slotInsertEndoFib_apply_eval` + slotExtendFib_apply_eval +
explicit Fin.cases permutation bookkeeping (swap01 on both r and s
sides).  For the ARM version the constructor is NON-square
(g (s+1) (s+2)); derive the correct reindex/rsDom permutations at the
MODEL level from `armSlotFib_apply_eval` (arm s = sIEF (s+1) 0 at
(Arm v0) with vecTail) vs slotExtend-of-arm-s — write the candidate
equation first at unitModel on explicit vectors, read off the two
permutations, then run the ext-chain.  CAUTION: do this with a fresh
context and the :2725 template open side-by-side; the Fin.cases block
is unforgiving.  After it: the rfns mirror induction, the l2/h1/h2
wrappers, then armConn moduli and the capstone — all dissected above.

ARM SUCC-EQUATION — MODEL-LEVEL DERIVATION (s-side DONE):
`slotExtendFib_apply_eval` (OperatorFieldCovariantCalculus:293):
toModel(slotExtendFib A D)(cons v0 vs) = toModel(A (curry D v0)) vs —
the new slot SLICES D first.  Hence
slotExt(armFib s Arm) D' [w0,w1,w2,w3..] = D'[w0, Arm w1 w2, w3, ...]
vs armFib (s+1) Arm D' [v0,v1,v2,v3..] = D'[Arm v0 v1, v2, v3, ...].
Identification (v0,v1)=(w1,w2), v2=w0, rest equal: the INPUT-side
(Fin (s+3)) permutation is the 3-cycle sigma = (swap 0 1).trans
(swap 1 2)  [check: 0->1->2, 1->0->0, 2->2->1 — i.e. w = v after sigma]
— one order deeper than the template's swap01 because the arm eats TWO
slots.  The D'-slot (rsDom) permutation: ArmRes at 0 vs at 1 => swap01
(same as template).  REMAINING: derive the r-side (reindexCoeffGen rho,
Fin (s+2)) by the same model calc on the OPERATOR-as-tensor encoding
(check how reindexCoeffGen acts in the template's :2757 step), then run
the ext-chain with the :2725 template's Fin.cases style (expect one
extra case layer from the 3-cycle).

R-SIDE PINNED: `reindexCoeffFibGen_apply`
(Tensor/CovGrad/RicciDeTurckSectionDifference.lean:4036, PUBLIC):
reindexCoeffFibGen r s rho x A D = A (ofModel (domDomCongr rho
(toModel D))) — the r-side perm acts on the OPERATOR'S ARGUMENT D by
model domDomCongr.  So in the arm succ-equation the rho on Fin (s+2)
(the D'-side) is the swap01 moving the sliced/passthrough D'-slot past
the Arm-output slot (same role as the template's rsDom swap01), and the
sigma on Fin (s+3) (the v-side) is the derived 3-cycle
(swap 0 1).trans (swap 1 2).  ALL permutations for the arm
succ-equation are now determined; write the equation with these and run
the :2725-template ext-chain (expect one extra Fin.cases layer).
Estimated remaining to (N): class-2 capstone ~550 lines; classes 4/3/1
~800-1100; master telescope + integral ~250-400; a1Lo hookup ~100-200;
refreshes/notes/claims; then the endpoint wiring session.

ARM JET TRANSFER — COMPLETE (session count 20 greens): armSlot_sub_lip,
armSlot_succ_lip (perms: rho = swap01 on Fin (s+2), sigma =
(swap 0 1).trans (swap 1 2) on Fin (s+3); after the simp-normalization
chain [TensorMultilinear.tensor0S_curry_apply_eval — NOTE the namespace
qualifier, unknown-identifier was the root cause of 4 failed rw
attempts — , toModel_ofModel, domDomCongr_apply] the three Fin.cases
branches closed by rfl), rfns_arm_le_lip (mirror induction via
both_eq + slotExtend_le), arm_l2/h1/h2_lip wrappers.  NEXT: restate
the s=0 base `bdConnDiffSection_eq_armSlotEndoCc_zero` (JetTower:4359
private) in Lip, then armConn pair/bdd moduli, H1 bdds, ties, capstone.

CLASS-2 CONSTRUCTION LOG (this session, all focused GREEN in LowBaseLip):
* `hat_eq_lip` (rfl: lrOmegaHat = lipOmega), `curvF_pair_h1` (linear
  J1<=C*J2(T-U)), `quadB_tel`/`quadA_tel` (two-slot app telescopes),
  `quad_pair_h1` (six-block lrQuadF telescope, abstract product form),
  `r4_pair_h1` (lieCovR4 pair via the public `lieCovR4_eq`, s in Icc01,
  conclusion C*(J2(T-U) + [J2(cU)*J1(hatD) + J2(cD)*J1(hatT)] at
  realizedFam metrics)).
* PALATINI EXPORTS this session: + lrPermA/B/C (the perms appear in
  lrQuadF's body and must be nameable downstream).  Palatini re-checked
  green + refreshed after each export batch.
* NEW DURABLE LESSON (cured a hard whnf wall at 1.6M heartbeats): in this
  file (respectTransparency false), the jet-chain arithmetic over tensor
  atoms MUST be closed by `linarith [explicit jet_add_lip applications +
  dom equations + prior bounds]` — `exact add_le_add_left ... _`,
  `gcongr`, and goal-side `nlinarith` all whnf-explode on the tensor
  atoms.  Fold every jet value with `set ... with h` and do the final
  numeric step on the folded real variables.
REMAINING for class 2: (iii) lcvPair coefficient pair at H2 (lieCovPair
is PUBLIC Palatini:3627; mirror the private lcvPair_h2_low Action:9138
from its public inputs), (iv) H1Poly mini-plumbing + `lieCov_pair_h1`
assembly plugging the concrete moduli (connLow pair/bdd for the
b-slots, lieOmega machinery via hat_eq_lip for the hat slots).

CLASS-2 FINAL ASSEMBLY MAP (all bridges verified):
* unit equation: `edgePair_eq` is rfl (Action-private but rfl —
  restate in Lip); `lieCov_residual` PUBLIC (Palatini:9033):
  armField(gm_s) - RefoldPairTraceFamily(q,eps,s) = (-1) . appCcRS 2 6 2
  (lieCovPair gm_s) (rsDom lieCovSigma (slotExtendIter 2 (lieCovR4 T s))),
  hyps = hTsymm + hs in Icc01 + hdelta_lt.
* Telescope: unitT - unitU = (-1).[app(PairDiff, X_T) + app(Pair gmU,
  X_T - X_U)], X_S = rsDom lieCovSigma (Ext^2 (lieCovR4 S s)).
* NEW GREEN this stretch: trace4_pair_h2 + trace4_h2_bdd (C2Lip, public,
  .2-projection of trace24_h2_lip + zero-state trick; C2Lip refreshed),
  lcvPair_eq_lip (rfl) + lcvPair_pair_h2 (Lip; telescope over
  trace2/trace4 pair+bdd via app_h2_mul_lip 6 4 2; NOTE trace producers
  are LowBaseInternal.* qualified).
* STILL TO BUILD (patterned): slot_h1_lip / rsperm_h1_lip (+ their _l2
  bases — mirror Action-private slot_l2 / rsperm_l2_sq, order-agnostic);
  lcvPair_h2_bdd (from trace bdds); H1 single-state bdds for
  CurvF/QuadF/lieCovR4 (via lieCovR4_eq; hat-bdd = lieOmega_bdd_h2 +
  jet_mono; coeff-bdd = LowBaseInternal.connLow_h2_bdd — VERIFY it
  matches armSlotEndoCc(bdConnPair)); realizedFam tie plumbing block
  (mirror lieCov_h2_tame's hδP/hcP/hP/hP2); then `lieCov_pair_h1`.
* Lean fixes this stretch: rw-first-occurrence hit LHS -> use conv_rhs;
  nlinarith product-monotonicity unreliable -> explicit mul_le_mul
  chains; trace producers need LowBaseInternal qualification.

GREEN TALLY (this session, LowBaseLip/C2Lip/Palatini):
lieOmega_pair_h1 (+app_h21_mul_lip/dom_h1_lip/omega_pair_h1),
riem_pair_h1, hat_eq_lip, curvF_pair_h1, quadB_tel, quadA_tel,
quad_pair_h1, r4_pair_h1, trace4_pair_h2, trace4_h2_bdd,
lcvPair_eq_lip, lcvPair_pair_h2, slot_l2_lip/slot_h1_lip,
rsperm_l2_lip/rsperm_h1_lip, lcvPair_h2_bdd — 14 public/private
declarations, every one focused GREEN; Palatini export band + 2
refreshes; C2Lip export + refresh.  NEXT (the class-2 capstone
`lieCov_pair_h1`): (a) H1 single-state bdds — CurvF (linear, trivial),
QuadF (six blocks; coeff J2 bdd = LowBaseInternal.connLow_h2_bdd
[VERIFY statement matches armSlotEndoCc(bdConnPair)], hat J1 bdd =
lieOmega_bdd_h2 + jet_mono via hat_eq_lip), R4 (via lieCovR4_eq);
(b) realizedFam tie plumbing (mirror lieCov_h2_tame's
hδP/hcP/hP/hP2 block, Action:10724-10760); (c) final telescope via
edgePair_eq (restate as rfl in Lip) + lieCov_residual (PUBLIC) +
app_h21_mul_lip 2 6 2 + slot_h1_lip x2 + rsperm_h1_lip + the pair/bdd
family.  Then classes 4 -> 3 -> 1, master telescope, lowC0_sub
integral, a1Lo_diff hookup, ONE exact LowBaseLip refresh.

CORRECTION (coefficient moduli for QuadF): `connLow_h2_bdd` bounds the
RANK-(3,3) `connLowOp` (public, Action:3388) — NOT the rank-(3,4)
`armSlotEndoCc 2 (bdConnPair g gm)` that lrQA/lrQB carry.  The QuadF
coefficient needs its own J2 pair/bdd: search Action for an
armSlotEndoCc jet-transfer (`armSlot.*h2|armSlot.*jet|EndoCc.*jet`) and
for how lcvPair_h2_low's siblings bounded arm-slot endo coefficients;
the revSlot pattern (`revSlot_bdd_h2`/`revSlot_pair_h2` for
slotInsertEndoCc(fullRaisedEndoField)) is the shape template — a
bdConnPair analogue (`armConn_bdd_h2`/`armConn_pair_h2`) may need
building from the connDiff H2 machinery (C1/C2 connSec/connLow family)
plus an endo-slot jet transfer.

QUADF-COEFFICIENT MODULI (the one genuinely new sub-brick left for the
class-2 capstone): J2 pair/bdd of `armSlotEndoCc 2 (bdConnPair g gm)`
(def MetricArmCoeffJetTower:1959, public) never existed — the H2 route
bounded the OUTER (6,2) lieCovPair only.  Build order: (1) grep C1/C2
for an H2 connDiffSection pair (`connSec_pair_h2`?) or derive from
`connLow_pair_h2` shapes; (2) the endo-slot jet transfer: mirror the
INTERNALS of `LowBaseInternal.revSlot_bdd_h2`/`revSlot_pair_h2` (they
bound slotInsertEndoCc 2 (fullRaisedEndoField) — same TYPE pattern,
different endo content); Palatini:4359
`bdConnDiffSection_eq_armSlotEndoCc_zero` is the s=0 endo/section
bridge (private, rfl-adjacent — check for an s=2 sibling or re-derive);
(3) useful splitters in Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound
(READ-ONLY): `connDiff_cocycle` (:91), `dLaCovKernel_backgroundSplit`
(:248).  Then assemble `lieCov_pair_h1` per the FINAL ASSEMBLY MAP.

ARMCONN MODULI ROUTE (refined): the two-state difference
bdConnPair(gmT) - bdConnPair(gmU) = connDiff(gmT,g) - connDiff(gmU,g)
collapses by `connDiff_cocycle` (DeTurckLieKernelL2JetBound:91, public,
READ-ONLY file) to a single connDiff(gmT,gmU)-type object; its H2 jet
is reachable through the connLowOp packaging: `connLow_pair_h2`
(PUBLIC, C2:4752) gives J2(connLowOp gT - connLowOp gU) <= (C*|T-U|)^2,
and the bridge connDiffSection <-> connLowOp lives in the
`connSec_eq_raise` (C1:892) / `connLower_unit` (Action:171, private —
re-derive if needed) family.  The armSlot jet transfer mirrors
`revSlot_bdd_h2`'s internals (C1:4501: bdd = pair vs base-state +
fr^2-factor; the pair's engine is `revSlot_pair_h2` nearby).  BDD:
zero-state trick as in revSlot_bdd_h2.  All pieces are in claimed or
read-only files; nothing blocks.

REVSLOT ENGINE DISSECTED (C1:4452): pair = `slotInsertEndoCc_sub`
(linearity) + `fullRev_sub` (endo diff = symmRaiseEndo(T-U)) +
`endo_slot_h2` (J2(slotInsert s=2 endo) <= fr^2 * J2(slotInsert 0 endo))
+ s=0 base identification.  For armConn: find/mirror the ARM-version
transfer (`armSlotEndoCc` vs `slotInsertEndoCc` are different
constructors — grep MetricArmCoeffJetTower's public surface for
`arm.*slot.*h2|armSlotEndoCc_sub|arm.*jet` and an endo-difference
linearity `armSlotEndoCc_sub`); the endo DIFFERENCE
bdConnPair(gmT)-bdConnPair(gmU) needs its own `fullRev_sub` analogue
(via connDiff_cocycle).  Everything else for `lieCov_pair_h1` is
assembled and green.  NEXT WINDOW: (1) grep the arm transfer; (2) write
armConn_pair/bdd; (3) H1 bdds (CurvF/QuadF/R4); (4) realizedFam ties;
(5) `lieCov_pair_h1`; then classes 4 -> 3 -> 1, master telescope,
lowC0_sub integral, a1Lo_diff hookup, exact refresh, notes, release
claims.

ARM JET TRANSFER — FINAL DEPTH (the ONE new pointwise lemma left for the
class-2 capstone): the endo_slot chain bottoms out at
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (pointwise fiber-norm
bound under iterated covariant gradients, single-endo slotInsert).  The
arm version `rfns_iteratedCovGrad_armSlotEndoCc_le_*` does not exist;
mirror the slotInsert one (locate + read its proof; likely in the
JetTower/NablaOnTensors layer) with the bilinear endo's extra slot paid
by a v0-basis expansion (one extra fr factor).  Wrappers after it are
mechanical (arm_slot_l2 -> arm_h1/h2, mirroring endo_slot_l2/h2 which
are fully dissected above).  `armSlot_sub_lip` is GREEN (15th this
session; proof pattern = rs-rank ext + fib-level hfib via
armSlotFib_apply_eval + slotInsertEndoFib_sub_left + dsimp-only for the
beta-redex; synthInstance+maxHeartbeats bumps needed).

ARM TRANSFER — COMPLETE IMPLEMENTATION SCRIPT (all proofs dissected):
(1) `armSlot_succ_eq` (new, ~60-80 lines, Lip-private): the arm analogue
    of `slotInsertEndoCc_succ_eq_reindex_slotExtend` (JetTower:2725,
    private — read its proof as template): armSlotEndoCc (s+1) Arm =
    rsDomDomCongr-reindex of slotExtend (armSlotEndoCc s Arm); prove at
    unitModel level via armSlotFib_apply_eval on both sides (the same
    ext+dsimp pattern that landed armSlot_sub_lip).
(2) `rfns_icg_armSlot_le` (new, ~50 lines): VERBATIM mirror of
    `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (JetTower:2795,
    PUBLIC — its induction consumes only the succ-equation +
    `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (public) +
    `rfns_iteratedCovGrad_slotExtend_le` (public)), with base case s=0.
(3) `arm_l2_lip` / `arm_h1_lip` / `arm_h2_lip` wrappers (~40 lines,
    mirror endo_slot_l2/endo_slot_h2 which are fully dissected).
(4) The s=0 base: armSlotEndoCc 0 (bdConnPair g gm) vs
    connDiffSection gm g — `bdConnDiffSection_eq_armSlotEndoCc_zero`
    (JetTower:4359, private, rfl-adjacent — restate in Lip).
(5) armConn moduli: pair via armSlot_sub_lip + connDiff_cocycle +
    transfer to s=0 + connSec H1/H2 machinery; bdd via zero-state trick.
Then `lieCov_pair_h1` per the FINAL ASSEMBLY MAP, classes 4/3/1, master
telescope, integral, a1Lo hookup, exact refresh.

ARM SUCC-EQUATION DERIVATION NOTE: the slotInsert succ template
(JetTower:2725-2792, full text dissected) proves the Cc equation by
ext-chain + `slotInsertEndoFib_apply_eval` + slotExtendFib_apply_eval +
explicit Fin.cases permutation bookkeeping (swap01 on both r and s
sides).  For the ARM version the constructor is NON-square
(g (s+1) (s+2)); derive the correct reindex/rsDom permutations at the
MODEL level from `armSlotFib_apply_eval` (arm s = sIEF (s+1) 0 at
(Arm v0) with vecTail) vs slotExtend-of-arm-s — write the candidate
equation first at unitModel on explicit vectors, read off the two
permutations, then run the ext-chain.  CAUTION: do this with a fresh
context and the :2725 template open side-by-side; the Fin.cases block
is unforgiving.  After it: the rfns mirror induction, the l2/h1/h2
wrappers, then armConn moduli and the capstone — all dissected above.

ARM SUCC-EQUATION — MODEL-LEVEL DERIVATION (s-side DONE):
`slotExtendFib_apply_eval` (OperatorFieldCovariantCalculus:293):
toModel(slotExtendFib A D)(cons v0 vs) = toModel(A (curry D v0)) vs —
the new slot SLICES D first.  Hence
slotExt(armFib s Arm) D' [w0,w1,w2,w3..] = D'[w0, Arm w1 w2, w3, ...]
vs armFib (s+1) Arm D' [v0,v1,v2,v3..] = D'[Arm v0 v1, v2, v3, ...].
Identification (v0,v1)=(w1,w2), v2=w0, rest equal: the INPUT-side
(Fin (s+3)) permutation is the 3-cycle sigma = (swap 0 1).trans
(swap 1 2)  [check: 0->1->2, 1->0->0, 2->2->1 — i.e. w = v after sigma]
— one order deeper than the template's swap01 because the arm eats TWO
slots.  The D'-slot (rsDom) permutation: ArmRes at 0 vs at 1 => swap01
(same as template).  REMAINING: derive the r-side (reindexCoeffGen rho,
Fin (s+2)) by the same model calc on the OPERATOR-as-tensor encoding
(check how reindexCoeffGen acts in the template's :2757 step), then run
the ext-chain with the :2725 template's Fin.cases style (expect one
extra case layer from the 3-cycle).

R-SIDE PINNED: `reindexCoeffFibGen_apply`
(Tensor/CovGrad/RicciDeTurckSectionDifference.lean:4036, PUBLIC):
reindexCoeffFibGen r s rho x A D = A (ofModel (domDomCongr rho
(toModel D))) — the r-side perm acts on the OPERATOR'S ARGUMENT D by
model domDomCongr.  So in the arm succ-equation the rho on Fin (s+2)
(the D'-side) is the swap01 moving the sliced/passthrough D'-slot past
the Arm-output slot (same role as the template's rsDom swap01), and the
sigma on Fin (s+3) (the v-side) is the derived 3-cycle
(swap 0 1).trans (swap 1 2).  ALL permutations for the arm
succ-equation are now determined; write the equation with these and run
the :2725-template ext-chain (expect one extra Fin.cases layer).
Estimated remaining to (N): class-2 capstone ~550 lines; classes 4/3/1
~800-1100; master telescope + integral ~250-400; a1Lo hookup ~100-200;
refreshes/notes/claims; then the endpoint wiring session.

ARM JET TRANSFER — COMPLETE (session count 20 greens): armSlot_sub_lip,
armSlot_succ_lip (perms: rho = swap01 on Fin (s+2), sigma =
(swap 0 1).trans (swap 1 2) on Fin (s+3); after the simp-normalization
chain [TensorMultilinear.tensor0S_curry_apply_eval — NOTE the namespace
qualifier, unknown-identifier was the root cause of 4 failed rw
attempts — , toModel_ofModel, domDomCongr_apply] the three Fin.cases
branches closed by rfl), rfns_arm_le_lip (mirror induction via
both_eq + slotExtend_le), arm_l2/h1/h2_lip wrappers.  NEXT: restate
the s=0 base `bdConnDiffSection_eq_armSlotEndoCc_zero` (JetTower:4359
private) in Lip, then armConn pair/bdd moduli, H1 bdds, ties, capstone.

RECOVERY COMPLETE (2026-07-30): full transcript replay succeeded.
File GREEN at ~7076 lines, zero sorry, ALL session declarations back
PLUS the vbmcd bridge (vb_rank0_smul_lip / vbMcd_unit_lip /
vbPK_slotExt_lip / vbmcd_rel_lip / vbmcd_perm_eq / vbmcd_h2_lip /
vbmcd_sub_h1_lip) now VERIFIED (it had never been checked pre-crash;
needed beta_reduce before the rsDom rw - the beta-redex lesson again).
armSlot_succ_lip's final tail reconstructed:
rw [armSlotFib_apply_eval] ; rw [slotInsertEndoFib_apply_eval x2] ;
simp only [TensorMultilinear.tensor0S_curry_apply_eval,
toModel_ofModel, domDomCongr_apply] ; congr 1 ; funext ; Fin.cases ;
rfl x3.  Replay machinery kept at scratchpad/replay/ (extractor,
driver, base snapshots lip_head.lean + lip_base75.lean).

*** CLASS-3 (lc0VB) COMPLETE ***: vb_pair_h1 GREEN FIRST TRY (447s) -
the Opus draft (opus_vb/vb_pair_h1_draft.lean SS1) compiled unmodified
on top of the bridge + trace1 + safe helpers.  FOUR OF FIVE classes
green (2 lieCov, 3 vb, 4 amix, 5 riem); class 1 (ricciGoodLow) being
built from opus_good draft (fullSlot bricks green in C1; dagLow
exports textually in Action pending its check).  File ~7775 lines.

*** CLASS-1 (ricciGoodLow) COMPLETE (2026-07-30) ***: `good_pair_h1`
GREEN, file 10353 lines, ZERO sorry.  ~2575 lines / 42 private
declarations inserted between `amix_pair_h1` and `selfLow_sub_parts`.
ALL FIVE C0 H1 classes are now green (1 ricciGoodLow, 2 lieCov,
3 vb, 4 amix, 5 riem); next brick is the five-way master telescope
over `selfLow_sub_parts`, then `lowC0_sub` path integration and the
`a1Lo_diff` hookup in Pair.

What class 1 needed and how it was built (dependency order):
* leaves: `jet_sub_lip` (X-Y folded as X+(-1).Y), `grad_l2_sq_lip`
  + `grad_h1_le_h2_lip` / `grad_h2_le_h3_lip` (Lip copies of Action's
  PRIVATE `grad_l2_sq` / `grad_h2_le_h3`, same 3-line
  `rfns_iteratedCovGrad_covGrad_comm_rs` proof).
* Layer A: `ccSymm_sub_lip`, `inputSymm_h1` (swap field frozen at J2,
  moving factor at J1 via `app_h12_mul_lip`).
* Layer B: `connSec_bdd_h2` (= `connSec_self_h2` + `wXi_self_tame`),
  then `connIns_bdd_h2` / `connIns_pair_h1` / `connInn_bdd_h2` /
  `connInn_pair_h1` -- ALL four are just `reindex_jet_lip` +
  `slot_h1_lip`/`slot_h2_lip` on top of `connSec_pair_h1`, because
  `connDiffContrInsertionField_eq_reindex_slotExtend_two` and
  `connDiffContrInsertionInnerField_eq_reindex_slotExtend` are PUBLIC.
  No new pointwise lemma; C1's private `insert_h2` was NOT needed.
* Layer C: `pureCoeff_eq_lip` (ricciArmPrincipalCoeffPure = pureTrace 2,
  a 4-line ext chain) + `fourtrace_jet_le` (the 22-fold bookkeeping of
  `ricciCometricFourTraceCastG0_eq_reindex_combination`) collapse the
  moving four-trace onto C2's `trace2_pair_h2` / `trace2_h2_bdd`.
* Layer D: `refold_sub_lip` / `refold_h1_lip` / `refold_h2_lip` from
  the PUBLIC `refoldKernelContractionMonomialField_eq_mvPairTraceRefold`
  (`slotExtendIter g 0 4 2 D = slotExtend 1 5 (slotExtend 0 4 D)` is rfl).
* Layer E: `dagLow_bdd_h2` consumes Action's newly-public `dagLow_h2_rf`
  ACROSS the private/public `dagLowOp` split (Action has BOTH a private
  copy at :347 and `LowBaseInternal.dagLowOp` at :3406 with identical
  bodies; `.trans` unifies them by delta -- this works, no bridge lemma
  needed).  `dagLow_pair_h1` = `connLow_pair_h2` + `grad_h1_le_h2_lip`
  + `app_h21_mul_lip 3 4 4`.
* Layer F (AA arm): local copies `aaP3201..aaP120` of EdgeRicciPairing's
  private `ricPerm*`, generic `aaBlk`/`aaInn`, and `aaKer_eq_lip` proved
  by `rfl` at maxHeartbeats 1600000 (the feared whnf blow-up did NOT
  materialise).  `aaPK` = the SUM of the eight permCoeff H2 jets, with
  `aaPK_ge4`/`aaPK_ge3` giving one uniform permutation constant --
  this avoids Action's eight-constant ladder entirely.  Generic
  `aaBlk_h2` / `aaBlk_pair_h1` are instantiated six times; the
  left-associated six-fold `jet_add_lip` cascade gives factor 94.
* Layer G (DA arm): `ricciDA_pair_h1` -- the only place where the second
  argument of `ricciGoodLow` moves, consumed exactly at
  `J1 (covGrad (P-Q)) <= J2 (P-Q) <= D2^2` (no D3).  Uses C1's public
  `LowBaseInternal.fullSlot_bdd_h2` / `fullSlot_pair_h1`.

ALLOCATION (verified against the C0 rules): connection differences only
at J1; only `fourtrace` and `connLowOp` are consumed at J2 on the
difference side, both in the spectral Hs (N) currency; no J3-of-
difference anywhere.  A-budget: the DA arm is the binding constraint at
total degree p^3 (p = 1+A+A^2), comfortably inside (1+A+A^2)^4.

LESSONS (new):
* `pi` (the Greek letter) is a RESERVED TOKEN in Lean 4 and cannot be a
  binder name: "unexpected token; expected '_' or identifier".  `rho`,
  `sigma`, `delta` are fine.  Renamed to `pm` throughout.
* `nlinarith`/`linarith` WITHOUT `only` inside these proofs is a
  heartbeat bomb: the context carries ~30 obtained constants, and the
  simplex (`Gauss.getTableauImp`) times out at 3.2M heartbeats even on
  a two-hypothesis goal.  EVERY scalar close in `ricciDA_pair_h1` was
  rewritten as `linarith only [...]` or as an explicit
  `mul_le_mul_of_nonneg_left` + `calc ... := by ring` chain.  This was
  the single failure in the whole class-1 build.
* `set x := e with h` makes `x` OPAQUE to `positivity`.  Any nonneg
  fact about an expression containing a `set` variable must be proved
  by hand (`mul_nonneg _ hpl20`), never by `positivity`.
* `aaPK`-style "sum of all the constants" is much cheaper than a
  per-permutation constant ladder when a generic block lemma is
  instantiated many times.
* Stale upstream olean: `dagLow_h2_rf` reported "unknown identifier"
  purely because Action.olean predated the concurrent publicization.
  One targeted `lake-locked build -NoLakeLock +...LowBaseAction` fixed
  it (9558 jobs, ~2 min); nothing referenced the old private names, so
  the refresh was safe.

VERIFICATION: focused check of DeTurckRemainderLowBaseLip.lean passed
(green, zero sorry).  Three checks were needed: stage 1 (leaves) green
except the stale-olean identifier; stage 2 (AA arm) green first try;
stage 3 (DA arm + capstone) needed only the linarith-scoping repair.

*** C0 H1 CHAIN MAIN BODY COMPLETE (2026-07-30) ***
ALL FIVE CLASSES GREEN (1 good [Opus-built, ~2575 lines, 42 privates,
all 10 draft gaps proved, no D3 anywhere], 2 lieCov, 3 vb, 4 amix,
5 riem) + selfLow_pair_h1 (five-way master telescope at fixed s,
B := 64Bg+16Bl+8Bv+4Ba+2Cr^2) + c0Diff_tame (path integral via
path_jetL2_le g 2 2 1): J1(lowC0Diff) <= B R * (1+A+A^2)^4 *
(D2^2+N^2).  File ~10690 lines, zero sorry, focused-check 271.5s.
Master-fix lessons: `set` folds existing hypotheses AND goals ->
redundant rw-at fails ('did not find pattern' = already folded);
set-var spellings must match goal-folded forms (Y1 via P/Q not s*T).
REMAINING for the uniform-uniqueness endpoint: a1Lo_diff = operator
bound ||(lowBaseDiff).a1Lo|| via a1_spec_lo (Pair) + forall-W core
bound [J1(a1Sub W) <= Q*J2(W): C0d flip-app app_h12 g 0 2 2 +
C1d app_h21 g 0 3 2 + grad-shift J1(covGrad W) <= J2(W)] with
Q from c0Diff_tame (D2,N) + c1Diff_tame (D3,N).

*** UNIFORM-UNIQUENESS ENDPOINT PROVED (2026-07-30) ***
`a1Sub_lo_tame` GREEN (275.1s):
  ||Hs1((lowBaseDiff g T U hdlt hdT hdU hdZ).a1 W)||
    <= C * sqrt(Bq R * (1+A+A^2)^4 * (D2^2+N^2)
              + (B0*D3 + B1*N + B1*A*N)^2) * ||Hs2 W||
on the common spectral H2 ball, sizes R (H2), A (H3, both states),
differences D2 (H2), D3 (H3, from the C1 leg only), N (spectral).
Chain: five classes -> selfLow_pair_h1 (master telescope) ->
c0Diff_tame (path integral) -> [+ c1Diff_tame, a1_spec_lo now public,
grad_shift_lip clone of norm_iCG_comp via rfns_iteratedCovGrad_comp]
-> a1Sub_lo_tame.  File ~10950 lines, ZERO sorry/admit/axiom/trace.
Endpoint-fix lessons: set-folding means hM0/hM1 arrive pre-folded -
never unfold the goal to meet them (drop rw [hXdef]-style); prefer
refine h.trans (term) over one-step calc inside have-blocks.
STATUS HONESTY: this completes the UNIQUENESS estimate of the C0
lane.  The (N) uniform-EXISTENCE theorem itself remains 0% (unstated;
its campaign = UNIF_EXISTENCE_PLAN No.36, handed to Codex); this
estimate is one required input to its contraction/uniqueness step.
