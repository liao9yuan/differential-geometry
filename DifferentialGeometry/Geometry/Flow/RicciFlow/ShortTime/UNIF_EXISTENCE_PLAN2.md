# UNIF_EXISTENCE_PLAN2 - continuation (entries No. 70+)

Continuation of `UNIF_EXISTENCE_PLAN.md` (which hit the 3000-line cap
at entry No. 69 + the class-3 marker).  THE OLD FILE REMAINS THE
AUTHORITATIVE HISTORY for No. 1-69; this file is the live planner
log from 2026-07-30 onward.  Endpoint: `ricci_flow_unif_existence`
(stated, one sorry, Evolution/ExtendViaUniqueness.lean:80).  Route:
R1tau (UNIF_N_PRO_RULING.md) + the lane structure of No. 51.
HANDOFF 2026-07-30: resume from entry No. 81 (end of file).

## Planner update No. 70 (2026-07-30) - H2Pair CLASS 3 DISCHARGED; plan file split

vb class proved sorry-free; H2 layer split at the abstraction
boundary into DeTurckRemainderLowBaseH2VB.lean (jet algebra +
interpolation chain + class 3, 1827 lines; builds ~3x faster) with
H2Pair.lean (1866) importing it - same namespace, no call-site
churn.  Devices reused: jetInterp3 instantiation at
a := sqrt(Cip*R*A4), D2 := D3 feeding, pairFold3 hoisted scalar.
RECIPE CORRECTION recorded: per-state rfns bounds cannot bound a
DIFFERENCE - the vbMcdArm section identity (private upstream) was
re-established locally (~120-line fibre chain); wXi single-state H2
recovered from public wXi_sub_tame at U := 0 (wXi g g g = 0).
Capstone selfLow_pair_h2 at 3/5 classes (~60%).  Remaining: class 2
(covX_bdd/pair_h2, ~450 lines, routine - DISPATCHED), class 1
(aaKer sharpening per the No. 58 ruling: the kernel's blocks are
app-products of connection-insertion fields each with sharp
(1+A)-H2 bounds via connSec/mcd producers; the existing envelope's
A^2 loss is pairing slack, not structure - then aaKer_pair_h2 +
dagLow_pair_h2).

## Planner update No. 71 (2026-07-30) - E3 recon result: curvature wall located; connection/Ricci layer BANKED

E3's two theorem targets (unifFc satisfying hcurv, Ksup satisfying
hsup) are 0% - NEITHER can currently be stated.  The wall is NOT in
the Lambda-class layer: the tree has NO order->=1 sibling of
PerturbedRiemannOpDifferenceBound.lean:88 (nothing bounds
nabla^{g1}Rm(g1) - nabla^{g2}Rm(g2), or nabla^{gBase,a} of a
curvature difference, by metric jets); nabla^a Rm is not even
STATEABLE in the iteratedCovGrad/SmoothCcTensor currency
(metricRm04 is a Tensor0SField; curv_apply_iterCov in
CurvTowerBridge.lean is private).  This is the prior session's
"2a-hi" sub-brick - confirmed unbuilt, a Geometry/Curvature/ brick
(differentiated Palatini at the fibre-norm level), not a leaf
assembly.  Also blocks Ksup's j=1 half (needs nabla Ric).

BANKED (green, axiom-clean): HCGCompactness/UnifCurvatureJetsLow.lean
- unifRicSup, unifRicBilin (first Lambda-class Ricci bounds in the
tree), unifConnDiffSup, unifCovConnDiffSup (Gamma(g0)-Gamma(gBase)
and its first gBase-cov derivative), all constants closed in
(Lambda, gBase) before any class member is named.

TWO DISPATCHES RULED: (a) the small trace lemma closing Ksup at j=0
- compute nabla^{g0}(deTurckVF g0 gBase) as the g0-trace of
nabla^{g0}(connDiff g0 gBase), differentiating the trace invariantly
from nabla^{g0} g0^{-1} = 0 (NOT via the pointwise orthonormal frame
of deTurckVF_eq_orthoFrame_trace, which is orthonormal only AT x);
then Cartan L_W g0(v,w) = g0(nabla_v W, w) + g0(v, nabla_w W) +
connDiff_outerCovDeriv_eq (DeTurckVFConnDiffVariation.lean:382) fed
by the two banked bounds closes deTurckRicciRHS at j=0 with
unifRicBilin.  (b) the 2a-hi brick itself, staged: first the
Tensor0SField -> SmoothCcTensor packaging for metricRm04 (publicize
or wrap curv_apply_iterCov), then the a=1 difference envelope via
the split nabla^{g0}Rm(g0) - nabla^{gBase}Rm(gBase) =
(A star Rm(g0)) + nabla^{gBase}(Rm-diff): the first term is
unifConnDiffSup x order-0; only the second term is new math (the
differentiated order-0 asset).

SIDE FINDINGS: (i) hsCovsumC/covsumHsC at n<=4 only reference Fc p
for p<=2, but consumers take unrestricted hcurv - a p-restricted E1
refactor (~14 theorems) could shrink the needed curvature orders;
moot until the wall falls; do not dispatch yet.  (ii) UNGATED route
off the Lambda<2 staging for the CONNECTION layer:
covDerivConnDiff_gJet_le ((3/2)Lambda^4(Lambda''+Lambda*Lambda'^2))
+ lcDiff_norm_le + covDConnDiff2_gJet_le, at the cost of carrying
reversed jets MetricCovDerivOrderBoundOn a gBase g0 - same extra
hypotheses sqrtRfns_cross_le already takes.  Curvature wall is
independent of this.

## Planner update No. 72 (2026-07-30) - horizon smallness DONE; lift-two application audit

ShortTime/LowRegLiftSmall.lean landed green + axiom-clean:
lowregLiftHorizon c M = min 1 (min ((1-c)/(2(c+1)))
((1-c)^2/(64(M+1)^2))), antitone in both args (class-uniform bound
=> class-uniform horizon), with the packaged smallness theorems
lift_smallness / lift_small_two_bd consumed VERBATIM at
lowreg_lift_two's hsmallHi/hsmallLo (probe-tested at the concrete
operator types).  Bridges norm_toLp_le_bd / norm_le_of_affine
convert pointwise operator bounds into the M*sqrt(T) shape.

TWO FRAMING CORRECTIONS (durable): (i) in the engine condition
C2(1+T) + 2 sqrt(1+T) ||A1||_{L2t} < 1 the first summand tends to
C2, NOT 0, as T->0 - so C2 < 1 is a RADIUS condition
(lowRegA2Total_data's ||A2|| <= C2*rho with rho small), never
buyable by the horizon; hc1 : c < 1 is a genuine standing
hypothesis.  (ii) a T-independent L2 bound on A1 would NOT vanish
as T->0 (concentration at 0); the honest producer is the pointwise
bound from lowRegA1_memLp, giving M = Phi(1+K) under a pointwise
H3 field bound K.

REMAINING to APPLY lowreg_lift_two (the two expensive witnesses,
untouched): (1) c-witness: lowRegA2Total_data's constant < 1 at a
chosen radius - per-metric this is a radius choice; class-uniform
needs the E7 packet.  DEFERRED while the c1_pair_lip agent holds
LowRegOperatorTime-adjacent files.  (2) M-witness: downstream of
lowRegA1_memLp's hcont/hlin - the affine bound Phi(1+||v||) is THE
outstanding low-base frontier (remainder_low_pair's degree-6
envelope contradicts a naive affine bound; the c1_pair_lip
discharge-check in flight is exactly this).  Composition with
lowregHorizon is a plain lt_min - no lemma needed.

## Planner update No. 73 (2026-07-30) - Kjet tower-match DONE; E4 closed for dim=3

HCGCompactness/UnifJetTowerMatch.lean (761 lines, no existing file
edited) landed green, axiom-clean, hAcc_of_jets confirmed OFF the
path (UnifCovSumN3 not imported).  The gap was currency mismatch,
not math: iterCov/covStep-on-Tensor0SField vs
iteratedCovGrad-on-SmoothCcTensor, previously identified only in a
rank-(0,2) metric-specific private.  Chain: ccUnitField (metric-free
unit value) -> iterCovGrad_unit_eq (rank-generic tower match, no
arity cast) -> rfns0_unit_eq (fibre bridge) -> rfns_iterCovGrad_eq
-> sqrtRfns_cross_le (pointwise cross-metric, j<=2, via iterCovG1_le
N=1 + unconditional iterCovG1_two) -> jetCross_l2 (L2, CS over the
3-order window + volumeMeasure_cross_le) -> kjet_of_class = E4's
hjet slot verbatim -> fibreMorrey_unif_class = BRICK E4 WITH NO
ABSTRACT INPUT REMAINING.  Closed constant kjetConst n L L' L'' s =
sqrt(3 sqrt(L^n)) * sqrt(L^{s+2}) * (1+D1+D2) (Dtower N=1,2);
morreyUnifConst fully closed.

SCOPE: hDim (finrank/2+2 = 3) exactly matches iterCovG1_two's
unconditional reach - fine, (N)'s E0 amendment pins hDim = 3 anyway.
Higher dim would need iterCovG1_three (= the open hAcc_of_jets).
LEAN LESSON (in the .md): anonymous-constructor Tensor0SField hits
a NormedSpace synthesis failure even with haveI; the canonical
MixedSection.toMultilinearSection map elaborates cleanly and keeps
the unit-value equation rfl.

E-lane state after No. 71-73: E4 DONE (dim=3), E6 j=0 in flight
(trace lemma), E6 j=1 + E2/E5-hcurv + unifFc all behind the 2a-hi
curvature wall (in flight).  DISPATCH: Lane C N2-lift residual (the
only remaining non-overlapping brick; H2VB/H2Pair held by class-2
agent, LowRegOperatorTime by c1_pair_lip agent, curvature files by
the two E agents).

## Planner update No. 74 (2026-07-30) - hHiPair is FALSE; honest A1 pair estimate banked

MATHEMATICAL RULING (counterexample, durable): lowA1_lip's hHiPair
- one constant C with ||a1Hi(T)-a1Hi(U)|| <= C||T-U||_{H3} for ALL
smooth states - CANNOT hold.  a1Hi is H3->H2, its coefficient is
read at the H2 jet, costing the THIRD jet of the state, which the
spectral H2 ball does not control.  Counterexample: T oscillatory
with ||T||_{H2} <= rho/2, ||T||_{H3} = A -> infty, U = T + eps V,
V a fixed low bump: coefficient telescope gives eps*A vs eps with
no cancellation, ratio to ||T-U||_{H3} ~ A unbounded.  The B1*A*D2
slot of c1Diff_tame is SHARP, not lossy.  lowA1_lip / lowA1_square
/ lowRegA1_square are vacuously conditional (WARNING docstrings
added, statements untouched).  hLoPair (a1Lo: H2->H1, coefficient
at H1 jet, costs only the second jet) is plausibly TRUE but not
derivable from current c0Diff_tame/c1Diff_tame moduli
((1+A+A^2)^4, B1*A*N losses).

BANKED: DeTurckRemainderLowBaseA1Pair.lean (+ .md) - c1_pair_lip
(the a1_diff input shape: lowJetSq 2 of C0-diff + C1-diff <=
(K R (1+A+A4)(D4+D3+D2+N))^2) and a1_pair_lip (operator-norm pair
bound for BOTH completions).  Pure packaging: c0Diff_h2_tame +
c1Diff_tame glued via lowC0_sub/lowC1_sub through a1_diff.  Placed
one module above H2Pair (C1Lip sits below Lip, cannot see
c1Diff_tame).  Focused+targeted green; #print axioms carries
sorryAx INHERITED from the H2Pair class-1/class-2 frontiers
(goodH2Pair :215, lieCovH2Pair :275) - discharging those (class 2
in flight) makes both new theorems axiom-clean with no change.

TWO RULED FOLLOW-UPS: (1) A4/D4-free sharpening - the one-state
bound lowData_a1_coeff needs only J3 (K0(1+J3S)^6), so the sharp
pair estimate should be ||a1Hi(T)-a1Hi(U)|| <= K_A ||T-U||_{H3} on
{J3 <= A^2}; the A4/D4 in c0Diff_h2_tame are telescope artefacts.
DEFERRED until the class-2 agent releases H2Pair/H2VB.  (2) a
dense-extension lemma for locally Lipschitz core maps: map on a
dense subspace, Lipschitz on every bounded set, into a complete
codomain, extends continuously (Cauchy filter -> Cauchy image ->
DenseInducing.continuous_extend); then lowA1's conclusion is
Continuous (never LipschitzWith - dense_lipschitz inapplicable) and
the forall-v square follows from radialA1_pair's core square by
DenseRange.induction_on.  DISPATCHED (self-contained Analysis
lemma, no file overlap).  M-witness note: the degree-6 one-state
envelope is HARMLESS for the M-witness on a bounded H3 ball (Phi
need only be monotone, not affine - restate hlin accordingly when
wiring).

## Planner update No. 76 (2026-07-30) - hfLo bridge SCOPED; buildable now with one named hypothesis

Recon complete; authoritative implementation plan =
ShortTime/LOWREG_HFLO_BRIDGE_PLAN.md (builder brief at its end).
DESIGN RULING: equalizer-along-the-field does NOT work - the a.e.-t
identity must come from closedness of {w | lowRegN w = lowBaseN w}
+ smoothCore_dense, so coefficient CONTINUITY is unavoidable.  But:
(i) Continuous (lowA2Lo) is ALREADY PROVED (second conjunct of
lowA2_small, LowRegOperatorTime.lean:668, via radialA2_lip) - the
A2 half is closed; (ii) the bridge needs NEITHER spectral symmetry
NOR radial inactivity - mirror lowBaseA summand-for-summand with
radialCLM kept inside the time family, making the family-vs-
lowBaseA identity definitional (lowRadial_eq_self_sol /
lowreg_sol_symm_h3 are downstream, not prerequisites); (iii)
lowreg_partial_sol already exports TOTAL Continuous Nfun on the
ball subtype; (iv) f0Lo = N 0 definitionally via
liftForceLo_lowBase + nZero_h1_eq, but ONLY at g_bg := g0 (hard
statement constraint).

MISSING: (1) Continuous (lowA1Lo) - the one real blocker; enters
as an EXPLICIT honestly-named hypothesis (allowed: precisely-ruled
frontier with a queued discharge = the D4-free a1Lo pair estimate,
No. 74 item 1 restricted to the a1Lo half, gated on class-2
releasing H2Pair/H2VB; the banked a1_pair_lip does NOT feed
cont_extend_pair because its D4 difference-side term is not
H3-controlled - state-side A4 is absorbable, difference-side D4 is
fatal).  (2) lowRadial_eq_self smooth side (one min_eq_left, next
to lowRadial_norm, DeTurckRemainderLowBaseTime.lean:492).  (3)
publicize a1Lo_core_any (DeTurckRemainderLowBasePair.lean:494).
(4) VERIFY deTurckArmContractionThreshold'' <= 1/3 (delta-range;
if false, producer-side change - report, do not patch silently).
(5) VERIFY lowRegPrincipalLo is contained in lowBaseData.C2 FIRST -
else the lowRegA2TotalLo-family form of hfLo DOUBLE-COUNTS the
principal arm and is FALSE; the plan's lowBaseA-derived family
avoids this if the check passes.  CAUTION: never route through
lowA1_lip (hHiPair false, all conclusions vacuous); use
extend_pair_apply on lowA1LoCore directly.  DISPATCHED.

## Planner update No. 75a (2026-07-30) - dense-extension lemma DONE (No. 74 item 2)

Analysis/DenseExtension.lean (226 lines, 8 declarations, green,
axiom-clean; generic normed spaces, core index type carries NO
structure).  Mathlib had no such statement (its LipschitzOnWith
extensions are special-codomain Kirszbraun forms, not density
arguments); built on Dense.extend +
IsDenseInducing.continuous_extend_of_cauchy.  Faces: subset
(cont_of_lipBalls / cont_extend_lip, codomain needs only
CompleteSpace + T0Space), dense-range (cont_extend_pair /
extend_pair_apply / exists_extend_pair, hypothesis hpair = per-ball
K with K : R absorbed via max K 0; eq_of_lipPair shows the estimate
forces descent to range j, no injectivity needed), norm transport
(norm_extend_le / exists_extend_le - MONOTONICITY OF Phi DROPPED,
continuity suffices via the closed-set {||F x|| <= Phi ||x||}).

CONSUMABILITY (probe-verified): lowA1Hi/lowA1Lo are literally
Dense.extend (ccToHsLin_dense) of the core maps and highCore g =
Set.range (ccToHsLin g 2 3), so the theorems apply with no glue.
KEY FINDING: lowA1_lip's proof runs on continuity alone everywhere
except the two LipschitzWith conjuncts - swapping the conclusion to
Continuous leaves lowA1_square / lowRegA1_square structurally
intact.  Consumer still owes: the ball-currency bridge (||j T|| <= R
vs lowJetSq-3 <= A^2) and the map_sub rewrite (same as
highCorePair).  SEQUENCING: the ball-local restatement is NOT yet
dispatchable - the Hi face needs the A4/D4-free sharpening (No. 74
item 1, H2Pair files held by the class-2 agent) because the current
a1_pair_lip carries J4 hypotheses the H3 ball cannot supply.
Follow-up noted, deferred: re-derive dense_cont_on_balls
(TameForcingFixedPoint.lean) from the new module.

## Planner update No. 75 (2026-07-30) - Lane C N-term at aHi=2 LANDED (frozen forcing)

New file ShortTime/LowRegLiftNTerm.lean (18 decls, sorry-free, 9891-job
targeted build, all axiom-clean).  AUDIT RESULT FIRST: lowreg_lift_two has
NO Nemytskii-shaped N-hypothesis.  Its only nonlinearity slots are
f0Hi / f0Lo / hf0 - the AFFINE CONSTANT term, i.e. exactly the frozen
split's N(0).  Everything state-dependent is already carried by A2/A1
(Lane B, landed).  So the ruled frozen split closes the N-side of the
rung outright.

Delivered: staticForce g0 g_bg sigma (= smoothCcToTensorHs of
deTurckRHSSection g_bg g0, the static field of nZero_eq_static) at
ARBITRARY real order, with staticForce_incl (inclusion naturality - the
whole reason the N-side is free: a fixed smooth field costs nothing to
raise) and staticForce_congr; baseForceH2_eq_static +
lowBaseForce_eq_static identify the two forcing objects the low-base
layer already carries as this same field at orders 2 and 1 (reuse, no
parallel hierarchy); nZero_staticForce / nZero_h1_eq pin it to N(0) also
at the literal order 1 the lift uses.  Endpoints liftForceHi /
liftForceLo / lift_force_incl are the f0Hi / f0Lo / hf0 slots VERBATIM -
FIT-TESTED by elaborating lowreg_lift_two at aLo:=1, aHi:=2 with them in
place, no transport, no restatement.  Sizes norm_liftForce{Hi,Lo}_le =
D*sqrt(T) with D any bound on the static field's H2 (resp H1) norm; no
A-constant enters.  Reusable time layer added: timeConstL2 +
compLpL_timeConstL2 + norm_timeConstL2_le (built ON norm_toLp_le_bd from
LowRegLiftSmall, not duplicated).

RULING CORRECTION (durable): the frozen split does NOT produce the
state-dependent N2 of lowreg_force_id at the state ball.  lowA2Hi is
H4 -> L H2, so A2Hi(v) v needs v in H4 while lowerState g0 1 R carries
only H3.  The split closes the N-term at the TIME-FIELD level, where
maximal regularity supplies the extra derivatives - i.e. through hfLo,
not through a pointwise N2.  Do not re-dispatch N2 as a frozen-split
brick.

REMAINING to APPLY lowreg_lift_two after this: (1) Lane-A first-order
affine bound (No. 74's c1_pair_lip chain / a1Hi_lin) for
hA1Hi/hA1Lo/hA1compat; (2) hfLo - bridging lowreg_partial_sol's
Nemytskii export (gforce =ae lowRegN o field) to the affine form
fLo = nonautL2Map ... + f0Lo.  That is the ball-level completion of
lowCore_split / lowBaseN_frozen (the coefficient maps lowA2Lo/lowA1Lo
are themselves Dense.extends), Lane B/A territory.  (3) an H2 sibling of
nZeroC for the class-uniform D (E3's Ksup at order <= 2).

## Planner update No. 78 (2026-07-30) - No. 77 reconciliation: the "unbridged towers" gap is MOSTLY CLOSED by No. 73; two dispatches

No. 77's separate-cheaper-gap claim ("iterCov/normSq0S vs
iteratedCovGrad/riemannianFiberNormSq unbridged anywhere in the
tree") is STALE: UnifJetTowerMatch.lean (No. 73) landed
CONCURRENTLY with that agent's run and contains the bridge in the
section->field direction - iterCovGrad_unit_eq (rank-generic tower
match) + rfns0_unit_eq + rfns_iterCovGrad_eq (norm-level).  The
genuinely remaining piece is only the FIELD->SECTION packaging:
produce a SmoothCcTensor whose unit field IS metricRm04 g (fixed
smooth geometric field -> section; precedent: the staticForce
packaging of deTurckRHSSection in LowRegLiftNTerm.lean), then
rfns_iterCovGrad_eq transports every iterCov-currency estimate to
the SmoothCcTensor shapes E3's consumers (hcurv
UnifBochnerGap.lean:304, hsup UnifNZeroBound.lean:343) speak.
DISPATCH (i): the curvature packaging brick.  DISPATCH (ii): the
No. 77 wall itself - the field-level Palatini difference identity
(metricRm04 g0 - metricRm04 gBase = lowering defect + gBase star
Palatini(A) as a bundled (0,4)/(1,3) FIELD identity, so covStep
applies directly), then term 2 of the a=1 envelope via the
existing analytic inputs (covDConnDiff2_gJet_le,
unifCovConnDiffSup, unifConnDiffSup, covStepDiff_norm_le).
Placement per No. 77's correction: HCGCompactness/ siblings, NOT
Geometry/Curvature/ (iterCov/diffStep/MetricCovDerivOrderBoundOn
all live in HCGCompactness/).  REUSE the No. 77 routing trick:
instantiate diffStep_jet_one_le at g1=gBase, g2=g0 so the jet
hypothesis is exactly the class hjet1 and the norm lands in g0
(sign absorbed by diffStep antisymmetry + normSq0S_neg).

## Planner update No. 77 (2026-07-30) - 2a-hi stages 1+2a LANDED; the wall is a tensorial Palatini identity
(renumbered from a duplicate No. 76 by the planner; No. 76 = the hfLo bridge entry above)

Two recon corrections to No. 71 first.  (i) `nabla^a Rm` WAS already
stateable: `iterCov g 4 (metricRm04 g) a` is exactly it, is public, and
is the currency the whole covStep/diffStep/telescoping machinery uses.
`curv_apply_iterCov` relates it to the HCG static tower `curvCovDeriv`;
BOTH are Tensor0SField-side, so publicizing it does NOT touch
iteratedCovGrad/SmoothCcTensor.  (ii) the brick cannot live in
`Geometry/Curvature/` - iterCov/diffStep/MetricCovDerivOrderBoundOn are
all HCGCompactness.

BANKED (green, axiom-clean, no warnings): `curvCovDeriv_normSq_eq`
(CurvTowerBridge.lean, public curvEquiv-free face of the private bridge;
`curvNormSq_eq` now calls it) and a new sibling of UnifCurvatureJetsLow,
`HCGCompactness/UnifCurvatureJet1Diff.lean`:
`curvJet1_diff_eq` (the exact split nabla^{g0}Rm(g0) - nabla^{gB}Rm(gB)
= diffStep g0 gB 4 Rm(g0) + covStep gB 4 (Rm(g0)-Rm(gB)));
`unifRm04Sup` (FIRST Lambda-class curvature bound on the (0,4) FIELD
rather than riemannOp: |Rm(g0)|_{g0} <= n^2 F, via g0-ON frame +
metricRm04StdAt_eq_inner_riemannOp + normSq0S_le_card_of_component_bound);
`unifCurvJet1Conn` (term 1 of the a=1 envelope CLOSED, constant
4*sqrt(n^5)*(3/2)*sqrt(Lambda^3)*Lambda*(n^2 F), closed in (Lambda,gBase));
`exists_curvJet_sup` (fixed-metric sup of nabla^a Rm at every order, a
one-liner off `sqrtNormSq0S_bddOn` - this DISSOLVES the No. 71 worry that
the uncontracted gBase-side sup needed new machinery).

ROUTING LESSON worth reusing: `diffStep_jet_one_le (g1 g2 ...)` measures
in g2 and consumes the jets of g2 against g1.  Taking g1=g0,g2=gBase
therefore demands the REVERSED jets (side-finding (ii) of No. 71).  Take
instead g1=gBase, g2=g0: the jet hypothesis becomes exactly the class
`hjet1`, the norm comes out in g0 (which is also what E3 wants), and NO
cross-metric Lambda^{s/2} conversion is needed anywhere.  The sign is
absorbed by diffStep g0 gB x = -(diffStep gB g0 x) + normSq0S_neg.

THE WALL, now precisely located: term 2, `covStep gB 4 (metricRm04 g0 -
metricRm04 gB)`.  Its analytic inputs ALL EXIST (covDConnDiff2_gJet_le
for nabla^2 A, unifCovConnDiffSup for nabla A, unifConnDiffSup for A,
covStepDiff_norm_le).  The single obstruction is that
`riemannSec_difference` - the order-0 Palatini - is an EVAL-level
identity on smoothExtensionTangent-extended fields, so differentiating it
drags nabla^{gB}(extension) corrections into every slot.  Needed: the
Palatini difference as a BUNDLED (0,4)/(1,3) field identity so covStep
applies directly.  Nearest existing objects are the Kotschwar lane's
`rmDiffLowAt` / `rmDiffLow_split` / `rm2Low_eq_sub`, which have no A-jet
expression.  Smallest next lemma: field-level
`metricRm04 g0 - metricRm04 gB = (lowering defect) + gB * Palatini(A)`.
This is a dedicated-session brick, NOT a leaf; do not re-attempt by
adding an `hpal` hypothesis to unifCurvJet1Conn.

SEPARATE still-open gap (independent of the wall, and cheaper): the E3
consumers speak SmoothCcTensor/iteratedCovGrad/riemannianFiberNormSq while
ALL of the above speaks Tensor0SField/iterCov/normSq0S, and the two towers
are unbridged (covGrad goes through covGradBundleEquiv, covStep through
nabla0SFun).  `Tensor0SField.toTensorRSField` supplies the object; missing
is `iteratedCovGrad g 0 s j (toRS0 A) = toRS0 (iterCov g s A j)` or its
norm-level equivalent.  That single bridge would unlock EVERY
iterCov-currency estimate for E3 at once - worth dispatching before the
Palatini brick.  Details: `HCGCompactness/UnifCurvatureJet1Diff.md`.

## Planner update No. 79 (2026-07-30) - No. 71 DISPATCH (a) DONE: Ksup CLOSED at j=0

Two new files, both green + axiom-clean under a real `lake build`
(9706 jobs), no existing file edited.

`Geometry/Flow/DeTurckVFCovDeriv.lean` - the missing trace lemma.
`deTurckVF_covDeriv_eq`: nabla^{g0}_v W = sum_i [ (nabla^{gBase}_v A)(B_i,B_i)
+ A(A(B_i,B_i),v) - A(B_i,A(B_i,v)) - A(A(B_i,v),B_i) ], A = connDiff g0
gBase, W = deTurckVF g0 gBase, B_i = smoothOrthoFrame g0 x i, first
summand = covDerivConnDiff gBase g0 (ext v) B_i B_i x.  Supporting layer:
`orthoFrame_expand` (vector Parseval), `frameDiag_indep` (diagonal trace
of a VECTOR-valued bilinear map is frame-independent),
`deTurckVF_frame_trace` (the trace formula against ANY g_x-ON family),
`frameCorr_vanish` (the moving-frame correction, skew one-form x
symmetric A).

RECON CORRECTION (durable, No. 71 was wrong here): "the orthonormal
frame of deTurckVF_eq_orthoFrame_trace is orthonormal only AT x and so
cannot be differentiated" is FALSE.  `smoothOrthoFrame g x i` is a
SMOOTH SECTION and `smoothOrthoFrame_orthonormal` gives g_y-orthonormality
for EVERY y in `smoothOrthoFrameNbhd x`.  So the honest route is the
frozen-frame one: rewrite W by the x-centred frame sum on that
neighbourhood (needs `deTurckVF_frame_trace`, the frame-independence
generalisation, since `deTurckVF_eq_orthoFrame_trace` at y uses the
y-centred frame), transfer by `IsCovariantDerivativeOn.congr_of_eventuallyEq`,
differentiate term by term with `connDiff_outerCovDeriv_eq`, and kill the
correction with `smoothOrthoFrame_cov_skew` x `connDiff_symm`.  That
pairing was already announced in `connDiff_symm`'s docstring; it had
simply never been built.  No new "invariant trace differentiation"
machinery was needed and `cometric_skew_core` was not required.

`HCGCompactness/UnifDeTurckRHSZero.lean` - the class assembly.
`covDerivConnDiff_tens` (covDerivConnDiff is TENSORIAL - proved off the
public `connDiffSection_covGrad_eq_covDerivConnDiff` by pairing with a
one-form and separating with the g-flat of the difference).  This bridge
is unavoidable: the trace identity necessarily carries FRAME SECTIONS in
slots 2/3 while every Lambda-class bound is stated on
smoothExtensionTangent.  Then `unifCovDerivVF`
(|g0(nabla_v W, w)| <= n(C1+3C0^2)Lambda^4 sqrt sqrt),
`unifRHSBilin` (|deTurckRicciRHS gBase g0 (v,w)| <= (2K_Ric+2K) sqrt sqrt,
via `deTurckRicciRHS_apply` + `cartan_formula_for_lie_deriv_metric` +
`unifRicBilin`), `unifRHSFib`, and `unifKsupZero` = the hsup slot of
`UnifNZeroBound.staticN_h1_le` AT j=0 VERBATIM.  All constants closed in
(Lambda, gBase) before any class member is named.

STATE: `nZeroC`'s Ksup input is now half-discharged.  The j=1 half is
UNCHANGED and still behind the 2a-hi curvature wall (No. 77/78): it needs
nabla Ric(g0), i.e. term 2 of the a=1 envelope = the field-level Palatini
difference identity.  Nothing in these two files touches or unblocks that
wall.  E-lane after No. 79: E4 done (dim=3), E6 j=0 DONE, E6 j=1 +
E2/E5-hcurv + unifFc still behind the wall.

## Planner update No. 80 (2026-07-30) - H2 CLASS 2 DISCHARGED; H2Pair down to ONE sorry

`lieCovH2Pair` proved sorry-free and axiom-clean ([propext,
Classical.choice, Quot.sound]) in a THIRD sibling,
`DeTurckRemainderLowBaseH2Cov.lean` (1856 lines): developing class 2
inside H2VB pushed that file to 3252 lines, over the 3000 cap, so the
covariant-arm class was split off at the abstraction boundary.  Chain
is now Lip -> H2VB -> H2Cov -> H2Pair; the theorem keeps its name in
the same namespace, so the master telescope's call site was untouched
- only the `sorry` stub was deleted from H2Pair.  **H2Pair now carries
exactly ONE sorry: class 1 (`goodH2Pair`, the aaKer sharpening).**

Modulus achieved is the file's arm class verbatim,
`(B0 R (1+A)(D4+D3+D2+N) + B1 R * A4 * (D3+N))^2`, with
`B0 R = sqrt(8 Bh R)`, `B1 R = sqrt(8 Bh R) Cip R`,
`Bh R = 2(Ca Cp^2 Dx R + Ca Bp^2 Cx R)`.

Route: `lieCov_residual` (Palatini, public) collapses the ENTIRE edge
to a single product `(-1) . app262(lieCovPair gm, X)` with
`X = rsPerm(lieCovSigma)(Ext^2(lieCovR4 T))`.  So the telescope has
only two levels: the `lieCovPair` factor is already public at H2 and
A-FREE (`pairTrace_bdd_h2`) with a purely spectral difference
(`pairTrace_pair_h2`), and all the new content is the X slot -
`covXBddH2` / `covXPairH2`, built from `r4BddH2` / `r4PairH2` through
`rspermH2` + two `slotH2`.  The class-4/5 devices transferred verbatim:
jetInterp3 at `a := sqrt(Cip*R*A4)` (applied to T and U DIRECTLY, not
to `P = s.T` - the X producers take the original state and build P
internally), `D2 := D3` feeding, `pairFold3`, `amixScalar`, difference
budget `u = D3^2 + N^2`.

THREE RECIPE CORRECTIONS worth banking:
(a) The CurvF pair case is FREE.  `lrCurvF g T = app(lrRiemW1 g,T) +
    app(lrRiemW2 g,T)` with both kernels frozen g-objects, so it is
    LINEAR in T: `curvSub` (lrCurvF T - lrCurvF U = lrCurvF (T-U))
    plus a single `curvBddH2` covers both the bounded and the
    difference side.  No `curvF_pair_h2` was needed.
(b) The arm slot tower does NOT need the H1 lane's `rfns_arm_le_lip` /
    `arm_l2_lip` pointwise induction.  Cloning only `armSlot_succ_lip`
    (as `armSuccEq`) and composing it with H2VB's already-public
    `reindexJet` + `rspermH2` + `slotH2` gives `armSuccH2` in four
    lines and `arm2H2` in two steps - ~100 lines of clone saved.
(c) `lipOmega` is `private` to Lip, so the `lrOmegaHat = lipOmega`
    bridge cannot be STATED here at all (the error is at the name, not
    the proof).  It does not need to be: consume the public
    `lieOmega_bdd_h2` / `lieOmega_pair_h2` by `exact` at the
    `lrOmegaHat` type and let definitional unfolding discharge it.
    `hatBddH2` / `hatPairH2` are exactly those two restatements.
Also: `connSec_sub_tame` (C1Lip, public) IS the H2 arm difference -
the H1 route through `connSec_pair_h1`/`armD_pair_h1` has no H2
analogue and is not wanted.  NO Lip publicization was needed, third
class in a row; the "minimal publicization list" in H2Pair.md has now
been unnecessary for classes 2, 3 and 4.

LEAN LESSON: a theorem whose STATEMENT mentions neither I nor M (pure
scalar facts - here `envSq`, `envQuart`, `envOne`) drops the section
variables entirely, so call sites must not pass `(I := I) (M := M)`;
the error reads `Invalid argument name 'I' for function ...`.

NEXT on this lane: class 1 (`goodH2Pair`).  Its blocker is unchanged
and is NOT the missing pair lemmas - it is that `aaKer_bdd_h2`
(Lip:8451) gives `J2(ricciAAKer) <= B R (1+A+A^2)^4`, i.e. an
H2-NORM ~ A^4 where `ricciAAKer ~ Gamma*Gamma` is truly ~A^2.
Re-pairing the lossy bound with jetInterp3 yields the FORBIDDEN A4^2.
The rebuild is mechanical (six blocks, `appRS_h2_h2_h2` against the
two sharp connection factors) but must be done BEFORE `aaKer_pair_h2`
/ `dagLow_pair_h2`.

## Planner update No. 81 (2026-07-30) - No. 78 dispatch (i) LANDED: the curvature packaging brick

HCGCompactness/UnifCurvaturePack.lean (new sibling, no existing file
edited) is green under a real `lake build` and axiom-clean on all
nine declarations.  It closes the FIELD->SECTION direction that
No. 78 identified as the only remaining piece of the tower bridge.

CONTENT, in two layers.  (1) Rank-generic, curvature-free:
`ccOfField g s A : SmoothCcTensor g 0 s` packages any smooth
`(0,s)` field as a section via `MixedSection.fromMultilinearSection`
(exactly the `deTurckRHSSection` precedent lifted off `(0,2)`), with
`ccOfField_unit : ccUnitField g s (ccOfField g s A) = A` and the
TRANSPORT EQUATION `rfns_ccOfField_eq`:
`riemannianFiberNormSq g 0 (s+j) x ((iteratedCovGrad g 0 s j
(ccOfField g s A)).toSection x) = normSq0S g x (s+j) (iterCov g s A
j x)`, every order.  NO support hypothesis is needed: compact
support is `HasCompactSupport.of_compactSpace` off the ambient
`[CompactSpace M]` the HCG layer already carries.  (2) The curvature
instance: `rmSection g = ccOfField g 4 (metricRm04 g)`,
`rmSection_unit`, `rfns_rmSection_eq`.

TRANSPORTED BOUNDS (deliverable 2): `exists_rmJetSup g a` (fixed
metric, order a) and `exists_rmJetSups g a` (ONE constant for the
whole window j <= a, running max) off `exists_curvJet_sup`; and
`unifRmSecSup gBase g0 hLam hLam2 hcomp hjet1 hjet2` - the
Lambda-class ORDER-0 bound `riemannianFiberNormSq g0 0 4 x
((rmSection g0).toSection x) <= C^2` with C closed in (Lambda,
gBase) - off `unifRm04Sup`.  Both are stated in the squared-norm
shape the consumers use.

CONSUMER SLOTS, honestly: every `hsup`-shaped slot (a fibre sup on
`iteratedCovGrad ... .toSection x`) is now directly fillable FOR THE
CURVATURE SECTION at all orders fixed-metric and at order 0
class-uniformly.  `UnifNZeroBound.staticN_h1_le`'s own `hsup` is
about `deTurckRHSSection` (rank 2), NOT `rmSection` - that is why
`ccOfField`/`rfns_ccOfField_eq` were stated rank-generically: the
same one-rewrite transport will serve there the moment a
`deTurckRHSField` iterCov bound exists (No. 79's j=0 Ksup is exactly
such an input).  `hcurv` (UnifBochnerGap:304) is NOT filled and NO
`unifFc` was defined: `hcurv` bounds `||nabla^p (pointwiseTensorCurv
g0 r S)||_{L2}` for an ARBITRARY section S, which needs (a) a
Leibniz/Kato product estimate for the curvature ACTION
`pointwiseTensorCurv` - a separate missing lemma, not merely a
curvature sup - and (b) a class-uniform ALL-ORDER sup of nabla^a Rm,
still open for every a >= 1 behind No. 78 dispatch (ii) (the
Palatini difference brick).  Naming a `unifFc` here would have
promised content that does not exist.

PLACEMENT NOTE for the next agent to touch UnifJetTowerMatch.lean:
`ccOfField`/`ccOfField_unit`/`rfns_ccOfField_eq` are curvature-free
and belong next to `ccUnitField` there; they live in
UnifCurvaturePack only because that file was held during this run.
Move them and keep UnifCurvaturePack as the curvature instance.
Details and two Lean lessons (the `4 + 0` vs `4` rewrite trap; `set`
zeta-expanding a `have` goal) in `UnifCurvaturePack.md`.

## Planner update No. 82 (2026-07-30) - H2 FIVE-CLASS CAPSTONE CLOSED; resume order

`DeTurckRemainderLowBaseH2Pair.lean` is now five classes out of five.
The last class, `goodH2Pair`, was discharged by rebuilding the sharp
six-block `ricciAAKer` H2 estimate, proving the inverse-slot H2
factorization and the AA/DA pair estimates, applying the spectral
`jetInterp3` bridge before re-pairing, and finally passing through the
input symmetrizer.  The high arm is `A4 * D3`; no `A4^2` term is
introduced.  The real focused check is GREEN with no placeholders.
Consequently `selfLow_pair_h2` and `c0Diff_h2_tame` are unconditional.

Honest accounting: `ricci_flow_unif_existence` itself remains 0% (its
endpoint declaration still has one placeholder); dedicated machinery
is approximately 76%.  Whole-project HCG compactness remains in the
low single digits.

Resume in this order:

1. Prove the D4-free `a1Lo` pair estimate.  This one brick should
   discharge the `hfLo` bridge, the `lowA1` restatement, and the
   M-witness consumer.
2. Finish the Palatini field identity, then the `a = 1` envelope,
   class-uniform `Ksup` at `j = 1`, and E6.
3. Assemble the E7 class-consistency packet, then the c-witness and
   E8b `tau0`.
4. Close Lane F by correcting E0 (`a <= 6`, dimension three) and
   coordinating the endpoint edit; the geometric terminal route is
   already placeholder-free.

## Planner update No. 83 (2026-07-30) - D4-free low affine packet CLOSED

The first item of No. 82 is now complete.  The fourth-jet-free
`a1Lo_pair_lip` was transported through the radial cutoff and dense
completion.  `ShortTime/LowRegA1LoPair.lean` exports the unconditional
`LowA1CorePair` producer and `lowA1Lo_ball`, a genuine uniform operator bound
on each fixed ambient H3 ball.  It does not assert the false global affine
envelope.

`ShortTime/LowRegLiftHfLo.lean` now contains the exact low affine split and all
three time-family witnesses consumed on the low side:

1. `lowAffA2_data`: strong measurability plus an `NNReal` pointwise A2 bound;
2. `lowAffA1_data`: strong measurability, `MemLp`, and the pointwise M-bound
   along an a.e. bounded H3 Duhamel trajectory;
3. `lowreg_hfLo_data`: the two packets plus the exact `hfLo` fixed-point
   equality on one radius.

The A2 family contains the radialized total low-base second-order coefficient,
and the A1 family contains the radialized first-order coefficient.  The
self-application identity was checked before estimating, so the principal arm
is not counted twice.  Both new ShortTime modules passed focused and exact
verification and are placeholder-free.

Honest accounting: `ricci_flow_unif_existence` remains 0% because its endpoint
declaration still has one placeholder.  Dedicated machinery is approximately
78%.  Whole-project HCG compactness remains in the low single digits.

Resume at item 2 of No. 82: audit and finish the field-level Palatini
difference identity, then feed it to the `a = 1` envelope, class-uniform
`Ksup` at `j = 1`, and E6.  Do not reopen the completed D4-free pair or hfLo
routes.

## Planner update No. 84 (2026-07-30) - KSUP j=1 GEOMETRIC PRODUCER CLOSED

The intrinsic class-uniform first covariant jet of the static
Ricci--DeTurck field is now proved.  The completed chain is:

1. the differentiated Palatini and curvature-one-jet packets;
2. reverse metric jets through order three and the connection-difference
   two-jet estimate;
3. a fixed rank-three-to-rank-one trace tower for the differentiated
   DeTurck covector;
4. the exact section-level split into the differentiated Ricci arm and the two
   Cartan/Lie arms.

`HCGCompactness/UnifDeTurckRHSOne.lean` exports `unifKsupOne` and
`unifKsupLow`.  The latter is exactly the `j <= 1` `hsup` shape consumed by
`ShortTime/UnifNZeroBound.lean`.  Focused and exact verification are GREEN,
and the module is placeholder-free.

This closes the geometric `hsup` producer, not the whole E6 assembly.
`staticN_h1_le`, `nZero_unif`, and `nZero_lowregNfun` still take the independent
`Fc/hFc/hcurv` packet explicitly, and there is no existing higher-level class
assembly call site.  Do not import the class-specific producer into the
parameterized consumer.  The smallest remaining E6 frontier is the
class-uniform `Fc/hcurv` producer; after it exists, assemble both packets in a
new high-level sibling and feed `nZero_lowregNfun`.

Honest accounting: `ricci_flow_unif_existence` remains 0% because its endpoint
proof still has a placeholder.  Dedicated machinery is approximately 80%.
Whole-project HCG compactness remains in the low single digits.

## Planner update No. 85 (2026-07-31) - E6 H1 CURVATURE ARTIFACT REMOVED; TRUE UNIFORM WALL EXPOSED

`ShortTime/UnifNZeroBound.lean` now derives the spectral `H¹` norm from the
curvature-free order-one identity `hsOne_sq`, specialized directly from
`rawIter_tsum` and `covIter_tsum`.  Consequently `staticN_h1_le`,
`nZero_unif`, and `nZero_lowregNfun` no longer take the artificial
`Fc/hFc/hcurv` packet.  Focused and exact verification are GREEN, and direct
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.  This
supersedes the remaining-boundary diagnosis in No. 84.

The E6 consumer is therefore curvature-free, but the class-uniform producer is
not yet in the quantifier shape required by a common horizon:
`unifKsupLow` currently gives only `∀ g₀, ∃ K` and assumes `Λ < 2`.  The final
route needs one `Kstar` chosen before `g₀`, uniformly for arbitrary `Λ ≥ 1`.
The route-closing theorem is `unifKsupLeOne`.  Reordering the witness under
`Λ < 2` is only a staged API refactor; removing that restriction requires a
finite-order nonperturbative assembly from the existing connection-difference
`A₀/A₁/A₂` estimates.  Do not present the staged sub-two result as the uniform
theorem.

A second, independent frontier remains on the high side:
`hfHi_eq_nemytskii` must identify the high fixed-point forcing almost
everywhere with the concrete Ricci--DeTurck Nemytskii term.  The affine high
equation alone cannot provide this identification for arbitrary supplied
`A2/A1/f0` data.  The fixed DeTurck background must remain `gBase`; any
low-affine producer hard-coded to `g_bg := g₀` must be parameterized before it
can feed the endpoint.

Honest accounting: `ricci_flow_unif_existence` itself remains 0% because its
endpoint proof still has a placeholder.  Recalibrated dedicated machinery is
approximately 65% complete; the previous 80% estimate omitted the uniform
quantifier reversal, removal of the `Λ < 2` restriction, and the independent
high Nemytskii realization frontier.  Whole-project HCG compactness remains in
the low single digits.

## Planner update No. 86 (2026-07-31) - KSUP j≤1 UNIFORM QUANTIFIERS CLOSED

The route-closing geometric theorem `unifKsupLeOne` is now proved in
`HCGCompactness/UnifDeTurckRHSOne.lean`.  For arbitrary `Λ ≥ 1`, it chooses one
nonnegative `Kstar` from the fixed background before `g₀`, and controls the
static Ricci--DeTurck fibre jets for every `j ≤ 1` throughout the metric class.

The dependency chain was made explicit rather than hidden behind
metric-dependent existential witnesses:

1. `UnifCurvatureJetsLow.lean` exposes fixed low-order connection and Ricci
   coefficients with supplied background caps;
2. `UnifDeTurckRHSZero.lean` exposes `ksupZeroC` and `unifKsupZero_of`;
3. `UnifDeTurckRHSOne.lean` exposes `ksupOneC`, `unifKsupOne_of`, and combines
   the two slots under one sum coefficient.

Focused and exact verification are GREEN.  Direct axiom audit of
`unifKsupLeOne` contains only `propext`, `Classical.choice`, and `Quot.sound`.
The upstream `.olean` files were refreshed only after their focused checks;
the already-open downstream LSP worker was then deliberately recycled before
continuing, preventing an old-import false diagnostic.

This closes the uniform `Ksup` producer, not E6 or the endpoint theorem.  The
next independent frontier is the high-side identity `hfHi_eq_nemytskii`, with
the fixed DeTurck background kept equal to `gBase`; after that producer is
available, assemble the class-level zero-forcing packet without importing a
class-specific theorem back into the parameterized consumer.

Honest accounting: `ricci_flow_unif_existence` remains 0% because its endpoint
proof still contains a placeholder.  Dedicated machinery is approximately
68% complete; the whole HCG compactness project remains in the low single
digits.

## Planner update No. 87 (2026-07-31) - HIGH FORCING SMOOTH IDENTITY CLOSED

`ShortTime/LowRegForceHi.lean` now proves `force_hi_smooth`: whenever the
lifted solution field is represented by a smooth family `F`, the high `H²`
forcing is almost everywhere the genuine order-two smooth Ricci--DeTurck
nonlinearity of `symmS (F t)`.  The fixed DeTurck background remains the
independent parameter `g_bg`, so the endpoint may specialize it to `gBase`.

The proof is purely the correct spectral-scale injectivity argument.  It
combines the existing high-to-low forcing identity, `lowReg_force_smooth`, and
`deTurckSmoothN_incl`, then applies `tensorHsInclusion_injective`.  It does not
postulate the mathematically over-strong global `H³ → H²` Nemytskii map whose
second-order passenger would require `H⁴` regularity.

Persistent-LSP diagnostics, focused verification, and the targeted module
refresh are GREEN.  Direct axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`; the module is placeholder-free.

This closes `hfHi_eq_nemytskii` only after a smooth representative `F` with
the stated pinning and ball bounds is available.  The smallest remaining
high-side frontier is therefore the representative producer from the actual
low-regularity solution packet, followed by the class-level E6 assembly.

Honest accounting: `ricci_flow_unif_existence` remains 0% because its endpoint
proof still contains a placeholder.  Dedicated machinery is approximately
70% complete; the whole HCG compactness project remains in the low single
digits.

## Planner update No. 88 (2026-07-31) - ARBITRARY-BACKGROUND LOW AFFINE CLOSED

`ShortTime/LowRegBgAffine.lean` now assembles the completed low forcing with an
independent fixed DeTurck background `gB`.  It exports the zero forcing
`lowBaseForceBg`, the completed affine forcing `lowBaseNBg`, continuity, and
the exact dense-extension identity `lowreg_N_bg_affine`.  The proof uses
`lowCoreBg_split`, `lowA2LoBg`, and `lowA1LoBg` on the smooth core and then
passes to the completed H2 target by density.  Focused and targeted
verification are GREEN, and the module is placeholder-free.

This corrects the remaining-frontier sentence in No. 87.  A general completed
H3 state does not admit an exact smooth representative, so `force_hi_smooth`
cannot be closed by producing such a representative from the actual packet.
It remains a valid conditional smooth-core theorem, not the endpoint producer.

The next genuine high-side frontier is a D4-free H2 pair estimate for the
C0/high-A1 coefficient, local on H3 balls.  Use it to construct the continuous
H3-to-H2 high A1 extension and its time-integrable forcing packet.  The low A1
pair and arbitrary-background low affine identity are closed and must not be
reopened.

Honest accounting: `ricci_flow_unif_existence` itself remains 0% because its
endpoint proof still contains a placeholder.  Dedicated machinery is
approximately 72% complete; the whole HCG compactness project remains in the
low single digits.

## Planner update No. 89 (2026-08-01) - HONEST HIGH A1 TIME PACKET CLOSED

The false global-Lipschitz high-A1 route is now fully superseded.  The
dimension-three smooth-core estimate was completed in
`DeTurckRemainderLowBaseH2Pair.lean`; `ShortTime/LowRegBgA1Pair.lean` transfers
it to the same-background high action, and `ShortTime/LowRegBgTime.lean`
constructs the ball-local completed high and low maps with their adjacent-scale
commuting square.  `ShortTime/LowRegBgA1Time.lean` then freezes the canonical
radial passenger along a measurable bounded H3 trajectory and supplies the
high `H3 → H2` and low `H2 → H1` measurable, time-L2, uniformly bounded
families.  Focused and targeted verification of each completed module are
GREEN and the route is placeholder-free.

No smooth representative of a general completed state is chosen, and no
global affine estimate is asserted.  The time bounds are correctly local on
the H3 state ball.  The old `liftA1Two_data` input `hlin` and the old
`lowRegA2Total = principal + extra` family are not endpoint routes: the new
`LowBaseActionData.C2` is already the complete small second-order deviation
after subtraction of the fixed rough Laplacian, so adding the separate
principal arm would double count it.

The active brick is `ShortTime/LowRegBgA2Time.lean`.  At `g_bg = g`, it must
transfer the smooth-core `c2_h2_small` estimate through the completed
`lowA2HiBg`/`lowA2LoBg` maps, freeze the same H2 radial scalar on the H4 and H3
passengers, and return measurable uniformly small compatible A2 families.
After that packet is GREEN, combine it with the completed A1 packet and the
existing low affine identity at `lowreg_realize_two`; do not revive the old
all-order or separate-principal wrappers.

Honest accounting: `ricci_flow_unif_existence` remains unstated/proved at this
lane endpoint (0%; its single placeholder remains in
`Evolution/ExtendViaUniqueness.lean`).  Its dedicated low-regularity machinery
is approximately 76% complete; the whole HCG compactness project remains in
the low single digits.

## Planner update No. 90 (2026-08-01) - ACTUAL L2-H3 C1 TIME ARM CLOSED

No. 89 records a valid bounded-trajectory packet, but it is not the packet
supplied by the actual low-regularity solution: that state is in time `L2 H3`,
not `L∞ H3`.  The complete-A1 bound in `LowRegBgA1Time.lean` therefore remains
a conditional consumer and must not be used to close the endpoint.

`ShortTime/LowRegBgC1Time.lean` now isolates the path-integrated `C1` arm, whose
fixed-H2-ball coefficient estimate is genuinely affine in the independent H3
size.  It constructs continuous completed maps on both adjacent scales,
identifies them with one smooth-core action, proves their commuting square,
and radializes the common passenger along every actual `L2_t H3` state.  The
public `c1_bg_time` packet returns time-L2 operator certificates with affine
Minkowski bound `L * ||u|| + sqrt T * Z`.  It introduces no H3/H4 smallness and
no essentially bounded H3 trajectory.

The complete A2 time packet in `LowRegBgA2Time.lean` is already GREEN, so it is
not the active brick stated in No. 89.  The remaining first-order endpoint wall
is C0: path-integrate the same-background C0 pair together with the completed
arbitrary-background `lie0_bg_pair_h1` correction, then construct its
radius-free time-integrable completed action.  Do not return to the obsolete
global-affine full-A1 or separate-principal A2 routes.

Focused verification, the named module refresh, and direct axiom inspection
of `c1_bg_aff` and `c1_bg_time` are GREEN; the source is placeholder-free.

Honest accounting: `ricci_flow_unif_existence` itself remains 0% because the
endpoint proof is still absent.  Its dedicated low-regularity machinery is
approximately 83% complete after the C1 time packet; the whole HCG compactness
project remains in the low single digits.

## Planner update No. 91 (2026-08-02) - C0CORE SPLIT CHAIN GREEN; C0PAIR CAPSTONE RESTORED

Compile-stabilization pass, no new mathematics.  All fourteen chunks of the
C0Core split (`Alg → Joint → Zero → One → {PairBase→PairCurv→PairDA→PairRic |
PairEst | Amix} → CoeffPair → Integrate → Assemble → Core`) are focused +
exact GREEN with current `.olean`s; the public `LowRegBgC0Core` endpoint
(`c0CoreData`, `c0Core_self`, `c0CorePair`, `c0Coeff_aff`, `refold_low_split`)
is preserved and the monolith OOM is resolved.  `LowRegBgC0Time` is GREEN
after narrow import repair (`DenseExtension`, `NonautonomousL2Cross`); the
split had dropped the monolith's `LowRegBgC1Time` import, and the closure gap
was refilled narrowly at each consumer (`Assemble` ← `LowRegBaseForce`,
`Core` ← `DeTurckRemainderLowBaseTime`) rather than re-importing C1Time.

Separately, the `LowRegBgC0Pair` overwrite accident is now FULLY healed: the
earlier 33-patch replay had restored only the intermediate `dlaBg_pair_h1`
snapshot; the remaining 43 patches from the true authoring session
(`rollout-2026-07-29T06-05-04`) were replayed with context-validated diffs,
restoring `dlbIns_pair_h1`, `amixBg_pair_h1`, and the capstone
`lie0_bg_pair_h1` (3401 lines, zero sorry, build 121 s; new SHA in
`LowRegBgC0Pair.md`).  `LowRegBgA1Pair` compiles again on top of it (27 s),
and the C1Time closure is current.

`LowRegBgA1Refold.refold_time` (new, first elaboration) initially hit
heartbeat-immune `whnf`/`isDefEq` deterministic timeouts — the signature of
instance-tower unification divergence, here `MemLp.add` instantiated at the
CLM space over the reducible `metricH3/H2/H1 = tensorHs` abbrevs.  Fixed
structurally (route the time-`L²` membership through `memLp_clm_affine`
exactly as `c0_time` does, so `MemLp.add` only ever sees `ℝ`); GREEN in ~27 s
at the default term budget, statement unchanged (details in
`LowRegBgA1Refold.md`).  `LowRegLiftAffine` then exposed one defeq-transparency
regression (`LowA1CorePair`, a Prop wrapper passed where `extend_pair_apply`
wants the literal ∀∃ form, no longer unfolds as a `def` at application
positions) — fixed by declaring it `abbrev`, faithful to its docstring;
focused 22 s + build 24 s GREEN.  The full mandated chain
`Amix → CoeffPair → Integrate → Assemble → Core → C0Time → A1Refold →
LiftAffine` is exact GREEN with current `.olean`s.

The HfLo migration to the refolded `FLo` route also LANDED in this pass:
`LowRegLiftHfLo.lean` now consumes a supplied `FLo` at the equation level
(mirroring `lowreg_N_affine`'s hypothesis block) and invokes `refold_time`
once at the packet level in `lowreg_hfLo_data`, which re-exports the obtained
`FLo` existentially; `refoldAffA1` replaces `lowAffA1` (same slot type, so
the `lowreg_lift_two` fixed-point shape at `LowRegLiftTwo.lean:169/:206` is
unchanged), and `lowA1Lo` no longer appears in the file.  In
`LowRegA1LoPair.lean` the stale `lowreg_N_radial` was REMOVED as unrepairable
on the new route (its core formula would need `refoldCore.C1 = lowCoreData.C1`,
which is false: `refoldCore.C1 = c0CoreData.C1 + lowCoreDataBg.C1`);
`lowA1Core_pair`/`lowA1Lo_ball` are kept as the honest producers for
`lowBaseN`-shaped statements.  Both modules focused + targeted-build GREEN
(HfLo 24 s, A1LoPair 17 s), zero grep hits remain for the removed
declarations, details in `LowRegLiftHfLo.md`.  This removes the module's
dependence on the D₄-free `a1Lo` pair estimate but proves no new mathematics.

Honest accounting: `ricci_flow_unif_existence` remains 0%.  Dedicated
machinery unchanged at approximately 83% (this pass moved compile health and
restored lost verified content, not the endpoint); the whole HCG compactness
project remains in the low single digits.

## Planner update No. 92 (2026-08-02) - HI-SIDE REFOLD PACKET EXPORTED; A2-COMPAT ROUTE RULED

Wiring brick toward the `(aLo, aHi) = (1, 2)` instantiation of
`lowreg_realize_two` (plan: `LowRegApplyTwo.md`).  `LowRegLiftHfLo.lean`
(746 → 1053 lines, GREEN, no set_option) now re-exports from its single
`refold_time` invocation everything it previously discarded: explicit
`Z L ≥ 0`; `FHi` with continuity, smooth-core formula
(`c0CoreData.a1Hi + oneCore.a1Hi`), and pointwise affine bound; the Hi
family `refoldAffA1Hi` (congr baked in, slot type
`tensorHs g 0 2 ((2:ℝ)+1) →L tensorHs g 0 2 (2:ℝ)`) with `MemLp`, toLp
bounds `≤ L*‖duhH3 f‖ + √T*Z` on BOTH scales, an a.e. uniform Hi bound
`≤ Z + L*B3`, and the verbatim `hA1compat` square
`∀ᵐ t, incl ∘ AHi t = ALo t ∘ incl`.  `lowreg_hfLo` unchanged; MemLp
certificates re-derived via `memLp_clm_affine` rather than transported
(instance-tower discipline); square proved pointwise, never as an
operator-family equality.

RULING (recorded in `LowRegApplyTwo.md` Risk 1): `lowAffA2` and
`lowRegA2TotalLo` are genuinely different families (missing principal
summand, extra radial factor, a.e.-only state identification), so the
existing total-A2 square cannot serve as `hA2compat` — realize_two's `A2Lo`
slot is forced to the term of the proved `hfLo` equation.  The A2 arm gets
the same treatment as A1: build `lowAffA2Hi` from `lowA2Hi` with the radial
factor at the high scale and prove its own square.  `liftA2Two` is NOT the
A2Hi of this instantiation.

Honest accounting: `ricci_flow_unif_existence` remains 0% (unstated).
Machinery ~83%; this entry is packet plumbing on the Lane-B/C junction.

## Planner update No. 93 (2026-08-02) - APPLY_TWO LANDED: (1,2) REALIZATION ASSEMBLED

ACCOUNT CORRECTION first: `ricci_flow_unif_existence` is STATED — black box
(N) at `Evolution/ExtendViaUniqueness.lean:80`, the file's single `sorry`
(line 98) is its placeholder.  Earlier entries' "unstated" is wrong from here
on; say "(N) stated, proof 0%".  Its header also fixes the discharge shape:
a-posteriori endpoint bootstrap of the ONE low-regularity solution on its
fixed horizon (never per-order horizon-shrinking re-runs).

Brick (two stages, both GREEN, ledger `LowRegApplyTwo.md`):

2a `LowRegLiftHfLo.lean` (1264 lines): A2 arm now mirrors the A1 arm —
`lowAffA2Hi` (from `lowA2Hi`, radial factor at the high scale, congr baked
in), `lowAffA2Hi_le/_data`, and the compat square `lowAffA2_compat`.  The
completed `∀ v` a2 Hi/Lo square was FOUND, not rebuilt: `radialA2_lip`
(`DeTurck/DeTurckRemainderLowBaseTimeA2.lean:370`, last conjunct), re-exported
with continuity and `C·ρ` bounds on BOTH scales by `lowA2_small`
(`TensorMaximalRegularity/LowRegOperatorTime.lean:667`).  Also:
`Continuous FLo` + `FLo` core formula + `FLo` affine bound + `(C2:ℝ) = B2`
now exported by `lowreg_hfLo_data`; `stateField` promoted to public.

2b NEW `LowRegApplyTwo.lean` (255 lines): `lowreg_apply_two` — the
`(aLo, aHi) = (1, 2)` instantiation of `lowreg_realize_two` with the refold
families, smallness closed via `lift_small_le` + `lift_smallness`.
STATABILITY RULING: the horizon condition cannot be an outer hypothesis —
the first-order constant `K = max (Z + L·B3) B1` exists only after
`refold_time` runs at the given `T, f`; conclusion shape is
`∃ K ≥ 0, ∀ {c}, 0 ≤ c → c < 1 → B2 ≤ c → B2Hi ≤ c →
T ≤ lowregLiftHorizon c K → ∃ …, realize_two package`.  Honest-input audit:
the three new `lowA2Hi` hypotheses are jointly satisfiable by `lowA2_small`
alone (same lever, shrink `ρ` against its `C`, also gives `B2, B2Hi ≤ c`).

Still owed by this lane (next brick): wire `lowreg_partial_sol` into
`hball`/`hforce`/`hball3`, thread `lowA2_small` at a chosen `ρ` with
`C·ρ < 1`, and the consumer `T`-choice against the reported `K`.  Unchanged
mathematical frontier elsewhere: field-level Palatini difference identity;
class-uniform `Ksup` at `j = 1`.

Honest accounting: (N) stated, proof 0%.  Dedicated machinery ~81%
(sub-estimates across passes range 78–83; the spread is estimate noise, not
regression).  Whole HCG compactness project: low single digits.

## Planner update No. 94 (2026-08-02) - SOLVE_TWO LANDED; B3 IS THE ONE OPEN INPUT, ROUTE RULED

`LowRegApplyTwo.lean` (547 lines, GREEN, axiom-clean): `lowreg_solve_two`
(line 412) takes ONLY `hDim, g` and PRODUCES the coefficient radius `ρ`, the
fibre threshold `δ` with `hreal'`, a horizon `T₀ > 0`, `B2`, and for every
`0 < T ≤ min T₀ 1` the solver's own trajectory `f` with the full
`lowreg_apply_two` package (`IsRealizedTwo`, line 273).  Caller supplies
only: `T`, the contraction level `c` (`B2 ≤ c < 1`,
`T ≤ lowregLiftHorizon c K` against the packet's `K`), and `B3` with the
a.e. `H³` trajectory bound.  Producer→slot map and probed Lean facts in
`LowRegApplyTwo.md` (notably: `((1:ℕ):ℝ)` is NOT defeq `(1:ℝ)`; the
completed-`a2Lo` identification must be done at `C2` and lifted — direct
`rfl` is a kernel timeout).

FINDING 1: `lowreg_partial_sol` itself is UNUSABLE for this wiring — it
picks its state radius with no cap, while the lift forces `R ≤ ρ` at
`lowA2_small`'s radius.  The six-number pair `lowreg_bounds_exist` +
`lowreg_partial_sol_of_bounds` (`UnifClassBounds.lean`) at realization
radius `P := min ρ ρN` gives the nested cascade `ρ₀ → Pr → ρN → ρL → ρ → P`
with `R = lowregStateRad … P ≤ ρ`.

FINDING 2 (the one open analytic input): the `B3` slot is `L^∞_t H³` on the
trajectory, and structurally has NO producer here — maximal regularity gives
`L²_t H³` with norm ≲ ‖f‖ ≤ R/4, not shrinking in `T`; `L^∞_t H³` is half a
derivative above the trace space.

ROUTE RULING (planner, 2026-08-02, for the next brick): do NOT chase
`O(√T)` decay of `‖duhH3‖` (T-dependent fixed-point family, genuinely
nontrivial).  The contraction does not need the `M·√T` SHAPE, only
smallness: `‖toLp A1‖ ≤ L·‖duhH3‖ + √T·Z` and `‖duhH3‖_{L²ₜH³} ≤ c₀·‖f‖ ≤
c₀·R/4` (the CORE maximal-regularity estimate — locate its spelling), with
`R` shrinkable through the Finding-1 cascade.  So: drop/optionalize the
pointwise `hball3/B3` inputs (the a.e. uniform Hi bound they feed is not
consumed by `nonautL2Map`, which needs only `MemLp`), thread the maxReg
norm bound, and repackage the contraction arithmetic as joint smallness in
`(ρ, R, T)` beside `lowregLiftHorizon`.  If the maxReg `L²ₜ`-norm lemma for
`maxRegDuhamelSolField`/`duhH3` is genuinely absent, THAT is the recorded
frontier (name it), not the `L^∞` bound.

Honest accounting: (N) stated, proof 0%.  Machinery ~83% — the Lane-B/C
junction is now SOLVED (not hypothesis-parameterized) modulo the single `B3`
input.  Whole HCG compactness project: low single digits.

## Executor report on No. 94 (2026-08-02) - B3 DISSOLVED, ROUTE RULING LANDED

The ruling is implemented and GREEN; ledger in `LowRegApplyTwo.md`, brick 4.

The CORE maximal-regularity estimate was NOT missing.  It is
`norm_maxRegDuhamelSolField_zero_le`
(`Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:217`),
`‖maxRegDuhamelSolField a hT hT1 0 F‖ ≤ (1 + T)·‖F‖`, i.e. the zero-initial
Duhamel map is bounded `L²ₜHᵃ → L²ₜHᵃ⁺²` with a `T`-benign constant.  Its
`duhH3` spelling is the new `norm_duhH3_le` (`LowRegLiftHfLo.lean:153`), via the
new `norm_congrLp` (`:136`).  No new analysis was required.

`B3`/`hball3` are gone from `lowreg_hfLo_data`, `lowreg_apply_two`,
`IsRealizedTwo` and `lowreg_solve_two`.  `lowreg_solve_two`'s hypotheses are
again only `hDim` and `g`, and the caller's obligations are now two inequalities
between reals the packet reports: the `T`-free margin `6A < 1 - c` and
`T ≤ lowregLiftHorizon' c Z`, with `A = 2L‖f‖` and `Z` the zeroth-order size.
New arithmetic in `LowRegLiftSmall.lean`: `lowregLiftHorizon'` (`:282`),
`lift_aff_arith` (`:304`), `lift_small_aff` (`:350`).

NEW SMALLEST FRONTIER for this lane (an ordering issue, not analysis): the
margin `6A < 1 - c` is discharged by capping the realization radius `P`, since
`A ≤ L·R/2` and `R ≤ P`, but `L` is bound *inside* `lowreg_hfLo_data` because
`refold_time` (`LowRegBgA1Refold.lean:324`) quantifies `∃ Z L` AFTER its state
argument `u : timeL2 H³ T`.  Hoist `Z, L` above that binder — they are the
affine-growth constants of `FHi`/`FLo`, built from `ρ, δ, hreal` only — and
`lowreg_solve_two` can then take a target `η > 0`, cap `P ≤ η/L`, and report
`A ≤ η`.

Honest accounting: (N) stated, proof 0%.  Machinery ~84%.  Whole HCG
compactness project: low single digits.

## Executor report on No. 94 (later, 2026-08-02) - ORDERING OBSTRUCTION DISSOLVED; SOLVE_TWO IS UNCONDITIONAL

The frontier the previous report left ("hoist `Z, L` above the `u` binder") is
done, and it cost no mathematics: the u-free halves already existed.
`c0_ext_pair` (`LowRegBgC0Time`, private) was *verbatim* the C0 packet, and
`c1_ext_pair` (`LowRegBgC1Time`, private) *verbatim* the C1 packet.  Neither
`F`-construction ever mentioned the trajectory.  Full ledger in
`LowRegApplyTwo.md`, brick 5.

New public spine, one per lane, each REPLACING the old `*_time` (no wrappers
kept - every consumer chain here is single-consumer):

- `c0_pack` (`LowRegBgC0Time:322`), `c1_bg_pack` (`LowRegBgC1Time:763`),
  `refold_aff` (`LowRegBgA1Refold:331`): `∃ ρ₀ > 0, ∀ ρ δ …, ∃ Z L FHi FLo,
  Continuous + smooth-core formulas + `‖F x‖ ≤ Z + L‖x‖` + the u-free
  Sobolev square`.  No `T`, no `u`.
- `lowreg_hfLo_data` (`LowRegLiftHfLo:1117`) and `lowreg_apply_two`
  (`LowRegApplyTwo:171`) now TAKE that packet instead of producing it.
- `IsRealizedTwo` (`:84`) is the bare package: it lost the `∃ A Z ∀ c …` prefix
  and the `B2 B2Hi` parameters, and moved above `lowreg_apply_two`, which now
  states its conclusion by name instead of repeating 55 lines of existential.

`lowreg_solve_two` (`:383`) is now UNCONDITIONAL in the sense that matters:

```
∃ ρ δ hρ hδ0 hδ_le hreal' B2, 0 ≤ B2 ∧
  ∀ {c}, B2 ≤ c → c < 1 →
    ∃ T₀, 0 < T₀ ∧ ∀ {T} (hT : 0 < T), T ≤ T₀ → ∀ (hT1 : T ≤ 1),
      ∃ f, IsRealizedTwo g hρ hδ0 hδ_le hreal' hT hT1 f
```

The caller picks only `c` and `T`.  Both former obligations are discharged
inside: the horizon one by folding `lowregLiftHorizon' c Z` into `T₀`, the
margin `6·(2L‖f‖) < 1 - c` by capping the realization radius
`P := min (min ρ ρN) ((1-c)/(6(L+1)))` - possible exactly because `c` and `L`
are now both in scope before `P` is chosen.  Then `‖f‖ ≤ P/4` via
`norm_congrLp` + `lowregStateRad_le_P` + the `‖gforce‖ ≤ R/4` conjunct of
`lowreg_partial_sol_of_bounds`, and the rest is `linarith`.  Note the quantifier
order `ρ, B2 → c → T₀ → T → f`: `T₀` really does depend on `c`, because the
radius does.

Also deleted as dead: `refoldAffA1_data`, `refoldAffA1Hi_data` (the two
`L^∞_t H³` WARNING wrappers from brick 4), the ~105 lines of per-`u` time
plumbing inside the old `refold_time`, and the ~275 lines of the same inside
`c0_time`/`c1_bg_time` - all of it was already being discarded by its single
consumer, which rebuilt the `MemLp` witnesses itself from the affine bounds.
The five files went 3953 -> 3507 lines with no proof obligation added, and the
`set_option synthInstance.maxHeartbeats 1000000` that `refold_time` needed is
gone (the blow-up was the `timeL2`/`MemLp` statement layer, not the actions).

Verification: focused check + targeted `lake build` GREEN for all five modules
in dependency order; the six touched endpoints report exactly
`[propext, Classical.choice, Quot.sound]`.

Honest accounting: (N) stated, proof 0%.  Machinery ~84% (unchanged - this pass
removed a wiring obstruction and 450 lines of dead code, it did not add
mathematics).  Whole HCG compactness project: low single digits.

## Planner update No. 95 (2026-08-02) - RUNG (1,2) CLOSED END-TO-END

Milestone marker for the four-brick sequence No. 92-94 + the two executor
passes: `lowreg_solve_two` (`LowRegApplyTwo.lean:383`) now derives, from
`hDim, g` ALONE, the packet `ρ, δ, hreal', B2` such that for every
contraction level `c` with `B2 ≤ c < 1` there is `T₀ > 0` under which every
horizon `0 < T ≤ T₀, T ≤ 1` carries the solver's own trajectory `f` with the
full realized package `IsRealizedTwo` (CrossScaleField, zero trace, clean
equation, both fixed points, forcing inclusions, carrier/representative
pins).  Caller freedom = exactly `(c, T)`.  Axiom-clean; the five touched
modules are focused + build GREEN with zero heartbeat options; acceptance
included a mojibake sweep of the encoding-repaired `LowRegBgC0Time.lean`.

Candidate next fronts, in rough leverage order (planner, not yet
dispatched):
1. Lane C C3 residue - supply the smooth representative to
   `LowRegForceHi.force_hi_smooth` from the solution packet (makes
   `fHi =ᵐ N2 ∘ state` honest at `aHi = 2`).
2. The a-posteriori fixed-horizon bootstrap: iterate the closed rung to all
   orders on the ONE horizon, per the (N) discharge ruling in
   `Evolution/ExtendViaUniqueness.lean`'s header.
3. The class-uniformity layer for τ₀ (the actual (N) content); open
   mathematical walls unchanged: field-level Palatini difference identity,
   class-uniform `Ksup` at `j = 1`, E7, Lane F.

Honest accounting: (N) stated (`Evolution/ExtendViaUniqueness.lean:80`,
sorry at :98), proof 0%.  Dedicated machinery ~84%.  Whole HCG compactness
project: low single digits.

## Planner ruling No. 96 (2026-08-02) - C3 ROUTE CORRECTED: FROZEN-SPLIT N2, NOT THE SMOOTH FAMILY

Recon before dispatching front 1 of No. 95 found that `force_hi_smooth`'s
`F`/`hpin` inputs (a SMOOTH-CORE family realizing the trajectory field a.e.)
have NO producer in the solution packet — `lowreg_partial_sol` exports only
the abstract Duhamel field, and smooth-core membership of the actual
trajectory is a-posteriori regularity, i.e. front 2's content.  No. 95
mis-ranked front 1 as a wiring brick on that route.

CORRECT ROUTE (already recorded in `LowRegRealizeTwo.md`, "alternative
producer", now actionable): take `N2` to be the frozen split
`N2 u := N(0) + (A2 u + A1 u) u`, whose right side is `H²`-valued at the
`H⁴` regularity the LIFTED solution has; prove `incl ∘ N2 = lowRegN` on the
ball by the equalizer-closed density argument — both sides are now
CONTINUOUS (this is what tonight's packets unlocked: `Continuous FHi` from
`refold_aff`, `Continuous lowA2Hi` from `lowA2_small`, `Continuous lowRegN`
from the packet), and they agree on the smooth core by `lowCore_split`
(`DeTurckRemainderLowBaseTime.lean:1723`) + the smooth-core formulas +
`staticForce` at order 2 (`LowRegLiftNTerm`, arbitrary real order).  Then
the ALREADY-PROVED `lowreg_force_id` (`LowRegRealizeTwo.lean`) upgrades
`fHi =ᵐ N2 ∘ state` for the realized trajectory.  `force_hi_smooth` stays
as the smooth-family variant for the smooth era; no representative is
needed now.

## Executor report on No. 96 (2026-08-02) - C3 CLOSED AT `aHi = 2`; N2 IS PURE ALGEBRA

GREEN.  The frozen-split `N2` exists, lifts `lowRegN` along the scale
inclusion, and the realized `(1,2)` package now *carries* the high Nemytskii
identity.

**Route correction inside the ruling.**  No. 96 expected an equalizer-closed
density argument for `incl ∘ N2 = lowRegN`.  That work is already banked one
layer down, in `lowreg_N_affine` (`LowRegLiftAffine.lean:318`), which proves
`congr(lowRegN w) = refoldBaseN (congr w.1)` on the whole `H3` ball.  So the
new object only has to be a **lift of `refoldBaseN`**, and that is pure algebra
of the two commuting squares this lane already exports.  No density, no
smooth-core re-entry, no new estimate.

**Domain ruling.**  `lowreg_force_id`'s `N2` slot is `lowerState g 1 R -> H^σ`,
i.e. `H3`-domained, and the `H4` passenger of `lowA2Hi` genuinely cannot live
there.  It does not have to: `CrossScaleField.hiL2` at `a = 2` is `H^{a+2} =
H4`-valued, so the lifted solution's own field is `H4`.  `liftHiN` is therefore
defined on `H4`, and the pin `incl_{3<=4}(hi t) = state t` is derivable from
the package.  `lowreg_force_id` itself is used only through its unconditional
half `lowreg_force_lo`.

**Decls added** (`ShortTime/LowRegForceHi.lean`, +1 import `LowRegLiftAffine`):

- `liftHiN` (:132) - `staticForce g g 2 + lowA2Hi (incl42 v) (radialCLM_{H4} ρ
  (incl42 v) v) + FHi (incl43 v) (lowRadialH3 ρ (incl43 v))`, `H4 -> H2`.
- `hiN_incl` (:166) - `incl_{1<=2} (liftHiN v) = refoldBaseN (incl_{3<=4} v)`.
- `hiN_lowreg` (:299) - `congr_{1N=1}(lowRegN w) = incl_{1<=2}(liftHiN v)`
  whenever `incl_{3<=4} v = congr_{1N+2=3} w.1`.  This is the `N2` slot.
- `force_hi_id` (:373) - `fHi =ᵐ fun t => liftHiN (hi t)` from `lowreg_force_lo`
  plus the pin, by injectivity of the inclusion.

**Core identities -> summand map** (what makes `hiN_incl` true):

| `liftHiN` summand | discharged by | `refoldBaseN` summand |
| --- | --- | --- |
| `staticForce g g 2` | `staticForce_incl`, `lowBaseForce_eq_static` | `lowBaseForce g` |
| `lowA2Hi (incl42 v) (radialCLM_{H4} …)` | `lowA2_small`'s square, `radialCLM_incl`, `radialCLM_h3`, `tensorHsInclusion_trans_apply` | `lowA2Lo (incl32 u) (lowRadialH3 ρ u)` |
| `FHi (incl43 v) (lowRadialH3 ρ …)` | `refold_aff`'s square, `lowRadialH3_incl` | `FLo u (lowRadialHs ρ (incl32 u))` |

`lowCore_split` / `refold_split` / `a2Lo_core` / `refoldLo_core` /
`lowRadial_eq_self` are what make `lowreg_N_affine` true, and they are consumed
there; this brick does not re-enter them, and `liftHiN` mirrors `refoldBaseN`
summand for summand so the algebraic shape stays `N(S) - N(0) = a2 S + a1 S`.

**Endpoint wiring.**  `IsRealizedTwo` (`LowRegApplyTwo.lean:90`) gained one
conjunct, `fHi =ᵐ fun t => liftHiN g … FHi (congr_{2+2=4} (u.hiL2 t))`, proved
inside `lowreg_apply_two` from `u.link`, the two `repr` pins, `aeSetLift_coe_ae`
and `hiN_lowreg`.  A standalone corollary was rejected: the package
existentially binds `FHi`, `fHi`, `u`, so a corollary could not name them
without duplicating the whole existential.  `IsRealizedTwo` has no other
consumer, and `lowreg_solve_two` transmits the conjunct unchanged - so for the
trajectory it produces, the high forcing **is** the genuine Ricci--DeTurck
nonlinearity along the lifted `H4` field.

**Not touched.**  `force_hi_smooth` stays as the smooth-era variant; its `F` /
`hpin` inputs still have no producer, as No. 96 diagnosed.

**Verification.**  Focused checks GREEN for both edited files; targeted builds
`+…LowRegForceHi` and `+…LowRegApplyTwo` GREEN, no warnings from either, no
`sorry`, no heartbeat option.

**Honest accounting.**  `(N)` (`Evolution/ExtendViaUniqueness.lean:80`, sorry at
:98) still 0%.  Lane C is now complete for the `(1,2)` rung, C3 included.
Dedicated machinery ~85%.  Whole HCG compactness project: low single digits.
The next front is unchanged from No. 95's list: the a-posteriori fixed-horizon
bootstrap to all orders, then the class-uniformity layer for `τ₀`.

## Planner update No. 97 (2026-08-02) - PALATINI WALL VERIFIED CLOSED; No. 95 WALL LIST CORRECTED

A read-only recon pass (report: `PALATINI_WALL_PLAN.md`, grep-verified)
found that the field-level Palatini difference identity and ALL THREE of
its blocked consumers were already proved sorry-free by ledger No. 84-86
(2026-07-30/31), and that No. 95's "open mathematical walls" line was a
stale carry-over that post-dated the closure:

- the differentiated Palatini identity: `covDerivPal_eq`
  (`Geometry/Curvature/CurvatureOperator/DifferentiatedPalatini.lean:380`),
  bundled field form `curvCovDerivOf_sub_base`
  (`HCGCompactness/UnifPalatiniDiff.lean:319`); the No. 77 obstruction
  (extension corrections) was killed by tensoriality
  (`covDerivConnDiff_congr` / `covDerivConnDiff_eq_ext`);
- (a) the `a = 1` curvature envelope: `unifRmJetOne`
  (`HCGCompactness/UnifCurvatureJetOne.lean:876`, `1 ≤ Λ` only);
- (b) class-uniform `Ksup` at `j = 1`: `unifKsupLeOne`
  (`HCGCompactness/UnifDeTurckRHSOne.lean:1538`, `∃ Kstar` before `∀ g₀`);
- (c) `unifFc`: dissolved by No. 85 (`hcurv` gone from `UnifNZeroBound` /
  `UnifRealizeRadius`).

CORRECTED OPEN-WALL LIST (replacing No. 95's): **E7 class-uniform packet
and Lane F wiring** — plus one dormant, consumer-less residue (the
all-order abstract `hcurv` of `UnifBochnerGap.lean:304`) and one design
flag: `(N)`'s hypothesis budget is `∀ a ≤ 3`
(`Evolution/ExtendViaUniqueness.lean:85`) and the `a = 1` envelope already
consumes all three jet orders; any future `a ≥ 2` envelope would need
jets past order 3, i.e. a change to `(N)`'s own hypothesis — do not start
an `a ≥ 2` envelope without ruling on that first.

Stale doc corrections applied: `UnifPalatiniJet1.md` "Remaining frontier"
retired (the `Λ < 2` migration is done; `unifKsupLeOne` exists);
`UnifCurvatureJet1Diff.md` §4 retitled CLOSED with pointers, W1/W2 kept
as history.  CALIBRATION (4th instance of walls-smaller-than-reported,
per the standing over-count memory): grep-verify every "open wall" line
against the tree before dispatching an attack on it; recon-before-
implementation just saved a full implementation cycle here.

Honest accounting: (N) stated, proof 0%.  Machinery ~85% (this entry adds
no content — it removes a phantom from the map).  Whole HCG compactness
project: low single digits.

ADDENDUM (corrected after line-by-line adjudication) — grep-verified
`sorry` census, 2026-08-02, both lanes.  The H2Pair chain
(`DeTurckRemainderLowBaseH2*.lean`) is ZERO-sorry — the "capstone 3/5,
classes 1–2 open" memory line was the FIFTH walls-overcount phantom.
Every other candidate line turned out to be docstring PROSE
(`UnifCovSumCross`, `UnifCurvatureJetBound`, `UnifJetTowerMatch`,
`DeTurckInitialDataExistence` all have ZERO real sorries; the first two
even contain "FALSE WALL — proved sorry-free upstream" narratives) — the
sixth overcount.  The COMPLETE real `sorry` inventory of
`HCGCompactness/Unif*.lean` + `ShortTime/*.lean` is exactly TWO:

1. `hAcc_of_jets` (`UnifCovSumN3.lean:461`) — the general-`m` (`m ≥ 3`)
   accumulator bound.  NOT on (N)'s critical path: the `m ≤ 2` cases are
   theorems, (N)'s jet budget is `∀ a ≤ 3`, and nothing on the endpoint
   path consumes it (its only mentions are its own file and
   `UnifJetTowerMatch`'s "not on this path" note).  Dormant frontier,
   same status as `UnifBochnerGap`'s `hcurv`.
2. `weyl_pointwise_diagonalKernel_bound_of_closed`
   (`WeylEigenvalueCountingBound.lean:115`) — a DELIBERATE cited
   analytic input.  CORRECTED 2026-08-03 (front-3 recon, transitive
   import-closure measurement): its self-description "the only sorry on
   the short-time-existence dependency path" is STALE — it is reachable
   only from `RealizeTransport`/`SolutionC2Continuous`/`DeTurckRicciPde`,
   none of which lies in the closure of the endpoint chain
   (`LowRegAllOrderJet`, `MaxRegSolutionJointlySmooth`,
   `ShortTimeExistence`, `ExtendViaUniqueness`, …); the
   smooth-representative gate was re-proved Weyl-free
   (`SpectralSmoothRepresentativeRealize.lean:478`).  Policy: carry, do
   NOT thread into (N), do NOT commission a discharge; acceptance gate =
   `#print axioms` on the finished endpoint (import closure bounds
   module reachability, not axiom use).

CONSEQUENCE: "E7 + Lane F" as open WALLS is also stale narrative — the
(N) critical path now reduces to: front 2 (fixed-horizon bootstrap →
chart-Gram C∞ fields), the (N) assembly with the τ₀ class-uniformity
layer (whose `unifKsupZero`/`unifKsupLeOne` inputs EXIST), and the Weyl
citation policy.  The bootstrap recon (in flight) is the decisive input
for everything that remains.

## Executor report on No. 95/96 front 2 (2026-08-02) - RECON: THE ENDPOINT CHAIN ALREADY EXISTS; FRONT 2 IS A RE-BASE, NOT A LADDER

Read-only recon pass on front 2 (the a-posteriori fixed-horizon bootstrap).
Plan written to `ShortTime/LOWREG_BOOTSTRAP_PLAN.md`.  No Lean edited, no file
claimed, no build run.

**Headline: front 2 was mis-scoped as ladder-building.**  The machinery it was
supposed to construct is already in the tree and sorry-free.
`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
(`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean:1311`)
takes a `MaxRegSolutionSpace a T` with zero trace plus an all-order
smooth-in-time forcing-coordinate package and returns exactly the `(N)` `rr`
fields - `F 0 = 0`, the `Ico`-slab PDE with `HasDerivWithinAt … (Ici 0)`, and
`JointChartGramSmooth T` (joint `C∞` on the CLOSED `Icc 0 T` slab, corner
included, i.e. strictly stronger than `(N)`'s `Ico`) - on the FULL, UNSHRUNK
horizon `T`.  Below it, `deTurckRicci_chartRegularity_of_jointChartGramSmooth`
(`ShortTime/DeTurckChartRegularityFromJoint.lean:701`) already derives the whole
six-conjunct chart-regularity tail sorry-free, and the apex
`jointChartGramSmooth_of_spectralSmooth_timeSmooth`
(`SpectralEigenSeriesJointGram.lean:1687`) is axiom-clean.  Decisively: the tame
endpoint's `hC` slot has a purpose-built dim-3 producer at **`a = 2`** -
`hs2_opBound_at_two` (same file `:1593`) - with **no consumer anywhere in the
repo**.  `a = 2` is exactly the high scale of the rung No. 95 closed.  The
architecture was designed for this join and never wired.  So the corner is NOT a
separate frontier (§4 of the plan), and none of the `Analysis/Elliptic`
`laplacianDomainPow` / `TimeSliceBootstrap` bridges the dispatch asked about are
on the critical path - `laplacianDomainPow` is scalar and provably UNBRIDGED to
`tensorHs` (0 files mention both), and no `Ico`-corner `∞` PDE bootstrap exists
or is needed.

**Both proposed ladder routes are ruled out, on evidence already in the tree.**
(i) Rung-via-fixed-point: `lowreg_lift_two` delegates to `nonautL2_lift`
(`NonautonomousL2Lift.lean:526`), which CONSTRUCTS the high solution by a Banach
fixed point and carries the per-rung smallness
`(C2Hi)*(1+T) + 2√(1+T)*‖A1Hi‖ < 1`.  The `(1+T)` factor does not vanish as
`T → 0`, so the only lever is the coefficient radius `ρ`, fixed once before the
trajectory exists - a single `ρ` cannot beat order-dependent constants.  That is
the forbidden "shrinking horizons" shape.  (ii) Rung-via-maxreg-lifting: the
smallness-free same-horizon engine DOES exist and is sorry-free
(`solField_into_all_tensorHs_interior`, `ParabolicInteriorSmoothing.lean:326`),
but its `hcouple` is a `+1` coupling while the DeTurck remainder loses `+2`;
`ForcingTimeBootstrap.lean`'s own header (lines 22-36) records verbatim that this
bootstrap STALLS at net advance 0, and `DeTurck/PrincipalPartMatch.lean`
§"Scope (honest)" records that only the SYMBOL-level principal-part match is
established - the operator-level `H^{d+1} → H^d` bound is not assembled.  Do not
commission a `+1` coupling.

**Recommended route + first brick.**  Re-base the existing endpoint chain at
`a = 2` on the solver's own horizon.  Every slot of the tame endpoint has a
producer from `IsRealizedTwo` (`LowRegApplyTwo.lean:90`) or is routine glue,
EXCEPT the all-order smooth-in-time forcing-coordinate package
(`f`/`hf_smooth`/`hf_mass`/`hf_id`), whose only producer
(`deTurckForcing_smoothTimeCoordinateFamilySymm`, `ForcingTimeBootstrap.lean:199`)
is stated at supercritical order with the HIGH-ORDER existence horizon and rests
on two honest `sorry` POSITs in `ForcingCoordinateTimeRegularity.lean`.  Front 2
= re-base those two POSITs at `a = 2` pinned to the low lane's `force_hi_id`, then
re-run the sorry-free glue.  FIRST BRICK: new
`ShortTime/LowRegAllOrderJet.lean`, theorem `lowreg_allOrderJet`, deriving the
`f`-package from `IsRealizedTwo` with exactly two named honest inputs (A′)/(B′)
and a folded realizability-ball clause.  Top risk, recorded honestly: `a = 2`
sits in a band BELOW every supporting estimate in the tree - the whole `(1,2)`
coefficient layer is at literal exponents `1,2,3,4`, the one classical-shape tame
estimate (`smoothN_h1_tame`, `LowRegCoreTame.lean:201`) is at `a = 1`, and every
generic-order estimate (including the genuine all-orders Nash-Moser-shaped
splitting at `DeTurckRemainderPrincipalArmOpNorm.lean:9271`, whose small constant
`εwrap ≲ δ/(1−δ)` is uniform in `k`) is gated on `2·finrank + 10 ≤ a`.  (A′)/(B′)
are nonetheless TRUE and the analytic raw material is present and fully generic
(`tensorHeatSemigroupHs_opNorm_le`, `TensorHeatEquation/SmoothingHs.lean:791`;
`heatPower_opNorm_le`, `Heat/Semigroup/SpectralBounds.lean:524`; `staticForce` at
arbitrary real order, `LowRegLiftNTerm.lean:142`).  Also recorded: the route is
dim-3-pinned, and the supercritical route cannot be salvaged for `(N)` because its
`T` is the lifetime of a high-order fixed point, hence a function of all
derivatives of `g₀`, which the ruling forbids for the LIFETIME.

**Honest accounting.**  Unchanged by a recon pass: `(N)`
(`Evolution/ExtendViaUniqueness.lean:80`, sorry at :98) still 0%.  Dedicated
machinery ~85%.  Within front 2: the endpoint chain above the forcing package is
~90% and sorry-free; the forcing package at `a = 2` is 0%.  Whole HCG compactness
project: low single digits.  The recon moved no mathematics - it re-scoped the
front and removed two dead ends.


## Executor report on No. 77 final paragraph (2026-08-02) - ALREADY DISCHARGED; delivered the object-level strengthening instead

DISPATCH OUTCOME, honestly first: the commissioned brick did not need
building.  No. 77's closing item ("the E3 consumers speak
SmoothCcTensor/iteratedCovGrad/riemannianFiberNormSq while everything
above speaks Tensor0SField/iterCov/normSq0S, and the two towers are
unbridged; missing is iteratedCovGrad g 0 s j (toRS0 A) = toRS0
(iterCov g s A j) or its norm-level equivalent") was already closed
TWICE: No. 73 (UnifJetTowerMatch.lean) in the section->field direction
(ccUnitField, iterCovGrad_unit_eq, rfns0_unit_eq, rfns_iterCovGrad_eq)
and No. 81 (UnifCurvaturePack.lean) in the field->section direction
(ccOfField, ccOfField_unit, rfns_ccOfField_eq, rmSection,
rfns_rmSection_eq), together with the exact consumer corollary this
dispatch asked for - exists_curvJet_sup transported into the
iteratedCovGrad/riemannianFiberNormSq currency IS exists_rmJetSup
(UnifCurvaturePack.lean, squared-norm shape), plus exists_rmJetSups
(one constant over a window) and unifRmSecSup (the Lambda-class order-0
face).  No. 78 had already recorded the staleness; the No. 77 paragraph
itself was never updated, which is what re-commissioned it.

A fresh sibling HCGCompactness/IterCovLiftBridge.lean was written and
verified green (real lake build, axiom-clean) before this was noticed;
it was then DELETED rather than landed, because its three public
theorems were verbatim duplicates of ccOfField_unit /
rfns_ccOfField_eq / exists_rmJetSup under different names.  Nothing
that only renames ratified API should enter the tree.

WHAT DID LAND (UnifCurvaturePack.lean, +93 lines, no existing
declaration touched, real targeted lake build of the importing module
UnifCurvatureJetOne green, all three new public declarations
axiom-clean):

* cc_ext_unit - the converse of ccUnitField: a (0,s)-rank section is
  DETERMINED by its unit field.  This extensionality principle was
  missing from the whole ccUnitField/ccOfField layer; both existing
  transports were "compute the unit value", never "conclude from it".
* iterCovGrad_ccOfField - the tower bridge as an identity of OBJECTS:
  iteratedCovGrad g 0 s j (ccOfField g s A) = ccOfField g (s+j)
  (iterCov g s A j).  Both sides at (0, s+j): no arity cast, no
  combinatorial factor, constant exactly 1.
* iterCovGrad_rmSection - the curvature instance: the a-th section-level
  jet of rmSection g IS the packaging of nabla^a Rm(g).

Why this is not a fourth restatement: rfns_ccOfField_eq transports
NORMS, so each new functional of the jet (toL2, toHs, the Bochner
L2 shapes, linearity) needs its own transport lemma.  The object
identity transports all of them by one rewrite.  It is cheap for a
structural reason worth recording: an upper-rank-zero fibre is one
dimensional, so agreement on the parallel unit (0,0)-tensor is
agreement outright.

DEBT RECORDED, not paid: ccOfField now has a twin, ccLift0S
(Evolution/ForwardUniqueIBP.lean:72), the same map built through
unitScalarRSLiftCs instead of MixedSection.fromMultilinearSection, with
its own ccLift0S_unit.  When No. 81's placement note is executed (move
ccOfField/ccOfField_unit/rfns_ccOfField_eq next to ccUnitField in
UnifJetTowerMatch.lean), collapse ccLift0S onto it.

LEAN LESSON, reusable: apply ContMDiffSection.ext on a
TensorRSModel/TensorRSSpace section fails with "failed to synthesize
FiberBundle ..." unless the declaration is elaborated under
set_option backward.isDefEq.respectTransparency false.  The knob is
TRANSPARENCY, not synthInstance.maxHeartbeats - UnifCurvaturePack
already budgets 1600000 heartbeats and still failed.

HONEST ACCOUNTING.  This moves E3's packaging layer from "norms
transport" to "objects transport" and adds the layer's missing
extensionality lemma; it moves no analysis.  E3's two real walls are
untouched and unchanged: hcurv (UnifBochnerGap.lean:304) still needs a
Leibniz/Kato product estimate for pointwiseTensorCurv AND a
class-uniform ALL-ORDER sup of nabla^a Rm, the latter still gated on
No. 78 dispatch (ii) (the Palatini difference brick) at every order
>= 1.  (N) (Evolution/ExtendViaUniqueness.lean:80) remains 0%; its
dedicated machinery is unchanged at ~85%; whole HCG compactness
project: low single digits.

## Executor report on No. 95/96 front 2, brick B1 (2026-08-02) - LowRegAllOrderJet LANDED: FRONT 2 REDUCED TO ONE NAMED LEAF + TWO WIRING OBLIGATIONS

New file `ShortTime/LowRegAllOrderJet.lean` (530 lines), notes in the
same-name `.md`.  Focused check GREEN; targeted module build GREEN
("Build completed successfully"); sorry census EXACTLY ONE, the frontier
body.  Nothing else was touched: no existing Lean file edited, no claim
forced.

WHAT LANDED

* `lowreg_allOrderJet` (:203) - from `IsRealizedTwo` alone (the output of
  `lowreg_solve_two`, whose horizon is built from `hDim` and `g` only),
  produce the four forcing slots the tame joint-smoothness endpoint
  consumes at `a = 2`, on the FULL unshrunk horizon: the carrier `u` with
  vanishing trace identified with the affine zero-datum Duhamel map of the
  high forcing (brick B2, `timeH1.ext` against `maxRegDuhamelMap_init` /
  `maxRegDuhamelMap_timeDeriv_eq`); smooth-in-time spectral coordinates
  `fc` with the all-`(j,tau)` majorant on `Icc 0 T` and the a.e. pin; the
  per-mode Duhamel identity `hf_id`; and the realizability radius `R0` with
  the endpoint's `hball_full` on ALL of `Icc 0 T` (brick B4, folded in per
  the plan's risk 2).
* `lowreg_joint_smooth` (:362) - the endpoint re-run at `a = 2`, feeding
  `hs2_opBound_at_two` into the `hC` slot.  FIRST CONSUMER of that
  purpose-built dim-3 producer.  Sorry-free AND independent of the frontier.
  Conclusion = the `(N)`-shaped triple on the full `T`: `F 0 = 0`, the
  `Ico`-slab PDE with `HasDerivWithinAt ... (Ici 0)`, and
  `JointChartGramSmooth T` on the CLOSED slab (corner included, strictly
  stronger than `(N)`'s `Ico`).
* `lowreg_joint_of_re` (:462) - the composition: `IsRealizedTwo` implies
  there is a package such that, once the two named wiring obligations hold
  for it, the `(N)` fields follow on the solver's own horizon.

THE POSIT DESIGN CHOICE: ONE LEAF, NOT TWO

The brief asked for a verbatim mirror of the supercritical (A)/(B) split
with `deTurckSobolevNHa2Symm` replaced by `liftHiN`.  (B) IS UNWRITABLE AT
`a = 2` as a true standalone statement: there is no intrinsic `H4 -> H2`
Ricci-DeTurck Nemytskii in the tree, and the only high-scale nonlinearity
at the closed rung is the frozen split `liftHiN`, whose first-order arm
`FHi` is an UNCONSTRAINED EXISTENTIAL inside `IsRealizedTwo` - no
continuity, no bound, no smooth-core formula.  "Jet-mass preserving" is
false for a general such `FHi`, and becomes true only after re-importing
the `refold_aff` / `lowA2_small` bundle that `lowreg_solve_two` discards.
Taking the plan's own fallback (S8.1: "if the two-posit split is unwritable
at `a = 2`, collapse to a single named leaf"), (A')+(B') are composed into

  `lowreg_forceJetMass` (:151, sorry at :180)

hypothesised on the low-lane forcing identity (`IsRealizedTwo`'s last
conjunct = `force_hi_id`'s conclusion, so NOT vacuous), concluding exactly
what `lowreg_allOrderJet` consumes: a radius `R0` with the endpoint's
`hball_full` on the whole closed slab, plus a `JetSpectralMassControl`
coordinate family for the forcing agreeing a.e. with `t |-> (fHi t).coeff i`.

WHAT IS STILL OPEN, AND WHY IT IS NOT A THIRD POSIT

`hfloor` (S8.3) and `hForce` (B3) are NOT derivable from `IsRealizedTwo`,
and they are producer-side gaps, not new mathematics:

* `IsRealizedTwo` carries NO norm bound at the high scale.  `hfloor` needs
  `||u.deriv||`, and `u.deriv = timeScaleLaplacian 2 u.hiL2 + fHi` with
  neither factor bounded in the package (`lowreg_solve_two` caps `||f||`
  at the LOW scale, internally, and does not export it).
* `hForce`'s route `force_hi_id -> hiN_lowreg -> lowreg_N_affine ->
  lowRegN_on_smooth` needs `hR`, `hreal`, `hNcont`, `hcore`, `hA2cont`,
  `hA2core`, `FLo`, `hFLo`, `hFcore`, `hA2sq`, `hFComm` and the
  `lowerState g 1 R` membership of the pinned smooth state.  Separately the
  a.e.-to-everywhere upgrade on `Ico` (the supercritical model proof
  `realizedForcingCoord_eq_smoothNSymm` uses
  `Measure.eqOn_Ico_of_ae_eq`) needs continuity of the nonlinearity, i.e.
  `hA2Hicont` + `hFHi` at `a = 2`.  None of these are in the package.

SMALLEST UNBLOCKING NEXT STEP: widen `IsRealizedTwo`
(`LowRegApplyTwo.lean:90`) to export `Continuous FHi`, `hA2Hicont`, the two
commuting squares `hA2sq` / `hFComm`, the low radius `R` with `hreal`, and
the forcing-norm cap.  All six are already in scope at the single producer
`lowreg_apply_two`; this is a one-file edit and makes B3 + S8.3 provable in
place.  (Alternative: return the obligations alongside `IsRealizedTwo` from
`lowreg_solve_two`.  Larger.)

RISK REGISTER OUTCOME

* Risk 3 (exponent transports) MOSTLY DISSOLVED: `((2:N):R)` is
  DEFINITIONALLY `(2:R)` in this Mathlib, so `MaxRegSolutionSpace (2:R) T`
  drops into the endpoint's `a := 2` slot with no transport, and
  `Nat.cast_nonneg 2` unifies with `(show (0:R) <= (2:R))` by proof
  irrelevance (probed with `rfl` before writing anything).  Only `2+2` vs
  `4` needs work, and only at the one `liftHiN` junction; the single
  bookkeeping lemma `tensorHsCongr_coeff` (`cases h; rfl`) covers it.
* Risk 2 (`hball_full`) folded into the leaf as instructed.  RECORDED FOR
  THE PROVER: the supercritical lane shrinks the horizon there only because
  it must hit a PRE-FIXED realizability radius; the endpoint takes `R0`
  implicitly, so a proof may pick `R0` from the mass majorant
  (`perModeConv_allOrder_timeDeriv_spectralMass_le` at `j=0`,
  `tau=(2:R)+2`, `R0 := sqrt(sum Cmaj)`) with NO shrink.
* Risk 8.1 (`a = 2` below every in-tree estimate) CONFIRMED and is exactly
  why the leaf stays a leaf.

HONEST ACCOUNTING.  `(N)` (`Evolution/ExtendViaUniqueness.lean:80`) is
UNCHANGED at 0% - it is still unstated as a proof.  This brick moves front 2
from "the forcing package at `a = 2` is 0%" to "front 2 is one named
analytic leaf plus two named producer-side wiring obligations away from
closed": call front 2 ~55% done, the remaining 45% being ~35%
`lowreg_forceJetMass` (a genuine multi-session parabolic-regularity layer,
below every supporting estimate in the tree) and ~10% the B3 / S8.3 wiring
(an `IsRealizedTwo` widening, routine).  `(N)`'s dedicated machinery ~85% ->
~86%.  Whole HCG compactness project: low single digits, unchanged.

## Executor report on No. 95/96 front 2, brick B3 + S8.3 (2026-08-03) - hForce DISCHARGED; hfloor is a HORIZON task, not a packaging gap

Two files touched, both claimed and released:
`ShortTime/LowRegApplyTwo.lean` and `ShortTime/LowRegAllOrderJet.lean`.
Focused check GREEN on both; targeted builds in dependency order
(`+...LowRegApplyTwo`, then `+...LowRegAllOrderJet`) both "Build completed
successfully".  Sorry census over the two files: EXACTLY ONE, the frontier
`lowreg_forceJetMass` body.  No new sorry/admit/axiom, no heartbeat option.
`IsRealizedTwo` still has exactly the two consumers it had before (grep-verified
across the tree), both inside this brick's scope.

WHAT THE PREVIOUS BRICK ASKED FOR, AND WHAT IT BOUGHT

`IsRealizedTwo` (`LowRegApplyTwo.lean`) was widened to re-export the producer
certificates `lowreg_apply_two` already had in scope and discarded.  New
existential binders: `FLo`, `R`, `hR : 0 < R`, `hreal` (the R-radius
realization).  New conjuncts (14-25; the first thirteen are byte-stable):
`R <= rho`; `Continuous (lowRegN g g hR _ hreal)`; `Continuous (coreN g g _
hreal)`; `Continuous (lowA2Lo ...)`; the `lowA2Lo` smooth-core formula against
`refoldCore`; `Continuous (lowA2Hi ...)`; `Continuous FHi`; `Continuous FLo`;
the `FLo` smooth-core formula against `c0CoreData`/`oneCore`; the second-order
square `hA2sq`; the first-order square `hFComm`; and the a.e. carrier state-ball
bound `forall-ae t, ||u.lo.toFun t|| <= R`.

That last conjunct is the one item that was not literally lying around: `hball`
is stated for `stateField`, the consumer needs it for the carrier.  The bridge is
a five-step calc inside `lowreg_apply_two` from `hreprpin` + `hreprae` +
`tensorHsInclusion_trans_apply` + `norm_incl_congr` + `hsf`.  `lowreg_solve_two`
is UNCHANGED: every new item was already an argument it passes down.

THE HARVEST

`lowreg_joint_of_re`'s `hForce` slot is GONE - discharged, not hidden.  New in
`LowRegAllOrderJet.lean`: `lowregNsec` (the concrete Nsec = symmetrized smooth
DeTurck remainder, i.e. the supercritical lane's own Nsec, named) and the private
`coord_eq_smoothN`, the `a = 2` analogue of `realizedForcingCoord_eq_smoothNSymm`.
`lowreg_allOrderJet` gained one conclusion conjunct (the endpoint's hForce, with
the `hball` hypothesis DROPPED - the L^2 pin alone suffices, weakest-assumptions)
and one hypothesis `hDim`.

Two design points worth banking, because both dissolved an apparent wall:

* Inclusions preserve eigen-coordinates (`tensorHsInclusion_coeff_apply`, rfl).
  So `hiN_incl` alone moves the frozen split's coefficients down to
  `refoldBaseN`, and the whole a.e.-to-everywhere upgrade runs one scale lower,
  at H^3, where `refoldBaseN_cont` already exists.  NO `liftHiN` continuity
  lemma had to be written, and neither `hA2Hicont` nor `Continuous FHi` is
  actually consumed (they are exported anyway, as the plan named them).
* `R0 <= R` is NOT needed.  The state-ball membership of the pinned smooth family
  comes from `h_pin` (which forces `smoothCcToTensorHs g 2 (F t) = toFun u t`)
  plus the new a.e. bound, upgraded to every `t in Ico 0 T`.  Routing it through
  the endpoint's own `hball` (radius `R0`, produced existentially by the
  frontier) would have needed `R0 <= R`, which no producer supplies and which
  cannot be arranged by shrinking `R0` (hball_full is monotone the wrong way).

Both upgrades are `Measure.eqOn_Ico_of_ae_eq`: once on `fc i` vs the
`refoldBaseN` coordinate (continuity from the PUBLIC
`tensorHs_continuousOn_of_coeff_of_higher_mass` at sigma = 3, sigma' = 3 + weyl
+ 1, fed by `perModeConv_allOrder_timeDeriv_spectralMass_le` at k = 0 - the
supercritical private helper `realizedSol_solField_continuousOn_Ha2` is only a
~20-line wrapper of that public lemma, so it was re-derived rather than
de-privatised), and once on `min ||toFun u .|| R` vs `||toFun u .||` (continuity
from `timeH1.continuousOn_toFun`).

FINAL VISIBLE HYPOTHESES OF `lowreg_joint_of_re`

`hDim`, `g`, `F_RHS`, `hRepr` (now stated against `lowregNsec`), `hrho`, `hdelta0`,
`hdelta_le`, `hreal'`, `hT`, `hT1`, `f`, `hre`.  Conclusion:

  exists u : MaxRegSolutionSpace (2:R) T,
    sqrt T * ||u.deriv|| <= 1/(2*(hs2_opBound_at_two hDim g).choose) ->
    exists F delta' hdelta_lt hdelta', F 0 = 0 /\ (L^2 pin to u on Icc 0 T)
      /\ (Ico-slab PDE with HasDerivWithinAt ... (Ici 0))
      /\ JointChartGramSmooth T

`hRepr` stays a hypothesis on purpose (brick B6, explicitly out of scope).

WHY `hfloor` SURVIVES - AND WHY THAT IS NOT A PACKAGING GAP

I checked whether the widened exports suffice, as instructed.  They do not, and
the reason is structural, not bookkeeping.  `u.deriv = timeScaleLaplacian 2
u.hiL2 + fHi`; bounding it needs (1) a Neumann bound
`||fHi|| <= ||liftForceHi g g T||/(1-kappa)` from the exported fixed-point
conjunct, where kappa is the contraction certificate `hsmallHi` (in scope inside
`lowreg_apply_two`, NOT currently exported - this is the one further export a
future brick would want); (2) `||liftForceHi g g T|| <= sqrt T *
||staticForce g g 2||` plus the maximal-regularity and `timeScaleLaplacian`
bounds, giving `||u.deriv|| <= sqrt T * K(g)`; and therefore (3)
`sqrt T * ||u.deriv|| <= T * K(g)`, so `hfloor` reduces to `T <= 1/(2 C K(g))`.

Step (3) is the point: HFLOOR IS A SMALLNESS CONDITION ON `T` ITSELF.  For an
arbitrary `T` admitting an `IsRealizedTwo` package it is false.  No further
widening of the package can discharge it; it must be folded into the horizon
`T0` that `lowreg_solve_two` reports, which is a change to `lowreg_solve_two`'s
statement - a separate brick.  So it is left visible and precisely named, not
posited.

ONE LEAN LESSON THAT COST A COMPILE (recorded in both .md notes)

After editing a `def` that a downstream file destructures with `obtain`, the
downstream focused check reads the STALE .olean.  The symptom is not "unknown
constant" but a misaligned rcases pattern: the extra patterns are pushed onto
the last visible conjunct and rcases calls `cases` on it, reporting
"Dependent elimination failed ... at case Eq.refl" with the UNFOLDED
`Filter.EventuallyEq` (`some 0 = mu {x | ...}^c`).  Run the targeted upstream
`build +Module` before checking the consumer.

HONEST ACCOUNTING.  `(N)` (`Evolution/ExtendViaUniqueness.lean:80`) is UNCHANGED
at 0% - still unstated as a proof.  This brick moves front 2 from "one named
analytic leaf + two named wiring obligations" to "one named analytic leaf + one
horizon fold in `lowreg_solve_two`": call front 2 ~62% done (up from ~55%), the
remaining ~38% being ~35% `lowreg_forceJetMass` (unchanged: a genuine
multi-session parabolic-regularity layer, below every supporting estimate in the
tree) and ~3% the `hfloor` horizon fold.  `(N)`'s dedicated machinery ~86% ->
~87%.  Whole HCG compactness project: low single digits, unchanged.


================================================================================
EXECUTOR REPORT - 2026-08-03, brick 9 (front 2): HFLOOR FOLDED INTO THE HORIZON
================================================================================

GREEN.  The `hfloor` obligation that brick 8 left visible is gone.  Front 2 now
ends in a single self-contained theorem whose only inputs are the dimension, the
metric, the RHS functional and `hRepr`.

WHAT WAS PROVED

The high forcing of the realized `(1,2)` package has size `O(sqrt T)`, and the
carrier's time derivative is at most twice it, so the endpoint's horizon floor
is a plain smallness condition on `T` that the solver can meet itself.

Concretely, three facts compose:

  (a) NEUMANN.  `fHi` solves `fHi = nonautL2Map(...) fHi + liftForceHi g g T`.
      The map fixes the origin and is Lipschitz with constant
      `kappa = (C2Hi)(1+T) + 2 sqrt(1+T) ||A1Hi||_{L2}` (`nonautL2_dist_le`).
      If `kappa <= 1 - q` then `q ||fHi|| <= ||liftForceHi||`.  New private
      lemmas `nonautL2Map_zero`, `norm_fix_le` in `LowRegApplyTwo.lean`.

  (b) UNIFORM GAP.  The existing `lift_aff_arith` gives only `kappa < 1`, which
      bounds nothing.  Halving the `T`-free margin to `6(2L||f||) <= (1-c)/2`
      turns the same budget split into `kappa <= 1 - (1-c)/4`.  New
      `lift_aff_margin` in `LowRegLiftSmall.lean` (canonical home, beside
      `lift_aff_arith`).  The halved margin was ALREADY true in
      `lowreg_solve_two` - the old proof discarded a factor 2 in a `linarith`.

  (c) CARRIER DERIVATIVE.  The carrier is the zero-datum Duhamel map of `fHi`,
      so `maxRegDuhamelMap_deriv` +`maxRegHomogeneousDerivField_norm_le` (at
      `u0 = 0`) + `maximalRegularityDerivField_norm_le` give
      `||u.deriv|| <= 2 ||fHi||`.  NOTE: the route through the
      `timeScaleLaplacian` conjunct of `IsRealizedTwo`, which the brick-8 note
      proposed, is NOT needed and would have required an `H^4 -> H^2` operator
      norm for the rough Laplacian.  The Duhamel derivative split is sharper and
      already in the tree.

With `||liftForceHi|| <= ||staticForce g g 2|| sqrt T` (`norm_liftForceHi_le`,
cited, not re-exported), the chain is
`sqrt T ||u.deriv|| <= 2 sqrt T ||fHi|| <= 8 ||SF|| T/(1-c)`, so the floor
`<= 1/(2C)` holds as soon as `T <= Kf(1-c)/(4(||SF||+1))` with `Kf = 1/(4C)`.

WHAT THE INTERFACES LOOK LIKE NOW

`IsRealizedTwo` takes one more parameter `(Kf : R)` (appended after `f`) and
carries one more conjunct, `sqrt T * ||fHi|| <= Kf`.  All earlier binders and
conjuncts are byte-stable.

`lowreg_solve_two hDim g (hKf : 0 < Kf)` reports `T0` as a min of THREE horizon
factors (the third is the new `lowregFloorHorizon g c Kf`), and every `T <= T0`
package meets the floor.

`lowreg_joint_two hDim g F_RHS hRepr` (new, `LowRegAllOrderJet.lean`) is the
caller-facing endpoint:

  exists B2 >= 0, forall c in [B2,1), exists T0 > 0, forall T in (0, min T0 1],
    exists u F delta' ...,
      F 0 = 0  /\  (L2 pin of F to the carrier on Icc 0 T)
              /\  (Ico-slab PDE, HasDerivWithinAt ... (Ici 0))
              /\  JointChartGramSmooth T

`Kf` is deliberately a PARAMETER of the Lane-C layer rather than the hard-wired
`1/(4C)`: `C = (hs2_opBound_at_two hDim g).choose` belongs to the
joint-smoothness endpoint, and hard-wiring it would make the realization package
depend on that layer.  `lowreg_joint_two` is where the two meet.

DECLS CHANGED (line numbers after the edit)

  LowRegLiftSmall.lean   :354  lift_aff_margin                       NEW
  LowRegApplyTwo.lean    :228  lowregFloorHorizon                    NEW
                         :232  lowregFloorHorizon_pos                NEW
                         :244  nonautL2Map_zero (private)            NEW
                         :282  norm_fix_le (private)                 NEW
                         :107  IsRealizedTwo                         +1 param, +1 conjunct
                         :342  lowreg_apply_two                      margin halved, +hTfloor
                         :723  lowreg_solve_two                      +{Kf} hKf, T0 gains a min
  LowRegAllOrderJet.lean :481  lowreg_allOrderJet                    +{Kf}, +1 conjunct
                         :771  lowreg_joint_of_re                    hfloor implication REMOVED
                         :867  lowreg_joint_two                      NEW

REMAINING OPEN ITEMS ABOVE THIS FILE - exactly two

  1. `lowreg_forceJetMass` (`LowRegAllOrderJet.lean:421`, the single `sorry`):
     all-order interior-time smoothing of the zero-datum `a = 2` trajectory.
     Untouched.  Still a genuine multi-session parabolic-regularity layer - it
     sits BELOW every supporting estimate in the tree (the tame splitting is
     gated on `2 finrank + 10 <= a`, i.e. `a >= 16` in dimension three).
  2. `hRepr` (brick B6): extraction of the order-free Ricci-DeTurck
     representation block from `deTurckRicci_solution_with_jointReg`
     (`ShortTime/DeTurckInitialDataExistence.lean`).  A one-file edit, out of
     scope here.

LEAN LESSON THAT COST ONE COMPILE

`linarith`/`nlinarith` WITHOUT `only` scan the entire local context.  Inside
`lowreg_apply_two` (dozens of real-valued hypotheses, several of them large)
that turned cheap arithmetic into a `(deterministic) timeout at whnf` reported
at the DECLARATION line, not at the tactic - which reads like an elaboration
problem in the statement.  Rewriting every new arithmetic step as
`linarith only [...]` took the file from failing at 78s to green at 37s.  Use
`linarith only` inside any wide-context theorem.  (Also: `omit [Inst] in` must
precede the docstring, like `set_option ... in`.)

VERIFICATION

Focused checks GREEN for all three edited files; targeted builds
`+...LowRegLiftSmall`, `+...LowRegApplyTwo`, `+...LowRegAllOrderJet` all GREEN
("Build completed successfully").  Sorry census over the three files: exactly
one, `lowreg_forceJetMass`.  No new `sorry`/`admit`/`axiom`, no heartbeat option.

HONEST ACCOUNTING.  `(N)` (`Evolution/ExtendViaUniqueness.lean:80`) is UNCHANGED
at 0% - still unstated as a proof.  This brick closes the ~3% `hfloor` horizon
fold that brick 8 identified and makes front 2's endpoint self-contained: call
front 2 ~65% done (up from ~62%), the remaining ~35% being almost entirely
`lowreg_forceJetMass` plus the small `hRepr` extraction.  `(N)`'s dedicated
machinery ~87% -> ~88%.  Whole HCG compactness project: low single digits,
unchanged.

## Planner update No. 98 (2026-08-03) - FRONT 2 WIRED TO ONE LEAF: lowreg_joint_two

Milestone marker for the front-2 brick trio (executor reports above):

1. `LowRegAllOrderJet.lean` NEW (recon route: front 2 is a WIRING job — the
   joint-smoothness engine
   `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii` and its
   dim-3 `a = 2` producer `hs2_opBound_at_two` existed with zero consumers).
   The supercritical (A)/(B) posit split COLLAPSED to one leaf:
   (B′) is unwritable at `a = 2` as a true standalone statement (no intrinsic
   `H⁴→H²` Nemytskii below `2·finrank+10`; `IsRealizedTwo` then still
   discarded the FHi certificates), so the single honest frontier is
   `lowreg_forceJetMass` (:421, the sorry) — fixed-point-pinned, with the
   full-`Icc` ball clause folded in (no horizon shrink needed for `R₀`).
2. `IsRealizedTwo` WIDENED (conjuncts 14-25 + `Kf` + `√T‖fHi‖ ≤ Kf`):
   `hForce` fully discharged — inclusions preserve eigen-coordinates
   (`tensorHsInclusion_coeff_apply` is `rfl`), so the a.e.→`Ico` upgrade runs
   at `H³` where `refoldBaseN_cont` exists; `R₀ ≤ R` never needed.
3. `hfloor` FOLDED into the reported horizon: Duhamel-direct
   `‖u.deriv‖ ≤ 2‖fHi‖` (no rough-Laplacian norm), Neumann `norm_fix_le`
   off `nonautL2_dist_le`, margin halved (`lift_aff_margin`) to a UNIFORM
   `κ ≤ 1 − (1−c)/4` gap, `lowregFloorHorizon` third min-factor in
   `lowreg_solve_two`, `Kf` kept a parameter so Lane C never depends on the
   endpoint's `C`.

NET: `lowreg_joint_two` (`LowRegAllOrderJet.lean:867`) — from
`hDim, g, F_RHS, hRepr` alone: `∃ B2 ≥ 0, ∀ c ∈ [B2,1), ∃ T₀ > 0,
∀ T ≤ min T₀ 1, ∃ u F …, F 0 = 0 ∧ pin ∧ Ico-slab PDE ∧
JointChartGramSmooth T` — the (N) rr-field shapes on the solver's own
horizon.  Remaining inputs of front 2: the ONE sorry `lowreg_forceJetMass`
(attack recon in flight: the forcing-smoothness self-reference — how the
supercritical template closed the loop, what replaces coefficient
state-Fréchet-differentiability at `a = 2`) and the routine `hRepr`
extraction (B6).  Sorry census over the three touched files: exactly one.

Honest accounting: (N) stated, proof 0%.  Front 2 ~65%; machinery ~88%.
Whole HCG compactness project: low single digits.

## Executor report on No. 98 (2026-08-03) - forceJetMass RECON: THE SUPERCRITICAL POSITS ARE PROVED, AND THE JET LAYER IS ORDER-GENERIC

Read-only recon on front 2's single frontier `lowreg_forceJetMass`
(`LowRegAllOrderJet.lean:421`, sorry at `:450`).  Plan written to a NEW file
`ShortTime/FORCEJETMASS_PLAN.md` (419 lines).  No Lean edited, no file claimed,
no Lake process run; nothing here is build-verified.

THE STRUCTURAL ANSWER.  `LOWREG_BOOTSTRAP_PLAN.md` S6/S9 - and the header of
`HeatSemigroup/ForcingCoordinateTimeRegularity.lean` itself - still say the
supercritical template rests on two honest `sorry`s, POSIT (A)
`deTurckForcing_solCoeff_jetSpectralMass` and POSIT (B)
`deTurckSobolevNHa2_jetSpectralMass_preserving`.  That is STALE: both were
discharged (commits `358687842`, `b369c07f0`, `272498f86`), and `grep -rnw sorry`
over `Analysis/Spectral/Intrinsic/HeatSemigroup/` and `.../DeTurck/` returns ZERO
code sorries.  So the loop IS closed upstream, and the mechanism is now readable
end to end.  It never differentiates the nonlinearity in the state.  Five stages:
(S1) an a-priori ALL-sigma SPATIAL spectral-mass bound on the solution, proved by
a finite-dimensional Galerkin energy ladder + Gronwall + Fatou
(`GalerkinLimitUniformMass.lean:1125`) - no time-derivatives anywhere; (S2) all-order
spatial mass turns the trajectory into a genuine `SmoothCcTensor` path
(`ForcingFiniteOrderTimeRegularity.lean:513`, order-generic); (S3) on a smooth path the
DeTurck remainder's time-jets come from a joint C^k-in-(t,x) CHART chain rule
(Gram det/adjugate/inverse, Christoffel, DeTurck vector field, Ricci - the
`anisoOn_realize_*` chain, `:3170`-`:3519`); (S4) finite order to all orders by an
a.e.-agreement DIAGONAL (all `F k` agree a.e., hence EqOn, hence `F 0` is C-infinity),
`ForcingCoordinateTimeRegularity.lean:119`; (S5) the per-mode ODE recursion trading
2 spatial orders per time-derivative (`MaxRegInteriorTimeSmoothing.lean:196`).
So F-differentiability of the Nemytskii is not what closes the loop - a purely
SPATIAL a-priori estimate is, and the chart chain rule does the rest.

WHAT REPLACES IT AT a = 2.  The decisive finding: `ha_super` is VESTIGIAL in four
declarations of the smooth-core jet layer -
`deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection` (`:4980`),
`deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` (`:5116`),
`deTurckRemainder_path_timeJet_section` (`SmoothCoordinateJetPreservation.lean:132`),
`deTurckSmoothN_path_coeff_jetSpectralMass` (`:215`).  `grep -n ha_super` shows the
binder line, then nothing until the next declaration; the conclusions name
`deTurckSmoothRemainder`, which carries no `a`; each sits under
`set_option linter.unusedVariables false in`.  The Gronwall engine
`galerkin_energy_uniform_bound_perScale` (`GalerkinParabolicEnergy.lean:220`) has no
metric, no `a` and no nonlinearity at all (`sigma_0 : R` is free).  And the a=2
Nemytskii-to-smooth-core bridge is ALREADY PROVED twice over: `force_hi_smooth`
(`LowRegForceHi.lean:65`) gives `fHi =ae deTurckSmoothN g g 2 (symmS g (F t))` from a
pinned smooth family plus the ball - exactly what (S2) manufactures - and
`coord_eq_smoothN` (`LowRegAllOrderJet.lean:148`) is the state-level fallback.  Also,
the supercritical route's two horizon shrinks (`d_0`, `d_2`) exist only to enter the
realizability ball; at a=2 the ball is a GLOBAL hypothesis (`hreal'`, `delta <= 1/3`),
so both shrinks are dropped rather than transplanted - the full unshrunk `T` survives.
`hball_full` was separately verified to follow from `JetSpectralMassControl` + the pin
with no shrink: the sigma=4, j=0 majorant gives `R_0 := sqrt(sum Cmaj) + 1` by
`tensorHs.norm_eq_sqrt_tsum` + `Summable.tsum_le_tsum` (the exact pattern already run at
`ForcingFiniteOrderTimeRegularity.lean:5095`-`:5102`); only the a.e.-to-everywhere upgrade
of the coefficient pin is extra, and that is routine.

NET RE-CLASSIFICATION AND ROUTE.  Route R-a (coefficient-freeze) is rejected as stated -
`liftHiN`'s coefficient slots are `Dense.extend`-completed and `FHi` is an unconstrained
existential with only `Continuous` + affine growth, and an exhaustive grep confirms NO
Fréchet-differentiability-in-state lemma exists for any of `lowA2Hi`/`lowA2Lo`/`FHi`/`FLo`/
`lowRegN`/`liftHiN` - but its goal is reached for free by the identification above.  R-b
(smooth-core approximation + limit) is rejected: no limit theorem for
`JetSpectralMassControl` exists and it is superseded.  R-c (the No. 94 sigma-generic ladder
wall) is NOT required: the supercritical closure used neither a per-rung fixed point
(S3a's forbidden shape) nor a `+1` coupling (S3b's stall), because Galerkin approximants
are finite eigen-combinations, hence smooth, so no completed `H^{s+2} -> H^s` operator is
ever formed.  R-d (transplant) is ADOPTED.  The frontier therefore stops being "all-order
time-regularity of a self-referential forcing" and becomes ONE purely spatial,
time-derivative-free statement: for every real sigma there is `C_sigma` with
`sum_i w_i^sigma (perModeConv lambda_i (timeModeCoeff fHi i) t)^2 <= C_sigma` on all of
`Icc 0 T`.  The one genuinely new estimate behind it is the per-scale Galerkin dissipation
closure at BASE ORDER 2 (the a=2 analogue of `GalerkinParabolicEnergyDeTurck.lean:1390`,
today gated `4*finrank+10 <= a`, internally weakened to `2*finrank+10 <= a` for the
all-orders tame splitting).  In dim 3 the a=2 state control is `H^4 ⊂ C^{2,1/2}`, ample for
a second-order operator's coefficients, so the estimate is true - it is simply not the one
written.  This revises S8.1's "a = 2 is a band with no supporting estimates at all" to
"one spatial energy estimate at base order 2, plus wiring".  Bricks F1-F6 with the design
note (widen the leaf's hypotheses to carry the certificates the 2026-08-03 `IsRealizedTwo`
widening already exports, rather than re-deriving them from `hfix`) are in the plan file.
FIRST DISPATCHABLE BRICK: F1, delete the vestigial `ha_super` from the four declarations,
smaller file first, one focused check each - a pure hypothesis-deletion experiment.
STOP-SIGNAL: only if F1 goes RED (some `anisoOn_*`/`spectralPathFO_*` lemma genuinely needs
`a`) AND the base-order-2 dissipation is unstatable without a sigma-generic completed
coefficient family; that conjunction is R-c returning through the back door and is a
genuine route error.  Either failure alone is not a stop.

HONEST ACCOUNTING.  `(N)` UNCHANGED at 0% - stated, not proved.
`lowreg_forceJetMass` itself 0% - not one line of its proof exists; this pass moved NO
mathematics, it re-read the tree.  Its dedicated machinery is re-assessed from ~0% to
~60% of the transplantable stack (S2/S4/S5 proved and order-generic; S3 proved and
order-generic modulo the unverified F1 deletion; the a=2 core bridge proved; the Gronwall
engine order-generic), with the missing ~40% concentrated in F3 + F6 and essentially all
the mathematics in F6.  Front 2 stays ~65%; the change is classification, not progress.
`(N)`'s dedicated machinery ~88%.  Whole HCG compactness project: low single digits.

## Executor report on No. 98, brick F1 (2026-08-03) - GREEN: THE SMOOTH-CORE JET LAYER IS ORDER-FREE; RISK 1 REFUTED, STOP-SIGNAL CLOSED

F1 as dispatched in `FORCEJETMASS_PLAN.md` S9: a pure hypothesis-deletion experiment,
adding nothing.  Two files claimed and released,
`Analysis/Spectral/Intrinsic/HeatSemigroup/SmoothCoordinateJetPreservation.lean` and
`.../ForcingFiniteOrderTimeRegularity.lean`; 8 changed lines each (3 insertions,
5 deletions per file).  Focused check GREEN on both.  Targeted builds in dependency
order (`+...SmoothCoordinateJetPreservation`, then `+...ForcingFiniteOrderTimeRegularity`)
both "Build completed successfully".  No `sorry`/`admit`/`axiom` in either file, before
or after; no heartbeat option touched anywhere; no statement strengthened.

THE RESULT.  The supercriticality gate `2 * Module.finrank R E + 10 <= a` is VESTIGIAL in
the smooth-core time-jet layer, at both the all-order and the finite-order tier.  Deleted
from four declarations:

* `deTurckRemainder_path_timeJet_section` (`SmoothCoordinateJetPreservation.lean:132`) -
  dropped BOTH `(a : N)` and `ha_super`.
* `deTurckSmoothN_path_coeff_jetSpectralMass` (`:215`, private) - dropped `ha_super`;
  `(a : N)` kept, its conclusion names `deTurckSmoothN g0 g_bg a (F t) ...`.
* `deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection`
  (`ForcingFiniteOrderTimeRegularity.lean:4980`, private) - dropped BOTH.
* `deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` (`:5116`) - dropped `ha_super`;
  `(a : N)` kept for the same reason.

Four in-file call sites fixed by argument removal only (`:247`, `:483`, `:5147`, `:5384`;
the plan listed three - `:483` is the fourth, inside
`deTurckSobolevNHa2_jetSpectralMass_preserving`).  A repo-wide grep confirms these eight
sites are ALL the occurrences of the four names: no third file is affected, so nothing
was widened silently.

WHY THE RISK NEVER HAD TEETH.  Risk 1 feared `ha_super` re-entering transitively through
the ~30 `private` `anisoOn_*` / `spectralPathFO_*` lemmas (`:1116`-`:4527`) written inside
the supercritical section.  That block contains ZERO occurrences of `ha_super`.  It could
not have been otherwise: those lemmas are chart-level anisotropic regularity statements
about a path that is ALREADY smooth - Christoffel symbols, Gram determinant/adjugate/
inverse, chart Ricci, the DeTurck vector field, the pushed `connLapIter` - and once
smoothness is a hypothesis, the Sobolev exponent that bought it cannot reappear
downstream.  The jets' mass bound is likewise order-blind: it is produced from `hmodemass`
at an exponent `sigma' = 2k >= q` chosen INSIDE the proof, so no embedding threshold is
consulted.

THE BOUNDARY THIS DRAWS, which is the durable content.  `ha_super` survives exactly where
it feeds `deTurckRealizabilityRadius` / `deTurckSobolevNHa2_exists_of_super` - i.e. in
`deTurckSobolevNHa2_jetSpectralMass_preserving`,
`deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving`, and
`deTurckForcing_finiteOrderSmoothDriver`, all untouched.  So: THE COMPLETED-OPERATOR
REALIZABILITY LAYER IS ORDER-GATED; THE SMOOTH-CORE JET LAYER ABOVE IT IS NOT.  That is
the line the a=2 transplant has to respect, and it is now enforced by the signatures
rather than by prose.

CONSEQUENCE FOR THE CAMPAIGN.  (S3) is now available at `a = 2` unconditionally, so the
whole chart-level chain rule producing finite-order time-jets of the Ricci-DeTurck
remainder along a smooth path transplants for free.  Front 2's frontier collapses to the
single spatial statement (S1_2).  S8's stop-signal required F1 AND F6 to fail; F1 has
passed, so that conjunction is closed PERMANENTLY - route error R-c (the No. 94 sigma-
generic ladder wall) cannot return by this door, whatever F6 does.

FOLLOW-UP NOT TAKEN (out of this brick's scope, offered as intel).  A heuristic scan over
every file mentioning `ha_super` finds 28 further declarations that bind it and never name
it again, concentrated in `Sobolev/TensorHilbert/DeTurckVFJetRadiusFree.lean`,
`Spectral/Intrinsic/DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean`,
`.../DeTurckRemainderTameLipschitz.lean` and `Parabolic/RicciLinearization/`.  These are
CANDIDATES only - a bare `linarith`/`omega`/`simp_all` consumes a hypothesis from context
without naming it - but the reliable marker held in all four cases here:
`set_option linter.unusedVariables false in` sitting immediately above the declaration is
Lean itself having already noticed the binder is dead.  If more of the a=2 transplant
stalls on an order gate, sweep that list before believing the gate.
Also still stale and NOT fixed here (S7.6, deliberately left - it is a docstring edit
outside the two claimed files): `HeatSemigroup/ForcingCoordinateTimeRegularity.lean:38`,
`:46`, `:80`-`:84` still advertise POSITs (A)/(B) as "Honest `sorry`".

HONEST ACCOUNTING.  `(N)` UNCHANGED at 0% - stated, not proved; this brick moved no
mathematics toward it.  `lowreg_forceJetMass` itself UNCHANGED at 0% - not one line of its
proof exists; F1 deleted hypotheses, it proved nothing new.  What changed is that a
~60%-complete transplantable stack is now VERIFIED transplantable rather than conjectured:
S3's order-genericity was the one unverified load-bearing assumption in that 60%, and it
held.  Its dedicated machinery accordingly stays ~60% but is no longer conditional.
Front 2 stays ~65%.  `(N)`'s dedicated machinery ~88%.  Whole HCG compactness project:
low single digits.  NEXT: F2 (reuse `force_hi_smooth`, do not rebuild), then F3.

## Executor report on No. 98 front 3 (2026-08-03) - RECON: THE CLASS LAYER IS HALF-INSTANTIATED, AND THE WEYL SORRY IS OFF THE PATH

Read-only recon on front 3 (upgrading the single-metric endpoint chain to the
class-uniform `τ₀` that black box `(N)` demands).  Plan written to a NEW file
`ShortTime/FRONT3_ASSEMBLY_PLAN.md` (405 lines).  No Lean edited, no file
claimed, no Lake process run; nothing here is build-verified.

THE STRUCTURAL ANSWER.  Front 3 is not a new construction - it is finishing the
job `UnifClassBounds.lean` was written for and never wired.  That file already
re-states the whole low-regularity solve as a function of SIX REAL NUMBERS
(`Ctop, B0, B1, D, ρ, P`) and proves the horizon monotone in them
(`lowregHorizon_mono`, `:186`; `lowregHorizon_pos`, `:156`); its own docstring
(`:395`-`:397`) says verbatim that class-uniformity IS the problem of bounding
those six.  Crucially the consumer `lowreg_partial_sol_of_bounds` (`:263`) takes
them as HYPOTHESES, so the engine below needs ZERO change: the restructuring is
purely ∃-before-∀ on ten plain reals, exactly the shape `unifKsupLeOne`
(`UnifDeTurckRHSOne.lean:1538`) already realizes.  The `g₀`-spectral machinery
(`tensorHs g₀`, `metricH3 g₀`, eigenbasis, `MaxRegSolutionSpace`) must NOT be
hoisted and `(N)` never asks it to be - only one real number precedes `∀ g₀`.
The (A)/(B)/(C) split: (A) already class-uniform with proved producers = `D`
(`nZeroC`, `UnifNZeroBound.lean:417`, delivered by `nZero_lowregNfun` `:551` off
`unifKsupLeOne`) and `P` (`unifRealizeRad`, `H2PointwiseUnif.lean:346`, with
`realize_at_unif` `:360` and the horizon consequence `lowregHorizon_unif_pos`,
`UnifRealizeRadius.lean:43`); its `Cpt` input is ALSO closed - brick E4 IS landed
as `fibreMorrey_unif_base` (`SobolevEmbeddingUnif.lean:350`), so
`H2PointwiseUnif.lean:31`'s "brick E4 is not landed" is stale.  (B) individual
but routable through hypotheses (i)+(ii) = `Ctop, B0, B1, ρ` (`lowRegN_outer` ⟸
`coreN_outer` ⟸ `rem_h1_tame` `LowRegCoreTame.lean:104` ⟸ `rem_h1_of_jets`
`LowRegRemainderH1.lean:183`), `Z, L` (`refold_aff` = `c0_pack` + `c1_bg_pack`,
the latter ALREADY two-metric at `LowRegBgC1Time.lean:763`), `C`/`B2`/`c`
(`lowA2_small`, monotone in `ρ`, so shrinkable for free), and `Kjet`.  That is
brick E7 and it is the BULK - an API sweep with no new mathematics, one
constant-exposed sibling per producer, on the worked
`hs2_op_bound → hs2_op_bound_unif` template.  (C) genuinely individual = exactly
ONE quantity: `‖staticForce g g 2‖` inside `lowregFloorHorizon`
(`LowRegApplyTwo.lean:228`-`:231`), whose class bound needs `Ksup` at `j ≤ 2`,
hence metric jets to order FOUR, hence a change to `(N)`'s own `∀ a ≤ 3` budget
(`Evolution/ExtendViaUniqueness.lean:85`) that No. 97 already flagged as fully
consumed.  Plus the mechanical-but-load-bearing `g_bg := g₀` hard-wiring
(`lowreg_solve_two` calls `lowRegN_outer … g g` `:746` and
`lowreg_bounds_exist … g g` `:809`, and `oneCore g` is literally
`(lowCoreDataBg g g …).C1`, `LowRegBgA1Refold.lean:54`-`:65`), which must become
`g_bg := gBase` or NONE of (A) applies.

TWO CAMPAIGN NARRATIVES REFUTED BY MEASUREMENT (over-count instances nine and
ten).  (1) THE WEYL CITATION-SORRY IS NOT ON `(N)`'s DEPENDENCY PATH.  Transitive
import closure over the whole tree shows
`weyl_pointwise_diagonalKernel_bound_of_closed`
(`WeylEigenvalueCountingBound.lean:115`) is reachable from exactly THREE modules -
`RealizeTransport`, `SolutionC2Continuous`, `DeTurckRicciPde` - and NONE of
`LowRegAllOrderJet`, `LowRegApplyTwo`, `UnifNZeroBound`, `UnifRealizeRadius`,
`UnifDeTurckRHSOne`, `DeTurckInitialDataExistence`, `MaxRegSolutionJointlySmooth`,
`DeTurckRealizedSolutionFamily`, `ShortTimeExistence`, `ConjugatingDiffeoFamily`
or `ExtendViaUniqueness` has any of them in its closure.  Root cause: the
smooth-representative gate used to need Weyl and was RE-PROVED WEYL-FREE -
`spectralSmoothRealizesAsSmooth_holds`
(`SpectralSmoothRepresentativeRealize.lean:478`), docstring: "No Weyl
eigenvalue-counting / heat-trace input enters."  RECOMMENDATION: do NOT thread a
named Weyl hypothesis into `(N)`'s statement (it would be a fake frontier the
proof never uses), do NOT commission a discharge (a full local-Weyl-law
development, worth nothing to `(N)`), DO correct the two stale self-descriptions
(`WeylEigenvalueCountingBound.lean:59`-`:61` "the only sorry on the
short-time-existence dependency path" and No. 97's ADDENDUM item 2 "IT IS on the
path"), and make `#print axioms` on the finished endpoint the acceptance gate,
since import closure bounds module reachability, not axiom use.  (2) THE
DOCSTRING'S FINITE CHART-CENTRE FAMILY `S` IS NOT IN THE STATEMENT: `(N)`
quantifies `∀ (x₀ : M)` (`:87`) and the engine's `JointChartGramSmooth`
(`DeTurckChartRegularityFromJoint.lean:85`-`:90`) is `∀ (α : M)` on the CLOSED
`Icc 0 T`, strictly stronger than the needed `Ico 0 τ₀`.  No good-set atlas is
required; the docstring is aspirational prose and should be corrected, not
implemented.  Separately measured and GOOD NEWS: the DeTurck-to-Ricci conjugation
is HORIZON-PRESERVING - `conjugating_diffeo_family_jointsmooth`
(`ShortTimeAssembly/ConjugatingDiffeoFamily.lean:78`) closes at `:127` with
`refine ⟨T_DT, hDT, le_refl _, …⟩` - and `short_time_joint`
(`ShortTimeExistence.lean:72`) is a finished sorry-free assembly of exactly
`(N)`'s three conjuncts from `(IsQuasilinearMetricParabolicSolution,
JointChartGramSmooth)`, every step parametric in the background.  So the `rr`
packaging gap is genuinely only packaging: `lowreg_joint_two` (at `gBase`, at
`τ₀`) → `deTurckRicci_chartRegularity_of_jointChartGramSmooth`
(`DeTurckChartRegularityFromJoint.lean:701`) →
`conjugating_diffeo_family_jointsmooth` → `short_time_joint`'s body verbatim,
with `rr 0 = g₀` from `F 0 = 0` through `realizeMetric_zero`
(`UnifNZeroBound.lean:185`).

BRICKS AND FIRST DISPATCH.  G1 background widening of the refold packet
(`refold_aff_bg (g gB)` in `LowRegBgA1Refold.lean`, using the already-two-metric
`c1_bg_pack`; `c0_pack` is genuinely background-free), G2 background widening of
the solve chain, G3 `lowreg_bounds_unif` (the E7 sweep), G4 `Kjet`/`C*`
discharge, G5 the `lowregFloorHorizon` ruling, G6 `lowreg_solve_unif` + the `(N)`
endpoint.  FIRST DISPATCHABLE BRICK: G1 - it is in a file the front-2 lane does
NOT hold, it is one definition plus one restated theorem with `refold_aff` kept
as `refold_aff_bg … g g` so no call site changes, and without it none of the
class-uniform producers apply.  STOP-SIGNAL: only if G3 stalls because some
`_of_jets` constant provably needs `g₀`-data of order > 3 that (ii) cannot bound
AND G5's non-statement-changing options both fail; that conjunction means the
`a = 2` re-base cannot serve `(N)` at all.  Either failure alone is not a stop.
BLOCKING USER DECISION: R1/G5 - may `(N)`'s hypothesis budget rise from
`∀ a ≤ 3` to `∀ a ≤ 4`, or must the forcing floor be re-derived at `σ ≤ 1`?

NOTE FOR THE NEXT AGENT: `LowRegAllOrderJet.lean` is under active edit by the
front-2 lane and its line numbers moved during this pass (`lowreg_joint_two`
1676→1661, `lowreg_forceJetMass` 1068→1070).  Cite that file by declaration
name, never by line.  Every other file cited above is stable.

HONEST ACCOUNTING.  `(N)` (`Evolution/ExtendViaUniqueness.lean:80`, sorry `:98`)
UNCHANGED at 0% - stated, not one line of proof.  Front 3's own machinery ~25%,
and that number is INHERITED, not earned here: this pass moved NO mathematics, it
re-read the tree, removed two phantom requirements (the atlas and the Weyl
policy), corrected one stale doc line (E4), and classified the constants.  Front
2 stays ~65%.  `(N)`'s dedicated machinery ~88%.  Whole HCG compactness project:
low single digits.

## Planner update No. 99 (2026-08-03) - TWO PARALLEL RECONS BANKED; ONE USER DECISION SURFACED

Integrating the two read-only recon reports (both above; plans =
`F6_ESTIMATE_RECON.md`, `FRONT3_ASSEMBLY_PLAN.md`):

F6 SIDE: the supercriticality gate is a derivative-budget BOOKKEEPING
inequality (first load-bearing use: `omega` inside `bal_gridcore`,
`DeTurckRemainderPrincipalArmOpNorm.lean:7188-7200`), not an embedding
threshold — the protected embedding is gate-free with window `n/2+2 = 3
= H²` in dim 3.  L4 (`DeTurckRemainderRealizeBallUniformSplit.lean:204`)
is the entire mathematical content; L0-L3 are gate-free bookkeeping in
gated signatures.  A large gate-free dim-3 low-order layer exists to
mirror (`appCc_h2_h4_h2`, `principal_arm_h4_h2`, `hs2_opBound_at_two`'s
own proof).  MISSING = only the k-indexed ladder with k-uniform
`Cδ₀ < 1` (sub-brick E0b, the true wall); first sub-brick E0 (k = 0
rung, pure assembly of two existing halves) is READY once (S1₂) lands.
CALIBRATION CORRECTION to F1's heuristic: only 11/28 vestigial
candidates carry the linter marker; 17 are consumed silently by
`omega`/`linarith`, and `bal_gridcore` is genuinely load-bearing —
"binder never named" is NOT evidence of vestigiality, and the sweep
would NOT shrink F6's gated surface (dropped as a work item).

FRONT 3 SIDE: front 3 = finishing `UnifClassBounds`' own design.  Six
plain reals govern the whole solve; horizon monotone+positive in them.
(A) class-uniform producers PROVED for `D` (`nZeroC` ← `unifKsupLeOne`)
and `P` (`unifRealizeRad`; the "E4 not landed" doc line is stale —
`fibreMorrey_unif_base` exists: NINTH overcount).  (B) = the
constant-exposed-sibling sweep (brick G3, bulk, no new mathematics).
(C) = exactly ONE genuinely individual constant: `‖staticForce g₀ g₀ 2‖`
inside `lowregFloorHorizon` — see the USER DECISION below.  Weyl is OFF
the endpoint path (TENTH phantom; measured by import closure; No. 97
item 2 corrected above; policy = carry, never thread).  Two more
phantoms killed: (N) has no "S family" in its statement, and
`short_time_joint` (`ShortTimeExistence.lean:72`) is ALREADY a
sorry-free assembly of (N)'s three conjuncts, background-parametric,
with the DeTurck→Ricci conjugation horizon-preserving.  First front-3
brick G1 (`refold_aff_bg` two-metric widening, no call-site changes)
is ready; G2 must wait for the front-2 lane to release its files and
cite declarations by NAME (line numbers moved).

USER DECISION SURFACED (blocking only the floor-horizon item of front
3): bounding `‖staticForce g₀ g₀ 2‖` class-uniformly needs metric jets
to order 4, exceeding (N)'s stated budget `∀ a ≤ 3`
(`ExtendViaUniqueness.lean:85`).  Options: (a) widen (N)'s hypothesis
to `a ≤ 4` (consumer side must then produce chart-C⁴ from the Shi tail
— feasibility to check on the `ricci_flow_interior_restart` producers);
(b) re-derive the floor horizon at one order lower (design change in
the `Kf` chain); (c) carry a fourth-jet hypothesis as an explicit named
input of the uniform statement only.  G1/G3 proceed under any option.

Honest accounting: (N) stated, proof 0%.  Front 2 ~65% (F2-F5 in
flight); machinery ~88%.  Whole HCG compactness: low single digits.

---

## No. 99 — EXECUTOR REPORT, front 2, bricks F2–F5 (2026-08-03)

PLAN: `ShortTime/FORCEJETMASS_PLAN.md` §6.  RESULT: all four bricks GREEN.

WHAT CHANGED MATHEMATICALLY.  Front 2's forcing package used to rest on a single
composite `sorry`, `lowreg_forceJetMass`, which asserted *all-order interior-time
smoothing* of the `a = 2` trajectory read on its own forcing coordinates, plus an
a-priori realizability radius.  That statement mixed time regularity, spatial mass
and a ball bound, and nothing in the tree spoke to it at `a = 2`.  It is now
**proved**.  The one thing left unproved is a purely **spatial**, time-derivative-free
a-priori estimate, stated as `lowreg_spatialMass` in the same file:

  for every real σ there is Cσ with, for all t ∈ [0,T],
    ∑'ᵢ w_i^σ · (perModeConv λᵢ (timeModeCoeff fHi i) t)² ≤ Cσ,

for the low-lane trajectory pinned by the frozen-split identity `hfix`.  This is,
verbatim, the `hspatial` hypothesis that the supercritical driver
`deTurckForcing_finiteOrderSmoothDriverSymm` already consumes; only the Sobolev order
differs.  So the remaining obligation is no longer "invent a bootstrap at `a = 2`" but
"run the existing Galerkin energy ladder at base order 2".

HOW IT WAS DONE.  The supercritical forcing bootstrap has four stages, three of which
are order-generic (recon, plan §2).  The one order-gated stage is the identification
of the completed Nemytskii `deTurckSobolevNHa2` with its smooth core on the
realizability ball, and that operator does not exist at `a = 2`.  It was replaced by a
new pointwise state-level bridge proved from the certificates that the widened
`IsRealizedTwo` re-exports:

  (liftHiN … (smoothCcToTensorHs g 4 S)).coeff i
     = (deTurckSmoothN g g 2 (symmS g S) …).coeff i     for ‖S‖_{H²} ≤ R,

via `hiN_incl → lowreg_N_affine → lowRegN_on_smooth → smoothN_wd`.  With that in hand
the rung, the induction on k, and the a.e.-agreement diagonal transplant with no new
mathematics, and — because the low lane's state ball is a hypothesis on all of [0,T]
rather than something one has to reach by waiting — **both horizon shrinks of the
supercritical template were deleted rather than transplanted**.  The realizability
radius is then read off the σ = 4, j = 0 majorant of the resulting all-order control.

A second structural finding: the low lane's nonlinearity carries `symmS`, so it is the
*symmetrized* supercritical tower that transplants, not the raw one.  That tower's
`symmS` coefficient-transport machinery (block-diagonal in the eigenvalue blocks, one
Weyl-shifted order paid to Cauchy–Schwarz) already exists and is order-generic; five of
its declarations were promoted out of `private` and reused unchanged.  No Bessel or
Weyl majorant was re-derived.

CORRECTION TO THE PLAN.  §6's F2 row said `force_hi_smooth` could be reused directly.
It cannot: that theorem's forcing hypothesis is the low `lowRegN`-shaped identity at
`H¹`, while `IsRealizedTwo` exports the frozen-split identity.  Bridging the two IS the
`hiN_incl → lowreg_N_affine` chain, i.e. the plan's own fallback was the real route.

WHERE IT NOW STANDS, HONESTLY.  `(N)` (`Evolution/ExtendViaUniqueness.lean:80`, sorry
at `:98`) is unchanged at **0 %** — stated, not proved; this pass moved none of its
mathematics.  `lowreg_spatialMass` itself is **0 %** — stated, not proved.  What moved
is the wiring above it, which was 0 % and is now complete: front 2's forcing package
has exactly one leaf, and that leaf is a classical parabolic energy estimate rather
than a self-referential regularity claim.  Front 2 overall ~70 % (was ~65 %); the gain
is wiring, not analysis.  Whole HCG compactness project: low single digits, unchanged.

FILES TOUCHED.  `ShortTime/LowRegAllOrderJet.lean` (new: `liftN_smoothN_coeff`,
`lowreg_forceJetStep`, `lowreg_forceDriver`, `carrier_coeff_pmConv`,
`lowreg_spatialMass`; `lowreg_forceJetMass` widened and proved; `lowreg_allOrderJet`
call site updated and de-duplicated).  `HeatSemigroup/ForcingCoordinateTimeRegularity.lean`
(five `private` removed, docstrings added, stale POSIT prose fixed; no statement
changed).  Notes: `LowRegAllOrderJet.md`, `ForcingCoordinateTimeRegularity.md` (new),
`FORCEJETMASS_PLAN.md` §11.  Sorry census over the edited files: exactly one.

NEXT DISPATCHABLE BRICK: F6 — prove `lowreg_spatialMass`.  Its statement is frozen by
what `lowreg_forceDriver` consumes, so it can be attacked in isolation.  Verify plan
§7.3 first: the `a = 2` Galerkin forcing has to be built directly from
`deTurckSmoothN g g (2+k)` on the finite eigen-combination space, because the retracted
completed `deTurckSobolevNHa2Symm` does not exist at that order.  If that construction
fails, F6's shape changes and the planner should be consulted before proceeding.

## Planner update No. 100 (2026-08-03) - FRONT 2 WIRING COMPLETE; FRONTIER FROZEN AS lowreg_spatialMass

Milestone marker for the F2-F5 landing (executor report above).  The
composite leaf `lowreg_forceJetMass` is PROVED; front 2's single `sorry`
is now `lowreg_spatialMass` (S1₂) in `LowRegAllOrderJet.lean` (cite by
name — lines move): for every real σ a constant `Cσ` bounding
`∑'ᵢ wᵢ^σ · (perModeConv λᵢ (timeModeCoeff fHi i) t)²` uniformly on
`[0,T]`, for the trajectory pinned by the frozen-split fixed point —
VERBATIM the `hspatial` slot of the supercritical driver, so F6 attacks
it in isolation with its statement frozen.

Key facts from the landing: both horizon shrinks were DELETED (the low
lane's ball is a global hypothesis, not a target); the SYMMETRIZED
supercritical tower is what transplants (five `symmS`-transport
promotions in `ForcingCoordinateTimeRegularity.lean`, zero
re-derivation); plan correction — `force_hi_smooth` could NOT be reused
directly (its forcing hypothesis is the `lowRegN` shape; the
`hiN_incl → lowreg_N_affine` fallback chain was the actual route).
Sorry census across all edited files: exactly one.

Pipeline: E0 (k = 0 dissipation rung, IN FLIGHT) → G1 (`refold_aff_bg`,
front 3) → F6 sub-bricks per `F6_ESTIMATE_RECON.md`
(E0a / E0b = the k-ladder wall / E0c / E1-E5) ∥ G3 (constant-exposed
sweep).  The No. 99 USER DECISION (jet budget vs floor horizon) remains
open; planner default = try option (b) (floor one order lower) first.

Honest accounting: (N) stated, proof 0%; `lowreg_spatialMass` stated,
proof 0%.  Front 2 ~70% (all wiring; zero analysis of the leaf yet).
Machinery ~88-89%.  Whole HCG compactness: low single digits.

## Executor report No. 101 (2026-08-03) - E0 (k = 0 DISSIPATION RUNG) GREEN

**GREEN, sorry-free, no `maxHeartbeats` bump.**
New file `Analysis/Spectral/Intrinsic/DeTurck/LowRegDissipRung.lean` (265
lines, note `LowRegDissipRung.md`); one public theorem `n_diff_h1_rung`
(`:76`) plus one private order-generic helper `jetSq_le_hs` (`:48`).
Focused check clean (zero warnings) and one targeted module build clean.
No existing file was edited.

Proved, at `a = 2`, `k = 0`, dim-3-explicit, gate-free, same-background
(`g_bg = g₀`), all norms `‖ccTensorToHs g₀ 2 (σ : ℝ) ·‖`:

```
∀ R₀, ∃ ρ Cδ₀ C₀, 0 < ρ ∧ 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ 0 ≤ C₀ ∧
  ∀ T symmetric, δ ≤ 1/3 + the two gFibreOpBound certificates,
    ‖T‖_{H²} ≤ ρ → ‖T‖_{H³} ≤ R₀ →
      ‖N T − N 0‖_{H¹} ≤ Cδ₀‖T‖_{H³} + C₀‖T‖_{H²}
```

i.e. exactly L4's shape `‖N T − N 0‖_{H^{a+k−1}} ≤ Cδ₀‖T‖_{H^{a+k+1}} +
Crem k ‖T‖_{H^{a+k}}` at `a = 2, k = 0`.  `Cδ₀ = Capp·Cc2·ρ` with
`ρ = min ρ₂ (1/(2(Capp·Cc2+1)))` — the contraction is bought purely by
shrinking the `H²` ball, which is the low lane's own `hreal'` radius.
`C₀` depends on `R₀` only.

**Route correction to the recon.**  `F6_ESTIMATE_RECON.md` §5.2 named
`principal_arm_h2` + `appCc_h2_h3_h1` as the two halves.  They do not
assemble: subtracting `deTurckPrincipalCometricArm` leaves a third arm
`a₂ T − Arm T` with no low-order producer.  What assembles is the
canonical zero-based split itself — `lowData_split` (identity),
`c2_h2_small` (top-arm coefficient small pointwise AND in `H²` jet),
`appCc_h2_h3_h1` (top arm `H³→H¹`), `lowData_a1_coeff` + `a1_h2_h1`
(lower arm `H²→H¹`), `hsJet_le`/`hs_le_jet` (jet↔spectral).
`remainder_diag_h2` is the wrong producer here (its `a₁` clause is `H²`
in terms of `‖T‖_{H³}`).  Recon §5 updated in place.

**Early-signal verdict on the k-ladder (the reason E0 was scheduled
first): the decomposition DOES generalize; the k-uniform constant does
not come for free, but the ingredient that buys it already exists.**
`lowData_split`'s identity `N T − N 0 = a₂ T + a₁ T` carries no order at
all, so every rung is just "apply an `appCc` estimate at the shifted
pair" — no new algebra.  The `k = 0` smallness, however, rides on
`c2_h2_small`'s **jet** clause, which is small only because two
derivatives of `C2` cost two derivatives of `T` and `‖T‖_{H²} ≤ ρ`; at
rung `k` the same route wants the `H^{k+2}` jet of `C2`, costing
`‖T‖_{H^{k+2}} ≤ R₀` — bounded, not small.  BUT `lowData_split`'s second
clause caps the **pointwise** norm of `C2` by `κ·δ/(1−δ)²` with `κ` free
of `T`, `δ` and order — a genuinely `k`-free small quantity.  So recon
§5.3 clause 1 is NOT established; the degradation is forced only by the
current shape of the `appCc` family, every member of which takes a single
envelope for both the pointwise and the jet norm.

**E0b restated (next brick).**  Not "induct on k" but: add the
split-envelope `appCc` estimate at the `Tensor/Estimates/` layer,
`‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k (‖Φ‖_{C⁰}‖U‖_{H^{k+3}} +
‖Φ‖_{H^{k+1}}‖U‖_{H^{k+2}})`, pairing each coefficient norm with its own
data order (the only two-constant member today, `appCc_c1_h2_h1`, *adds*
the constants).  Second sub-brick: the `k`-generic analogue of
`c2_h2_small`'s jet clause.  This is a normal estimate gap per §5.3, not
a route obstruction.

**Durable Lean lesson (in `LowRegDissipRung.md`).**  Any consumer of the
low-base coefficient bundle must make `lowBaseData …` opaque immediately
— wrap the producers in one
`obtain ⟨A, …⟩ : ∃ A : LowBaseActionData g₀, …`.  Keeping it `set`-bound
(hence unfoldable) made `nlinarith`/`calc` compare atoms containing the
full path-integral witness and blow the 200k heartbeat budget at
`isDefEq`/`whnf` in three places; with `A` opaque the file checks in 20 s
with no heartbeat bump.

Honest accounting, unchanged where not touched: (N) stated, proof 0%;
`lowreg_spatialMass` stated, proof 0%.  F6 estimate side: E0 done, which
is roughly 10-15% of the estimate half (E0b is the wall, E0a/E0c/E1-E5
remain); F6 as a whole ~5%.  Front 2 ~70%.  Machinery ~89%.  Whole HCG
compactness: low single digits.

---

## №99 — E0b (front 2 / F6 estimate side): the split-envelope `appCc`
## estimate, GREEN

New file `Analysis/Spectral/Tensor/Estimates/AppCcSplitEnvelope.lean`
(377 lines; note `AppCcSplitEnvelope.md`).  Focused check clean, one
targeted module build clean, `#print axioms` on both public theorems
gives only `propext, Classical.choice, Quot.sound`.  No `sorry`, no
`maxHeartbeats` bump, no `set_option` anywhere in the file.

**`appCc_split_env` (`:110`) — order-generic, dimension-free, gate-free.**
For every `k`, with `A` a pointwise fibre bound on `Φ`, `B` an `L²` jet
bound on `Φ` through order `k+1`, and `Λ` a pointwise fibre bound on
`∇²U`,

  `‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k · (A · ‖U‖_{H^{k+3}} + B · Λ)`,  `C : ℕ → ℝ`.

This is the pairing №98/recon §5.1a asked for and that no existing member
of the family has: the coefficient's **C⁰** factor multiplies the **top**
data order, the coefficient's **jet** factor does not.  (`appCc_h2_h3_h1`,
`appCc_h2_h4_h2`, `appCc_h2_h2_h2` all take one envelope for both;
`appCc_c1_h2_h1` is the only two-constant member and it *adds* them.)

**`appCc_split_hs` (`:276`) — the one demonstration corollary.**  In
dim 3 this converts `Λ` into a spectral norm and lands the literal ladder
shape `C·(A‖U‖_{H^{m+3}} + B‖U‖_{H^{m+2}})` at the rungs `m = k + 2`.

**A pre-existing Leibniz split was FOUND, not built — wall #4 to dissolve
on grep.**  `appCc_iteratedCovGrad_diagonalProductGrid_le`
(`OperatorFieldFibreNormJet.lean:885`, an `appCc` wrapper on an induction
over the jet order) is exactly the order-generic pointwise Leibniz split,
and `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
(`RemainderCoeffPerOrderJetEnvelopes.lean:862`) is its integrated
Gagliardo–Nirenberg companion.  **No interpolation/GN inequality was
missing**, so the E0b stop-condition never triggered: the whole content
of the split is reading the two-arm bound asymmetrically (coefficient in
the `L^∞` slot on one arm, data in it on the other).
`MoserTameProduct.lean:110` was rejected — it wants `Cᵏ` coefficient
hypotheses and its file carries a real `sorry`.

**Correction to the E0b target as stated in №98/§5.1a: it is achievable
only for `m ≥ 2`, and at `m = 0` the literal statement is FALSE.**  The
grid cell `∇Φ·∇²U` is `L^{3/2}` at best when `Φ ∈ H¹∩L^∞`, `U ∈ H³` in
dim 3 — which is precisely why the existing `m = 0` member
`appCc_h2_h3_h1` demands the `H²` jet of `Φ`, not the `H¹` jet.  Rungs
`m = 0, 1` are already covered by `appCc_h2_h3_h1` / `appCc_h2_h4_h2`, so
the ladder is complete at every rung.  Window arithmetic: the gate-free
sharp `C⁰` window is `finrank/2 + 2 = 3` in dim 3, so `‖∇²U‖_{C⁰} ≲
‖U‖_{H⁴}` — two orders, hence `m ≥ 2`.  The `Λ`-form is kept as the
public interface so a consumer with a bootstrap `C⁰` bound on `∇²U` can
use it at any `m`.

**Honest k-growth (this is the load-bearing negative).**  `C k` is NOT
`k`-uniform and nothing in the proof suggests it can be made so: it sums
`√(appCcGdiag j · Cg j)` over `j < k+2` and
`appCcGdiag j = (2(n+1))^j`, so `C k ≳ (2(n+1))^{(k+1)/2}`.  The C⁰
pairing carries no growth *beyond* `C k`, but `C k` itself is
exponential.  So E0b supplies the **shape** that lets `lowData_split`'s
`k`-free pointwise cap on `C2` multiply the top order — the ingredient
№98 identified — but **not** the `k`-uniform `Cδ₀` that
`galerkin_energy_uniform_bound_perScale` needs.  Recon §5.3 clause 1 is
still open in both directions: not established, not refuted.  Closing it
needs a grid weight better than `appCcGdiag` (sharper Leibniz bookkeeping
at the `OperatorFieldFibreNormJet` layer) or a `k`-uniform
reformulation.  **This is now the sharpest open question on F6.**

**Still open, unchanged:** the second E0b sub-brick — the `k`-generic
analogue of `c2_h2_small`'s jet clause (an `H^{m+1}`-jet envelope for the
low-base coefficient `C2`; `m = 0` is `c2_h2_small`,
`DeTurckRemainderLowBaseAction.lean:13268`).  Nothing produces `B` yet.

**Lean lessons (full list in `AppCcSplitEnvelope.md`).**
`Finset.range_subset` in this Mathlib is `range n ⊆ s ↔ ∀ x < n, x ∈ s` —
the `n ≤ m` lemma is `Finset.range_subset_range`; the mis-pick surfaces
as a bogus `omega` failure at an unrelated line.  `calc` continuation
lines must start at the column of the first step's first token, or the
parser folds them into the previous justification term.  Stating spectral
orders as `((k + 3 : ℕ) : ℝ)` (never `(k + 3 : ℝ)`) makes every
`hsJet_le`/`hs_le_jet` application match with zero `push_cast` repair.

Honest accounting, unchanged where not touched: (N) stated, proof 0%;
`lowreg_spatialMass` stated, proof 0%.  F6 estimate side: E0 + E0b done,
≈25-30% of the estimate half (E0a/E0c/E1–E5 remain, and the `Cδ₀`
`k`-uniformity question above may still force a rethink of E0a); F6 as a
whole ~8%.  Front 2 ~70%.  Machinery ~90%.  Whole HCG compactness: low
single digits.

## №101 — front 3 / brick G1: the refold affine packet is now two-metric,
## GREEN, with the diagonal preserved byte-for-byte

`LowRegBgA1Refold.lean` (533 lines).  Focused check clean; targeted module
build clean; no `sorry`, no `set_option`, no new import.  96 inserted /
26 deleted lines, one file touched.

**What moved.**  The DeTurck background was hard-wired to the state metric
in exactly one place on this path: `oneCore g` was literally
`(lowCoreDataBg g g …).C1` packed as a `LowBaseActionData g`, and
`refold_aff` inherited the diagonal from it.  The order-one *engine*
`c1_bg_pack` (`LowRegBgC1Time.lean:763`) was already two-metric and the
order-zero engine `c0_pack` (`LowRegBgC0Time.lean:322`) is genuinely
background-free, so the widening is a re-parametrisation of the packet
statement, not new mathematics — as the plan predicted.

* `oneCoreBg g gB … : LowBaseActionData g` (`:56`) — `C1 :=
  (lowCoreDataBg g gB …).C1`, `C0 = C2 = 0`.
* `oneCore g … := oneCoreBg g g …` (`:71`) — same signature, same type,
  now a thin diagonal wrapper.  Its only unfolding site in the whole tree
  is `refoldLo_core`'s `simp only` (`:177`), which gained `oneCoreBg`;
  every downstream mention of `oneCore` is a *statement* occurrence, none
  unfolds it.
* `refold_aff_bg hDim g gB` (`:345`) — the affine packet
  `∃ ρ₀ > 0, ∀ ρ ≤ ρ₀ …, ∃ Z L FHi FLo` with continuity, the two
  smooth-core formulas now reading `c0CoreData g … .a1* + oneCoreBg g gB
  … .a1*`, the two affine bounds `‖F x‖ ≤ Z + L‖x‖`, and the u-free
  inclusion square.  Only the *state* metric `g` indexes the Sobolev
  scales `H³/H²/H¹`; `gB` enters solely through the order-one
  coefficient.  Proof = the old body verbatim with `c1_bg_pack hDim g gB`
  in the second `obtain`; the two `rfl`s that convert `c1_bg_pack`'s
  anonymous `{C0 := 0, C1 := …, C2 := 0}` into the named bundle still
  close, since `oneCoreBg` *is* that structure.
* `refold_aff hDim g` (`:488`) — kept as a theorem whose statement is
  **byte-identical to its previous text** (verified by diff against
  `HEAD`), proved term-mode by `refold_aff_bg hDim g g`.  This is the
  reason for the shape choice: making `refold_aff` a definitional
  abbreviation would have rewritten `oneCore` to `oneCoreBg g g` inside
  the packet's conclusion, and the seven downstream files that carry that
  conclusion as a *hypothesis* would then have had to be edited in
  lock-step.  A diagonal instance theorem costs one `exact` and zero
  churn.

**Diagonal-preservation gate — passed with zero edits downstream.**
`LowRegLiftAffine.lean` (the only direct importer), `LowRegLiftHfLo.lean`
(the named acceptance file) and `LowRegApplyTwo.lean` (the actual
`refold_aff` call site, `:744`) all re-elaborate green against the
refreshed `.olean`, unmodified.  Targeted builds of `LowRegLiftAffine`,
`LowRegLiftHfLo` and `LowRegForceHi` (the other `oneCore` consumer) are
clean.  `LowRegAllOrderJet.lean` mentions `oneCore` in statements only and
is untouched by the type-level change.

**What G1 did *not* buy.**  `refold_aff_bg` is now available at `gB ≠ g`,
but every consumer still calls the diagonal.  The `g g` occurrences that
matter for the class layer are downstream — `lowreg_solve_two`'s
`lowRegN_outer … g g` (`LowRegApplyTwo.lean:746`) and `lowreg_bounds_exist
… g g` (`:809`) — and are brick G2.  Nothing in G1 touched a constant.

**No stop condition fired.**  `c1_bg_pack`'s two-metric statement covers
the refold sum at `gB ≠ g` exactly: its `hreal` realization hypothesis is
about `g` alone (`SmoothCcTensor g 0 2`, `gFibreOpBound g`), so the two
lanes share a hypothesis bundle at any background, and the sum/affine
addition arguments never see `gB`.  The plan's failure signal — a
`rfl`-level identity in the `a1Lo_congr` layer that secretly needs `g g` —
did not appear; `a1Lo_core_any` and `a1_comm_any` are already background
agnostic.  G2's "routine but wide" cost estimate stands.

Honest accounting: (N) stated, proof 0% — unchanged, G1 moved no
mathematics.  Front 3 ~28% (was ~25%: G1 of G1–G6 done, and it was the
smallest brick).  Machinery ~90%.  Whole HCG compactness: low single
digits.

## Planner update No. 102 (2026-08-03) - L4 AUTOPSY VERDICT (β): TOP ORDER NEVER MEETS THE GRID; LEAF → c2_jet_tower

Integrating the k-uniformity autopsy (`L4_UNIFORMITY_AUTOPSY.md`) with
the E0b and G1 landings (executor reports above):

MECHANISM (stronger than hypothesized): L4's k-uniform `Cδ₀` is two
SCALARS fixed outside `∀ k`; the k-induction is a COMMUTATOR induction
against resolvent powers (`oneMinusConnLapSmoothIter`), not a Leibniz
expansion — every rung's cost is added to the LOWER-order constant
(`ClowerFn j = Mbase + ∑_{i<j} CEcomm i`), the top scalar is identical
at every rung, and the Leibniz grid touches the top-order path only at
`j = 0` where `appCcGdiag 0 = 1`.  Four gate-free, k-free,
absolute-constant ingredients carry it (pointwise fibre cap;
`riemannianFiberNormSq_compRS_le_mul` with constant exactly 1; Gårding
constant 1; spectral shift constant 1).  E0b's exponential `C k` is
therefore a WRONG-ROUTE artifact, not an obstruction — its honest
correction is what triggered this autopsy, and its split lemma stays
valid for lower-order bookkeeping.  Recon §5.3 clause 1 is REFUTED for
the mechanism that matters; route-error candidate (γ) is dead.

E0b′ ALREADY EXISTS: `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_
family_le` (`ConnLapCommutatorCoefficientTame.lean:1323`),
coefficient-abstract and order-generic, with the low-base arm literally
the same object (`LowBaseActionData.a2 = appCc … C2 ∘ ∇²`) and
`lowData_split`'s k-free pointwise cap as its `εC`.  At a = 2 it needs
only DE-GATING (derivative-budget `omega` re-derivations at fixed dim-3
orders).  The ONE genuinely new estimate left: the all-order jet tower
of `A.C2` UNDER THE PATH INTEGRALS (the supercritical analogue was
algebraic/Neumann) — frozen as the next leaf `c2_jet_tower` by brick
E0a′ (in flight: de-gate + assemble the a=2 ladder with the k-free top
constant, leaf as the single sorry).

Also banked: G1 (`refold_aff_bg`, front 3, zero downstream churn,
diagonal preserved as an INSTANCE with byte-identical `refold_aff`
statement).  Ledger hygiene note: executor reports above self-numbered
inconsistently (№99/№101 twice); planner numbering (this line of
entries) is canonical.

Honest accounting: (N) stated, proof 0%; `lowreg_spatialMass` stated,
proof 0%.  F6 ≈ de-gate + ladder assembly + `c2_jet_tower` + Galerkin
plumbing (E1′).  Front 2 ~70%; front 3 ~28%; machinery ~90%.  Whole
HCG compactness: low single digits.

---

## EXECUTOR REPORT — brick E0a′ (ladder assembly), 2026-08-03

GREEN, with the one planned frontier.  New file
`Analysis/Spectral/Intrinsic/DeTurck/LowRegLadderRung.lean` (254 lines; note
`LowRegLadderRung.md`).  Focused check clean; one targeted module build clean;
sorry census in the file = ONE.

LANDED — the k-uniform ladder for the low-base second-order arm,
`a2_ladder` (`:192`), gated `finrank ℝ E + 5 ≤ a`, ball `‖T‖_{H^{a+2}} ≤ R₀`,
`0 ≤ δ ≤ 1/3`, dim 3:

    ‖(lowBaseData g₀ g₀ T …).a2 T‖_{H^m}
        ≤ κ·(δ/(1−δ)²)·‖T‖_{H^{m+2}} + Clower m·‖T‖_{H^{m+1}}    for EVERY m

with `κ` realized as `lowData_split`'s own cap constant.  The top constant
carries NO `m`, so a single smallness threshold on `δ` contracts every rung
at once — this is the k-uniformity recon §5.3 clause 1 left open, and it is
now refuted in Lean, not just on paper.

DE-GATING, partial and axiom-clean: `appCc_cap_hs_le` (`:75`, no sorry,
`propext/Classical.choice/Quot.sound` only) re-derives the `m`-form of the
engine `…Hs_family_le` (`ConnLapCommutatorCoefficientTame.lean:1323`) by
reading its resolvent family at `p = 0` (`oneMinusConnLapSmoothIter_zero` is
`rfl`, so the side condition is `⟨0, rfl⟩`) and closing with the constant-one
shift `smoothCcToTensorHs_rawTensorConnLapSmooth_le`.  Gate `n+5 ≤ a` instead
of the shipped wrapper's `2n+10 ≤ a` (`…ArmOpNorm.lean:5129`), whose `_le_zero`
half never uses its gate and whose `_le_succ` half forwards it via one
`by omega`; top constant `εC` instead of `√(n³)·εC`.  In dim 3 the a-priori
ball drops `H^{18} → H^{10}`.  Obligations re-derived: ONE (that `by omega`).

CORRECTION TO THE AUTOPSY — the `a = 2` de-gate does NOT close, and this
revises §3.3(c) and §5 risk 2 (both amended in the autopsy file).  At `a = 2`
the leaf obligation is not wide bookkeeping, it is arithmetically FALSE: in
`master_appCc_jet_le_sharp` (`:469`) region one needs
`t + (w−1) + dc ≤ a + 2`, i.e. `4 + 2 + 3 = 9 ≤ a + 2` in dim 3 at the
`(dc,dd) = (3,2)` call site, so `a ≥ 7`; at `a = 2` it reads `9 ≤ 4`.
`hs_extreme_interp` saves region two (`dc+(w−1)+dd ≤ a+5` is `7 ≤ 7` at
`a = 2`) but not region one, which needs a NUMERIC coefficient sup bound with
no `f γ` to trade against.  Parameterizing the leaf's split threshold `t`
bottoms out at `a = 3` (ball `H⁵`), no lower — and that edits a `private`
statement inside a supercritical file, so it is a separate brick, not this one.
The six gated call sites from `:969` (2 × `master_…` at `(3,2)`,`(2,3)`;
4 × `appCc_term_…` at `(1,2)`,`(1,2)`,`(0,3)`,`(0,3)`) were therefore NOT
re-derived; they sit below the engine's public interface.

FROZEN LEAF: `c2_jet_tower` (`:146`, sorry at `:167`) — hypothesis (b) of the
engine for the low-base coefficient,
`∀ i, ‖∇ⁱ (lowBaseData g g T …).C2‖² ≤ Kc i (1 + ∑_{j<i+2} ‖∇ʲT‖²)`, uniform
in `δ ≤ 1/3` and over the `H^{a+2}` ball.  `i = 0` is `c2_h2_small`'s second
clause.  Route: differentiate `rhsRefoldTopInt + selfTopInt − deTurckPhiMetTotal`
under the path integral and bound the integrand's per-order jets uniformly in
the path parameter; the supercritical analogue is algebraic/Neumann and is NOT
a template (autopsy risk 1 stands).  This is a real estimate brick, not a
routine local proof.

## Planner update No. 103 (2026-08-03) - a2_ladder LANDED (k-UNIFORM IN LEAN); HANDOVER DESIGN PINNED

Milestone for E0a′ (executor report above): `a2_ladder`
(`DeTurck/LowRegLadderRung.lean:192`) proves the k-uniform rung bound
`‖A.a2 T‖_{H^m} ≤ κ·(δ/(1−δ)²)·‖T‖_{H^{m+2}} + Clower m·‖T‖_{H^{m+1}}`
with a TOP CONSTANT FREE OF m — recon §5.3 clause 1 is refuted IN LEAN;
the feared k-uniformity wall of F6 is closed.  De-gating cost ONE
re-derivation (`appCc_cap_hs_le`, gate `n+5 ≤ a`, top constant improved
`√(n³)·εC → εC`).  Single frontier left in the file: `c2_jet_tower`.

AUTOPSY CORRECTION (already recorded in both docs): at the literal
`a = 2` the leaf's budget obligation is ARITHMETICALLY FALSE (`9 ≤ 4`);
parameterizing the split threshold `t` closes it iff `a ≥ 3` (ball
`H⁵`) — a separate brick editing one `private` supercritical statement.
Autopsy §3.3 clause (c) was wrong; caught by implementation, no route
consumed.

HANDOVER DESIGN (planner, for E1′): the Galerkin per-scale induction
does not need the ladder at `a = 2` — rungs `m = 0, 1` are covered by
the FIXED-order members (`appCc_h2_h3_h1` ball `H³`, `appCc_h2_h4_h2`
ball `H⁴`, E0's `n_diff_h1_rung`), whose dissipation steps CONTROL
`H⁵`; the `a ≥ 3` ladder (ball `H⁵`) takes over from `m ≥ 2`.  The
threshold brick lands the `a ≥ 3` instance; the handover composition is
E1′'s first obligation.

Honest accounting, unchanged where not touched: (N) stated, proof 0%;
`lowreg_spatialMass` stated, proof 0%.  F6's estimate side is now
`c2_jet_tower` + (optional) the `a = 3` ball-order brick + E1′ Galerkin
plumbing.  The ladder itself — the part everyone feared — is done.

## EXECUTOR REPORT — brick E0a″ (a ≥ 3 threshold parameterization), 2026-08-03

GREEN.  The optional "`a = 3` ball-order brick" that No. 103 left hanging off
E0a′ is done, so F6's estimate side is now `c2_jet_tower` + E1′ and nothing
else.  Touched two Lean files; sorry census in `LowRegLadderRung.lean` stays
exactly ONE (`c2_jet_tower`), and `ConnLapCommutatorCoefficientTame.lean` stays
sorry-free.  Focused check + targeted build clean on both, and the downstream
supercritical consumer `DeTurckRemainderPrincipalArmOpNorm` rebuilds clean.

THE MATHEMATICS.  The `finrank ℝ E + 5 ≤ a` gate was never an analytic
requirement — it was the shadow of one hard-wired constant.  The Leibniz-grid
leaf `master_appCc_jet_le_sharp`
(`Sobolev/TensorHilbert/ConnLapCommutatorCoefficientTame.lean:475`) splits the
grid index at `t` and treats the two regions completely differently: below `t`
it needs a *numeric* sup bound on the coefficient jets over the a-priori ball
(`t + (w−1) + dc ≤ a + 2`), above `t` it trades through log-convexity and needs
only `(w−1) + dd ≤ t + 4`.  `t` was fixed at `n/2 + 3` — high enough that
region one alone forced `a ≥ n + 5`.  Making `t` a parameter carrying exactly
those two budgets removes `ha` from the leaf entirely: the two hypotheses
discharge all three budget `omega`s (`hbound`, `hβγ`, and the interpolation
side condition `hsum_ok`, the last following from the first two).  Setting
`t := n/2 + 3` recovers the old statement verbatim, so nothing was assumed away.

THE ONE THING E0a′'s ANALYSIS DID NOT SEE.  Its predicted windows were exactly
right — `0 ≤ t ≤ a−3` at `(dc,dd) = (3,2)` and `1 ≤ t ≤ a−2` at `(2,3)`, each
non-empty iff `a ≥ 3`.  But across all six gated call sites the windows are
`0 ≤ t ≤ a−3`, `1 ≤ t ≤ a−2`, `0 ≤ t ≤ a−1` (twice) and `1 ≤ t ≤ a` (twice),
whose **intersection** is `1 ≤ t ≤ a−3` — empty until `a ≥ 4`.  So `a = 3` is
not reachable by picking a better *global* threshold; each site must choose its
own (`n/2 − 1` where `dd = 2`, `n/2` where `dd = 3`).  That per-site freedom is
the entire content of the brick, and it is why parameterizing rather than
retuning was the right move.

RESULT.  `a2_ladder` (`DeTurck/LowRegLadderRung.lean:196`) now reads
`hDim : finrank ℝ E = 3` together with **`ha : 3 ≤ a`**: the a-priori ball drops
`H^{10} → H⁵`, which is exactly the order No. 103's handover design wants (the
fixed-order members cover rungs `m = 0, 1`, the ladder takes over from `m ≥ 2`,
and their dissipation steps control `H⁵`).  The three public theorems of the
engine file now gate on the sharp dimension-general
`max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`; `appCc_cap_hs_le` carries that form and
remains **axiom-clean** (`propext, Classical.choice, Quot.sound`).

THE TOP CONSTANT IS UNTOUCHED, which was the point.  `t` only redistributes
index mass between `S1` and `S2`, and both feed `Cm → CEcomm → ClowerFn`, i.e.
the *lower*-order constant.  The engine's top constant is still exactly `εC`
and `a2_ladder`'s is still `lowData_split`'s cap `K`, with no `m` in either.
Threshold slack was bought with rung-dependent lower-order cost, never by
weakening the `k`-uniformity that E0a′ established.

SCOPE NOTE (deviation from the brick prompt, deliberate).  The prompt asked to
keep the old private statement as a specialized instance.  All six of its call
sites are in-file and all six were edited by this brick, so a retained
specialization would have been dead private code; the house rule against
unnecessary private helpers wins, and the parameterized lemma keeps the old
name.  Faithfulness is recorded instead as the `t := n/2 + 3` remark in
`ConnLapCommutatorCoefficientTame.md`.  Separately, reaching `a = 3` genuinely
required weakening the gate on the three *public* theorems of the engine file —
there is no way to lower `a2_ladder` without it.  That is a pure hypothesis
weakening: the only external consumer
(`DeTurckRemainderPrincipalArmOpNorm.lean:5078`) passes the gate as `(by omega)`
and is byte-unchanged, and the other two have no external consumers at all.  No
duplicate/parallel API was created.

Docs updated: `ConnLapCommutatorCoefficientTame.md` (new same-name note),
`LowRegLadderRung.md`, `F6_ESTIMATE_RECON.md` §5.1c/§5.1d,
`L4_UNIFORMITY_AUTOPSY.md` status block.

Honest accounting, unchanged where not touched: (N) stated, proof 0%;
`lowreg_spatialMass` stated, proof 0%.  F6's estimate side is now
`c2_jet_tower` + E1′ Galerkin plumbing — the ball-order caveat is gone.
`c2_jet_tower` is a real estimate brick (differentiate the `A.C2` path integral
under the integral sign, per-order jets uniform in the path parameter), not a
routine local proof, and it is the only thing between here and an unconditional
ladder.  Whole HCG compactness: still low single digits.

---

## VOLUME FROZEN (2026-08-03)

This file is near the 3000-line cap.  Entries No. 104 onward live in
`UNIF_EXISTENCE_PLAN3.md` (which opens with the state snapshot at this
break).  Do not append here; treat No. 70–103 and their executor reports
as frozen history, same precedent as `UNIF_EXISTENCE_PLAN.md` (No. 1–69).
