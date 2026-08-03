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
