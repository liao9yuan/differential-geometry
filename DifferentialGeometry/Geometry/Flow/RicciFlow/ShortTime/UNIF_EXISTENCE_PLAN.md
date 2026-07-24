# UNIF_EXISTENCE_PLAN — filling black box (N) `ricci_flow_unif_existence`

Planned 2026-07-19 (Fable, planner) on branch `codex/analytic-producers-e87b`
@ `922dbc4ac` (worktree `C:/Users/liao9/.codex/worktrees/e87b/...`).  Executor:
Opus 4.8 session; acceptance loop stays with the planner/user.

## Target

The single `sorry` of
`Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean`, theorem
`ricci_flow_unif_existence` (black box (N)): for fixed `gBase`, for every
`Λ ≥ 1` a UNIFORM existence time `τ₀(gBase, Λ, S) > 0` such that every `g₀`
that is `Λ`-comparable to `gBase` with `MetricCovDerivOrderBoundOn` jets
`a ≤ 3` bounded by `Λ` flows on `[0, τ₀)` with the stated regularity fields.
This is the last `sorryAx` source of the `extends_of_rmBounded` route
(brick board in `ExtendViaUniqueness.md`; (A)/V and Y wiring are DONE).

## Mathematical position (verified before planning)

The PER-DATUM short-time existence is already PROVED sorry-free:
`deturck_ricci_flow_parabolic_short_time_existence`
(`ShortTime/DeTurckInitialDataExistence.lean`) assembles the quasilinear
engine `quasilinear_strictlyParabolic_2ndOrder_shortTimeExistence`
(`ShortTime/QuasilinearAbstractShortTimeExistence.lean`, sorry-free) with
concrete DeTurck producers (Sobolev scale `N₀ := 4·finrank + 10`,
`deTurckSobolevNHa2Symm`, parabolicity at `g₀`, Lipschitz + forcing
bootstrap).  (N)'s ONLY new content is UNIFORMITY of the time over the
`Λ`-class — i.e. uniform convergence of the engine's fixed-point iteration
with constants depending only on class data.

## Route decision (Stage 0 ratifies; do not skip)

**R1 (primary): quantitative uniformization of the existing engine.**
The engine's `T` arises from a maximal-regularity fixed point; its inputs
are (e1) the strict-parabolicity constant at `g₀`, (e2) the order-`N₀`
Sobolev data norm of `g₀`, (e3) the RHS Lipschitz/quasilinearity constants
near `g₀`, (e4) the forcing-bootstrap constants.  Each is to be bounded by
`F(gBase, Λ, S)` on the class.  **Known caveat (statement risk):** (e2)
needs `g₀`-jets of order ≈ `N₀ + 2`, while (N) currently supplies `a ≤ 3`.
Expected resolution: raise (N)'s hypothesis to `a ≤ A(n)` (A(n) ≈ 4n + 12).
The upstream producers (`metricCovOrderWindow_of_*`, Lemma 3.11 / Shi
`AllTimesBounds` layer) are order-parameterized, so brick-Y's discharge is
expected to lift verbatim; the (A)-from-(N) proof consumes (N) as a box and
is unaffected.  THIS STATEMENT CHANGE REQUIRES EXPLICIT PLANNER/USER
ACCEPTANCE after the Stage-0 audit — do not edit (N) before that.

**R2 (fallback, long lane, do NOT start here):** honest-`C³` low-regularity
Koch–Lamm existence via this branch's Euclidean heat/Duhamel machinery
(`Analysis/Parabolic/Euclidean/`, `heatD2Past_l2` ≈ 45%).  Months of
producer work; stays the branch's separate long game.

## Stages

**Stage 0 — engine-constant audit (NO Lean edits).**
Trace `T` through `QuasilinearAbstractShortTimeExistence` into the
`Analysis/Parabolic/{MaximalRegularity,QuasiLinear,TimeSobolev}` stack.
Deliverable: a table in `ShortTime/UnifClassBounds.md` listing every
`g₀`-dependent quantity the existence time consumes — file, lemma,
constant, and the class datum that must bound it — plus the minimal jet
order `A(n)` for (e2) and a check that Lemma 3.11-side producers exist at
every `a ≤ A(n)`.  STOP and report for acceptance.

**Stage 1 — uniform class-bound producers (new leaf file
`ShortTime/UnifClassBounds.lean`; additive only).**
One lemma per engine input, each stated over
`{g₀ | Λ-comparable ∧ jets ≤ A(n) bounded by Λ}`:
(e1) parabolicity constant from `Λ`-comparability (bilinear coercivity
transfer); (e2) order-`N₀` Sobolev norm from chart jets over the finite
atlas `S` (finite-cover summation; compact `M`); (e3) RHS Lipschitz
constants on the fixed `gBase`-scale ball; (e4) bootstrap constants.
Reuse the existing per-`g₀` producer proofs — the work is threading `Λ`
through them, not new analysis.

**Stage 2 — quantitative engine wrapper (additive; do NOT rewrite the
sorry-free engine).**  A sibling theorem
`quasilinear_..._shortTimeExistence_ge` returning `T ≥ φ(constants)` with
`φ` explicit, by re-running the same fixed-point with the supplied uniform
constants (or threading a lower bound through the existing proof if the
stack already exposes one).

**Stage 3 — (N) assembly.**  Choose the canonical finite atlas `S`; apply
Stage 2 + Stage 1 to produce `τ₀`; the (N) regularity fields are the plain
theorem's fields restricted to `[0, τ₀)`.  If the `a ≤ A(n)` change was
accepted, edit (N)'s statement and lift brick-Y's discharge (small,
coordinated with the Evolution lane; separate report).

## Planner acceptance of the route test (2026-07-22)

The item-(2) route test returned **verdict (a): R1τ FEASIBLE** — both
high–low orientations close with R-independent constants; the forbidden
shapes do not arise (details + provenance in
`Analysis/Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.md`).
**R1τ is hereby RATIFIED as the route.**  Scope finding accepted: the
smooth-core tame lemma is a multi-lemma assembly, not one-lemma; its deepest
generic producer (`CurvatureCoefficientDifferenceJetTower.lean`) is
IN-FLIGHT Codex work (dirty), so assembly against it is deferred.  Next
brick (dispatched with guardrails): in a NEW leaf file of the tame-envelope
layer, sum the per-order
`linearizedRicciArm{0,1}BaseCoeff_..._topSeparated` bounds
(`RemainderCoeffL2JetMoser.lean:1398` etc., all committed-clean) into a
single R-independent data-weighted jet-L2 bound per field — consuming ONLY
committed clean-file lemmas; STOP (do not repair) if the dirty JetTower
file breaks the build or its committed exports have drifted.

## Planner acceptance №2 (2026-07-22, after the summation brick)

Accepted: `ArmBaseCoeffJetL2Summed.lean` (arm0 + arm1 summed top-separated
bounds, R-independent constants, axiom-print-clean; helper
`jetL2_sum_of_perOrder` reusable).  Caveat accepted and recorded: the
authoritative `lake build` of the new module is blocked by a PRE-EXISTING
worktree build-cache inconsistency (missing `.olean.hash` for
`…EigenvectorChartRHSDiffNumeratorWkpNormSharp` in the worktree
`.lake/build` while present in the redirected tree `C:/dgbuild/e87b`);
verification was a direct `lean` typecheck against that redirected olean
tree with the lakefile's correctness options replicated in-file —
ENVIRONMENT REPAIR ITEM for the worktree owner (reconcile the build-dir /
hash split, then re-run the targeted build).  Next dispatched brick: the
remaining ~3 per-field summed bounds (trace-Hessian, connection-difference,
Lie fields; same `jetL2_sum_of_perOrder` pattern, same guardrails).  The
threeArm combination stays DEFERRED until the Codex lane lands
`CurvatureCoefficientDifferenceJetTower` (its decomposition lives in the
frozen `DeTurckRemainderTameLipschitz.lean`).

## Planner acceptance №3 (2026-07-22) — lane parked WAIT-ON-CODEX

Accepted the third executor's finding: the remaining 3 constituent fields
(trace-Hessian, connection-difference, Lie) CANNOT be built from
committed-clean inputs — their only clean per-order producers are
R-DEPENDENT (via `antidiagonalTupleGrid_integral_ballUniform_tameWindow`,
constant ~ `R^{7k}`), and summing them would inject the ruling's forbidden
`C(R₂)`-shape.  The four R-independent `_topSeparated_le` engines they need
exist ONLY in the dirty in-flight `CurvatureCoefficientDifferenceJetTower.lean`
(≈ lines 1823 / 10570 / 11141 / 11695).  The route-test note's claim that
the connDiff/Lie tame-envelope producers were R-independent was WRONG and
has been corrected in both notes.

**Lane state:** everything buildable from committed-clean inputs is DONE
(route ratified R1τ; `jetL2_sum_of_perOrder` engine; arm0+arm1 summed
bounds green/axiom-clean).

**CORRECTION (2026-07-22, planner verification):** the №3 "wait-on-Codex"
call was OVER-CONSERVATIVE.  Verified against HEAD: all FOUR R-independent
`_topSeparated_le` engines are ALREADY COMMITTED
(`CurvatureCoefficientDifferenceJetTower.lean` HEAD:1823/10543/11114/11668);
the file's dirty state is 64 UNRELATED inserted lines (`pureTrace` +
`koszul_l2_succ`, hunks at ~6455/~15078) that do not touch the engines.
What is genuinely missing — and in NOBODY's queue — is the intermediate
layer: per-field `_perOrder_topSeparated` (∃`Hd`, realizedFam,
R-independent) producers for trace-Hessian / connDiff / Lie, mirroring the
arm0/arm1 construction (`RemainderCoeffL2JetMoser.lean:1398/1532`) on top
of the four committed engines.  That layer is OURS TO BUILD NOW (dispatched;
new leaf files only; the only real coupling is that any build compiles the
64 dirty lines — if THEY fail to elaborate, stop and report, that alone is
the wait-on-Codex condition).  The actual asks to the Codex lane shrink to:
(i) commit the 64 lines at convenience (de-dirties the file, unblocks
authoritative builds); (ii) repair the worktree `.lake` hash split vs
`C:/dgbuild/e87b` (outstanding environment item).
Then: 3 summed bounds (~40 lines each, connDiff/Lie at offset `p = 1`) →
data-weighted threeArm decomposition (frozen
`DeTurckRemainderTameLipschitz.lean` assembly) → smooth-core tame lemma
(ruling item 2 proper) → ruling items 3–6.

## Planner acceptance №4 (2026-07-22) — constant-discipline CALIBRATED; roadmap ready

Accepted the fourth executor's verified refinement: the №3 "R-dependent ⇒
forbidden" reasoning was itself the error.  Verified against arm0's own
ACCEPTED L2 generic (`CurvatureCoefficientDifferenceJetTower.lean:14447`):
its lumped low constant `Kc` IS R-dependent — the ruling's stop-signal
discipline protects only the **top-split coefficient `Ktop`** (the factor
multiplying the `‖U−V‖_{a+2}`-type top difference), which the four
committed engines keep `(g₀,hδ₀)`-only.  R in `Kc`-lumped low terms is the
accepted house pattern.  Full verified per-field construction roadmap now
in `Analysis/Sobolev/TensorHilbert/RemainderCoeffTopSeparated.md`
(field→engine map; a cheaper DIRECT-summed route skipping the field-level
`∃Hd` construction; environment recipe).  Two consecutive sessions produced
verification-not-Lean: the brick is at single-session intricacy ceiling, so
scope narrows to ONE FIELD per dispatch.  Next: connDiff DIRECT summed
bound (~180–220 lines, roadmap claims no uncertain step) → Lie (reuses
connDiff) → traceHessian (hardest; three curvature engines).

## Planner acceptance №5 (2026-07-22) — connDiff constituent LANDED

Accepted: `ConnDiffJetL2Summed.lean` (548 lines, three public theorems —
generic per-order, realizedFam per-order, and the summed deliverable
`connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated`), green
via the redirected-olean typecheck, axiom-print-clean.  `Ktop = 2·finrank²·
Kt0` with `Kt0` = the committed engine head (`10·S 0`, `(g₀,hδ₀)`-only); `R`
only in `Kc` — calibrated discipline satisfied, no stop-signal.  New
reusable helper `jetL2_sum_lowShift` (two-offset generalization of
`jetL2_sum_of_perOrder`).  Elaboration trap recorded in the same-name note
(`toSection_sub` folding needs `simp only [...]; abel`, not `rw [←
toSection_add]`).  Constituents now 3-of-5 (arm0/arm1/connDiff).  Next
dispatched: the Lie field (cheap — reuses the connDiff producer via
`kernelField_eq_neg_arm_combination` + a `5·`-triangle assembly), then
traceHessian (hardest; three `(0,4)` curvature engines) as its own
dispatch.

## Planner acceptance №6 (2026-07-22) — Lie constituent LANDED

Accepted: `LieFieldJetL2Summed.lean` (summed + per-order + private bridge
`lie_normSq_le_25`), green/axiom-clean via the redirected-olean typecheck.
`Ktop_Lie = 25 · Ktop_connDiff` — combinatorial `5·`-triangle squared times
the `(g₀,hδ₀)`-only connDiff head; `R` only in `Kc` (house pattern); no
stop-signal.  The private arm-combination stack was copied verbatim with a
provenance comment; the `rfl`-identity reproduction succeeded.  Practical
note for downstream: the `ConnDiffJetL2Summed.olean` is CO-LOCATED in the
redirected tree (`C:/dgbuild/e87b/lib/lean/...`) — a second `LEAN_PATH`
root does NOT work; co-locate new oleans the same way.  Constituents now
4-of-5; dispatched: traceHessian (the hardest — assemble the R-independent
split from the three committed `(0,4)` curvature engines
`riemannLoweredBackgroundDifference` / `ricEndoBackgroundDifferenceField` /
`riemannG1LoweringDifference`; NOT a `slotExtend` of `connDiffSection`).

## Planner acceptance №7 (2026-07-22) — traceHessian LANDED; constituent set COMPLETE (5/5)

Accepted: `TraceHessJetL2Summed.lean` (per-order + summed, sibling-compatible
shape, green/axiom-clean; imports only committed-clean
`RemainderCoeffL2JetMoser`).  LOAD-BEARING CORRECTION accepted and recorded:
the roadmap's "three curvature engines" route for traceHessian was a
MISCLASSIFICATION — `traceHessianCoeff` is a purely algebraic cometric
(`g₁⁻¹`) coefficient with NO covariant-derivative gain (the gain lives in
the kernelField/Lie), its jet is order-preserving, so it reaches nothing at
the protected top window and **`Ktop = 0` is structural, not a mask**; the
discipline is satisfied vacuously at the top.  Honest limitation recorded:
the delivered `Kc` is a uniform ball-uniform constant, not yet genuinely
data-weighted; upgrade path identified (metric-inverse tame machinery —
either the ~660-line private copy or the public Hs-norm lemma + Hs→jet-L2
bridge).  `RemainderCoeffTopSeparated.md`'s falsified traceHessian section
corrected.

**Constituent set COMPLETE: arm0, arm1, connDiff, Lie, traceHessian — all
five carry uniform-shape summed top-separated producers, green and
axiom-clean.**  Next brick = the data-weighted threeArm decomposition
itself (the `C₀/C₁/C₂` assembly mirroring the frozen
`DeTurckRemainderTameLipschitz.lean:36054` shape with the five new
producers in place of the ballUniform ones).  OPEN PLANNING QUESTION for
that dispatch: whether the threeArm sum needs true data-weighting from the
traceHessian term (then the `Kc` upgrade goes first) or absorbs the
constant `Kc` (shape-compatible since `Ktop = 0`) — resolve by reading the
threeArm consumption shape in `SobolevNonlinearityExistence.md` before
dispatching.

## Planner acceptance №8 (2026-07-23) — Step-0 ABSORBED; assembly premise CORRECTED

Accepted both findings of the eighth executor (no Lean written — correctly):
(1) Step-0 verdict ABSORBED — traceHessian's constant `Kc` needs no upgrade
(`Ktop = 0` ⟹ nothing in orientation 2; its low part lands in the allowed
tame factor).  (2) The dispatch's "five producers converge into `C₀`"
premise was WRONG at HEAD.  CORRECTED CONSTITUENT MAP (forensics in
`ThreeArmTopSeparated.md`):
- `C₀ = pathIntegralCoeffField Ψ₀ + K₀`, `Ψ₀ = −2·arm0Field
  + deTurckLieCoeffField + lieCorr0Field` (all (2,2);
  `DeTurckRemainderTameLipschitz.lean:34827/36054`).  Landed producers cover
  only arm0Base; **`deTurckLieCoeffField` (`RicciDeTurckSectionDifference
  .lean:7716`) and `lieCorr0Field` (`LieCorr0Core.lean:583`) — both
  `g_bg`-dependent — have NO top-separated producer anywhere and genuinely
  carry the top window** (cannot be absorbed like traceHess).
- `C₁` analogously needs `deTurckLieArm1Coeff`-side producers beyond
  arm1Base.  `C₂` is covered (deviation head + traceHess).
- The landed connDiff/kernelField producers are (3,4), `g_bg`-independent,
  and belong to the `b3_`/`b4_` correction-engine family — valuable there,
  NOT `C₀` constituents.
**RATIFIED continuation: option (a)** — stay on the COMMITTED decomposition
and extend the producer set to the DeTurck-Lie fields (per-field bricks,
established pattern); option (b) (a new connDiff-routed `C₀` identity)
is REJECTED as statement-risk/orphan-API.  Next dispatch:
`deTurckLieCoeffField` first — reconnoiter its committed decomposition and
which committed topSeparated engine (if any) covers its top window; build
the summed producer if covered; report the exact missing engine if not.

## Planner acceptance №9 (2026-07-23) — deTurckLie Phase A accepted; MULTI-SESSION brick ratified

Accepted the ninth executor's Phase-A findings (forensics in
`DeTurckLieJetL2Summed.md`): the covering engine IS the committed
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` applied at order
`j = i+1`; all routing identities exist (`deTurckLieCoeffField = DLa + DLb`,
the `dLaLoweredCovec` covGrad identity, the DeTurck-VF ↔ connDiffSection
identities, the cocycles; `g_bg` parts are T-independent ⟹ `Kc`).  NO
missing mathematical frontier — the gap is the field-level bridge: the
committed reductions are fully grid-collapsed, and top-separating the
`g₁`-dependent `dLaBiContrFib` bicontraction (DLa) and the
`deTurckLieWEndoInsert` insertion (DLb) through the Leibniz with the
`Hd`-head kept separate is ~300–500 lines PER HALF.  **RATIFIED as an
explicit multi-session brick: DLa `Hd`-head per-order reduction → DLb →
`DLa+DLb` triangle.**  WINDOW NOTE recorded: deTurckLie's top window is
`a+2` (matches arm0Base, one order above connDiff/Lie) — the C₀ top window
is `a+2`, set jointly by arm0 and deTurckLie; sibling-compatibility for
this field means arm0-compatible.  Dispatched: the DLa sub-brick alone.

## DLa sub-brick recon snapshot (2026-07-23, preserved at user reboot)

The DLa executor was stopped cleanly for a machine reboot (no `.lean`
created; stall cause = cross-lane Lean concurrency with the Codex
processes — quiet-window protocol now mandatory for all dispatches).  Its
completed reconnaissance, preserved verbatim:
- Engine head: `10·S 0·rfns(∇^{j+1}T)` (R-independent); remainder
  `Kc j·∑_{k<j} b(j-k)·antidiagTupleGrid b (k+1)`.
- `rfns_iteratedCovGrad_covGrad_comm_rs` gives
  `rfns(∇^i(covGrad(connDiffSection))) = rfns(∇^{i+1}(connDiffSection))`
  — so the engine at `j = i+1` yields the `∇^{i+2}T` head.
- `dLaKernelRaisedCc` (`DeTurckLieKernelL2JetBound.lean:1589`) splits into
  8 summands with `A1 = covGrad(connDiffSection g₁ g₀)` the isolated top;
  the other 7 (the `g_bg` part + 6 quad terms) reach only product-order
  `i+2` with single factors `≤ ∇^{i+1}T`.
- **Scoping win:** the head atom (`covGrad(connDiffSection)`
  top-separation) is PURE connDiffSection — no DLa-specific def needed;
  it imports only committed-clean modules (same import cone as
  `ConnDiffJetL2Summed`), avoiding every dirty tracked file.
Next dispatch resumes from exactly here: prove the head-atom lemma first
(`∇^i(covGrad connDiffSection)` top-separated via the comm identity +
engine), then the 8-summand triangle.

### DLa STEP 1 (head atom) IMPLEMENTED — pending first typecheck (2026-07-23)

New leaf `Analysis/Sobolev/TensorHilbert/DLaTopSeparated.lean` (+`.md`), namespace
`DifferentialGeometry.Integral.Connection`, imports only committed-clean
`RemainderCoeffL2JetMoser` + `RicciConnDiffOrder1TameEnvelope` (same cone as
`ConnDiffJetL2Summed`; no `deTurckLie*` / dirty-file import — the head atom is pure
`connDiffSection`, so elaboration never enters `DeTurckLieKernelL2JetBound.lean` or the dirty
`CurvatureCoefficientDifferenceJetTower.lean`).  Three theorems for the DLa top factor
`covGrad (connDiffSection g₁ g₀)`:
`covGradConnDiffSection_perOrder_l2_topSeparated_generic` (generic `(g₁,P,htie)`;
`‖∇^i(covGrad(connDiffSection))‖² ≤ Ktop·‖∇^{i+2}P‖² + Kc i·(1+∑_{j<i+2}‖∇^jP‖²)`,
`Ktop = 2·Kt0` R-independent, `Kc i = 2·Kc0(i+1)·(i+1)·KI i` house R-pattern) →
`…_realizedFam_jetL2_perOrder_topSeparated` (top point `i+2`) →
`…_realizedFam_jetL2_summed_topSeparated` (top window `a+3` = `∑_{j≤a+2}`, matching arm0's `a+2`).
Route = recon snapshot's two-liner: comm identity `rfns_iteratedCovGrad_covGrad_comm_rs`
(`OperatorFieldFibreNormJet.lean:514`, same namespace ⇒ in scope) as an EQUALITY (no `finrank²`,
unlike connDiff's slotExtend transfer), then the committed engine
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` at order `j=i+1`; remainder reshaped by copied
private `tsResSum_le_boundedWindow` at `(i+1)` → window `(i+1)(i+3)` = converter window (NO
`boundedFactorGridWindow_mono` widen needed, unlike ConnDiff at order `i`); integrated by
`boundedFactorGridWindow_integral_ballUniform_tameWindow`.  Summed via copied `jetL2_sum_lowShift a 2 2`
(top offset `p=2`).  VERIFICATION: quiet-window waiter + direct `lean` vs `C:/dgbuild/e87b/lib/lean`
armed (Codex lane held the Lean lock continuously through the session); `#print axioms` audit pending.
(N) still **0%**; this is sub-brick 1 of 3 (DLa head → DLa 8-summand triangle → DLb → `DLa+DLb`) of
the 1st of 2 genuinely-missing C₀ constituents.  Step 2 plan (8-summand `dLaKernelRaisedCc` bridge,
`DeTurckLieKernelL2JetBound.lean:1589`; DLa = `dLaBiContrFib` bicontraction, `:44`) in
`DLaTopSeparated.md`.

## Planner acceptance №10 (2026-07-23) — DLa HEAD ATOM VERIFIED GREEN

The planner ran the verification directly in the post-reboot quiet window:
`DLaTopSeparated.lean` EXIT=0, zero errors/warnings, and all three theorems
(`covGradConnDiffSection_perOrder_l2_topSeparated_generic`,
`…_realizedFam_jetL2_perOrder_topSeparated`,
`…_realizedFam_jetL2_summed_topSeparated`) audit to exactly
`[propext, Classical.choice, Quot.sound]`.  Temporary `#print axioms` lines
stripped post-verification (pure commands; no proof content touched; file
now 514 lines).  Constant note confirmed: `Ktop = 2·Kt0` with NO `finrank²`
factor (the covGrad comm identity is an equality, not a slotExtend
transfer).  Next dispatched: DLa Step 2 — the 8-summand
`dLaKernelRaisedCc` triangle (A1 = the verified head atom; the 7 non-top
summands' committed ball-uniform bounds go wholly to `Kc`), yielding the
DLa per-order + summed top-separated bound.

## Planner acceptance №11 (2026-07-23) — DLa field bound STRUCTURALLY WAIT-ON-CODEX; head cell delivered

Accepted the twelfth executor's findings: (1) `DLaHeadCellRfns.lean` written
(pointwise `rfns` top-separated bound for the A1 head cell, committed-clean
imports only) — VERIFICATION PENDING on a quiet window (Codex lean active
again at check time; planner verified the file exists; will verify at next
quiet window).  (2) STRUCTURAL BLOCK confirmed by planner git-status check:
`DeTurckLieKernelL2JetBound.lean` is DIRTY (Codex in-flight), and the entire
DLa bridge (`deTurckLieDLaCoeffField_eq_pairTrace`, `dLaKernelRaisedCc`,
`dLaSymCc`, `pairTraceOpDla`, all `_tgrid` bounds) is PRIVATE inside it — a
leaf cannot reference privates, copying ≈1300–2500 lines would be forbidden
parallel API, and editing the dirty file is barred.  The correct home for
the DLa (and likely DLb) field bounds is INSIDE that file next to its
private deps.  **The deTurckLie constituent is therefore parked
WAIT-ON-CODEX** (release/land `DeTurckLieKernelL2JetBound.lean`, or expose
the bridge pieces as public).  ASKS TO THE CODEX LANE now three: (i) commit
the 64 JetTower lines; (ii) repair the worktree `.lake` hash split; (iii)
land/release `DeTurckLieKernelL2JetBound.lean` (or publicize its DLa/DLb
bridge).  Meanwhile dispatched: ruling item 1 — the generic `timeH1`
√t-modulus lemma (`‖u(t) − u(0)‖ ≤ √t · ‖∂ₜu‖_{L²([0,T];·)}`) — fully
independent of the Codex coupling; it also replaces the qualitative
`ContinuousWithinAt` δ in the eventual fixed-horizon representative
(ruling item 5).

## Planner acceptance №12 (2026-07-23) — ruling item 1 DONE; DLa head cell verified

Accepted: (1) **Ruling item 1 COMPLETE, verified green/axiom-clean** —
`timeH1.norm_toFun_sub_init_le` (the √t-modulus
`‖u.toFun t − u.init‖ ≤ √t·‖u.deriv‖`) + supporting sharp-horizon engine
`integral_norm_Icc_le` (`TimeSobolev/TimeH1Modulus.lean`); genuinely new
(no pre-existing modulus; `norm_toFun_le` was √T and not the difference);
consumed later by ruling item 5.  (2) `DLaHeadCellRfns.lean` VERIFIED by
the planner (EXIT=0, axioms exactly the standard three; audit line
stripped).  (3) `LieCorr0Core.lean` confirmed committed-clean — the
lieCorr0 constituent MAY be dispatchable, but C₀ remains blocked on the
DLa/Codex wait regardless, so priority goes to ruling item 3.  Next
dispatched: **ruling item 3** — the `H^{a+1}`-controlled scalar cutoff
acting on `H^{a+2}` (`U ↦ χ(‖ιU‖_{H^{a+1}})·U`), with its four lemmas
(maps into the ball, identity on the ball, `H^{a+1}`-Lipschitz, mixed
`H^{a+2}/H^{a+1}` difference estimate) — pure spectral-space construction,
Codex-independent, and the gateway to items 4–5 (the actual lifetime fix).

## Planner acceptance №12 (2026-07-23) — items 1 & 3 VERIFIED; head cell VERIFIED; item 4 dispatched ABSTRACT

Verified by the planner in the quiet window (all EXIT=0, axiom audits
exactly `[propext, Classical.choice, Quot.sound]`, audit lines stripped
after green):
- `DLaHeadCellRfns.lean` (`covGradConnDiffSection_perOrder_rfns_topSeparated`)
  — the DLa A1 head cell, pointwise form.
- `LowScaleCutoff.lean` (ruling item 3) — all five declarations
  (`incl_lowScaleCutoff`, `lowScaleCutoff_mem_ball`, `_eq_self`,
  `_incl_lip`, `_sub_le`); the mixed difference estimate carries the tame
  cross term with NO pointwise `H^{a+2}`-ball hypothesis.
- Ruling item 1 (`TimeH1Modulus.lean`: `timeH1.norm_toFun_sub_init_le` +
  `integral_norm_Icc_le`) was self-verified green by its executor earlier.
SCOREBOARD: ruling items 1 ✓, 3 ✓; item 2 = five summed constituents green
+ head cells green, field-level DLa/DLb assembly WAIT-ON-CODEX
(`DeTurckLieKernelL2JetBound.lean` private deps); items 4–6 open.
DESIGN DECISION for item 4 (dispatched): build it ABSTRACTLY — take the
two-orientation tame difference bound as a HYPOTHESIS (the shape item 2
will eventually instantiate), consume the verified cutoff API + the
`timeL2/timeH1` currencies, and conclude the `timeL2` contraction estimate
parallel to `nemytskiiMixedForcingMap_dist_le`.  This decouples item 4 from
the Codex-blocked concrete instantiation, mirroring the
`forward_ode2_of_bound` abstraction pattern.

## Planner acceptance №13 (2026-07-23) — tree COMMITTED CLEAN; authoritative build 7/8 pending one upstream rebuild

- User clarified nobody owns this branch; the orphaned Codex leftovers were
  committed by the user: `f55a993d6` (JetTower pureTrace/koszul lines +
  DeTurckLie `symmC0_rfns_le` wrapper) and `126aaebda` "update" (sweeps in
  the eight new modules and notes).  `git status --short` is now EMPTY.
- User ran the authoritative 8-target `lake build`: 9432/9433 jobs; single
  failure = `...EllipticBridge...EigenvectorChartRHSDiffNumeratorWkpNormSharp`
  (the previously hash-split heavy spectral module; its `.lake` artifacts
  are stale at 07-20 00:49 and its cached `.trace` log holds no error, so
  the job genuinely re-ran and failed — exact error text not yet captured).
  `LowScaleCutoff` IS lake-green (artifacts 07-23 21:14).  The six
  TensorHilbert engines + `TimeH1Modulus` sit downstream of the failed
  module and were skipped — still pending authoritative verification.
- ROOT CAUSE FOUND (deterministic, not a race / not thread exhaustion):
  Windows MAX_PATH.  With the 63-char worktree prefix, exactly two modules
  have build artifacts over the ~260-char C-runtime limit:
  `EigenvectorChartRHSDiffNumeratorWkpNormSharp` (`.olean.hash` = 261;
  its `.trace` = 256 is readable, so Lake starts the replay and then dies
  ENOENT on the hash — the exact observed error) and
  `EigenvectorChartRHSDiffWkpNormSharpBoundedExplicit` (`.olean.hash` =
  267, `.trace` = 262; not in today's closure, latent).  The 07-20 sidecar
  files were written by long-path-capable `cp` mirroring, which is why
  they exist yet Lake cannot open them.  This also retro-explains the
  original "missing hash" split that first broke `lake build`.
- Diagnosis nailed by minimal repro: Lean's own runtime on the 261-char
  path gives `pathExists: false` + `IO.FS.readFile` ENOENT, while bash and
  .NET read the same file fine.  A `C:\w87` junction did NOT help — Lake
  canonicalizes the workspace root back to the real long prefix.
- FIX (zero recompile, adopted): `lakefile.toml` on this branch sets
  `buildDir = "C:/dgb2/e87b"` (short absolute path; comment in the file
  explains why; REVERT before merging to a normally-located checkout).
  The old `.lake/build` (9.4 GB) was preseeded into `C:/dgb2/e87b` via
  hardlinks (`cp -al`, ~2 min, zero extra disk).  Trace keys survive:
  probes report "All targets up-to-date" for LowScaleCutoff (1902 jobs)
  AND for the previously-fatal Numerator module (8954 jobs) — the killer
  replay now passes.  No special cwd is needed anymore; plain `lake build`
  / `lake env lean` in the worktree just work.  The old
  `.lake/build` tree is abandoned (do not delete yet; it backs the
  hardlinks' provenance history).  The 8-target authoritative build was
  relaunched under the new buildDir; result recorded below.
- RESULT (2026-07-23 ~23:20): `lake build` of all eight targets GREEN —
  "Build completed successfully (9433 jobs)", EXIT=0.  The six
  TensorHilbert engines compiled fresh (23:19–23:20); `TimeH1Modulus` and
  `LowScaleCutoff` had already built in the user's run (21:14) and
  replayed.  ALL Stage/ruling machinery modules of this plan are now
  authoritatively lake-verified (not just focused-check green).  Scoreboard
  unchanged otherwise: (N) itself still 0% (its `sorry` untouched); next
  brick = DLa/DLb field-level assembly inside
  `DeTurckLieKernelL2JetBound.lean` (dispatched).
- NOTE (superseded same night): the №12 item-4 executor was STOPPED BY THE
  USER before reporting — but recon found it HAD delivered
  `Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/TameNemytskii.lean`
  (mtime 07-23 21:09, swept unverified into `126aaebda`): the abstract
  two-orientation tame `timeL2` contraction, exactly the №12 design
  (three declarations; see `TameNemytskii.md`).  Planner statement-level
  acceptance PASSED (constant discipline clean: leading coefficient
  `K(1+Minf)` radius-free; top norms only against the low-scale `Dinf`).
  User said "item 4 继续" → verification queued (lake build + axiom
  audit) behind the running DLa executor; result recorded below when it
  lands.  Also note: the 07-19 Codex lane files in the same directory
  (`TimeLocalNemytskii`, `TimeTameFixedPoint`, `MovingMass`,
  `RadialMixedBound`) are UNVERIFIED source-only drafts per their own
  `.md`s — separate concern, not item 4.
  Ruling scoreboard: items 1 ✓, 3 ✓; item 2 in flight (DLa brick);
  item 4 delivered pending verification; items 5, 6 open.
- ITEM 4 VERIFIED GREEN (2026-07-24): after one mechanical repair
  (`TameNemytskii.lean:116`, `add_le_add_right` → `add_le_add … le_rfl` on
  the ENNReal goal), `lake build +...TameNemytskii` succeeded (2500 jobs)
  and the axiom audit returned exactly `[propext, Classical.choice,
  Quot.sound]` for all three declarations.  Scoreboard now: items 1 ✓,
  3 ✓, 4 ✓; item 2 in flight (DLa multi-session brick, session 1 interim:
  `engineRem_le_dLaGridWin` + `exists_rfns_connDiffSection_topsep_dla`
  green, `exists_rfns_dLaKernelRaised_topsep` in re-check, field lift
  drafted); items 5, 6 open.

## Planner acceptance №14 (2026-07-24) — DLa session 1 ACCEPTED; item 4 DONE

- DLa brick session 1 (kernel top-separation) ACCEPTED: spot-checks pass
  (three lemmas present in `DeTurckLieKernelL2JetBound.lean`
  `section DLaGridBrick` at :4753/:4789/:4873; audit lines stripped; diff
  scope = the brick's own files only).  Discipline check PASSED: Ktop =
  `2·Kt0` (connDiffSection) and `256·Kt0` (8-summand kernel twin), both
  `(g₀,g_bg,hδ₀)`-level and R-free; R only in Kc (house pattern); the
  `A1 = covGrad(connDiffSection g₁ g₀)` head stays separate.  Axiom audit
  verbatim `[propext, Classical.choice, Quot.sound]` on all three.
- Ruling item 4 DONE the same night (`TameNemytskii.lean`, commit
  `3bd9a72f0`).  Scoreboard: items 1 ✓, 3 ✓, 4 ✓; item 2 = DLa piece 4
  (field lift, designed, next session) then DLb
  (`DeTurckVectorFieldL2JetBound.lean`) then assembly; items 5, 6 open.
- Next dispatch: DLa session 2 = piece 4 field lift per
  `DeTurckLieKernelL2JetBound.md` §"Remaining field assembly" (route
  4.1–4.7; `appCcGdiag i ≤ appCcGdiag a` monotone bound resolves the
  i-dependent top coefficient; `jetL2_sum_lowShift a 2 3` at the summed
  layer).

## Planner acceptance №15 (2026-07-24) — DLa HALF COMPLETE (field lift verified)

- DLa session 2 (piece 4, +971 lines) ACCEPTED.  Spot-checks pass: both
  public endpoints present
  (`deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated` :5680,
  `..._summed_topSeparated` :5966), zero `sorry`, audit lines stripped,
  diff scope = the four permitted files.  Executor evidence: whole-file
  focused check EXIT 0 with EMPTY log (zero errors/warnings, real — the
  identical command surfaced errors before the fixes), axiom audit exactly
  `[propext, Classical.choice, Quot.sound]` on both endpoints.
- Discipline PASSED: `Ktop = CPT0·fr²·8·256·Kt0·(1+fr⁵δ₀²)·(appCcGdiag a)²`
  — `(g₀,g_bg,hδ₀)`-level only, R-free, no top-norm products; R only in
  the lumped `Kc` via the tame-window integrator.  Summed endpoint uses
  `jetL2_sum_lowShift a 2 3` (both windows `a+3`), shape-matching the
  connDiff sibling.
- With session 1, the ENTIRE DLa half of `deTurckLieCoeffField` is done.
  Remaining for the constituent: DLb sibling producer
  (`DeTurckVectorFieldL2JetBound.lean`, near
  `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform` :3041),
  then the combined assembly via
  `deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField` (2·DLa²+2·DLb²).
- Maintenance note: `DeTurckLieKernelL2JetBound.lean` is now 6007 lines
  (over the 3000 cap, grandfathered mid-brick).  Split by abstraction
  boundary AFTER the deTurckLie constituent closes; do not churn now.
- (N) still 0%.  DLb session dispatched next.

## Planner acceptance №16 (2026-07-24) — DLb session 1 accepted; TWO RULINGS

- DLb session 1 ACCEPTED: three verified layers in
  `DeTurckVectorFieldL2JetBound.lean` `section DLbTopSeparated` (:3147) —
  `exists_rfns_connDiff_topsep` (:3245, public-grid-currency mirror of the
  DLa pointwise top-sep), `connDiff_L2_topsep` (:3337, retires the
  L2-integration route risk), `wXi_L2_topsep` (:3462).  Whole-file focused
  check EXIT=0 live (pre-existing warnings still emitted ⟹ not
  cached-stale); zero `sorry`; diff scope = the three permitted files.
  Intermediate helpers — axiom audit deferred to the endpoints.
- RULING 1 (structural, accepted): the named field endpoints CANNOT live
  in `DeTurckVectorFieldL2JetBound.lean` (`deTurckLieDLbCoeffField` is
  defined in `DeTurckLieKernelL2JetBound.lean:60`; the slotInsert bridge
  in `DeTurckLieCoeffL2JetBound.lean:47`).  Split per the canonical-home
  rule: insert-level endpoints
  `deTurckLieWEndoInsert_realizedFam_jetL2_{perOrder,summed}_topSeparated`
  in the vector-field file (the analytic heart), plus a THIN `×4·finrank`
  R-free field wrapper `deTurckLieDLbCoeffField_realizedFam_jetL2_*` in
  `DeTurckLieCoeffL2JetBound.lean` mirroring its ballUniform wrapper
  (:244).  Session 2's editable set extends to that file.
- RULING 2 (mathematical): GENUINE positive Ktop; the `Ktop = 0`
  shortcut is REJECTED for DLb.  DLb's top content is real
  (`wAlphaA = ∇^{i+1}wOmega` reaches `∇^{i+2}T`); lumping it under the
  R-carrying `Kc` loses the R-freeness of the top coefficient
  irrecoverably at this layer and would poison the combined
  `2·DLa² + 2·DLb²` assembly (DLa's R-free `256·Kt0` wasted).  `Ktop = 0`
  remains legitimate ONLY for constituents with no genuine top content
  (the traceHess pattern).
- Remaining insert tower (session 2, recipe in
  `DeTurckVectorFieldL2JetBound.md`): wOmega corner peel via
  `iteratedCovGrad_appCcRS_eq_argCorner_add_lower`
  (`OperatorFieldFibreNormJet.lean:1410`) + lower sum ball-uniform
  (:1372); wAlpha triangle; realizedFam wrapper with
  `appCcGdiag n ≤ appCcGdiag (a+1)`; summed via `jetL2_sum_lowShift a 2 3`;
  then the downstream field wrapper.  DLb insert producer ~40%;
  deTurckLie constituent ~65%; (N) 0%.

## Executor constraints (multi-agent; STRICT)

- Work ONLY in this worktree/branch.  The tree is committed clean as of
  №13 (`126aaebda`); the old "uncommitted Codex work — do not commit" rule
  is obsolete.  Keep commits surgical, never sweep unrelated files.  New
  leaf files + this plan's named files only; the Stage-3 statement edit
  only after acceptance.
- Verification: focused `lake env lean <file>` per edit; `lake build
  +<Module>` only for final verification of NEW modules.  Build artifacts
  live in `C:/dgb2/e87b` (branch-local `buildDir` in `lakefile.toml`; see
  №13 — MAX_PATH.  Do NOT change `buildDir` back or build with a stripped
  lakefile: the default `.lake/build` prefix deterministically fails on
  two deep spectral modules).  Never run two Lean processes at once.  Put `set_option autoImplicit false` at the top
  of every new file (`lake env lean` does NOT apply lakefile leanOptions —
  a focused check does not verify binder hygiene).
- Honest accounting: (N) remains 0% until its exact `sorry` is gone;
  stage completions are machinery.  Record per-file notes in same-name
  `.md`s and update THIS plan's status log.

## Status log

- 2026-07-19: plan created; Stage 0 not started.
- 2026-07-20: **Stage 0 COMPLETE — audit in `ShortTime/UnifClassBounds.md`. STOP for
  acceptance; Stage 1 NOT started (blocked).** Two obstructions found, both fatal to the
  stages as scoped:
  (1) The explicit time `T₀ = min 1 (min (1/(64(C₂+1)²)) ((1/(16(C₁+1))/(2(‖Nfun 0‖+1)))²))`
  (`DeTurckQuasilinearExistence.lean:701`; `L` does NOT enter) depends on three `g₀`-scalars
  `C₁,C₂,‖Nfun 0‖` that are all `Classical.choose`s of `g₀`-intrinsic Sobolev-scale
  constants (`Ca·Cb` norm-equiv, `R₀` embedding, `K` multiplication). There is NO explicit
  formula to thread `Λ` through and NO pre-existing uniform cross-metric Sobolev layer —
  so Stage 1's premise ("not new analysis") is false.
  (2) The engine RETURNS `T₁ = min(T₀, d/2, d₂, d₂F)` (not `T₀`) from
  `maxreg_solution_jointly_smooth_representative_of_nemytskii` (`MaxRegSolutionJointlySmooth.lean:957,1141`),
  a bare `∃ T₁, 0<T₁`. `d` is a δ from a QUALITATIVE `ContinuousWithinAt` of the solution at
  `t=0` (`:1138`); `d₂,d₂F` are existential bootstrap horizons — none has a quantitative
  floor. So Stage 2 ("expose `T ≥ φ`") is also under-scoped.
  `A(n) = 4·finrank+12` confirmed (needed in the `g₀`-spectral `H^a` norm, not just
  pointwise). Lemma-3.11 producers (`AllTimesBounds.lean:691,773,793,4415`) ARE order-generic
  (`a ≤ A(n)` fine); (N)'s `a ≤ 3` cap is the only input-side block. Statement change is
  necessary but NOT sufficient.
  **Planner decision needed:** ratify R1 as a multi-session analytic lane (build the uniform
  cross-metric `H^{A(n)}` layer §5(i) + the quantitative time-floor layer §5(ii)), OR pivot
  to a fixed-`gBase`-scale engine re-derivation (dissolves cross-metric, overlaps R2). See
  `UnifClassBounds.md` §0/§5.
- 2026-07-22: user ruled: **consult GPT Pro per protocol before choosing the route.**
  Consult STAGED: branch pushed to origin (`codex/analytic-producers-e87b` @ `922dbc4ac`,
  new remote branch) so Pro can read the cited files; the exact diagnostic prompt (with
  distilled Stage-0 audit + blob links) is `ShortTime/UNIF_N_PRO_PROMPT.md` (everything
  after its `---` separator is the message body).  Submission via the Chrome plugin is
  BLOCKED — the Claude-in-Chrome extension is not connected in this session (not a content
  blocker).  Next: submit the prompt in a fresh chat of the ChatGPT project "Lean Pro
  Consult Handoff" (user-side or once Chrome is connected), then bring the answer back
  here and record the ruling before any Stage-1 Lean is attempted.
- 2026-07-22: **GPT Pro ruling received (user-submitted); recorded verbatim in
  `ShortTime/UNIF_N_PRO_RULING.md`.  ROUTE = R1τ** (design issue: the
  faithfulness/identity-region guard lives in a pointwise `H^{a+2}` ball —
  the wrong topology; R1′ not literally, R1″ rejected, R2 parked).  The old
  Stages 1–3 of this plan are SUPERSEDED by the ruling's six-item lemma
  frontier (see the ruling file): (1) `timeH1` √t-modulus → (2) second-order
  TAME smooth-core difference estimate WITHOUT endpoint `H^{a+2}`-ball
  hypotheses (**decisive route test — implement first and alone**) →
  (3) `H^{a+1}`-controlled cutoff on `H^{a+2}` → (4) time-level tame
  Nemytskii → (5) fixed-horizon representative returning the input `T`
  exactly → (6) NARROW class-uniform packet at orders `a, a+1, a+2` only.
  Explicit stop signal for (2): unavoidable `C(R₂)·‖U−V‖_{H^{a+2}}` (pointwise
  `R₂`) or `‖U‖_{H^{a+2}}·‖U−V‖_{H^{a+2}}` term ⟹ R1τ dead at `A(n)=a+2`,
  reconsider formulation; do NOT mask with extra jets / reintroduced `d₂` /
  cross-metric layer / new `Classical.choose`.  Item (2) dispatched to an
  Opus executor with the ruling's own implementation prompt.
- 2026-07-22: **Item (2) route test — VERDICT (a) FEASIBLE; stop signal NOT
  hit.** Full analysis in
  `Analysis/Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.md`.
  Both high–low orientations close with **R-INDEPENDENT** constants, so no
  `‖T‖_{a+2}·‖T−T'‖_{a+2}` and no pointwise `H^{a+2}` radius:
  (i) the top-order coefficient (of `∇²(T−T')`) is the path-integral deviation
  `C₂ = deTurckPhiTotPathIntegral − deTurckPhiMetTotal(g₀)` with sup
  `≤ c·max βT βT'`, `c = √(8·CTH 0+8·CR 0)·(dim/(1−δ₀))` **R-independent**
  (`deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform`,
  `DeTurckRemainderTameLipschitz.lean:35645/35700`; `CTH,CR` from
  `traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns`,
  `RemainderCoeffL2JetMoser.lean:345`, take only `g₀`) → orientation 1;
  (ii) the low arms' `‖T‖_{a+2}` content is extractable **data-weighted** with
  R-independent constants via the **top-separated / tame-envelope** layer
  (`linearizedRicciArm{0,1}BaseCoeff_..._topSeparated` in
  `RemainderCoeffL2JetMoser.lean:1398/1532`; generic producers in
  `CurvatureCoefficientDifferenceJetTower.lean:14447` and
  `RicciArmOrder1KoszulTameEnvelope.lean`/`RicciConnDiffOrder1TameEnvelope.lean`;
  `Ktop,Kc` R-independent, from `..._backgroundDifference_topSeparated_le` on
  only `g₀,hδ₀`) → orientation 2 (`Hd`) + orientation 1 (remainder).
  The existing ball-Lipschitz proof HIDES both facts: it LUMPS the top-arm
  tight `c` into `ΛC ~ R` (`36054:36161`, `1353:1414`) and uses only the
  `ballUniform` (opaque-in-R) low-arm bounds
  (`ricciArmFields_concrete_lichnerowicz_uniform_rfns_ballUniform`,
  `RicciThreeArmAppCc.lean:3345`), so `1421` emits `Ccov ~ R` on BOTH `S₂` and
  `S₁`. **No Lean lemma was added:** the smooth-core tame theorem is a
  multi-lemma ASSEMBLY (data-weighted top-separated threeArm coeff bound —
  re-deriving `canonicalTop`+`curvatureFold`+`deviation` of `36054` with the
  top-separated per-field bounds instead of ballUniform — then covariant tame
  (analogue of `1421`) then smooth-core lift (analogue of `1924/1810`)), most
  of it landing in the frozen `DeTurckRemainderTameLipschitz.lean` on top of
  the tame-envelope producers whose deepest generic layer
  (`CurvatureCoefficientDifferenceJetTower.lean`) is in-flight Codex work
  (`M`). This exceeds "one theorem + one precursor"; not attempted to avoid
  orphan machinery / churn. Route is GREEN for R1τ; next brick = the
  data-weighted threeArm coeff bound (see the `.md`).
- 2026-07-22: **Ratified next brick DONE (2 of the ~5 constituent per-field
  bounds).** New leaf file
  `Analysis/Sobolev/TensorHilbert/ArmBaseCoeffJetL2Summed.lean` (+`.md`), namespace
  `DifferentialGeometry.Integral.Connection`.  Sums the per-order
  `linearizedRicciArm{0,1}BaseCoeff_realizedFam_jetL2_perOrder_topSeparated`
  (`RemainderCoeffL2JetMoser.lean:1398/1532`, committed-clean) over `i ≤ a` into
  `linearizedRicciArm{0,1}BaseCoeff_realizedFam_jetL2_summed_topSeparated`:
  `∑_{i≤a}‖∇^i F‖² ≤ Ktop·(topWindow) + Kc·(1 + lowWindow)`, `Ktop=2·Ktop_pO`,
  `Kc=2·∑Kc_pO` — built ONLY from the per-order `(g₀,hδ₀)`-level constants, **no
  `R`, no pointwise `H^{a+2}`**; ruling stop-signal NOT hit.  Both **GREEN,
  sorry-free** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`;
  no drift in the consumed exports).  arm0 windows top `a+2`/low `a+1`; arm1 at
  its natural top `a+1`/low `a` (first-cov-deriv arm; weaken downstream if the
  uniform shape is wanted).  A generic reusable `jetL2_sum_of_perOrder`
  (offset-parameterized) does the summation for both arms.  **threeArm
  combination NOT done — does not compose cleanly:** the threeArm `C₀:(2,2),
  C₁:(3,2), C₂:(4,2)` (`DeTurckRemainderTameLipschitz.lean:36054`) are SUMS of
  several fields (arm0/arm1 + traceHessian + connDiff + Lie) plus the top
  deviation `C₂`; the `C₀=…+arm0+…` decomposition lives in the frozen
  `DeTurckRemainderTameLipschitz.lean` on the dirty
  `CurvatureCoefficientDifferenceJetTower.lean`, and 3 more per-field summed
  bounds are still missing.  STOPPED at the two arm bounds per the note's
  guidance.  **Verification caveat:** authoritative `lake build` is blocked by a
  PRE-EXISTING worktree build-cache inconsistency (missing `.olean.hash` for an
  unrelated `EllipticBridge…EigenvectorChartRHSDiffNumeratorWkpNormSharp` in
  `.lake/build`, though present in the redirected `C:/dgbuild/e87b/lib/lean`);
  `scripts/lake-locked.ps1` is absent from this worktree.  Verified instead via
  direct `lean` against `C:/dgbuild/e87b/lib/lean` with the lakefile's
  correctness options replicated in-file.  (N) still **0%**.
- 2026-07-22: **Remaining 3 per-field summed bounds (trace-Hessian / connDiff /
  Lie): WAIT-ON-CODEX — none buildable from committed-clean inputs; no Lean
  added.**  Investigated all three; each has ONLY an `R`-DEPENDENT clean
  per-order producer, so a discipline-compliant (no-`R`-in-constants) summed
  bound cannot be built.  Root cause: their clean producers
  (`connDiffContrInsertionField_..._tameEnvelope_generic`
  `RicciConnDiffOrder1TameEnvelope.lean:982`;
  `linearizedRicciConnDiffOrder1KernelField_..._tameEnvelope_generic` `:1240`,
  built from the connDiff one; trace-Hessian
  `traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform`
  `RemainderCoeffL2JetMoser.lean:446` +
  `ricciCometricFourTraceCastG0_..._tameEnvelope_generic`
  `RicciConnDiffOrder1TameEnvelope.lean:226`) collapse a nonlinear jet product
  (from the `g₁⁻¹=(g₀+P)⁻¹` Neumann expansion) via
  `antidiagonalTupleGrid_integral_ballUniform_tameWindow`
  (`CurvatureCoefficientDifferenceJetTower.lean:8556`, **DIRTY**), whose constant
  `Gfun k = k·(max(Cemb·√(a+2)·R)…)^{7k}` grows like `R^{7k}`.  The `R`-independent
  engines these fields need (`rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
  JetTower:1823; `…riemannLoweredBackgroundDifference…` :10570;
  `…ricEndoBackgroundDifferenceField…` :11141; `…riemannG1LoweringDifference…`
  :11695) exist ONLY in the DIRTY in-flight `CurvatureCoefficientDifferenceJetTower`.
  Per the brick guardrail ("STOP if a needed export exists only there") and the
  ruling stop-signal (`SobolevNonlinearityExistence.md:106–108` — do not hide the
  low-arm `‖T‖_{a+2}` behind an `R`-ball), no R-dependent version was built.
  **The route-test note over-claimed:** it listed these tame-envelope producers as
  R-independent "analogues"; the actual Lean shows they are R-dependent (only
  arm0/arm1 have the R-independent `_backgroundDifference_topSeparated_le`
  engines committed clean).  Unblock = Codex lands the four `_topSeparated_le`
  engines clean; then each summed bound is a ~40-line reuse of the existing
  field-agnostic `jetL2_sum_of_perOrder` (connDiff/Lie at offset `p=1`).  Detail
  in `Analysis/Sobolev/TensorHilbert/ArmBaseCoeffJetL2Summed.md`.  (N) still
  **0%**; item (2) = 2 of ~5 constituent bounds done, 3 Codex-blocked.
- 2026-07-22: **CORRECTION VERIFIED — the 3 fields are BUILDABLE, not
  Codex-blocked; NO Lean landed (scope).**  Executor confirmed the planner
  CORRECTION against HEAD `922dbc4ac`: (a) all FOUR `_topSeparated_le` engines are
  committed-clean (`CurvatureCoefficientDifferenceJetTower.lean:1823/10570/11141/11695`;
  the dirty state is the 64 unrelated `pureTrace`/`koszul_l2_succ` lines only);
  (b) the "R-independent" discipline = the TOP-split `Ktop` from the engine head
  is R-independent, exactly as arm0's own L2 generic (:14447) has `Kc` threaded
  through `boundedFactorGridWindow_integral_ballUniform_tameWindow` — so the
  previous "R-dependent ⇒ forbidden" reasoning was the error (it looked at the
  fields' `tameEnvelope_generic`, which discards the top-split, not the engine);
  (c) EVERY needed lemma exists committed-clean incl. the field↔section identity
  `connDiffContrInsertionField_eq_reindex_slotExtend_two`, the transfer
  (`rfns_iteratedCovGrad_slotExtend_le`, `iteratedCovGrad_reindexCoeffGen`,
  `exists_iteratedCovGrad_slotExtend_rsDomDomCongr`), the remainder reshaper
  `tsResSum_le_boundedWindow` (private but pure-combinatorial ⇒ copyable), and a
  COMPLETE `∃Hd` template `rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le`
  (:10570, ~250 lines).  No missing mathematical frontier.  **Environment
  validated** (direct `lean` typecheck vs `C:/dgbuild/e87b/lib/lean`, EXIT 0;
  LEAN_PATH recipe recorded).  Full verified construction roadmap (per-field
  recipe + exact lemma/line refs + the cheaper DIRECT summed route that skips the
  `∃Hd`/DDC assembly) in the new
  `Analysis/Sobolev/TensorHilbert/RemainderCoeffTopSeparated.md`.  NOT LANDED:
  each field is a ~180–350-line intricate tensor-transfer assembly with ~3-min
  focused-check cycles; this exceeded one careful-iteration session.  Recommended
  order connDiff → Lie (reuse) → traceHessian (hardest).  (N) still **0%**.
- 2026-07-22: **connDiff DIRECT summed bound DONE (constituent 3-of-5).** New leaf
  file `Analysis/Sobolev/TensorHilbert/ConnDiffJetL2Summed.lean` (+`.md`), namespace
  `DifferentialGeometry.Integral.Connection`.  Built exactly per the
  `RemainderCoeffTopSeparated.md` DIRECT route (skips the field-level `∃Hd`).  Three
  GREEN sorry-free theorems: `connDiffContrInsertionField_perOrder_l2_topSeparated_generic`
  (generic `(g₁,P,htie)`) → `…_realizedFam_jetL2_perOrder_topSeparated` →
  `…_realizedFam_jetL2_summed_topSeparated`
  (`∑_{i≤a}‖∇^i(connDiffContrInsertionField g₀ (realizedFam …))‖² ≤ Ktop·(∑_{j<a+2}(‖∇^jT‖²+‖∇^jT'‖²))
  + Kc·(1+∑_{j<a+2}(…))`, both windows `a+2`).  `Ktop = 2·finrank²·Kt0` is
  `(g₀,hδ₀)`-only (`Kt0` = engine head `10·S 0` of
  `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`), **R-independent**; `Kc`
  carries the converter `KI` (`boundedFactorGridWindow_integral_ballUniform_tameWindow`),
  accepted house R-pattern.  Stop-signal NOT hit (no R in `Ktop`, no
  `‖T‖_{a+2}·‖T−T'‖_{a+2}` product).  `#print axioms` = `[propext, Classical.choice,
  Quot.sound]` on all three.  Copied private helpers (all pure): `tsResSum_le_boundedWindow`
  (from JetTower, provenance comment), `sum_shift_le`, `iteratedCovGrad_smul_real`; NEW
  `jetL2_sum_lowShift` (two-offset generalization of `jetL2_sum_of_perOrder` — connDiff has
  top point at order `i+1` but low window `i+2`).  Imports the committed-clean JetTower
  engines only; the file's 64 dirty Codex lines were untouched.  Verified via direct `lean`
  vs `C:/dgbuild/e87b/lib/lean` (0 errors, 0 warnings); authoritative `lake build` still
  blocked by the pre-existing `.olean.hash` split.  **item (2) = 3 of ~5 constituent
  per-field summed bounds done (arm0/arm1/connDiff); remaining = Lie + traceHessian.**
  (N) still **0%**.  Next: Lie (`linearizedRicciConnDiffOrder1KernelField`, reuses this
  connDiff producer via `kernelField_eq_neg_arm_combination` + `5·`-triangle).

## Status log — Lie constituent LANDED (2026-07-22)

`Analysis/Sobolev/TensorHilbert/LieFieldJetL2Summed.lean` (+`.md`), namespace
`DifferentialGeometry.Analysis.Parabolic.TensorSpectral`, imports `ConnDiffJetL2Summed`.
GREEN sorry-free, warning-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]` on
the private bridge and both public theorems.  Delivers:
`linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_summed_topSeparated` (the summed
deliverable, both windows `a+2`) and `…_realizedFam_jetL2_perOrder_topSeparated`.  Route = the
roadmap "Lie — combination of connDiff": the Lie field is `-(A+B+C+D+E)`, a negation of five
slot-permuted/reindexed copies of `connDiffContrInsertionField`, each an isometry of the jet
(`armFull_norm_eq`/`armOuter_norm_eq`); `c3_norm_five_le` gives the per-order bridge
`‖∇^i Lie‖ ≤ 5·‖∇^i connDiff‖`, squared to the private `lie_normSq_le_25`
(`‖∇^i Lie‖² ≤ 25·‖∇^i connDiff‖²`).  The connDiff SUMMED producer
`connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated` is REUSED as a black box.
`Ktop = 25·Ktop_connDiff` is `(g₀,hδ₀)`-only (25 = the pure `5·`-triangle squared, and
`Ktop_connDiff = 2·finrank²·(10·S 0)` has no R); `Kc = 25·Kc_connDiff` is house R-pattern.
Stop-signal NOT hit.  The private arm-combination stack (7 perms, `slotPermCc`,
`kernelField_eq_neg_arm_combination` [`rfl`], `armOuter/Full_rfns_eq`, `armOuter/Full_norm_eq`,
`c3_norm_five_le`) was COPIED verbatim from committed-clean `RicciConnDiffOrder1TameEnvelope.lean`
(private there); the risky `rfl` decomposition with copied perms/`slotPermCc` reproduces
(byte-identical defs + proof-irrelevant `decide` proofs).  Verified via direct `lean` vs the
redirected olean tree (multi-file: emit `ConnDiffJetL2Summed.olean` then co-locate it in the
redirected tree — a second `LEAN_PATH` root did not work; recipe in the same-name `.md`);
authoritative `lake build` still blocked by the pre-existing `.olean.hash` split.  The 64 dirty
lines of `CurvatureCoefficientDifferenceJetTower.lean` were untouched.
**item (2) = 4 of ~5 constituent per-field summed bounds done (arm0/arm1/connDiff/Lie);
remaining = traceHessian only.**  (N) still **0%**.  Next: traceHessian
(`traceHessianCoeff`/`ricciCometricFourTraceCastG0`, `(4,2)`; hardest — assemble the R-independent
split from the three curvature `(0,4)` engines, NOT a slotExtend of connDiffSection; see
`RemainderCoeffTopSeparated.md`).
- 2026-07-22: **traceHessian constituent 5-of-5 LANDED — but the "three curvature engines" route
  was a MISCLASSIFICATION; delivered with `Ktop = 0`.**  New leaf `TraceHessJetL2Summed.lean`
  (two public theorems: realizedFam per-order + summed `traceHessianCoeff_realizedFam_jetL2_summed_topSeparated`,
  same window shape as connDiff/Lie), GREEN / sorry-free / axioms = standard three, via direct
  `lean` vs the redirected olean tree (imports only committed-clean `RemainderCoeffL2JetMoser`, so
  NO untracked-olean co-location needed).  **FINDING (verified HEAD `922dbc4ac`):** the roadmap /
  №4–№6 premise that trace-Hessian assembles from the three `(0,4)` curvature engines is
  mathematically WRONG for this field.  `traceHessianCoeff` is a purely algebraic coefficient in
  `g₁⁻¹` (`traceHessianFib = cometricDoubleTraceFib ∘ domDomCongrFib`) — the low-order coefficient
  in `appCcRS(traceHessianCoeff)(kernelField)`, carrying NO covariant-derivative gain; the derivative
  gain is in the kernelField (= Lie).  Its committed decompositions route to the metric-inverse
  difference (`deTurckPrincipalCometricCoeff`/`gInvDiffSlotCoeff` at `RemainderCoeffL2JetMoser.lean:328`,
  or `ricciArmPrincipalCoeffPure`/`gInvDiffRaisedEndoField` at `RicciConnDiffOrder1TameEnvelope.lean:137/171`),
  NEVER to the curvature engines — and there is NO `topSeparated` engine for any metric-inverse field.
  So the field produces no term reaching the protected `a+1`/`a+2` top window: `Ktop = 0` is the
  CORRECT value (not a mask), discipline satisfied vacuously at the top.  **Caveat:** the delivered
  `Kc` is a uniform CONSTANT (from the ball-uniform `:446`), not yet data-weighted — genuine
  data-weighting needs the metric-inverse tame machinery (private `gInvDiffSlotCoeff_perOrder_l2_tame`
  + its `productGridTerm_integral_le_topOrderJetSq` dep, ~660-line copy; or the public Hs-norm
  `deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic` with a fragile Hs→jet-L2 bridge).  Kept
  the constant `Kc` for robustness (Ktop=0 either way; a constant is absorbed by the downstream sum).
  Full detail in `TraceHessJetL2Summed.md`.  **All 5 constituents now have a uniform-shape summed
  producer; next brick = the data-weighted threeArm decomposition (revisit the trace-Hessian `Kc`
  upgrade if it needs true data-weighting from this term).**  (N) still **0%**.
- 2026-07-22/23: **threeArm assembly brick — STEP 0 verdict = ABSORBED; assembly BLOCKED by a
  structural mismatch (five producers are NOT `C₀`'s constituents).  No Lean written.**  Full
  forensics in `Analysis/Sobolev/TensorHilbert/ThreeArmTopSeparated.md`.
  - **STEP 0 (№7 open question): ABSORBED.**  traceHessian's `Ktop = 0` is structural, so it feeds
    nothing into orientation-2 (`max‖T‖_{a+2}‖T'‖_{a+2}·‖T−T'‖_{a+1}`); its uniform-constant
    `Kc·(1+low)` lands wholly in orientation-1's allowed low factor.  A traceHessian `Kc` upgrade is
    NOT a prerequisite — the current constant `Kc` is shape-compatible and absorbed.
  - **BLOCKER (verified HEAD `922dbc4ac`):** the committed reference `C₀`
    (`deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm`,
    `DeTurckRemainderTameLipschitz.lean:36054`) is `C₀ = C₀_arm + K₀` with
    `C₀_arm = pathIntegralCoeffField Ψ₀` and `Ψ₀ = −2·linearizedRicciArm0Field + deTurckLieCoeffField
    + lieCorr0Field` (`:34827`) — all **(2,2)** fields.  Of these only `arm0BaseCoeff`
    (`arm0Field = arm0BaseCoeff + arm0CorrField`) has a landed data-weighted producer.  The two
    DeTurck-Lie constituents `deTurckLieCoeffField`/`lieCorr0Field` (both `(2,2)`, `g_bg`-DEPENDENT;
    `RicciDeTurckSectionDifference.lean:7716`, `DeTurckCoefficients/LieCorr0Core.lean:583`) have ONLY
    ball-uniform bounds and **no top-separated producer anywhere**, yet they genuinely carry the
    top-window `‖T‖_{a+2}` weight (order-`a` jet reaches `∇^{a+2}T`), so they cannot be absorbed like
    traceHess.  The landed `connDiff`/`kernelField` producers are **(3,4)**, `g_bg`-INDEPENDENT, and
    appear in the frozen file only inside the `b3_`/`b4_` engine helpers (`:40196–:42170`), NOT in
    the `C₀` assembly — they belong to the linearized-Ricci-correction / LowReg / Edge family, a
    different decomposition.  No committed identity bridges `deTurckLieCoeffField` ↔
    `connDiff`/`kernelField` (only co-occurrence is the frozen file, disjoint regions).  So the
    "five producers converge into `C₀` via a committed sum-of-fields decomposition" premise does not
    hold: `arm1Base`→`C₁`, `traceHess`→`C₂`, `connDiff`/`kernelField`→correction-engines, and only
    `arm0Base` is a genuine `C₀` constituent.
  - **Smallest next step (the real frontier):** a data-weighted top-separated summed producer for
    `deTurckLieCoeffField` (+`lieCorr0Field`, +`deTurckLieArm1Coeff` for `C₁`) — a per-field producer
    task like the five already landed, derived from the DeTurck-Lie structure (does NOT factor
    through the connDiff/kernelField engines).  ALTERNATIVELY, if a new connDiff-routed `C₀`
    decomposition is intended, its algebraic identity (difference-level `g_bg`-cancellation) + a
    (3,4)→(2,2) contraction must be built first.  **Planner: confirm which `C₀` decomposition the
    assembly targets before re-dispatching.**  (N) still **0%**.
- 2026-07-23: **`deTurckLieCoeffField` Phase-A reconnaissance DONE — covering engine FOUND, but the
  field-level top-separated BRIDGE is grid-collapsed and a LARGE multi-lemma brick, not the ~40-line
  engine-swap the §№4/§№5 roadmap assumed.  No Lean written.**  Full forensics in
  `Analysis/Sobolev/TensorHilbert/DeTurckLieJetL2Summed.md`.  Verified at HEAD `922dbc4ac`:
  - **Structure:** `deTurckLieCoeffField g₀ g₁ g_bg` (2,2) = `deTurckLieDLaCoeffField +
    deTurckLieDLbCoeffField` (`DeTurckLieKernelL2JetBound.lean:77`).  DLa's lowered covector is
    `dLaLoweredCovec = covGrad(connDiffSection g₁ g₀) − covGrad(connDiffSection g_bg g₀)` (`:1591`,
    + `deTurckLieCovDerivA_backgroundSplit`:106 / `dLaCovKernel_backgroundSplit`:248 / `connDiff_cocycle`:91);
    the (2,2) field is the **g₁-dependent `dLaBiContrFib` bicontraction** (g₁-orthoframe) of that
    covector.  DLb routes through the DeTurck VF `deTurckLieWEndoInsert` with the cocycle
    `wXi = connDiffLoweredCc g₀ g₁ − connDiffLoweredCc g₀ g_bg` (`DeTurckVectorFieldL2JetBound.lean:57`).
  - **Covering engine = `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
    (`CurvatureCoefficientDifferenceJetTower.lean:1823`, committed-clean)** — head `10·S 0·rfns(∇^{j+1}T)`,
    R-independent; applied at order `j=i+1` it reaches the deTurckLie top window `∇^{i+2}T`.  All
    routing identities present (`rfns_iCG_connDiffLoweredCc_eq_connDiffSection`:2192/2211,
    `rfns_iCG_wCA_eq_connDiffSection`:2624; g_bg parts are T-independent ⇒ Kc).  The three (0,4)
    curvature engines do NOT fit (deTurckLie's top factor is literally `covGrad(connDiffSection)`).
  - **BLOCKER:** the committed field-level reduction is FULLY GRID-COLLAPSED —
    `rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le` (`:4397`) dissolves the
    connDiffSection head into a raw `∏ rfns(∇^{e m}T)` grid (`k∈range(i+3)`) via `dLaGridWin`/
    `dLaPairCount`, then integrates ball-uniformly; DLb (`deTurckLieWEndoInsert_..._ballUniform`,
    `DeTurckVectorFieldL2JetBound.lean:3041`) consumes the ball-uniform `connDiffSection_lowOrder_
    jetL2_succ_generic`.  NO committed head/topSeparated variant for any `deTurckLie*`/`wEndo*`/
    `dLaBiContr*` field.  Unlike connDiff/Lie (single clean field↔section reindex), the deTurckLie
    bridge is the whole g₁-nonlinear bicontraction (DLa) + VF-insertion (DLb) — building the
    top-separated `Hd`-head reduction per half is a ~300–500-line intricate re-derivation each
    (multi-session), not one careful-iteration session.  No missing MATH frontier (engine +
    identities all exist); the missing piece is a large tensor-transfer bridge.
  - **Window note for the assembly:** deTurckLie top window = `a+2` (max `∇^{a+2}T`), matching
    **arm0Base**, NOT connDiff (`a+1`).  The C₀ top window is `a+2` (set by arm0 + deTurckLie); the
    deTurckLie top sum is `∑_{j<a+3}` = `∑_{j≤a+2}`, one order above connDiff/Lie's `∑_{j<a+2}`.
  - **Planner decision needed:** dispatch the DLa/DLb bicontraction top-separation as a multi-session
    brick (DLa first — cleaner `dLaLoweredCovec` covGrad identity — then DLb, then `DLa+DLb`
    triangle), or reconsider.  Recommended smallest sub-brick: the DLa `Hd`-head per-order reduction
    (top factor `rfns(∇^{i+2}P)` via the engine at order `i+1`, remainder via
    `boundedFactorGridWindow_integral_ballUniform_tameWindow`).  (N) still **0%**;
    `deTurckLieCoeffField` = 1st of 2 genuinely-missing C₀ constituents.
- 2026-07-23: **DLa Step 2 (8-summand triangle) — STRUCTURAL BLOCKER found; leaf route infeasible.**
  Executor verified the private/public surface of `DeTurckLieKernelL2JetBound.lean` at HEAD
  `922dbc4ac` (+10 dirty lines).  The dispatch premise ("import `DeTurckLieKernelL2JetBound` and the
  DLa field's identities" from a new leaf) is **false**: the ENTIRE `(2,2)`-field top-separation
  bridge is `private` — `deTurckLieDLaCoeffField_eq_pairTrace`, `dLaKernelRaisedCc`, `dLaLoweredCc`,
  `dLaSymCc`, `pairTraceOpDla`, `dLaQuadCc`, `dLaConnArmPt`, `dLaGridWin`, `dLaPairCount`,
  `exists_rfns_dLaKernelRaised_tgrid`, `exists_rfns_dLaSym_tgrid`, `exists_rfns_pairTraceOpDla_tgrid`,
  `exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla`, `exists_fixedField_rfns_jet_dla`,
  `dLaQuad_tower_of_factors`, `rfns_iCG_add/sub_le_dla` are all `private`.  The only public DLa
  surface is the field defs, three fibre identities, order-0 ballUniform, `symmC0_rfns_le` (the +10
  dirty lines), and the R-dependent grid-collapse/ballUniform — **no top-separated entry point.**  A
  leaf cannot reference `private` decls; copying them would duplicate existing private defs (a
  forbidden parallel API) at ~1300 lines (kernel) / ~2500+ (full field), unverifiable in one session;
  editing the dirty (Codex-owned) file is barred by the executor constraints.  **The correct home is
  IN `DeTurckLieKernelL2JetBound.lean` next to its private deps** — the +10 dirty lines
  (`symmC0_rfns_le`, exporting the `symmS` order-0 rfns bound used by `exists_rfns_dLaSym_tgrid`)
  indicate the Codex lane may already be building this in-file.  So this sub-brick is **blocked on the
  Codex lane** (finish/release that file, or expose the needed private pieces as public: minimally
  `dLaKernelRaisedCc`, `deTurckLieDLaCoeffField_eq_pairTrace`, and top-separated variants of
  `exists_rfns_dLaSym_tgrid`/`exists_rfns_pairTraceOpDla_tgrid`).  DELIVERED (compiling prefix, new
  leaf `Analysis/Sobolev/TensorHilbert/DLaHeadCellRfns.lean` + `.md`): the ONE public-API-buildable,
  non-duplicative piece — `covGradConnDiffSection_perOrder_rfns_topSeparated`, the **pointwise**
  (`rfns`, per-`x`) top-separated bound for the `A1` head cell `covGrad(connDiffSection g₁ g₀)`
  (`Ktop = 2·Kt0` R-independent + `boundedFactorGridWindow` remainder).  This is the un-integrated
  sibling of `DLaTopSeparated`'s head atom, in the shape the 8-summand triangle's `A1` slot consumes;
  the other 7 summands + the pairTrace `(2,2)` bridge are private-blocked as above.  Full audit +
  next-step recipe in `DLaHeadCellRfns.md`.  (N) still **0%**.  Verification: <pending — Codex lane
  held the Lean lock continuously through the session; quiet-window waiter armed, typecheck pending>.
- 2026-07-23: **R1τ ruling item 1 (generic `timeH1` √t-modulus) — IMPLEMENTED + VERIFIED (sorry-free).**
  New leaf `Analysis/Parabolic/TimeSobolev/TimeH1Modulus.lean` (+ `.md`).  Two public theorems:
  `TimeSobolev.timeH1.norm_toFun_sub_init_le` — the deliverable, `‖u.toFun t − u.init‖ ≤ √t·‖u.deriv‖`
  on `Icc 0 T`, in the carrier's own currency (`u.init` = value-at-0 = `trace0`; `u.deriv` =
  time-`L²([0,T];X)` field = `timeDeriv`) — the explicit ½-Hölder modulus replacing the naked
  `ContinuousWithinAt` δ at `MaxRegSolutionJointlySmooth.lean:1138`; and its engine
  `TimeSobolev.integral_norm_Icc_le` (`∫_{[0,t]} ‖f‖ ≤ √t·‖f‖`), the sharp-horizon √t companion of
  `BochnerL2.integral_norm_le`'s √T.  Route: FTC increment (`toFun_apply`+`abel`) → `Ioc 0 t`
  (`integral_of_le`) → `norm_integral_le_integral_norm` → `setIntegral_mono_set` → sub-measure `L¹⊆L²`
  Hölder nesting on `timeMeasure t` (mass `t`) + `eLpNorm_mono_measure` back to the full `[0,T]` norm.
  ZERO coupling to Codex-dirty files (imports ONLY committed-clean `TimeH1.lean`; `scripts/` absent in
  this worktree ⟹ verification = direct `lake env lean` read-only, precedent №2).  Reuse audit clean:
  no pre-existing √t modulus in TimeSobolev/ShortTime.  All Mathlib primitives signature-checked vs
  `.lake/packages/mathlib` before writing.  (N) still **0%** — pure supporting infra; 1 of 6 R1τ
  items, consumed later by item 5 (fixed-horizon representative).  Verification: **GREEN** — poll
  waiter caught a window; `lake env lean` (read-only; `scripts/` absent here) exit 0, no errors/warnings;
  `#print axioms` on both theorems = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  (Both
  checks ran with mild concurrency as 2–3 Codex `lean.exe` respawned — safe: concurrency risks only
  false failures, not false passes; fresh file ⟹ no stale-olean false-green.)  Full audit in
  `TimeH1Modulus.md`.
- 2026-07-24: **DLa field bound — kernel top-separation (dispatched "Step 2") BUILT inside
  `DeTurckLieKernelL2JetBound.lean`; field-level lift (Step 3) designed, not yet built.**  Three new
  private lemmas added before `end DLaGridBrick`: (1) `engineRem_le_dLaGridWin` (reshape the
  connDiffSection topSeparated engine remainder into `dLaGridWin` currency); (2)
  `exists_rfns_connDiffSection_topsep_dla` (connDiffSection top-separated jet in `dLaGridWin`
  currency, `Ktop = 2·Kt0` R-indep — consumes the committed engine
  `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`, already in the file's import cone via
  `CurvatureCoefficientDifferenceJetTower`); (3) `exists_rfns_dLaKernelRaised_topsep` (the 8-summand
  kernel triangle top-separated twin of `exists_rfns_dLaKernelRaised_tgrid` — `hA1` swapped for (2),
  `Ktop = 128·(2·Kt0)` R-indep from the 2⁷ triangle doubling; the other 7 summands unchanged in the
  `dLaGridWin` remainder).  **R-independence linchpin CONFIRMED**: `dLaGridWin b 1 = antidiagonalTupleGrid
  b 0 = 1`, so both appCcRS frame operators (`pairTraceOpDla`, the perturb `slotInsert(perturbSharp)`)
  have R-independent order-0 `rfns` ⟹ each field/perturb appCcRS `(i'=0,l=i)` cell carries the top
  `∇^{i+2}T` with R-independent coefficient.  **KEY finding**: `dLaLoweredPerturbCc =
  appCcRS(perturb)(dLaLoweredCc)` also carries A1 ⟹ the field needs TWO nested appCcRS `(0,i)`-cell
  extractions (handled by a generic extractor `rfns_iCG_appCcRS_topsep_of`, drafted).  Full route + piece
  status in `DeTurckLieKernelL2JetBound.md`; recon corrections in `DeTurckLieJetL2Summed.md`.  **All
  three pieces VERIFIED GREEN** — focused `lake env lean` (whole file, `LEAN_NUM_THREADS=4`,
  quiet-window waiter) EXIT=0, zero errors, zero warnings; `#print axioms` on all three ⇒
  `[propext, Classical.choice, Quot.sound]` (audit lines stripped).  Two fixes were needed on the
  kernel twin (a dropped `hW_ge1`, and a `mul_assoc` regroup hint so `linarith` relates the shared
  `KtopA·τ` atom scaled by 128).  The `unusedVariables` lint on hypothesis binders is suppressed with
  `set_option` matching the file's existing tgrid theorems.  Remaining Step 3 (field assembly ≈ 450
  lines: generic extractor + perturb extraction + sym/X glue + two `hfull` re-derivations + integrate +
  realizedFam sum) is genuinely multi-session as the recon estimated; fully designed in
  `DeTurckLieKernelL2JetBound.md` §"Remaining field assembly".  (N) `ricci_flow_unif_existence` still
  **0%** (kernel top-separation is machinery toward the field-level lift of `deTurckLieCoeffField`,
  the 1st of 2 genuinely-missing C₀ constituents).

## Status log — DLa field lift LANDED (session 2, 2026-07-24)

- **Piece 4 (field-level lift) BUILT + VERIFIED** in `DeTurckLieKernelL2JetBound.lean`
  `section DLaGridBrick` (+971 lines).  Public DLa ENDPOINT now exists:
  `deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated` (+ per-order sibling), landing
  `∑_{i≤a}‖∇^i(deTurckLieDLaCoeffField g₀ (realizedFam …) g_bg)‖² ≤ Ktop·(∑_{j<a+3}(‖∇^jT‖²+‖∇^jT'‖²))
  + Kc·(1+∑_{j<a+3}(‖∇^jT‖²+‖∇^jT'‖²))` via `jetL2_sum_lowShift a 2 3`.
- Realized decls: `gridSplit_dla` (pure-real top-cell split), `appCcGrid_le_dla` (shared full-grid,
  window `(i'+1)(l+3)→(i+3)` for BOTH extractions), `exists_rfns_dLaLowered_topsep` (4.2, raise-eq into
  piece 3), `exists_rfns_dLaSym_topsep` (4.3+4.4), `rfns_iCG_dLaField_topsep` (4.5), `sum_shift_le` +
  `jetL2_sum_lowShift`, and the two `…_realizedFam_jetL2_{perOrder,summed}_topSeparated` endpoints.
- **Constant discipline PASSED**: `Ktop = CPT0·fr²·8·256·Kt0·(1+fr⁵δ₀²)·(appCcGdiag a)²` — only
  `(CPT0, fr=finrank, Kt0, δ₀, appCcGdiag a)`, i.e. `(g₀,g_bg,hδ₀)`-level and R-FREE; NO `‖T‖_top`
  products.  `R` lives ONLY in `Kc` (tame-window integrator `K`).  The two i-dependent `appCcGdiag i`
  powers (from the two nested appCcRS extractions) stay EXPLICIT in the producer statements and
  collapse to one fixed `Ktop` at the summed layer via `appCcGdiag i ≤ appCcGdiag a`
  (`pow_le_pow_right₀`); a `1 ≤ appCcGdiag i` lift keeps each producer's top a single power.
- Verification: focused `lake env lean` whole-file EXIT=0 zero-errors/zero-warnings after 3 fixes on the
  two lowest helpers (gridSplit `hrest` nonneg witness; `one_le_appCcGdiag` PRIVATE upstream → inlined
  `one_le_pow₀`; `dLaSym hG1` `add_le_add_right` arg-order → `add_le_add … (le_refl _)`).  Direct-lean
  axiom audit on both endpoints ⇒ `[propext, Classical.choice, Quot.sound]` (audit lines stripped).
  Diff scope = the brick's own files only.
- **Next frontier (NOT this session): DLb + combined assembly.**  (a) DLb top-separated summed producer
  in `DeTurckVectorFieldL2JetBound.lean` (`deTurckLieDLbCoeffField`); (b) combined-coefficient assembly
  `‖∇^i deTurckLieCoeffField‖² ≤ 2‖∇^i DLa‖² + 2‖∇^i DLb‖²` summed via
  `deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField`.  Then `deTurckLieCoeffField` (ruling item 2's
  1st constituent) is DONE.  (N) `ricci_flow_unif_existence` still **0%** — this is a C₀-constituent
  producer far below (N).
- 2026-07-24: **DLb session — recon + head; two findings for planner ruling.**  Recon of the DLb
  top-separation in `DeTurckVectorFieldL2JetBound.lean` (notes in `DeTurckVectorFieldL2JetBound.md`).
  (1) **STRUCTURAL — endpoint location.**  `deTurckLieDLbCoeffField_realizedFam_jetL2_*_topSeparated`
  CANNOT be stated in this file: `deTurckLieDLbCoeffField` is defined in the SIBLING
  `DeTurckLieKernelL2JetBound.lean:60`, and the (2,2)↔(1,1) slotInsert bridge
  `deTurckLieDLbCoeffField_eq_slotInsert_sum` lives further downstream in
  `DeTurckLieCoeffL2JetBound.lean:47` (imports both).  So the DLb split is asymmetric to DLa: the
  editable file hosts the INSERT-level producer `deTurckLieWEndoInsert_realizedFam_jetL2_*_
  topSeparated` (upgrading the ball-uniform :3041); the FIELD endpoints are a THIN downstream wrapper
  (× `4·finrank`, R-free), mirroring the ball-uniform field wrapper
  `deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_ballUniform` (`DeTurckLieCoeffL2JetBound.lean:244`).
  №15 located the producer "near :3041" (insert level) but named it `deTurckLieDLbCoeffField_…`;
  resolution = build insert-level here, dispatch the field wrapper against `DeTurckLieCoeffL2JetBound.lean`.
  (2) **ROUTE SIMPLIFIED — no private arm1 machinery.**  The wOmega layer's appCc two-arm grid has a
  metric-coefficient arm (cometricCastG0) that carries P-content; naively its remainder needs the
  `boundedFactorGridWindow` currency + cometricCastG0 grid bound (`rfns_iteratedCovGrad_cometricCastG0_
  gridWindow_le`, PRIVATE in `CurvatureArm1KoszulTopSeparation.lean:35`).  AVOIDED: since
  `jetL2_sum_lowShift`'s per-order remainder is `Kc i·(1+∑low)`, the `Kc i·1` slot absorbs ANY
  ball-uniform (R-dependent) constant, so the ENTIRE sub-top remainder integrates BALL-UNIFORMLY
  (existing two-arm integrator + F_B) and only the single top `∇^{i+2}P` needs R-free separation.
  Stays fully in-file/in existing machinery.  Route ≈300–500 lines (5 L2-chaining lemmas + wrapper +
  summed), turnkey recipe in the `.md`.
  Progress: BATCH 1 (`exists_rfns_connDiff_topsep` = connDiffSection pointwise top-sep in public
  `antidiagonalTupleGridWindow` currency, + `engineRem_le_grid` reshape + `sum_shift_le` +
  `jetL2_sum_lowShift`) WRITTEN in `section DLbTopSeparated`, desk-checked (mirrors the verified DLa
  `exists_rfns_connDiffSection_topsep_dla`).  **Focused check + axiom audit PENDING** — foreign lean
  lanes were near-continuous during the session (heavy builds contending; verify window not secured).
  Kept the file at batch-1-only so the first window confirms the head clean.  Ktop plan R-free:
  `2·appCcGdiag(a+1)·cΦ0·2·2Kt0`.  (N) still **0%**.
- 2026-07-24 (cont.): **3 of ~6 DLb tower layers VERIFIED GREEN.**  Secured verify windows (foreign
  lanes intermittent).  `section DLbTopSeparated` now has (all whole-file `lake env lean` EXIT=0,
  zero errors, zero new warnings, live/not-cached): `exists_rfns_connDiff_topsep` (connDiffSection
  pointwise top-sep, public grid currency), **`connDiff_L2_topsep`** (connDiffSection L2 top-sep —
  the crux L2-integration idiom PROVEN: `normSq_le_integral_of_pointwise_fiberNormSq_le_rs` + the
  tame-window integrator `antidiagonalTupleGrid_integral_ballUniform_tameWindow` + `hPball` (k+1)R²
  conversion; the biggest route uncertainty is now retired), `wXi_L2_topsep`.  No axiom audit yet
  (these are intermediate helpers, not endpoints; EXIT=0 confirms sorry-free).
- **DECISION POINT for the planner (changes remaining effort a lot).**  Does the DLb endpoint need a
  GENUINE positive `Ktop` on `‖∇^{i+2}T‖²` (like DLa, whose leading `wAlphaA = ∇^{i+1}wOmega ~
  ∇^{i+2}T`), or may it use **`Ktop = 0`** — reusing the existing ball-uniform
  `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform` (:3041) via `P i ≤ 0·top + P i·(1+
  low)` (`low ≥ 0`), exactly the **traceHessian** constituent's accepted route
  (`TraceHessJetL2Summed.md`)?  The endpoint SHAPE and the R-free-`Ktop` discipline are satisfied by
  BOTH; the combined `deTurckLie` top is then `2·Ktop_DLa` (R-free) with DLb folded into `Kc`.
  - If `Ktop = 0` acceptable: the insert endpoint + field wrapper are ~40+40 lines reusing :3041 —
    near-immediate.  The 3 genuine layers already built stay reusable if you later want it tight.
  - If GENUINE required (DLa-sibling reading): remaining = wOmega_L2 corner peel (the crux; recipe in
    `DeTurckVectorFieldL2JetBound.md` — `iteratedCovGrad_appCcRS_eq_argCorner_add_lower`
    `OperatorFieldFibreNormJet.lean:1410` + `rfns_iteratedCovGrad_appCc_coeffLower_le` :1372), then
    wAlpha_L2 + wrapper + `jetL2_sum_lowShift a 2 3`, then the downstream field wrapper in
    `DeTurckLieCoeffL2JetBound.lean`.  ~300 lines, multi-session.
  My default absent a ruling: GENUINE (sibling of DLa); the 3 verified layers are that foundation.
