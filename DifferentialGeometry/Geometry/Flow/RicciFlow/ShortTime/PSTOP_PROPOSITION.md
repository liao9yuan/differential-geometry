# P-STOP: the stopped projected bottom-scale energy proposition (v5, 2026-08-04)

Status: **CLOSED — PASSED-WITH-ADAPTERS** (v5 adds two: §6.4 G/H).
See §10 for the verdict, the
adapter list, and the instruction for the first brick.  This document is
the RULING2-mandated gate (Pro item (i)): no E1′/E4/G4 Lean work until
the proposition is verified on paper or refuted.  The gate is now OPEN,
with a narrower lane than originally scoped.  Ledger: No. 115/116.

History: v1 (2026-08-03) setup + absorption arithmetic, §6 open;
v2 refuted the self-dependent route and forced the tower-direct form;
v3 (2026-08-04) projected maximal regularity dissolved first-exit;
v4 (2026-08-04) READ-ONLY Lean audit of §6.1(a)/(b), §7 and the landed
ladder shapes — one substantive correction (§6.1(ii)), §7 rewritten from
compactness+uniqueness to fixed-point stability, verdict issued;
v5 (2026-08-04) §6.4 re-prices the tower-direct rungs with the `L^∞`
embedding cost that §6.3's budget check omitted — §6.3 corrected, the
`k = 3` derivation displayed, two new adapters (G, H).
Everything below is paper work; it moves no Lean.

## 1. Objects (all in the g₀-rebased spectral frame)

Closed M³, individual smooth g₀ (the rebased route, G-2 adapter 1).
Spectral scales `H^k := tensorHs g₀ 0 2 k` via the connection Laplacian
Δ of g₀ on (0,2)-tensors; eigenmodes `e_i`, eigenvalues `λ_i ≥ 0`,
`‖U‖²_{H^k} = Σ_i (1+λ_i)^k u_i²`.  Galerkin space `V_N = span(e_1…e_N)`,
projector `Π_N` (spectral truncation).

Two structurally FREE facts (Pro R-2 requirement 1 — verified by the
spectral form, no Lean risk):
- `‖Π_N‖_{H^m → H^m} ≤ 1` for every m (diagonal truncation);
- `Π_N` commutes with Δ, resolvents, and the heat semigroup.
No inverse inequality can enter unless written by hand — the watch item
is only that no lemma SMUGGLES `λ_N` in (stop signal 1).

Spectral identities (these make the parabolic constant exact):
`E_k(U) := ‖U‖²_{H^k}`,  `D_k(U) := Σ λ_i (1+λ_i)^k u_i²`,
`E_{k+1} = E_k + D_k`,  and along `∂_t U = −ΔU + f`:
  d/dt E_k = −2 D_k + 2⟨f, U⟩_{H^k}.
So the coercivity constant is c_par = 1 EXACTLY — no norm-equivalence
or Gårding loss in this frame.  (Pro R-5's "after including any
norm-equivalence constants" resolves cleanly here.)

## 2. The projected system

E4's system, per §7.3: for `U_N : [0,T] → V_N`, `U_N(0) = 0`,
  ∂_t U_N = −Δ U_N + Π_N 𝒩(U_N),      𝒩(V) := N_sm(V) = static + (𝒩(V) − 𝒩(0)),
with `N_sm = deTurckSmoothN g₀ g₀ 2 ∘ (ball data)` the smooth core (the
bridge `hbridge` identifies it with `liftHiN … FHi` on the H² R-ball —
S0's widened frontier makes this available; E3's `finiteEigenComboHs_eq`
lets it act on Galerkin states).

Ladder inputs (Lean status in brackets):
- a₂ arm [PROVED, `a2_ladder`]:  ‖a₂(V)W‖_{H^m} ≤ Cδ·‖W‖_{H^{m+2}}
  + C₂(m, R₀)·‖W‖_{H^{m+1}},  Cδ = κ·δ/(1−δ)², κ m-FREE, gate 3 ≤ a,
  ball ‖V‖_{H^{a+2}} ≤ R₀.
- a₁ arm [designed, A1c]:  ‖a₁(V)W‖_{H^m} ≤ C₁(m, ·)·‖W‖_{H^{m+1}}.
- coefficient towers [c2 proved; c1/c0 stated over `low1Ker_jet` /
  `selfLow_jet`; C0 needs the H³-cap thread per R-3].
- combined [A1d `n_diff_hm_rung`, designed]:
  ‖𝒩(V) − 𝒩(0)‖_{H^m} ≤ Cδ·‖V‖_{H^{m+2}} + C(m, ·)·‖V‖_{H^{m+1}}.

## 3. The pairing and absorption arithmetic (VERIFIED on paper)

Spectral Cauchy–Schwarz with weight split (1+λ)^k = (1+λ)^{(k−1)/2}·
(1+λ)^{(k+1)/2}:
  ⟨f, U⟩_{H^k} ≤ ‖f‖_{H^{k−1}} · ‖U‖_{H^{k+1}}.
Apply with f = Π_N(𝒩(U) − 𝒩(0)) (projector drops, norm ≤ 1) at scale
k−1 via the combined ladder:
  ⟨𝒩(U)−𝒩(0), U⟩_{H^k}
    ≤ (Cδ·‖U‖_{H^{k+1}} + C(k−1)·‖U‖_{H^k}) · ‖U‖_{H^{k+1}}
    ≤ (Cδ + ε)·E_{k+1} + (C(k−1)²/4ε)·E_k
    =  (Cδ + ε)·D_k + (Cδ + ε + C(k−1)²/4ε)·E_k          [E_{k+1}=E_k+D_k]
and the static part
  ⟨𝒩(0), U⟩_{H^k} ≤ ε·E_{k+1} + (1/4ε)·‖𝒩(0)‖²_{H^{k−1}}.
Hence
  d/dt E_k ≤ −2(1 − Cδ − 2ε)·D_k + A(k)·E_k + (1/2ε)·‖𝒩(0)‖²_{H^{k−1}},
  A(k) := 2(Cδ + 2ε + C(k−1)²/4ε).

ABSORPTION CONDITION (R-5, resolved):  Cδ = κ·δ*/(1−δ*)² < 1 − 2ε.
Since c_par = 1 exactly, the required internal fibre radius is
  δ* = min{ 1/3, δ_abs(κ) },   δ_abs solving κ·δ/(1−δ)² = 1/2 (say),
and the state-radius cap must place the realized trajectory's fibre
operator bound ≤ δ*.  κ is a fixed Lean-side constant of `a2_ladder`;
exposing it (or re-running the ladder's final constant assembly with an
explicit bound) is brick A2-ABS.  This kills stop-signal 8 IF κ is
finite and explicit — no structural obstruction.

Requirement-4 shape (VERIFIED): the source enters as ‖𝒩(0)‖_{H^{k−1}}
on the RIGHT only.  For rungs k ≥ 3 this is the ORDER-(k−1) static
force — a PER-DATUM high norm.  It must never constrain T; see §5.

Requirement-1/3 shapes (VERIFIED at this level): projector norm ≤ 1;
A(k) multiplies E_k (Pro's benign form C(m)·E_m); the dissipation D_k
keeps a fixed margin (1 − Cδ − 2ε) > 0 independent of k and N.

## 4. Grönwall at a fixed rung (VERIFIED, conditional on §6)

With U(0) = 0 (zero seed) and the margin positive:
  sup_{t≤T} E_k(t) ≤ (e^{A(k)·T} − 1)/A(k) · (1/2ε)·‖𝒩(0)‖²_{H^{k−1}}
                  =: Φ_k(T; A(k), static_{k−1})
and ∫₀^T D_k ≤ (same order).  Φ_k is monotone in T and in its
constants; NO shrinking of T is used at any rung — the same-horizon
claim holds AT THIS LEVEL.

## 5. The per-datum exit radii, chosen AFTER T (the requirement-4/5 mechanism)

Order of choices (this ordering is the whole point):
1. τ₀ and the state radius are chosen from CLASS data alone (front 3):
   absorption δ*, the k ≤ 2 closure (already-built bottom rungs +
   state ball), and the order-1 static force.  τ₀ NEVER sees a high
   static norm, an H⁵ ball, or an exit radius (stop-signal 9 guard).
2. With T = τ₀ FIXED, define the exit radii UPWARD and PER DATUM:
   R₃² := 2·Φ₃(τ₀) + 1, then R₄² := 2·Φ₄(τ₀; C(·, R₃…)) + 1, then
   R₅² := 2·Φ₅(τ₀; …) + 1.  Each Φ uses only constants already fixed
   at its turn.  The stopped estimate at rung k then gives the STRICT
   improvement `sup E_k ≤ Φ_k < R_k²/2` on the full [0, τ₀] — the
   first-exit time can only be τ₀ (requirement 5), uniformly in N
   (every constant above is N-free).
This mechanism is SOUND provided the Grönwall coefficient A(k) at rung
k depends only on radii ALREADY chosen (R_j for j ≤ k) — which is
exactly §6.

## 6. THE CENTRAL OPEN CHECK: cross-scale coefficient dependence

The danger (sharpens Pro's R-2 caveat): `a2_ladder`'s PROVED form
consumes the H^{a+2} = H⁵ ball at LOW rungs — the master engine's
`hballf` reaches f 5 already at rung m = 2 (f(i+m+dc), a = 3, t = 0,
dc = 3).  If the rung-k Grönwall coefficient A(k) (through C(k−1, R₀))
depends on the H⁵ radius R₅ for k ≤ 4, then §5's upward ordering is
CIRCULAR ACROSS SCALES: A(3) would need R₅, which is chosen after Φ₄,
which needs A(4), which needs R₅ … — and the proposition FAILS AS
DESIGNED.  (This is invisible at any single rung; it is a dependence-
GRAPH condition.)

RESOLUTION (v2 analysis, 2026-08-03 evening — the self-dependent
route is now REFUTED on paper, which FORCES the tame form):

Step 1 — the self-dependent route violates requirement 4.  Suppose the
top stopped rung's Grönwall coefficient sees its own radius:
A(5) = C(R₅) with C at least linear.  The improvement condition reads
  R₅² ≥ 2·e^{C(R₅)·T}·S,     S := the per-datum static source term.
At FIXED T this crossing exists only while C(R₅)·T stays ≲ ln R₅, i.e.
only for T ≲ (ln R₅)/C(R₅) → the admissible T is CONSTRAINED BY S
(through the size R₅ must have) — a per-datum high norm restricting
the horizon, which is exactly what requirement 4 forbids.  So ANY
design in which a stopped rung's coefficient depends on that same
rung's radius is dead — Pro's danger (a) is not a risk but a theorem.

Step 2 — the ladder's ball-absorbed form is the WRONG interface for
the stopped rungs; the TOWERS' jet-explicit form is the right one,
and it already exists.  The H⁵ ball enters `a2_ladder` only at the
Hs-ASSEMBLY step (the engine absorbs the coefficient-jet sums into
the constant USING the ball: `hballf` at `f(i+m+dc)` ≤ f 5).  But the
underlying coefficient estimates — the TOWERS — are jet-EXPLICIT with
δ-only constants:
  lowJetSq_i(C2-coeff) ≤ Kc(i)·(1 + Σ_{j<i+2} ‖∇^j T‖²),
(c2 proved; c1/c0 stated, C0 with the H³ cap after the R-3 repair).
Pairing the towers DIRECTLY in the rung-k energy identity keeps the
state jets EXPLICIT and LINEAR-in-E: the jet sums are Σ_{j≤k+1}‖∇^jU‖²
≈ E_{≤k+1}-terms, which land as (already-controlled E_{≤k}) + (D_k
absorbed by the δ-margin) — the tame-and-triangular structure Pro
described, with NO radius inside any constant.  The k-uniform TOP
part is untouched (`lowData_split`'s δ-only constant).

CONSEQUENCES:
- No new low-rung ladder variant is needed as a first resort: the
  stopped bottom system (rungs 3–5) should be assembled from the
  TOWER estimates + `appRS`/pairing algebra, bypassing `a2_ladder`;
  `a2_ladder`'s ball-absorbed form remains the right interface for
  the HIGH rungs (k ≥ 6), where R₅ is already fixed — the dependence
  graph is then triangular by construction and §5's ordering closes.
- The paper obligation that remains is to WRITE the rung-3..5 pairing
  once, with the towers' `range (i+2)` budgets checked against the
  spectral Cauchy–Schwarz split of §3 (the budgets match: pairing at
  H^{k−1} consumes coefficient jets ≤ k+1, state jets ≤ k+1 — inside
  E_{k+1} = E_k + D_k), and to confirm the a₁/a₀ arms' stopped-rung
  assembly likewise keeps jets explicit (their towers are `range
  (i+2)` with the H³ cap — same shape).
- Fallback (b) (single coupled radius) is REFUTED by Step 1 except in
  the sub-logarithmic-C regime, which we cannot certify — discard.
- (c) (engine t-threshold rung-local rerun) is now moot unless the
  tower-direct pairing hits an unexpected budget mismatch.

VERDICT CRITERION for P-STOP (unchanged in substance, sharpened in
route): the proposition stands iff the rung-3..5 tower-direct pairing
closes with jets explicit and constants from {δ*, H³-cap, class data,
already-chosen radii} only.  The §3 arithmetic strongly indicates it
does; writing it out is the remaining §6 work.

### 6.1 The rung-3..5 closure (v3, 2026-08-04) — first-exit DISSOLVED

THE KEY OBSERVATION (projected maximal regularity): the spectral
projector `Π_N` commutes with Δ, the resolvents, and the heat
semigroup, and is norm-nonincreasing on every `H^m` (§1).  Therefore
the ENTIRE A1 fixed-point solve replays VERBATIM at the projected
level: `Π_N ∘ 𝒩` is Lipschitz on the same `H²` ball with the SAME
constants (projection eats nothing), the Duhamel map has the SAME
maximal-regularity constants, and the contraction closes on the same
radius `P` and horizon `T`.  Consequences, all N-UNIFORM and
CLASS-uniform:
  (i)  `‖U_N(t)‖_{H²} ≤ R` for a.e. `t`      (projected state ball);
  (ii) `‖U_N‖_{L²_t H³} ≤ B₃ := (1+T)·R/4`   (projected MR bound).
(ii) is the point: the H³ quantity that the C0 tower's `L∞(∇P)` cap
consumes is an A-PRIORI CLASS BOUND for the approximants — NOT a
stopped radius.  Nothing at any rung refers to its own (or a later)
exit radius, so:

CORRECTION (audit, 2026-08-04) — v3 claimed `C_tH³ ∩ L²_tH⁴` here.
That is NOT what the A1 solve delivers and it is not needed.  The
solve runs at `a = 1`: forcing in `L²_tH¹` with `‖gforce‖ ≤ R/4`
(`partial_sol_const`, `…/TensorMaximalRegularity/PartialForcingFixedPoint.lean:195`),
field in `L²_tH³` with `‖field‖ ≤ (1+T)‖gforce‖`
(`maximalRegularitySolField_norm_le`,
`…/TensorMaximalRegularity/LocallyLipschitzExistence.lean:363`).  There is
no `L²_tH⁴` and no `C_tH³` at `a = 1`; getting them would need the solve
re-run at `a = 2`, whose `partial_sol_const` hypothesis `hsingle` carries
a `max‖·‖_{H³}` prefactor — one full scale above what the difference-tame
layer (`c0Diff_tame` / `bg0_pair_h1` / `a1Sub_lo_tame`, the H¹/H²/H³
pair) delivers.  So that route is NOT available.
It is also not needed, because the C0 cap enters the rung-`k` Grönwall
coefficient QUADRATICALLY (the `∇P·∇P` symbol of R-3), so
  `A(k)(t) ≤ class + C·‖U_N(t)‖²_{H³}`,
which is `L¹` in `t` with `∫₀^T ‖U_N‖²_{H³} = ‖U_N‖²_{L²_tH³} ≤ B₃²` —
N-free and class-uniform.  Grönwall with an `L¹_t` coefficient is
standard and gives `sup_t E_k ≤ exp(∫A(k))·Φ_k` with NO restriction on
`T` beyond the already-fixed `τ₀`.  Every requirement below survives
verbatim under this substitution; only the word `C_tH³` changes to
`L²_tH³` and `A(k)` becomes a time-integrable coefficient.

RUNG-3..5 CLOSURE, tower-direct (per §3's pairing):
  d/dt E_k(U_N) ≤ −2(1 − Cδ* − 2ε)·D_k
                 + A(k; δ*, B₃, class)·(Σ_{j≤k} E_j)
                 + (1/2ε)·‖𝒩(0)‖²_{H^{k−1}},
with the coefficient jets bounded by the TOWERS (C2: δ-only; C1:
ball-free; C0: `K(i, B₃)` via `‖∇U_N‖_∞ ≲ ‖U_N‖_{H³} ≤ B₃`), the
state jets explicit and landing on `E_{≤k}` (triangular) or absorbed
into `D_k` by the δ*-margin.  Zero seed ⟹ Grönwall on the FULL [0,T]
gives `sup_t E_k ≤ Φ_k(T; class, ‖static‖_{H^{k−1}})`, k = 3,4,5,
sequentially (A(k) sees only E_{≤k}, all previously closed).
Per-datum high statics sit on the right only (requirement 4 ✓); T is
never restricted (requirement 5 ✓); every constant is N-free
(requirements 1–3 ✓); the rungs are coupled only downward
(requirement 6 ✓).

THEN DEFINE `R₅ := (2Φ₅)^{1/2} + 1` — a per-datum number — and hand
it to the `a2_ladder`-based HIGH rungs (k ≥ 6) of the σ-hierarchy as
their (now fixed, harmless) `H⁵` ball radius.  NO first-exit
argument, NO stopped system, NO retraction is needed anywhere:
R0's option-2 machinery dissolves into (projected MR) + (plain
Grönwall).  Pro's six requirements are met with room to spare, and
Pro's "coupled bottom scales" requirement is satisfied trivially
(downward coupling only).

### 6.2 Residual checks — RESOLVED (audit, 2026-08-04)

**(a) The MR engine accepts projected forcing: VERBATIM-APPLICABLE.**
The forcing slot is an ARBITRARY element of the time-`L²` space, with
no structural side condition anywhere in the chain:

* `maxRegDuhamelSolField` / `maxRegDuhamelSolFieldHa1` / `maxRegDuhamelMap`
  (`…/TensorMaximalRegularity/SolutionSpace.lean:582 / :596 / :613`) all take
  `gforce : timeL2 (tensorHs g r s a) T` bare;
* the only side hypotheses in the whole family are `hT : 0 < T`,
  `hT1 : T ≤ 1` and `h_compact : IsCompactOperator (tensorResolventL2 g r s)`
  — background operator facts, independent of the forcing;
* the constants are forcing-generic: `maximalRegularityOp_norm_le`
  (`…/MaximalRegularity/Operator.lean:657`) gives `‖MR f‖_{H¹([0,T];Hᵃ)} ≤ 2‖f‖`;
  `maximalRegularitySolField_norm_le`
  (`…/TensorMaximalRegularity/LocallyLipschitzExistence.lean:363`) gives
  `‖solField f‖_{L²(H^{a+2})} ≤ (1+T)‖f‖`;
  `maxRegDuhamelMap_dist_le` (`SolutionSpace.lean:688`) gives the `2`-Lipschitz
  dependence on the forcing.

And `Π_N` on that exact space ALREADY EXISTS:
`timeL2EigenProj g σ T N : timeL2 (tensorHs g 0 2 σ) T →L[ℝ] …`
(`…/HeatSemigroup/TimeL2EigenProjection.lean:189`), built from the spatial
CLM `spatialEigenProj` (`:66`), with `norm_timeL2EigenProj_le_one` (`:194`),
`norm_spatialEigenProj_apply_le` (`:83`) and — decisive for §7 —
`timeL2EigenProj_tendsto` (`:199`): `Π_N x → x` strongly for every `x`.
So `Π_N f` is literally an inhabitant of the forcing slot.  NO adapter is
needed for (a).

**(b) The A1 Lipschitz input is operator-level: REUSABLE-AS-STATED**
— and stronger than v3 assumed.  The A1 fixed point is NOT built on an
inline Lipschitz estimate.  Its engine is the public

  `partial_sol_const`
  (`…/TensorMaximalRegularity/PartialForcingFixedPoint.lean:195`),

whose nonlinearity data are four explicit HYPOTHESIS SLOTS on the
ball-restricted map `Nfun : lowerState g₀ a R → tensorHs g₀ 0 2 a`:

    hLip    : LipschitzWith L Nfun
    hsingle : ‖Nfun u − Nfun u'‖ ≤ C₁·max(‖u‖_{a+1},‖u'‖_{a+1})·‖u−u'‖_{a+2}
                                   + C₂·‖u−u'‖_{a+1}
    hzero   : ‖Nfun 0‖ ≤ D
    hsmall  : C₁·R ≤ 1/8

and whose conclusion is a CLOSED-FORM horizon
`T₀ = min 1 (min (1/(64(C₂+1)²)) ((R/4)/(2(D+1)))²)` together with the
Duhamel identity, the a.e. state ball, the Nemytskii identity,
`trace0 u = 0`, the PDE `timeDeriv u = timeScaleLaplacian field + gforce`,
and `‖gforce‖ ≤ R/4`.  Nothing is fused into the proof.  (The DeTurck
instantiation is `lowreg_partial_sol_of_bounds`, `ShortTime/UnifClassBounds.lean:263`,
feeding `lowregNfun` through `hcont`/`htame`; the generic forcing-space
Lipschitz algebra is `nonautL2_dist_le`,
`…/TensorMaximalRegularity/NonautonomousL2.lean:213`, and the affine
uniqueness `affine_unique`, `…/NonautonomousL2Lift.lean:465`, is private.)

CONSEQUENCE — this is the concrete verification of §6.1's central claim.
`Π_N ∘ Nfun` satisfies ALL FOUR slots with the SAME `L, C₁, C₂, D`
(each by one application of `norm_spatialEigenProj_apply_le`), hence
`partial_sol_const` returns the SAME `T₀` and the SAME forcing radius
`R/4` for the projected system.  "Same radius, same horizon, N-free" is
not an analogy — it is the identical closed formula in identical inputs.

**(c) C1/C0 tower threading** — unchanged as a design constraint, and now
sharper: with (ii) corrected to `L²_tH³`, the C0 cap must be threaded at
`a = 1` (ball `H³`).  If `selfLow_jet` is threaded at `a = 3` (`H⁵`),
rungs 3–5 cannot feed it and the surgery must be re-cut to the `H³` cap.
(A1-CUR closed both towers unconditionally; this is about which `a` the
consumer instantiates, not about the towers' proofs.)

**(d) E4 simplification: CONFIRMED and now mandatory.**  With
`partial_sol_const` applied to `Π_N ∘ Nfun` there is no Galerkin ODE to
construct at all — the projected trajectory IS a `partial_sol_const`
output.  E4's ODE-existence brick should be deleted from the lane, not
merely simplified.  G4 changes too — see §7.

**(e) NEW, found by the audit — the one genuinely load-bearing adapter.**
The energy identity of §1 (`d/dt E_k = −2D_k + 2⟨f,U⟩_{H^k}`) needs
`t ↦ E_k(U_N(t))` absolutely continuous, i.e. it needs the projected
trajectory to stay in `V_N`.  That is TRUE and mechanical but NOT yet a
lemma: `maximalRegularitySolField_timeModeCoeff`
(`…/MaximalRegularity/Operator.lean:491`) gives
`timeModeCoeff (solField f) i = solModeCoeff f i`, and
`solModeCoeff` (`:88`) is `perModeConvL2 λᵢ (timeModeCoeff f i)` — a
function of mode `i` of `f` ALONE.  So modes of `f` outside
`eigenIdxFinset N` produce zero modes of the field, i.e. `Π_N` commutes
with the whole Duhamel family.  One short modewise lemma; see §10 adapter A.

Once `U_N(t) ∈ V_N`, everything the rung-3..5 pairing needs about the
state is available on SMOOTH tensors: `finiteEigenComboHs_eq`
(`…/DeTurck/DeTurckRemainderDefs.lean:119`) identifies a finite
eigen-combination in `H^σ` with `smoothCcToTensorHs σ (finiteEigenCombo …)`,
so the towers, the difference-tame layer and the jet↔`H^k` bridges — all
stated on `SmoothCcTensor` — apply to Galerkin states DIRECTLY.  This is
a real advantage of the projected route that v3 did not record: the
approximants are smooth, while the A1 trajectory itself is only `H³`
(which is why `lowRegN` had to be a `Dense.extend`).

### 6.3 Ladder-shape consistency against the LANDED statements

Re-checked §3–§5 and §6.1 against the shapes actually proved (A1c/A1d,
`…/DeTurck/LowRegLadderRung.lean`):

* `a2_ladder` (`:233`) — one small constant `κ·δ/(1−δ)²` on `‖T‖_{H^{m+2}}`,
  `κ` m-free, gate `3 ≤ a`, ball `‖T‖_{H^{a+2}} ≤ R₀`.
* `a1_ladder` (`:407`) — κ-FREE, `Clower m·‖T‖_{H^{m+1}}`, gate `2 ≤ a`.
* `n_diff_hm_rung` (`:542`) — the combined form §3 consumes, gate `3 ≤ a`.
* towers (`c0_jet_tower`, `c1_jet_tower`, `selfLow_jet`) — jet-explicit,
  gate `1 ≤ a`, stated on `SmoothCcTensor`.

§3's arithmetic uses EXACTLY `n_diff_hm_rung`'s shape (one small constant
on `H^{m+2}`, everything else on `H^{m+1}`, both uniform in `m`).  NO
mismatch.

§6.1's tower-direct pairing at rungs 3–5 converts to the spectral `H^k`
pairing of §3 through bridges that EXIST, in both directions, at
`…/Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean`:

* `hsJet_le` (`:834`) and its rank-(0,2) form
  `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs` (`:1021`):
  `Σ_{j≤n}‖∇^j S‖ ≤ C·‖S‖_{H^n}`;
* `hs_le_jet` (`:855`): `‖S‖_{H^n} ≤ C·Σ_{j≤n}‖∇^j S‖`;

and `lowJetSq g m S = Σ_{q≤m}‖∇^q S‖²`
(`…/DeTurck/DeTurckRemainderLowBaseAction.lean:2871`) differs from the
bridges' jet sum only by a finite Cauchy–Schwarz.  All four are on
`SmoothCcTensor`, which by §6.2(e) is exactly where the Galerkin states
live.

BUDGET CHECK — **SUPERSEDED BY §6.4, WHICH CORRECTS IT.**  The paragraph
below is kept verbatim because §6.4's correction is stated against it.
It is WRONG as written: it prices only the Leibniz term `l = 0` and omits
the `L^∞` conversion that every `l ≥ 1` term needs.

> Pairing at rung `k` costs `‖𝒩(U)−𝒩(0)‖_{H^{k−1}}·‖U‖_{H^{k+1}}`.
> Estimating the `H^{k−1}` factor tower-directly: the towers' `range (i+2)`
> window at `i = k−1` reaches state jets `j ≤ k`, i.e. inside `E_{≤k}` —
> strictly BELOW `E_{k+1}`, so the coefficient side is triangular with room
> to spare; the a₂ arm's own two derivatives on the state give the single
> `‖U‖_{H^{k+1}}` factor, which is the one absorbed by the δ*-margin
> through `E_{k+1} = E_k + D_k`.  The budgets match, in the direction that
> has margin.  §6.1's parenthetical said "coefficient jets ≤ k+1"; the
> true window is `≤ k`, which is better, not worse.

CORRECTED SUMMARY (details and the displayed derivation in §6.4).  The
`H^{k−1}` factor is not one Leibniz term but `k` of them; only `l = 0`
is priced above.  For `l ≥ 1` ONE factor must go to `L^∞`, and the tree's
sup embedding charges `+2` `L²`-orders.  The worst term is `l = k−1`,
`‖∇^{k−1}C₂‖_∞·‖∇²U‖_{L²}`, which needs the a₂ tower at index `k+1`.
With the LANDED `range (i+2)` window that reaches state jets `j ≤ k+2` —
**ABOVE `E_{k+1}`, i.e. circular**, not "triangular with room to spare".
With the window sharpened to `range (i+1)` (free — the proof already
gives it, §6.4 exhibit) it reaches `j ≤ k+1`, landing exactly ON
`E_{k+1}` with coefficient `K_R·R` (`R` = the class `H²` ball).  So the
budget is tight to ONE order and closes only after §6.4's two adapters
and the strengthened absorption condition `Cδ* + K_R·R + 2ε < 1`.

ONE UNRESOLVED NUMERICAL PREMISE (R-5's, unchanged in substance, now
localized to a binder).  `a2_ladder` and `n_diff_hm_rung` bind `{δ}`
BEFORE `∃ κ`, so as STATED `κ` may depend on `δ` and the absorption
choice `δ* = min{1/3, δ_abs(κ)}` is formally circular.  It is not
circular in substance: `κ` is inherited unchanged from `lowData_split`
(`…/DeTurck/DeTurckRemainderLowBaseAction.lean:3841`), whose
`∃ K, 0 ≤ K ∧ ∀ T … {δ} …` quantifies `K` BEFORE `δ` — the constant is
δ-free.  So A2-ABS is a binder hoist in `a2_ladder`, propagated to
`n_diff_hm_rung`, not new mathematics.  It is nevertheless REQUIRED: the
absorption condition `Cδ < 1 − 2ε` is not certified until it lands.

### 6.4 RE-PRICING the tower-direct rungs with the `L^∞` cost (v5, 2026-08-04)

**VERDICT: HOLDS-WITH-ADAPTERS at rungs 3–5.**  Two adapters, one free and
one a numerical strengthening of §3's absorption condition; §6.3's BUDGET
CHECK is wrong as written and is corrected above.  Read-only paper work,
prompted by executor report No. 148-executor (PLAN5): M3 proved the LADDER
cannot serve rungs 3–5 (`A ≥ 4` forced) and flagged that §6.3 omitted the
same `L^∞` cost.  It did.  The tower-direct route pays that cost too — but
it pays it with the class `H²` radius `R` instead of an `H⁵` ball, which
is why ruling No. 149 (rungs 3–5 tower-direct, ladders for `k ≥ 6`)
survives.  M3's `A ≥ 4` does NOT transfer; see "why the routes differ".

**THE OMITTED COST.**  `‖𝒩(U)−𝒩(0)‖_{H^{k−1}}` is not one estimate but a
Leibniz sum.  For the a₂ arm `appCc C₂ (∇²U)` at derivative index
`q ≤ k−1`,
```
‖∇^q(appCc C₂ (∇²U))‖_{L²} ≤ ∑_{l≤q} binom(q,l)·‖ |∇^l C₂|·|∇^{q−l+2}U| ‖_{L²}
```
Only `l = 0` is charged to the pointwise fibre cap (`gFibreOpBound`,
δ-only, `lowData_split`, `…/DeTurck/DeTurckRemainderLowBaseAction.lean:3841`).
Every `l ≥ 1` term needs ONE factor in `L^∞`, and the tree's sup embedding
```
|S(x)|² ≤ C² · ∑_{j < finrank/2 + 2} ‖∇^j S‖²_{L²}          (dim 3: j ≤ 2)
```
(`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`,
`…/Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`) charges `+2`
`L²`-orders.  That is the `+2` §6.3 omitted.  It is the SAME `+2` M3
counted; what differs is where it can be parked.

**THE DISPLAYED DERIVATION AT `k = 3`** (the derivation this document has
deferred since v2; `k = 4, 5` below are uniform).  Notation: `X := ‖U‖_{H⁴}`
(`= ‖U‖_{H^{k+1}}`, the pairing factor), `Y := ‖U‖_{H³} = E_3^{1/2}`,
`R` = the class `H²` radius (`‖U_N(t)‖_{H²} ≤ R` a.e., §6.1(i)),
`B₃ = ‖U_N‖_{L²_tH³}` (§6.1(ii)).  Class constants: `Kc(·)` the a₂ tower
(`c2JetTowerQ`, `…/DeTurck/LowRegLadderRung.lean:148`), `C_s` the sup
embedding above, `C_J` the jet↔`H^n` bridges (`hsJet_le` / `hs_le_jet`,
`…/SobolevScale/IteratedCovGradHsJetBound.lean:834 / :855`).  Every
`l ≥ 1` term takes Hölder split **(A)** — `L^∞` on the COEFFICIENT, `L²`
on the state — which is the choice §6.3 never made explicit.

* `l = 0`:  `≤ |C₂|_∞·‖∇⁴U‖_{L²} ≤ Cδ*·X`.
  Pairing ⟹ `Cδ*·X² = Cδ*·E_4`, absorbed by the δ*-margin.  [§3 unchanged]
* `l = 1`:  `≤ ‖∇C₂‖_∞·‖∇³U‖_{L²}`.
  `‖∇C₂‖_∞ ≤ C_s(∑_{p≤3}‖∇^pC₂‖²)^{1/2} ≤ C_s√(Kc 3)·(1 + C_J·Y)` — tower
  index `1 + 2 = 3`, state window `j ≤ 3` under (B-WIN); `‖∇³U‖_{L²} ≤ C_J·Y`.
  Pairing ⟹ `K₁(Y + Y²)·X`; Young ⟹ `2ε X² + C(Y² + Y⁴)`
  `= 2εE_4 + C·E_3 + C·E_3(t)·E_3`.  The last is §6.1's `L¹_t`-Grönwall
  coefficient: `∫₀^{τ₀} E_3 = ‖U_N‖²_{L²_tH³} ≤ B₃²`.  ✓
* `l = 2` (**the term §6.3 missed**):  `≤ ‖∇²C₂‖_∞·‖∇²U‖_{L²}`.
  `‖∇²C₂‖_∞ ≤ C_s(∑_{p≤4}‖∇^pC₂‖²)^{1/2} ≤ C_s√(Kc 4)·(1 + C_J·X)` — tower
  index `2 + 2 = 4`, state window `j ≤ 4` under (B-WIN), i.e. `H^{k+1}`
  EXACTLY; `‖∇²U‖_{L²} ≤ C_J‖U‖_{H²} ≤ C_J·R`.
  Set `K_R := C_s·max(1,C_J)²·√(Kc 4)`.  Pairing ⟹
  `K_R·R·X + K_R·R·X² = K_R R X + K_R R·E_4`, and `E_4 = E_3 + D_3`.
  The first is `≤ εX² + (K_RR)²/4ε` — an additive CLASS constant.  The
  second contributes `K_R·R·D_3`, absorbed iff **`Cδ* + K_R·R + 2ε < 1`**.
  ✓ under (A-R).

Summing (a₁/a₀ arms are strictly cheaper — their `L^∞` factors are
`‖∇U‖_∞ ≲ ‖U‖_{H³}` and `‖U‖_∞ ≲ ‖U‖_{H²} ≤ R`, so the landed `range (i+2)`
windows of `c1JetTowerQ` / `c0_jet_tower_quad` suffice for them):
```
d/dt E_3 ≤ −2(1 − Cδ* − K_R R − 2ε)·D_3 + A(t)·E_3 + [ (1/2ε)‖𝒩(0)‖²_{H²} + c_cls ]
A(t) = a₀ + a₁·E_3(t),   ∫₀^{τ₀} A ≤ a₀τ₀ + a₁B₃² < ∞,  all N-free
```
Zero seed + `L¹_t`-Grönwall ⟹ `sup_{t≤τ₀} E_3 ≤ Φ_3` with NO restriction
on `τ₀`; the per-datum static force stays on the right (requirement 4 ✓),
`c_cls` is class (requirement 5 ✓), every constant is `N`-free (1–3 ✓).

> **CORRECTION (2026-08-05, №155 — brick-4a acceptance panel).**  The
> parenthetical above is FALSE as stated for the a₁/a₀ arms: it prices only
> the EXTREME Leibniz indices (`i = 0` and the pure-state factors) and is
> silent on intermediate ones.  With the state-side `L^∞` split at every
> `i ≥ 1` (the first Lean attempt), the `i = 1` slot of the `C₁` group reads
> `class·(1+jet_{H²})·jet_{q+2}` — after the cross-scale pairing this puts a
> NON-SMALL, `R`-free constant into the `E_{k+1}` coefficient and the
> absorption line fails.  The correct pricing is the MIXED per-index split,
> with PER-GROUP boundaries (№157 amendment — the first uniform version of
> this correction put the boundary at `i = q` for both groups; the C₀ group's
> `i = q−1` coefficient-sup slot then carries the tower's quadratic factor
> `1+‖U‖²_{H³}(t)` against `√E_{k+1}`, i.e. after pairing a TIME-DEPENDENT
> `E_{k+1}`-coefficient no Grönwall variant accepts):
> - **C₁ group**: coefficient-side `L^∞` at `1 ≤ i ≤ q−1` (sup at index `i`
>   reads the `range (i+2)` tower at `i+2`, state order `i+3 ≤ q+2` — in
>   budget up to `i = q−1`), state-side `L^∞` only at `i = q`.  Its `i = q−1`
>   slot reads `q+2` against the class window — the `K_R^{a₁}·R` absorption
>   term.
> - **C₀ group**: coefficient-side at `1 ≤ i ≤ q−2`, state-side at BOTH
>   `i = q−1` and `i = q` — legal because C₀'s data at `i = q−1` is only
>   `∇T`/`T` (sup orders 3/2, in budget), where C₁'s would be `∇²T` (order 4).
>   C₀ then never reaches `q+2`; its evolving `1+E₃(t)` factors pair to
>   `ε·E₄ + A(t)·E₃` with `A ∈ L¹_t` — the same mechanism as the a₂ `l = 1`
>   slot above.
> The condition of adapter H becomes
> `Cq(k−1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε < 1`, `K_R^{a₁}` from the C₁ tower
> constants.  The arms are still cheap — they need no small fibre constant —
> but they are NOT free.

**`k = 4, 5`: uniform, same two adapters.**  At rung `k` the worst term is
`l = k−1`: `‖∇^{k−1}C₂‖_∞ ≤ C_s√(Kc(k+1))(1 + C_J‖U‖_{H^{k+1}})` (tower
index `k+1`, window `j ≤ k+1` under (B-WIN)) times `‖∇²U‖_{L²} ≤ C_J R`;
pairing ⟹ `K_R R‖U‖_{H^{k+1}} + K_R R·E_{k+1}` — the SAME absorption
condition, with `K_R := C_s max(1,C_J)²·max_{i≤7}√(Kc i)` covering
`k = 3,4,5` (finitely many tower indices).  Intermediate `l` are strictly
better: at rung 4, `l = 1` gives `C(1+R₃)E_4^{1/2}‖U‖_{H⁵} ⟹ εE_5 + CE_4`;
`l = 2` gives `CR₃(1+E_4^{1/2})‖U‖_{H⁵} ⟹ εE_5 + C(1+E_4)`; at rung 5 the
already-fixed `R₃, R₄` make every `l ≤ 3` term outright class.  §5's upward
ordering is preserved: rung `k` sees only `R_j`, `j < k`, plus class data.

**THE TWO ADAPTERS.**

* **(B-WIN) — sharpen the a₂ tower's state window from `range (i+2)` to
  `range (i+1)`.  FREE: the proof already establishes it.**  `topKer_jet`
  (`…/DeTurck/LowRegC2JetTower.lean:196`) reaches
  `hfin.2.2 i : lowJetSq g i (topKernel …) ≤ A i·(1 + lowJetSq g i T)` — the
  SHARP window `j ≤ i` — at `:260`, and then spends the last two `calc`
  steps (`hsub`/`hmono`, `:263–:280`) WEAKENING `lowJetSq g i T` to
  `∑_{j ∈ range (i+2)}`, purely for shape-uniformity with the C0/C1 towers.
  Deleting that weakening restates `topKer_jet` and its consumer
  `c2JetTowerQ` (`LowRegLadderRung.lean:148`) with `range (i+1)`.  This is
  the whole difference between `j ≤ k+2` (circular — the `H^{k+2}` the
  corrected §6.3 warns about) and `j ≤ k+1` (absorbable).  Backwards
  compatible: every current consumer takes the tower as a HYPOTHESIS in the
  `range (i+2)` shape (e.g.
  `exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`,
  `…/DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean:4670`, `:4682`), and
  the sharpened tower implies it by `Finset.sum_le_sum_of_subset_of_nonneg`.
* **(A-R) — strengthen §3's absorption condition to `Cδ* + K_R·R + 2ε < 1`.**
  Legal ordering: `Kc` is `∃`-bound before the state in `c2JetTowerQ`, `C_s`
  and `C_J` are background constants, so `K_R` is fixed BEFORE `R` is chosen;
  front 3 then picks `R ≤ (1 − Cδ* − 2ε)/(2K_R)` alongside the existing
  `hsmall : C₁·R ≤ 1/8` (`partial_sol_const`,
  `…/TensorMaximalRegularity/PartialForcingFixedPoint.lean:195`).  Shrinking
  `R` only shrinks `τ₀` through the closed formula
  `T₀ = min 1 (min (1/(64(C₂+1)²)) ((R/4)/(2(D+1)))²)`, whose inputs are all
  class data — so `τ₀` stays class-uniform and requirement 5 is untouched.
  This is a numerical premise of exactly the same kind as A2-ABS, and it
  should be discharged together with it.

**WHY THE TOWER-DIRECT ROUTE ESCAPES M3'S `A ≥ 4`.**  The ladder interface
must collapse the whole `l ≥ 1` sum onto ONE lower slot `Clower·‖T‖_{H^{m+1}}`
whose constant may depend only on a BALL radius; log-convexity then forces
`q+5 ≤ A + (q+1)`, i.e. `A ≥ 4` (M3, No. 148-executor).  The tower-direct
pairing is not obliged to collapse: it may leave the cost on the TOP slot as
`(K_R·R)·‖U‖_{H^{k+1}}`, where the δ*-margin — not a ball — pays for it.
That is the entire structural difference, and it is why the same `+2` `L^∞`
cost is fatal for the ladders at `k ≤ 5` and survivable tower-directly.  The
price is that `R` now enters the absorption condition, so the bottom block's
smallness is `min(δ*, R)`-shaped rather than `δ*`-only.

**RESIDUAL RISK / WHAT IS NOT PROVED HERE.**  This is paper arithmetic over
the LANDED statement shapes.  The Lean deliverable is a BALL-FREE per-index
`appCc` `H^{k−1}` assembly making the per-`l` split choice explicit.  It does
not exist: the two engines that assemble this product either absorb the cost
into a ball constant (`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`,
`…/TensorHilbert/ConnLapCommutatorCoefficientTame.lean:1334`; the `m ≤ 1`
band-split `…PrincipalArmOpNorm.lean:4670`) or use a uniform `C^k`-sup on the
coefficient that is too crude for rung 3
(`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`,
`…/Sobolev/MoserTameProduct.lean:111`, whose `Λ` bounds `‖∇^i c‖_∞` for ALL
`i ≤ k` at once).  The GN producer in that file
(`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`, `:1115`) interpolates
`‖∇^j u‖_{L²}` between `‖u‖_∞` and `‖∇^k u‖_{L²}` — not the shape needed here,
and NOT needed by the derivation above (which uses no fractional scale, no
Agmon inequality, and no interpolation beyond plain Young).  That absence is
deliberate: an Agmon-type `‖∇²U‖²_∞ ≲ ‖U‖_{H³}‖U‖_{H⁴}` would be an
alternative to (A-R) but would need a fractional/Weyl-summability embedding
the tree does not have, so the (A-R) route is the cheap one.

**STATUS UPDATE (2026-08-05, No. 150-executor-J4PREP).**  The residual risk
above is DISCHARGED: the ball-free per-index assembly exists in Lean, sorry-free
and census-clean, as `appCcPerIdxL2` / `a2PerIdxJet` / `a2PerIdxLin`
(`…/DeTurck/LowRegA2PerIndex.lean`), and adapter G is landed
(`topKerJetSharp`, `c2JetTowerSharp`, old names kept as byte-identical
wrappers).  The per-`l` bookkeeping of the displayed derivation was confirmed
term by term, not exceeded.  One correction to adapter H: the linear form's top
slot is `Cq(k−1)·Cδ*` where `Cq q = √(appCcGdiag q)` — an absolute constant
fixed before `δ` and before `R` — so the absorption premise reads
`Cq(k−1)·Cδ* + K_R·R + 2ε < 1`.

**WHICH SEQUENCE THE RUNGS RUN ON — the Fatou seam (No. 149-executor-M2).**
`galTamePerMode` (`…/HeatSemigroup/GalerkinTameSol.lean:886`) represents the
GALERKIN ODE coordinates as `perModeConv` of `galTameForce … (U N ·)`, while
`lowreg_projMode_tendsto` (`ShortTime/LowRegGalerkinIdent.lean:165`) proves
convergence for `perModeConv` of the PROJECTED-solve forcing
`timeModeCoeff (fseq N) i`.  Two different sequences; Fatou needs one.
**RULING: run everything on the PROJECTED sequence.**  This is §6.2(d)'s
"delete the Galerkin ODE" applied one level further out, and it is forced by
three facts:

* the convergence to `fLo` is a TRUNCATION-DEFECT estimate on the projected
  forcings (`‖fseq N − fLo‖ ≤ 2‖Π_N fLo − fLo‖`, `projFixTame_le_two` +
  `projFix_tendsto`, assembled at `LowRegGalerkinIdent.lean:~130–:160`).
  Nothing of the kind is available for `galTameForce`, so riding the Galerkin
  sequence alone would mean RE-PROVING the convergence, which strictly
  contains the identification;
* the projected side already has the same per-mode representation without
  `galTamePerMode`: `maximalRegularitySolField_timeModeCoeff`
  (`…/MaximalRegularity/Operator.lean:491`) with `solModeCoeff` (`:88`) gives
  `y_i(t) = perModeConvL2 λᵢ (timeModeCoeff gforce i)`, and `projField_fixed`
  (`…/HeatSemigroup/EigenProjPartialSol.lean:561`) supplies the `V_N`-valuedness
  that §6.2(e)'s adapter A asked for — **adapter A is LANDED**; what is left of
  (e) is only the differentiability of `t ↦ E_k`, and on `V_N` that is a finite
  sum of `perModeConv_hasDerivAt` (`…/MaximalRegularity/PerMode.lean:586`);
* the a-priori data the rungs consume (§6.1(i) state ball, (ii) `L²_tH³`, the
  Nemytskii identity and the PDE) are OUTPUTS of `proj_partial_sol_tame`
  (`…/HeatSemigroup/EigenProjTameSol.lean:118`), i.e. they exist only on the
  projected trajectory.  The Galerkin ODE trajectory has NO ball bound at all
  — `galTameRetr` exists precisely to avoid needing one — so even
  `galTameForce_eq` (`GalerkinTameSol.lean:627`, hypothesis
  `hc : ‖galLowView …‖ ≤ R`) cannot be applied along it without a new estimate.

Consequence for the lane: the identification brick is NOT needed, and
`lowregGalSol` / `galTameSolOne` / `galTamePerMode` / `galTameForce_contOn`
are sound API that is OFF the critical path.  What IS needed is a statement
widening: `lowreg_proj_tendsto` / `lowreg_projMode_tendsto` currently `obtain`
the projected trajectory and DISCARD it (`⟨_u, gforce, _hu, _hstate, hgE,
_htr, _hpde, hgball⟩`, `LowRegGalerkinIdent.lean:~143`), keeping only the
forcing.  The rungs need `u`, `hstate`, `hgE`, `hpde` exposed alongside
`fseq`.  Cheap — the conjuncts are already produced.

## 7. Identification: RESOLVED — the compactness+uniqueness route is not needed

R-4's "weakest link" (steps 4–6) DISSOLVES under the §6.2(b) finding.
Both trajectories are fixed points of maps that differ only by `Π_N`,
inside ONE contraction with ONE modulus:

  `partial_sol_const`'s internal contraction factor is
  `Λ = C₁·R·(1+T) + C₂·2√T`, and its own hypotheses force
  `Λ ≤ 1/4 + 1/4 = 1/2` (the two arms are bounded by `1/4` each from
  `hsmall : C₁R ≤ 1/8` and the horizon cap `T ≤ 1/(64(C₂+1)²)`).

Write `Φ(f) := Nfun ∘ field(f)` for the unprojected forcing map and
`Φ_N := Π_N ∘ Φ`.  With `f_*` the A1 fixed point and `f_N` the projected
one (both with zero seed, both in the same `R/4` forcing ball):

  `f_N − f_* = Π_N(Φ(f_N) − Φ(f_*)) + (Π_N − 1)Φ(f_*)`
  ⟹ `‖f_N − f_*‖ ≤ (1 − Λ)^{-1}·‖(Π_N − 1)Φ(f_*)‖ → 0`

by `timeL2EigenProj_tendsto` (`TimeL2EigenProjection.lean:199`).  Then
`field_N → field_*` in `L²_tH³` by `maxRegDuhamelSolField_dist_le`.  The
limit IS the A1 fixed point, by construction — no Aubin–Lions, no
weak-* extraction, no diagonal subsequence, no per-σ limit bookkeeping,
and no uniqueness theorem.  R-4's requirement "one approximant sequence
and one limit trajectory for every rung σ" is met trivially: there is
one sequence and its limit is a pre-existing object.

Ingredients, all present: `nemytskiiOn_mixed`
(`…/PartialForcingFixedPoint.lean:96`, public — the map's own mixed
Lipschitz bound), `maxRegDuhamelSolField_dist_le`
(`…/TensorMaximalRegularity/ForcingFixedPoint.lean:282`),
`timeL2EigenProj_tendsto`.  The one thing `partial_sol_const` does NOT
export is its contraction as a reusable object (`Λ` is a local `set`),
so the stability lemma is stated and proved beside it rather than
extracted from it — see §10 adapter C.  It belongs to A2 (G-2 adapter 2),
exactly where §7 v1 predicted, and it is smaller than the Grönwall
lemma that section anticipated.

FALLBACK, if adapter C is ever wanted in the compactness+uniqueness
form: a MASTER uniqueness theorem DOES exist and is proved and used —
`deTurckStrong_unique` (`…/DeTurck/StrongSolutionUniqueness.lean:90`,
callers at `EdgeStrongData.lean:296` and `SmoothStrongPair.lean:715`),
explicitly for "two independently supplied ... pairs [that] need not
have been constructed by the fixed-point solver".  Hypothesis match
against what a Galerkin limit provides:

| `deTurckStrong_unique` hypothesis | status |
| --- | --- |
| `trace0 uᵢ = 0` (zero initial datum) | MATCHES |
| `timeDeriv uᵢ = timeScaleLaplacian fieldᵢ + forceᵢ` (a `timeL2` identity, i.e. a.e.) | MATCHES |
| `incl fieldᵢ = toTimeL2 uᵢ` (scale link) | MATCHES (`partial_sol_const` output shape) |
| `forceᵢ = nemytskii hLip fieldᵢ` | MATCHES (a.e. Nemytskii identity) |
| `‖forceᵢ‖ ≤ ρ` (force ball) | MATCHES (`‖gforce‖ ≤ R/4`) |
| `hsingle` (the tame two-arm difference bound) | MATCHES — this is precisely what `c0Diff_tame` / `bg0_pair_h1` / `a1Sub_lo_tame` produce |
| `hsmall : C₁√(1+T)ρ(1+T) + C₂·2√T < 1` | MATCHES the same horizon caps |
| **`hLip : LipschitzWith L Nfun` for a GLOBAL `Nfun : H^{a+2} → H^a`** | **MISMATCH** |

The single mismatch is real: the low-regularity nonlinearity is
`lowRegN : lowerState g₀ 1 R → H¹` (`ShortTime/LowRegDenseSolve.lean:100`),
a `Dense.extend` on a BALL SUBTYPE, not a global map — which is exactly
why `partial_sol_const` (ball-restricted) exists alongside
`quasilinear_strong_unique` (`…/ForcingFixedPoint.lean:476`, global
`hN : LipschitzWith L N` with `2L < 1`).  Using the master would cost a
globally-Lipschitz extension of `lowRegN` off the ball — strictly more
work than adapter C.  Recorded so the option is not re-discovered later;
NOT on the critical path.

Note also: the difference-tame layer is NOT wasted by this ruling.  It
is `partial_sol_const`'s `hsingle`/`htame` slot — i.e. it is what makes
the A1 solve and its projected replay exist at all.  It was never only
a uniqueness input.

## 8. Six requirements — scoreboard (FINAL, 2026-08-04)

1. **Projector norm ≤ 1 on every scale, commuting with Δ/resolvents/
   semigroup, no inverse inequality: MET.**  Free in the spectral frame
   (§1) and already Lean-realized: `norm_spatialEigenProj_le_one`,
   `norm_timeL2EigenProj_le_one`.  Commutation with the Duhamel family
   is modewise (§6.2(e)) — adapter A, mechanical.  No `λ_N` appears
   anywhere in the argument (stop-signal 1 clear).
2. **Nonlinear constants from radii + background only, never the largest
   retained eigenvalue: MET, conditional on A2-ABS.**  §6's
   dependence-graph danger is not merely avoided — it is REFUTED as a
   design (§6 Step 1) and then bypassed: with the projected solve, the
   coefficient inputs are `δ*`, the class `H³` bound `B₃`, and the
   towers' δ-free constants.  Nothing sees its own or a later exit
   radius.  The one open number is `κ` (A2-ABS, §6.3).
3. **Projected source bound ≤ 1; per-datum highs only in constants:
   MET** (§3–§5 shape, §6.2(a) for the Lean slot).
4. **Strict improvement / per-datum highs never restricting T: MET, and
   now trivially** — the horizon is `partial_sol_const`'s closed formula
   `T₀ = min 1 (min (1/(64(C₂+1)²)) ((R/4)/(2(D+1)))²)`, identical for
   the projected system, containing no high static norm, no `H⁵` ball,
   no fourth derivative of `g₀` (RULING2 stop-signal 9 clear).
5. **Full-horizon closure `τ_N = T`: MET, vacuously.**  There is no
   first-exit argument left: the projected trajectory exists on all of
   `[0, T₀]` by the same fixed point, and its state ball is an OUTPUT of
   `partial_sol_const`, not a stopping hypothesis.
6. **Coupled bottom scales + identification: MET.**  Rungs couple
   downward only (§6.1); identification is fixed-point stability (§7),
   not compactness+uniqueness.

No stop signal from RULING2 §(ii) fired during this audit.

## 9. Honest denominators

* **P-STOP (paper): ≈ 93%.**  §1–§5 verified; §6/§6.1 resolved with one
  substantive correction (the `C_tH³ ∩ L²_tH⁴` claim replaced by the
  available `L²_tH³` bound plus `L¹_t`-coefficient Grönwall); §6.2(a)–(e)
  audited against the Lean statements with file:line evidence; §7
  resolved and simplified.  §6.3's window-level budget check was WRONG
  (it omitted the `L^∞` embedding cost of every Leibniz term `l ≥ 1`) and
  is corrected in §6.4, where the rung-3 pairing is now written out as a
  displayed line-by-line derivation and rungs 4–5 shown uniform —
  discharging v4's open item (ii).
  The remaining ~7% is: (i) A2-ABS — the `κ` binder hoist, without which
  the absorption condition is not certified; (ii) the two §6.4 adapters
  (G: the free a₂-tower window sharpening; H: the strengthened absorption
  condition `Cδ* + K_R·R + 2ε < 1`), neither of which is Lean-landed;
  (iii) the ball-free per-index `appCc` `H^{k−1}` assembly that the
  tower-direct rungs consume does not exist as a producer (§6.4 residual
  risk) — that is the largest single piece of Lean work the bottom block
  still needs.
* **Nothing in this document is Lean-verified.**  It moves no Lean; the
  proposition is a gate, not a brick.
* **(N) `ricci_flow_unif_existence`: 0%** — still stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  P-STOP
  passing does not move it by one line.
* Whole HCG compactness project: low single digits.

## 10. P-STOP VERDICT

**PASSED-WITH-ADAPTERS.**

The proposition holds as stated, in the corrected §6.1 form.  The
Galerkin lane MAY be built — but it is a smaller lane than R0/R-2
imagined: the projected system is not a Galerkin ODE, it is the SAME
`partial_sol_const` solve with `Π_N ∘ Nfun` in place of `Nfun`, and the
identification is fixed-point stability rather than compactness plus
uniqueness.  Two of the lane's planned bricks (E4's ODE existence, G4's
compactness/uniqueness plumbing) should be DELETED, not implemented.

Adapters — all small, all named, none a design change:

* **A. `Π_N` commutes with the Duhamel family.**  From
  `maximalRegularitySolField_timeModeCoeff` (`…/MaximalRegularity/Operator.lean:491`)
  and `solModeCoeff` (`:88`, a function of mode `i` alone): the projected
  solve is `V_N`-valued, so the §1 energy identity is legitimate.
  Load-bearing — without it there is no Galerkin energy argument.
* **B. `Π_N ∘ Nfun` inherits `partial_sol_const`'s four slots**
  (`hLip`, `hsingle`, `hzero`, `hsmall`) with the same `L, C₁, C₂, D`,
  each one line from `norm_spatialEigenProj_apply_le`.  Gives projected
  existence on the identical horizon `T₀`.  Tiny.
* **C. Fixed-point stability** `‖f_N − f_*‖ ≤ (1−Λ)^{-1}‖(Π_N−1)Φ(f_*)‖ → 0`,
  over `nemytskiiOn_mixed`, `maxRegDuhamelSolField_dist_le` and
  `timeL2EigenProj_tendsto`.  Belongs to A2 / G-2 adapter 2.  Small.
* **D. A2-ABS** — hoist `∃ κ` above `{δ}` in `a2_ladder`, propagate to
  `n_diff_hm_rung`; `κ` is `lowData_split`'s δ-free `K`.  Binder work,
  but REQUIRED: the absorption condition `κ·δ*/(1−δ*)² < 1 − 2ε` is not
  certified without it (R-5, RULING2 stop-signal 8).
* **E. C0 tower instantiated at `a = 1`** (ball `H³`), per §6.2(c).  If
  `selfLow_jet` is threaded at `a = 3`, re-cut the surgery to the `H³`
  cap before the rung-3..5 assembly.
* **F. Paper-side, no Lean:** §6.1(ii) reads `L²_tH³`, and rung-`k`
  Grönwall runs with an `L¹_t` coefficient.  Already applied above.
* **G. (B-WIN, §6.4) Sharpen the a₂ tower's state window** from
  `range (i+2)` to `range (i+1)` in `topKer_jet`
  (`…/DeTurck/LowRegC2JetTower.lean:196`, weakening at `:263–:280`) and its
  consumer `c2JetTowerQ` (`LowRegLadderRung.lean:148`).  FREE — the proof
  already establishes the sharp window; only the final `calc` throws it
  away.  Backwards compatible (consumers take the tower as a hypothesis in
  the weaker shape).  LOAD-BEARING: without it the rung-`k` pairing needs
  state jets `j ≤ k+2`, i.e. above `E_{k+1}`, and the bottom block is
  circular.
* **H. (A-R, §6.4) Strengthen the absorption condition** from
  `Cδ* < 1 − 2ε` to `Cδ* + K_R·R + 2ε < 1`, `K_R` built from the a₂ tower
  constants `Kc(i)`, `i ≤ 7`, the sup-embedding constant and the jet↔`H^n`
  bridge constant.  Numerical premise of the same kind as D (A2-ABS) and
  should be discharged with it; `R` is chosen after `K_R` in front 3, and
  shrinking `R` moves `τ₀` only through `partial_sol_const`'s closed
  formula, so `τ₀` stays class-uniform.

Adapters A, B, C are the whole of what used to be called "the Galerkin
lane"; D and E are pre-existing debts now dated; G and H are v5's, forced
by §6.4's re-pricing.

**2026-08-05 (No. 150-executor-J4PREP): G is LANDED** — `topKerJetSharp` /
`c2JetTowerSharp` (`…/DeTurck/LowRegC2JetTower.lean`, `…/LowRegLadderRung.lean`),
with `topKer_jet` / `c2JetTowerQ` kept as byte-identical `range (i+2)` wrappers,
so no consumer moved and no census changed.  **H is restated**, not discharged:
the linear per-index assembly's top slot carries the absolute prefactor
`Cq q = √(appCcGdiag q)`, so the premise to thread is
`Cq(k−1)·Cδ* + K_R·R + 2ε < 1` (legal ordering — `Cq` depends only on `g₀` and
`q`).  §9(iii)'s missing producer is landed as `a2PerIdxLin`; the forcing-side
statement widening asked for at the end of §6.4 is also landed
(`lowreg_proj_tendsto` / `lowreg_projMode_tendsto` now expose the whole
projected trajectory with `N`-free constants).

**2026-08-05 (№155): H WIDENS AGAIN** — the a₁/a₀ arms are not free (see the
§6.4 correction block): under the correct mixed per-index split the `C₁`
group's `i = q−1` coefficient-sup slot contributes an own class-radius term,
so the premise to thread is
**`Cq(k−1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε < 1`**, with `K_R^{a₁}` built from
the `C₁` tower constants exactly as `K_R` is from the a₂'s (№157 amendment:
the `C₀` group is state-side at `i ∈ {q−1, q}` and feeds the `L¹_t` Grönwall
coefficient instead — it does NOT enter the absorption).  Same ordering
discipline (`R` after all the `K`'s); still a numerical premise of D's kind,
not discharged in Lean.

WHAT THE FIRST BRICK (E1′a) SHOULD BE TOLD.  Do NOT build a Galerkin
ODE.  Build adapter A: prove that `spatialEigenProj`/`timeL2EigenProj`
commutes with `maximalRegularitySolField`, `maximalRegularityDerivField`
and `maxRegDuhamelMap`, modewise, from the `_timeModeCoeff` lemmas.  It
is the only load-bearing adapter, it is upstream of B and C, and it
belongs in `…/Spectral/Intrinsic/HeatSemigroup/TimeL2EigenProjection.lean`
(where the projector already lives) or a sibling module — NOT in
`ShortTime/`.  Ship A, then B (one `partial_sol_const` application),
then C.
