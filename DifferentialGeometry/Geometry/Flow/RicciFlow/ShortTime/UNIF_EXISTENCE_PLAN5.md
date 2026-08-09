# UNIF_EXISTENCE_PLAN5 — continuation of `UNIF_EXISTENCE_PLAN4.md`

`UNIF_EXISTENCE_PLAN4.md` approached the project's 3000-line file limit
after the tame-C0 session-4 executor report (No. 126–142 live there; PLAN3
= No. 104–125, PLAN2 = No. 70–103, PLAN = No. 1–69, all frozen).  This
file continues it.  Same conventions: one planner entry per landed/ruled
brick, executor reports appended by builders (READ THE CURRENT TAIL
IMMEDIATELY BEFORE APPENDING; re-anchor on modified-file errors),
honest-denominator footers everywhere.  Planner numbering is canonical.

State snapshot at the volume break (2026-08-04, post No. 142):

- (N) `ricci_flow_unif_existence`: STATED
  (`Evolution/ExtendViaUniqueness.lean:80`, sorry :98), proof 0%.
- Front 2's sole Lean sorry: `lowreg_loMass`
  (`ShortTime/LowRegAllOrderJet.lean`, cite by name; `lowreg_spatialMass`
  is PROVED by transport over it).  Machinery ≈ 30%.
- Governing plan: `CODEX_LOMASS_AUDIT.md` (STOP-AND-REDESIGN adopted at
  No. 136) + the tame-C0 re-scope (No. 138).  Route-error counter: 2/3
  (user-reset semantics: unattended drift guard).
- Tame C0 bottom: FIVE of six arm families closed at the deliverable
  shape (`ricciAAJet`, `lc0VBJet`, `lc0AMixJet`, `lc0RiemJet`,
  `lieCovJet`); remaining = the `ricciDALow` groundwork brick (a
  `topSeparated` window for `covGrad (connLowOp)` via ∇-parallelism), the
  `selfLow_jet_quad` assembly, and the `gridIntHigh` one-case frontier
  (`(2,2,2)` = `∫|∇²P|⁶`, i* = 4).
- Marked-currency layer: `MarkedTupleGrid.lean`, `TameMarkWin.lean`,
  `TameGridProd.lean`, `TameArmJets.lean`, `TameLieCorrJets.lean`,
  `SelfLowArmCaps.lean` (grown).  Key rules: marks are free at any order,
  LEVELS are not; affine-plus-quadratic arms are SPLIT, not demoted;
  check `topSeparated` producers and call-site vanishing identities
  BEFORE re-deriving anything (over-count exhibits now EIGHT).
- Whole HCG compactness project: ≈ 3%.

## Planner update No. 142 (2026-08-04) - SESSION 4 ACCEPTED (lieCov CLOSED, 5/6; EXHIBIT EIGHT); PLAN5 OPENED; SESSION 5 (ricciDALow GROUNDWORK) DISPATCHED

Acceptance (recorded here; the executor report is at PLAN4's tail):
`lieCovJet` closes the lieCov pair at the exact deliverable shape
(no `s` in any constant).  OVER-COUNT EXHIBIT EIGHT: the dispatched
`∇²T` design question DID NOT EXIST — `lrCurvF` carries no state
derivative at all (fixed background Riemann contracted with `T`);
the `∇²T` lives in the subtracted edge, which `lieCov_residual`
cancels.  Third throw-away exhibit in three sessions; the
check-the-producer-first rule is now the single highest-yield
discipline in the campaign.  Durable rules ratified: MARKS ARE FREE
AT ANY ORDER, LEVELS ARE NOT (`markGrid`'s recursion makes an
order-two factor just the `c = 1` summand); AFFINE-PLUS-QUADRATIC
ARMS ARE SPLIT (tensor-level, `norm_sub_le`), NOT DEMOTED.
`ricciDALow` correctly narrowed to ONE missing-groundwork brick: a
`topSeparated`-shaped window for `covGrad 3 3 (connLowOp g₀ g₁)` —
true by ∇-parallelism of `connLowOp g₀ g₀` (three pieces:
`covGrad (permCoeff) = 0`, `covGrad (koszulOp-part) = 0` — the
opacity trick applies, only ∇-parallelism of the witness is needed —
`covGrad (slotInsertEndoCc (fullRaisedEndoField g₀ g₀)) = 0`, plus a
`topSeparated` window for `covGrad (gInvDiffRaisedEndoField)` whose
exact-weight producer exists).  The two ruled-out alternatives
(Leibniz through `connLow_app`; a `markJet1` bridge) are recorded —
the problem is the LEVEL, not the mark count.

DISPATCHED: SESSION 5 — the `ricciDALow` groundwork brick, then
(budget permitting) the `selfLow_jet_quad` ASSEMBLY over the six arm
jets (class-3 residuals via `gridIntHigh` only).  After it: only
`gridIntHigh` (one case) remains of the tame C0 bottom.

Honest denominators: `selfLow_jet_quad` 0% (machinery ≈ 88%, five
of six arms); `lowreg_loMass` 0% (≈ 30%); (N) 0% (stated, sorry
:98); whole HCG ≈ 3%.  Route-error counter: **2/3**.

## Executor report No. 142-executor (2026-08-04) - TAME C0 BOTTOM SESSION 5: BOTH PARTS DONE; `selfLow_jet_quad` PROVED; ONLY `gridIntHigh` REMAINS

**Verdict: both dispatched parts landed.**  The `covGrad connLowOp` groundwork
brick is built, `ricciDALow` closes the sixth arm family at the deliverable
shape, and the `selfLow_jet_quad` ASSEMBLY is stated and proved.  The tame C0
bottom is now **[`gridIntHigh`] only** — the priced one-case frontier.  No new
`sorry` was added, no statement was weakened, no `maxHeartbeats` raised.
Route-error counter unchanged (**2/3**).

### The deliverable

```
selfLow_jet_quad (hDim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ x u v, ccTensorBilin g T x u v = ccTensorBilin g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound g (ccTensorBilinSymm g T) δ)
        (hδZ : gFibreOpBound g (ccTensorBilinSymm g (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq g i (rhsSelfLow g g T hδg hδZ s) ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3, ‖iteratedCovGrad g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad g 0 2 j T‖ ^ 2)
```

`‖T‖²_{H³}` is spelled `∑_{j<3}‖∇^{1+j}T‖²` (`gradCapLin`'s convention — the
exact spelling every arm jet already uses).  **No `R₀`, no `H^{a+2}` ball, no
`a`, no `Λ`, no `s` in any constant, exactly one power of `‖T‖²_{H³}`,
constants chosen before the state.**  The audit's acceptance criteria
(`CODEX_LOMASS_AUDIT.md` :509-521) are met as stated; the only inputs are
`hDim`, the symmetry of `T`, and `δ ≤ 1/3`.

### The brick: the dispatched design was OVER-PRICED

The dispatch asked for three obligations, of which **two do not exist**.
`covGrad (permCoeff ρ) = 0` and `covGrad (koszulOp) = 0` are never needed: a
permutation coefficient does not have to be DIFFERENTIATED, it has to be
RECOGNISED AS AN ISOMETRY.

* Outer factor: `permCoeff(lowPerm) ⋆ Y` is an output-slot permutation of `Y`,
  so `rfns(∇ⁿ(connLowOp)) = rfns(∇ⁿY)` by
  `rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr` (the `mkDdc` idiom) — the
  `hrel` obligation is four lines of `slotPermCLM_apply` + `toModel_ofModel`.
* Inner Koszul factor: the CLSPLIT OPACITY TRICK used offensively a SECOND time.
  `clZ` writes the witness out explicitly as
  `(1/2)•(permCoeff ρ₁ + permCoeff ρ₂ − permCoeff ρ₃)` and is still `rfl`; the
  private `koszulOp` of the read-only module is never named.  Then
  `appCcRS Φ (permCoeff ρ) = reindexCoeffGen Φ ρ` (`permRe`, 12 lines) makes each
  a SOURCE reindex — again a jet isometry
  (`rfns_iteratedCovGrad_reindexCoeffGen_eq`).
* Only obligation (2) was real, and it is the `s = 0` proof verbatim: `sieZero`
  from the PUBLIC `endoCovariantDerivative_fullRaised_id_eq_zero` and the
  generic-`s` `tensorCovDerivAt_slotInsertEndoCc_eq`.

So `covGrad(connLowOp)`'s whole derivative sits on the inverse-metric difference,
whose jets the tree delivers at EXACT weight — and the missing input was NOT a
`topSeparated` producer but a new *currency entry*.

### The one genuinely new piece of mathematics

`Combinatorics.atgLeMark1`: an EXACT-weight grid is a once-marked window one
level down, **provided `b 0 ≤ 1`**:

```
antidiagonalTupleGrid b (i+1) ≤ antidiagonalTupleGridCount (i+1) · markGrid b 1 i
```

The anchor is load-bearing, not decoration: `b(i+1)·b(0)^i` IS a term of
`atg b (i+1)` (the length-`(i+1)` tuple `(i+1,0,…,0)`), while `markGrid b 1 i`
contains `b(i+1)` only against an empty grid — without a bound on `b 0` the
statement is FALSE for every `i ≥ 1`.  It is the same δ-anchor `mkOfP` spends,
so it costs the deliverable nothing.  Proof: recurse on the tuple LENGTH
(`Fin.prod_univ_succ`), splitting on `e 0 = 0` (drop the factor) vs `e 0 = c+1`
(`single_factor_mul_antidiagonalTupleGrid_le`, then `markOne_of_term`).  The
"restrict to the support and reindex `Fin n \ {m₀}`" route was considered and is
strictly worse.  `mkOfAtg` is the resulting bridge into `HasMarkWin … 1`.

### What landed

* `MarkedTupleGrid.lean` 229 → 308: `prodLeGrid`, `prodLeMark1`, `atgLeMark1`.
* `TameMarkWin.lean` 1137 → 1173: `mkOfAtg` (exact-weight entry, `u = 1`).
* `SelfLowArmCaps.lean` 1521 → 1953: `sieZero`, `permRe`, `clZ`, `icgSm`,
  `clExact`, `clCovMk` (private) and the endpoints `ricciDAMark` (`u = 2`) and
  `ricciDAJet` (`ricciAAJet`'s exact sibling).
* `LowRegC01JetTower.lean` 639 → 1037: `ricciGoodMark`, `jetFold`, `jetTrans`,
  `ricciGoodJet` (private) and **`selfLow_jet_quad`**.
* `ScratchC01Census.lean` extended with the seven new census entries.

### Verification

Focused checks of all four files green.  Targeted builds green in dependency
order (`MarkedTupleGrid`, `TameMarkWin` 9538 jobs, `SelfLowArmCaps` 9614 jobs,
`LowRegC01JetTower` 9615 jobs, `ScratchC01Census`).  Axiom census:
`prodLeGrid`, `prodLeMark1`, `atgLeMark1`, `mkOfAtg`, `ricciDAMark` are
`[propext, Classical.choice, Quot.sound]` — CLEAN.  `ricciDAJet` and
`selfLow_jet_quad` carry `sorryAx` **through `gridIntHigh` and nothing else**
(both consume `markJet` → `markMon`), exactly as `lieCovJet` does.  The file's
prior census is unchanged: `selfLow_jet`, `c0_jet_tower`, `c1_jet_tower`,
`low1Ker_jet`, `selfLow_split`, `ricciDACap`, `lieCovCap` all still clean.

### Lean lessons worth keeping

* A `have` inside a big theorem that quantifies over `{r c}` is a LEMMA.  The
  first `selfLow_jet_quad` was one declaration and blew the default 200000
  heartbeats; splitting `jetTrans`/`ricciGoodJet` out fixed it with no
  `maxHeartbeats` change (the budget is per-declaration).
* `jetSmul` already existed, PUBLIC, in `DeTurckRemainderLowBaseH2VB.lean`; a
  duplicate was written and deleted.  Grep before writing even a four-line
  helper — the wall/duplicate census is now at NINE.
* `rw [h1, h2, h3] at hA hB` applies every rewrite to every hypothesis and fails
  if one has no occurrence; split the rewrites.
* `positivity` ignores hypotheses — `0 ≤ fr^2 * Cb (i+1)` needs `mul_nonneg`.

### Census (explicit)

Remaining tame-C0 work: **0** arms, **0** assemblies, **1** frontier —
`gridIntHigh` (`TameMarkWin.lean`, one case `(2,2,2)` = `∫|∇²P|⁶`, first at
tower order `i = 4`).  It DID drop to [`gridIntHigh`] as the dispatch hoped.

### Honest denominators

`selfLow_jet_quad`: **0% → 100%** (stated and proved, conditional only on the
declared `gridIntHigh`).  Its dedicated machinery: ≈ 88% → **100%**.  The tame
C0 bottom as a whole: **≈ 95%** (the one `gridIntHigh` case is what is left, and
it may be OFF the critical path — if the `(N)` jet budget is `∀ a ≤ 3` the
`(2,2,2)` class never occurs, which is a planner call already recorded in
`LowRegC01JetTower.md`).  `lowreg_loMass`: **still 0%** — not stated in Lean;
machinery ≈ 30% → ≈ **38%**.  `(N)` `ricci_flow_unif_existence`: **0%** (stated,
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`); nothing this session
moved the theorem itself.  Whole HCG compactness project: **≈ 3%**.
Route-error counter: **2/3**.

### What the next brick should be told

Two candidates, in order:

1. **Decide `gridIntHigh`.**  Before proving it, settle whether the `(N)` jet
   budget is `∀ a ≤ 3`.  If yes, the `(2,2,2)` case never occurs and the
   frontier should be discharged by NARROWING the statement (drop the `q ≥ 3`
   all-order-`≥2` class from `markMon`'s hypothesis) rather than proved — that
   would make the whole tame C0 bottom axiom-clean at zero analytic cost.  If
   no, it needs an interpolation between the two Gagliardo–Nirenberg scales in
   the tree.
2. **The post-tame lane.**  `selfLow_jet_quad` is an INPUT to `lowreg_loMass`,
   not a part of it; the audit's next items are the `c0`-tower/ladder consumers
   that must be re-derived against the quadratic bound in place of
   `selfLow_jet`'s ball-conditioned one.  `c0_jet_tower` is the first: it is
   currently proved from `selfLow_jet`, and its quadratic sibling is the
   statement `lowreg_loMass` actually consumes.

## Planner update No. 143 (2026-08-04) - SESSION 5 ACCEPTED (selfLow_jet_quad PROVED); gridIntHigh RULED: BUILD, NOT NARROW; NEXT BRICK DISPATCHED

Acceptance: both parts green; the audit's deliverable is MET as
stated (statement recorded in the report above; only inputs `hDim` +
symmetry + `δ ≤ 1/3`; the 9615-job build carries exactly ONE sorry
warning = `gridIntHigh`).  Over-pricing corrected again (permutation
coefficients are JET ISOMETRIES, not differentiation targets; the
clSplit opacity trick's second offensive use; exhibit NINE = a
duplicate `jetSmul` self-caught).  The one genuinely new piece —
`atgLeMark1` (exact-weight grid ≤ once-marked window one level down,
IFF `b 0 ≤ 1`; the δ-anchor is load-bearing) — is the kind of
currency entry the whole lane runs on.  Lean lesson banked: a `have`
quantifying over `{r c}` is a LEMMA (per-declaration heartbeat
budget).

**RULING on `gridIntHigh`: BUILD IT — the narrowing option is
REFUTED.**  №139/№140's `i* = 4` arithmetic stands: the bottom-rung
closure consumes tower order 4, where the `(2,2,2)` case FIRST
OCCURS — narrowing `markMon` would break the consumer at exactly the
order it needs.  (The executor's "if the budget is ∀ a ≤ 3 it never
occurs" repeats the №139-corrected conflation of the DATA-jet budget
with the TOWER order.)  The proof is feasible within the quadratic
budget: the session-1 feasibility criterion `∑_j (i+1−c_j)/i ≥ 1`
reads `9/4 ≥ 1` for `(2,2,2)` at `i = 4` — a three-point
interpolation (`‖∇P‖_∞`, `‖P‖_∞ ≤ δ`, top `L²`) between the tree's
two GN scales.

DISPATCHED: [`gridIntHigh` one-case + the quadratic `c0_jet_tower`
sibling] — the frontier proof plus the first post-tame consumer
(the statement `lowreg_loMass` actually consumes).

Honest denominators: `selfLow_jet_quad` 100% (conditional on
`gridIntHigh`); tame C0 bottom ≈ 95%; `lowreg_loMass` 0%
(machinery ≈ 38%); (N) 0% (stated, sorry :98); whole HCG ≈ 3%.
Route-error counter: **2/3**.

## Executor report No. 143-executor (2026-08-04) - PART 2 LANDED; PART 1 NOT LANDED (`gridIntHigh` still `sorry`); route de-researched + last analytic brick built; EXHIBIT TEN

**Lead with the failure: `gridIntHigh` is NOT proved.**  The dispatch's SUCCESS
criterion — the tame C0 bottom fully axiom-clean — is **not met**.  The frontier
was mis-sized in the dispatch: it is not a one-case interpolation exercise but
two sized bricks (~450-550 lines) on top of an analytic input the tree did not
have.  That input now exists and is axiom-clean, and the route is fully
concrete, but the frontier itself is unchanged.

Route-error counter unchanged (**2/3**).  No. 143's feasibility ruling is
**CONFIRMED, not refuted**: the interpolation stays inside the quadratic budget
with the `Λ`-exponent landing on exactly `2` and no slack spent.  No STOP
condition was triggered; this is a scope report, not a route error.

### Part 2 — DONE

`c0_jet_tower_quad` (`LowRegC01JetTower.lean`, after `c0_jet_tower`):

```
c0_jet_tower_quad (hDim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2) (hT : symmetry of T)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδg) (hδZ) (i : ℕ),
        ‖iteratedCovGrad g 2 2 i (lowBaseData g g T _ hδg hδZ).C0‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3, ‖iteratedCovGrad g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad g 0 2 j T‖ ^ 2)
```

The ball is not made inert, it is REMOVED: `a`, `ha : 1 ≤ a`, `R₀`, `hR₀` and
the `‖T‖_{H^{a+2}} ≤ R₀` premise are all gone from the signature.  Same
`path_jetL2_le` skeleton as `c0_jet_tower` with `selfLow_jet` replaced by
`selfLow_jet_quad`; constants `K0 i = 2(K0' i + Φ_i)`, `K2 i = 2 K2' i` with
`Φ_i = lowJetSq g i (−phiMetCurvCoeff g g g)` the state-free curvature summand,
absorbed into `K0` by the `JS ≥ 1` factor (`2Φ(JS−1) ≥ 0`).  Quantifier order is
TK3's: constants before the state.  This is the shape `lowreg_loMass`'s
tower-direct pairing (`PSTOP_PROPOSITION.md` §6.3) reads at `i = k−1` for the
stopped rungs `k = 3,4,5`; `c1`/`c2` were already ball-free, so this was the only
tower needing a quadratic sibling.

### Part 1 — the frontier, and why it did not land

**Exhibit TEN (an over-count avoided, and the session's main finding).**  The
dispatch (and my own first plan) assumed the assembly had to go through
`grid_prod_int_le`, which would have needed a weakened clone (443 lines: it
hard-codes the canonical Hölder weights `θ_j = c_j/i`, demands `hGNP` at every
`0 < j < i`, and demands `hNi : ‖∇^{m+1}P‖ ≤ R` — the out-of-budget top jet).
It does not.  `Analysis/Integration/L2/FiniteProductHolderFiberNorm.lean`
already carries, PUBLIC and axiom-clean:

* `holder_integral_prod_riemannianFiberNormSq_le` (`:89`) — **free-weight**
  Hölder: `∫ ∏ rfns(S m) ≤ ∏ (∫ rfns(S m)^{1/θ m})^{θ m}` for any `θ m > 0`
  with `∑ θ m = 1`;
* `..._le_of_sup_bound` (`:153`) — the same with the sup-bounded factors split
  off, i.e. the "discard the weight-`0` entries against `Λ₀ ≤ 1`" step;
* `holder_integral_prod_rpow_le_prod_integral_rpow` (`:22`) — the scalar engine.

Consequence: the mid-session scare that unbalanced tuples (`2c_j > m+1`, first
at `(5,2,2)`, `m = 8`) resist the interpolation was **an artefact of the wrong
tool**.  With free weights the balance condition disappears and `gridIntHigh` is
provable in FULL generality — no restatement, no narrowing of `markMon`'s `∀ m`.
Recording that explicitly so no future session re-adds a balance hypothesis.

**What landed instead.**  The single genuinely missing analytic input — named as
missing by `gridIntHigh`'s own docstring ("the interpolation BETWEEN the two
scales") — is now built, sorry-free, in the canonical home next to the Hölder
engine it comes from:

```
Integral.lyapunov_pow_le :
  (∀ᵐ x, 0 ≤ F x) → 0 < a → 0 < b → 0 ≤ lam → lam ≤ 1 → c = lam*a + (1-lam)*b →
  Integrable (F^a) → Integrable (F^b) →
    ∫ F^c ≤ (∫F^a)^lam * (∫F^b)^(1-lam)
```

i.e. log-convexity of `p ↦ ‖F‖_{Lᵖ}`.  40 lines, axiom-clean, derived from the
existing scalar Hölder at `Finset (Fin 2)`.

**The remaining two bricks (execution, not research).**  With
`i := m+1 = ∑c_j`, `R := ‖∇^mP‖`, `Λ := max Λ₁ 1`:

1. `GN2` (~200-250 lines): for `2 ≤ c < m` and `θ ∈ [(c−1)/(m−1), c/m]`,
   `(∫ rfns(∇^cP)^{1/θ})^θ ≤ C·Λ^{2(c−θm)}·R^{2θ}`.  `lyapunov_pow_le` between
   the two existing instances of
   `exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs` — base `P` at
   top `m`, base `u = ∇P` at top `m−1` (using `icgNormComp` and
   `rfns_iteratedCovGrad_comp`).  The `Λ₀` weight is `≥ 0` and dies against
   `Λ₀ ≤ 1`; the `Λ₁` weight is exactly `α = c − θm`.
2. `ASSEMBLY` (~200-300 lines): `θ_j := (1−t)(c_j−1)/(m−1) + t·c_j/m` with
   `t := (1−L)/(U−L)`, `L := (m+1−q)/(m−1)`, `U := (m+1)/m`; `q ≥ 2` gives
   `t ∈ [0,1]` and `∑θ_j = 1`.  Then free-weight Hölder + `GN2` give
   `C^q·Λ^{2(∑c_j−m)}·R² = C^q·Λ²·R²` — the `Λ` exponent is `2` automatically
   because `∑c_j = m+1` and `∑θ_j = 1`.

Three impossibility proofs are recorded in `TameMarkWin.md` so they are not
re-derived: single-anchor-per-factor is infeasible (per-factor MIXING is
necessary); even-integrand interpolation is infeasible for `(2,2,2)` at `m = 5`
(the LP forces the odd `L⁵`, hence a genuine `Lᵖ` scale); rescaling is
homogeneous and cannot move the `Λ^{2q−2}`.

### Verification

Focused checks green: `LowRegC01JetTower.lean`, `FiniteProductHolderFiberNorm.lean`,
`ScratchC01Census.lean`.  Targeted builds green in dependency order
(`FiniteProductHolderFiberNorm`, `LowRegC01JetTower`).  Axiom census run on the
full dispatch list: **`lyapunov_pow_le`, `holder_integral_prod_rpow_le_prod_integral_rpow`,
`holder_integral_prod_riemannianFiberNormSq_le`, `markJet0`, `lc0RiemJet` are
`[propext, Classical.choice, Quot.sound]` — CLEAN.  `gridIntHigh`, `markMon`,
`markJet`, `ricciAAJet`, `lieCovJet`, `lc0VBJet`, `lc0AMixJet`,
`selfLow_jet_quad` and the new `c0_jet_tower_quad` carry `sorryAx`, all through
`gridIntHigh` and nothing else.**  The dispatch's SUCCESS condition (all clean)
is therefore **NOT met** — stated explicitly as required.

### Honest denominators

`gridIntHigh`: **0%** — still `sorry`, statement unchanged, NOT narrowed.  Its
dedicated machinery: ≈ **35%** (the free-weight Hölder assembly pre-existed and
is now identified; `lyapunov_pow_le` built; `GN2` and the assembly are the two
remaining bricks).  Tame C0 bottom: **≈ 95%**, unchanged — one frontier, now
de-risked but not closed.  `c0_jet_tower_quad`: **100%** (stated and proved,
conditional only on `gridIntHigh`).  `lowreg_loMass`: **still 0%** — not stated
in Lean; machinery ≈ 38% → ≈ **41%** (its first tower consumer now exists in the
right shape).  `(N)` `ricci_flow_unif_existence`: **0%** (stated,
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`); nothing this session
touched the theorem.  Whole HCG compactness project: **≈ 3%**.
Route-error counter: **2/3**.

### What the next brick should be told

`gridIntHigh` is now an EXECUTION task.  Dispatch `GN2` first as its own brick
(it is self-contained, has a crisp statement, and is the only place rpow/cast
algebra is needed); the assembly is arithmetic on top of it and should NOT be
bundled into the same session.  Do not narrow `gridIntHigh`, do not add a
balance hypothesis, and do not touch `grid_prod_int_le`.

## Planner update No. 144 (2026-08-04) - PART 2 ACCEPTED (BALL-FREE QUAD TOWER); gridIntHigh RE-PRICED (EXHIBIT TEN); GN2 DISPATCHED

Acceptance: `c0_jet_tower_quad` GREEN (the ball REMOVED from the
signature — `a`/`ha`/`R₀`/`hR₀`/`H^{a+2}` premise all gone; the
statement `lowreg_loMass` actually consumes; conditional only on
`gridIntHigh`).  Part 1's mis-sizing is a PRICING miss by the
No. 143 dispatch, not a route error — the feasibility ruling is
CONFIRMED (quadratic budget holds, `Λ`-exponent exactly 2).  Counter
stays **2/3**.  Gains banked: `lyapunov_pow_le` (the log-convexity
`∫F^c ≤ (∫F^a)^λ(∫F^b)^{1−λ}` — the input `gridIntHigh`'s own
docstring named missing) is PROVED; OVER-COUNT EXHIBIT TEN — the
free-weight Hölder engine already exists public
(`FiniteProductHolderFiberNorm.lean:89` + the sup-bounded split
:153), so no weakened `grid_prod_int_le` clone is needed and the
unbalanced-tuple scare evaporates: `gridIntHigh` is provable IN FULL
GENERALITY (no restatement, no narrowing, no balance hypothesis).
Three impossibility proofs recorded against re-derivation.

DISPATCHED: `GN2` alone (the per-factor two-anchor bound
`(∫ rfns(∇^cP)^{1/θ})^θ ≤ C·Λ^{2(c−θm)}·R^{2θ}` — self-contained,
rpow/cast algebra); the assembly (free weights
`θⱼ = (1−t)(cⱼ−1)/(m−1) + t·cⱼ/m`) is the brick after.

Honest denominators: `gridIntHigh` 0% (machinery ≈ 35%); tame C0
≈ 95% (de-risked); `c0_jet_tower_quad` 100% conditional;
`lowreg_loMass` 0% (machinery ≈ 41%); (N) 0% (stated, sorry :98);
whole HCG ≈ 3%.  Route-error counter: **2/3**.

## Executor report No. 144-executor (2026-08-04) - GN2 LANDED, sorry-free and axiom-clean; FULL `(c, θ)` RANGE, no narrowing

**GN2 is PROVED.**  `gnTwoAnchor`,
`Analysis/Sobolev/TensorHilbert/GNTwoAnchor.lean:249` (new file, 422 lines),
namespace `DifferentialGeometry.Integral.Connection`.  Axiom census:
`[propext, Classical.choice, Quot.sound]` — CLEAN.  Focused check green;
targeted build `+DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GNTwoAnchor`
green (9537 jobs).  Route-error counter unchanged (**2/3**); no STOP condition
was triggered, and No. 143's feasibility ruling is CONFIRMED again — the
exponent identity closes exactly, with no slack.

### The statement

Constants first, state after; valence-generic `(r, s)`:

```
gnTwoAnchor (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
  ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
    ∀ (Ψ : SmoothCcTensor g₀ r s) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
      (∀ x, rfns g₀ r s x (Ψ.toSection x) ≤ Λ₀ ^ 2) →
      (∀ x, rfns g₀ r (s+1) x ((iteratedCovGrad g₀ r s 1 Ψ).toSection x) ≤ Λ₁ ^ 2) →
      ∀ m c : ℕ, 2 ≤ c → c < m → ∀ θ : ℝ,
        ((c:ℝ) - 1)/((m:ℝ) - 1) ≤ θ → θ ≤ (c:ℝ)/(m:ℝ) →
        (∫ x, rfns g₀ r (s+c) x ((iteratedCovGrad g₀ r s c Ψ).toSection x) ^ (1/θ)
            ∂(riemannianVolumeMeasure g₀)) ^ θ ≤
          C m * Λ₁ ^ (2 * ((c:ℝ) - θ * (m:ℝ))) * ‖iteratedCovGrad g₀ r s m Ψ‖ ^ (2*θ)
```

`C m = max 1 (A m) * max 1 (B (m-1)) ^ (2:ℝ)` — state-free, independent of
`Ψ, Λ₀, Λ₁, c, θ`.  At `r = 0, s = 2` the integrand IS `gridBase g₀ P x c` on the
nose and the top jet IS `gridIntHigh`'s `‖iteratedCovGrad g₀ 0 2 m P‖`.

**Range audit (asked for explicitly).**  Class-3 monomials are
`∏_{j≤q}|∇^{c_j}P|²`, `q ≥ 3`, `c_j ≥ 2`, `∑c_j = m+1`; hence
`c_j ≤ m+1-2(q-1) ≤ m-3 < m`, so `2 ≤ c_j < m` holds for every factor, and the
assembly's `θ_j = (1-t)(c_j-1)/(m-1) + t·c_j/m` with `t ∈ [0,1]` lies in
`[(c_j-1)/(m-1), c_j/m]` by construction.  **Every `(c_j, θ_j)` pair the class
generates is covered.**  No narrowing, no balance hypothesis, no fallback used.

### One correction to the dispatch

`Λ` does NOT need to be `max Λ₁ 1`.  The `Λ₁` exponent `2(c - θm)` is exact and
nonnegative on the range (it vanishes precisely at the `Ψ`-anchored endpoint
`θ = c/m`), so the honest anchor is `Λ₁` itself under `0 ≤ Λ₁` alone.  The
assembly should NOT introduce a `max`; `Λ₁² ≤ 1 + Λ₁²` at the very end is the
only softening needed to hit `gridIntHigh`'s RHS.

### Home (deviation from the dispatch, with the reason)

Not "beside `lyapunov_pow_le` or the GN primitives": `GagliardoNirenbergLpFiberNorm.lean`
is 5642 lines (already over the 3000-line rule — must not grow) and
`FiniteProductHolderFiberNorm.lean` sits below the `iteratedCovGrad` layer.  The
deciding fact is that the two composition bridges GN2 consumes — `icgNormComp`
and the public `tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs` —
both live in `Analysis/Sobolev/TensorHilbert/`.  Placing GN2 lower would have
forced a duplicate of `icgNormComp`; `TensorHilbert/` is the canonical home.

### Structure (three private helpers, all reusable inside the file)

`rpowFlip` (`X^a ≤ Y`, `a·b = 1` ⟹ `X ≤ Y^b`); `gnMixCore` (the entire
interpolation as pure real analysis, endpoints as hypotheses — this is what kept
the rpow/cast grind out of the geometric proof); `gnFam` (the `Lᵖ` GN scale
repackaged with its constant as a `ℕ → ℝ` family indexed by top order, the shape
`gridIntHigh`'s `∃ K : ℕ → ℝ` needs).

### The arithmetic, for the record

`pA = m/c`, `pB = (m-1)/(c-1)`, `lam = (pB - 1/θ)/(pB - pA) ∈ [0,1]`,
`1/θ = lam·pA + (1-lam)·pB`.  Endpoint A discards `Λ₀^{2(1-c/m)} ≤ 1`; endpoint
B is the same GN theorem at base `∇Ψ`, valence `(r, s+1)`, `k = m-1`, `j = c-1`.
Both flipped to `∫F^p ≤ K^p·R²`, joined by `lyapunov_pow_le`, raised to `θ`.
**`θ·(1-lam)·(pB-1) = c - θm` exactly** — proved in Lean via three factored
quotients plus one `field_simp` (the unfactored `field_simp` fails: the compound
denominator `pB - pA` is not recognized nonzero).  Constant absorption uses
`θ·pA ≤ 1` and `θ·pB ≤ c(m-1)/(m(c-1)) ≤ 2`; the second is the ONLY place
`c ≥ 2` (rather than `c ≥ 1`) is spent.

### Lean lessons (full list in `GNTwoAnchor.md`)

`MeasurableSpace M` is NOT ambient in `TensorHilbert/` — stating
`Integrable f (riemannianVolumeMeasure …)` needs the four `borel`/`BorelSpace`
`private local instance`s, and `Continuous.integrable_of_hasCompactSupport`
additionally needs an explicit
`haveI : IsFiniteMeasureOnCompacts … := riemannianVolumeMeasure_isFiniteMeasureOnCompacts …`.
Substituting `c = 1+d`, `m = 1+n` (rather than fighting `c-1`) is what makes
`rfns_iteratedCovGrad_comp` match syntactically under the integral binder.
Name the integrand by `obtain ⟨F, hFapp⟩ : ∃ F, ∀ x, <long> = F x := ⟨_, fun _ => rfl⟩`,
not `set` (`set` will not fold an applied lambda under a binder; `simp only [hFapp]`
will).  `rw [mul_div_assoc]` before `set`ting an exponent, or `2 * ↑j / ↑k` hides
the quotient.  `Real.rpow_add'` avoids the `R = 0` case split.  This Mathlib rev
wants `div_le_iff₀` / `le_div_iff₀` / `div_lt_div_iff₀`.

### Verification

Focused check green (`GNTwoAnchor.lean`).  Targeted build green.  Axiom census:
`gnTwoAnchor` = `[propext, Classical.choice, Quot.sound]`.  Nothing else in the
tree was touched — `gridIntHigh` untouched and still `sorry`, `grid_prod_int_le`
untouched, `markMon` untouched.  All claims released.

### Census (explicit)

`gnTwoAnchor` CLEAN.  `gridIntHigh`, `markMon`, `markJet`, `ricciAAJet`,
`lieCovJet`, `lc0VBJet`, `lc0AMixJet`, `selfLow_jet_quad`, `c0_jet_tower_quad`
still carry `sorryAx`, all through `gridIntHigh` and nothing else — unchanged
from No. 143-executor, because this session added a producer and wired nothing.

### Honest denominators

`gnTwoAnchor` (this brick): **100%** — stated, proved, axiom-clean.
`gridIntHigh`: **0%** — still `sorry`, statement unchanged, NOT narrowed.  Its
dedicated machinery: ≈ 35% → **≈ 70%** (free-weight Hölder pre-existing,
`lyapunov_pow_le` built last session, GN2 built now; only the assembly remains).
Tame C0 bottom: **≈ 95%**, unchanged — one frontier, now genuinely one brick
away.  `lowreg_loMass`: **still 0%** (not stated in Lean); machinery ≈ **41%**,
unchanged.  `(N)` `ricci_flow_unif_existence`: **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; nothing this session
touched the theorem.  Whole HCG compactness project: **≈ 3%**.
Route-error counter: **2/3**.

### What the assembly brick should be told

Import `…TensorHilbert.GNTwoAnchor` into `TameMarkWin.lean` (GN2 is a leaf;
it imports only `GradCapAtgw`, `GagliardoNirenbergLpFiberNorm`,
`FiniteProductHolderFiberNorm`, so no cycle).  Use
`holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound` (`:153`) to drop the
weight-0 entries against `Λ₀ ≤ 1`, then the free-weight Hölder (`:89`) at
`θ_j = (1-t)(c_j-1)/(m-1) + t·c_j/m`, `t = (1-L)/(U-L)`, `L = (m+1-q)/(m-1)`,
`U = (m+1)/m`.  Do NOT introduce `max Λ₁ 1`.  Watch the `q`-dependence of the
final constant: the product contributes `C m ^ q` and `q ≤ 2 + k ≤ m + 1`, so
bound `q` by `m+1` BEFORE choosing `gridIntHigh`'s state-free `K m`.

## Planner update No. 145 (2026-08-04) - GN2 ACCEPTED (FULL RANGE, SORRY-FREE); FINAL gridIntHigh ASSEMBLY DISPATCHED

Acceptance: `gnTwoAnchor` (`TensorHilbert/GNTwoAnchor.lean:249`,
new 422-line file) GREEN — full `(c, θ)` range, valence-generic,
constants-first, census `[propext, Classical.choice, Quot.sound]`;
the range audit confirms every class-3 pair is covered; the home
deviation is RATIFIED (both suggested homes were unsuitable — one
over the line cap, one below the `iteratedCovGrad` layer; the
composition bridges live in `TensorHilbert/`).  The two assembly
handoff facts are recorded above (exact `Λ₁`-exponent, no
`max Λ₁ 1`; bound `q ≤ m+1` before choosing `K m`).  The one real
arithmetic (`θ(1−lam)(pB−1) = c − θm` via three factored quotients +
`field_simp`) is banked in `GNTwoAnchor.md`.

DISPATCHED: the FINAL `gridIntHigh` assembly brick — free-weight
Hölder (`FiniteProductHolderFiberNorm.lean:89` + :153) over the
class-3 monomials, `gnTwoAnchor` per factor at the recorded weights,
land on `markMon`'s required shape, replace the sorry at
`TameMarkWin.lean:591`.  SUCCESS ⟹ the ENTIRE tame C0 bottom
(six arm jets + `selfLow_jet_quad` + `c0_jet_tower_quad`) becomes
axiom-clean, and the campaign returns to the audit's post-tame lane
(J0/J1/J2/J4/J5/J6/J7).

Honest denominators: `gridIntHigh` 0% (machinery ≈ 70% — assembly
only); tame C0 ≈ 95%; `lowreg_loMass` 0% (≈ 41%); (N) 0% (stated,
sorry :98); whole HCG ≈ 3%.  Route-error counter: **2/3**.

## Executor report No. 145-executor (2026-08-04) - `gridIntHigh` PROVED; THE TAME C0 BOTTOM IS FULLY AXIOM-CLEAN

**Verdict: SUCCESS.**  `gridIntHigh` (`TameMarkWin.lean`, formerly the `sorry`
at `:591`) is proved.  Statement unchanged: not narrowed, no balance hypothesis,
`grid_prod_int_le` untouched, no `max Λ₁ 1` introduced.  The dispatch's SUCCESS
condition is met — the entire tame C0 bottom is axiom-clean.  Route-error counter
unchanged (**2/3**); no STOP condition triggered, no fallback used, no scoped
sorry.  No. 143's feasibility ruling is confirmed a third time: the `Λ₁`-exponent
sum is exactly `2`, with no slack.

### What landed

`gnProdJet`, `Analysis/Sobolev/TensorHilbert/GNTwoAnchor.lean` (the file grew
422 → 611 lines; still one file, still under the cap):

```
gnProdJet (g₀) (r s : ℕ) :
  ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
    ∀ Ψ {Λ₀ Λ₁}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ → (sup bounds on Ψ, ∇Ψ) →
      ∀ (m N : ℕ) (c : Fin N → ℕ) (t : Finset (Fin N)),
        (∀ j ∈ t, 2 ≤ c j) → (∀ j, j ∉ t → c j = 0) → 2 ≤ t.card →
        (∑ j ∈ t, c j) = m + 1 →
        ∫ ∏ j : Fin N, |∇^{c j}Ψ|² ≤ K m · Λ₁² · ‖∇^mΨ‖²
```

`K m = max 1 (C m) ^ (m + 1)` with `C` from `gnTwoAnchor`: state-free, and `q`
is bounded by `m + 1` (each active order is `≥ 2`) **before** `K` is chosen, as
the dispatch required.  `gridIntHigh` then reuses that same `K` verbatim — no new
constant is invented in `TameMarkWin.lean`.

**The exponent-sum lemma is `gnExpSum`** (private, `GNTwoAnchor.lean`), the
design's core:

```
gnExpSum (s) (cf θ : ι → ℝ) (mR : ℝ) :
  ∑ j ∈ s, cf j = mR + 1 → ∑ j ∈ s, θ j = 1 → ∑ j ∈ s, 2 * (cf j - θ j * mR) = 2
```

Four lines.  The content is that it holds for ANY weight family summing to `1`,
so the quadratic budget is pinned before the weights are chosen.  Its companion
`gnFreeWt` builds the weights themselves at the recorded values — `L =
(mR+1−card)/(mR−1)`, `U = (mR+1)/mR`, `tt = (1−L)/(U−L)`, `θ j = (1−tt)(cf j
−1)/(mR−1) + tt·(cf j)/mR` — and returns `∑ θ = 1` together with the band
membership `(cf j −1)/(mR−1) ≤ θ j ≤ cf j / mR` that `gnTwoAnchor` consumes.  The
№144-era range audit is confirmed: the band is non-degenerate exactly because
`cf j ≤ mR`, and `tt ∈ [0,1]` exactly because `card ≥ 2`.

### Two corrections to the dispatch, both weakenings

1. **`2 ≤ q` suffices; `3` is not needed.**  At `q = 2` the ratio is `tt = 0` and
   the weights collapse to the pure `∇Ψ`-anchored family, which already sums to
   `1`.  `gnProdJet` is therefore stated at `2 ≤ t.card` (weakest-assumptions
   rule); `gridIntHigh`, which always has `q ≥ 3`, simply meets it.
2. **`1 ≤ k` is not used.**  `gridIntHigh`'s two marked factors alone give
   `q ≥ 2`; the unmarked block may be empty as far as the assembly is concerned.
   The hypothesis stays in the statement (it is part of the dispatch shape and
   `markMon` supplies it), but nothing depends on it.

The active set enters `gnProdJet` as an explicit `Finset` with "orders off it are
`0`", not as `univ.filter (c · ≠ 0)`.  That keeps `DecidablePred` out of the
statement, so a caller under `classical` cannot hit an instance mismatch when
folding its own filter — the one design correction the session needed.

### `gridIntHigh` itself

Pure bookkeeping, ~55 lines: `cc := Fin.cons c₁ (Fin.cons c₂ e)` on `Fin (n+2)`;
`Fin.prod_univ_succ` twice plus `ring` identifies the marked monomial with
`∏_j gridBase (cc j)`, which is *definitionally* `gnProdJet`'s integrand
(`change`, no rewriting); `t := univ.filter (cc · ≠ 0)` with `2 ≤ t.card` from
`{0, Fin.succ 0} ⊆ t`; then `Λ₁² ≤ 1 + Λ₁²` lands on the required RHS.

### Verification

Focused checks green and **warning-free** on both edited files.  Targeted builds
green in dependency order: `+…TensorHilbert.GNTwoAnchor`, then
`+…TensorHilbert.TameMarkWin`, then `+…DeTurck.ScratchC01Census` (9626 jobs).

### Census (explicit)

Every dispatched target is `[propext, Classical.choice, Quot.sound]`:
`gridIntHigh`, `markMon`, `markJet`, and all six arm jets — `markJet0`,
`ricciAAJet`, `lieCovJet`, `lc0VBJet`, `lc0AMixJet`, `lc0RiemJet` — plus
`selfLow_jet_quad`, `c0_jet_tower_quad`, `gnTwoAnchor` and the new `gnProdJet`.
**`sorryAx` occurs zero times in the whole `ScratchC01Census` output.**

**The tame C0 bottom is fully axiom-clean.**

### Honest denominators

`gridIntHigh`: **100%** — stated and proved, statement unchanged.  `gnProdJet`
(this brick): **100%**.  Tame C0 bottom: **100%** — no frontier left; its two
consumers `selfLow_jet_quad` and `c0_jet_tower_quad` are now unconditional.
`lowreg_loMass`: **still 0%** — not stated in Lean; its dedicated machinery
≈ 41% → ≈ **46%** (the audit's J3 deliverable is now real rather than
`sorry`-conditional; J0/J1/J2/J4/J5/J6/J7 are untouched).  `(N)`
`ricci_flow_unif_existence`: **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; nothing this session
touched the theorem.  Whole HCG compactness project: **≈ 3%**.
Route-error counter: **2/3**.

### What the next brick should be told

Per `CODEX_LOMASS_AUDIT.md` §5, the viability gate is "quantitative `C0` `H³`²
coefficient **plus** the first tower-direct bottom closure".  The first half is
now delivered unconditionally (J3 = `selfLow_jet_quad` + `c0_jet_tower_quad`,
both axiom-clean).  **The next brick is J4: the tower-direct bottom-rung
closure at `k = 3`** — the lowest rung, no `H⁵` radius, no inverse estimate, no
same-rung radius in its own Grönwall coefficient.  Its producer is
`c0_jet_tower_quad` read at `i = k−1 = 2` (its `range (i+2)` state-jet budget is
exactly what `PSTOP_PROPOSITION.md` §6.3 pairs), and its algebraic engine is
`two_mul_sum_ladder_le` (`Sobolev/Tensor/CrossScaleCauchySchwarz.lean:232-247`),
which needs only `α, β, D` supplied.  Do the bottom rung alone first; rungs 4
and 5 are the brick after, and J0/J1/J2/J5/J6/J7 stay behind the gate.

## Planner update No. 146 (2026-08-04) - **TAME C0 BOTTOM FULLY AXIOM-CLEAN** (J3 CLOSED); J0/J5 RECON ADOPTED; [J0a + J5 + J4-RUNG-3] DISPATCHED

MILESTONE ACCEPTED: `gridIntHigh` proved (statement unchanged, no
narrowing/balance/`max Λ₁ 1`; `grid_prod_int_le` untouched); the
ENTIRE tame C0 bottom — six arm jets, `selfLow_jet_quad`,
`c0_jet_tower_quad` — is axiom-clean.  The audit's DECISIVE gap
(J3) is closed.  `gnProdJet`/`gnExpSum`/`gnFreeWt` landed; the two
dispatch corrections are WEAKENINGS (`2 ≤ q` suffices; `1 ≤ k`
unused) — ratified per the weakest-assumptions rule.  №143's
feasibility confirmed a third time (`Λ₁`-exponent sum exactly 2).

J0/J5 RECON ADOPTED (`POSTTAME_J0J5_PLAN.md`): J0's widening = ONE
binder (`hDim`) + `IsLowSolve` repairs (delete `g_bg`; δ-range and
`coreN`-continuity as body conjuncts); satisfiability GREEN, zero
producer work.  J5 = IN-PLACE generalization (zero call sites;
conclusion unchanged; the substitution proof generalizes).  The
J0a/J0b SPLIT adopted (J0b = absorption, behind J4).  Exhibit
ELEVEN registered CONDITIONALLY (sequencing flavor; confirm iff
J0a ≤ 1 session).  RE-PRICING adopted: post-tame remainder 11–18,
central 14 (not "14 − consumed").

SEQUENCING RECONCILIATION: the assembly executor's "J4 rung 3
first, rest behind the gate" and the recon's "J0a/J5 first"
COMPOSE — J0a's δ★ threading and J5's N-indexed engine are the rung
calibration's inputs, and all three are small.  DISPATCHED as ONE
brick: [J0a + J5 + J4-rung-3] — the widening/certificates, the
engine index, then the first tower-direct bottom closure at k = 3
(producer `c0_jet_tower_quad` at i = 2; engine
`two_mul_sum_ladder_le`; supply `α, β, D` per the calibration
design; no H⁵ radius, no inverse estimate, no same-rung radius).
Rungs 4–5 are the brick after; the audit's second gate-half closes
with rung 3.

Honest denominators: tame C0 bottom 100% CLEAN; `lowreg_loMass` 0%
(machinery ≈ 45%); (N) 0% (stated, sorry :98); whole HCG ≈ 3%;
post-tame ≈ 14 central.  Route-error counter: **2/3**.

## Executor report No. 146-executor (2026-08-04) - J0a DONE, J5 DONE; J4-RUNG-3 **NOT DELIVERED**, narrowed to three named pieces

**LEAD WITH THE FAILURE.  J4-rung-3 was not stated.**  The dispatch's premise —
"the algebraic engine `two_mul_sum_ladder_le` needs only `(α, β, D)` supplied" —
**under-counts by three pieces**, and writing the closure now would have required
all three as fresh hypotheses.  That is the frontier-wrapper failure mode
`CLAUDE.md` forbids, so nothing was stated.  This is a **dispatch scoping
under-count**, not a route error: no wrong route was implemented, the finding came
out of read-only recon.  **Planner must rule whether it increments the
route-error counter; I left it at 2/3.**

Classification: **missing groundwork / API**, not a mathematical obstruction.

**The dispatch's own STOP condition was NOT met.**  The pairing budget at `k = 3`
HOLDS.  At `σ = 3` the engine wants `‖fd‖_{H²} ≤ α‖u‖_{H⁴} + β‖u‖_{H³}`, which is
exactly `n_diff_hm_rung`'s shape read at `m = k−1 = 2`; and `c0_jet_tower_quad` at
`i = 2` has window `range 4`, i.e. state jets `j ≤ 3`, inside `E₃` and strictly
below `E₄`.  PSTOP §6.3's displayed pairing is CONFIRMED at rung 3, with room.
The obstruction is UPSTREAM of the pairing.

### The three missing pieces (full census in `LowRegAllOrderJet.md`)

* **(M1) Finset-form Bessel truncation** — `∑_{i∈S} w i σ (v.coeff i)² ≤ ‖v‖²_{Hˢ}`.
  Only the SINGLE-mode `weight_mul_coeff_sq_le_normSq` existed.  This is the step
  that lets the truncated pairing term read a full-`Hˢ` ladder bound.
  **LANDED THIS SESSION** as `tensorHs.weight_sum_le_normSq`
  (`Spectral/Intrinsic/TensorHsInterpolationLimit.lean`, beside the single-mode
  lemma); 5-line proof via `Finset.sum_le_tsum` + `weighted_summable`.
* **(M2) a low-lane Galerkin forcing at `a = 1`** — `deTurckGalerkinForcingSymm`
  is defined through `deTurckSobolevNHa2Symm`, which only EXISTS above the
  Lipschitz gate `2*finrank+10 ≤ a`.  At `a = 1` no mode-coordinate forcing
  function is defined for `lowregNfun`.  **Without it the rung-3 closure has no
  `Fseq` to be stated about.**  This is producer #2 of the three that
  `lowreg_loMass`'s own docstring already lists; the dispatch treated it as
  present.
* **(M3) ball-free (quad) ladders** — `a2_ladder` / `a1_ladder` /
  `n_diff_hm_rung` all carry `‖T‖_{H^{a+2}} ≤ R₀` with `a ≥ 3` (resp. `2`), i.e.
  the H⁵ (resp. H⁴) ball the dispatch forbids at rung 3.  J3 delivered the
  ball-free `c0_jet_tower_quad`, but the ladders above it were never re-derived
  on it.
  Refinement (grep-verified): the a₂ arm's H⁵ ball sits in `appCc_cap_hs_le`
  (`LowRegLadderRung.lean:78`, gate `max 2 (finrank/2*2+1) ≤ a`), NOT in
  `c2_jet_tower` — whose `a`, `R₀`, `hball` binders are vestigial (its proof goes
  through `topKer_jet g`, which takes only `hDim` and `g`).  So M3 splits into an
  a₂ half (re-read `appCc_cap_hs_le` at a lower `a`, or a quad sibling) and an a₁
  half (thread `c0_jet_tower_quad` through the private `coeffCap`).
  FEASIBILITY, and why dimension three matters: `coeffCap`'s window is
  `range (finrank/2 + 2) = range 3`, i.e. state jets `j ≤ 2` — so the quad route
  needs only the **H² state ball** (PSTOP §6.1(i)), never H⁵, with the extra
  `K2*‖T‖²_{H³}` term carrying the `L²_tH³` dependence (§6.1(ii)) that becomes the
  `A N t` coefficient.  **That is precisely why J5 had to land first.**

Recommended next-brick order: **M3 → M2 → the calibration**.  M1 is done.

### J0a — DONE, sorry-free, all four steps

1. **`realize_at_delta`** — the δ-generic `H²` realization radius (`R := δ/C` from
   `hs2_op_bound`).  `realize_at_thr`, `lowreg_realize_h2` and `lowreg_realize`
   are now all instances; ~45 lines of triplicated proof removed.
   **PLACEMENT CORRECTION to `POSTTAME_J0J5_PLAN.md` §A.6.1:** the plan put it in
   `LowRegDenseSolve.lean` while also asking that all three copies fold onto it.
   Incompatible — `LowRegDenseSolve` IMPORTS `LowRegRealize`.  It lives in
   `LowRegRealize.lean`, the lowest file with `hs2_op_bound`: both the canonical
   home and the only placement that folds all three.
2. **`lowreg_solve_two` takes the threshold as a parameter** —
   `{thr : ℝ} (hthr : 0 < thr) (hthr3 : thr ≤ 1/3)`; conclusion UNCHANGED (`δ`
   stays existential, now instantiated to `thr`).  Body churn was exactly the
   three `have`s plus three type ascriptions — the plan's claim that everything
   else was already δ-generic is CONFIRMED.  Named `thr`, not the plan's `δ★`:
   ASCII, and it avoids shadowing the conclusion's own `δ`.
3. **`IsLowSolve` repaired** — `g_bg` binder DELETED (self-background); `0 ≤ δ`,
   `δ ≤ 1/3` and `Continuous (coreN g₀ g₀ hδ (lowregRealRad …))` added as body
   conjuncts.  `isLowSolve_of_sol` drops one argument and gains three.
   **The plan's proof-irrelevance prediction is CONFIRMED**: at the unique call
   site, `hcoreN : Continuous (coreN g g hδ (realizeOfLE g le_rfl hrealR))` closes
   the slot wanting `coreN g g hδ hrealR` by a bare `exact` — Lean 4 definitional
   proof irrelevance, no `convert`, no `show`.  One destructuring consumer
   re-patterned (`LowRegGalerkinIdent.lean`), three fields taken as `-`.
4. **`hDim` on `lowreg_loMass` and `lowreg_spatialMass`** — conclusions untouched;
   propagation was one argument at two call sites, both of which already bound
   `hDim`.  `lowreg_loMass` is STILL `sorry`; the widening only makes the eventual
   proof statable.

Producer work required: **zero**, as the plan predicted — every new field was
already a named `have` in `lowreg_solve_two`'s context.

### J5 — DONE, sorry-free, in place

`galerkin_energy_l1_bound`: `A S : ℝ → ℝ` becomes `ℕ → ℝ → ℝ`; the five
`S`-hypotheses `∀ N`; `hclosure`'s coefficient `Cmid k + A N t`.  `Sbd` stays a
shared SCALAR — that is the `N`-uniformity mechanism, and it is why the
**conclusion is unchanged**.  `energy_hier_l1_bound` untouched.  Zero call sites,
so no alias and no shim.  The `intro N`-before-`A`-use structure made it
mechanical, exactly as the recon said.

### Verification

Focused checks GREEN on six files: `GalerkinParabolicEnergy`, `LowRegRealize`,
`LowRegDenseSolve`, `UnifClassBounds`, `LowRegApplyTwo`, `LowRegGalerkinIdent`.
`LowRegApplyTwo` was checked against FRESH oleans (targeted builds
`+…LowRegRealize` and `+…UnifClassBounds`, the latter rebuilding
`LowRegDenseSolve`), so the new `isLowSolve_of_sol` signature and
`realize_at_delta` were genuinely in scope.

Focused checks GREEN on all EIGHT edited files — the six above plus
`LowRegAllOrderJet` (one `sorry` warning, at `:1052`, the pre-existing
`lowreg_loMass`; nothing else) and `TensorHsInterpolationLimit` (M1).

Targeted builds GREEN in dependency order: `+…LowRegRealize`,
`+…UnifClassBounds` (rebuilding `LowRegDenseSolve`), `+…LowRegApplyTwo`
(**9984 jobs** — editing `LowRegRealize.lean`, a LOW file, forces a rebuild of
the whole ShortTime cone), `+…TensorHsInterpolationLimit` (8707 jobs),
`+…LowRegAllOrderJet`.

**AXIOM CENSUS — 11 declarations, explicit.**  `[propext, Classical.choice,
Quot.sound]` on all NINE touched or new declarations: `galerkin_energy_l1_bound`
(J5), `realize_at_delta`, `realize_at_thr`, `lowreg_realize_h2`, `lowreg_realize`,
`isLowSolve_of_sol`, `lowreg_solve_two`, `lowreg_proj_tendsto`,
`lowreg_projMode_tendsto`, plus `tensorHs.weight_sum_le_normSq` (M1).
`sorryAx` appears on exactly TWO: `lowreg_loMass` and `lowreg_spatialMass` —
the single pre-existing frontier and the theorem that transports it.
**J0a, J5 and M1 introduced no new axiom dependency and no new `sorry`.**

Lesson for the next dispatch: a one-line edit in a LOW ShortTime file costs a
full-cone rebuild (~9 984 jobs at `-LeanThreads 1`).  Budget it, or batch
low-file edits first.  Lean-name lesson: the Mathlib truncation lemma is
`Summable.sum_le_tsum` with `(Finset) (nonneg-off-s) (Summable)` argument order —
`Finset.sum_le_tsum` exists only in the `ENNReal` namespace.

### Exhibit eleven — CONFIRMED

`POSTTAME_J0J5_PLAN.md` §C.4 said to register it iff J0a lands at or under one
session.  **It did** — J0a landed as a share of one session, alongside J5 and the
J4 recon.  Register exhibit eleven (sequencing): the audit put the whole "honest
producer" phase behind the viability gate, but three of the four repairs were
already named `have`s in the producer's context and the only genuine δ-pin was
one hard-coded witness.

Two-sided honesty: the same session produced the OPPOSITE finding on J4 — a
dispatch UNDER-count.  The recon-optimism correction runs both ways.

### Honest denominators

`lowreg_loMass`: theorem **0%** (`LowRegAllOrderJet.lean`, still `sorry`); its
dedicated machinery ≈ 46% → ≈ **51%** (J0a and J5 closed — 2 of the audit's 8
joints, and 2 of the cheap ones; J4, the dominant one, is untouched apart from M1
and the census).  J4-rung-3: **0% stated**; of its three prerequisites M1 is 100%,
M2 and M3 are 0%.  Tame C0 bottom: **100%** (unchanged).
`(N) ricci_flow_unif_existence`: theorem **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; untouched.
Whole HCG compactness project: ≈ **3%**.
Post-tame remainder: still **11–18, central 14** — this session consumed roughly
one of the "J5 + J0a + J1: 2–3" allocation, and J4's 4–7 is unchanged (the M2/M3
discovery makes the low end of that range unlikely).
Route-error counter: **2/3** (planner to rule on the under-count).

## Planner update No. 147 (2026-08-04) - J0a+J5+M1 ACCEPTED; COUNTER RULED 2/3 (UNDER-COUNT ≠ ROUTE ERROR); M3 DISPATCHED

Acceptance: J0a (widening + `IsLowSolve` repairs + `realize_at_delta`
with the placement CORRECTION ratified — the plan's home imported the
wrong way, it lives in `LowRegRealize.lean`), J5 (in-place N-index),
and M1 (`tensorHs.weight_sum_le_normSq`, the Finset Bessel) all
census-clean; the proof-irrelevance prediction confirmed (`exact`);
exhibit ELEVEN CONFIRMED (J0a ≤ 1 session-share).  The executor's
refusal to state the rung-3 closure over three fresh hypotheses is
RATIFIED — that is exactly the frontier-wrapper failure mode the
project rules forbid.

**COUNTER RULING: 2/3 UNCHANGED.**  The J4 premise ("only α, β, D")
was an under-count, not a route error: no wrong route was
implemented (the finding came from read-only recon inside the
session); the STOP condition did NOT fire — the k = 3 pairing budget
HOLDS with room (the §6.3 design is confirmed); M2 is a producer
`lowreg_loMass`'s own docstring already lists; M3 comes with its own
feasibility refinement (the H⁵ ball lives in `appCc_cap_hs_le`, NOT
in `c2_jet_tower` whose ball binders are VESTIGIAL; the quad route
needs only the H² state ball — which is exactly why J5 landed
first).  Taxonomy: missing groundwork.  The under-pricing pattern is
real and stands in the honest footers (J4's low end unlikely).

DISPATCHED: **M3** — the ball-free (quad) ladders: re-derive the
`a2`/`a1`/`n_diff_hm_rung` layer over the QUAD towers
(`c0_jet_tower_quad` + the c1/c2 towers) with only the H² state
ball, exorcising the vestigial `H^{a+2}` binders (the ball enters at
`appCc_cap_hs_le:78` only).  Then M2 (the a = 1 mode-coordinate
forcing), then the calibration — per the executor's order.

Honest denominators: `lowreg_loMass` 0% (machinery ≈ 51%, 2 of the
audit's 8 joints closed); (N) 0% (stated, sorry :98); whole HCG
≈ 3%; post-tame 11–18 central 14.  Route-error counter: **2/3**.

## Planner update No. 148 (2026-08-04) - EXHIBIT TWELVE: M2 IS A FALSE WALL (galTameForce EXISTS); BRICK-(1) DELETION RULING SUPERSEDED; M2 RE-SCOPED TO TWO ADAPTERS

The M2 recon (`M2_FORCING_PLAN.md`) found the a = 1 mode-coordinate
forcing ALREADY IN THE TREE: `galTameForce`
(`HeatSemigroup/GalerkinTameSol.lean:549` — its docstring literally
says "the tame analogue of `deTurckGalerkinForcingSymm`"; no gate,
generic; `_apply` simp-rfl, `_eq` bridge), instantiated at a = 1 for
`lowregNfun` by `lowregGalSol` (`ShortTime/LowRegGalerkinSol.lean:91`,
whose header calls itself "the first" of `lowreg_loMass`'s three
producers).  Timing unarguable (files written 11:32/11:39; the
"missing" claim recorded 21:15/22:23); root cause: BOTH FILES ARE
UNTRACKED, so the census grep missed them.  NEW RULE: census greps
must include untracked files (`git status --short` first; grep the
worktree, not the index).

**CONSEQUENCE FOR THE RECORD: the Codex audit's "delete brick (1)"
ruling is SUPERSEDED** — brick (1)'s artifacts are LOAD-BEARING
(producer #1 = `lowregGalSol`; the forcing = `galTameForce`).  Route
error No. 2-of-the-new-count was scored on that deletion ruling;
whether to decrement is the USER's call under the reset semantics —
flagged, not decided here.  Counter formally stays **2/3**.

Two more over-counts corrected in passing: `deTurckSobolevNHa2Symm`
binds NO gate (a `dite` with `else 0` — exists at a = 1, junk
branch); and two distinct gates were being conflated (the forcing's
Lipschitz gate `2·finrank+10` vs the closure's `4·finrank+10`).

M2 RE-SCOPED: two adapter lemmas, ≈ 1 session — M2a
`galTameForce_contOn` (route via `galTameField_lip` + the in-file
bridge, ~15–25 lines) and M2b `galTamePerMode` (mechanical port of
the private original with `ha_super` deleted; import-cone verified,
zero churn).  Disjoint from M3's files; dispatch after M3 (single
Lean process).  The energy engine consumes NOTHING from `Fseq` but
`hderiv` and `hclosure` — the free list covers everything else.

Honest denominators: `lowreg_loMass` 0% (machinery ≈ 55%; producer
#1 done, #2 ≈ 70% pre-existing, #3 = the real frontier);
(N) 0% (stated, sorry :98); whole HCG ≈ 3%.  Route-error counter:
**2/3** (user may adjust re the superseded deletion).

## Executor report No. 148-executor (2026-08-04) - M3 PARTLY DELIVERED: ball BINDERS gone (5 new decls, census-clean); the H²-ONLY LOWER CONSTANT IS **IMPOSSIBLE** — STOP-AND-REPORT, planner ruling needed on the rung design

**LEAD WITH THE FAILURE.**  The dispatch's target — "the LOWER constant
depending only on the H² state ball / the quad towers' `(K₀ + K₂‖T‖²_{H³})`
data" — **cannot be met**, and not for tooling reasons.  This is the dispatch's
own declared STOP condition ("if the Hs-assembly genuinely cannot close without
a ball above H²"), and it fires.  Classification: **mathematical/structural**,
not missing groundwork.  I did NOT state anything over fresh hypotheses.

**The sharp count** (route-independent; full derivation in
`LowRegLadderRung.md` §M3).  `a₂T = appCc C₂ (∇²T)`; Leibniz at rung `q` gives
`∑_{l≤q}‖∇^l C₂ ⊗ ∇^{q-l+2}T‖_{L²}`.  `l = 0` is the top term, charged to the
pointwise fibre cap — genuinely δ-only and ball-free, as designed.  For `l ≥ 1`
one factor must go to `L^∞`, which in dimension three costs `finrank/2 + 2 = 3`
extra `L²`-orders.  Both Hölder splits land on the SAME total order `q + 5`:

* `‖∇^lC₂‖_∞·‖∇^{q-l+2}T‖_{L²}` ⟹ `(l+3) + (q-l+2)`  (tower: `‖∇^iC₂‖_{L²} ≲ 1 + ‖T‖_{H^{i+1}}`)
* `‖∇^lC₂‖_{L²}·‖∇^{q-l+2}T‖_∞` ⟹ `(l+1) + (q-l+4)`

The ladder's lower slot is `‖T‖_{H^{q+1}}`, so the log-convexity trade
`f α·f β ≤ f A·f Γ` (valid iff `α+β ≤ A+Γ`) needs `q+5 ≤ A+(q+1)`, i.e.
**`A ≥ 4`**.  No Hölder choice, no re-gating and no quad tower moves this.  The
landed engine realizes `A = a+2 = 5`, one above sharp.

**Grep-verified in the engine**, so this is not an inference from the statement:
`master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:475`) is
called at exactly two shift pairs `(dc,dd) = (3,2)` and `(2,3)` (`:1022`,
`:1026`); its gates `ht1 : t + finrank/2 + 1 + dc ≤ a+2` and
`ht2 : finrank/2 + 1 + dd ≤ t+4` read, in dimension three, `t+dc ≤ a` and
`dd ≤ t+2`, forcing `a ≥ 3` on BOTH calls.  So
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`'s gate
`max 2 (finrank/2*2+1) ≤ a` is the binding constraint, not slack.  The a₁ arm is
one order better but still `H⁴`: the low band of
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le` (`:4670`)
splits at `finrank/2 + m`, leaving `q ≤ 1` needing `∇^{i+j}C`,
`j ≤ finrank/2 + 1`, inside the ball ⟹ `a ≥ 2`.

**Correction to my own No. 146-executor feasibility note** (the under-count ran
one level deeper than No. 147 ruled): `coeffCap`'s window `range 3` is the
COEFFICIENT index `j ≤ 2`; each such `j` drags the tower's STATE window
`∑_{l<j+2}`, i.e. `l ≤ 3`.  So the arm I called "H²" was already `H³`, and
`coeffCap` was only one of two ball uses in `a1_ladder`.  Planner's call whether
this touches the counter; I left it at **2/3** (again a read-only-recon finding,
no wrong route implemented — but this one was MY note, so I flag it explicitly).

### What DID land — the ball BINDER is gone (5 decls, sorry-free, census-clean)

* `c2JetTowerQ`, `c1JetTowerQ` — the vestigial-binder diagnosis of No. 146 is
  **CONFIRMED and realized in the statement**: `a`, `R₀`, `hR₀` and the ball
  premise deleted (`c2` runs through `topKer_jet`, `c1` through `low1Ker_jet`;
  `hball` was an unused `intro` in both).  `c2_jet_tower`/`c1_jet_tower` are now
  four-line wrappers — statements byte-identical, zero duplicated proof.  All
  three coefficient towers are now ball-free in statement.
* `a2LadderQ`, `a1LadderQ`, `nDiffHmQ` — the ladder layer with the ball binder
  hoisted BELOW the constants:

  ```
  ∃ κ, 0 ≤ κ ∧ ∀ {δ} hδ0 hδ_le, ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
    ∀ T hT hδg hδZ {R} (hR : ‖T‖_{H⁵} ≤ R) m,
      ‖…‖_{H^m} ≤ κ·δ/(1-δ)²·‖T‖_{H^{m+2}} + Clower R m·‖T‖_{H^{m+1}}
  ```

  No `a`, no `R₀` before the state, **no admissibility hypothesis on `T` at
  all** — the estimate holds for EVERY state and the consumer picks the radius
  after seeing it (`R := ‖T‖_{H⁵}` is always legal).  `κ` before `δ` (A2-ABS),
  `Clower` before the state (TK3).  `a1LadderQ`'s sharp radius is `H⁴`;
  `nDiffHmQ` merges via order-monotonicity.  `a2_ladder` is now a COROLLARY of
  `a2LadderQ`, so the ball form costs nothing extra.

  The mechanism is one idiom: `choose … using fun R : ℝ => <engine> (R₀ := |R|)
  (abs_nonneg R)`, then `le_abs_self` at the call site.

### Why this does not unblock J4, and the ruling I need

`nDiffHmQ` at `m = 2` has lower coefficient `Clower ‖U_N(t)‖_{H⁵} 2`.  The
projected trajectory's a-priori data are `‖U_N(t)‖_{H²} ≤ R` and
`‖U_N‖_{L²_tH³} ≤ B₃` (§6.1(i),(ii)).  `H⁵` is what rung 5 is supposed to
PRODUCE, so using it at rung 3 is circular.  Two readings:

1. **PSTOP §6.1 already agrees**: rungs 3–5 close "tower-direct", and the `H⁵`
   radius `R₅ := (2Φ₅)^{1/2}+1` is handed to the ladder-based HIGH rungs
   `k ≥ 6`.  On this reading M3's premise (ladders at rungs 3–5) was the
   under-count, the ladders were always correctly scoped, and what landed here
   is a real convenience for `k ≥ 6` (no radius needed before the state).
2. If a ladder IS to serve rungs 3–5, its lower slot must widen from
   `‖T‖_{H^{m+1}}` to something that can pay the `L^∞` cost — e.g.
   `Clower m·(1 + ‖T‖_{H^{m+3}})·‖T‖_{H^{m+1}}` — a different rung design that
   changes §3's absorption arithmetic.  **Planner decision.**

**A THIRD item the planner should re-price.**  §6.3's BUDGET CHECK ("the towers'
`range (i+2)` window at `i = k−1` reaches state jets `j ≤ k`, strictly BELOW
`E_{k+1}`") omits the SAME `L^∞` embedding cost: converting a coefficient jet to
a sup-norm costs `+2` orders in dimension three.  So the tower-direct route at
rungs 3–5 needs the same re-count before it is treated as settled.  I did not
touch it — it is §6.3's, not M3's.

### Next cheap improvement (identified, not done)

`master_appCc_jet_le_sharp`'s `Cm q = √(appCcGdiag q·(S1 q + S2 q))` carries
`(1+R₀)²` in both `S1` (`:502`) and `S2` (`:512`) — the lower constant is
**affine in `(1+R₀)`**.  Exposing that factorization upgrades `a2LadderQ` from an
opaque `Clower R m` to the genuine tame form `Ĉ(m)·(1+‖T‖_{H⁵})·‖T‖_{H^{m+1}}`.
Cost: threading it through `exists_appCc_covGradCoeff_secondCovGrad_l2_le` and
the commutator chain in `ConnLapCommutatorCoefficientTame.lean` — a low shared
file, full-cone rebuild.  It does NOT change the `H⁵` obstruction.

### Verification

Focused checks green: `LowRegC01JetTower.lean`, `LowRegLadderRung.lean`.
Targeted builds green in dependency order: `+…LowRegC01JetTower` (9617 jobs),
`+…ScratchC01Census` (9626), `+…ShortTime.LowRegAllOrderJet` (9989, the
downstream consumer — its only `sorry` is still the pre-existing
`lowreg_loMass`).  **AXIOM CENSUS: zero `sorryAx` anywhere in the census
output.**  The five new declarations (`c1JetTowerQ`, `c2JetTowerQ`, `a2LadderQ`,
`a1LadderQ`, `nDiffHmQ`) and the five originals (`a1_ladder`, `a2_ladder`,
`n_diff_hm_rung`, `c1_jet_tower`, `c2_jet_tower`) all depend on
`[propext, Classical.choice, Quot.sound]` only — the originals' census is
**unchanged**, as the dispatch required.  No new `maxHeartbeats`; no read-only
lane file touched; names ≤ 20 letters; files well under 3000 lines.

Lean lesson worth banking: `tensorHs.ext` lives in
`DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation` and does NOT
resolve from the DeTurck files' open set; `smoothCcToTensorHs_norm_mono` already
exists but is `private` in `DeTurckPrincipalArmEnergyCrossTerm.lean` — the local
`hsMono` is its THIRD private copy.  Make the original public the next time that
file is edited for another reason.

### Honest denominators

`nDiffHmQ`/`a2LadderQ`/`a1LadderQ` as STATED: **100%** (sorry-free,
census-clean).  M3 as DISPATCHED: **~50%** — the binder half delivered, the
`H²`-lower-constant half proved impossible.
`lowreg_loMass`: theorem **0%** (`LowRegAllOrderJet.lean:1052`, still `sorry`);
its dedicated machinery ≈ 55% → ≈ **57%** (M3's binder half is small; the
obstruction finding is worth more than the code).  J4-rung-3: **0% stated**, and
now BLOCKED on a planner ruling rather than on missing lemmas — its M1 is 100%,
M2 re-scoped to two adapters (No. 148), M3 half-delivered/half-impossible.
`(N) ricci_flow_unif_existence`: theorem **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; untouched.
Whole HCG compactness project: ≈ **3%**.
Post-tame remainder: **11–18, central 14**, unchanged in count but J4's low end
is now clearly unreachable — the rung design has to be settled first.
Route-error counter: **2/3** (planner to rule on my own No. 146 feasibility
under-count).

## Planner update No. 149 (2026-08-04) - M3 ACCEPTED (HALF-DELIVERED, HALF-IMPOSSIBLE); RULING (a): TOWER-DIRECT PER §6.1 STANDS; §6.3 RE-PRICING + M2 DISPATCHED IN PARALLEL

Acceptance: the delivered half is genuinely valuable — all three
coefficient towers are now BALL-FREE (`c2JetTowerQ`/`c1JetTowerQ`
with the originals as four-line wrappers, vestigial binders
exorcised), and `a2LadderQ`/`a1LadderQ`/`nDiffHmQ` hoist the radius
BELOW the constants (κ before δ per A2-ABS, `Clower : ℝ → ℕ → ℝ`
before the state per TK3; `a2_ladder` is now a corollary).  The
impossible half is a THEOREM, not a failure: the H²-only lower
constant cannot exist — the `l ≥ 1` Leibniz terms force an L∞ factor
costing `finrank/2 + 2 = 3` orders in dim 3, and both Hölder splits
land on total order `q+5` ⟹ A ≥ 4, route-independently
(grep-verified at the engine's exact call sites).  The executor's
refusal to state anything over fresh hypotheses is RATIFIED, and its
self-correction of the №146 feasibility note is noted with credit.

**RULING (a): PSTOP §6.1 STANDS** — rungs 3–5 are TOWER-DIRECT (the
quad towers' explicit `(K₀ + K₂‖T‖²_{H³})` form is the rung input,
with the §6.1-v4 L¹ₜ-Grönwall absorbing the quadratic coefficient);
the ladders — including today's hoisted quad forms — serve k ≥ 6,
where `R₅` is legitimately available.  The M3 dispatch premise
(ladders for the rungs) was the planner's misdirection, built on the
№146 note.  CAVEAT ADOPTED before J4 redispatches: §6.3's budget
check omits the same L∞ +2 cost — the tower-direct budget at k = 3
must be RE-PRICED on paper first (does the jet-explicit form + the
L¹ₜ trick genuinely avoid the +3-order cost, or does the same
counting bite?).  Dispatched as a read-only §6.4 recon IN PARALLEL
with [M2a+M2b] (disjoint files; M2 consumes nothing from M3).

COUNTER PACKAGE (presented to the user at №148-149, formally held at
**2/3**): candidate +1 (the M3 half-impossible dispatch, №146-note
rooted) and candidate −1 (route error No. 2's superseded deletion
ruling, №148) — the planner's recommendation is they NET OUT.  The
user rules under the reset semantics.

Honest denominators: `lowreg_loMass` 0% (machinery ≈ 57%); J4-rung-3
0%, blocked on the §6.4 verdict; (N) 0% (stated, sorry :98); whole
HCG ≈ 3%; post-tame 11–18 central 14 with J4's low end unreachable.
Route-error counter: **2/3** (package pending user).

## Executor report No. 149-executor-M2 (2026-08-04) - M2a + M2b BOTH DELIVERED, census-clean; M2 is CLOSED, no route change, no import churn

Both adapters are in
`Analysis/Spectral/Intrinsic/HeatSemigroup/GalerkinTameSol.lean`, exactly
where §3 of `M2_FORCING_PLAN.md` put them, and both are axiom-clean.
Nothing outside that one file was touched.

* **M2a `galTameForce_contOn` (:674)** — for `i ∈ S` the forcing coordinate
  is the `i`-th coordinate of the *field* with the spectral diagonal added
  back, `F(c t) i = (galTameField … w t) ⟨i,hi⟩ + λᵢ·c t i`; the field is
  continuous because `galTameField_lip` makes it globally Lipschitz, and the
  coordinate curve `w t` is continuous by `continuousOn_pi` through
  `(EuclideanSpace.equiv {i // i ∈ S} ℝ).symm`.  Off `S` the forcing is
  constant.  **Route B as written in the plan** — Route A (the
  `GalerkinLimitUniformMass.lean:33` mirror) was never needed, and no new CLM
  projection wrapper was required, so the plan's stop signal never fired.
* **M2b `galTamePerMode` (:886)** — the mechanical port of the private
  `galerkinPerMode_eq_perModeConvSymm` with `ha_super` deleted; compiled on
  the first attempt.  `perModeConv` needed only a scoped
  `open …Parabolic.MaximalRegularity in` (the module is in cone via
  `GalerkinParabolicEnergyDeTurck → Plancherel → PerMode`): **zero import
  churn, zero low-file rebuild**, as the plan's import check predicted.
* **One lemma the plan did not list: `galTameStateC_emb` (:262).**
  `galTameState_eq` runs coordinates → coefficient family and lands on
  `fun i => if h : i ∈ S then w ⟨i,h⟩ else 0`, never on the caller's `c`.
  The bridge is the converse reading; its content is that `galTameStateC`
  sees `c` only through `finiteEigenComboHs … S c`, i.e. only on `S`.  Six
  lines of restricted congruence, and it is the only thing standing between
  `galTameField_apply` and `galTameForce_apply`.

Verification: focused check green, targeted build
`+…HeatSemigroup.GalerkinTameSol` green (9573 jobs), `#print axioms` on all
three new declarations **and** on `galTameSolOne` = `[propext,
Classical.choice, Quot.sound]`, zero `sorryAx`.  Existing censuses untouched.

**Signature ruling the planner should note, and what J4-rung-3 must carry.**
Both adapters take `hK : LipschitzOnWith K Nfun (galTameBall …)` — the
weakest-hypothesis form, matching `galTameField_lip`/`galTameField_aff` in
the same file — **not** `galTameSolOne`'s `A B C Rt + htame`.  The plan's
prose ("the hypothesis bundle is exactly `galTameSolOne`'s") and its literal
Lean statement disagreed; I took the literal statement.  This costs a call
site holding the tame estimate exactly the five-line `obtain` that
`galTameSolOne` already runs internally (`tame_lip_balls … Nfun 0 id
isometry_id rfl (galLowView g₀ a) A B C Rt hA hB hC hRt htame
(Real.sqrt κ * R)`), and it buys reusability for any call site that has a
Lipschitz constant but no tame data.  If the planner prefers the tame-flavour
bundle at the J4 call site, that is a four-line wrapper, not a re-proof.

Satisfiability at `a = 1` is **already witnessed** — no honest-input gap:
`ShortTime/LowRegGalerkinSol.lean:155–166` hands `galTameSolOne` the very
`hκ0`/`hκ`/`htame` these adapters need, at `S = eigenIdxFinset g₀ N`, and
`lowregGalSol`'s four output conjuncts are literally `galTamePerMode`'s
`hcont`, `hderiv` and `hzero` (its `∀ i, U N 0 i = 0` is stronger than the
`∀ i ∈ S` I ask for).  I did **not** write the `a = 1` instantiation into
`LowRegGalerkinSol.lean`: it is outside the M2 dispatch, and its natural
statement depends on the §6.4 verdict about what rung 3 consumes.

**Seam the redispatch must price (not an M2 defect).**  `galTamePerMode`
gives the Galerkin coordinates as `perModeConv` of the **Galerkin** forcing
`Set.IccExtend … (galTameForce … (U N ·))`, while `lowreg_projMode_tendsto`
(`ShortTime/LowRegGalerkinIdent.lean:165`) gives convergence of `perModeConv`
of the **projected-solve** forcing `timeModeCoeff (fseq N) i`.  Fatou needs
both sides indexed by the same sequence; §2.3 of `M2_FORCING_PLAN.md` lists
them as two independent FREEs without an identification between them.  Either
the closure rides the Galerkin sequence alone (then `lowreg_projMode_tendsto`
is not the Fatou input the plan says it is), or a forcing-identification brick
is missing.  That question belongs with the §6.4 re-pricing.

Honest denominators (mine, not inherited): **M2 100% — CLOSED.**
`lowreg_loMass` theorem **0%**; of the three order-one producers its docstring
lists, #1 (`lowregGalSol`) is done, #2 (the perMode identification) went from
~30% to ~**75%** — its two adapters exist and are proved; what is left is the
`a = 1` instantiation plus the Galerkin/projected forcing seam above — and #3
(the per-scale closure) is still **0%** and still the real frontier; so the
dedicated machinery ≈ 57% → ≈ **60%**.  J4-rung-3: **0% stated**, still
blocked on the §6.4 verdict, but its M2 prerequisite is no longer a
prerequisite.  `(N) ricci_flow_unif_existence`: theorem **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; untouched by this
work.  Whole HCG compactness project: ≈ **3%**.  Post-tame remainder
**11–18, central 14** — unchanged; M2 was priced at ~1 session and cost well
under one, but it was never the critical path's long pole.
Route-error counter: **2/3**, untouched (no route error here; the
signature-vs-prose mismatch above is a plan ambiguity I resolved in favour of
the weaker hypothesis, and I am flagging it rather than banking it).

## Planner update No. 150 (2026-08-04) - M2 ACCEPTED CLOSED; THE FORCING-IDENTIFICATION SEAM FED INTO THE §6.4 RECON

Acceptance: `galTameForce_contOn` (:674, route B verbatim),
`galTamePerMode` (:886, first-try port with `ha_super` deleted, zero
import churn), plus the unlisted bridge `galTameStateC_emb` (:262) —
all census-clean; nothing outside `GalerkinTameSol.lean` touched.
The weaker-hypothesis resolution of the plan's signature-vs-prose
ambiguity is RATIFIED (weakest-assumptions rule; the tame call site
pays a five-line `obtain` it already runs elsewhere).  The `a = 1`
instantiation is correctly left to the J4 redispatch (its shape
depends on the §6.4 verdict).

THE SEAM (the session's most valuable find): `galTamePerMode` speaks
of the GALERKIN forcing's `perModeConv`; `lowreg_projMode_tendsto`
speaks of the PROJECTED-SOLVE forcing's.  Fatou needs one sequence.
Either the mass argument rides the Galerkin sequence alone (changing
the identification layer's role) or a forcing-identification brick
is missing (candidate composition: `galTameForce_eq` + the
fixed-point a.e. identity + `projForce_fixed`).  FED into the
running §6.4 recon by planner message — its verdict must price it.

Honest denominators: M2 100%; `lowreg_loMass` 0% (machinery ≈ 60%;
producer #2 ≈ 75%, #3 = the per-scale closure = the real frontier at
0%); J4-rung-3 0% (blocked on §6.4 only); (N) 0% (stated, sorry
:98); whole HCG ≈ 3%; post-tame 11–18 central 14.  Route-error
counter: **2/3** (user package still pending).

## Recon report No. 150-recon-§6.4 (2026-08-04) - TOWER-DIRECT RE-PRICED: **HOLDS-WITH-ADAPTERS** at rungs 3–5; §6.3's budget check WAS WRONG; EXHIBIT THIRTEEN (a₂-tower window slack); the Fatou seam RULED (ride the projected sequence, no identification brick needed)

Read-only paper recon; no Lean run, no `.lean` touched.  Written into
`PSTOP_PROPOSITION.md`: §6.4 (new, with the displayed `k = 3` derivation),
§6.3 (corrected in place, the wrong text quoted so the correction is
readable), §9, §10 (adapters G, H), header v4→v5.

**VERDICT: HOLDS-WITH-ADAPTERS.**  M3's caveat was right — §6.3's BUDGET
CHECK omits the same `L^∞` cost and is wrong as written — but the conclusion
it feared does not follow: the tower-direct route pays that cost with the
CLASS `H²` radius `R`, not with an `H⁵` ball.  Ruling No. 149(a) (rungs 3–5
tower-direct, ladders for `k ≥ 6`) SURVIVES, and M3's `A ≥ 4` does not
transfer — for a structural reason, not by luck.

**What §6.3 got wrong.**  It priced ONE Leibniz term.
`‖𝒩(U)−𝒩(0)‖_{H^{k−1}}` is a sum over `l ≤ q ≤ k−1` of
`‖ |∇^lC₂|·|∇^{q−l+2}U| ‖_{L²}`; only `l = 0` is charged to the pointwise
fibre cap.  Every `l ≥ 1` needs one factor in `L^∞`, and the tree's sup
embedding (`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`,
`…/Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`, window
`range (finrank/2 + 2)`) charges `+2` `L²`-orders — M3's `+2`, the same
number.  So "state jets `j ≤ k`, strictly BELOW `E_{k+1}`, triangular with
room to spare" is false for `l ≥ 1`: the worst term `l = k−1` needs the a₂
tower at index `k+1`, whose state window is `j ≤ k+2` as landed — ABOVE
`E_{k+1}`, i.e. circular.

**EXHIBIT THIRTEEN — why it is repairable.**  The `+1` in the a₂ tower's
window is PURE SLACK.  `topKer_jet` (`…/DeTurck/LowRegC2JetTower.lean:196`)
reaches, at `:260`, `hfin.2.2 i : lowJetSq g i (topKernel …) ≤ A i·(1 +
lowJetSq g i T)` — the SHARP window `j ≤ i` — and then spends its last two
`calc` steps (`hsub`/`hmono`, `:263–:280`) weakening `lowJetSq g i T` to
`∑_{j ∈ range (i+2)}`, purely for shape-uniformity with the C0/C1 towers.
Deleting that weakening moves the rung-`k` requirement from `j ≤ k+2`
(circular) to `j ≤ k+1` (absorbable).  **The "the a₂ tower only reaches
`H^{k+2}`" wall exists in the statement, not in the proof.**  Backwards
compatible: every consumer takes the tower as a HYPOTHESIS in the weak shape
(e.g. `…/DeTurckRemainderPrincipalArmOpNorm.lean:4670`, `:4682`), and the
sharp tower implies it by `Finset.sum_le_sum_of_subset_of_nonneg`.

**The `k = 3` derivation** (in full in §6.4; `X = ‖U‖_{H⁴}`, `Y = ‖U‖_{H³}`,
`R` = the class `H²` radius).  Every `l ≥ 1` term takes the Hölder split
`L^∞` on the COEFFICIENT / `L²` on the state — the choice §6.3 never made:

* `l = 0` → `Cδ*·X`; pairing `Cδ*·E_4`; δ*-margin.  Unchanged.
* `l = 1` → `‖∇C₂‖_∞‖∇³U‖_{L²} ≤ K₁(1+Y)Y`; pairing + Young →
  `2εE_4 + C·E_3 + C·E_3(t)·E_3`, the last an `L¹_t` Grönwall coefficient
  (`∫E_3 ≤ B₃²`, §6.1(ii)).  ✓
* `l = 2` (the missed term) → `‖∇²C₂‖_∞‖∇²U‖_{L²} ≤ K_R·R·(1+‖U‖_{H⁴})` —
  tower at index 4, sharp window landing exactly ON `H^{k+1}`; pairing →
  `K_R R X + K_R R·E_4`, `E_4 = E_3 + D_3`.  Absorbable iff
  **`Cδ* + K_R·R + 2ε < 1`**.

Rungs 4 and 5 are uniform (same worst term `l = k−1`, same condition, `K_R`
from `max_{i≤7}√(Kc i)`); at rung 5 the already-chosen `R₃, R₄` make every
`l ≤ 3` term outright class.  §5's upward ordering survives: rung `k` sees
only `R_j`, `j < k`.  The a₁/a₀ arms need nothing new — their `L^∞` factors
are `‖∇U‖_∞ ≲ ‖U‖_{H³}` and `‖U‖_∞ ≲ ‖U‖_{H²} ≤ R`, so the landed
`range (i+2)` windows of `c1JetTowerQ` / `c0_jet_tower_quad` suffice.

**Why the tower-direct route escapes `A ≥ 4`.**  The ladder must collapse the
whole `l ≥ 1` sum onto one lower slot `Clower·‖T‖_{H^{m+1}}` whose constant
may depend only on a ball radius; log-convexity then forces `A ≥ 4`.  The
tower-direct pairing is not obliged to collapse: it may leave the cost on the
TOP slot as `(K_R·R)·‖U‖_{H^{k+1}}`, where the δ*-margin — not a ball — pays
for it.  The price is that the bottom block's smallness becomes
`min(δ*, R)`-shaped instead of `δ*`-only.

**The two adapters** (now PSTOP §10 G and H):

* **G / (B-WIN)** — sharpen `topKer_jet` + `c2JetTowerQ`
  (`LowRegLadderRung.lean:148`) to `range (i+1)`.  FREE, load-bearing.
* **H / (A-R)** — strengthen §3's absorption to `Cδ* + K_R·R + 2ε < 1`.
  Ordering is legal: `Kc` is `∃`-bound before the state, so `K_R` is fixed
  before `R`; front 3 picks `R ≤ (1−Cδ*−2ε)/(2K_R)` next to the existing
  `hsmall : C₁R ≤ 1/8`, and shrinking `R` moves `τ₀` only through
  `partial_sol_const`'s closed formula (class inputs only), so `τ₀` stays
  class-uniform.  Same species as A2-ABS; discharge them together.

**No new analytic lemma is needed** — no fractional Sobolev scale, no Agmon,
no interpolation beyond plain Young.  (The Agmon alternative
`‖∇²U‖²_∞ ≲ ‖U‖_{H³}‖U‖_{H⁴}` would also close it but needs a
fractional/Weyl-summability embedding the tree lacks, so (A-R) is strictly
cheaper.)  Check-first on the product layer: `…/Sobolev/MoserTameProduct.lean`
DOES hold a genuine Moser tame product (`:111`) and a GN interpolation
(`:1115`); neither fits — `:111` demands a uniform `C^k`-sup on the
coefficient (too crude for rung 3: it forces one `l`-independent split),
`:1115` interpolates `‖∇^ju‖_{L²}` between `‖u‖_∞` and `‖∇^ku‖_{L²}` (wrong
shape).  Correctly NOT counted as the producer, and correctly not called a
missing wall either.

**THE REAL LEAN COST.**  A BALL-FREE per-index `appCc` `H^{k−1}` assembly
making the per-`l` Hölder choice explicit.  Both existing engines absorb the
cost into a ball constant: `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`
(`…/TensorHilbert/ConnLapCommutatorCoefficientTame.lean:1334`) and the `m ≤ 1`
band split `…/DeTurckRemainderPrincipalArmOpNorm.lean:4670`, whose conclusion
`Cm q·√(∑_{i≤q+1}…)` is exactly the ladder's collapsed lower slot.  New
assembly theorem, not wiring; the bottom block's largest remaining piece.

### The Fatou seam (No. 150) — RULED: ride the PROJECTED sequence; NO identification brick

The coordinator's option (i), with a correction: the closure rides the
PROJECTED sequence (not the Galerkin one), and `lowreg_projMode_tendsto` IS
the Fatou input.  Three grep-verified reasons:

1. convergence to `fLo` is a truncation-defect estimate on the PROJECTED
   forcings (`projFixTame_le_two` + `projFix_tendsto`, assembled at
   `LowRegGalerkinIdent.lean:~130–:160`).  Nothing analogous exists for
   `galTameForce`, so riding the Galerkin sequence alone means re-proving
   that convergence — which strictly CONTAINS the identification;
2. the projected side already has the per-mode representation without
   `galTamePerMode`: `maximalRegularitySolField_timeModeCoeff`
   (`…/MaximalRegularity/Operator.lean:491`) + `solModeCoeff` (`:88`); and
   `projField_fixed` (`…/HeatSemigroup/EigenProjPartialSol.lean:561`) already
   supplies the `V_N`-valuedness PSTOP §6.2(e) listed as adapter A — **adapter
   A is LANDED** (a small over-count of its own).  The rest of (e),
   differentiability of `t ↦ E_k`, is on `V_N` a finite sum of
   `perModeConv_hasDerivAt` (`…/MaximalRegularity/PerMode.lean:586`);
3. the rungs' a-priori inputs (state ball, `L²_tH³`, Nemytskii identity, PDE)
   are OUTPUTS of `proj_partial_sol_tame` (`EigenProjTameSol.lean:118`) and
   live only on the projected trajectory.  The Galerkin ODE trajectory has NO
   ball bound — `galTameRetr` exists precisely so none is needed — so even
   `galTameForce_eq` (`GalerkinTameSol.lean:627`, hypothesis
   `hc : ‖galLowView …‖ ≤ R`) cannot be applied along it without a new
   estimate.  So route (ii) costs TWO bricks, not one: (S1) an a-priori ball
   bound along the Galerkin trajectory (retraction inert), then (S2) the
   finite-dimensional uniqueness Grönwall — and it still needs everything
   route (i) needs.  Route (i) strictly dominates.

Stated plainly: **the forcing-identification brick is not missing — it is not
needed.**  `lowregGalSol` / `galTameSolOne` / `galTamePerMode` /
`galTameForce_contOn` are sound API that is OFF the critical path; M2's work
is not wasted, but it should stop being counted as a `lowreg_loMass`
prerequisite (producer #2's ≈ 75% is measuring a producer the closure will
not call).  What IS needed is a statement widening: `lowreg_proj_tendsto` /
`lowreg_projMode_tendsto` currently `obtain` the projected trajectory and
DISCARD it (`⟨_u, gforce, _hu, _hstate, hgE, _htr, _hpde, hgball⟩`,
`LowRegGalerkinIdent.lean:~143`), keeping only the forcing.  Expose `u`,
`hstate`, `hgE`, `hpde` next to `fseq` — the conjuncts are already produced.

### J4-rung-3 REDISPATCH handoff

Ordered; each step independently checkable.  Do NOT start with the rung.

1. **G (B-WIN), first and alone.**  Restate `topKer_jet`
   (`LowRegC2JetTower.lean:196`) and `c2JetTowerQ` (`LowRegLadderRung.lean:148`)
   with `range (i+1)`; delete `hsub`/`hmono` and the last two `calc` steps
   (`:263–:280`).  Keep `c2_jet_tower` as the `range (i+2)` wrapper (one
   `Finset.sum_le_sum_of_subset_of_nonneg`) so no consumer moves.  STOP
   SIGNAL: if a downstream file needs more than that one weakening line, the
   window is load-bearing somewhere unexpected — report instead of pushing.
2. **The forcing-sequence widening** (seam item above): expose the projected
   trajectory alongside `fseq` in `lowreg_proj_tendsto` /
   `lowreg_projMode_tendsto`.  Purely additive.
3. **The ball-free per-index `appCc` `H^{k−1}` assembly** — the real brick.
   Target shape at `q ≤ k−1`, no ball, constants before the state:
   `‖∇^q(appCc C₂ (∇²T))‖_{L²} ≤ Cδ·‖T‖_{H^{q+2}} + ∑_{1≤l≤q} K(l)·‖T‖_{H^{l+2}}·‖T‖_{H^{q−l+2}}`,
   `K(l)` from the sharpened tower at index `l+2` and the sup embedding.
   Model it on `…/DeTurckRemainderPrincipalArmOpNorm.lean:4670`'s band split
   but STOP before the collapse into `Cm q·√(∑_{i≤q+1}…)` — the collapse is
   exactly what needs the ball.
4. **Then** rung 3, with H (A-R) threaded as an explicit hypothesis
   `hR : K_R·R ≤ 1 − Cδ* − 2ε` rather than silently discharged.

### Honest denominators

P-STOP (paper): ≈ 90% → ≈ **93%** — v4's open item (ii) ("the rung-3..5
pairing has been checked at window level, not written out as a displayed
derivation") is DISCHARGED; two new adapters are open in its place.  §6.4
itself: **100% as paper, 0% as Lean** — it moves no Lean and does not pretend
to.  `lowreg_loMass`: theorem **0%** (`LowRegAllOrderJet.lean:1052`); dedicated
machinery ≈ 60% → ≈ **62%** — the re-pricing removes a blocker and retires a
prerequisite, but adds the per-index assembly brick, which is bigger than what
it removes; I am not banking more.  J4-rung-3: **0% stated**, no longer
blocked on a ruling, now blocked on the three ordered inputs above.
`(N) ricci_flow_unif_existence`: theorem **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; untouched by this
work and unmoved by the verdict.  Whole HCG compactness project: ≈ **3%**.
Post-tame remainder: **11–18, central 14** — J4's low end is reachable again
(the rung design is settled), but step 3 is new visible work.
Route-error counter: **2/3**, untouched by this report.

## Planner update No. 151 (2026-08-04) - §6.4 VERDICT ADOPTED (TOWER-DIRECT HOLDS-WITH-ADAPTERS; SEAM RESOLVED: RIDE THE PROJECTED SEQUENCE); [J4-PREP: G + WIDENING + ASSEMBLY] DISPATCHED

Adopted in full:
- **§6.4 HOLDS-WITH-ADAPTERS**: ruling 149(a) survives — the
  tower-direct route pays the L∞ cost with the CLASS H² radius on
  the TOP slot (`K_R·R·‖U‖_{H^{k+1}}`), absorbed by the δ*-margin;
  absorption strengthens to `Cδ* + K_R·R + 2ε < 1` (adapter H,
  A2-ABS species, `K_R` before `R`).  §6.3's budget check was wrong
  (only l = 0 priced) and is corrected in place; the FULL k = 3
  derivation is now displayed in PSTOP §6.4 — the deferred-since-v2
  item, discharged.  M3's `A ≥ 4` does NOT transfer (it was forced
  by the ladder interface's collapse-onto-one-slot, which the
  tower-direct pairing avoids).
- **EXHIBIT THIRTEEN**: the a₂ tower's `+1` window is pure slack —
  `topKer_jet` reaches the sharp form at :260 and spends :263-:280
  weakening it; deleting the weakening (adapter G, statement-level,
  backwards-compatible) moves rung k from circular to absorbable.
- **THE FATOU SEAM RESOLVED — ride the PROJECTED sequence** (option
  (i) corrected): `lowreg_projMode_tendsto` IS the Fatou input;
  PSTOP adapter A is ALREADY LANDED (`projField_fixed`); the
  Galerkin trajectory has no ball bound so `galTameForce_eq` cannot
  even apply along it — route (ii) strictly contains (i).
  CONSEQUENCE, honestly recorded: M2's four declarations are sound
  API but OFF the critical path (producer #2's ≈75% measured a
  producer the closure will not call); the needed piece is instead
  the IDENTIFICATION-LAYER WIDENING (expose `u/hstate/hgE/hpde`
  next to `fseq`).
- `MoserTameProduct :111` checked and correctly rejected (uniform
  `C^k` sup — too crude for rung 3).  The real Lean cost = the
  ball-free per-index `appCc` `H^{k−1}` assembly (model :4670's band
  split, STOP before the collapse).

DISPATCHED: [J4-PREP] = (1) adapter G sharp-window restatements with
wrapper compatibility, (2) the identification widening, (3) the
per-index assembly theorem — the session's core; then (4) rung 3
with H threaded, as the following brick.

Honest denominators: P-STOP ≈ 93% (paper); `lowreg_loMass` 0%
(machinery ≈ 62%); J4-rung-3 0% (three ordered inputs, no ruling
pending); (N) 0% (stated, sorry :98); whole HCG ≈ 3%; post-tame
11–18 central 14.  Route-error counter: **2/3** (user package
pending).

## Planner update No. 152 (2026-08-05) - USER RULING: ROUTE-ERROR COUNTER RESET TO 0/3

The user ruled on the No. 148-149 counter package: **reset to 0/3**
("计数清0好了").  Per the No. 114 semantics (the counter is an
unattended drift guard; the user re-adjudicates and may reset when
present), counting restarts from zero now.  The underlying findings
remain fully recorded regardless (the S0-era falseness chain, §7.4,
the loMass unprovability, the M3 half-impossible dispatch, the
superseded brick-(1) deletion) — the reset clears the STOP-counter,
not the history.  Route-error counter: **0/3**.

## Executor report No. 150-executor-J4PREP (2026-08-05) - ALL THREE ORDERED PARTS DELIVERED: adapter G LANDED (free, zero consumer churn), the trajectory widening LANDED, and the **ball-free per-index `appCc` assembly EXISTS** (3 public theorems, sorry-free, census-clean)

The §6.4 redispatch ran to completion in order.  Nothing was blocked; no
STOP-signal fired; no route change.  The largest single piece of Lean work the
bottom block was missing (§9(iii), "the ball-free per-index `appCc` `H^{k−1}`
assembly ... does not exist as a producer") now exists.

### Part 1 — adapter G / (B-WIN): FREE, exactly as predicted

`topKerJetSharp` (`DeTurck/LowRegC2JetTower.lean`) and `c2JetTowerSharp`
(`DeTurck/LowRegLadderRung.lean`) are the sharp-window forms

```
lowJetSq g i (topKernel …) ≤ Kk i * (1 + ∑_{j ∈ range (i+1)} ‖∇^j T‖²)
‖∇^i A.C2‖²             ≤ Kc i * (1 + ∑_{j ∈ range (i+1)} ‖∇^j T‖²)
```

and the old names `topKer_jet` / `c2JetTowerQ` survive with **byte-identical**
statements as weakened wrappers.  The recon was right that the `+1` was pure
slack: deleting `hsub`/`hmono` and the last two `calc` steps left the sharp
window already proved.  **Zero consumer churn** — `topKer_jet`'s only Lean
consumer was `c2JetTowerQ`, and `c2JetTowerQ`'s consumers (`c2_jet_tower`,
`a2LadderQ`, `ScratchC01Census`) take the tower in the weak shape and are
untouched; their census is unchanged.  The dispatch's stop condition ("a
downstream file needs more than that one weakening line") did not fire.

`a2LadderQ` deliberately keeps consuming the **weak** tower: its `H⁵` ball is
structural (M3's `A ≥ 4`), so the sharp window buys it nothing.  The sharp form
is useful only tower-directly, which is the point.

### Part 2 — the forcing-sequence widening: purely additive

`lowreg_proj_tendsto` / `lowreg_projMode_tendsto`
(`ShortTime/LowRegGalerkinIdent.lean`) now bind `δ, Ctop, B1, ρ, P` and their
certificates **once, outside `∀ N`** (so every constant stays `N`-free) and
expose, per `N`: `Π_N`-fixedness; the a-priori state ball
`U_N(t) ∈ lowerState g₀ 1 (lowregStateRad Ctop B1 ρ P)` a.e. (§6.1(i) — note
`lowerState` is the `H²` ball inside `H³`, so this *is* `‖U_N(t)‖_{H²} ≤ R`);
the truncated Nemytskii identity `fseq N =ᵐ Π_N ∘ lowregNfun` along `U_N`; the
zero seed; the PDE `∂_t U_N = Δ U_N + fseq N`; and `‖fseq N‖ ≤ R/4`.  The
trajectory is written as `maxRegDuhamelSolField … 0 (fseq N)` (the `u` binder is
`subst`ed away), so the whole package depends on `fseq` alone.  Widened in
place: a repo-wide grep found **no Lean consumer** of either theorem, only prose
references.  Same proofs, more conclusion.

### Part 3 — the assembly.  THE COLLAPSE IS NOT NEEDED; the grid was already there

New file `DeTurck/LowRegA2PerIndex.lean` (~570 lines), three public theorems:

```lean
appCcPerIdxL2 (g₀) (b₀ s₀ q) :
  ∃ C ≥ 0, ∀ Φ W (Λ : ℕ → ℝ),
    (∀ i x, |∇^i Φ|²(x) ≤ (Λ i)²) →
    ‖∇^q (appCc Φ W)‖² ≤ C * ∑_{i ≤ q} (Λ i)² * ∑_{l ≤ q-i} ‖∇^l W‖²

a2PerIdxJet (hDim : finrank ℝ E = 3) (g) :
  ∃ Cq K : ℕ → ℝ, … ∀ T (sym) δ (0 ≤ δ ≤ 1/3) hδg hδZ Cδ
    (hfib : ∀ x, |A.C2|²(x) ≤ Cδ²) (q),
    ‖∇^q (A.a2 T)‖² ≤ Cq q * (Cδ² · J(q+2) + ∑_{1≤i≤q} K i · (1 + J(i+2)) · J(q-i+2))

a2PerIdxLin … :
    ‖∇^q (A.a2 T)‖ ≤ Cq q * (Cδ · jet_{q+2} + ∑_{1≤i≤q} K i · (1 + jet_{i+2}) · jet_{q-i+2})
```

with `J(n) = ∑_{j≤n}‖∇^j T‖²`, `jet_n = √(J n)`, all constants fixed before `T`,
`δ` and `Cδ`, and **no Sobolev ball anywhere**.  `a2PerIdxLin` is §6.4's
displayed shape at `q = k−1`.

**Why it worked without new analysis.**  The per-index Leibniz grid already
existed, public and unused by the collapsing engines:
`appCc_iteratedCovGrad_diagonalProductGrid_le`
(`Spectral/Tensor/CovGrad/OperatorFieldFibreNormJet.lean:885`) gives pointwise
`|∇^q(appCc Φ W)|² ≤ G q ∑_{i≤q}|∇^iΦ|²·∑_{l≤q-i}|∇^lW|²`.  The whole content of
`appCcPerIdxL2` is: bound `|∇^iΦ|²(x)` by its *own* constant `(Λ i)²` **inside
the integral**, index by index, then integrate the data factor.  Everything else
is instantiation — sup embedding (`SobolevEmbeddingSharpC0JetSum.lean:717`,
window `range 3` in dim 3) on `∇^i C₂`, jet composition, and the **sharp** tower
from part 1.  Index bookkeeping confirms §6.4 exactly: coefficient index `i` ⇒
`+2` sup cost ⇒ tower index `i+2` ⇒ (sharp) state jets `j ≤ i+2`; data factor
`∇^{q-i+2}T`; both `≤ q+2`; and order `q+2` occurs **only** in the `i = 0` slot,
against the small `Cδ`.  §6.4's order budget is confirmed, not exceeded — the
"order count above the displayed budget" stop condition did not fire.

> [Planner correction, №153 — adversarial panel, assembly-shape verifier.]  The
> "occurs **only** in the `i = 0` slot" clause is FALSE as stated: for `q ≥ 1`
> the `i = q` term's coefficient factor is `1 + J(q+2)`, so the top order `q+2`
> occurs in exactly TWO slots — `i = 0` (against `Cδ`) and `i = q` (against
> `K q`, i.e. the `K_R·R` cost that adapter H prices).  This matches §6.4's
> displayed derivation (which itself contains the `i = q` occurrence); only this
> summary sentence and the same sentence in `a2PerIdxJet`'s docstring were
> wrong.  Both fixed; the Lean statements needed no change.

**Exhibit — why the existing two-arm engine genuinely cannot serve** (checked, not
assumed): `appCc_topOrder_l2_twoArm_mixed_le`
(`DeTurckRemainderHigherOrderTame.lean:512`) bounds the sum by
`C(Λ_W²∑_i‖∇^iΦ‖² + Λ_Φ²∑_l‖∇^lW‖²)`, whose first summand carries
`Λ_W = ‖∇²U‖_∞ ≲ ‖U‖_{H⁴}` — order `X`, not small — so the pairing gives
`C·E_4` with `C` not small: a non-absorbable `D_3`.  That is the ladder collapse
in miniature, and it is why this was a new assembly rather than wiring.

> [Planner correction, №153 — adversarial panel, overcount-hunt verifier:
> **exhibit FOURTEEN**.]  Two claims in the two paragraphs above are false.
> (1) "grid … unused by the collapsing engines": the two-arm engine consumes the
> grid in its own proof (`DeTurckRemainderHigherOrderTame.lean:566`), and the
> grid has ~30 call sites in ~12 files.  (2) Far more important: the tree
> ALREADY had the integrated per-index assembly — `app_jet_sq_le`
> (`Analysis/Sobolev/TensorHilbert/ParametricAppCcJetBound.lean:40`), tracked
> and live API, states verbatim "per-index caps `B i` ⟹
> `‖∇^j(appCc Φ W)‖² ≤ appCcGdiag j · Σ_{i≤j} B i · Σ_{l≤j-i} ‖∇^l W‖²`".
> `appCcPerIdxL2`'s ~90-line proof re-derived it.  §9(iii)'s "missing producer"
> was an over-count of missingness (executor and planner both; the file's own
> "two engines refuse this" census missed the third producer).  REPAIRED at
> №153: `appCcPerIdxL2` is now a 5-line wrapper over `app_jet_sq_le` (statement
> byte-identical, `contRfns` deleted, header rewritten; focused check + census
> green).  The exhibit-check rule extends: census greps for "no producer exists"
> must sweep the TensorHilbert/parametric layer, not only the local
> engine-family names.

### The one finding that touches adapter H

`a2PerIdxLin`'s top slot is `Cq q · Cδ`, not `Cδ`, with
`Cq q = √(appCcGdiag q) = (2(d+1))^{q/2}`.  Ordering is legal — `Cq` depends only
on `g₀` and `q`, so it is fixed before `δ` and before `R` — but **PSTOP §10
adapter H should be restated as `Cq(k−1)·Cδ* + K_R·R + 2ε < 1`**.  For `k ≤ 5`
that is four numbers, chosen before `δ*`; it changes nothing structurally and is
not discharged here (threaded as an explicit hypothesis by the consumer, per the
dispatch).  I did not attempt the `H^q`-*norm* version: `hs_le_jet` plus a sum
over `j ≤ q` would multiply the top constant again, for no gain — the rung pairs
against `‖U‖_{H^{k+1}}` and can bridge at the point of use.

### Verification

Focused checks green on all four touched/created files; targeted builds green for
`LowRegC2JetTower`, `LowRegLadderRung`, `LowRegA2PerIndex`, and the downstream
`ScratchC01Census`.  Axiom census over eleven declarations — the three new
public theorems, the four sharp/wrapper tower forms, the two widened
identification theorems, plus the untouched `c2_jet_tower` and `a2LadderQ` —
**zero `sorryAx`**, `[propext, Classical.choice, Quot.sound]` only.  No new
`maxHeartbeats`.  Claims released.

### Honest denominators

`(N) ricci_flow_unif_existence`: theorem **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`, untouched by this
work.  `lowreg_loMass`: theorem **0%** (`LowRegAllOrderJet.lean:1052`); its
dedicated machinery ≈ 62% → ≈ **70%** — the largest named missing producer
(§9(iii)) is now landed and two adapters are discharged, which is the biggest
single machinery jump this lane has had; I am not banking more because the rung
itself is still unstated.  J4-rung-3: **0% stated**, and it is now unblocked on
all three ordered inputs — what remains is the rung's own pairing/Grönwall
assembly, which needs the trajectory package (part 2) plus `a2PerIdxLin`
(part 3) plus the `a₁`/`a₀` arms (cheaper, and per §6.4 the landed
`range (i+2)` windows of `c1JetTowerQ` / `c0_jet_tower_quad` already suffice for
them).  P-STOP (paper) unchanged at ≈ 93%, with §9(iii) now discharged and
adapter H restated as above.  Whole HCG compactness project: ≈ **3%**.
Post-tame remainder: **11–18, central 14**, unchanged — this consumed visible
work rather than adding it.  Route-error counter: **0/3** (per the user's reset
recorded immediately above; my dispatch predated it and said 2/3).

---

## №153 (planner, 2026-08-05) — J4-PREP ACCEPTED WITH CORRECTIONS: adversarial
## panel verdicts, exhibit FOURTEEN, repairs landed, rung 3 re-scoped

**Acceptance instrument.**  First ultracode acceptance: a 5-agent read-only
adversarial workflow (run `wf_a43cbfb6-88b`; every verifier prompted to REFUTE,
schema-forced verdicts, no lake/lean, untracked files in scope per №148).

**Verdicts.**
- `wrapper-compat` **CONFIRMED** — byte-identity git-forced for `topKer_jet` and
  `c2_jet_tower` (statement blocks diffed against HEAD `7f54201cf`);
  `c2JetTowerQ` corroborated only (born uncommitted in M3 — no git baseline).
  Caveat noted: the whole J4-PREP delta sits on the uncommitted working tree.
- `ident-widening` **CONFIRMED** — constants/certificates bound before `∀N`
  (`LowRegGalerkinIdent.lean:84–90`), all six per-N conjuncts present, only
  N-dependent quantity inside is `lowregStateRad` args (N-free); zero external
  Lean consumers (sweep included untracked/ignored trees), so the telescope
  change was safe.
- `assembly-shape` **REFUTED as stated** — ONE false conjunct (top order `q+2`
  in two slots, not only `i = 0`); all load-bearing conjuncts survive: no
  ball binder, constants-first, `≤ q+2` leak-hunt clean, term-for-term match
  with §6.4's displayed k=3 derivation, adapter-H premise recorded in PSTOP.
  Severity: doc/report bookkeeping, zero Lean impact.  Corrections inline above.
- `census-audit` **UNVERIFIABLE→now discharged** — front-2 census CONFIRMED to
  the line (sole real sorries: `lowreg_loMass` `LowRegAllOrderJet.lean:1065`,
  (N) `ExtendViaUniqueness.lean:98`); but 8/11 claimed `#print axioms` runs had
  left no persisted artifact.  REPAIRED: see below.
- `overcount-hunt` **REFUTED (headline)** — **exhibit FOURTEEN**:
  `app_jet_sq_le` already was the per-index assembly (correction inline above).
  Also: the a₁/a₀ "arms already suffice" parenthetical hides ≥3 concrete Lean
  joints (see re-scope).  All three delivered artifacts confirmed to exist and
  check out structurally.

**Repairs landed this session (all green, claims released).**
1. `appCcPerIdxL2` folded to a thin wrapper over `app_jet_sq_le`
   (`B i := Λ i ^ 2`, `C := appCcGdiag q`); private `contRfns` deleted; file
   header rewritten to credit `app_jet_sq_le`; import added.  Focused check
   green (23.3s); statement byte-identical, `a2PerIdxJet`/`a2PerIdxLin`
   untouched.
2. False doc sentence fixed in `a2PerIdxJet`'s docstring (two-slot version).
3. Census persistence: 6 new `#print axioms` lines appended to
   `ScratchC01Census.lean` (import of `LowRegA2PerIndex` added) and NEW
   `ShortTime/ScratchIdentCensus.lean` with the two widened-identification
   lines.  Both census files run green: **every J4-PREP declaration
   `[propext, Classical.choice, Quot.sound]` only — zero `sorryAx`,
   independently re-verified and now reproducible.**  Targeted builds
   `+LowRegA2PerIndex`, `+ShortTime.LowRegGalerkinIdent` green (everything
   upstream replayed — the executor's olean state was current).
4. Two bracketed corrections inserted in the №152-report above.

**Counter adjudication.**  No route error scored; counter stays **0/3**.
Exhibit 14 is wasted re-derivation (~90 lines, now deleted), not a wrong route:
the statement was correct, consumer-facing shape right, and the intended proof
route (per-index grid + integrate) is exactly what `app_jet_sq_le` does.  The
false doc sentence is a bookkeeping over-claim.  The a₁/a₀ under-pricing is a
scope correction, absorbed into the dispatch below.

**Rung-3 re-scope (supersedes №151's "(4) then rung 3" single brick).**
The panel's named a₁/a₀ joints make part 4 two bricks:
- **Part 4a — the a₁/a₀ arm caps + per-index assemblies** (NEW, next dispatch):
  (i) order-0/1 fibre caps for `A.C0`/`A.C1` analogous to `lowData_split`'s C2
  cap (`DeTurckRemainderLowBaseAction.lean:3841` caps C2 only);
  (ii) per-index `H^{k-1}` assemblies for `A.a1 = appCc C0 W + appCc C1 (∇W)`
  and `A.a0` WITHOUT the H⁴ ball (`a1_ladder`/`a1LadderQ` are H⁴-radius-indexed
  and their docstring says the ball cannot be lowered — the per-index route
  does not need it), now CHEAP via the same `app_jet_sq_le` wrapper pattern as
  `appCcPerIdxL2`;
  (iii) promote/generalize the private C2-only helpers `jetCompSq`/`c2SupJet`
  (`LowRegA2PerIndex.lean`) to serve C0/C1 — public, lowest suitable layer.
- **Part 4b — the rung-3 closure at k=3**: pairing + L¹ₜ-Grönwall with adapter
  H threaded (`Cq(k−1)·Cδ* + K_R·R + 2ε < 1`), consuming `a2PerIdxLin` +
  part-4a arms + the widened identification + `two_mul_sum_ladder_le`
  (`CrossScaleCauchySchwarz.lean:232`) + `galerkin_energy_l1_bound`
  (`GalerkinParabolicEnergy.lean:497`) → `fatou_sq_mass`
  (`GalerkinCompactness.lean:28`); jet↔`H^n` bridges `hsJet_le`/`hs_le_jet`
  (`IteratedCovGradHsJetBound.lean:834/:855`); statement model
  `deTurckGalerkin_forcing_closure_perScaleSymm`
  (`GalerkinParabolicEnergyDeTurck.lean:1484`).  All confirmed present with
  zero consumers by the panel.

**Honest denominators.**  (N) **0%**; `lowreg_loMass` **0%**, machinery holds
at ≈ **70%** (the fold deletes duplication, adds nothing; the a₁/a₀ re-pricing
surfaces a joint that was always there).  Whole HCG ≈ **3%**.  Post-tame
remainder 11–18 central 14, with rung 3 = 4a+4b now explicitly two bricks.
Route-error counter **0/3**.

---

## №154 (executor, 2026-08-05) — BRICK 4a LANDED: the a₁ arm is priced from the
## other Hölder side; the dispatch's cap recipe would have broken the budget

**Delivered** (all green, axiom-census-clean, no new `maxHeartbeats`):
`a1PerIdxJet` and `a1PerIdxLin` in the new
`Analysis/Spectral/Intrinsic/DeTurck/LowRegA1PerIndex.lean`, on a new engine
`app_jet_sq_head` in `Sobolev/TensorHilbert/ParametricAppCcJetBound.lean`, plus
the promoted shared helpers `icgWinShift`/`sqrtAdd2`/`sqrtFinSum` in
`LowRegA2PerIndex.lean`.  There is no `A.a0` in Lean: `LowBaseActionData` has
`C0/C1/C2` and the arms `a1`, `a2` only, and `lowData_split` decomposes the
remainder as `a2 + a1`.  The paper's `a₁` and `a₀` arms are the two `appCc`
summands of `A.a1 = appCc C₀ T + appCc C₁ (∇T)`; both are covered.

### The finding: part (i) of the dispatch, taken literally, exceeds §6.4's budget

The dispatch asked for per-index `L^∞` caps on `∇ⁱC₀`/`∇ⁱC₁` from the sup
embedding composed with the towers' `range (i+2)` windows — i.e. the `a₂`
recipe.  That recipe **cannot** be used here.  The embedding costs `+2` `L²`
orders, so an `L^∞` coefficient at Leibniz index `i` reads the tower at index
`i+2`, hence — with window `range (i+2)` — state jets of order `i+3`; at the top
index `i = q` that is `q+3`, one **above** the rung budget `q+2`.  And there is
no slack to recover the way adapter (B-WIN) recovered it for `C₂`: `C₂` is
algebraic in `T`, but `C₁` genuinely contains `∇T` and `C₀` is quadratic in it,
so `range (i+2)` is sharp for both.  I did not widen and did not invent a
smallness constant.

The resolution is §6.4 itself, read carefully: its parenthetical for these arms
names `‖∇U‖_∞ ≲ ‖U‖_{H³}` and `‖U‖_∞ ≲ ‖U‖_{H²} ≤ R` — sup norms of the
**state**, not of the coefficient.  So §6.4 prescribes the *other* Hölder side
for these arms, which is exactly why it says the landed `range (i+2)` windows
"suffice".  Implemented: index `0` keeps the coefficient in `L^∞` (embedding
reads the tower at index `≤ 2`, state order `≤ 3`); every index `i ≥ 1` puts the
state window in `L^∞` and reads `∇ⁱC` in `L²` at its own tower index.  The stop
condition "if §6.4 actually demands a small constant somewhere in these arms,
STOP" did not fire — it demands a different split, not a constant.

### Order ledger (honest, two-slot style)

With `J n = ∑_{j<n}‖∇ʲT‖²` (so `J n` sees jets `≤ n-1`):

| slot | coefficient factor | data factor | top state order |
|---|---|---|---|
| `C₀`, `i=0` | `(1+J 4)²` | `J(q+1)` | `max(3, q)` |
| `C₀`, `i≥1` | `(1+J 4)(1+J(i+2))` | `J(q-i+3)` | `≤ q+1` |
| `C₁`, `i=0` | `(1+J 4)` | `J(q+2)` | `max(3, q+1)` |
| `C₁`, `i≥1` | `(1+J(i+2))` | `J(q-i+4)` | `≤ q+2`, `=` at `i=1` |

For `q ≥ 1` — every rung, since `q = k-1 ≥ 2` — nothing exceeds `q+2`, and the
top order `q+2` occurs in exactly ONE slot: the `i=1` term of the `C₁` group,
whose companion factor is `1 + J 3`, the class `H²` radius.  **Consequence for
4b: the `a₁` arm costs the rung neither `Cδ*` nor `K_R·R`** — its top slot is
class × pairing factor, which Young turns into `εX²` + class.  Adapter H stays
an `a₂`-only statement: `Cq(k−1)·Cδ* + K_R·R + 2ε < 1`.

> [Planner correction, №155 — acceptance panel, 4b-readiness verifier:
> **REFUTED, route error**.]  The ledger's window arithmetic above is correct
> (verified line-by-line), and "exactly ONE slot at `q+2`" holds for `q ≥ 2`
> (at `q = 1` four factors reach it — docstring imprecision).  But the
> **consequence drawn is FALSE**: the top slot `class·(1+jet_{H²})·jet_{q+2}`
> is NOT "Young ⟹ εX² + class".  In the cross-scale pairing every forcing
> slot reaching `√E_{σ+1}` contributes its coefficient to `α` in
> `two_mul_sum_ladder_le`'s `hladder`, and `(2α+ε)·E_{σ+1}` must clear the
> absorption `Cδ < 2`; this slot's `α`-contribution is `K₁·C_J·(1+C·R)` — a
> non-small, `R`-free constant.  The Young argument applies only to slots
> LINEAR in `√E_{σ+1}` after pairing; this one is quadratic.  The uniform
> state-side `L^∞` choice at all `i ≥ 1` is therefore a route-level error:
> the landed `a1PerIdxJet`/`a1PerIdxLin` cannot be consumed by the rung.
> Correct split (№155 ruling): coefficient-side `L^∞` at `1 ≤ i ≤ q−1`
> (state order `i+3 ≤ q+2`, in budget), state-side ONLY at `i = q`; then all
> `q+2` occurrences meet class-radius factors and adapter H widens to
> `Cq(k−1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε < 1`.  PSTOP §6.4/§10 corrected;
> v2 brick dispatched.  Counter: **1/3**.

### Exhibit FIFTEEN (same shape as 14, smaller)

Part (iii) asked to promote `jetCompSq`.  It did not need promoting: the public
`icgNormComp` (`Sobolev/TensorHilbert/GradCapAtgw.lean`) already is that lemma
in norm form, inside both files' import closure.  `jetCompSq` was a ~20-line
re-derivation; deleted, both call sites now use `icgNormComp`.  Two further
private copies exist (`norm_iteratedCovGrad_comp`,
`AllOrderGardingConstant.lean:143`; `jet_comp_norm`,
`Garding/SlotTransportPairing.lean`) plus a second window-shift copy
(`jet_shift_le`, same file).  Left alone — deduplicating them means editing deep
prefixes of the build graph for zero mathematical gain; recorded as a punch-list
in `LowRegA1PerIndex.md`.  The census sweep for the *engine* was done properly
this time and came back genuinely empty: `app_jet_sq_le`/`app_jet_of_bdd` are
coefficient-side only, and `appCc_topOrder_l2_twoArm_mixed_le` collapses both
sides onto single constants, which is precisely what destroys the per-index
accounting.  Hence `app_jet_sq_head` is a real new producer, placed next to the
engine it generalizes.

`icgWinShift`/`sqrtAdd2`/`sqrtFinSum` were promoted **in place** in
`LowRegA2PerIndex.lean` rather than moved to their ideal home (`GradCapAtgw` /
a real-analysis file): moving them forces a rebuild of a very deep prefix, and
the dispatch sanctioned importing the a₂ file for shared helpers.  Flagged in
the note as a deferred relocation.

### Verification

Focused checks green on all four touched/created files; targeted builds green
for `ParametricAppCcJetBound`, `LowRegA2PerIndex`, `LowRegA1PerIndex`.  Six new
`#print axioms` lines appended to `ScratchC01Census.lean` (import added); the
census file runs green and **every** new declaration —`app_jet_sq_head`,
`icgWinShift`, `sqrtAdd2`, `sqrtFinSum`, `a1PerIdxJet`, `a1PerIdxLin` — reports
`[propext, Classical.choice, Quot.sound]` only, zero `sorryAx`.  Claims released.

### Honest denominators

Brick 4a ≈ **100%** of itself, and rung 3 = 4a + 4b, with 4b carrying the actual
mathematics (pairing + L¹ₜ-Grönwall + the closure statement).  Brick 4a is ≈
**25%** of rung 3 — it is input plumbing, not the rung.  **J4-rung-3: still 0%
stated.**  `lowreg_loMass`: theorem **0%** (`LowRegAllOrderJet.lean:1052`); its
dedicated machinery ≈ 70% → ≈ **73%** (one named input landed; the rung itself
unwritten).  `(N) ricci_flow_unif_existence`: theorem **0%**, untouched.  Whole
HCG compactness project: ≈ **3%**.  Post-tame remainder: **11–18, central 14**,
unchanged.  Route-error counter: **0/3** — no route error; the dispatch's part
(i) was a paraphrase slip of §6.4, caught before any Lean was written.

### Next smallest step (brick 4b)

State the rung-3 closure at `k = 3` with `q = k-1 = 2`, modelled on
`deTurckGalerkin_forcing_closure_perScaleSymm`
(`GalerkinParabolicEnergyDeTurck.lean:1484`): consume `a2PerIdxLin` +
`a1PerIdxLin`, bridge jets↔`H^n` with `hsJet_le`/`hs_le_jet`, pair via
`two_mul_sum_ladder_le` (`CrossScaleCauchySchwarz.lean:232`), and thread adapter
H as an explicit hypothesis on the `a₂` arm alone.  The `a₁` arm enters only
through the `2ε` Young margin.

> [Planner, №155: this handoff is SUPERSEDED — see the correction above and
> №155.  The a₁ assembly needs the mixed-split v2 first; 4b's dispatch will
> follow №155's joint ledger.]

---

## №155 (planner, 2026-08-05) — BRICK 4a: PANEL VERDICT 4×CONFIRMED,
## 1×REFUTED (JOINT-A1TOP); ROUTE ERROR SCORED (1/3); a₁ v2 RULED + DISPATCHED

**Acceptance instrument.**  Second adversarial panel (run `wf_0fcfed91-d0d`,
5 read-only skeptics, ~760k tokens).

**Verdicts.**
- `order-ledger` **CONFIRMED** — the landed statements' windows match №154's
  table slot-for-slot; nothing exceeds `q+2` for `q ≥ 1`; constants before
  `T`/`δ`; no ball binder; `hDim` threaded.  Caveat: "exactly ONE slot at
  `q+2`" is false at `q = 1` (true at every rung `q ≥ 2`) — docstring
  imprecision, fix in v2.  The impossibility arithmetic for the dispatched
  recipe (coefficient-sup at `i = q` reads `q+3`; no sharp C0/C1 tower exists)
  verified against the tower statements.
- `engine-novelty` **CONFIRMED** — `app_jet_sq_head` is a genuine new producer;
  six candidate pre-existing engines each fail for a citable reason (incl. the
  private `master_appCc_jet_le_sharp`, fused to Hs-ball hypotheses, and the
  HEAD-side `appCc_split_env`, which collapses the coefficient tail).  No
  exhibit sixteen.
- `statement-preservation` **CONFIRMED** — a₂ file's three public theorems
  match all cited records; `icgNormComp` is the deleted `jetCompSq` at general
  valence; rewired call sites correct; `icgWinShift` generalization
  conservative.  Caveat: the composition-lemma duplicate count is FIVE private
  copies, not two (three more found: `norm_iteratedCovGrad_comp_cc`,
  `norm_iteratedCovGrad_comp_local` ×2) — punch-list undercount, folded into
  the deferred dedup list ([[todo-dedup-iteratedcovgrad-smul]] adjacent).
- `census-inventory` **CONFIRMED** — no `A.a0` (three-field structure, two
  arms, `lowData_split = a2 + a1`; paper's a₁/a₀ = the two `appCc` summands,
  both covered); six census lines exist and target real declarations;
  front-2 sorry census unchanged (`lowreg_loMass`:1065 + (N):98); size/naming
  discipline clean.
- `fourb-readiness` **REFUTED** — **JOINT-A1TOP**, the breaker: see the
  bracketed correction in №154.  The landed `a1PerIdxLin` puts a non-small
  `R`-free constant into the `E_{k+1}` absorption via its top slot; the rung
  cannot consume it.  №154's "εX² + class" pricing confused linear-in-X
  pairing terms with quadratic ones.

**Counter adjudication: ROUTE ERROR, 1/3.**  The uniform state-side `L^∞`
choice at all `i ≥ 1` survived into the landed statement, its docstring, the
`.md` note, and the 4b handoff — a consumer-unusable public statement is a
wrong route, not bookkeeping.  Shared responsibility recorded: §6.4's
parenthetical (planner-approved paper design) prices only extreme Leibniz
indices and is silent on intermediate ones — the paper gap is the root cause;
the executor generalized the parenthetical's state-side reading to every
index without re-running the pairing arithmetic.  Caught by the acceptance
panel before 4b was stated (the guard worked).  PSTOP §6.4 correction block +
§10 adapter-H widening written this session.

**№155 RULING — the a₁ mixed split (v2).**
- Per-index Hölder choice: `i = 0` head (coefficient `L^∞`, as landed);
  `1 ≤ i ≤ q−1` **coefficient-side** `L^∞` (sup at index `i` reads the
  `range (i+2)` tower at `i+2` ⟹ state order `i+3 ≤ q+2`, in budget);
  `i = q` **state-side** `L^∞` (coefficient `∇^q C` in `L²` reads tower `q`,
  state order `q+1`; data sup ≤ class).  All `q+2` occurrences then meet
  class-radius factors (`K·R`-type), none needs smallness.
- Engine: neither `app_jet_sq_le` (all-coefficient-sup) nor `app_jet_sq_head`
  (head-only) gives the mixed split.  v2 adds ONE finset-parameterized engine
  (`app_jet_sq_split S`: coefficient caps on `i ∈ S`, data caps on `i ∉ S`),
  of which `le`/`head` are the `S = range (j+1)` / `S = {0}`… instances — or,
  if the general form fights elaboration, the specific three-region statement.
  Same integration route (the diagonal grid + integrate); no new analysis.
- `a1PerIdxJet`/`a1PerIdxLin` REPLACED in place (same names, corrected
  windows/slots): zero consumers exist, both born this week — no compat
  wrappers.  Census lines stay (same names).  Docstrings: two-slot honesty +
  the `q = 1` scoping fix.
- Adapter H (final form, PSTOP §10): `Cq(k−1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε
  < 1`, `K_R^{a₁}` from the C0/C1 tower constants.

**Joint ledger for 4b (from the panel; carried into the 4b dispatch).**
1. ~~JOINT-A1TOP~~ → the v2 brick (dispatched now).
2. JOINT-BESSEL: finite-`S` `(1+λ)^n`-weighted mode mass of a `SmoothCcTensor`
   ≤ `‖ccTensorToHs n ·‖²`; only near-producer `mode_le_jet` is private and
   `λ^j/tsum`-shaped (`SobolevScale/IteratedCovGradHsJetBound.lean:438`).
3. JOINT-NEMYTSKII: eval-at-smooth-point for `lowregNfun = Dense.extend coreN`
   (`LowRegDenseSolve.lean:75`) + `coreN → lowData_split` arm reach + a
   low-reg static seed-mass producer `‖𝒩(0)‖_{H²} ≤ class` (none found).
4. JOINT-REP: thread `δ ≤ 1/3` + symmetry + fibre caps from the class data
   (ball→fibre exists at `lowregRealRad` via `lowregStateRad_le_P`,
   `UnifClassBounds.lean:220–230`).
5. JOINT-IDENT (post-closure): ODE-trajectory coordinates = `perModeConv` of
   the projected forcing — missing, and named missing by `lowreg_loMass`'s own
   docstring (:1041–1051); high-reg analogue is private
   (`galerkinPerMode_eq_perModeConvSymm`, `GalerkinLimitUniformMass.lean:70`).
   This partially reopens №151's seam: №151's "ride the projected sequence"
   stands for the FATOU stage, but the ENERGY stage cannot run on the
   identification's a.e.-t exports.
6. JOINT-RETR: keep the retraction inert along the run (`galTameForce_eq`,
   `GalerkinTameSol.lean:627`) — the model closure has no retraction.
- ARCHITECTURE (panel, adopted): the closure/Grönwall runs on `lowregGalSol`'s
  ODE trajectory (which ALREADY supplies ∀-t mode continuity, per-mode ODE,
  zero seed, finset support — under-count in №154's handoff, `galerkin_energy_l1_bound`'s
  inputs are ready there); the widened identification is consumed only at the
  Fatou stage.  Note: `hsJet_le`/`hs_le_jet` real home =
  `Analysis/Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean`
  (:834/:855), not TensorHilbert — path corrected for future dispatches.

**Honest denominators.**  (N) **0%**; `lowreg_loMass` **0%**; machinery
revised DOWN ≈73% → ≈**71%** (4a's durable content — engine, caps, promotions
— is ~+1pp; the assembly statement needs v2 before anything consumes it).
Rung 3: **0% stated**; it now = v2 → 4b, with 4b's joint ledger above priced
into the standing post-tame 11–18 central 14 (the ledger names what "4b" was
always going to contain; no re-pricing).  Whole HCG ≈ **3%**.  Route-error
counter: **1/3**.

---

## №156 (executor, 2026-08-05) — a₁ v2 LANDED: the mixed per-index split, on a
## new finset-parameterized engine; ledger verified against №155, one rider

**Delivered** (green, census-clean, no new `maxHeartbeats`, no consumer churn):

- `app_jet_sq_split` in `Sobolev/TensorHilbert/ParametricAppCcJetBound.lean` —
  the mixed engine.  For `S ⊆ range (j+1)`: coefficient caps `B i` on `S`, data
  caps `D i` off it, conclusion the per-index sum with the coefficient jets in
  `L²` on the complement.  `app_jet_sq_le` is `S = range (j+1)`,
  `app_jet_sq_head` is `S = {0}`; the a₁ arm uses `S = range q`.  Same
  integration route as its two siblings; the one new ingredient is
  `Finset.sum_sdiff`.  Neither `B` nor `D` needs a nonnegativity hypothesis.
- `a1PerIdxJet` / `a1PerIdxLin` **replaced in place** in
  `Spectral/Intrinsic/DeTurck/LowRegA1PerIndex.lean` (same names, corrected
  windows).  Private helpers reworked; `dataCap` **deleted** — v2 sup-caps only
  the single data term `l = 0`, which is the fibre embedding applied to `T`
  resp. `∇T` directly, so the wrapper carried no content.
- Census: `app_jet_sq_split` line added; the six existing brick-4a lines still
  target real declarations (names unchanged).

**The v2 ledger, verified slot by slot before proving** (`J n = ∑_{j<n}‖∇ʲT‖²`):

| slot | coefficient factor | data factor | top state order |
|---|---|---|---|
| `C₀`, `i < q` | `(1+J 4)(1+J(i+4))`, sup | `J(q-i+1)` | `i+3 ≤ q+2` |
| `C₀`, `i = q` | `(1+J 4)(1+J(q+2))`, `L²` | `J 3`, sup | `max(q+1, 3)` |
| `C₁`, `i < q` | `(1+J(i+4))`, sup | `J(q-i+2)` | `i+3 ≤ q+2` |
| `C₁`, `i = q` | `(1+J(q+2))`, `L²` | `J 4`, sup | `max(q+1, 3)` |

This is №155's expected ledger, slot for slot: for `q ≥ 1` nothing exceeds
`q+2`; `q+2` is reached only in the COEFFICIENT sup at the single index
`i = q-1` of either group (tower index `q+1`, window `range (q+3)`), and its
data companion there is `J 2` (`C₀`) resp. `J 3` (`C₁`) — class-order.  No slot
puts a non-class, non-small constant against state order `q+2`.  The `q = 1`
scoping fix is in both docstrings and the note.

**One rider, reported not improvised.**  `c0_jet_tower_quad` is quadratic in
`T`, so every `C₀` slot — the `i = q-1` one included — carries the extra factor
`1 + J 4 = 1 + ‖T‖²_{H³}`, an `L²_t` quantity rather than a class one.  So the
`C₀` top slot's contribution to the `E_{k+1}` coefficient is
`K·R·(1+‖U‖_{H³}(t))`, not `K·R`; the `C₁` top slot is exactly
`K_R^{a₁}·R`-shaped.  This is inherited from the tower (it *is* §6.4's own
`‖∇U‖_∞ ≲ ‖U‖_{H³}`) and was present in v1 too — it is not a v2 artefact and it
does not change the ruled split — but adapter H as phrased prices only
`K_R^{a₁}·R`.  4b must either absorb `K R (1+E₃(t)^{1/2})·D_k` with an argument
that survives `E₃` being only `L¹_t`, or re-price the `C₀` top slot (a `c0`
tower variant whose quadratic factor sits at a class window).  Flagged in
`LowRegA1PerIndex.md` and in the two docstrings so 4b cannot inherit it
silently; no PSTOP edit made, since the choice between (i) and (ii) is a
planner ruling.

**Engine novelty re-checked (exhibit-14/15 discipline).**  Empty again:
`app_jet_sq_le`/`app_jet_of_bdd` coefficient-side only;
`appCc_topOrder_l2_twoArm_mixed_le` collapses both sides onto single constants;
`appCc_split_env` collapses the coefficient tail; and the private
`master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:475`) — the
closest relative, and notably the SAME threshold direction (coefficient sup at
low indices, data side at high) — is fused to `Hs`-ball hypotheses and collapses
its conclusion onto one `Hs` norm.  No exhibit sixteen.

**Verification.**  Focused checks green on all three touched files; targeted
builds green for `+…ParametricAppCcJetBound` and `+…LowRegA1PerIndex`
(`LowRegA2PerIndex` untouched).  Census run: no `sorryAx` anywhere in its
output; `app_jet_sq_head`, `app_jet_sq_split`, `icgWinShift`, `sqrtAdd2`,
`sqrtFinSum`, `a1PerIdxJet`, `a1PerIdxLin` all
`[propext, Classical.choice, Quot.sound]`.  Claims released.

**Honest denominators.**  v2 is ≈**25%** of rung 3 (it restores 4a's ~25% of
plumbing to a consumable state; 4b still carries the rung's actual mathematics —
pairing, `L¹_t`-Grönwall, the closure statement).  **Rung 3: still 0% stated.**
`lowreg_loMass`: theorem **0%**; dedicated machinery ≈**71%** unchanged (v2
repairs a statement that №155 had already discounted to zero value, so no
increment is claimed).  `(N)`: theorem **0%**.  Whole HCG ≈ **3%**.
Route-error counter: **1/3**, unchanged.

**Next smallest step (4b).**  State the rung-3 closure at `k = 3`, `q = 2`, on
`lowregGalSol`'s ODE trajectory (∀-t mode continuity, per-mode ODE, zero seed,
finset support are already there), consuming `a2PerIdxLin` + `a1PerIdxLin`,
bridging jets↔`H^n` with `hsJet_le`/`hs_le_jet`
(`SobolevScale/IteratedCovGradHsJetBound.lean:834/:855`), pairing via
`two_mul_sum_ladder_le`, and threading adapter H in the **widened** form
`Cq(k-1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε < 1` — with the `C₀` rider above resolved
first, since it changes what `K_R^{a₁}` can mean.  Joint ledger unchanged:
JOINT-BESSEL, JOINT-NEMYTSKII, JOINT-REP, JOINT-IDENT (Fatou stage only),
JOINT-RETR.

---

## №157 (planner, 2026-08-05) — v2 ACCEPTED; RIDER RULED (amended at panel:
## per-group asymmetric split); planner near-miss recorded; 4b decomposed

**Acceptance instrument.**  Third panel (run `wf_35a3e057-ad7`, 3 read-only
verifiers): `v2-ledger` CONFIRMED, `rider-audit` REFUTED-the-draft,
`fourbpre-scout` CONFIRMED.

**v2 ACCEPTED.**  Every Finset window in all four statements matches the №156
ledger at general `q` and at `q = 2`; the engine reduces to both extremes;
binder order, ball-freeness, `hDim`, docstring scoping all verified.  Two
non-refuting caveats recorded: the table's "top state order" column mixes
conventions (i<q rows report the sup factor's order, not the slot max — the
data companion can exceed it while staying ≤ q+1), and the `q = 1` docstring
enumeration is illustrative, not exhaustive.

**PLANNER NEAR-MISS (recorded, not scored).**  My draft rider ruling — Young
at the ladder level, `K·R·√E₃·√E₄ ≤ (K·R/2)(E₃+E₄)` — was REFUTED by the
audit: the cross-scale pairing multiplies every ladder entry by a further
`√E_{σ+1}` (`abs_sum_crossScale_le`, `CrossScaleCauchySchwarz.lean:75–80`), so
the slot's true contribution is `K·R·(1+√E₃(t))·E₄` — a TIME-DEPENDENT
`E₄`-coefficient, which no landed Grönwall variant accepts
(`galerkin_energy_l1_bound` hard-codes constant `Cδ < 2`; time dependence is
allowed only on the same-scale term) and no Young repairs (`√E₃·E₄` is
supercritical).  This is the mirror of the №155 error (ladder-level vs
pairing-level, off by one Cauchy–Schwarz factor).  NOT scored: the draft was
sent to adversarial verification BEFORE adoption and never entered a ruling or
dispatch — the check-first discipline did its job, twice now.  Standing rule
(new): planner pricing arithmetic is panel-checked before it is ruled.
Counter stays **1/3**.

**№157 RULING — the rider, amended form (audit-checked, adopted).**
Per-GROUP asymmetric split boundaries for the a₁ arm:
- **C₁ summand: keep `S = range q`** (v2 as landed).  Its `i = q−1`
  coefficient-sup slot reads `q+2` against the class window `J 3` — the
  `K_R^{a₁}·R` absorption term of adapter H.
- **C₀ summand: re-split at `S = range (q−1)`** — state-side at BOTH
  `i = q−1` and `i = q`.  Legal precisely because C₀'s data at `i = q−1` is
  only `∇T` (sup order 3, in budget), where C₁'s would be `∇²T` (order 4, the
  v1 breaker).  Then C₀ never touches `q+2` at all: its worst slot is
  `K·(1+E₃(t))·class` with NO `√E₄` factor, pairing → `K(1+E₃)·√E₄` → Young →
  `ε·E₄ + A(t)·E₃ + class`, `A(t) = C·(1 + E₃(t)) ∈ L¹_t` (`∫E₃ ≤ B₃²`) —
  §6.4's own a₂-`l=1` mechanism.  Uniform over rungs 3–5 (`J(q+1)` sits at
  `H^{k−1} ≤ R_{k−1}`, §5 upward ordering).
- Rejected alternative: a c0-tower variant with the quadratic factor at a
  class window = a new embedding layer (the tree deliberately lacks the
  Agmon/fractional interpolation; PSTOP:571–578) — high cost, zero need.
- Adapter H: UNCHANGED from №155's widened form (only a₂ + C₁ feed it).
- Consequence: **a₁ v3 touch, C₀ arm only** — re-instantiate `a1Arm0` with
  `S = range (q−1)`, adjust the C₀-group windows in `a1PerIdxJet`/`Lin`,
  docstrings; C₁ path untouched.  Same names, zero consumers, no wrappers.

**Interface extensions assigned to 4b (audit item, needed regardless of the
rider).**  `hladder` has no additive-constant term and the closure no additive
slot, so §6.4's own display (`(1/2ε)‖𝒩(0)‖² + c_cls`) is inexpressible as
landed.  Two routine variants: `two_mul_sum_ladder_le` with `+γ` (one extra
Young) and the Grönwall bound with `seed²/4 + c₀` (same proof shape as the
existing seed term).

**4b decomposition (scout-verified, supersedes the №156 handoff).**
- **Brick A (dispatch now): a₁ v3 (C₀ re-split) + JOINT-BESSEL + seed mass.**
  BESSEL: finite-`S` `(1+λ)^n`-weighted mode mass of a `SmoothCcTensor` ≤
  `‖ccTensorToHs n ·‖²` — genuinely new public lemma (near-producer
  `mode_le_jet` private and `λ^j/tsum`-shaped,
  `SobolevScale/IteratedCovGradHsJetBound.lean:438`).  Seed mass: port of
  `deTurckGalerkinForcing_seed_mass` at `a = 1` via `lowRegN_on_smooth` at
  `S = 0` (skeleton `GalerkinParabolicEnergyDeTurck.lean:446–470`; the
  `ha_super` gate is what blocks direct reuse); depends on BESSEL.
- **Brick B: 4b-pre, the forcing-realization lemma** (ONE assembly session,
  all six links scout-verified constructible): along `lowregGalSol`'s
  trajectory — (a) state ∈ `smoothCore` with named rep `t•finiteEigenCombo`
  (glue via `finiteEigenComboHs_eq` `DeTurckRemainderDefs.lean:119`,
  `smoothCcToTensorHs_smul`); (b) `lowregNfun(state) = deTurckSmoothN 1
  (symmS rep)` — the eval layer EXISTS (`LowRegSmoothBridge.lean`:
  `lowRegN_on_core`:67, `lowRegN_on_smooth`:84, `lowReg_force_smooth`:127);
  (c) `𝒩(state) − 𝒩(0) = smoothCcToTensorHs 1 (A.a2 + A.a1)` with the C2 cap
  (`deTurckSmoothN_sub_eq_…remainderSub` `SobolevNonlinearityExistence.lean:229`
  + `lowData_split`).  MUST take IsLowSolve-grade inputs directly
  (`0 ≤ δ ≤ 1/3`, `Continuous coreN`, `hreal` at `P` — all IsLowSolve fields,
  `UnifClassBounds.lean:423–427`); `lowreg_proj_tendsto` DISCARDS them
  (`LowRegGalerkinIdent.lean:121–122`) — export gap noted, do not route
  through it.  Hypothesis transport producers all named by the scout
  (`ccTensorBilin_symmS_symm`, `coreSymm_h2`, `lowregStateRad_le_P`,
  zero-embed pattern).
- **Brick C: 4b-core** — the closure statement + pairing + `L¹_t`-Grönwall
  with the two interface variants, adapter H threaded; then JOINT-IDENT
  (Fatou-stage; `galerkinPerMode_eq_perModeConvSymm` is private high-reg
  analogue) and JOINT-RETR (`galTameForce_eq` exists) at the Fatou wiring.

**Honest denominators.**  (N) **0%**; `lowreg_loMass` **0%**, machinery
≈**71%** (unchanged — v3 is a repair inside 4a's share; BESSEL/seed are small
new API).  Rung 3 **0% stated**; it is now Bricks A→B→C.  Whole HCG ≈ **3%**.
Post-tame 11–18 central 14 (the decomposition names the work, does not add
it).  Counter **1/3**.

---

## №158 (executor, 2026-08-05) — BRICK A LANDED: a₁ v3 (`C₀` re-split) + the
## `a = 1` seed mass; JOINT-BESSEL is an OVER-COUNT (exhibit sixteen)

**Part 1 — a₁ v3, landed.**  `a1Arm0` re-instantiated with the mixed engine at
`S = Finset.range (q-1)` (state-side at BOTH `i = q-1` and `i = q`); `a1Arm1`
untouched at `S = Finset.range q`.  `a1PerIdxJet` / `a1PerIdxLin` replaced in
place (same names, zero consumers), both docstrings and the module header
rewritten for the per-group boundaries.  One private helper added, `sumPairLe`
(`∑_{i ∈ {a,b}} f i ≤ f a + f b` for nonnegative `f`) — needed because the `C₀`
complement `range (q+1) \ range (q-1)` is the PAIR `{q-1, q}`, which collapses
to a singleton at `q = 0`, so `Finset.sum_pair` does not apply.  **No new
producer**: the second data cap at `i = q-1` is the rank-`(0,3)` fibre embedding
composed with `icgWinShift`, exactly the pair `a1Arm1` already used for `∇T`.

**Verified v3 `C₀` ledger** (checked slot by slot BEFORE proving; `J n` sees
state jets of order `≤ n-1`; read `q-1+2 = q+1`, valid for `q ≥ 1`):

| slot | coefficient factor | data factor | top state order |
|---|---|---|---|
| `C₀`, `i ≤ q-2` | `(1+J 4)(1+J(i+4))`, sup | `J(q-i+1)` | `max(i+3,3) ≤ q+1` |
| `C₀`, `i = q-1` | `(1+J 4)(1+J(q+1))`, `L²` | `J 4`, sup | `max(q, 3)` |
| `C₀`, `i = q` | `(1+J 4)(1+J(q+2))`, `L²` | `J 3`, sup | `max(q+1, 3)` |
| `C₁`, `i < q` | `(1+J(i+4))`, sup | `J(q-i+2)` | `i+3 ≤ q+2` |
| `C₁`, `i = q` | `(1+J(q+2))`, `L²` | `J 4`, sup | `max(q+1, 3)` |

This is №157's expected ledger: the `C₀` group tops out at `q+1`, never `q+2`;
its evolving factors `1 + J 4` meet only class windows (`J(q+1)`, `J 3`) and the
same-scale `J 4`, with NO `√E_{q+2}`-order data factor, so they land in the
`L¹_t` Grönwall coefficient; and the sole `q+2` in the whole arm remains `C₁`'s
`i = q-1` coefficient sup against `J 3`.  Adapter H unchanged (№155 widened
form).  **One honest refinement of the ruling's phrasing**: the `q ≥ 2` scope
now covers the `C₀` claim too, not only the "exactly one slot" reading — at
`q = 1` the `C₀` data sups already reach `3 = q+2`.  Every rung has `q ≥ 2`, so
nothing is lost; it is stated in both public docstrings.  Not a disagreement, so
no STOP was triggered.

**`q = 0` handled without a hypothesis.**  The `i = q-1` coefficient window is
written `range (q-1+2)` — literally what `c0_jet_tower_quad` produces at index
`q-1` in ℕ — which is `range (q+1)` for every `q ≥ 1`.  The sharper `range (q+1)`
spelling would have been unprovable at `q = 0`.  So the statement is
unconditional, as preferred.

**Part 2 — JOINT-BESSEL: NOT WRITTEN, it already exists TWICE.  Over-count
exhibit sixteen.**  The dispatch's target — finite-`S` `(1+λ)^n`-weighted mode
mass of a `SmoothCcTensor` ≤ `‖ccTensorToHs n ·‖²` — is verbatim
`cc_partial_le_norm`, PUBLIC, at
`Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean:165`, i.e. 273
lines ABOVE the private `mode_le_jet` the scout reported as the only
near-producer.  The fully general `tensorHs`-level form is also public:
`weight_sum_le_normSq` (`Spectral/Intrinsic/TensorHsInterpolationLimit.lean:210`),
docstring literally "**Finite-set Bessel truncation in `Hˢ`**", and its own
docstring already names the Galerkin use ("lets a spectrally truncated
(Galerkin) energy estimate read an `Hˢ` bound").  Only the first is in the
ShortTime import closure — `TensorHsInterpolationLimit` is NOT imported there
despite being two hops away, which is worth remembering.  No new lemma; no
duplicate created.

**Part 3 — the low-reg static seed mass, landed.**  `lowRegSeedMass` in
`ShortTime/LowRegSmoothBridge.lean`: for every `n : ℕ` and every FINITE mode set
`F`, `∑_{i ∈ F} (1+λᵢ)^n · (𝒩(0).coeff i)² ≤ Cseed n ²` with
`Cseed n = ‖smoothCcToTensorHs g₀ n (deTurckSmoothRemainder g₀ g_bg (symmS g₀ 0))‖`.
Route: zero-embed + `Subtype.ext` → `lowRegN_on_smooth` at `S = 0` →
`deTurckSmoothN_coeff` → `cc_partial_le_norm`, with the `rfl`-level bridge
`ccTensorToHs g₀ 2 σ = smoothCcToTensorHs g₀ σ`.  The `2·finrank+10 ≤ a` gate of
`deTurckGalerkinForcing_seed_mass` is used there ONLY to identify the abstract
nonlinearity at zero with a smooth remainder; the dense extension supplies that
directly at `a = 1`, so no supercriticality hypothesis appears.  **Shape
decision** (recorded in the note): quantify over an arbitrary finite `F` and
arbitrary `n`, not over `eigenIdxFinset N` at a fixed order — strictly stronger,
free from `cc_partial_le_norm`, and it leaves Brick C free to pick its own
truncation family.  Constants are per-datum (`g₀`, `g_bg`, `δ`); the rung needs
`N`-freeness, which this has.

**Verification.**  Focused checks green on `LowRegA1PerIndex.lean`,
`LowRegSmoothBridge.lean` and both census files; targeted builds green for
`+…LowRegA1PerIndex`, `+…LowRegSmoothBridge`, `+…ScratchC01Census`,
`+…ScratchIdentCensus`.  Census: `lowRegSeedMass`, `cc_partial_le_norm` (added
to `ShortTime/ScratchIdentCensus.lean`) and the seven brick-4a lines all report
`[propext, Classical.choice, Quot.sound]`; **zero occurrences of `sorryAx` in
either census output**.  Two local style warnings introduced by the v3 edit
(`show`-that-changes-the-goal; a two-goal `refine`) were cleaned in place.  No
new `maxHeartbeats`.  No read-only other-lane file touched.  Claims released.

**Honest denominators.**  Brick A is ≈**30%** of rung 3 by effort but ≈**0%** of
its mathematics: v3 is a repair inside 4a's plumbing share, and Parts 2–3 are
one small new API lemma plus one dissolved exhibit.  **Rung 3: still 0%
stated** — Bricks B and C carry all of the pairing, the `L¹_t` Grönwall and the
closure statement.  `lowreg_loMass`: theorem **0%**; dedicated machinery
≈**71%** — held, not raised: v3 repairs a statement №155 had already discounted
to zero value, JOINT-BESSEL turned out to be pre-existing (so it was never
missing machinery), and `lowRegSeedMass` is genuinely new but worth well under
a point.  `(N)`: theorem **0%**.  Whole HCG ≈ **3%**.  Route-error counter
**1/3**, unchanged.

**Next (Brick B, spec in №157).**  The forcing-realization lemma along
`lowregGalSol`'s trajectory, one assembly session, six scout-verified links:
(a) state ∈ `smoothCore` with named rep `t • finiteEigenCombo` (glue
`finiteEigenComboHs_eq`, `DeTurckRemainderDefs.lean:119`, plus
`smoothCcToTensorHs_smul`); (b) `lowregNfun(state) = deTurckSmoothN 1 (symmS
rep)` via the existing eval layer (`LowRegSmoothBridge.lean`:
`lowRegN_on_core`:67, `lowRegN_on_smooth`:84, `lowReg_force_smooth`:127 —
`lowRegSeedMass` now sits beside them and is the `state = 0` instance of exactly
this pattern); (c) `𝒩(state) − 𝒩(0) = smoothCcToTensorHs 1 (A.a2 + A.a1)` with
the C2 cap (`deTurckSmoothN_sub_eq_…remainderSub`,
`SobolevNonlinearityExistence.lean:229`, plus `lowData_split`).  It MUST take
`IsLowSolve`-grade inputs directly (`0 ≤ δ ≤ 1/3`, `Continuous coreN`, `hreal`
at `P` — `UnifClassBounds.lean:423–427`); do NOT route through
`lowreg_proj_tendsto`, which discards them (`LowRegGalerkinIdent.lean:121–122`).

---

## №159 (planner, 2026-08-05) — BRICK A ACCEPTED: panel 3/3 CONFIRMED;
## exhibit sixteen legitimate; four caveats recorded; Brick B in flight

**Acceptance instrument.**  Fourth panel (run `wf_eea8273a-d8a`, 3 read-only
verifiers), run CONCURRENTLY with the Brick B executor — first concurrent
panel+executor operation (panel is read-only and runs no Lean; no
interference).

**Verdicts (all CONFIRMED).**
- `v3-ledger` — all five №158 table rows match the landed statements
  window-for-window (general `q` + hand instantiation at `q = 2`); C₀ never
  reaches `q+2` for `q ≥ 2` and carries no `√E_{q+2}`-order factor; the sole
  arm `q+2` is C₁'s `i = q−1` slot against `J 3`; `sumPairLe` correct incl.
  the `q = 0` pair collapse; `a1Arm1` statement-identical to v2; PSTOP
  §6.4/§10 carry the №157 amendment verbatim.
- `exhibit16` — legitimate: `cc_partial_le_norm`
  (`SobolevScale/IteratedCovGradHsJetBound.lean:165–180`, PUBLIC, at HEAD
  since 2026-07-24, weight exactly `(1+λ)^σ`) is verbatim the dispatched
  JOINT-BESSEL shape — 273 lines above the private `mode_le_jet` the panel-3
  scout cited as sole near-producer; `weight_sum_le_normSq`
  (`TensorHsInterpolationLimit.lean:210`) is the general `tensorHs` form (not
  in the ShortTime import closure).  The scout's miss was real: even
  adversarial scouts over-count missingness — the executor-side
  re-sweep-before-writing rule is load-bearing and stays in every dispatch.
- `seed-mass` — statement/route/no-gate/consumability all confirmed: `g_bg`
  is a bound binder (the rung instantiates `g_bg := g₀` per IsLowSolve's
  pinned-background design, `UnifClassBounds.lean:402–406`); every hypothesis
  is a verbatim IsLowSolve field; the `ha_super` gate is honestly traded for
  the `Continuous coreN` field (downstream-satisfiable); arbitrary-`(n,F)` is
  strictly stronger than the high-reg model's shape and feeds
  `two_mul_sum_sameScale_le_sqrt` → the `seed·√E_σ` slot exactly as the
  high-reg closure does.  Consumer-side residuals = precisely №157's two
  interface variants + a trivial ℕ-cast exponent bridge, all Brick C.

**Caveats recorded (none refuting).**
1. Ledger tables' "top state order" column prints the sup-factor order on the
   `i < q−1` rows (data windows can exceed it while staying `≤ q+1`) — same
   convention note as №157; consequences unaffected.
2. Stale private docstring: `a1Arm1` still opens "Same mixed Hölder choice as
   `a1Arm0`" — true in v2, false after v3.  Fix on next touch of the file.
3. №158's "sharper `range (q+1)` would have been UNPROVABLE at `q = 0`" is an
   overstatement — a `q = 0` case split would prove it; what fails is only
   the uniform per-slot proof.  The landed spelling's actual claim
   (unconditional truth) is correct.
4. `lowReg_force_smooth` moved `:127 → ~:230` (seed-mass insertion); the
   Brick B executor was notified mid-flight.  Also noted for Brick C:
   `lowRegSeedMass`'s `𝒩(0)` is the same zero subtype element
   (`zero_mem_lowerState g₀ 1 …`) that IsLowSolve's `D`-field bounds
   (`UnifClassBounds.lean:452–454`) — the two seed handles compose without
   transport.

**State.**  Rung 3 = Brick A ✓ → B (in flight, reports as №160) → C.
Machinery ≈**71%** (per №158's own audit, held).  (N) **0%**;
`lowreg_loMass` **0%**; HCG ≈ **3%**; counter **1/3**.

---

## №160 (executor, 2026-08-05) — BRICK B LANDED: the forcing-realization layer
## `ShortTime/LowRegForceArms.lean`; all six links closed, `symmS 0` dissolved

**All six scout-verified links landed, none refused.**  New file
`ShortTime/LowRegForceArms.lean` (429 lines), ten public declarations, no
`sorry`, no new `maxHeartbeats`, no read-only other-lane file touched.  The file
moves **no estimate**: it is pure translation between the Galerkin ODE's forcing
coordinate and the objects the per-index ladders bound.

**(a) Trajectory-in-core.**  `galCoreRep g₀ R S c :=
(min 1 (R/‖galLowView g₀ 1 (finiteEigenComboHs g₀ S c 3)‖)) • finiteEigenCombo g₀ S c`
is the named smooth representative; `galCoreRep_eq` identifies its embedding with
`galTameStateC g₀ 1 R S c` (one `rw` chain: `smoothCcToTensorHs_smul`,
`finiteEigenComboHs_eq`, then `rfl` on `galTameStateC`); `galCoreRep_ball` is the
state-ball bound read through it; `galState_core` is the `smoothCore` membership.
No density or continuity input — the representative is exhibited, not chosen.

**(b) Eval.**  `galN_eval`: `lowRegN g₀ g₀ hR hδ hreal ⟨galTameStateC …, …⟩ =
deTurckSmoothN g₀ g₀ 1 (symmS g₀ (galCoreRep …)) hδ (galRepFib …)`.  Route =
`Subtype.ext (galCoreRep_eq).symm` then `lowRegN_on_smooth` — literally
`lowRegSeedMass`'s pattern at a nonzero state, as №158 predicted.

**(c) Arm reach.**  `galArmId`: `𝒩(state) − 𝒩(0) = smoothCcToTensorHs g₀ 1
(A.a2 T + A.a1 T)` with `T = symmS g₀ (galCoreRep …)`,
`A = lowBaseData g₀ g₀ T hδ (galRepFib …) (lowregFibZero …)`.  Three-step `calc`:
`galN_eval` + `nZero_eq_static` + `← deTurckSmoothN_zero` to reach the smooth
pair; `deTurckSmoothN_sub_eq_…remainderSub`; `congrArg _ (lowData_split …).1`.
`galArmCap` carries the `C2` fibre cap with the constant `K·δ/(1−δ)²` hoisted
**outside** `∀ S c` — hence mode-set-free, hence Galerkin-level-free — stated at
`riemannianFiberNormSq g₀ (2+2) 2`, i.e. verbatim `a2PerIdxLin`'s `hfib` binder.

**(d) Hypothesis transport (JOINT-REP).**  `galRepFib` (the `hδg` slot) and
`lowregFibZero` (the `hδZ` slot) are the two named certificates; symmetry is
`ccTensorBilin_symmS_symm` consumed inline (unconditional, no binder cost); the
δ-range and `Continuous coreN` are taken as binders.  **Statement discipline
held**: every lemma takes IsLowSolve-grade inputs directly (`δ < 1`, `0 ≤ δ`,
`δ ≤ 1/3`, `hreal` at `P`, `Continuous (coreN g₀ g₀ hδ (lowregRealRad …))`);
`lowreg_proj_tendsto` is not used anywhere.  Constants and certificates precede
the trajectory data `(S, c)`.  Background pinned to `g₀` (self-background),
matching IsLowSolve, `lowData_split g₀ g₀`, and `a2PerIdxLin`'s `lowBaseData g g`.

**Consumer endpoint.**  `galForceArm`: at the six-number / `lowregNfun` level,
`galTameForce g₀ 1 (lowregStateRad_pos …).le (lowregNfun g₀ g₀ hδ …) S c i =
if i ∈ S then (𝒩(0)).coeff i + (smoothCcToTensorHs g₀ 1 (A.a2 T + A.a1 T)).coeff i
else 0`.  The `galTameForce` head is **syntactically** the term
`lowregGalSol`'s ODE conclusion carries (`LowRegGalerkinSol.lean:127–130`) once
`g_bg := g₀`, `S := eigenIdxFinset g₀ N`, `c := U N t`, so Brick C can `rw` with
it directly.  The zero-state element is the same `⟨0, zero_mem_lowerState g₀ 1
(lowregStateRad_pos …).le⟩` that `lowRegSeedMass` bounds and IsLowSolve's
`D`-field bounds — the two seed handles compose with no transport, as №159 noted.

**`symmS 0` was a false wall (over-count exhibit seventeen — self-caught).**
The apparent obstruction: `𝒩(0)` evaluates through `coreN` at
`symmS g₀ (coreRep …)`, while `lowData_split`'s seed is the *literal* zero
tensor — seemingly forcing a new `symmS_zero` in the upstream
`CovGrad/RicciDeTurckSectionDifference.lean`, a large-cone edit.  It is
unnecessary: `nZero_eq_static` (`UnifNZeroBound.lean:249`) already crosses that
gap onto `smoothCcToTensorHs g₀ 1 (deTurckRHSSection g₀ g₀)`, and
`deTurckSmoothN_zero` (:229) turns that back into `deTurckSmoothN g₀ g₀ 1 0`.
Same file also already holds `smoothCcToTensorHs_zero` (:169) and
`zero_mem_smoothCore` (:176), so `lowRegSeedMass`'s open-coded `hzero_embed`
need not have been open-coded.  **Rule reinforced**: grep `UnifNZeroBound.lean`
before writing anything about the zero state.  No upstream file was touched.

**Design decisions (recorded in `LowRegForceArms.md`).**  New file rather than an
extension of `LowRegSmoothBridge.lean`: the bridge file would stay under the size
limit, but the new content needs `GalerkinTameSol`, `UnifNZeroBound` and
`DeTurckRemainderLowBaseAction` in its closure, which would land on the bridge's
three existing consumers for no benefit.  General `lowRegN`-level statements
(arbitrary `R`, `hreal` at `R`) plus one six-number specialization — the
`nZero_unif` / `nZero_lowregNfun` pattern — because only the specialized head
matches `lowregGalSol` syntactically.  The `lowBaseData` slot is written with the
ambient `hδ : δ < 1`; the ladders write `lt_of_le_of_lt hδ3 (by norm_num)` there,
and the two are definitionally equal — checked with a throwaway `rfl` `example`
(`lowBaseData … h … = lowBaseData … h' …`), which elaborated; probe removed, fact
recorded in the module docstring.  So **Brick C needs no transport lemma**.
One local iteration only: `galForceArm`'s `if i ∈ S` needs
`open scoped Classical in`, the same idiom `galTameForce` itself uses.

**Verification.**  Focused checks green on `LowRegForceArms.lean` and
`ScratchIdentCensus.lean`; targeted builds green for
`+…ShortTime.LowRegForceArms` and `+…ShortTime.ScratchIdentCensus`
("Build completed successfully").  Census: all ten new declarations —
`galCoreRep`, `galCoreRep_eq`, `galCoreRep_ball`, `galState_core`, `galRepFib`,
`lowregFibZero`, `galN_eval`, `galArmId`, `galArmCap`, `galForceArm` — report
`[propext, Classical.choice, Quot.sound]`; **zero occurrences of `sorryAx` in the
census output**.  Claims released.

**Honest denominators.**  Brick B is ≈**25%** of rung 3 by effort and ≈**0%** of
its mathematics — ten thin translation lemmas, not one estimate.  **Rung 3: still
0% stated**; Brick C carries the closure statement, the cross-scale pairing, the
`L¹_t` Grönwall and adapter H.  `lowreg_loMass`: theorem **0%**; dedicated
machinery ≈**72%** (+1pp on №158's 71%, justified narrowly: the ODE↔ladder
translation layer is a named prerequisite of the closure and now exists
end-to-end with no gap; it prices nothing, so no more than a point).  `(N)`:
theorem **0%**.  Whole HCG ≈ **3%**.  Route-error counter **1/3**, unchanged —
the single `Decidable` fix was a normal local iteration, not a route error.

**Next (Brick C, spec in №157 + №159).**  State the rung-3 closure at `k = 3`,
`q = 2` on `lowregGalSol`'s trajectory at `g_bg := g₀`.  `obtain` once, outside
`∀ N` and `∀ t`: `galArmCap` (the `hfib` constant `Cδ`), `lowRegSeedMass` (the
seed mass, arbitrary `(n, F)`), `a2PerIdxLin` and `a1PerIdxLin` (v3, `C₀`
re-split).  Then per `(N, t)` apply `galForceArm` at `S := eigenIdxFinset g₀ N`,
`c := U N t`, bridge jets↔`H^n` with `hsJet_le` / `hs_le_jet`, pair via
`two_mul_sum_ladder_le`, and thread adapter H in №155's widened form.  The two
interface extensions assigned in №157 are still unwritten and belong here:
`two_mul_sum_ladder_le` with an additive `+γ` (one extra Young), and the Grönwall
bound with a `seed²/4 + c₀` additive slot (same shape as the existing seed term).

---

## №161 (planner, 2026-08-05) — BRICK B ACCEPTED (panel 2×CONFIRMED); the
## Brick-C walk REFUTED the "two variants + casts" bar: TWO pre-dispatch
## breakers found (JOINT-KSCOPE, JOINT-L1BUDGET); JOINT-RETR DISSOLVES;
## Brick C dispatched amended

**Acceptance instrument.**  Fifth panel (run `wf_8b0b48be-d44`, 3 read-only
verifiers): `endpoint-syntax` CONFIRMED, `cap-transport` CONFIRMED,
`brickC-walk` REFUTED-the-bar (constructively — every gap named with a fix).

**Brick B ACCEPTED.**  `galForceArm`'s head verified character-identical to
`lowregGalSol`'s ODE forcing term (per-slot audit incl. the `hR` proof term;
`rw` fires); the `lowBaseData` two-spelling transport is sound by definitional
proof irrelevance (all differing slots are Props); `galArmCap`'s `Cδ` is
hoisted before `∀ S c` with witness `K·(δ/(1−δ)²)` from `lowData_split` —
genuinely per-datum, and STRICTLY STRONGER than `a2PerIdxLin`'s per-`T` cap
(uniform over the trajectory — what makes the Grönwall constant time- and
N-uniform); exhibit 17 legitimate; zero `lowreg_proj_tendsto` hits; the
`else 0` branch is inert for the engine.  Consumer seams recorded: seed-lane
`lowregNfun` vs `lowRegN` spelling closes by `exact` (delta-unfold), NOT `rw`;
one `add_comm` in `hsplit`; apply `galArmCap`/`galRepFib` by `exact`/defeq at
the two benign defeq seams (`δ<1` Prop slot; `4 2` vs `(2+2) 2` indices).

**The walk's two breakers (both pre-dispatch, neither scored — found by
scouting, not landed).**
- **JOINT-KSCOPE** (certain, cheap): `galerkin_energy_l1_bound` takes
  `hclosure : ∀ N k, …` with ONE `Cδ < 2` shared over all `k`
  (`GalerkinParabolicEnergy.lean:502, 515–522`), and every sibling engine in
  the file is likewise ∀k.  The rung produces the closure at ONE scale
  (adapter H's prefactor `Cq(k−1)` grows with `k`; ∀k is underivable at
  `a = 1` — the ∀k engines are a high-reg artifact where supercriticality
  gave `k`-free constants).  Fix: a SINGLE-SCALE `L¹`-Grönwall variant — the
  existing proof is per-`k` independent, so this is a ~40-line restatement;
  fold the `c₀` additive slot into it.  A THIRD interface variant, now
  assigned.
- **JOINT-L1BUDGET** (certain, architectural-but-honest): the engine's
  `(A, S, Sbd)` inputs need the a-priori N-uniform `∫₀^T E₃(U_N) ≤ B₃²` —
  №157's rider mechanism (`A(t) = C(1+E₃(t)) ∈ L¹_t`) consumes it.  Its only
  designed producer is PSTOP §6.1(ii)'s projected-MR replay
  (`‖U_N‖_{L²_tH³} ≤ B₃`), connected to the ODE trajectory only through
  JOINT-IDENT (deferred to Fatou) and itself not yet Lean-instantiated.
  RULING: rung 3 takes **`hL2H3`** (in the `S`-primitive form matching
  `hSderiv`/`hSbd`) as an EXPLICIT honest-input hypothesis; its discharge —
  projected-MR §6.1(ii) + the identification, or a scale-2 pre-rung with an
  `∫E₃` export — is hereby REGISTERED as a named obligation (honest-input
  audit pattern; consumers must not multiply against it silently).  Also
  noted for rungs 4–5 (outside C's scope): the engine exports only
  `sup_t E_k`, not `∫E_{k+1}` — a dissipation-export variant will be needed.
- **JOINT-RETR DISSOLVES** for the closure: the retraction scalar
  `min 1 (R/‖·‖) ∈ [0,1]` only SHRINKS jets (`symmS_smul` public), so
  `jets_n(T) ≤ C·√E_n(raw c)` unconditionally via
  `finiteEigenCombo_spectral_normSq` — no first-exit/ball hypothesis in the
  closure.  (`galTameForce_eq` remains a Fatou-stage item only.)
- Seams (a) mass↔jets (directions right: `cc_partial_le_norm` +
  `hs_le_jet`), (c) weight convention (`lambda_mul_tensorSobolevWeight`
  converts the ODE to the engine's derivative shape verbatim), (d)
  ε-arithmetic (2ε sufficient; the C₀ Young IS the middle Young, no 3ε),
  (e) seed (n:=3, F:=eigenIdxFinset; same subtype element) — ALL CLOSE.

**Small producers budgeted into C** (walk items): public re-export of the
private `symmS_jet_le` (`ShortTime/LowRegCoeffJets.lean:149–173`; public
ingredients named), `ccTensorToHs` additivity for the `a2+a1` split, the
`tensorHsInclusion`-norm ↔ `ccTensorToHs`-at-2 bridge for `jet₂`, FTC
construction of `S N` from continuous `E₃` (`galerkinEnergy_continuousOn`
exists), `hDim : finrank ℝ E = 3` threading.

**State.**  Rung 3 = A ✓ B ✓ → C (in flight, reports as №162).  Machinery
≈**72%**.  (N) **0%**; `lowreg_loMass` **0%**; HCG ≈ **3%**; counter **1/3**.
Standing user-side reminder: the whole campaign delta (five-plus sessions of
verified work incl. every load-bearing untracked file) remains uncommitted —
checkpoint commit recommended before C lands.

---

## №162 (executor, 2026-08-05) — BRICK C PARTIAL: the four interface/producer
## bricks landed (parts 1a, 1b, 1c, 4); **the closure (part 3) and the endpoint
## statement (part 2) did NOT land**.  Rung 3 remains **0% stated**.  Shape
## check run analytically and **PASSED**

**LEAD WITH THE FAILURE.**  The rung-3 closure — the mathematics of Brick C —
was **not attempted in Lean**, and the endpoint `∃ Φ₃, ∀ N, ∀ t ∈ Icc 0 T,
E₃(U N t) ≤ Φ₃` is **not stated**.  Rung 3 is therefore still **0% stated, 0%
proved**; it is not "stated with `hL2H3` + sorry".  No `sorry` was written and
no half-edited file was left.  The stop was a budget stop at a part boundary
(the option №161's dispatch explicitly allows), not a mathematical obstruction:
no missing API was found, and the route is now *more* settled than at dispatch
(see the shape check below).

**Why part 2 was left unwritten deliberately.**  Adapter H in №155's widened
form has to be stated about the constants that actually occur, and that
inventory is fixed only by part 3's regrouping.  Writing the statement first
would have pinned an interface before knowing what it must mention, and a
theorem whose only content is turning the goal into fresh hypotheses is the
adapter antipattern the project rules forbid.  The honest inputs it will carry
are nevertheless now fixed and realized in Lean: IsLowSolve-grade certificates,
`hDim`, adapter H, and `hL2H3` in the primitive form `galRiderBound` consumes.

**Landed (all sorry-free, census-clean, targeted builds green).**

- **Part 1a — JOINT-KSCOPE fixed.**  `energy_l1_single` (ODE level) and
  `galerkin_l1_single` (Galerkin level) in
  `HeatSemigroup/GalerkinParabolicEnergy.lean`: the closure at ONE scale, with
  a merely nonnegative `Yhi` for the scale above (only the sign of the
  discarded dissipation is used, so `hc : 0 ≤ c` suffices) and — new — an
  additive `c₀`, which lands in the Grönwall `ε` slot beside `seed²/4`.  It is
  a fresh ODE-level proof, not an instantiation: the `if k = 0` collapse does
  reduce single-scale to `energy_hier_l1_bound`, but `c₀` folds into neither
  the seed slot (`seed·√Y + c₀ ≤ seed'·√Y` fails at `Y = 0`) nor the `A` slot.
- **Part 1b.**  `two_sum_ladder_add_le` in `Sobolev/Tensor/`
  `CrossScaleCauchySchwarz.lean`: the ladder with `+γ`, absorbed by one extra
  Young `2γ√E_{σ+1} ≤ ε·E_{σ+1} + γ²/ε` at the **same** `ε` (no third `ε`, per
  seam (d)).  Dissipation constant `2α + 2ε`; new additive slot `γ²/ε`.
- **Part 1c.**  New file `ShortTime/LowRegRungThree.lean` (three public
  declarations): `symmS_jet_le` (public form of the private copy), and the two
  jet bounds on the trajectory representative — `galRepJet_le`, the
  **retraction-shrink route** (`∑_{j≤n}‖∇ʲ(symmS rep)‖ ≤ C·√Eₙ` of the RAW
  coefficient family, unconditionally, no ball hypothesis — JOINT-RETR's
  dissolution realized), and `galRepJet_rad` (`∑_{j≤2}‖·‖ ≤ C·R` off the state
  ball).
- **Part 4 — the `L¹` rider.**  `galRiderBound`, next to the engine: the
  coefficient is the concrete `Crid·(1 + E_σ)`, its primitive `Crid·(t+P N t)`,
  the shared bound `Crid·(T+B)`.  `P` is `hL2H3` in primitive form — carried as
  an explicit honest input, **not discharged**, as №161 ruled.  Stated at
  general `(σ, sseq)` so rungs 4–5 reuse it.

**SHAPE CHECK: PASSED (analytic).**  Instantiating `a2PerIdxLin`/`a1PerIdxLin`
at `q = 0,1,2` against the two new jet bounds, the ONLY slots reaching `E₄` are
the four allowed: `Cq·Cδ*` (a₂ top at `q=2`), `K_R·R` (a₂ `i=q`), `K_R^{a₁}·R`
(a₁ `C₁` group at `i=q−1`), `2ε` (the two Youngs).  Every other slot carries at
most `Jt 4 ≤ C√E₃` with coefficient factors `(1+Jt 4)`, `(1+Jt 3)`, so it lands
in `β√E₃` with `β = C(1+√E₃)`, whence middle coefficient `β²/ε ≤ C(1+E₃)` —
exactly `galRiderBound`'s slot.  **JOINT-A1TOP did not trigger.**  Checked
specifically that no slot has the form `(1+Jt 4)²·Jt 4` (which would give
`β² ⊇ C·E₃²` and blow the `∫E₃ ≤ B₃²` budget): the two `(1+Jt 4)²` slots of the
`C₀` group both multiply `Jt 3`, a class quantity — **№157's `C₀` re-split is
what makes this work**, confirmed at the pricing level.

**Design decisions (recorded in `LowRegRungThree.md`).**  `symmS_jet_le` was
rebuilt from its two public ingredients rather than un-`private`-d in
`LowRegCoeffJets.lean` (2711 lines), which would have landed a heavy module on
a light consumer.  Known small duplication recorded, with the fix named: the
canonical home for both copies is the `CovGrad/RicciDeTurckSectionDifference`
layer next to `iteratedCovGrad_symmS_eq`.  The FTC construction budgeted in
№161 turned out **unnecessary**: with `hL2H3` supplied in primitive form the
primitive is the hypothesis, and only the rider's primitive `Crid·(t+P)` has to
be built.  `ccTensorToHs` additivity is likewise not needed as a new lemma —
`iteratedCovGrad_add` splits `a₂+a₁` at the jet level, one step later.

**What part 3 now costs.**  Per `(N,t)`: `rw [galForceArm]`; mass↔jets by
`cc_partial_le_norm` at `σ=2` + `hs_le_jet g₀ 2 2` + `iteratedCovGrad_add`;
SIX ladder instantiations each regrouped into an explicit `(α,β,γ)` triple via
`galRepJet_le`/`galRepJet_rad`; `two_sum_ladder_add_le` at `σ=3` with
`lowRegSeedMass` (`n:=3`); then `galRiderBound`.  Large but routine — a long
session, not a hard one.  One unwritten micro-bridge: `√(∑ aⱼ²) ≤ ∑ aⱼ`, to
convert the jet shape of `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs`
into the ladders' `√(∑ ‖∇ʲ‖²)`.

**Verification.**  Focused checks green on all three edited/new Lean files;
targeted builds green for `+…HeatSemigroup.GalerkinParabolicEnergy`,
`+…Sobolev.Tensor.CrossScaleCauchySchwarz`, `+…ShortTime.LowRegRungThree`.
Census: `energy_l1_single`, `galerkin_l1_single`, `two_sum_ladder_add_le`,
`galRiderBound` (in `DeTurck/ScratchC01Census.lean`) and `symmS_jet_le`,
`galRepJet_le`, `galRepJet_rad` (in `ShortTime/ScratchIdentCensus.lean`) all
report `[propext, Classical.choice, Quot.sound]`; zero `sorryAx`.  Claims
released.  No read-only other-lane file touched; no new `maxHeartbeats`; no
file over 3000 lines.

**Honest denominators.**  Rung 3: **0% stated, 0% proved** — unchanged from
№161.  Brick C: parts 1a/1b/1c/4 of five landed, ≈**35% by effort** and ≈**0%
of its mathematics** (the closure IS the mathematics).  `lowreg_loMass`:
theorem **0%**; dedicated machinery ≈**74%** (+2pp on №161's 72%: the two
interface variants were named blockers of the closure — no closure could be
stated without them — and the rider plus the two jet bounds are its remaining
non-arithmetic prerequisites; they price nothing, so no more).  Rung 3 is one
of J4's rungs 3–5; J1/J2/J6/J7 and the Fatou glue are untouched.  `(N)`:
theorem **0%**.  Whole HCG ≈ **3%**.  Route-error counter **1/3**, unchanged.

**Next.**  Part 3 (the closure) then part 2 (the endpoint), in that order, in
`LowRegRungThree.lean`; the constant inventory the endpoint's adapter H must
mention is produced by part 3.  Fatou stage (JOINT-IDENT + `galTameForce_eq`
wiring, №155/№161) remains after the rung.  Standing user-side reminder from
№161 still open: the campaign delta is uncommitted.

---

## №163 (planner, 2026-08-05) — C-1 PROVISIONALLY ACCEPTED (panel deferred to
## rung landing); statement-last ordering RATIFIED; C-2 dispatched

**Provisional acceptance, with rationale for deferring the panel.**  C-1's
four landed parts (the two engine variants, the three producers,
`galRiderBound`) are interface work whose fitness is tested BY the very next
brick: if the single-scale engine's `c₀` slot or the ladder variant's shape
is wrong, part 3 wedges inside the executor session and reports — there is
no window in which a wrong statement gets silently consumed downstream
(the failure mode the panels exist to prevent).  The adversarial panel
therefore runs ONCE on the landed rung (C-2 + C-1 together), not twice.
The executor's analytic shape check replicated the №161 walk's own
regrouping (same whitelist, same `β = C(1+√E₃)` middle coefficient, and the
specific `(1+Jt4)²·Jt4` hazard verified absent — №157's `C₀` re-split
confirmed at the pricing level); that arithmetic gets its independent check
at the rung panel.

**Statement-last ordering RATIFIED**: part 2 after part 3 is the correct
reading of the anti-adapter rule — the endpoint's adapter-H hypothesis must
name the constants that actually occur, and that inventory exists only
after the regrouping.  Budget stop at a part boundary with no `sorry` and
no half-edit is the intended checkpoint behavior.

**Two dissolved producers recorded** (FTC — the primitive IS the `hL2H3`
hypothesis in primitive form; `ccTensorToHs` additivity —
`iteratedCovGrad_add` splits one step later): both were priced in №161 and
came out free; noted so the pricing ledger stays honest in both directions.

**C-2 dispatched** (reports as №164): parts 3 + 2 in `LowRegRungThree.lean`,
per №162's own "Next" with the recorded seam guidance (exact-not-rw at the
defeq seams, `add_comm`, seed-lane `exact`, the slot-destination map kept in
the docstring and confirmed in Lean as it lands); the one named micro-bridge
(`√(∑aⱼ²) ≤ ∑aⱼ`) to be swept against the public a₂-file helpers before
writing (exhibit discipline — `sqrtFinSum` is nearby).

**State.**  Rung 3 **0% stated / 0% proved**; machinery ≈**74%** (№162's
justification accepted: the two variants were hard blockers).  (N) **0%**;
`lowreg_loMass` **0%**; HCG ≈ **3%**; counter **1/3**.

---

## №164 (executor, 2026-08-05) — **RUNG 3 IS PROVED.**  Parts 3 and 2 both
## landed sorry-free: the closure, then the endpoint `lowregRung3`.  The shape
## check is now a Lean theorem, not an analytic argument

**Result.**  `lowregRung3` (`ShortTime/LowRegRungThree.lean`) is stated and
proved, `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.  This is the
first of J4's rungs 3–5.  Nothing was weakened to get there: the only inputs
beyond the `IsLowSolve`-grade certificates are `hDim`, the registered honest
input `hL2H3` in `galRiderBound`'s primitive form, and **one** numerical
absorption inequality naming the constants the theorem itself produces.

**The endpoint (compressed).**

```
lowregRung3 (hDim : finrank ℝ E = 3) (g₀) {δ Ctop B1 ρ P T B}
  (hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore)      -- IsLowSolve fields, destructured once
  {U} (hUcont hUderiv hUinit)                   -- the order-one Galerkin trajectory
  {Pr} (hPr0 hPrnn hPrcont hPrderiv hPrbd) :    -- hL2H3, primitive form
  ∃ Ctop₂ Kr2 Kr1 Cδ, 0 ≤ … ∧
    ∀ {ε}, 0 < ε →
      Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1        -- adapter H, R = lowregStateRad Ctop B1 ρ P
      → ∃ Φ, ∀ N, ∀ t ∈ Icc 0 T,
          galerkinEnergy (eigenIdxFinset g₀ N) (U N) 3 t ≤ Φ
```

Adapter H is exactly the four whitelist contributions: `Cq·Cδ*` as `Ctop₂·Cδ`,
`K_R·R` as `Kr2·R`, `K_R^{a₁}·R` as `Kr1·R`, and the two Youngs as the single
`ε` (the engine's gate is `Cδ_eng = 2α + 2ε < 2`, so the `< 1` normalization is
the natural one).  The constants are the theorem's own outputs, so nothing
free-floating is asserted about them.

**SLOT MAP: CONFIRMED IN LEAN.**  `armLadderAbs` (private, same file) *is* the
slot map — from abstract handles `jet₅ ≤ X`, `jet₄ ≤ Y`, `jet_{≤3} ≤ Z` it
proves `∑_{q≤2}(‖∇^q a₂T‖+‖∇^q a₁T‖) ≤ (Ctop·Cδ + Kr2·Z + Kr1·Z)·X +
Kmid·(1+Cδ)·(1+Y)²(1+Z)²`.  Only three constants multiply `X`, and they are the
three whitelist slots; the remaining seventeen Leibniz slots of the six
per-index instantiations all land in the middle bucket.  **No foreign constant
reached `E₄`; JOINT-A1TOP did not trigger.**  The load-bearing discipline —
newly identified while writing the proof, and worth recording — is that the
window `jet₃` (`Finset.range 3`) must ALWAYS be priced by the class radius `Z`,
never by `Y`: pricing it by `Y` makes the `a₁` `C₀` slots
`K₀ i·(1+jet₄)²·jet₃` cubic in `√E₃`, i.e. `β² ⊇ E₃²`, outside the `∫E₃ ≤ B`
budget.  With that discipline every slot is at most quadratic in `Y`, which is
precisely what `galRiderBound` absorbs (`β = Kmid(2+√E₃)`,
`β²/ε ≤ 6Kmid²/ε·(1+E₃)`; `Cmid = 0`, `Crid = 6Kmid²/ε`, `c₀ = Kmid²/ε`,
`seed = 2·Cseed 3`, `B0 = 0`).

**New public declarations.**  `galArmVec` (def — the seed-subtracted forcing arm
of a retracted Galerkin state, definitionally `galForceArm`'s arm term, so the
`fd`/`fs` split closes by `exact add_comm _ _` after `if_pos`), `galArmMass`
(the trajectory ladder input: `√(∑_{i∈F} w_i²·(arm)²) ≤ (Ctop·Cδ + Kr2·R +
Kr1·R)·√E₄ + Kmid·(1+√E₃)²`), `lowregRung3`.  Private: `jetSqrtLe`,
`jetWinMono`, `mul3Le`, `armLadderAbs`.

**The micro-bridge was already in the tree**, as №163 guessed: `√(∑aⱼ²) ≤ ∑aⱼ`
is `sqrtFinSum` (public, `LowRegA2PerIndex`) composed with `Real.sqrt_sq`.
Nothing new was written for it.  The three predicted seams all behaved: the
`δ<1` Prop slot and the `4 2` vs `(2+2) 2` indices closed by `exact`, the
seed-lane `lowregNfun`-vs-`lowRegN` spelling by `simpa only [Nat.cast_ofNat]
using …` (delta in the final `exact`), and the `hsplit` needed exactly one
`add_comm`.

**Two durable Lean lessons** (recorded in `LowRegRungThree.md`).  (i) `set`
bodies poison `linarith`: the jet windows and the middle bucket were introduced
with `set`, and the arithmetic tactics then burned their whole heartbeat budget
in `isDefEq`/`whnf` unfolding the let-values back into `iteratedCovGrad` sums.
`clear_value` on all of them — plus `clear` of the defining equations, which are
ℝ-equalities and therefore consumed by `linarith` — removed two hard timeouts
outright.  (ii) `nlinarith` where `linarith` suffices is a timeout: all fifteen
arithmetic steps are linear over the monomial basis, so supplying the monomial
nonnegativities and calling `linarith` is instant where `nlinarith` with the
same hints times out.  Also: never `norm_num` a per-index bound — it unfolds
`iteratedCovGrad` into `covGrad` chains and destroys the window shape; reduce
the outer Leibniz sums only, per hypothesis (`range 2` is an index set at
`q = 2` but a *window* at `q = 0,1`, so one shared simp set corrupts the latter).

**Verification.**  Focused check green after each part; targeted builds green for
`+…ShortTime.LowRegRungThree` and `+…ShortTime.ScratchIdentCensus`.  Census
extended with `galArmVec`, `galArmMass`, `lowregRung3`; all three report
`[propext, Classical.choice, Quot.sound]`, and the whole census run contains
zero `sorryAx`.  Files touched: `ShortTime/LowRegRungThree.lean` (224 → 919
lines), `ShortTime/LowRegRungThree.md`, `ShortTime/ScratchIdentCensus.lean`.  No
read-only other-lane file touched; no new `maxHeartbeats`; no file over 3000
lines; claims released.

**Honest denominators.**  Rung 3: **stated and proved, 100%** — but it is ONE of
J4's rungs 3–5, and rungs 4–5 are **0%** (they need the general-`k` regrouping
and, additionally, a dissipation-export engine variant, since
`galerkin_l1_single` exports only `sup_t E_k`, not `∫E_{k+1}`).  J1/J2/J6/J7:
untouched.  The `hL2H3` discharge (PSTOP §6.1(ii) projected-MR replay + the
identification): **0%**, still a registered obligation.  Fatou glue (JOINT-IDENT
+ `galTameForce_eq`): **0%**.  `lowreg_loMass`: theorem **0%** — the rung is
machinery, and the theorem is not stated.  Dedicated machinery ≈**80%** (+6pp on
№163's 74%: the closure was the single largest unbuilt piece of the rung stack
and it is now a proved theorem, but rungs 4–5 and the Fatou stage are the
remaining fifth and they are not small).  `(N)`: theorem **0%**.  Whole HCG
≈ **3%**.  Route-error counter **1/3**, unchanged.

**Next.**  The Fatou stage per №155/№161 — JOINT-IDENT plus the
`galTameForce_eq` retraction-inertness wiring — is now the critical path, since
the rung supplies the `H²`-uniform bound that `galTameForce_eq` consumes.
Standing user-side reminder from №161/№162 still open: the whole campaign delta
remains uncommitted.

---

## №165 (planner, 2026-08-05) — RUNG 3 ACCEPTED (panel 2×CONFIRMED); the
## Fatou scout REFUTED №164's wiring and DISSOLVED JOINT-IDENT: ride the
## rung on the PROJECTED sequence directly; F1–F4 ladder adopted; F1 dispatched

**Acceptance instrument.**  Sixth panel (run `wf_e63ec78d-0f1`, 3 read-only
verifiers): `endpoint-statement` CONFIRMED, `slotmap-lean` CONFIRMED,
`fatou-scout` REFUTED-the-№164-handoff (constructively).

**Rung 3 ACCEPTED.**  Φ bound outside `∀N`, no N-leak in any binder;
adapter-H quantifiers usable (constants before the gate, ε consumer-picked,
Φ may depend on ε); Cδ is the δ-only fibre cap, Kr2/Kr1 multiply the class
radius exactly as PSTOP demands (ε-vs-2ε = recorded engine normalization,
strength-neutral); no circularity; σ-convention identical to
`lowreg_loMass`'s weights.  Slot map verified IN THE LEAN TEXT: all 19
PerIdxLin summands land at their claimed destinations, only the three
whitelist constants (+2ε) touch X, the `jet₃`-by-Z discipline holds at every
e-lemma, handles have no off-by-one, the middle term is genuinely linear in
`E₃` (`β² ≤ 6Kmid²(1+E₃)` via `2s ≤ 1+s²`).
- **GAP-ORDER registered** (panel caveat, not refuting): the ∃-constants
  are bound after the class parameters, so the statement alone does not
  express "K's fixed before R".  The proof's witnesses are verified
  class-parameter-free (only Cδ carries δ, and Cδ → 0 with δ) — a
  strengthened restatement hoisting the ∃ is mechanically available from
  the same proof when front 3 needs it.  Follow-up, not a defect.

**The Fatou re-architecture (scout finding, ADOPTED).**
- **KEY SIMPLIFICATION — JOINT-IDENT dissolves.**  `lowregRung3`'s
  trajectory `U` is universally quantified, so instantiate it AT THE
  PROJECTED SEQUENCE's mode coordinates
  `c N t i := perModeConv λᵢ (timeModeCoeff (fseq N) i) t`.  Then `hUinit`
  = `perModeConv_zero_left`, `hUcont` = `continuousOn_perModeConv_timeL2`
  (`PerModeL2.lean:138`), `hUderiv` = the package's a.e. Nemytskii conjunct
  + `perModeConv_timeL2_congr` + `perModeConv_hasDerivAt` — **no
  ODE-uniqueness; `galTamePerMode` and `lowregGalSol` drop off the critical
  path** (the M2 pair and the ODE construction remain sound banked API).
  Every link of the a.e. forcing identity exists and is named
  (conjuncts 2/3 + `spatialProj_coeff`/`projNfun` + `aeSetLift_coe_ae` +
  `projField_fixed` + `timeModeCoeff_eq_perModeConv_forcing`
  (`PointwiseSpectralCoordinate.lean:364–393`, PUBLIC, a-generic — named
  here to prevent exhibit 19) + `galTameForce_eq`).
- **№164's wiring claim REFUTED**: the rung does NOT feed
  `galTameForce_eq` — its `hc` (raw combo in the H² ball at
  `lowregStateRad`) is unrelated to the rung's Grönwall Φ; the true
  producer is package conjunct 2 (a.e. Duhamel ball at exactly that
  radius).  The rung's sole role in the stage is Fatou's `hbound`.
- **hL2H3 discharge = the same keystone** (PSTOP §6.1(ii) in Lean-ready
  form): `E₃(c) =ᵃᵉ ‖field‖²_{H³}` (`finiteEigenCombo_spectral_normSq` +
  the identity), `∫₀^T = ‖field‖²_{timeL2} ≤ ((1+T)R/4)²` via
  `norm_maxRegDuhamelSolField_zero_le` (`TameForcingFixedPoint.lean:518,
  893`) + conjunct 6; `Pr` by FTC from `galerkinEnergy_continuousOn`.
  F3 retroactively unconditionalizes the rung except adapter H.
- **GAP-ADAPTH registered**: nothing in the Fatou stage discharges the
  rung's absorption inequality — the stage endpoint stays conditional on
  it (honest input; discharge = a separate smallness audit of
  `lowregStateRad` vs the produced constants, producer-side, likely with
  GAP-ORDER's hoisted restatement).
- **σ-scope honesty**: the stage delivers the σ ≤ 3 instance + the hL2H3
  discharge ONLY.  Full `lowreg_loMass` (∀σ real) remains 0% and gated on
  rungs 4–5 (general-k regrouping + the dissipation-export engine variant).

**The F-ladder (ranked, adopted).**
- **F1 GAP-CERT** (dispatched now, reports №166): third in-place widening of
  `lowreg_proj_tendsto`/`lowreg_projMode_tendsto` — the package drops
  `hδ0`/`hδ3`/`hcore` (the `-,-,-` at `LowRegGalerkinIdent.lean:120–121`)
  and never exports `htame`/`hcont`/`B0`, yet `lowregRung3` and the
  `tame_lip_balls → hK` derivation need them AT THE PACKAGE'S constants
  (re-destructuring `hlo` gives incomparable witnesses).  Precedent: the
  J4-PREP widening; zero external consumers again (grep-confirmed by the
  scout).  Mechanical, short.
- **F2 FATOU-IDENT** (the keystone): `c N` satisfies the rung's
  `hUcont`/`hUderiv`/`hUinit`.  One serious session of ae-filter/Subtype
  bookkeeping; no new analysis.
- **F3 FATOU-L2H3** (half session): discharge `hL2H3` for `c` as above.
- **F4 FATOU-ASSEMBLE** (half session): σ-parametric glue mirroring
  `GalerkinLimitUniformMass.lean:1167–1210` (`fatou_sq_mass` + weight
  domination; `hconv` = `lowreg_projMode_tendsto` verbatim).

**State.**  Rung 3 **proved + accepted**.  Machinery ≈**80%**.  (N) **0%**;
`lowreg_loMass` **0%**; HCG ≈ **3%**; counter **1/3**.  Campaign delta still
uncommitted (user-side).


## №166 (executor, 2026-08-05) — F1 GAP-CERT DONE: both identification
## theorems now carry the nonlinearity certificates at their OWN constants;
## `lowregRung3`'s certificate block is fully instantiable from the package

**No failure to lead with.**  The widening landed exactly as №165 scoped it,
including the optional `htame`/`hcont`/`B0` half — nothing turned out to be
non-exportable.

**What was exported.**  Seven new ∃-binders in *both* `lowreg_proj_tendsto` and
`lowreg_projMode_tendsto`, inserted **between `hreal` and `fseq`** so that every
pre-existing binder keeps its relative position and the whole
`Tendsto … ∧ ∀ N …` body is byte-identical:

    (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1/3)
    (_hcore : Continuous (coreN g₀ g₀ hδ (lowregRealRad g₀ … hP.le hreal)))
    (B0 : ℝ) (_hB0 : 0 ≤ B0)
    (_hcont : Continuous (lowregNfun g₀ g₀ hδ hCtop hB1 hρ hP hreal))
    (_htame : three-arm estimate on lowerState g₀ 1 (lowregStateRad Ctop B1 ρ P))

All seven are **verbatim `IsLowSolve` fields at the bound constants** — no
derived facts, no new hypotheses.  `B0` had to become a bound real because it is
`_htame`'s middle-arm coefficient; it sits *after* `_hcore` rather than inside
the leading `(δ Ctop B1 ρ P : ℝ)` group precisely so that no existing binder
position moved.  The full compressed telescope is now

    ∃ δ Ctop B1 ρ P, hδ hCtop hB1 hρ hP hreal | _hδ0 _hδ3 _hcore B0 _hB0
      _hcont _htame | fseq, Tendsto ∧ [projMode: ∧ per-mode limit] ∧ ∀ N, ⟨6⟩

**What was NOT exported, and why it is not an obstruction.**  `D`, `hzero`
(`‖𝒩(0)‖ ≤ D`) and `hTτ` (the horizon cap `T ≤ lowregHorizon Ctop B0 B1 D ρ P`).
These are cleanly exportable by the *same* pattern — nothing blocks them; they
were outside F1's dispatch and no named consumer asks for them at the package's
constants (`lowRegSeedMass` carries its own seed bound; the horizon cap is
consumed inside this proof).  If F3's `hL2H3` discharge wants the cap at these
constants it is two more binders and two more names in the `obtain`/`refine`.

**Diff shape.**  Exactly as the J4-PREP precedent: the `-, -, -` at the `obtain`
became `hδ0, hδ3, hcore`; both `refine`s thread the seven items; the in-file
consumer (`lowreg_projMode_tendsto` destructuring `lowreg_proj_tendsto`) was
updated in step.  Same proof route, same witnesses, no new lemma.

**The one Lean wrinkle.**  Statement-only binders trip `unusedVariables`, so the
six proof-valued names are underscore-prefixed (`_hδ0`, `_hcore`, …) — the tree
already uses that idiom (`LowRegBgC0Pair.lean:671`).  Destructuring is
positional, so a consumer names them whatever it likes.  Also recorded in the
same-name `.md`: `coreN`/`lowregRealRad` resolve unqualified here (same
namespace, unlike `SmoothCcTensor`); `_htame` must be copied verbatim from
`IsLowSolve` in the `u.1`/`v.1` spelling; and `hcore` mentioning `hδ` as a
*term* is harmless because proof irrelevance is definitional, so the rung's own
`hδ` slot unifies.

**F2's gate is open.**  `lowregRung3`'s certificate block is
`hδ, hδ0, hδ3, hCtop, hB1, hρ, hP, hreal, hcore` — all nine are now handed out
by the package at one tuple of constants, and the rung's conclusion is stated at
`lowregStateRad Ctop B1 ρ P`, the same `R` the package's state and forcing balls
use.  So F2 owes **only** the trajectory block `hUcont`/`hUderiv`/`hUinit` for
`c N t i := perModeConv λᵢ (timeModeCoeff (fseq N) i) t`, plus F3's `Pr` block.
The `tame_lip_balls → hK` route likewise now has `_htame` + `B0` + `_hB0` at the
package's constants; the caller renormalizes into `(A·R, B, C)` exactly as this
file's own `hsingle` does at `:129–163` (`A := toNNReal (Ctop·lowregOuterRad/R)`,
`B := toNNReal B0`, `C := toNNReal B1`) — mechanical, no new mathematics.

**Verification (persisted).**  Focused check green **and warning-free**;
targeted build `+…ShortTime.LowRegGalerkinIdent` — "Build completed
successfully", zero errors; `ScratchIdentCensus.lean` prints
`[propext, Classical.choice, Quot.sound]` for all twenty censused declarations
including both widened theorems, **no `sorryAx`**.  Repo-wide grep re-confirmed
zero external Lean consumers of either theorem.

**One in-scope prose correction.**  `LowRegForceArms.lean`'s module docstring
said the arms take the certificates directly "rather than routing through
`lowreg_proj_tendsto`, whose export discards them" — this widening made that
false, so the sentence now records that the package re-exports them and that
re-destructuring `IsLowSolve` is the thing to avoid.  That file re-checks green.

**Honest denominators.**  F1 is a certificate **export**, not mathematics: it
discharges no proof obligation and is worth ≈**0pp** of machinery, which stays
at ≈**80%**.  Its entire value is removing the constant mismatch that would have
wedged F2.  Rung 3 **proved**; `lowreg_loMass` theorem **0%**; (N) **0%**;
HCG ≈ **3%**; counter **1/3**.  Campaign delta still uncommitted (user-side).

**Next.**  F2 FATOU-IDENT as №165 scoped it.

---

# THIS LEDGER IS CLOSED (№142–166).

Rolled 2026-08-05 at the 3000-line cap.  **The active ledger is
`UNIF_EXISTENCE_PLAN6.md`** (№167+; its header carries the state-at-rollover
summary, the F-ladder, and the registered honest inputs).  Do not append here.
