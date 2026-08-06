# `TameMarkWin.lean` — the marked arm calculus and the tame `L²` bridge

Companion note.  Status, route, what was verified, what failed, the exact
remaining frontier.

## Why this file exists

Executor report No. 138-executor (`ShortTime/UNIF_EXISTENCE_PLAN4.md`) built the
tame `L²` composition layer (`TameGridProd.lean`) and found the blocker one level
below it: every existing per-arm window is stated in the `∇P`-**capped**
currency, where the `∇P` factors have already been spent into
`shiftConst Λ (i+1)` — a constant whose `Λ`-degree grows with the order.  Feeding
`gridIntPull`/`gridIntGrad` needs a per-arm window with the factors still
EXPLICIT.

This module is that currency:

`HasMarkWin g₀ P X u K  ↔  ∀ i x, |∇ⁱX|²(x) ≤ K i · markGrid (bP x) u i`

with `markGrid` from `Analysis/Sobolev/MarkedTupleGrid.lean`.  A `u`-marked
monomial carries `u` explicit factors `|∇^cP|²`, `c ≥ 1`, at total weight
`≤ i + u`.  **No cap is spent anywhere in the calculus**, so the constants are
state-free; the single `∇P` cap is spent once, after integration.

## Contents

### The calculus (all sorry-free, axiom-clean)

| name | content |
| --- | --- |
| `HasMarkWin` | the invariant |
| `markFold` | the pointwise Leibniz fold; **the marks add**, at the unmarked fold constant `foldConst 0 0` |
| `mkOfBnd` | a state-free arm enters at `u = 0` |
| `mkOfWin` | an `F(P)`-type arm with the ordinary offset-`+1` window enters at `u = 0` — definitionally the same statement |
| `mkOfTop` | **the load-bearing bridge**: a `topSeparated` producer enters at `u = 1` |
| `mkApp`, `mkAdd`, `mkSub`, `mkSmul`, `mkNeg`, `mkMono`, `mkCongr`, `mkReindex`, `mkSlotExt`, `mkIter` | the calculus, mirroring `GradCapArms.lean` one-for-one (`mkIter` = the marked `capIter`, session 3) |

`mkOfTop` is why no arm has to be re-derived geometrically.  The tree's
`topSeparated` producers already present an order-one arm as

`Ktop·|∇^{i+1}P|² + Kc i·∑_{k<i} |∇^{i-k}P|²·grid(bP)(k+1)`,

i.e. as a sum of monomials each carrying an explicit state jet of order `≥ 1` at
total weight exactly `i + 1`.  That IS a once-marked window
(`Combinatorics.markOne_of_term`).  The same arm's ordinary `atgw bP (i+2)`
window is not: it also admits the bare constant and the unaccompanied top jet.

### The bridge out

| name | content |
| --- | --- |
| `gridIntHigh` | **the class-3 frontier — the only `sorry`** |
| `markMon` | the tame integral of ONE marked monomial (four-way dispatch) |
| `contGB`, `contGrid`, `contMk` | continuity of the state jets / grids / marked windows (private) |
| `markJet` | **the deliverable**: a twice-marked window integrates to `K n·(K₀ n·(1+Λ₁²))·(1 + ∑_{j<n+2}‖∇ʲP‖²)`, `K₀` state-free |
| `markJet0` | the `u = 0` end (session 3): an UNMARKED window is already tame, `K n·K₀ n·(1 + ∑_{j<n+2}‖∇ʲP‖²)`, **no `Λ₁` factor, no `sorryAx`** |

`markJet0` is a short consequence of `atgwToJet` at `w = 1`, because
`markGrid b 0 n = atgw b (n+1)` *definitionally*.  It is what the LINEAR summands
consume (`lc0RiemJet`), and it is why those summands come out of the marked
currency fully axiom-clean: they never reach `markMon`, hence never reach
`gridIntHigh`.  It is already a strict improvement on the tree's own radius-free
route for such a summand — `lc0Riem_perOrder_rf` lands on `range (i + 3)`, one
order over budget, whereas the unmarked marked-window route lands on
`range (i + 1)`.

`markMon`'s dispatch at `m = n + 1`, for a monomial
`|∇^{c₁}P|²·|∇^{c₂}P|²·∏_q |∇^{e q}P|²` with `c₁, c₂ ≥ 1`, `∑ e = k`,
`c₁ + c₂ + k ≤ m + 1`:

1. total weight `≤ m` — already inside the budget; `gridIntUnit` at the δ-anchor,
   **state-free constant, no `Λ₁` at all**;
2. total weight `m + 1` and a bare `∇P` factor (`c₁ = 1`, `c₂ = 1`, or some
   `e q = 1`) — `gridIntPull`, one power of `Λ₁²`;
3. total weight `m + 1`, `c₁, c₂ ≥ 2`, `k = 0` — `gridIntGrad`, one power of
   `Λ₁²`;
4. residual — `gridIntHigh`.

The marked structure is exactly what excludes the fifth possibility, a lone
`|∇^{m+1}P|²`, which is out of budget and cannot be tamed at all.

## The remaining frontier (one, precisely stated)

**SUPERSEDED by session 7 (2026-08-04): `gridIntHigh` is PROVED and this file
has no `sorry`.  The inventory below is still the correct description of the
case, and is kept for that reason.**

`gridIntHigh`, then `sorry`'d, with its inventory recorded in the docstring:
`c₁, c₂ ≥ 2`, tuple weight `k ≥ 1` with no entry equal to `1`, total weight
`m + 1` exactly.  Discarding the weight-`0` entries (each `≤ Λ₀ ≤ 1`), such a
monomial is `∏_{j≤q}|∇^{c_j}P|²` with `q ≥ 3`, every `c_j ≥ 2`, `∑ c_j = m+1`;
hence `m ≥ 5`, i.e. **tower order `i ≥ 4`**, and at the first order where it
occurs (`m = 5`, `i = 4`) the inventory is the SINGLE monomial `(2,2,2)`, i.e.
`∫ |∇²P|⁶`.

The estimate is true (three-point interpolation with weights
`c_j = α_j + θ_j·m`, `∑ α_j = ∑ θ_j = 1`, feasible exactly when `q ≥ 2`); what is
missing is an interpolation BETWEEN the two two-point Gagliardo–Nirenberg scales
the tree has (`P`-anchored and `∇P`-anchored).  Pure `∇P`-anchoring costs
`Λ₁^{2(q-1)}`; pure `P`-anchoring overshoots the derivative budget by one.  This
is a separate counted brick.

**Confirmation of the tower order (planner No. 139's mandated check).**
`PSTOP_PROPOSITION.md` §6.3 BUDGET CHECK: pairing at rung `k` costs
`‖𝒩(U)−𝒩(0)‖_{H^{k−1}}·‖U‖_{H^{k+1}}`, and the `H^{k−1}` factor is estimated
tower-directly by the towers' window "at `i = k−1`".  With the stopped rungs
`k = 3, 4, 5` (§6.1) the maximal consumed tower order is **`i* = 4`**.  Since
`i* ≥ 4`, class 3 STAYS on-path — but only barely, and only in the single
`(2,2,2)` instance.

## Verification

Focused check: **passed, no errors, no warnings.**  Targeted module build:
passed.  Axiom census: `markFold`, `mkApp`, `mkOfTop`, `mkOfWin`, `mkOfBnd`
**clean** (`[propext, Classical.choice, Quot.sound]`); `markMon`, `markJet`,
`gridIntHigh` carry `sorryAx`, all through the single declared frontier.

## Lean lessons

* `Continuous.congr` against a `gridBase` goal: `rw` cannot see through
  `gridBase` (it is a plain `def` but the rewrite pattern is syntactic).  Prove
  the continuity statement in the explicit `riemannianFiberNormSq` form as a
  `have`, then close with `exact` — defeq does the rest.
* `rw [MeasureTheory.integral_finset_sum _ (fun i _ => hint _ (…continuity…))]`
  FAILS: the inline continuity term is elaborated before the goal fixes the
  summand family, and higher-order unification returns `Pi.mul` shapes
  (`(fun x => f x) * (fun x => g x)`) which then do not match the goal.  Always
  state the integrability as a separate `have` whose type spells the summand
  out, then `rw [… integral_finset_sum _ hIT]`.
* After `rw [Fin.prod_univ_succ]` on a `Fin.cons` tuple, the `Fin.cons_zero` /
  `Fin.cons_succ` rewrites have ALREADY happened (`Fin.cons` reduces on `0` and
  `succ`), so a following `simp only [Fin.cons_zero, Fin.cons_succ]` errors with
  "made no progress".  Drop it and close with `rfl`.
* `rw [Fin.prod_univ_zero, mul_one]` leaves a `gridBase … = riemannianFiberNormSq …`
  goal that is `rfl` but which `rw`'s closing `rfl` (reducible transparency) does
  not see.  Add an explicit `rfl` line.
* To reassociate a product of fibre-norm atoms whose two sides are DEFEQ but not
  syntactically equal, `ring` is unusable (different atom syntax).  Use a
  `∀ A B C D : ℝ, … = …` helper proved `by intros; ring`, `rw` it, then `rfl`.
* `set x := e with h` produces a transparent local definition here: a later bare
  `rfl` does unfold `x`.  (Confirmed by the `Fin.cons` blocks.)

## Session 4 (2026-08-04): three calculus entries + the `∇P` mark

Added, all green on the first check, all axiom-clean:

* `mkOfP` — the state itself enters at `u = 0`.  `|∇ⁱP|²` is the single-factor
  monomial of weight `i`, a term of `atgw bP (i+1) = markGrid bP 0 i` for
  `i ≥ 1`, via `single_factor_mul_antidiagonalTupleGrid_le` at `k = 0` plus
  `antidiagonalTupleGrid_le_window`.  The exceptional order is `i = 0`, where
  `markGrid bP 0 0 = atgw bP 1 = atg bP 0 = 1` EXACTLY, so the δ-anchor
  `|P|²_∞ ≤ 1` is genuinely needed and is a hypothesis of the lemma.  This is
  what lets an arm LINEAR IN `P` ITSELF (the Palatini curvature head
  `lrCurvF g₀ P`) enter the marked currency; `capOfP` had to spend both
  pointwise caps for the same bridge.
* `mkOfDP` — `∇P` enters at `u = 1` with constant `1`.  `|∇ⁱ(∇P)|² = bP (i+1)`
  after `rfns_iteratedCovGrad_covGrad_comm_rs`, and that is the mark-only
  monomial of `markGrid bP 1 i` (`markOne_of_term` at `c = i`, `k = 0`).  No
  estimate, no hypothesis.  Not yet consumed on-path — it is the free half of
  the `ricciDALow` arm (see `SelfLowArmCaps.md`).
* `mkDdc` / `mkDdc0` — output-slot permutation is a marked-window isometry, for
  `rsDomDomCongrSection` and for `domDomCongrSection`.  Verbatim mirrors of
  `capDdc`/`capDdc0`; the marked currency had `mkReindex` (source slots) but no
  output-slot entry, which blocked every Palatini normal form.

### Design finding: an order-two factor IS a legal mark

The session was dispatched to decide "the marked treatment of a single `c = 2`
factor".  Re-reading `markGrid`: `markGrid b (u+1) w = ∑_{c ≤ w} b (c+1) ·
markGrid b u (w-c)`, so a mark is any factor of order `≥ 1`, NOT order exactly
one — an order-two factor is the `c = 1` summand and simply consumes two units
of the level budget.  So `mkOfTop`-at-`c = 2` is a non-problem; what a lone
`∇²P` really costs is a LEVEL, not a mark: `|∇^{i+2}P|²` at tower order `i` has
weight `i+2`, which is inside `markGrid b 1 (i+1)` and outside
`markGrid b 1 i` — one order over budget, exactly the thing the currency exists
to detect.  The question turned out to be moot for the dispatched arm (see
below), but the rule is worth keeping: **marks are free at any order; levels are
not.**

## Session 5 (2026-08-04): `mkOfAtg`, the exact-weight bridge in

`mkOfTop` consumes a *top-separated* producer; the tree also has *exact-weight*
producers (`…_diagonalProductGrid_le` shapes) that deliver `K i · atg(bP)(i+1)`
for the jets of an arm whose covariant derivative always costs one derivative of
the state.  `mkOfAtg` is the entry for those, via `Combinatorics.atgLeMark1`:

```
|∇ⁱX|²(x) ≤ K i · grid(bP x)(i+1)   ⟹   HasMarkWin g₀ P X 1 (K · count(i+1))
```

It costs the δ-anchor `|P|²_∞ ≤ 1` (`hP0`), which `mkOfTop` does not need — the
anchor is what lets the inert `bP 0` factors of an over-long tuple be dropped.

Its first customer is `clCovMk` (`SelfLowArmCaps.lean`): `∇(connLowOp)` is
delivered exactly this way.  Expect any "coefficient built from `g₀` plus a
moving inverse-metric insertion" to enter here.

Verification: focused check green (only the declared `gridIntHigh` sorry),
targeted build green, `mkOfAtg` axiom-clean.

## Session 6 (2026-08-04): `gridIntHigh` — the route is now FULLY CONCRETE and general; NOT landed

**Verdict: `gridIntHigh` is still `sorry`.**  What changed is that the route is
no longer research: every tool it needs exists in the tree or in mathlib, the
last genuinely missing analytic brick (`lyapunov_pow_le`) is now BUILT and
axiom-clean, and the general statement needs **no narrowing** — the earlier worry
that unbalanced tuples resist is an artefact of one tool, not of the mathematics.

### The corrected route (verified on paper, end to end)

Notation: `i := m + 1 = ∑_j c_j`, `q` factors after discarding the weight-`0`
entries, all `c_j ≥ 2`, `q ≥ 3`; `R := ‖∇^m P‖_{L²}`, `Λ := max Λ₁ 1 ≥ 1`,
`Λ₀ ≤ 1`.

1. **Free-weight Hölder — ALREADY EXISTS, public, axiom-clean.**
   `Integral.Connection.holder_integral_prod_riemannianFiberNormSq_le`
   (`Analysis/Integration/L2/FiniteProductHolderFiberNorm.lean:89`):
   ```
   ∫ ∏_{m∈t} rfns(S m) ≤ ∏_{m∈t} (∫ rfns(S m)^{1/θ m})^{θ m}
   ```
   for ANY `θ m > 0` with `∑ θ m = 1`.  Its sibling
   `..._le_of_sup_bound` (`:153`) already splits off the sup-bounded factors —
   i.e. the "discard the weight-`0` entries against `Λ₀ ≤ 1`" step is also done,
   and `..._natWeight_le_of_sup_bound` (`:216`) is the `θ = e/k` specialization.
   THIS IS THE OVER-COUNT THAT ALMOST HAPPENED: the session began by planning a
   weakened clone of `grid_prod_int_le` (443 lines) because that theorem
   hard-codes the canonical Hölder weights `θ_j = c_j/i` and additionally demands
   `hNi : ‖∇^i P‖ ≤ R` (the out-of-budget top jet) and `hGNP` at every
   `0 < j < i`.  None of that is needed — the free-weight Hölder is the right
   tool and it was already sitting one layer down.  **Exhibit TEN.**

2. **Per-factor two-anchor GN (`GN2`) — the one brick still to build.**
   For `2 ≤ c < m` and any `θ ∈ [(c−1)/(m−1), c/m]`:
   ```
   (∫ rfns(∇^c P)^{1/θ})^{θ} ≤ C · Λ^{2(c − θ m)} · R^{2θ}.
   ```
   Proof = Lyapunov between the two existing two-point scales, both instances of
   `exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs`:
   * `A`: base `P`, top `k = m` ⟹ `(∫F^{m/c})^{c/m} ≤ C_A Λ₀^{2(1−c/m)} R^{2c/m}`;
   * `B`: base `u := ∇P` (valence `(0,3)`), top `k = m−1`, order `c−1` ⟹
     `(∫F^{(m−1)/(c−1)})^{(c−1)/(m−1)} ≤ C_B Λ₁^{2(1−(c−1)/(m−1))} R^{2(c−1)/(m−1)}`,
     using `‖∇^{m−1}u‖ = ‖∇^m P‖` (`icgNormComp`) and
     `rfns(∇^{c−1}u) = rfns(∇^c P)` (`rfns_iteratedCovGrad_comp`).
   `1/θ` lies between `m/c` and `(m−1)/(c−1)` exactly on the stated `θ`-range, so
   `lyapunov_pow_le` applies with `1/θ = lam·(m/c) + (1−lam)·((m−1)/(c−1))`.
   Raising to the `θ` power and collecting: the two weights
   `lam₁ = lam·θ·m/c`, `lam₂ = (1−lam)·θ·(m−1)/(c−1)` satisfy `lam₁ + lam₂ = 1`,
   the `R` exponent collapses to `2θ`, the `Λ₀` exponent `2β` has `β ≥ 0` and is
   discarded by `Λ₀ ≤ 1`, and the `Λ₁` exponent is `2α` with **`α = c − θm`**
   (the derivative-count identity), so `Λ₁^{2α} ≤ Λ^{2α}`.

3. **Assembly — arithmetic only.**  Choose
   ```
   θ_j := (1−t)·(c_j−1)/(m−1) + t·c_j/m,    t := (1 − L)/(U − L),
   L := ∑_j (c_j−1)/(m−1) = (m+1−q)/(m−1),  U := ∑_j c_j/m = (m+1)/m.
   ```
   `q ≥ 2` gives `L ≤ 1 < U`, so `t ∈ [0,1]` and `∑ θ_j = 1`; each `θ_j` is a
   convex combination of its two endpoints, hence inside the `GN2` range.  Then
   step 1 + step 2 give
   ```
   ∫ ∏_j rfns(∇^{c_j}P) ≤ ∏_j C·Λ^{2(c_j − θ_j m)}·R^{2θ_j}
                         = C^q · Λ^{2(∑c_j − m)} · R^2 = C^q · Λ² · R²
   ```
   because `∑ c_j = m+1` and `∑ θ_j = 1`.  **The `Λ` exponent lands on exactly
   `2` with no slack spent and no balance condition** — the `∑ α_j = 1` identity
   is automatic, not something to arrange.  Finish with `Λ² ≤ 1 + Λ₁²`.

### Why the "unbalanced tuple" scare was wrong

Mid-session the route looked to need `2c_j ≤ m+1` for every factor (first
violated at `(5,2,2)`, `m = 8`).  That condition is EXACTLY the price of the
canonical Hölder weights `θ_j = c_j/i` that `grid_prod_int_le` hard-codes: with
`θ_j = c_j/i` one needs `β_j = 1 − 2c_j/i ≥ 0`.  With the free weights of step 3
the constraint disappears.  Do not reintroduce a balance hypothesis.

Also ruled out, with proof, so nobody re-derives them:
* **Single-anchor-per-factor is impossible.**  If each factor is estimated at one
  anchor only, then `∑_{j∈S_u}(1 − 1/p_j) ≤ 1` (the `Λ₁` budget) together with
  `1/p_j ≥ c_j/m` (P-anchor) / `≥ (c_j−1)/(m−1)` (u-anchor) and `∑ 1/p_j ≤ 1`
  forces `|S_u| ≤ 1` and then `(c_1−1)/(m−1) ≤ (c_1−1)/m`, false.  Genuine
  per-factor MIXING is necessary.
* **Even-integrand interpolation is impossible.**  For `(2,2,2)` at `m = 5` the
  only in-budget pure-power integrals are `∫|∇²P|^{2a}` with `a ≤ 2`
  (P-anchor, `2a ≤ m`) and `a ≤ 4` (u-anchor, `a+1 ≤ m`); the LP
  `λa + (1−λ)b = 3`, `(b−1)(1−λ) ≤ 1` has the UNIQUE solution `a = 5/2`, `b = 4`.
  The odd `L⁵` norm is forced, hence a genuine `Lᵖ` (not integer-power) scale.
* **Rescaling cannot help.**  `P ↦ P/t` is homogeneous of the right degree on
  both sides; the pure-`u` bound's `Λ^{2q−2}` is scale-invariant.
* **Geometric mean of the two ANSWERS fails** (unlike the per-factor Lyapunov):
  the `P`-anchored answer involves `‖∇^{m+1}P‖`, out of budget for any weight
  `> 0`.

### What landed this session

`Integral.lyapunov_pow_le`
(`Analysis/Integration/L2/FiniteProductHolderFiberNorm.lean`, `ScalarHolder`
section, next to the free-weight Hölder it is derived from):
```
0 ≤ᵐ F, 0 < a, 0 < b, lam ∈ [0,1], c = lam·a + (1−lam)·b,
Integrable (F^a), Integrable (F^b)
  ⟹ ∫ F^c ≤ (∫F^a)^lam · (∫F^b)^{1−lam}
```
= log-convexity of `p ↦ ‖F‖_{Lᵖ}`, i.e. THE bridge between two `Lᵖ` scales that
the `gridIntHigh` docstring names as missing.  Axiom-clean.  It is a 40-line
corollary of the existing `holder_integral_prod_rpow_le_prod_integral_rpow` at
`t = Finset.univ : Finset (Fin 2)`, `f = ![F^a, F^b]`, `θ = ![lam, 1−lam]`; the
only real steps are `Real.rpow_mul` (twice) and `Real.rpow_add'` (whose `≠ 0`
side condition is why `0 < a`, `0 < b` are hypotheses).

### Remaining work, honestly sized

Brick GN2 (step 2): ~200–250 lines — the two GN instantiations plus rpow/cast
algebra; the fiddly parts are the `ℕ→ℝ` casts in `m/c`, `(m−1)/(c−1)` and the
`0 < c < m`, `0 < c−1 < m−1` side conditions of the GN theorem.
Brick ASSEMBLY (step 3): ~200–300 lines — merging `(c₁, c₂, e)` into one
`Finset`-indexed family, the `θ` construction, `∑θ = 1`, and the range checks.
No further mathematics.  `gridIntHigh` is now an EXECUTION task, not a research
task.

Verification: `FiniteProductHolderFiberNorm.lean` focused check green, targeted
build green, `lyapunov_pow_le` axiom-clean.  `gridIntHigh` unchanged (still the
single declared `sorry`), so `markMon`, `markJet` and the five `sorryAx`-carrying
arm jets are unchanged too.

## Session 7 (2026-08-04): `gridIntHigh` PROVED — the tame C0 bottom has no frontier left

The `sorry` is gone.  `gridIntHigh` now has a real proof, at the statement it
always had: no narrowing, no balance hypothesis, `grid_prod_int_le` untouched,
no `max Λ₁ 1` introduced.

### The route, as executed

The whole analytic content sits in `TensorHilbert/GNTwoAnchor.lean`
(`gnProdJet`, built this session on top of last session's `gnTwoAnchor`).  What
`gridIntHigh` does here is purely the bookkeeping that turns the marked monomial
into `gnProdJet`'s input:

1. `cc : Fin (n+2) → ℕ := Fin.cons c₁ (Fin.cons c₂ e)` — the two marked orders
   in front of the unmarked block.  `Fin.prod_univ_succ` twice + `Fin.cons_zero`
   / `Fin.cons_succ` + `ring` identifies the integrand
   `gridBase c₁ · gridBase c₂ · ∏_q gridBase (e q)` with `∏_j gridBase (cc j)`.
2. `t := univ.filter (cc · ≠ 0)` is the active set.  `2 ≤ t.card` from
   `{0, Fin.succ 0} ⊆ t` (both marked orders are `≥ 2`); `2 ≤ cc j` on `t` from
   `cc j ≠ 0` and `cc j ≠ 1`; `∑_{t} cc = ∑_{univ} cc = c₁+c₂+k = m+1`.
3. `gnProdJet` gives `K m · Λ₁² · ‖∇^mP‖²`; `Λ₁² ≤ 1 + Λ₁²` lands on the
   required RHS.  The SAME `K` is reused, so no new constant is invented here.

`gridBase g₀ P x j` is *definitionally* the fibre-norm-square that `gnProdJet`
integrates, so `change _ = ∏ j, gridBase g₀ P x (cc j)` crosses the two
statements with no rewriting at all.  (`change`, not `show` — the style linter
rejects a goal-changing `show`.)

### Lean lessons (session 7)

* Case analysis on `Fin (n+2)` for a `Fin.cons`-built family: `rw [hcc]` first,
  then `induction j using Fin.cases with | zero => … | succ i => …`, nested once
  more on `i`.  `refine Fin.cases ?_ ?_ j` is the flaky version (higher-order
  motive); the `induction … using` form unifies `Fin (n+2)` against
  `Fin (?k+1)` by literal-offset matching without help.
* Use `Fin.succ 0`, never `(1 : Fin (n+2))`, as the second index: `Fin.cons_succ`
  then fires syntactically, `Fin.succ_ne_zero` gives the distinctness needed for
  `card {0, Fin.succ 0} = 2`, and no `Matrix.cons_val_one` / `Fin.val_one`
  detour is required.
* `obtain ⟨cc, hcc⟩ : ∃ cc, cc = <body> := ⟨_, rfl⟩` rather than `set` — and the
  same for the `Finset`.  Under `classical`, re-writing a `Finset.filter` inside
  the proof can pick a different `DecidablePred` instance than the one the
  statement elaborated with; keeping the filter behind an opaque local plus an
  equation sidesteps it.  (`gnProdJet` avoids the problem in its own statement by
  taking the active set as an explicit `Finset` argument.)

### Verification

Focused checks green and warning-free (`GNTwoAnchor.lean`, `TameMarkWin.lean`).
Targeted builds green in dependency order (`GNTwoAnchor`, then `TameMarkWin`).
Axiom census: see `UNIF_EXISTENCE_PLAN5.md`, executor report No. 145.
