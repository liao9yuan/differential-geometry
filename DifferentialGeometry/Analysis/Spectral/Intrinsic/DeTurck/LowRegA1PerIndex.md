# `LowRegA1PerIndex.lean` — the ball-free per-index assembly of the `a₁` arm

Brick 4a of the rung-3 re-scope (ledger №153), landed v1 in №154, **replaced in
place by v2 in №156** after the acceptance panel refuted v1's Hölder geometry
(ledger №155), and **re-split in the `C₀` group only as v3 in №158** after the
№157 ruling on v2's rider.  Sibling of `LowRegA2PerIndex`, for the first-order
arm `A.a1 T = appCc C₀ T + appCc C₁ (∇T)`.

## What is in the file (v3)

* `a1Arm0`, `a1Arm1` (private) — the two `appCc` summands, each priced by the
  mixed engine `app_jet_sq_split`, but with **different thresholds**:
  `S = Finset.range (q-1)` for `C₀` and `S = Finset.range q` for `C₁`.
* `a1PerIdxJet` — the squared `H^q` bound for the whole arm.
* `a1PerIdxLin` — its square-root form (what the rung pairing consumes).
* `sumPairLe`, `sqAddLe`, `combine2`, `sqrtOnePlus` (private) — arithmetic glue.
  `sumPairLe` is new in v3: the `C₀` complement `range (q+1) \ range (q-1)` is
  the pair `{q-1, q}`, which collapses to a singleton at `q = 0`, so the two
  state-side terms are bounded by `∑_{i ∈ {a,b}} f i ≤ f a + f b` rather than by
  `Finset.sum_pair` (which needs `a ≠ b`).

`dataCap` (v1's `L^∞` cap on a whole data jet window) is **gone** since v2.
v3's `C₀` arm does sup-cap a two-term data window (`l ∈ {0,1}`) at `i = q-1`,
but it does so with the two fibre embeddings directly (`Cd0` at rank `(0,2)` for
`T`, `Cd1` at rank `(0,3)` for `∇T`), through the single constant
`Cd0² + Cd1²`; no wrapper is needed.

## The mathematics (v1's finding, v1's error, the v2 fix, the v3 re-split)

v1's finding stands and is the reason a₂'s recipe does not transfer: the sup
embedding costs `+2` `L²` orders, so an `L^∞` coefficient at Leibniz index `i`
reads the `C₀`/`C₁` tower at index `i+2` and hence state jets of order `i+3`; at
the top index `i = q` that is `q+3`, one above the rung budget `q+2`.  There is
no slack to recover as there was for `C₂` (`c2JetTowerSharp`): `C₁` genuinely
contains `∇T` and `C₀` is quadratic in it, so `range (i+2)` is sharp for both.

v1's **error** was the conclusion it drew: it put the *state* window in `L^∞` at
**every** `i ≥ 1`.  That is only forced at `i = q`.  At `i = 1` of the `C₁`
group it produces the slot `class·(1+jet₃)·jet_{q+3}` — state order `q+2` in the
DATA factor, against the coefficient factor `1 + jet₃` whose leading `1` is
`R`-free.  In the cross-scale pairing (`two_mul_sum_ladder_le`,
`CrossScaleCauchySchwarz.lean:232`) every forcing slot reaching `√E_{σ+1}` adds
its coefficient to `α`, and `(2α+ε)·E_{σ+1}` must clear `Cδ < 2`; this slot is
*quadratic* in `√E_{σ+1}`, so Young does not apply to it and the absorption
fails.  Route error, counter 1/3 (№155).

**v2 (the first ruled split).**  Per Leibniz index, uniformly in both groups:
coefficient side for `i < q`, state side at `i = q`.  Then every `q+2` sits in a
*coefficient* factor whose data companion is a class-order window, so the arm
costs the rung a `K_R^{a₁}·R` absorption term rather than a smallness constant,
and PSTOP adapter H widens to `Cq(k-1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε < 1`
(PSTOP §6.4 correction block, §10).

**v2's rider, and its №157 resolution — this is what v3 implements.**
`c0_jet_tower_quad` is quadratic in `T`, so every `C₀` slot carries the extra
factor `1 + J 4 = 1 + ‖T‖²_{H³}`, an `L²_t` quantity rather than a class one.
In v2 that evolving factor also sat on the `i = q-1` slot, whose coefficient sup
reached state order `q+2`; adapter H prices only `K_R^{a₁}·R`, so the `C₀`
contribution `K·R·(1 + √E₃(t))` did not fit.  The planner's first repair (Young
at the ladder level) was refuted by the acceptance panel: the cross-scale
pairing multiplies every ladder entry by a further `√E_{σ+1}`
(`abs_sum_crossScale_le`, `CrossScaleCauchySchwarz.lean:75–80`), so the slot's
true contribution is `K·R·(1+√E₃)·E₄` — a time-dependent `E₄`-coefficient that
no landed Grönwall variant accepts and no Young repairs.

The adopted ruling (№157) is the **per-group asymmetric split**: keep
`S = range q` for `C₁`, and lower `C₀` to `S = range (q-1)`, i.e. state-side at
BOTH `i = q-1` and `i = q`.  Legal for `C₀` and only for `C₀`: its data is `T`,
so the extra `l = 1` term of the `i = q-1` data window is `|∇T|_∞ ≲ ‖T‖_{H³}`
(order `3`, in budget), where `C₁`'s would be `|∇²T|_∞` (order `4`, v1's
breaker).  Rejected alternative: a `c0` tower variant whose quadratic factor
sits at a class window — a new embedding layer the tree deliberately lacks
(PSTOP:571–578), high cost, zero need.  Adapter H is UNCHANGED: only `a₂` and
the `C₁` group feed it.

## Verified v3 order ledger

`J n = ∑_{j<n}‖∇ʲT‖²`, so `J n` sees state jets of order `≤ n-1`.  Read off the
landed statements slot by slot, with `q - 1 + 2 = q + 1` for `q ≥ 1`:

| slot | coefficient factor | data factor | top state order |
|---|---|---|---|
| `C₀`, `i ≤ q-2` | `(1+J 4)(1+J(i+4))`, sup | `J(q-i+1)` | `max(i+3, 3) ≤ q+1` |
| `C₀`, `i = q-1` | `(1+J 4)(1+J(q+1))`, `L²` | `J 4`, sup | `max(q, 3)` |
| `C₀`, `i = q` | `(1+J 4)(1+J(q+2))`, `L²` | `J 3`, sup | `max(q+1, 3)` |
| `C₁`, `i < q` | `(1+J(i+4))`, sup | `J(q-i+2)` | `i+3 ≤ q+2` |
| `C₁`, `i = q` | `(1+J(q+2))`, `L²` | `J 4`, sup | `max(q+1, 3)` |

Checked against №157's expected ledger before proving, and it agrees:

* the whole `C₀` group tops out at `max(q+1, 3)`, i.e. at `q+1` for `q ≥ 2` — it
  never reaches `q+2`;
* the `C₀` slots' evolving factors `1 + J 4` now meet only class windows
  (`J(q+1)`, `J 3`) and the same-scale window `J 4`, never a `√E_{q+2}`-order
  data factor, so they belong in the `L¹_t` Grönwall coefficient (`∫E₃ ≤ B₃²`);
* the only `q+2` left in the whole arm is `C₁`'s `i = q-1` coefficient sup
  (tower index `q+1`, window `range (q+3)`), against the class window `J 3` —
  exactly the `K_R^{a₁}·R` term adapter H already prices.

**Scoping, honestly.**  The `q ≥ 2` scope now covers the `C₀` claim too, not
only the "exactly one slot" reading: at `q = 1` the `C₀` data sups already reach
`3 = q+2`, and at `q = 0` they reach `q+3`.  Every rung has `q = k-1 ≥ 2`, so
this costs nothing; it is stated in both public docstrings.

**`q = 0` is not excluded.**  The `i = q-1` coefficient window is written
`range (q-1+2)`, which is `range (q+1)` for `q ≥ 1` and `range 2` at `q = 0` —
exactly what `c0_jet_tower_quad` produces at index `q-1 = 0` in ℕ.  With that
one shape choice the statement is unconditionally true and no `2 ≤ q` hypothesis
was needed.  The sharper `range (q+1)` spelling would have been UNPROVABLE at
`q = 0`: `hcoeff 0` gives `1 + J 2`, and `(1+J 2)/(1+J 1)` is unbounded.

## Reused / adapted / found

* **New producer**: `app_jet_sq_split` in
  `Analysis/Sobolev/TensorHilbert/ParametricAppCcJetBound.lean` — the
  finset-parameterized mixed engine, of which `app_jet_sq_le` (`S = range (j+1)`)
  and `app_jet_sq_head` (`S = {0}`) are the extremes.  Census sweep before
  writing it came back empty for a second time; the closest relative is the
  private, `Hs`-ball-fused `master_appCc_jet_le_sharp`
  (`ConnLapCommutatorCoefficientTame.lean:475`), which collapses its conclusion
  onto a single `Hs` norm.  Details in that file's `.md`.
* **Reused unchanged**: `c0_jet_tower_quad`, `c1JetTowerQ` (`LowRegC01JetTower`),
  `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
  (`SobolevEmbeddingSharpC0JetSum.lean:717`), `icgNormComp` (`GradCapAtgw`),
  `icgWinShift`, `sqrtAdd2`, `sqrtFinSum` (public in `LowRegA2PerIndex`),
  `appCcGdiag`, `iteratedCovGrad_add`.
* `app_jet_sq_head` is left in place: it is a legitimate public statement (the
  `S = {0}` extreme), it is now census-covered alongside the general engine, and
  removing it would churn a file with no other cost saved.
* **v3 added no new producer.**  The lower `C₀` threshold reuses the same engine
  at a different `S`; its second data cap is the rank-`(0,3)` instance of
  `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
  composed with `icgWinShift` — exactly the pair `a1Arm1` already used for `∇T`.
  Only the private arithmetic helper `sumPairLe` is new.

## Deferred dedup punch-list (unchanged, count corrected in №155)

The composition lemma `icgNormComp` has **five** private re-derivations in the
tree — `norm_iteratedCovGrad_comp` (`AllOrderGardingConstant.lean:143`),
`jet_comp_norm` (`Garding/SlotTransportPairing.lean`),
`norm_iteratedCovGrad_comp_cc` (`CovDivergenceRoughLaplacianCommutation.lean:551`),
`norm_iteratedCovGrad_comp_local` (`SobolevNonlinearityExistence.lean:572`,
and `DirichletSpectralBochnerGap.lean:443`) — plus a second copy of the
window-shift lemma (`jet_shift_le`, linear form, same file as `jet_comp_norm`).
Not touched: deduplicating means editing files deep in the build graph for no
mathematical gain.  Likewise `icgWinShift`/`sqrtAdd2`/`sqrtFinSum` still live in
`LowRegA2PerIndex.lean` rather than in `GradCapAtgw` / a real-analysis file;
moving them forces a rebuild of a very deep prefix.

## Lean lessons

* `Finset.range_subset.mpr` does **not** prove `range q ⊆ range (q+1)` here: the
  ambient `Finset.range_subset` unfolds to `∀ x < q, x ∈ s`.  Prove it by
  `intro i hi; rw [Finset.mem_range] at hi ⊢; omega`.
* `Finset.range (q+1) \ Finset.range q = {q}` closes with
  `ext i; simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton];
  omega` — then `Finset.sum_singleton` turns the engine's complement sum into
  the single top slot.
* v3's `C₀` complement is `Finset.range (q+1) \ Finset.range (q-1) = {q-1, q}`,
  by the same `ext`/`omega` recipe with `Finset.mem_insert` added.  Do NOT then
  reach for `Finset.sum_pair`: it needs `q - 1 ≠ q`, false at `q = 0`.  Use the
  private `sumPairLe` (`∑_{i ∈ {a,b}} f i ≤ f a + f b` for nonnegative `f`,
  proved by `rcases eq_or_ne a b` and `simp` for `{a,a} = {a}`), which is the
  bound one actually needs anyway.
* The engine's data-cap hypothesis is stated with a bound FUNCTION, so the goal
  arrives as an unreduced beta-redex `(fun i => …) i` and `rw` cannot see the
  pattern `q + 3 - i` inside it (the lambda body has a bound variable there).
  Fix it with `change _ ≤ <the beta-reduced RHS>` before rewriting.  `show` also
  works but trips `linter.style.show`.
* Choosing the data-cap function as `fun i => C * J (q + 3 - i)` — rather than a
  case split `if i < q then … else …` — makes both state-side indices come out
  of one uniform expression: `q + 3 - i` is `4` at `i = q-1` (for `q ≥ 1`) and
  `3` at `i = q`, and each branch rewrites it with a plain `omega`.
* `q + 1 - i` (what the engine produces) and `q - i + 1` (what the statement
  should read) are not defeq; rewrite with `show q + 1 - i = q - i + 1 from by
  omega` under `hi : i < q`.
* At the top index the engine's data window is `Finset.range (q + 1 - q)`;
  rewrite to `1` first, then `Finset.sum_range_one` and
  `simpa only [Nat.add_zero, iteratedCovGrad_zero]` to reach the embedding for
  the data tensor itself.  At `i = q-1` the window is `range 2`: peel with
  `Finset.sum_range_succ` then `Finset.sum_range_one`.
* `set J : ℕ → ℝ := fun n => ∑ …` keeps the statements readable and stays defeq
  to the explicit sums, so `calc`/`exact` cross the boundary freely — but any
  `rw` must target the explicit form.
* For "loosen the constants" endgames an explicit `calc` with `mul_le_mul_*`
  and hand-supplied nonnegativity remains far more reliable than one big
  `nlinarith`.  v3 replaced v2's `nlinarith only [hnn, sq_nonneg Cd]` steps by
  `le_mul_of_one_le_left hnn (by linarith only [hCd2_nn])`, which is both
  shorter and faster.
* `SmoothCcTensor g r s` is NOT a `NormedAddCommGroup` (only a
  pre-inner-product space), so a generic `‖x+y‖² ≤ 2‖x‖²+2‖y‖²` helper over
  `[NormedAddCommGroup F]` fails to instantiate.  State it on `ℝ` (`sqAddLe`)
  and feed it `norm_nonneg _`, `norm_add_le _ _`.
* `linter.style.multiGoal`: `refine add_le_add (le_trans h ?_) ?_` followed by a
  second `refine add_le_add ?_ ?_` leaves a goal untouched and warns.  Focus the
  first goal with `·` and nest.

## Verification

Focused checks green on `LowRegA1PerIndex.lean` and both census files; targeted
builds green for `+…LowRegA1PerIndex` and `+…ScratchC01Census`.  Axiom census
run: `app_jet_sq_head`, `app_jet_sq_split`, `icgWinShift`, `sqrtAdd2`,
`sqrtFinSum` and the replaced `a1PerIdxJet`/`a1PerIdxLin` all report
`[propext, Classical.choice, Quot.sound]`; zero occurrences of `sorryAx` in the
whole census output.  No new `maxHeartbeats`.  Two local style warnings raised
by the v3 edit (`show`-that-changes-the-goal, and a two-goal `refine`) were
cleaned in place.

## Next (brick B of the rung-3 campaign)

Brick A (this v3 re-split, plus the `a = 1` seed mass in
`ShortTime/LowRegSmoothBridge.lean`) is done.  Brick B is the
forcing-realization lemma along `lowregGalSol`'s trajectory; Brick C is the
closure statement itself — the pairing (`two_mul_sum_ladder_le`,
`CrossScaleCauchySchwarz.lean:232`), the `L¹_t` Grönwall
(`galerkin_energy_l1_bound`, `GalerkinParabolicEnergy.lean:497`) with its two
new additive-slot variants, and adapter H in the widened form
`Cq(k-1)·Cδ* + (K_R + K_R^{a₁})·R + 2ε < 1`.  Joint ledger left for them:
JOINT-NEMYTSKII, JOINT-REP, JOINT-IDENT (Fatou stage only), JOINT-RETR.
JOINT-BESSEL is CLOSED as an over-count — `cc_partial_le_norm` and
`weight_sum_le_normSq` already exist; see `ShortTime/LowRegSmoothBridge.md`.
The `C₀` quadratic-factor rider is CLOSED by this v3 re-split.
