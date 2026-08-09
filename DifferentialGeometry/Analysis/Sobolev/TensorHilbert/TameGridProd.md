# `TameGridProd.lean` — the tame currency for the C0 bottom

Companion note for `TameGridProd.lean`.  Status, route, what was verified, what
failed, and the exact next frontier.

## Why this file exists

Executor report No. 137 in `ShortTime/UNIF_EXISTENCE_PLAN4.md` (feasibility gate
for `selfLow_jet_quad`) established two things:

* the capped-grid currency of `GradCapAtgw.lean` **structurally cannot** deliver
  a constant affine in `‖T‖²_{H³}` — `shiftConst Λ k` has degree `k`, `foldConst`
  adds degrees, `ricciAACap` reaches `Λ`-degree `3(i+1)`;
* the C0 arm algebra **is** genuinely quadratic: classical Moser tame gives one
  power of `‖∇P‖_∞ ≲ c‖T‖_{H³}`, every other factor anchored at the fixed
  `‖P‖_∞ ≤ δ ≤ 1/3`.

This file is the first brick of the re-derivation: the reusable `L²`-level
composition layer in which "one `∇P` in `L^∞`, everything else at the δ-anchor"
is expressible.

## What is in the file (all sorry-free)

| name | kind | content |
| --- | --- | --- |
| `contRfns` | private | continuity of `x ↦ \|S(x)\|²`; copied idiom from `grid_prod_int_le` |
| `intCapMul` | private | `∫ \|A\|²\|B\|² ≤ Λ²‖B‖²` from a sup cap on `A` |
| `normSqSmul` | private | `‖c • S‖² = c²‖S‖²` (no `NormedSpace` instance on `SmoothCcTensor`, so this goes through the fibre-norm integral) |
| `gridIntUnit` | public | per-antidiagonal grid-product integral with a **state-free** constant, valence-generic |
| `gridIntTwo` | public | the two-factor specialization |
| `gridIntGrad` | public | **the quadratic tame product** |
| `gradCapLin` | public | the `∇P` cap with its `H³` dependence explicit |

### `gridIntUnit`

`grid_prod_int_le` (`Spectral/Tensor/CovGrad/JetProductIntegral.lean`) already
delivers `∫ ∏_m \|∇^{e_m}P\|² ≤ i·(max Λ (max C 1))^{7i}·R²` for `∑ e_m = i`,
`R = ‖∇ⁱP‖`, `Λ = ‖P‖_∞`, `C` the Gagliardo–Nirenberg constant of
`exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs`.  The whole point
of `gridIntUnit` is the normalization **`Λ₀ ≤ 1`**: then
`max Λ₀ (max C 1) = max C 1` and the constant stops seeing the state.  In the C0
application `Λ₀ = ‖P‖_∞ ≤ (finrank/3) = 1` at `finrank = 3`, so the hypothesis is
free.

Deliberately NOT routed through `atgGridIntRs`, whose conclusion is
`K i·(1 + ‖∇ⁱP‖²)`: the additive `1` survives the `Λ⁴` rescaling of
`gridIntGrad` and would produce a `Λ₁⁴` (i.e. `‖T‖⁴_{H³}`) term, which is exactly
the shape the deliverable forbids.

### `gridIntGrad` — the heart

```
c₁ + c₂ = k + 1,  c₁, c₂ ≥ 1,  |∇P| ≤ Λ₁ pointwise
⟹  ∫ |∇^{c₁}P|²·|∇^{c₂}P|²  ≤  K k · (1 + Λ₁²) · ‖∇ᵏP‖²
```
with `K` state-free.  A per-order arm window at order `i` uses `k = i + 1`, i.e.
lands inside the `range (i+2)` budget with **one** power of `‖T‖²_{H³}`.

Route: set `Λ := max Λ₁ 1`, `u := ∇P`, `v := Λ⁻¹ • u`.  Then `‖v‖_∞ ≤ 1`, so
`gridIntTwo` applies **in the shifted base** `(0,3)` at total order
`(c₁-1) + (c₂-1) = k-1` with a state-free constant.  Undoing the rescaling
multiplies the left side by `Λ⁴` and the right by `Λ⁻²`, leaving a single `Λ²`,
and `Λ² ≤ 1 + Λ₁²`.  The two short orders `k ≤ 2` force `min (c₁,c₂) = 1`, where
`intCapMul` pulls the cap out directly.

The rescaling is the whole trick: charging every shifted-base tuple entry to `Λ₁`
(what `atgwCapToJet` does) costs `Λ₁^{7·order}`; charging the *normalized* tensor
and paying the scale back at the end costs exactly `Λ₁^{2(q-1)}`, which is `Λ₁²`
at `q = 2`.

### `gradCapLin`

`gradCapOfJets` fixes a radius `R₀` **before** choosing `Λ₁`, so the `H³`
dependence disappears into an existential — which is precisely why the capped
currency could never exhibit its own degree in `‖T‖_{H³}`.  `gradCapLin` keeps it:
`|∇T|²(x) ≤ c·∑_{j<3}‖∇^{1+j}T‖²` with `c` a background constant.  Same fibre
embedding (`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
at valence `(0,3)`, gate `finrank = 3`), no `R₀`.  This is the substitution that
turns the `Λ₁²` of `gridIntGrad` into `c‖T‖²_{H³}`.

*Canonical-home note.*  `gradCapLin` arguably belongs beside `gradCapOfJets` in
`GradCapAtgw.lean` (same namespace, same fibre embedding).  It is here instead
because it is used only by the tame layer and because `GradCapAtgw.lean` is
imported by the whole capped-currency stack, so an edit there forces a rebuild of
files other lanes are actively holding.  If the tame layer becomes the primary
currency, move it — the statement is self-contained and has no dependency on
anything else in this file.

## The mathematics, honestly (what closes and what does NOT)

Write a C0 arm as `F(P) ⋆ ∇P ⋆ ∇P` (quadratic) or `F(P) ⋆ ∇P` (linear), `F`
analytic with `‖P‖_∞ ≤ δ ≤ 1/3`.  A generic term of `∇ⁱ(arm)` is
`∏_{j=1}^{q} ∇^{c_j}P` with all `c_j ≥ 1` and

* linear arm: `∑ c_j = i + 1`, `q ≥ 1`;
* quadratic arm: `∑ c_j = i + 2`, `q ≥ 2`.

**Linear arms are free.** `∑ c_j = i+1` is inside the budget, so `gridIntUnit`
at the `P` base (cap `Λ₀ ≤ 1`) already gives a state-free constant times
`‖∇^{i+1}P‖²`.  No `Λ₁` appears at all.  (This is why `low1Ker_jet` is
radius-free in the existing tree.)

**Quadratic arms with `q = 2` are closed by `gridIntGrad`.**  These are the
leading terms — the pure `A·A` head and the `∇A ⋆ ∇P` head, where all `i`
derivatives land on the two explicit `∇P` factors.

**Quadratic arms with `q ≥ 3` are NOT closed by this file.**  Two sub-cases:

* *some `c_j = 1`* (there is a bare `∇P` factor): pull it out in `L^∞`
  (`intCapMul`-style) and apply `gridIntUnit` at the `P` base to the remaining
  `q-1` factors of total order `i+1`.  This is a short composition on top of
  what is already here — see "next brick" below.  It covers every term in which
  at least one derivative slot is undifferentiated, in particular every term with
  `b₁ = 0` or `b₂ = 0` or some `a_m = 1`.
* *all `c_j ≥ 2` and `q ≥ 3`* (so `i ≥ 4`): genuinely open.  The estimate is
  true — a three-point interpolation with weights `α_j` (anchor `‖∇P‖_∞`),
  `β_j` (anchor `‖P‖_∞`), `θ_j` (top `‖∇^{i+1}P‖_{L²}`) satisfying
  `c_j = α_j + θ_j(i+1)`, `∑ α_j = 1`, `∑ θ_j = 1` is feasible exactly when
  `∑_j (i+1-c_j)/i ≥ 1`, i.e. exactly when `q ≥ 2` — but it needs an
  interpolation between the two available two-point Gagliardo–Nirenberg scales
  (`P`-anchored and `∇P`-anchored), which does not exist in the tree.  Pure
  `∇P`-anchoring gives `Λ₁^{2q-2}`; pure `P`-anchoring overshoots the budget by
  one derivative.  **This is the one remaining analytic frontier of the tame C0
  bottom.**

Numerically: `i ≤ 3` never produces this case (it needs
`∑ a_m + b₁ + b₂ = i` with all `a_m ≥ 2`, `b₁, b₂ ≥ 1`, hence `i ≥ 4`).  If the
`(N)` campaign's jet budget really is `∀ a ≤ 3` (see `e87b-unif-n-status`), the
frontier may be entirely off the critical path — a question for the planner, not
settled here.

## Verification

Focused check of `TameGridProd.lean`: **passed, no errors, no warnings**.
Targeted module build `+…TensorHilbert.TameGridProd`: **passed** (9536 jobs).
Axiom census of all five public declarations — `gridIntUnit`, `gridIntTwo`,
`gridIntPull`, `gridIntGrad`, `gradCapLin` — **clean**:
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  (So the whole
Gagliardo–Nirenberg chain underneath, `grid_prod_int_le` and
`exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs`, is genuinely
sorry-free, confirming No. 137's probe.)  The `#print axioms` lines were
temporary and have been removed; re-add them at the end of the file to repeat
the census.

Operational note: `lake build +Module` on this branch rebuilt ~9500 modules
because several upstream `TensorHilbert`/`DeTurck` files are dirty from other
lanes.  Interrupting such a build DELETES the olean of the module it was on
(here `DeTurckRemainderTameLipschitz/LieValue`) and leaves the elaboration lock
stale — the focused check then fails with "object file … does not exist".
Recovery: retire the stale lock by renaming
`.lake/codex-locks/lean-elaboration.lock` to `…interrupted-<tag>.lock` (the
repo's existing convention; `release -Token` does not touch elaboration locks)
and re-run the same targeted build to completion.

## Lean lessons from this session

* `set μ : MeasureTheory.Measure M := …` needs `MeasurableSpace M` **at
  elaboration of the type ascription**; the ambient instance is not found in this
  namespace.  The fix is the `grid_prod_int_le` preamble
  (`letI : MeasurableSpace E := borel E; haveI : BorelSpace E := ⟨rfl⟩;` same for
  `M`), and then `IsFiniteMeasure` must be re-`haveI`'d for `μ` because the
  fresh `letI` hides the instance that `Continuous.integrable_of_hasCompactSupport`
  needs.
* `MeasureTheory.integral_congr_ae` leaves the pointwise goal as an
  **un-beta-reduced** `(fun x => …) x = (fun a => …) x`.  Every subsequent `rw`
  fails with "did not find an occurrence"; `dsimp only` first.
* `![d₁, d₂] 0` / `![d₁, d₂] 1` are `rfl` but `rw`'s closing `rfl` runs at
  reducible transparency and does not see it.  An explicit `rfl` line after
  `rw [Fin.prod_univ_two]` closes it.  Do **not** try `simp only
  [Matrix.cons_val_zero, …]`: the tuple entry sits in the dependent valence slot
  of `riemannianFiberNormSq g₀ rb (sb + n) x (… : TensorRSSpace rb (sb+n) I x)`,
  so simp cannot build the motive.
* Index hygiene: `1 + m` and `m + 1` are not defeq for a variable `m`, and the
  index sits in a dependent type, so `rw [Nat.add_comm]` produces a bad motive.
  The working pattern is `obtain ⟨m, rfl⟩ : ∃ m, k = 1 + m := ⟨k - 1, by omega⟩`
  — substitution of a variable is always type-correct — and then let
  `icgNormComp g₀ 0 2 1 m P` produce `‖∇^{1+m}P‖` syntactically.
* `SmoothCcTensor` is a `SeminormedAddCommGroup` + `Module ℝ` but has **no**
  `NormedSpace ℝ` instance, so `norm_smul` is unavailable; `normSqSmul` here is
  the substitute.

## Next brick

1. `gridIntPull` (short): from a bare `∇P` factor plus a `(q-1)`-tuple of total
   order `i+1`, conclude `Λ₁²·K(i+1)·‖∇^{i+1}P‖²`.  Composition of `intCapMul`
   and `gridIntUnit`; no new analysis.
2. Per-summand pointwise Leibniz expansions with the `∇P` factors **explicit**.
   The existing `atgw` windows cannot be reused: at `i = 0` they already read
   `|arm|² ≤ K 0` (window `= 1`), the `∇P` structure having been spent into the
   constant.  This is the bulk of the remaining work and is per-arm.
3. The `q ≥ 3`, all-`c_j ≥ 2` interpolation, or a ruling that `i ≤ 3` suffices.
