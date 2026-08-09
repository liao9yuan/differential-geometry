# AppCcSplitEnvelope.lean — E0b, the split-envelope `appCc` estimate

Status: **GREEN, sorry-free, axiom-clean** (2026-08-03).  Focused check clean (no
warnings from this file); one targeted module build clean; `#print axioms` on both
public theorems reports only `propext, Classical.choice, Quot.sound`.  No
`maxHeartbeats` bump, no `set_option` of any kind in the file.

Brick: **E0b** of `ShortTime/F6_ESTIMATE_RECON.md` §5.1 (as re-scoped in §5.1a and
in `Intrinsic/DeTurck/LowRegDissipRung.md`) — the split-envelope member of the
`appCc` family that the base-order-2 dissipation `k`-ladder needs.

## What is proved

### `appCc_split_env` (`:110`) — the split, order-generic, dimension-free

```
∀ k Φ U A B Λ, 0 ≤ A → 0 ≤ B → 0 ≤ Λ →
  (∀ x, rfns g (s+2) c x (Φ x) ≤ A²)                    -- pointwise / C⁰ on Φ
  → (∑_{i<k+2} ‖∇ⁱΦ‖² ≤ B²)                             -- L² jet of Φ thru order k+1
  → (∀ x, rfns g 0 (s+2) x ((∇²U) x) ≤ Λ²)              -- pointwise / C⁰ on ∇²U
  → ‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k * (A * ‖U‖_{H^{k+3}} + B * Λ)
```

with `C : ℕ → ℝ`, `∀ k, 0 ≤ C k`, all spectral norms spelled
`‖ccTensorToHs g · ((k+j : ℕ) : ℝ) ·‖`.

This is the pairing the ladder needs and that **no** existing family member has:
the coefficient's `C⁰` factor `A` multiplies the **top** data order `H^{k+3}`, and
the coefficient's jet factor `B` multiplies only the lower factor `Λ`.  Every
existing member (`appCc_h2_h3_h1`, `appCc_h2_h4_h2`, `appCc_h2_h2_h2`, …) uses a
single envelope for both; `appCc_c1_h2_h1` (`H2H3Principal.lean:346`) is the only
two-constant member and it *adds* the constants, `C(B0+B1)‖U‖_{H²}`.

No `hDim`, no gate, no budget predicate.  Realized constant:
`C k = Csp k · (∑_{j<k+2} √(appCcGdiag j · Cg j)) · (Cin (k+3) + 1)`.

### `appCc_split_hs` (`:276`) — the demonstration corollary (dim 3, rungs `m ≥ 2`)

```
hDim : finrank ℝ E = 3 →
∀ k Φ U A B, … (pointwise A on Φ) … (∑_{i<k+4} ‖∇ⁱΦ‖² ≤ B²) →
  ‖appCc Φ (∇²U)‖_{H^{k+3}} ≤ C k * (A * ‖U‖_{H^{k+5}} + B * ‖U‖_{H^{k+4}})
```

i.e. the literal E0b shape `‖·‖_{H^{m+1}} ≤ C(A‖U‖_{H^{m+3}} + B‖U‖_{H^{m+2}})`
at `m = k + 2`, with `B` the coefficient jet through order `m + 1`.  One
corollary only; the ladder assembly stays E0a's job.

## The honest limitation: why `m ≥ 2` and not all `m`

Converting the `Λ` slot into a spectral norm requires a `C⁰` bound on `∇²U`.  The
gate-free sharp window
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`) has window
`finrank/2 + 2`, which in dimension three is `Finset.range 3` — the `H²` jet.
So `‖∇²U‖_{C⁰} ≲ ‖U‖_{H⁴}`, costing **two** Sobolev orders, and `‖U‖_{H⁴}` is
`≤ ‖U‖_{H^{m+2}}` only once `m ≥ 2`.

This is not a defect of the route: **the literal target is false at `m = 0`.**
The dangerous grid cell there is `∇Φ · ∇²U` in `L²`.  With only `Φ ∈ H¹ ∩ L^∞`
one has `∇Φ ∈ L²` and nothing better (gaining `L⁴` for `∇Φ` from an `L^∞` bound
on `Φ` needs `Φ ∈ H²`), while `U ∈ H³` gives `∇²U ∈ L⁶`; the product is `L^{3/2}`
at best.  Hence a genuine `H¹`-jet coefficient hypothesis cannot produce an
`H¹`-output bound with `‖U‖_{H²}` data — which is exactly why the pre-existing
`m = 0` member `appCc_h2_h3_h1` demands the `H²` jet of `Φ`, not the `H¹` jet.
Rungs `m = 0, 1` are therefore *already* covered by `appCc_h2_h3_h1` and
`appCc_h2_h4_h2`, and E0b's new content is exactly the rungs `m ≥ 2`.

The `Λ`-form (`appCc_split_env`) is left as the public interface precisely so a
consumer that has a better `C⁰` bound on `∇²U` (e.g. from a bootstrap, not from
the Sobolev window) can use it at any `m`.

## The `k`-growth honesty note (matters for E0a / §5.3 clause 1)

`C k` is **not** `k`-uniform and the proof gives no reason to expect it to be:

* `appCcGdiag j = (2(n+1))^j` is the Leibniz grid weight of
  `appCc_iteratedCovGrad_diagonalProductGrid_le`, exponential in the jet order;
* the constant sums `√(appCcGdiag j · Cg j)` over `j < k+2`, so
  `C k ≳ (2(n+1))^{(k+1)/2}`;
* `Cg j` (Gagliardo–Nirenberg two-arm) and `Csp k`, `Cin (k+3)` (spectral ↔ jet
  bridges) are themselves `k`-dependent with no proved uniformity.

The `C⁰` pairing carries no *extra* growth beyond `C k` — `A` multiplies
`‖U‖_{H^{k+3}}` with coefficient exactly `C k` — but `C k` itself grows.  So E0b
supplies the **shape** the `k`-uniform contraction needs (the `k`-free pointwise
smallness of `C2` from `lowData_split`'s second clause can now be paired with the
top order) but **not** the `k`-uniform constant.  Recon §5.3 clause 1 is still
open: it is not established that the constant *must* degrade, but this brick does
not refute it either.  Any `k`-uniform `Cδ₀` will need a grid weight better than
`appCcGdiag`, i.e. a sharper Leibniz bookkeeping at the
`OperatorFieldFibreNormJet` layer, or a `k`-uniform reformulation of the ladder.

## Producers used → summand map

| step | producer | file:line |
|---|---|---|
| pointwise Leibniz split at every order `j` | `appCc_iteratedCovGrad_diagonalProductGrid_le` | `Spectral/Tensor/CovGrad/OperatorFieldFibreNormJet.lean:885` |
| grid weight and its nonnegativity | `appCcGdiag`, `appCcGdiag_nonneg` | same file `:704`, `:708` |
| integrated Gagliardo–Nirenberg two-arm bound of that grid | `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le` | `Sobolev/TensorHilbert/RemainderCoeffPerOrderJetEnvelopes.lean:862` |
| pointwise → `L²` packaging | `normSq_le_integral_of_pointwise_fiberNormSq_le_rs` | `Sobolev/TensorHilbert/MetricArmCoeffJetTower.lean:83` |
| jet ↔ spectral bridges | `hsJet_le`, `hs_le_jet` | `Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean:834`, `:855` |
| `‖∇ⁱ(∇ʲU)‖ = ‖∇^{i+j}U‖` | `icg_comp_norm` | same file `:569` |
| sharp `C⁰` window (corollary only) | `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical` | `Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717` |

**A pre-existing general-order Leibniz split was FOUND, not built.**  Before
writing anything I grepped for product/Leibniz iterated-covariant-gradient
bounds; `appCc_iteratedCovGrad_diagonalProductGrid_le` (an `appCc` wrapper around
`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le`, proved by induction on the
jet order) is exactly the order-generic pointwise Leibniz split, and
`exists_integrated_…twoArm_rs_le` is exactly its order-generic integrated GN
companion.  So E0b needed **no new Leibniz algebra and no new interpolation
inequality** — only the observation that the two-arm bound may be read
asymmetrically (coefficient in the `L^∞` slot on one arm, data in it on the
other).  This is the fourth "wall" in the campaign that dissolved on grep.

**Not used, and why.**  `Sobolev/MoserTameProduct.lean:110`
(`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`) is the tree's other tame
product; it was rejected for two reasons: (i) it requires sup bounds on *every*
coefficient jet up to order `k` (a `Cᵏ` hypothesis), which the `c2_h2_small`-style
producers do not supply, and (ii) that file carries a real `sorry`
(`l2jet_logConvex_iteratedCovGrad`), so depending on it would have made E0b
axiom-dirty.  The route taken is `sorryAx`-free end to end.

## Home

New sibling `Analysis/Spectral/Tensor/Estimates/AppCcSplitEnvelope.lean`, not an
addition to `H2H3Principal.lean`:

* `H2H3Principal.lean` is the *fixed-order, dimension-three* member of the family
  (`H² × H³ → H¹`); this brick is order-generic and, in its main statement,
  dimension-free.  Different abstraction boundary.
* the family is already one file per member (`H2H4Principal` 161 lines,
  `H2H3FirstOrder` 134, `H1H2AppCc` 234), so a sibling matches the granularity.
* the file needs `[BoundarylessManifold I M]` (required by
  `OperatorFieldFibreNormJet`), which the fixed-order members do not carry;
  adding it to `H2H3Principal.lean` would have strengthened the hypotheses of
  eight downstream consumers for no reason.

Imports: `Estimates.H2Pointwise`, `Sobolev.TensorHilbert.AppCcJetWindowTame`,
`Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes` — the same three as
`H2H3Principal.lean`.  Not added to the root `DifferentialGeometry.lean`
aggregate, which does not list any `Estimates/` module.

`icg2_jet_le` (`:62`, private) — "the `L²` jet of `∇²U` below order `n` is
controlled by `‖U‖_{H^m}` when `n + 1 ≤ m`" — is order-generic and reusable; its
canonical home if a third consumer appears is
`Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean`, next to
`icg_comp_norm` and `hsJet_le`.  Kept private here for now, exactly as
`jetSq_le_hs` is kept private in `LowRegDissipRung.lean`.

## Hotspots / Lean lessons

* **`Finset.range_subset` is not the `≤` lemma.**  In this Mathlib
  `Finset.range_subset : range n ⊆ s ↔ ∀ x < n, x ∈ s`; the one wanted is
  `Finset.range_subset_range : range n ⊆ range m ↔ n ≤ m`.  The failure mode is
  an "application type mismatch … expected `∀ x < j+1, x ∈ ?m`" that looks like a
  unification bug, plus a bogus `omega` failure at a *different* line.
* **`calc` continuation lines must start at the column of the first step's first
  token**, not deeper.  Indenting `_ ≤ …` two spaces further makes the parser
  read it as an application of the previous justification term
  (`Function expected at hspY`) and then reports `unexpected token ':='` far
  away.  Two of the three errors in the first check were this one mistake.
* **Cast spelling drives statement design.**  `hsJet_le g s n` / `hs_le_jet g c n`
  produce `‖ccTensorToHs g · ((n : ℕ) : ℝ) ·‖`; stating the theorem with
  `((k + 3 : ℕ) : ℝ)` (not `(k + 3 : ℝ)`, which elaborates to `↑k + 3`) makes
  every bridge application match syntactically, with zero `push_cast` repair.
  The only casts needing repair are the corollary's `k + 2 + 1 → k + 3` and
  `k + 2 + 3 → k + 5`, handled by `rw [show … from by omega]` on the `ℕ`
  subterm.
* **Avoid writing the grid integral twice.**  `refine le_trans ?_ (le_of_eq (by
  ring : …)); refine le_trans ?_ (mul_le_mul_of_nonneg_left (hbnd.trans hinner)
  …); rw [← MeasureTheory.integral_const_mul]; exact
  normSq_le_integral_of_pointwise_fiberNormSq_le_rs … _ _ (hint.const_mul _) …`
  lets the goal supply both the integrand and the tensor, so the (very long)
  diagonal-product-grid expression never appears in the proof text.
* `choose C hC hspec using fun k : ℕ => <∃-lemma at k>` is the clean way to turn
  the family's per-order `∃ C, 0 ≤ C ∧ …` producers into the `C : ℕ → ℝ` the
  statement needs; three of them are used here (`Csp`, `Cin`, `Cg`).
* The E0 opacity lesson did not bite: nothing here binds a path-integral witness.
  `set W := iteratedCovGrad g 0 s 2 U` and `set N := ‖…‖` are fine, but the
  hypothesis they abstract must be derived **before** the `set` so it gets folded
  (`hWjet` and `hNnn` are stated first for exactly this reason).
* `a² + b² ≤ (a + b)²` for nonneg `a, b` is one `nlinarith` with the single hint
  `0 ≤ a * b`; the same pattern closes the two envelope-merging steps
  `X + Cin·Y ≤ (Cin + 1)(X + Y)`.

## Where this leaves the ladder

E0's rung `k = 0` (`LowRegDissipRung.lean:76`, `n_diff_h1_rung`) is green.  With
`appCc_split_hs`, the `a₂`-arm estimate is now available at every rung `m ≥ 2`
in the split form, and `appCc_h2_h3_h1` / `appCc_h2_h4_h2` cover `m = 0, 1`.
The remaining E0b-adjacent sub-brick named in `LowRegDissipRung.md` is
**unchanged and still open**: the `k`-generic analogue of `c2_h2_small`'s second
clause, i.e. an `H^{m+1}`-jet envelope for the low-base coefficient `C2` (the
`m = 0` case is `c2_h2_small` at `DeTurckRemainderLowBaseAction.lean:13268`).
Without it there is nothing to feed `B`.  That, plus the `k`-uniformity of
`Cδ₀` discussed above, is what stands between here and E0's full ladder.
