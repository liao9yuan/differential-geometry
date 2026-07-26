# ForwardUniqueConnBound — brick K1C-b (the pointwise bound on `|∂ₜA₀₃|²`)

## Outcome (current: after pass 4 — the closing pass)

**(A) — 0 `sorry`.  The file is complete.**

Pass 4 executed the planner's four tasks: `[I.Boundaryless]` added (R9(a)), the `htrace`
frontier closed, the hypothesis list pruned (R9(c)), and the docstrings brought to the final
state.  Focused check green; targeted module build **Built** (fresh, 20 s) and **warning-clean**
(no warning in the build log is attributed to this file).  `#print axioms` on
`connSpeedLow_normSq_le`, `connDiffDot_normSq_le`, `nablaRicDiff_trace_le` and
`connSpeedRHS_self` all report `[propext, Classical.choice, Quot.sound]`.  1469 lines.

### The `htrace` route, as executed

The planner's route was correct except in one respect: **the realizer-uniqueness lemma already
existed** and did not have to be written.  It is `totalNabla0SRealizes_unique`
(`Tensor/RSTensor/NablaDomDomCongr.lean:184`, namespace `Tensor0SBundle`), with exactly the
`ContMDiffSection.exists_eq_at_gen` proof the planner predicted; there is a second copy in
`HCGCompactness/ProductMFoldNorm.lean:82`.  This is the *fourth* time in this lane that an API
declared missing was already in the tree — grep the concept across the whole tree, not the
directory where it ought to live.

Three declarations were added, in a new `section TraceCommute` between `NablaRicci` and
`Hamilton`:

* `nabla_trace_field` (private, ~25 lines) — `∇(tr_g A) = tr_g (∇A ∘ traceNablaShuffle)` for the
  Levi-Civita connection of `g`.  This is `nablaRealizes_metricTraceFirstTwo`
  (`Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`) transported onto the canonical
  `metricNabla0S` by `totalNabla0SRealizes_unique`, both realizers being produced by
  `totalNabla0S_realizes`.  **This is where `[I.Boundaryless]` enters**, and it is the only
  place in the file that needs it.
* `traceShuffle_normSq_le` (private) — `traceNormSq_le` at rank `s+1` with the shuffle absorbed
  by `normSq0S_domDomCongr` against the in-file `exists_onFrame`/`onFrame_inv` pair.
* `nablaTracePerm_normSq_le` (private) — `|∇ tr_g(A∘e)|² ≤ n^{s+3}·|∇A|²` for any slot
  permutation `e`; `∇` past the reindexing is `totalNabla0SFun_domDomCongr` (fibre level — **no**
  realizer-uniqueness needed for this half, contrary to the plan's sketch).
* `nablaRicDiff_trace_le` (public) — the frontier itself,
  `|∇¹(Ric₁ − Ric₂)|²_{g₁} ≤ n⁵·|∇¹S₀₄|²_{g₁}`.  Body: `ricciDiff_eq_trace` pointwise, upgraded
  to a field equality by `DFunLike.ext` (`(Ric₁ − Ric₂) y = Ric₁ y − Ric₂ y` is `rfl`), then a
  single `exact nablaTracePerm_normSq_le (s := 2) g₁ rm04TraceSlots S x`.

Inside `connSpeedLow_normSq_le` the `sorry` block collapsed to one line:
`have htrace := nablaRicDiff_trace_le (g₁ t) (g₂ t) S hS Ric₁ Ric₂ hRic₁ hRic₂ x`.

**Post-proof simplification.**  The two new norm lemmas would have made the
`exists_onFrame` + `onFrame_inv` + `normSq0S_domDomCongr` incantation appear a third time, so it
was factored into one private rank-uniform lemma `normSq0S_reindex` (end of `section Frame`);
`normSq0S_perm3` now reduces to a one-line application of it.  Net effect: three copies of the
pattern became one, and callers never mention a basis.

**Relocation TODO (new).**  `nabla_trace_field` belongs in
`Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`, immediately after
`nablaRealizes_metricTraceFirstTwo`, as the `metricCov`-specialised field identity; it is here
only because that shared file must not be edited mid-campaign.  `traceShuffle_normSq_le` and
`nablaTracePerm_normSq_le` are rank-uniform norm facts with no Ricci-flow content and belong
next to `traceNormSq_le` in `Evolution/ForwardUniqueRmBounds.lean`.  Also:
`totalNabla0SRealizes_unique` has a duplicate in `HCGCompactness/ProductMFoldNorm.lean` that
should redirect to the Tensor-layer copy (that file's own note already says so).

### The prune (R9(c)), verified by the linter

Proof inspection plus the `linter.unusedVariables` warnings (which fired on exactly `hRm₂`,
`hRF₁`, `hRF₂` once `htrace` closed) confirm the pass-3 prediction: the route consumes `B₁`,
`B₃`, `hΓ`, `hA`, `hΛ`, `hΛ0`, `hgInv₁/₂`, `hNR₁/₂`, `hRic₁/₂`, `hS`, and the frame package
`frame/hframe/hu/hx`.  **Dropped** from both `connSpeedLow_normSq_le` and
`connDiffDot_normSq_le`: `Rm₂`, `hRm₂`, `hRF₁`, `hRF₂`, `B₂`, `hB₂`, `B₄`, `hB₄`.  The RHS
group `(B₁ + B₂ + B₃ + B₄)` became `(B₁ + B₃)`, and `connSpeed_arith` lost its `B₂`/`B₄`
variables and their nonnegativity hypotheses.  After the prune the focused check emits **no**
unused-variable warnings, so every remaining binder is genuinely consumed.

**Constant unchanged at `200(n⁶ + 1)`,** and it is honest: shrinking the `B`-sum makes the RHS
smaller but `hprod1`/`hprod2` only ever needed `B₁ + B₃ ≥ B₁` and `≥ B₃`, so no coefficient
moved.  The chain contributes `200` on the `P` side (`hs1`) and `160 + 40 = 200` on the
carrier side (`hs2` + `hs3`); the `+1` still removes the `finrank = 0` split for free.

`connSpeedRHS_self` was restated with `(Λ, B₁, B₃)` and the constant `200(n⁶+1)` so that it
still literally is "the right-hand side of `connSpeedLow_normSq_le` collapses"; its proof
(ending in `ring`) was unaffected.

### Verification and hygiene (pass 4)

Focused check green after every edit; final targeted module build *Built* and warning-clean.
Hygiene grep for `instance`/`axiom`/`notation`/`macro`/`opaque`/`syntax`/`elab`/fixity in every
modifier-prefixed form: clean.  No new imports (all of `nablaRealizes_metricTraceFirstTwo`,
`totalNabla0SRealizes_unique`, `totalNabla0SFun_domDomCongr`, `normSq0S_domDomCongr` were
already in the 303-module import closure).  Grep over `DifferentialGeometry/` for
`connSpeedLow_normSq_le`, `connDiffDot_normSq_le`, `connSpeedRHS_self`, `nablaRmDiffSq`,
`IsRmDiffField`, `nablaRmDiff`: **zero hits outside this file**, so the signature changes broke
nothing (third independent verification).  No file outside this one and its `.md` was edited.

---

## Outcome (historical: after pass 3)

**(B) — repaired statement, proof complete except the contracted trace; ONE `sorry`, at
`htrace` inside `connSpeedLow_normSq_le`.**

Pass 3 (planner ruling **R9**) closed the `Φ`-defect — the piece the pass-2 report flagged as
needing new API — and the whole Hamilton half.  The proof of `connSpeedLow_normSq_le` now runs
end to end; the single `sorry` is the local `htrace` step
`|∇¹(Ric₁ − Ric₂)|² ≤ n⁵·|∇¹S₀₄|²` and nothing else.

**Green in pass 3** (all axiom-clean, `[propext, Classical.choice, Quot.sound]`):

* `inner_le_sum_sq` (private) — `Σₖ g₁(v,eₖ)² ≤ Λ²·Σₖ g₂(v,eₖ)²` in a `g₁`-orthonormal frame,
  from the **one-sided** `hΛ` only.  Mechanism: Parseval, Cauchy–Schwarz on the `g₁`-coordinates,
  and `|v|²_{g₁} ≤ Λ g₂(v,v)`; the division by `|v|²_{g₁}` is avoided by a `0 = N` / `0 < N` split.
* `lowerBilin_metric_le` — `|g₁(A·,·)|²_{g₁} ≤ Λ²·|g₂(A·,·)|²_{g₁}`: **the `Φ`-defect bound**.
* `lowerHamRHS_comp` — frame components of `g(Γ̇·,·)` are the *lowered* Hamilton RHS; no inverse
  metric survives.
* `perm3`, `perm3_apply`, `normSq0S_perm3`, `perm3_sub` — typed slot-reindexing wrapper with its
  isometry and additivity.
* `hamSum`, `hamSum_sub`, `hamSum_normSq_le` — Hamilton's three-term slot combination; additive,
  and `|hamSum N|² ≤ 10|N|²`.
* `lowerHam_eq_perm` — `g(Γ̇·,·) = hamSum (∇Ric)`.
* `connSpeed_arith` (private) — the constant bookkeeping as **pure real arithmetic**.

**Route as executed** (body of `connSpeedLow_normSq_le`):

1. `connSpeedLow_eq` splits `g₁(Adot·,·) = g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·) − h₀₂(Γ̇₂·,·)`; then
   `normSq0S_sub_le`.
2. `lowerHam_eq_perm` (twice) turns each Hamilton term into `hamSum` of that flow's `∇Ric`;
   `hamSum_sub` subtracts *before* the slot combination; `hamSum_normSq_le` costs `10`.
3. `nablaRicDiff_le` (already green) splits off `8n³·|A₀₃|²·|Ric₂|²` — this is what `B₃` is for.
4. `htrace` (**the `sorry`**) supplies `|∇¹(Ric₁−Ric₂)|² ≤ n⁵·|∇¹S₀₄|²`.
5. `lowerBilin_normSq_le`, then `lowerBilin_metric_le`, then `hamSum_normSq_le` bound the defect
   by `10Λ²B₁·|h₀₂|²`.
6. `connSpeed_arith` does the constants.

**Constant:** `9n⁶ → 100n⁶ → 200(n⁶ + 1)`.  The `+1` is deliberate — it removes the
`finrank = 0` case split (where `n⁵ ≤ n⁶` is the only obstruction) at zero mathematical cost.

**Size / verification:** 1358 lines (limit 3000); 26 public declarations (5 `def`, 21
`theorem`), 14 `private` helpers; **exactly one tactic `sorry`**.  Focused check green after
every edit; final targeted module build reports *Built* (fresh) and is **warning-clean** apart
from the expected `uses sorry`.  Hygiene grep clean (no `instance`/`axiom`/`notation`/`macro`/
`syntax`/`elab`), no leftover `#print` probes, no file outside this one edited.

**Relocation TODO (R9(b)).**  `lowerBilin_metric_le` and its helper `inner_le_sum_sq` are
general fibre-metric comparisons with nothing Ricci-flow-specific about them.  Canonical home:
`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean`, next to `normSq0S_upper_le_of_equiv` and
`normSq0S_le_of_metric_equiv`.  They live in this file only because that shared file must not be
edited mid-campaign.  Likewise `perm3`/`normSq0S_perm3` are a thin typed wrapper over
`Tensor0SSpace.domDomCongr` + `normSq0S_domDomCongr` and belong next to the latter in
`Tensor/RSTensor/NormSqProduct.lean`.

**Unused inputs, for the R9(c) prune once `htrace` lands** (deferred, per R9(c)'s
prove-then-prune ordering) — **prediction CONFIRMED and executed in pass 4**: the route consumes
`B₁`, `B₃`, `hΓ`, `hA`, `hΛ`, `hgInv₁/₂`, `hNR₁/₂`, `hRic₁/₂`, `hS`.  It does **not** consume
`B₂`, `B₄` (hence not `Rm₂`/`hRm₂` either), nor `hRF₁`/`hRF₂` — whose mathematical content
arrives through `hΓ`.  `htrace`'s statement mentions none of them, so closing it cannot change
this list.

**Remaining frontier, fully scoped** — **CLOSED in pass 4** (see the pass-4 section; the only
correction is that the realizer-uniqueness lemma already existed as
`totalNabla0SRealizes_unique`).  `ricciDiff_eq_trace` gives
`Ric₁ − Ric₂ = tr_{g₁}(S₀₄ ∘ rm04TraceSlots)` pointwise with **no residual `h₀₂` term**, hence as
bundled fields by `DFunLike.ext`; `nablaRealizes_metricTraceFirstTwo`
(`Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`) commutes `∇` past the trace up to
`traceNablaShuffle`; a realizer-uniqueness step identifies the result with `metricNabla0S`
(`TotalNabla0SRealizes` is pointwise on `Fin.cons (X x) slots`, so two realizers agree via
`ContMDiffSection.exists_eq_at` — this small lemma does not yet exist and is the first thing to
write); then `traceNormSq_le` at `s = 3` gives the `n⁵` and `normSq0S_domDomCongr` absorbs both
reindexings.  Needs `[I.Boundaryless]` (authorized, R9(a); **not yet added**, since nothing in
the file requires it until this step) and the field-level `MultilinearSection.domDomCongr`
plumbing that `ForwardUniqueReLower.nabla_reLower_eval` already exercises.

---

## Outcome (historical: after pass 2)

**(B) — repaired statement, Layer A proved, ONE `sorry` on a strictly reduced goal.**

Two passes on 2026-07-26:

1. **The audit pass** found `connSpeedLow_normSq_le` **FALSE as stated** and reported rather
   than patching (§"The frontier was false" below — kept as the permanent record).
2. **The repair pass** (planner ruling **R8**, which approved the statement change) restated
   `connSpeedLow_normSq_le` and the in-file capstone `connDiffDot_normSq_le` with the honest K1
   Hamilton input, and proved Layer A.

**Now green:** `coeff_adot_eq` (uniqueness of derivatives pins the frame coefficients of `Adot`
from `hΓ` — this is what makes the Hamilton input bite, and is the structural discharge of the
falsity), `lower_raise_cancel` (the "structural gift": lowering with a metric cancels that
metric's own inverse-metric raising), `connSpeedLow_eq` (the splitting identity), plus
`normSq0S_sub_le`, `lowerBilin_basis`, `repr_bilinOfComp`, and the audit pass's
`connSpeedRHS_self`.  `connSpeedLow_eq` is **on the proof path** of the frontier: the `sorry`
now sits on `2·|g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·)|² + 2·|h₀₂(Γ̇₂·,·)|² ≤ RHS`, not on the original goal.

914 lines; 16 public declarations (3 `def`, 13 `theorem`), 11 `private` helpers; **exactly one
`sorry`**, in `connSpeedLow_normSq_le`.  Focused check GREEN and targeted module build GREEN and
**warning-clean** apart from the expected `uses sorry`.  (Two `unusedDecidableInType` warnings
appeared only in the `lake build` output, not in the focused `check` — the build runs linters
the focused check does not, so a final targeted build is required to certify warning-cleanliness.
Fixed by dropping the unneeded `[DecidableEq Idx]` from `repr_bilinOfComp` and
`connSpeedLow_eq`; `classical` already supplies it inside the proofs.)

**Honest correction to the audit pass's "Defect 2".**  The audit predicted both `|Ric₂|²` and
`|Rm₂|²` would be needed.  Working the route out showed `ricciDiff_eq_trace` has **no residual
`h₀₂` term** (both flows are lowered *and* traced with `g₁`), so only `B₃ ≥ |Ric₂|²` is actually
consumed.  `B₄ ≥ |Rm₂|²` was added as instructed and is retained for the downstream `adotLe`
wiring, but this route does not use it (nor `B₂`).  Unused-but-monotone hypotheses only weaken
the theorem, so they are harmless — but drop them if the wiring turns out not to want them.

## The repaired statement (ruling R8)

Added to `connSpeedLow_normSq_le` and mirrored on `connDiffDot_normSq_le`:

* a local frame `{Idx} [Fintype] [DecidableEq] {u}`, `frame`, `hframe`, `hu`, `hx` — the frame
  the K1 producer works in;
* `Ric₁` + `hRic₁` alongside the existing `Ric₂` + `hRic₂` (needed even to *state* the trace
  step: `Ric₁ − Ric₂` must exist as a bundled field to be differentiated);
* `gInv₁`, `gInv₂` with `hgInv₁`, `hgInv₂` (`MetricInverseInBasis_gen` at `x` in
  `hframe.toBasisAt hx`) and `nablaRic₁`, `nablaRic₂` with `hNR₁`, `hNR₂` pinning them to
  `component0S` of `metricNabla0S gₐ Ricₐ x` (derivative slot `0`);
* **`hΓ`** — `HasDerivAt` of the Christoffel-symbol difference with derivative
  `christoffelEvolutionRHSInFrame gInv₁ nablaRic₁ − christoffelEvolutionRHSInFrame gInv₂
  nablaRic₂`, i.e. verbatim the conclusion of `ChristoffelEvolutionEquationInFrameOn`;
* `hB₃ : |Ric₂ x|²_{g₁} ≤ B₃`, `hB₄ : |Rm₂ x|²_{g₁} ≤ B₄`, and `B₃ + B₄` in the right-hand
  sum;
* constant resized `9 n⁶ → 100 n⁶` (provisional and generous — resize again when the two norm
  reductions land).

`hA` is **kept** as the realisation link (it is what `HasDerivAt.unique` runs against).
`hRF₁`/`hRF₂` are kept for interface stability; this proof consumes them only through `hΓ`.

**Import added:** `Evolution.ForwardUniqueRatePro` (for `ricciDiff_eq_trace`, and it re-exports
`ForwardUniqueRmBounds`, so that import was replaced rather than added) and
`Evolution.Connection.Components` (for `christoffelEvolutionRHSInFrame`).  No cycle: neither
imports this file.

## Layer A, proved (the mathematical heart)

```
coeff_adot_eq :  hframe.coeff k x (Adot x (frame j x) (frame i x)) = c i j k
```
from `hA` (vector-valued `HasDerivAt`) composed with the coordinate functional `b.coord k`,
against `hΓ`, by `HasDerivAt.unique`.  This is the **converse** of
`ForwardUniqueConnDot.connDiffVec_hasDerivAt` (which goes components → invariant), and the
`hdiff`/`hfun` frame computation is lifted from that proof.

```
lower_raise_cancel :  ∑ m, (∑ l, gInv m l * L l) * g.inner x (b m) (b k) = L k
```
the structural gift, from the **second** conjunct of `MetricInverseInBasis_gen` plus `g.symm`.
Stated for an arbitrary lowered family `L`, so it serves either flow.

```
connSpeedLow_eq :  lowerBilin g₁ (Adot x)
                     = lowerBilin g₁ Γ̇₁ − lowerBilin g₂ Γ̇₂ − lowerBilin h₀₂ Γ̇₂
```
with `Γ̇ₐ = bilinOfComp (hframe.toBasisAt hx) (christoffelEvolutionRHSInFrame gInvₐ nablaRicₐ)`.
Proof: `Module.Basis.ext_multilinear` at `s = 3` (the RatePro pattern) + `lowerBilin_basis`
(`lowerBilin_apply` then `tensor02_expand`) + `repr_bilinOfComp`, then scalar `ring` — the
identity is *purely* `g₁ = g₂ + h₀₂`, so no inverse metric is needed for the splitting itself.
`lower_raise_cancel` is what later turns each `lowerBilin gₐ Γ̇ₐ` into the lowered Hamilton sum
`Lₐ(i,j,k) = −∇_iRicₐ_{jk} − ∇_jRicₐ_{ik} + ∇_kRicₐ_{ij}`.

## What is left inside the single `sorry`

After `rw [connSpeedLow_eq …]` and `normSq0S_sub_le` the goal is
`2·|T₁ − T₂|² + 2·|Def|² ≤ 100 n⁶ (…)`, and two reductions remain.

1. **Contracted trace.**  `lower_raise_cancel` makes `T₁ − T₂` the permutation sum
   `−T − T∘(0 1) + T∘(0↦2,1↦0,2↦1)` of `T = ∇¹Ric₁ − ∇²Ric₂`; `normSq0S_domDomCongr`
   (`Tensor/RSTensor/NormSqProduct.lean`) makes each summand isometric, `nablaRicDiff_le`
   (green here) splits off `8n³·|A₀₃|²·|Ric₂|²` — this is what `B₃` is for — and
   `∇¹(Ric₁ − Ric₂) = tr_{g₁}(∇¹S₀₄)` comes from `ricciDiff_eq_trace` plus
   `nabla_metricTraceFirstTwo0S` / `traceNablaShuffle`, closed by `traceNormSq_le` at `s = 3`
   (`n⁵`).  **Risk:** `nabla_metricTraceFirstTwo0S` needs `[I.Boundaryless]` (not in this
   file's variable block — it would be a new typeclass *hypothesis*, flagged) and is stated in
   `totalNabla0SFun` terms, and the reindexed `(0,4)` object must be built as a bundled
   *smooth* `Tensor0SField`; `ForwardUniqueReLower.lean` has the `totalNabla0SFun_domDomCongr`
   plumbing for exactly this.
2. **`Φ`-defect.**  `lowerBilin_normSq_le` (green here) gives
   `|Def|² = |h₀₂(Γ̇₂·,·)|² ≤ |h₀₂|²·|g₁(Γ̇₂·,·)|²`, so what is missing is
   `|g₁(Γ̇₂·,·)|²_{g₁} ≤ Λ²·|g₂(Γ̇₂·,·)|²_{g₁}`.  **The one-sided `hΛ` suffices**, at cost `Λ²`:
   in a `g₁`-orthonormal frame at `x` the left side is `∑_{ij}|Γ̇₂(e_j,e_i)|²_{g₁}`, and for
   `ω = L₂(i,j,·)`,
   `|g₂^♯ω|²_{g₁} ≤ Λ|g₂^♯ω|²_{g₂} = Λ|ω|²_{g₂^{-1}} ≤ Λ²|ω|²_{g₁^{-1}}`
   (the first step is `hΛ` on vectors, the last is `g₁ ≤ Λg₂ ⟹ g₂^{-1} ≤ Λg₁^{-1}` on
   covectors).  The missing API is a **slot-precomposition norm bound**; its home is
   `Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean`, next to `normSq0S_upper_le_of_equiv`
   and `normSq0S_le_of_metric_equiv`.

**Correction to the planner's fallback wording:** the residual risk is *not* concentrated on
the trace step.  Reduction 2 is at least as large, because it needs new API rather than
plumbing of existing lemmas; reduction 1 is mostly plumbing plus one typeclass hypothesis.

## What is proved

### 1. The named `∇¹S₀₄` carrier (green)

* `IsRmDiffField g₁ g₂ S` — the realisation predicate `∀ x, S x = rmDiffLowAt g₁ g₂ x`.
* `nablaRmDiff g₁ S = metricNabla0S g₁ S` — the `(0,5)` field `∇¹S₀₄`.
* `nablaRmDiffSq g₁ S x = normSq0S g₁ x 5 (nablaRmDiff g₁ S x)` — the ruling's fourth integrand.
* `nablaRmDiffSq_nonneg`, `nablaRmDiffSq_self` (equal metrics ⟹ the integrand vanishes; this is
  the sanity check that the carrier really is a difference).

**Design decision.**  `S₀₄` is a *supplied* field pinned by a realisation equation, not a
constructed one — exactly the pattern `ForwardUniqueRmDiff.lean` uses for `Rm2`
(`rm2Low_eq_sub`).  Constructing the field would require the joint smoothness of
`x ↦ rmDiffLowAt g₁ g₂ x`, which is the producer's business (and is the same `hdens`-flavoured
debt K3 already records); manufacturing it here would have been a fake.

### 2. The lowering-contraction bound (green) — gaps (2)+(3) discharged together

```
lowerBilin_normSq_le :
  normSq0S g x 3 (lowerBilin q A) ≤ normSq0S g x 2 q * normSq0S g x 3 (lowerBilin (g-tensor) A)
```

**This one statement replaces both** of the `ForwardUniqueConnDot.md` gaps (2) "lowering with
`g₁` is a fibre isometry" and (3) "contraction bound for a general `(0,2)` lowering".  Instead
of introducing a mixed-variance `normSqRS` norm for the `(1,2)` object and then proving the
`g`-lowering is an isometry onto it (which is what `RSLoweringNorm.normSqRS_eq_normSq0S_lowerAllSpace`
would give — but its producer carries the model-space `[InnerProductSpace ℝ E]` taint the lane
keeps flagging), it compares the two *lowerings* directly.  Constant is sharp (`1`).
No isometry framework, no new norm, no `omit` repair needed.

`connDiffLow_eq_lower` identifies `connDiffLowAt g₁ g₂ x = lowerBilin (metricTensorField g₁ x) Δ`,
so the right-hand factor at `A = ∇¹−∇²` *is* `connDiffSq`.

### 3. The main bound

* `connDiffDot_le_speed` (**green**):
  `|∂ₜA₀₃|²_{g₁} ≤ 8·Λric·connDiffSq + 2·|g₁(Adot ·,·)|²`, with `Λric` a named background bound
  on `|Ric₁|²`.  Route: `normSq0S_add_le` (the №11 kit) + `normSq0S_smul` (the `(-2)` gives `4`)
  + `lowerBilin_normSq_le` + `connDiffLow_eq_lower`.
* `nablaRicDiff_split` / `nablaRicDiff_le` (**green**): the first half of the `∇Ric`-difference
  consumption — `∇¹Ric₁ − ∇²Ric₂ = ∇¹(Ric₁ − Ric₂) + (∇¹−∇²)Ric₂`, with the flux summand
  bounded by `8n³·connDiffSq·|Ric₂|²` via the existing `fluxNormSq_le` at `s = 2`.  Stated for
  arbitrary `(0,2)` fields (no Ricci realisation needed), hence reusable.
* `connSpeedRHS_self` (**green**, added 2026-07-26): if `g₁ t = g₂ t` then the *entire*
  right-hand side of `connSpeedLow_normSq_le` is `0`, for every `Λ`, `B₁`, `B₂`.  Route:
  `rw [hg]` at `hS` and the goal, then `nablaRmDiffSq_self` + `metricDiffAt_self` +
  `connDiffLowAt_self` + `(tensor0SMetricData …).inner_self_eq_zero_iff` + `ring`.  This is a
  `_self` sanity lemma in the file's existing idiom *and* the formal half of the counterexample
  below.
* `connSpeedLow_normSq_le` (**the one `sorry`** — and ⚠ **false as stated**) — see below.
* `connDiffDot_normSq_le` (proved *from* the above, hence **inheriting the false frontier**):
  the capstone in the ruling's shape,
  `|∂ₜA₀₃|² ≤ 8Λric·|A₀₃|² + 2C(n)(|∇¹S₀₄|² + (1+Λ)²(B₁+B₂)(|h₀₂|² + |A₀₃|²))`.

## The frontier WAS false (`connSpeedLow_normSq_le`) — 2026-07-26 audit pass

**Permanent record — the statement below has since been repaired under ruling R8** (see §"The
repaired statement" above).  Kept in full because the counterexample is the justification for
the added `hΓ` input, and because the degenerate-collapse test that found it is reusable.

**Classification: wrong statement.**  Not a missing lemma, not a routing problem, not a
typeclass issue.  Two independent defects; the first alone is fatal.

### Defect 1 (fatal) — the hypotheses do not determine `Adot`

`hA` says only that `Adot x` is the `t`-derivative of `r ↦ CovariantDerivative.difference
(metricCov (g₁ r)) (metricCov (g₂ r)) x Y X`, and `hRF₁`/`hRF₂` pin `∂ₜg₁`, `∂ₜg₂`
**pointwise in space**.  Recovering `∂ₜΓ` from `∂ₜg` interchanges `∂ₜ` with a *spatial*
derivative; that is a Schwarz/Clairaut step and needs joint `(t, y)` regularity.  Nothing in
the hypothesis list supplies it.  This is exactly why the repo's producer
`christoffelEvolution_of_solution`
(`Evolution/Connection/MetricCovDerivProducer.lean:203`) demands, on top of a `SolutionOn` +
`IsSolutionOn` pair, the three regularity inputs

* `hSmooth : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) 2 (fun p : ℝ × M => (metric p.1).inner p.2 …)`
* `hFdiff`, `hFtdiff` (spatial `MDifferentiableAt` of the metric and of the Ricci components)

plus the `MetricFrameTimeRegularityInFrameOnLocal` black box.  **None of these is derivable
from `hRF₁`/`hRF₂`.**  So the planner's suggested route ("frame producer + `HasDerivAt.unique`")
cannot start: `SolutionOn` is *data*, and the joint regularity is a genuinely new assumption.

**Counterexample.**  `SmoothRiemannianMetric` is a per-time object and `g₁ : ℝ → …` carries no
joint regularity whatsoever, so the gap is real, not bookkeeping.  Take `t = 0`, `M = ℝⁿ`,
`x = 0` and

```
w r y  = r³y/(r² + y²)   (w 0 y = 0)          χ = bump, ≡ 1 near 0, supp ⊆ [−1,1]
g₂ r   ≡ δ
g₁ r   = (1 + ε · χ r · w r y₁) · δ           (ε = 1/2)
```

* each `g₁ r` is a genuine smooth Riemannian metric (`|w| ≤ r²/2 ≤ 1/2` on `supp χ`, and
  `y ↦ w r y` is `C^∞` for every fixed `r`, including `r = 0` where it is `0`);
* `g₁ 0 = δ = g₂ 0`, so **all three difference carriers vanish** and `S ≡ 0`, hence the whole
  right-hand side is `0` — this half is now machine-checked as `connSpeedRHS_self`;
* `∂ᵣ w 0 y = 0` for **every** `y` (for `y ≠ 0`, `w r y / r = r²y/(r²+y²) → 0`; for `y = 0`,
  `w r 0 = 0`).  Since `Ric_δ = 0`, `hRF₁` and `hRF₂` both hold at `t = 0` with both sides `0`;
* but `∂_y w r 0 = r³(r²−0)/(r²)² = r`, so at the origin `g(r,0) = δ` exactly while
  `∂_b g_{dc}(r,0) = ε χ r · r · δ_b¹ δ_{dc}`, giving
  `Γ^a_{bc}(r,0) = ½ ε χ r · r · (δ_b¹δ_{ac} + δ_c¹δ_{ab} − δ_a¹δ_{bc})`.
  This is differentiable in `r` at `0` with derivative `½ε(…) ≠ 0` (e.g. `a=b=c=1` gives `½ε`),
  so `hA` holds with `Adot x ≠ 0`.

Conclusion: LHS `> 0`, RHS `= 0`.  The mechanism is precisely the failure of Schwarz for `w`:
`∂ᵣ∂_y w 0 0 = 1 ≠ 0 = ∂_y∂ᵣ w 0 0`.

Note the counterexample only uses the degenerate configuration `g₁ t = g₂ t`; **any** repaired
statement must explain why `∂ₜ∇¹ = ∂ₜ∇²` when the two metrics agree at `t`, and only joint
regularity does that.

### Defect 2 — the background bundle `B₁, B₂` is too small

**Evidentiary status (be honest about the difference).**  Defect 1 is a *disproof*: an explicit
family satisfying every hypothesis with the conclusion failing, half of it machine-checked.
Defect 2 is weaker — it says the natural derivation *produces* two carriers that no hypothesis
bounds, and I did not construct a counterexample isolating it.  There is no visible cancellation
(the flux `(∇¹−∇²)Ric₂ = A₀₃ ⋆ Ric₂` is a genuine term, and the file's own green
`nablaRicDiff_le` already exhibits `|Ric₂|²` on its right-hand side), so the repaired statement
should carry the extra norms; but a cleverer route that avoids them is not formally excluded.

Independent of Defect 1, and visible from the green in-file lemmas.  With Hamilton's formula
available, lowering `∂ₜΓ` for each flow by `g₁` gives

```
g₁(Adot(Y,X), Z) = (L₁ − L₂)(X,Y,Z) + L₂(X, Y, (1 − Φ)Z),
Lₐ = −∇^aRic_a(X;Y,Z) − ∇^aRic_a(Y;X,Z) + ∇^aRic_a(Z;X,Y),   Φ = g₂^♯ ∘ g₁^♭.
```

* the `Φ`-defect summand is `O(B₁ · |h₀₂|²)` — covered, and `hΛ` (`g₁ ≤ Λ g₂`, i.e.
  `g₂^{-1} ≤ Λ g₁^{-1}`) is the *correct* one-sided direction for `|1 − Φ| ≲ Λ|h₀₂|`;
* `L₁ − L₂` goes through `nablaRicDiff_split`, whose flux summand is bounded by
  `nablaRicDiff_le` — and that bound's right-hand side contains `normSq0S g₁ x 2 (Ric₂ x)`,
  i.e. **`|Ric₂|²`, which no hypothesis bounds**;
* the contracted trace of `∇¹(Ric₁ − Ric₂)` produces `∇¹((g₁^{-1} − g₂^{-1}) ⋆ Rm₂)`, and
  `∇¹h₀₂ = −∇¹g₂ = (∇¹−∇²)g₂` is again an `A₀₃`-flux, giving `|A₀₃|²·**|Rm₂|²**`.

So the right-hand side needs two further named background norms, `B₃ ≥ |Ric₂|²_{g₁}` and
`B₄ ≥ |Rm₂|²_{g₁}` (a single `B₄` may suffice up to `n`, since `Ric₂` is a `g₂`-trace of `Rm₂`,
but that trace bound is itself a missing lemma).  The file's own sibling `connDiffDot_le_speed`
already carries the analogous zeroth-order bound `Λric ≥ |Ric₁|²`; the frontier simply omitted
the `g₂` counterparts.

### The repair (proposed by the audit pass; APPLIED under ruling R8)

Keep the conclusion's shape, add the two background norms, and replace the insufficient `hA`
by the K1 input the lane actually produces (keeping `hA` as the realisation link).  In the
existing frame vocabulary of `ForwardUniqueConnDot.connDiffVec_hasDerivAt`:

```lean
{Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
(frame : Idx -> (y : M) -> TangentSpace I y)
(hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u)
(gInv₁ gInv₂ : Real -> InverseMetricComponents M Idx)   -- pinned to g₁ t, g₂ t at x
(nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)  -- pinned to ∇^a Ric_a
(hΓ : ∀ i j k : Idx,
  HasDerivAt (fun r : Real => christoffelSymbolInFrame (metricCov (g₁ r)) frame hframe x i j k -
                              christoffelSymbolInFrame (metricCov (g₂ r)) frame hframe x i j k)
    (christoffelEvolutionRHSInFrame gInv₁ nablaRic₁ t x i j k -
     christoffelEvolutionRHSInFrame gInv₂ nablaRic₂ t x i j k) t)
```

`hΓ` is precisely the conclusion of `ChristoffelEvolutionEquationInFrameOn`
(`Evolution/Connection/Christoffel.lean:142`), discharged from a solution pair by
`christoffelEvolution_of_solution`, so it is an honest lane input and *not* a restatement of the
conclusion (which is a norm bound).  `HasDerivAt.unique` against `hA` then pins
`hframe.coeff k x (Adot x (frame j x) (frame i x))`.

**Structural gift found while scoping this.**  `christoffelEvolutionRHSInFrame gInv nablaRic =
∑ₗ gInv k l · christoffelVariationLoweredRHSInFrame nablaRic i j l`, and
`christoffelVariationLoweredRHSInFrame nablaRic i j l = −∇_iRic_{jl} − ∇_jRic_{il} + ∇_lRic_{ij}`
by `rfl` (see the `christoffelRHS_id` proof, `Evolution/Connection/Components.lean:80`).  So
**lowering the flow-1 half back with `g₁` cancels the `gInv₁` raising exactly** — no inverse
metric survives on the `g₁` side.  Only the flow-2 half carries `Φ = g₂^♯∘g₁^♭`, which is the
`sharpFlat`/`reLower` operator already built in `Evolution/ForwardUniqueReLower.lean`
(`sharpFlat_eq_raise`, `reLower_rm04`).  That is the cheapest route through Defect 2's algebra.

### Remaining ingredient after the repair (unchanged from the earlier note)

**The contracted trace `∇Ric = tr_g(∇Rm)`.**  This is *not* second Bianchi.
`curvSecondBianchi` (`Geometry/Curvature/Bianchi.lean:820`) is a proved operator-level theorem,
but the route never needs it — the identity required is the commutation of `∇` past a metric
trace (`nabla_metricTraceFirstTwo0S`, `traceNablaShuffle` in `MetricTrace/NablaTraceGen.lean`),
which holds because `∇g = 0`.  What blocks it today is *slot bookkeeping*: `metricRicciAt` is
`ricciFromRm13At` of the **(1,3)** tensor (`metricRicciAt_eq_trace`,
`Geometry/Curvature/Metric.lean:104`), and the bridge to the metric trace of the **(0,4)**
tensor exists only at the component level (`ricciFromRm13_comp_eq_rm04_trace`,
`Curvature/Components/RicciTrace.lean:96`; `ricciComp_eq_trace_rm04`,
`Curvature/Components/LocalFrame.lean:144`), both with `hLower` hypotheses.

**~~Smallest missing API~~ — SUPERSEDED.**  The audit pass called for a new tensor-level
`Ric = tr_g(Rm₀₄)` in `Geometry/Curvature/`.  **It already exists** and the audit missed it:
`ricci_eq_trace_rm04` and `ricciDiff_eq_trace` in `Evolution/ForwardUniqueRatePro.lean`, with
`rm04TraceSlots` the `(0,1,2,3) ↦ (0,2,3,1)` permutation carrying the trace pair `(0,3)` onto
the leading pair, built for K4's rate capstone.  `ricciDiff_eq_trace` is exactly the shape the
trace step needs and, better than expected, carries **no residual `h₀₂` term**.  Lesson: the
audit's "smallest missing API" scan searched `Geometry/Curvature/` (where the concept belongs)
but not the sibling `Evolution/` files (where the lane had already put it).

**The displayed dimensional constant is provisional** — the shape of the right-hand side is the
interface; raise the constant freely when the proof lands.  Currently `100 n⁶`.

### Why the audit pass changed no statement

The brief made the hypothesis list an audited interface and instructed a stop-and-report if the
producer needed unavailable inputs.  The repair was also a genuine design choice (which frame
vocabulary, how many background norms, whether `Adot` survives as an argument).  Nothing outside
this file consumes `connSpeedLow_normSq_le` or `connDiffDot_normSq_le` — verified by grep over
`DifferentialGeometry/` for `connDiffDot_normSq_le`, `connSpeedLow_normSq_le`, `nablaRmDiffSq`,
`IsRmDiffField`: **zero hits outside this file** — so the repair was free of downstream
breakage, and the planner authorized it as ruling R8 in the following pass.

## Lean lessons (durable)

* **`n + k` vs a literal: put the literal in an explicitly-typed `have`, never in a `rw`.**  The
  whole friction of the trace step is that `traceNormSq_le` is stated at `s + 2` and produces
  `(s+1)+2` / `3+2` where the goal reads `s+3` / `5`.  These are defeq (`Nat` literal/offset
  arithmetic), so `exact`, `refine … ?_` and an annotated `have` all accept them silently —
  but `rw` and `simp only` need *syntactic* agreement and will fail or hit a
  "motive is not type correct" when the index sits in a dependent position such as
  `normSq0S g x s T`.  The working discipline: state each intermediate step as a `have` with the
  index written the way the *goal* writes it, prove it by a bare application of the general
  lemma, and let `exact` do the arithmetic.  Choosing `s + 2 + 1` (rather than `s + 3`) as the
  house form of the derivative rank made every application match syntactically, because
  `metricNabla0S g A : (0, (s+2)+1)` already prints that way.
* **Grep the *concept* before writing a "missing" lemma — fourth time in this lane.**  The
  realizer-uniqueness step was scoped as "this small lemma does not yet exist and is the first
  thing to write".  It exists twice: `totalNabla0SRealizes_unique`
  (`Tensor/RSTensor/NablaDomDomCongr.lean`) and a copy in `HCGCompactness/ProductMFoldNorm.lean`.
  A one-line `grep -rn "Realizes.*unique\|_realizes_eq"` over `Tensor/` + `Geometry/` found both
  in seconds.  Likewise the `∇`-past-reindexing half needed no realizer argument at all:
  `totalNabla0SFun_domDomCongr` states it at the fibre level, and `metricNabla0S g T x` is `rfl`
  for `totalNabla0SFun s (metricCov g) T x`, so it applies directly.
* **`Realized.lean`'s `canRicNabla`-style block is the template for any `∇`-through-a-trace
  argument.**  `Geometry/Connection/LeviCivita/Curvature/Realized.lean:1100–1180` runs exactly
  this chain (`totalNabla0S_realizes` → `totalNabla0SRealizes_domDomCongr` →
  `nablaRealizes_metricTraceFirstTwo` → `totalNabla0SRealizes_unique`) for `∇Ric = tr(∇Rm)`.
  Reading it first turned a scoped-as-hard step into ~25 lines that compiled on the first check.
* **`metricCov`'s regularity/compatibility producers are reachable by defeq, so skip the
  wrapper.**  `have hcov1 := leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
  (I := I) (M := M) g` (no type ascription) passes straight into a slot expecting
  `ContMDiffCovariantDerivativeLocally (metricCov g) 1`: `metricCov` is a `def` for
  `leviCivitaConnectionOfMetric`, and `exact` unfolds `def`s.  `ForwardUniqueReLower.lean`'s
  `private metricCov_one` (a `simpa [metricCov]` wrapper) is not needed, and writing an
  annotated `have` would have forced naming `CovariantDerivative.ContMDiffCovariantDerivativeLocally`
  in a file that does not `open DifferentialGeometry.Integral.Connection`.
* **This file deliberately does *not* `open DifferentialGeometry.Integral.Connection`,** unlike
  every sibling (`RatePro`, `RmDiff`, `ReLower`, `RmBounds`).  Adding the `open` would make
  `metricCov` ambiguous with the local `PDE.RicciFlow.metricCov` abbrev across 1400 lines; the
  cheap, zero-blast-radius alternative is to fully qualify the five or six names actually needed
  (`metricTraceFirstTwoField`, `traceNablaShuffle`, `nablaRealizes_metricTraceFirstTwo`,
  `leviCivitaConnectionOfMetric_*`).  `frontExtendEquiv`, `totalNabla0S_realizes`,
  `totalNabla0SRealizes_unique`, `totalNabla0SFun_domDomCongr` need no prefix — they live in
  `Tensor0SBundle`, which the file already opens.
* **`Tensor0SSpace` arithmetic needs the expected type at elaboration time; a type ascription is
  not enough.**  Writing `(-1:ℝ) • N + (T.domDomCongr e : Tensor0SSpace … 3 x)` fails with
  `failed to synthesize HAdd (Tensor0SSpace 3 I x) (ContinuousMultilinearMap …)` — the ascription
  does not stop `domDomCongr` from elaborating as a bare `ContinuousMultilinearMap`, and the `+`
  then has mismatched operands.  The fix is a **thin typed wrapper `def`** whose declared return
  type forces the elaboration (`perm3 e N : Tensor0SSpace … 3 x := N.domDomCongr e`); then all
  the module arithmetic resolves.  This is why `hamSum` exists as a named object at all.
* **Keep `nlinarith` away from tensor atoms.**  Inlining the final constant bookkeeping — where
  the atoms are `normSq0S … (lowerBilin … (bilinOfComp …))` terms — timed out at `isDefEq`/`whnf`
  (200 000 heartbeats), *not* in the polynomial search.  Factoring the arithmetic into a
  standalone lemma over plain reals (`connSpeed_arith`) made it instant.  Corollary: when a
  geometric proof ends in a messy inequality, extract the inequality as a real-number lemma
  first.  The file-level `set_option backward.isDefEq.respectTransparency false` makes this
  failure mode more likely, not less.
* **`nlinarith` on a many-variable polynomial goal is a last resort even for pure reals.**  The
  first version of `connSpeed_arith` still timed out with 17 real variables; rewriting every step
  as an explicit `mul_le_mul_of_nonneg_*` / `le_mul_of_one_le_left` chain followed by a single
  `ring`-rewrite and `linarith` made it cheap.  `nlinarith` survives only for the three genuinely
  quadratic facts (`1 ≤ (1+Λ)²` etc.).
* **`↑(0 : ℕ) ^ a` is not `(0 : ℝ) ^ a` to `rw [zero_pow]`.**  After `rw [h0]` with
  `h0 : Module.finrank ℝ E = 0`, the goal carries `(↑(0:ℕ) : ℝ)`; insert `simp only [Nat.cast_zero]`
  before `zero_pow`.  Cost one round trip.
* **`Equiv.swap` on `Fin 3` does not reduce under bare `simp`.**  `Equiv.swap (0:Fin 3) 1 2 = 2`
  needs `simp [Equiv.swap_apply_def]`; `Equiv.swap_apply_of_ne_of_ne` is reported as an unused
  simp argument because it never fires without the `≠` side conditions in scope.
* **To prove a `(0,s)` fibre-tensor identity, go through basis components, not `ext`.**  The
  working pattern (lifted from `ForwardUniqueRatePro.ricci_eq_trace_rm04` and reused verbatim
  for `connSpeedLow_eq` at `s = 3`): `refine tensor0SSpace_ext (𝕜 := Real) s x fun w => ?_`,
  then `set L := …`, `set R := …`, then
  `suffices h : L.toMultilinearMap = R.toMultilinearMap by exact congrArg (fun T => T w) h`,
  then `refine Module.Basis.ext_multilinear (e := fun _ => b) ?_` and `change L (fun a => b (v a))
  = R (fun a => b (v a))`.  You cannot apply `ext_multilinear` to the bundled `Tensor0SSpace`
  directly; the `suffices` is what unbundles it.  Evaluating a `sub` of tensors on the way needs
  explicit `Tensor0SSpace.sub_apply` rewrites (never `simp` through the FunLike coercion).
* **`HasDerivAt.unique` is the tool for consuming a supplied "speed" object.**  When a statement
  supplies an object `Adot` *and* a hypothesis saying it is the derivative of a curve, and a
  producer gives the same curve's derivative in another form, compose the vector-valued
  `HasDerivAt` with a coordinate functional
  (`(LinearMap.toContinuousLinearMap (b.coord k)).hasFDerivAt.comp_hasDerivAt`) and run
  `HasDerivAt.unique` against the producer.  `coeff_adot_eq` is the reusable instance; it is the
  exact converse of `ForwardUniqueConnDot.connDiffVec_hasDerivAt`, and the frame computation
  (`IsCovariantDerivativeOn.difference_apply` → `christoffelSymbolInFrame_eval` → `map_sub`) can
  be lifted from that proof unchanged.
* **`MetricInverseInBasis_gen` has two conjuncts and you usually want the second.**  Conjunct 1
  sums `gInv`'s *second* index, conjunct 2 sums its *first*.  `christoffelEvolutionRHSInFrame`
  raises with `gInv k l` (raised index first), so pairing back against the metric needs conjunct
  2 plus `g.symm x _ _` — there is no need to assume `gInv` symmetric.  That is the whole content
  of `lower_raise_cancel`.
* **Search the sibling lane files, not only the canonical layer, before declaring an API
  missing.**  The audit pass called for a tensor-level `Ric = tr_g(Rm₀₄)` in
  `Geometry/Curvature/`; it already existed in `Evolution/ForwardUniqueRatePro.lean`
  (`ricci_eq_trace_rm04`, `ricciDiff_eq_trace`).  Grep the *concept* across the whole tree, not
  the directory where the concept ought to live.
* **Audit a pointwise-in-time PDE statement by collapsing every carrier before trying to prove
  it.**  The frontier's falsity was found in minutes, not by attacking the proof, but by asking
  "what does the statement say when all difference carriers vanish?".  For a bound whose
  right-hand side is built only from difference carriers, the degenerate configuration
  `g₁ t = g₂ t` forces the left-hand side to `0`; if the hypotheses do not *also* force that,
  the statement is false.  This test is cheap, is machine-checkable (`connSpeedRHS_self`), and
  should be run on every new pointwise-estimate frontier in the K-lane before any effort goes
  into filling its `sorry`.
* **`g : ℝ → SmoothRiemannianMetric I M` carries NO joint `(t, y)` regularity.**  Each `g r` is
  smooth *in space*; the family is an arbitrary function of `r`.  Any statement that needs
  `∂ₜ` to commute with a spatial derivative — every `∂ₜΓ`, `∂ₜRm`, `∂ₜRic` identity — must take
  the joint regularity as an explicit input, which is exactly what the `SolutionOn`/
  `IsSolutionOn` packaging and the `hSmooth`/`hFdiff`/`hFtdiff` triple exist for.  A pointwise
  `HasDerivAt (fun r => (g r).inner y X Y) … t` at every `y` is *not* a substitute: the standard
  Schwarz counterexample `w r y = r³y/(r²+y²)` sits entirely inside that hypothesis.
* **`Equiv.sum_comp` + `Fintype.sum_prod_type` reindexes a `(Fin k → Idx)` component sum into a
  `k`-fold iterated sum**, which is what makes slot-factorised estimates possible on
  `normSq0S_identity_eq_sum_sq`.  The pattern is: build the `Equiv` with `if`-chains (NOT
  `Matrix.vecCons` — `![a,b,c] 2` does not reduce by `rfl`), `left_inv`/`right_inv` by
  `funext`+`fin_cases`+`simp` / `simp`.  The closing step needs an **explicit `rfl` tactic**:
  the `rfl` that `rw` attempts is at reducible transparency and does *not* unfold the private
  `Equiv` def, so `rw [h, Fintype.sum_prod_type]` leaves a goal that a following bare `rfl`
  closes immediately.  (Cost me one round trip; `sumSlots2`/`sumSlots3` are now reusable.)
* `congr 1` on a `Tensor0SSpace` evaluation can close the whole goal (the slot-map arguments
  come out defeq), so a following `funext`/`by_cases` block errors with "No goals".  Try
  `congr 1` alone first.
* The `unusedFintypeInType` linter fires on `[Fintype Idx]` even when the *statement* needs it
  through `component0S` (which takes it from its own section variable).  For `comp_lowerBilin`
  removing it is a hard error; the correct response there is the file-level
  `set_option linter.unusedFintypeInType false` (the same one `ForwardUniqueConnDot.lean`
  carries).  For `repr_inner`, whose statement really does not need it, the linter's advice
  works: `[Finite Idx]` + `haveI : Fintype Idx := Fintype.ofFinite Idx` (the `absBasis_le`
  house pattern).
* The `linter.style.show` linter rejects a `show` that changes the goal even up to defeq — use
  `change`.
* **Two `private` helpers are duplicated from `ForwardUniqueRmBounds.lean`** (`exists_onFrame`,
  `onFrame_inv`) because they are `private` there.  Same situation as `RmBounds` itself
  re-proving `innerSelfNonneg`/`metricCS`.  Campaign-end cleanup: promote the orthonormal-frame
  existence + identity-inverse witness to a public pair in
  `Tensor/RSTensor/Tensor0SRiemannian/` — by my count this is now the **third** copy in the tree
  (RmBounds, here, and the inline `letI` block inside `TensorRSRiemannian.sqrt_normSqRS_apply`).

## Reuse audit (what was found and used)

* `Tensor0SMetricIneq.lean` (№11 kit): `normSq0S_add_le`, `normSq0S_nonneg` — used, no
  duplication.  Gap (1) confirmed discharged.
* `Tensor0SRiemannian/Scaling.normSq0S_smul` — used for the `(-2)` factor (the layering wart
  noted in №11 is real but not worth touching from here).
* `Tensor0SRiemannian/Comparison.normSq0S_identity_eq_sum_sq` — the orthonormal component sum.
* `ForwardUniqueRmBounds.fluxNormSq_le` — reused verbatim at `s = 2` for `nablaRicDiff_le`.
* `ForwardUniqueConnDot.tensor02_expand` — reused twice (in `repr_inner` and in the `(C)` step
  of `lowerBilin_normSq_le`); this is a second consumer, so its **relocation TODO**
  (`ForwardUniqueConnDot.md` §Relocation) is now due: `tensor02_expand`/`bilin_expand` belong in
  `Tensor/RSTensor/Components.lean`, `bilin12At`/`lowerBilin` in
  `Tensor/RSTensor/NablaOnTensors/ConnectionDifference.lean`.
* `RSLoweringNorm.normSqRS_eq_normSq0S_lowerAllSpace` — inspected and **deliberately avoided**
  (model-space `[InnerProductSpace ℝ E]` taint); the direct lowering-vs-lowering comparison made
  it unnecessary rather than blocked.

Added by the 2026-07-26 audit pass (inspected as reference for the frontier, **not** imported
or copied):

* `Evolution/Connection/MetricCovDerivProducer.christoffelEvolution_of_solution` — the `∂ₜΓ`
  frame producer; its hypothesis list is what proves Defect 1 (it needs `SolutionOn` +
  `IsSolutionOn` + `MetricFrameTimeRegularityInFrameOnLocal` + `hSmooth`/`hFdiff`/`hFtdiff`).
* `Evolution/Connection/Components.christoffelEvolutionRHSInFrame` /
  `christoffelVariationLoweredRHSInFrame` / `christoffelRHS_id` — the component Hamilton RHS and
  the observation that the lowered form is `rfl`-equal to `−∇_iRic_{jl} − ∇_jRic_{il} +
  ∇_lRic_{ij}`, so `g₁`-lowering cancels the `gInv₁` raising.
* `Evolution/ForwardUniqueReLower.lean` (`sharpFlat_eq_raise`, `reLower_rm04`, `reLowerPair`) —
  the existing realisation of `Φ = g₂^♯ ∘ g₁^♭`, i.e. the operator the flow-2 half needs.
* `Evolution/ForwardUniqueFields.lean` — `metricDiffAt_self`, `connDiffLowAt_self`,
  `rmDiffLowAt_self`, `metricDiffSq_def`, `connDiffSq_def`: reused in `connSpeedRHS_self`.
* `Tensor/RSTensor/FiberMetric/Tensor0SMetric.tensor0SMetricData` +
  `MetricFiberData.inner_self_eq_zero_iff` — reused for "`normSq0S` of `0` is `0`" inline rather
  than adding a fourth private `normSq0S_zero` copy (`ForwardUniqueClosure.lean:145` has one).

## Hygiene

No `instance`, `axiom`, `notation`, `macro`, `opaque`, `syntax` or `elab` declarations (in any
modifier-prefixed form), and no fixity declarations.  Four `set_option`s, all file-local and all
matching the lane's existing files.  **No file outside this one and its `.md` was edited** in any
of the four 2026-07-26 passes.

Imports: the repair pass replaced `Evolution.ForwardUniqueRmBounds` by
`Evolution.ForwardUniqueRatePro` (which re-exports it) and added
`Evolution.Connection.Components` — net `+1`.  Neither imports this file, so no cycle.  **Pass 4
added no import**: every lemma the trace step needs was already in the 303-module closure.

Declarations added across the 2026-07-26 passes: `connSpeedRHS_self`, `coeff_adot_eq`,
`lower_raise_cancel`, `connSpeedLow_eq`, `lowerBilin_metric_le`, `lowerHamRHS_comp`, `perm3`,
`perm3_apply`, `normSq0S_perm3`, `perm3_sub`, `hamSum`, `hamSum_sub`, `hamSum_normSq_le`,
`lowerHam_eq_perm`, `nablaRicDiff_trace_le` (public), and `lowerBilin_basis`,
`repr_bilinOfComp`, `normSq0S_sub_le`, `inner_le_sum_sq`, `hamPerm`, `connSpeed_arith`,
`normSq0S_reindex`, `nabla_trace_field`, `traceShuffle_normSq_le`, `nablaTracePerm_normSq_le`
(private).  All axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**One typeclass hypothesis was introduced, as authorized by R9(a):** `[I.Boundaryless]`, placed
per-theorem on `connSpeedLow_normSq_le`, `connDiffDot_normSq_le`, `nablaRicDiff_trace_le`,
`nabla_trace_field` and `nablaTracePerm_normSq_le` — deliberately **not** in the file-level
`variable` block, so that the other 20-odd public declarations keep their signatures.  It is
inherited from `nabla_metricTraceFirstTwo0S`, and the endpoint consumer
`ExtendViaUniqueness.lean` already carries it.
