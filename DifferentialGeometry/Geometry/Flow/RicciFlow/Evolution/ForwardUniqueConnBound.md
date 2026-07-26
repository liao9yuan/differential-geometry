# ForwardUniqueConnBound — brick K1C-b (the pointwise bound on `|∂ₜA₀₃|²`)

## Outcome

**(B)** — deliverables 1 and 2 fully green, deliverable 3 green except for one precisely named
and classified `sorry`.  555 lines; 11 public declarations (3 `def`, 8 `theorem`), 7 `private`
helpers; **exactly one `sorry`**, in `connSpeedLow_normSq_le`.  Focused check GREEN; targeted
module build GREEN.

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
* `connSpeedLow_normSq_le` (**the one `sorry`**) — see below.
* `connDiffDot_normSq_le` (**green modulo the above**): the capstone in the ruling's shape,
  `|∂ₜA₀₃|² ≤ 8Λric·|A₀₃|² + 2C(n)(|∇¹S₀₄|² + (1+Λ)²(B₁+B₂)(|h₀₂|² + |A₀₃|²))`.

## The remaining frontier (`connSpeedLow_normSq_le`)

**Classification: missing groundwork/API — not a mathematical obstruction, not a design
choice.**  Two ingredients are missing from the stack:

1. **Hamilton's `∂ₜΓ` formula in invariant form.**  The repo has it only as frame components
   (`Evolution/Connection/Christoffel.lean`, which is what K1/K1C-a consume).  What K1C-b needs
   is `g₁((∂ₜ(∇¹−∇²))(Y,X), Z)` expressed as a permutation sum of `∇Ric`-differences, i.e. the
   invariant reading of `∂ₜΓ^k_{ij} = −g^{kl}(∇_iR_{jl} + ∇_jR_{il} − ∇_lR_{ij})` for each flow,
   with the `g₂`-lowering of the second one converted to `g₁` at the cost of an `O(|h₀₂|)` term.
2. **The contracted trace `∇Ric = tr_g(∇Rm)`.**  This is *not* second Bianchi.  The planner's
   note is confirmed from this side: `curvSecondBianchi` (`Geometry/Curvature/Bianchi.lean:820`)
   is a proved operator-level theorem, but the route taken here never needs it — the identity
   required is the commutation of `∇` past a metric trace (`nabla_metricTraceFirstTwo0S`,
   `traceNablaShuffle` in `MetricTrace/NablaTraceGen.lean`), which holds because `∇g = 0`.
   What blocks it today is *slot bookkeeping*: `metricRicciAt` is `ricciFromRm13At` of the
   **(1,3)** tensor (`metricRicciAt_eq_trace`, `Geometry/Curvature/Metric.lean:104`), and the
   bridge to the metric trace of the **(0,4)** tensor exists only at the component level
   (`ricciFromRm13_comp_eq_rm04_trace`, `Curvature/Components/RicciTrace.lean:96`;
   `ricciComp_eq_trace_rm04`, `Curvature/Components/LocalFrame.lean:144`), both with `hLower`
   hypotheses.  A tensor-level `metricRicciAt = metricTraceFirstTwo (permuted metricRm04At)`
   lemma is the smallest missing bridge.

**Smallest next lemma that would unblock K1C-b**: a tensor-level (not component-level)
`Ric = tr_g(Rm₀₄)` with the trace pair moved to slots `0,1` by `domDomCongr`, in
`Geometry/Curvature/` (next to `metricRicciAt_eq_trace`).  With that plus item 1, the rest is
`nablaRicDiff_le` (already green here) + `traceNormSq_le` + `remNormSq_le`, all existing.

**Hypotheses of the frontier are honest inputs**, not restatements of the conclusion: `hA` is
the same derivative characterisation of `Adot` that `connDiffLow_hasDerivAt` already uses,
`hRF₁`/`hRF₂` are the two Ricci-flow equations, `hS`/`hRic₂`/`hRm₂` pin supplied fields, `hΛ`
is one-sided metric comparison, `hB₁`/`hB₂` are named background norms.  **The displayed
dimensional constant `9n⁶` is provisional** — the shape of the right-hand side is the
interface; raise the constant freely when the proof lands.

## Lean lessons (durable)

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

## Hygiene

No `instance`, `axiom`, `notation`, `macro`, `opaque`, `syntax` or `elab` declarations (in any
modifier-prefixed form).  Four `set_option`s, all file-local and all matching the lane's
existing files.  No existing file was edited.
