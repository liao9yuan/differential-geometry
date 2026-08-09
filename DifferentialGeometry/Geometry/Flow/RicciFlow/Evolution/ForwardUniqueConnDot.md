# ForwardUniqueConnDot — brick K1C (invariant speed of `A₀₃`)

Lane: `ricci_flow_forward_unique` Route K (`ShortTime/FORWARD_UNIQUE_PLAN.md` dispatch №7,
`ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §5 "K1 tail").

## Outcome

**(B).**  K1C-a is COMPLETE, 0 sorry, axiom-clean.  K1C-b (the pointwise
`|∂ₜA₀₃|² ≤ C(|h₀₂|² + |A₀₃|² + |∇¹S₀₄|²)` bound) is **classified, not stated** — see
"K1C-b: why it is a separate brick" below.  Verification: focused check green; authoritative
targeted build of the module green; `#print axioms` on all seven public results returns
exactly `propext, Classical.choice, Quot.sound`.

## What K1C-a proves

The lowering carrier `g₁(t)` moves, so the invariant speed of `A₀₃ = g₁(∇¹−∇², ·)` is a sum:

`∂ₜA₀₃ (X,Y,Z) = −2 Ric₁((∇¹−∇²)(Y,X), Z) + g₁(t)((∂ₜ(∇¹−∇²))(Y,X), Z)`.

`connDiffDot g₁ g₂ Adot t x : Tensor0SSpace 3 I x` is exactly that sum, and it is a genuine
`(0,3)` fiber tensor, so it can be passed as K3's `Adot` argument verbatim.

### The exact hypothesis package of `connDiffLow_hasDerivAt_frame` (the `hA` producer)

* `g₁ g₂ : ℝ → SmoothRiemannianMetric I M` (metric-family indexing — matches K3 and the
  `ForwardUniqueFields` carriers).
* `frame : Idx → (y : M) → TangentSpace I y`, `hframe : IsLocalFrameOn I E 1 frame u`,
  `hu : IsOpen u`, `hx : x ∈ u`.  `Fintype Idx` only.
* `Adot : (y : M) → T_y →L[ℝ] T_y →L[ℝ] T_y` — the invariant `(1,2)` speed of `∇¹ − ∇²`.
  Only its value at `x` is used by the pointwise theorems; `connDiffDot` needs the family
  because K3's `Adot` slot is `ℝ → (x : M) → Tensor0SSpace 3 I x`.
* `hPDE₁ : ∀ X Y, HasDerivAt (fun r => (g₁ r).inner x X Y) (−2 · Ric₁ (X,Y)) t` — literally
  `forwardUniqueEnergy_hasDerivAt`'s `hPDE₁ x`, so the caller reuses it unchanged.
* `hΓ : ∀ i j k, HasDerivAt (Γ(metricCov (g₁ r))ᵏᵢⱼ − Γ(metricCov (g₂ r))ᵏᵢⱼ)
  (hframe.coeff k x (Adot x (frame j x) (frame i x))) t` — K1's conclusion, with the RHS
  difference realised by `Adot`.
* Conclusion: `∀ v, HasDerivAt (fun r => connDiffLowAt (g₁ r) (g₂ r) x v)
  (connDiffDot g₁ g₂ Adot t x v) t` — K3's `hA` at `x`.

**`hPDE₂` is NOT needed.**  Only `g₁` lowers, so the second flow's Ricci-flow equation plays
no role in `∂ₜA₀₃`; it enters only through `Adot`.  Worth recording: it slims the endpoint's
input bundle.

### Discharging `Adot` (no dangling existence obligation)

`bilinOfComp b c` builds the bilinear map with prescribed basis components, and
`coeff_bilinOfComp` says its frame coefficients are `c`.  So a caller holding K1's component
right-hand sides `c i j k := christoffelEvolutionRHSInFrame gInv₁ nablaRic₁ t x i j k −
christoffelEvolutionRHSInFrame gInv₂ nablaRic₂ t x i j k` sets
`Adot x := bilinOfComp (hframe.toBasisAt hx) c` and discharges `hΓ` by rewriting with
`coeff_bilinOfComp`.  `christoffelInFrame_sol` bridges K1's `SolutionOn`-indexed Christoffel
symbols to the metric-family ones (definitional, `rfl`).

### Remaining wiring debt for the caller (NOT a frontier)

K1 concludes `HasDerivWithinAt … D.carrier t`, this file consumes `HasDerivAt`.  The upgrade
is `HasDerivWithinAt.hasDerivAt` with `D.carrier ∈ 𝓝 t`, which holds on the open window K3
works on.  Left to the assembly step because it is a property of the caller's interval, not
of this brick.

## Route notes (what worked)

* The only real construction problem was building a `(0,3)` fiber tensor from a formula.
  `Integral.L2.lowerAllUpperIndices` lowers only with a **metric**, but the reaction term
  lowers with `Ric₁`, so a general `(0,2)`-lowering was genuinely needed.  Solution:
  `bilin12At` (the `(1,2)` tensor of an arbitrary bilinear map, i.e.
  `connectionDifferenceTensorAt` with `CovariantDerivative.difference` generalised) composed
  with `ContinuousMultilinearMap.curryLeft` of `q`, then `ContinuousLinearMap.uncurryLeft`,
  then one `domDomCongr` slot permutation (same shape as `connDiffOutAt` in
  `ForwardUniqueFields`).  ONE construction serves both summands.
* Differentiating `r ↦ g₁(r)(F r, Z)` with **both** the bilinear form and the vector moving
  needs a basis expansion of the vector slot; `tensor02_expand` (slot-0 expansion of a
  `(0,2)` fiber tensor along a finite basis, via `MultilinearMap.map_update_sum`) does it in
  a single sum over the basis, then `HasDerivAt.fun_sum` + `HasDerivAt.mul`.  No frame is
  needed here — `Module.finBasis ℝ (TangentSpace I x)` suffices, exactly as `movingReact0S`
  in K3 does.
* The frame → invariant step (`connDiffVec_hasDerivAt`) is the R3 debt: `bilin_expand`
  (bilinear basis expansion of a `T →L T →L T`) reduces arbitrary `(X,Y)` to frame pairs,
  and `Basis.sum_repr` + `HasDerivAt.smul_const` lifts the scalar K1 facts to the
  vector-valued derivative.  Frame-domain bookkeeping cost: `IsOpen u` (needed for
  `IsLocalFrameOn.contMDiffAt` → `MDifferentiableAt`, which
  `IsCovariantDerivativeOn.difference_apply` requires).  No atlas/partition construction was
  needed — the statement is pointwise, so one chart frame around `x` is enough.

## Lean lessons (durable)

* **`Tensor0SSpace` vs the bare `ContinuousMultilinearMap` type is an instance diamond, not
  just a coercion nuisance.**  Writing the type `ContinuousMultilinearMap ℝ (fun _ : Fin 2 =>
  TangentSpace I x) ℝ` in a **declared signature** makes instance search pick the *bundle*
  instances (`instTopologicalSpaceContinuousMultilinearMap ℝ 2 E (TangentSpace I) x`), while
  `ContinuousLinearMap.uncurryLeft` wants the *normed-derived* ones
  (`ContinuousMultilinearMap.instTopologicalSpace`).  A `ContinuousLinearMap` whose codomain
  carries the wrong ones is an "Application type mismatch" that no amount of
  `backward.isDefEq.respectTransparency false` fixes.
  - What FAILS: an intermediate `def toCMM2 : Tensor0SSpace 2 I x →L[ℝ] ContinuousMultilinearMap …`
    conversion CLM, and `.comp`-ing it in.
  - What WORKS: keep the value's type inferred from the enclosing `uncurryLeft` (a *term*-level
    ascription `(bilin12At A (curryLeft q W) : ContinuousMultilinearMap …)` inside the
    structure literal elaborates fine — type ascription only needs `whnf`), and prove
    `map_add'`/`map_smul'` by `exact` of the `Tensor0SSpace`-typed fact
    (`(bilin12At A).toCLM.map_add _ _`).  `exact` checks defeq and crosses the diamond;
    `simp`/`rw` do NOT, because the two `DFunLike` coercion paths are syntactically distinct.
    This is the same family as the `ForwardUniqueFields` lesson ("`rw` fails on
    `Tensor0SSpace` fiber algebra via the FunLike coercion of a non-reducible def").
* `HasDerivAt.sum` produces `HasDerivAt (∑ i ∈ u, A i)` with a **Pi-type** sum of functions;
  for the `fun y => ∑ i, A i y` shape use `HasDerivAt.fun_sum`.  `simpa using` does not
  bridge them reliably (and re-normalises the derivative expression).
* `ContMDiffAt.mdifferentiableAt` takes `n ≠ 0` in this Mathlib, not `1 ≤ n`.
* `Module.Basis.constr_basis` does not fire under `simp` through
  `LinearMap.toContinuousLinearMap`; drive it with `change … = _` + `rw`.
* `TangentSpace I x` gets its `NormedAddCommGroup`/`NormedSpace`/`FiniteDimensional`
  instances from `Tensor0SBundle` (`Defs.lean:427`), NOT from Mathlib's `deriving` clause —
  so `TangentSpace`-valued `HasDerivAt` is available, which is what makes the vector-valued
  `connDiffVec_hasDerivAt` statement possible at all.

## K1C-b: why it is a separate brick (classification)

The ruling's bound is `|∂ₜA₀₃|²_{g₁} ≤ C(|h₀₂|² + |A₀₃|² + |∇¹S₀₄|²)`.  With
`connDiffDot = −2·lowerBilin(Ric₁, Δ_t) + lowerBilin(g₁, Adot)` the proof needs **four**
separate missing API families, i.e. it is not a tail of K1C-a:

1. **Fiber triangle / Cauchy–Schwarz at `Tensor0SSpace s I x`.**  `Tensor0SMetric.lean` has
   `normSq0S_eq_inner` and `normSq0S_nonneg` only; the inner-product structure appears as a
   *local* `letI : PreInnerProductSpace.Core ℝ (Tensor0SSpace s I x)` (`Tensor0SMetric.lean:473`),
   never as a usable `normSq0S_add_le` / `|a+b|² ≤ 2|a|²+2|b|²`.  Missing API.
2. **"Lowering with `g₁` is a fiber isometry"** — `normSq0S (g₁) (lowerBilin (metricTensorField g₁ x) A)`
   in terms of the mixed norm of `A`.  Nearest existing thing is `RSLoweringNorm.lowerAllSpace`,
   which the lane already flagged (plan №3 deferred item (i)) as needing an
   `omit [InnerProductSpace ℝ E]` at its producer.  Missing API + a known producer defect.
3. **Contraction bound for a general `(0,2)` lowering** — `|lowerBilin q A| ≤ ‖q‖·|A|`-type,
   needed for the `Ric₁` reaction term, together with raising/lowering to convert
   `|Ric₁ · Δ_t|` into `|Ric₁| · |A₀₃|`.  Missing API.
4. **The real mathematics: `∂ₜΓ¹ − ∂ₜΓ²` → `trace(∇¹S₀₄) + A·Rm + h`-terms.**  This is the
   ∇Ric-difference expansion via the second contracted Bianchi identity.  In this repo
   `contracted_bianchi_of_second` (`Geometry/Curvature/Bianchi.lean:1654`) is
   `hcontract hsecond` — a *hypothesis-shaped* predicate combinator
   (`ContractedBianchiOfSecondAt`, `SecondBianchiAt`), not a proved contraction identity, so
   the trace bridge itself has to be produced.

There is also a **statement-level blocker**: the bound's right-hand side needs a named
`∇¹S₀₄` carrier, which the lane does not have yet (K2's `ForwardUniqueRmDiff.lean` has
`metricNabla0S`-style operators but no `∇¹S₀₄` name).  Writing `∃ C, …` today would either
misstate the background-norm hypothesis package or hide the four gaps behind a wrapper, both
of which the charter forbids.  Recommendation: commission K1C-b after (i) a `normSq0S`
triangle/Cauchy–Schwarz layer in `Tensor/RSTensor/FiberMetric/`, (ii) the `RSLoweringNorm`
`omit` repair, and (iii) a named `∇¹S₀₄` carrier from the K2 lane.

**Smallest next lemma that unblocks K1C-b**: `normSq0S_add_le` (or
`normSq0S (a+b) ≤ 2 * normSq0S a + 2 * normSq0S b`) at
`Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean`, promoting the existing local
`PreInnerProductSpace.Core` to a reusable inequality layer.

## Relocation TODO (protocol-deferred)

`bilin12At`, `lowerBilin` (+ `lowerBilinOut`, `lowerStdPerm`), `tensor02_expand`,
`bilin_expand`, `bilinOfComp` are generic fiber algebra with canonical homes in
`Tensor/RSTensor/NablaOnTensors/ConnectionDifference.lean` (the first two) and
`Tensor/RSTensor/Components.lean` (the expansions).  They live in this file only because the
brick protocol forbade editing existing files.  Move on the next consumer or at campaign end.
`lowerStdPerm` duplicates the private `connDiffStdPerm` of `ForwardUniqueFields.lean`; merge
them at the same time.
