# ForwardUniqueRatePro.lean — K4 / K1C-b owed producers

Status: **VERIFIED GREEN, 0 sorry, axiom-clean** (all 7 public declarations on exactly
`[propext, Classical.choice, Quot.sound]`).  Focused check green; targeted module build
green; no linter warnings.

Outcome vs the brick's charter: **(B)** — the Ricci-trace slot bridge is DONE (and does
more than asked); `movingReact_le` is **NOT** implemented and is classified below.

## Delivered

| decl | what it gives |
|---|---|
| `rm04TraceSlots` | the `Fin 4` permutation `(0,1,2,3) ↦ (0,2,3,1)` moving the `Rm₀₄` trace pair `(0,3)` onto `(0,1)` |
| `domDomCongr_sub` | slot reindexing commutes with `-` (canonical home is `Tensor/RSTensor/Defs.lean`; relocation owed) |
| `ricci_eq_trace_rm04` | **the tensor-level identity**: `ricciFromRm13At Rm13 = metricTraceFirstTwo0STensor g (domDomCongr rm04TraceSlots Rm04)` for any `g`-lowering `Rm04` of `Rm13` |
| `metricRicci_eq_trace` | canonical specialisation at `(g, ∇^g)` |
| `metricRicci_eq_trace_cross` | `Ric₂` read as a `g₁`-trace of the `g₁`-lowering of `Rm¹³` of `∇²` |
| `ricciDiff_eq_trace` | **the `htr` producer** (see next section) |
| `normSq_ricciTraceRep` | `‖domDomCongr rm04TraceSlots (rmDiffLowAt g₁ g₂ x)‖²_{g₁} = rmDiffSq g₁ g₂ x` |

`ricci_eq_trace_rm04` is exactly the "tensor-level `Ric = tr_g(Rm₀₄)` slot bridge" named as
**K1C-b's blocker (ii)** and as K4's second owed producer.

## Does it match `ricciDiffSq_le`'s `htr` verbatim? — YES

`ForwardUniqueRateLe.lean:353` asks for

```
htr : metricRicciAt g₁ x - metricRicciAt g₂ x = metricTraceFirstTwo0STensor (I := I) g₁ V
hV  : normSq0S (I := I) g₁ x 4 V ≤ rmDiffSq g₁ g₂ x + B * metricDiffSq g₁ g₂ x
```

`ricciDiff_eq_trace g₁ g₂ x` is that statement verbatim with

```
V := ContinuousMultilinearMap.domDomCongr rm04TraceSlots (rmDiffLowAt (I := I) g₁ g₂ x)
```

and `normSq_ricciTraceRep` discharges `hV` **as an equality**, so `B = 0`: `ricciDiffSq_le`
instantiates to the unconditional `|Ric₁−Ric₂|²_{g₁} ≤ n⁴ · rmDiffSq g₁ g₂ x`.  Both `htr`
and `hV` are therefore fully discharged; there is no residual `h₀₂` term, because
`rmDiffLowAt` lowers **both** flows with `g₁` and the trace is taken with `g₁` as well.

The instantiation itself was deliberately **not** written into this file: consuming
`ricciDiffSq_le` would drag in `ForwardUniqueRateLe.lean`'s section variable block, which
carries model-space `[InnerProductSpace Real E]`.  Per the standing project ruling that
model-space `InnerProductSpace ℝ E` is the wrong hypothesis and must not be propagated,
this file stays on `NormedSpace`.  Producers stated under `NormedSpace` apply unchanged in
the `InnerProductSpace` context, so the wiring belongs on the consumer side.

## Slot convention, checked

`ricciFromRm13_comp_eq_rm04_trace` (`Curvature/Components/RicciTrace.lean:40`) gives
`Ric_{ij} = Σ_{a,k} g^{ak} Rm₀₄(e_a, e_i, e_j, e_k)` — the trace pair is slots `0` and `3`,
whereas `metricTraceFirstTwo0STensor` contracts slots `0` and `1`.  With
`metricTraceInput X Y tail` filling `(0,1,2,3) ↦ (X, Y, tail 0, tail 1)`, the reindexed
tensor `domDomCongr σ Rm04` evaluated there is `Rm04 (X, tail 0, tail 1, Y)`, so
`σ = ![0,2,3,1]` (inverse `![0,3,1,2]`) is forced.  Verified by `fin_cases m <;> rfl`.

## Reuse ledger

Reused as-is: `ricciFromRm13_comp_eq_rm04_trace`, `riemannCurvature04At_eq_lower_riemannCurvatureAt`
(`Riemann/Basic/Pointwise.lean:660`, discharges the `Rm04LowersRm13At` gate directly, both
for `∇¹` and for the cross pair `g₁`/`∇²`), `metricTrace0S2InBasis_eq_metricTrace`,
`metricTraceFirstTwo0STensor_apply`, `rm04CompAt_apply`, `ricciCompAt_apply`,
`basisInvMetric_real`, `Module.Basis.ext_multilinear`, `tensor0SSpace_ext`,
`normSq0S_domDomCongr`.  Nothing was re-proved.

Debt created: `exists_onFrame` / `onFrame_inv` are copied privately here (**4th copy**;
the other three are in `ForwardUniqueRmBounds.lean`, `ForwardUniqueConnBound.lean`, and the
`MovingEdgeEnergy` line).  Campaign-end dedup target is still a public pair under
`Tensor/RSTensor/Tensor0SRiemannian/`.

## Lean lessons

1. **`rw` is unusable on `Tensor0SSpace` applications.**  `rw [Tensor0SSpace.sub_apply]`,
   `rw [Tensor0SSpace.domDomCongr_apply]` and `rw [traceInput_domDomCongr …]` all failed
   with "did not find an occurrence of the pattern" against goals that visibly *contained*
   the pattern — the FunLike coercion instances are defeq but not syntactically equal
   whenever the two sides were produced by different elaborations (e.g. one from
   `tensor0SSpace_ext`, one written by hand).  Every such step had to become `calc` with
   `rfl` / `congrArg` / a term-form `have h := Tensor0SSpace.sub_apply (I := I) s x A B v`
   used as a *calc step*, not as a rewrite.  This is the same trap already recorded for the
   `S₀₄` carrier work; it is systematic, not incidental.
2. `rw` also fails on rank-offset mismatches: `metricTraceFirstTwo0STensor` on a
   `Tensor0SSpace 4` internally has rank `2 + 2`, so `← domDomCongr_sub` did not match a
   subtraction produced by `trace_sub`.  Fixed by supplying `(s := 2)` explicitly and
   chaining with `calc`/`congrArg` instead of `rw`.
3. `set … with h` was fine; the mismatch above is unrelated to `set`.
4. Reducing a tensor identity to components: `tensor0SSpace_ext` to get an arbitrary
   argument, then `suffices h : L.toMultilinearMap = R.toMultilinearMap` +
   `Module.Basis.ext_multilinear` to get *basis* arguments, is the working recipe (copied
   from `RiemannianFiberNormSqRiemannOpHigherRankParseval.lean:190`).

## `movingReact_le` — NOT DONE, classification

**Failure classification: missing groundwork / API (not a mathematical obstruction, not a
route-choice problem).  The statement is true and the analytic route is clear; a required
bridge lemma does not exist and is a brick, not a micro-brick.**

What was attempted: the `fluxNormSq_le` pattern named in `ForwardUniqueRateLe.md`
(pick a `g₁`-orthonormal frame, bound each frame component, sum squares).

Where it stops: **`movingReact0S` is frame-pinned.**  Its definition
(`ForwardUniqueEnergy.lean:82`) hard-codes

```
ricReactionContract (basisInvMetric g x (Module.finBasis ℝ (TangentSpace I x))) …
```

i.e. the *canonical finite basis*, which is not `g`-orthonormal.  Every existing tool for
`ricReactionContract` requires `gInv = identityInvMetric`:

* `ricReactionContract_delta_eq_compContract` (`IteratedRmTowerProducer.lean:289`);
* `abs_ricStarArray_le` (`IteratedRmTowerProducer.lean:246`) — already exactly the
  `|Ric ∗ W| ≤ s·n·Rbnd·‖W‖` estimate needed;
* `compNormSqMulti_orthoBasis_eq_normSq0S` (`NablaRiemannHeatFrameInvariant.lean:145`).

There is **no basis-independence lemma for `ricReactionContract` in the tree**, and none can
be avoided: the bound's right-hand side (`√normSq0S g x 2 Q · normSq0S g x s W`) is
basis-free while the left-hand side is evaluated at `finBasis`, whose Gram matrix is
uncontrolled.

Why the "~80 lines, `fluxNormSq_le` pattern" estimate in `ForwardUniqueRateLe.md` was
wrong: `fluxNormSq_le` bounds `lapDiffFlux`, a genuinely *invariant* object, so its proof is
free to choose its own orthonormal frame.  `movingReact0S` is not invariant on its face.

**Smallest unblocking lemma.**  `movingReact0S_orthoBasis`: for every `g`-orthonormal basis
`b`,
`movingReact0S g x s Q W = ricReactionContract identityInvMetric (fun i j => Q (b i, b j))
(comp_b W) (comp_b W)`.
After that, the bound itself is ~40 lines from the three lemmas above, with explicit
`C(n,s) = 2·s·n^{1+s/2}` (or the sharper `2s` via an operator-norm route).

**Route to that lemma** (the honest cost).  The invariant characterisation is
`movingReact0S g x s Q W = 2 Σ_b ⟪W, W ∘_b Q♯⟫_g`, where `Q♯` is the endomorphism with
`g(u, Q♯ v) = Q(u,v)` and `∘_b` composes slot `b`.  Derivation, purely algebraic, is:
substituting `RicUp^{ij} = Σ_{p,q} g^{ip}g^{jq}ric_{pq}` and re-indexing the slot-`b` sum
turns each slot term of `ricReactionContract` into `coordContract gInv cW cW^{(b)}` with
`cW^{(b)}_J = Σ_j (Q♯)^j_{J b} cW(J[b→j])`, and `coordContract gInv · ·` is basis-free by
`inner0S_eq_coord` — *provided* `cW^{(b)}` is exhibited as the component array of an actual
tensor.  That needs a new small layer:
(i) `Q♯ : TangentSpace I x →L[ℝ] TangentSpace I x` from `cotangentSharp` +
`oneFormAtSlot0S` (needs CLM packaging: linearity + continuity in `v`);
(ii) single-slot `ContinuousMultilinearMap.compContinuousLinearMap` with its component
formula, via `basis_coord_eq_sum_inv_inner` (`Curvature/Components/TraceOneForm.lean:88`);
(iii) transport through `inner0S_eq_coord`.
Estimated 250–400 lines.  A derivative-uniqueness shortcut (instantiate
`hasDerivWithinAt_normSq0S_ricciFlow` at two bases) was considered and rejected: it needs a
global `SmoothRiemannianMetric` family with prescribed `∂ₜg = −2Q` at one point, which is
heavier than the algebra and routes a linear-algebra fact through analysis.

**No `sorry` was left for this.**  Nothing is blocked by its absence: `hreact` is a named
slab *hypothesis* of `forwardUniqueRate_le`, not a proof obligation inside K4.  The only
thing lost is the upgrade `hreact ⟹ C_R = C(n,s)·sup_slab‖Ric₁‖`.  A `sorry` here would
have polluted this file's axiom audit for no route gain.
