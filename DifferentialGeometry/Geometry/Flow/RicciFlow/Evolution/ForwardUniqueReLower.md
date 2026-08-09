# `ForwardUniqueReLower.lean` — Route-K brick K2.6c (the re-lowering Leibniz defect)

Companion note for
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ForwardUniqueReLower.lean`.
Governing decision: `ShortTime/FORWARD_UNIQUE_PLAN.md` No.17 (dispatch), No.16 (the K2.6b
acceptance that scoped this brick).  Predecessor: `ForwardUniqueRmBridge.lean` /
`ForwardUniqueRmBridge.md` — this file discharges the "one remaining frontier" recorded
there.

## Outcome: **(A)** — deliverables 1, 2 and 3 all GREEN

992 lines, **0 sorry**, no new instances, no axioms, no notation; 33 public declarations
(28 theorems + 5 defs) + 8 private helpers.  Focused check PASS, targeted module build
PASS and **warning-free**, `#print axioms` on all 33 public declarations is exactly
`[propext, Classical.choice, Quot.sound]`.

## The slot layout (the thing the next brick must not re-derive)

`reLower g₁ g₂ (T : (0,s+1)) : (0,s+1)` is **the last slot of `T` precomposed with**
`Φ = g₂♯ ∘ g₁♭` (`sharpFlat`), realized as

```
reLower g₁ g₂ T = metricTraceFirstTwoField (s := s+1) g₂
                    (domDomCongr (reLowerPerm s) (T ⊗ metricTensorField g₁))
```

* the product is `T ⊗ g₁` **in that order** (`product (s := s+1) (q := 2)`), so its rank
  index is `(s+1)+2`, which is *syntactically* the rank `metricTraceFirstTwoField (s := s+1)`
  expects — putting `g₁` first would give `2+(s+1)` and force a `finCongr` cast;
* the contracted pair is (`T`'s last slot, `g₁`'s **first** slot);
* `reLowerPerm s : Equiv.Perm (Fin (s+1+2))` is `k ↦ k+2` for `k < s`, `s ↦ 0`,
  `s+1 ↦ 1`, `s+2 ↦ s+2` (a rotation-by-2 of the first `s+2` slots, fixing the last).

`reLowerPair g₂ (T : (0,s+1)) (K : (0,3)) : (0,s+2)` is the defect carrier: the same
construction with `g₁` replaced by an arbitrary `(0,3)` field, contracting `T`'s last slot
against `K`'s **middle** slot; `K`'s slot `0` becomes the leading (derivative) slot of the
result and `K`'s slot `2` becomes its trailing slot.  Its permutation
`reLowerPerm2 s : Equiv.Perm (Fin (s+1+3))` is `k ↦ k+3` for `k < s`, `s ↦ 0`, `s+1 ↦ 2`,
`s+2 ↦ 1`, `s+3 ↦ s+3`.

## Deliverable 1 (COMPLETE): representation + semantic pin

* `reLower_eval` — basis evaluation: `Σᵢⱼ gⁱʲ · T(…, eᵢ) · g₁(eⱼ, v_last)`.
* `reLower_apply` — **the semantic pin**:
  `reLower g₁ g₂ T x tail = T x (Function.update tail (Fin.last s) (sharpFlat g₁ g₂ x (tail (Fin.last s))))`.
  Proved through `sharpFlat_eq_raise` (identifying `Φ` with `raiseAt g₂ x basis (g₁♭ ·)`,
  which is `raiseAt_lower` applied to `S := ΦV`) plus single-slot multilinear expansion.
* `reLower_rm04` — the `mixLow_eq_rm04` instance: for a `(0,4)` field whose value at `x` is
  `metricRm04At g₂ x`, `reLower g₁ g₂ Rm2 x (vec4 X Y Z W) = g₁(Rm¹³₂(X,Y)Z, W)`.
  This is the checked identity against the semantics `ForwardUniqueRmBridge.md` pinned.

Defining `reLower` by the trace-of-product (rather than pointwise by `Φ`) is what makes it
a **smooth field for free**; a pointwise definition would have owed a section-smoothness
proof.

## Deliverable 2 (COMPLETE): the Leibniz defect

* `nablaProd_eval` — arbitrary-slot form of `nabla0SFun_product_eval` (the located
  ingredient is stated for *smooth-section* slots only; realizing the direction and the
  slots through `ContMDiffSection.exists_eq_at_gen` and `simp only [hV, hXsec]` lifts it).
* `nabla_reLower_eval` — the pointwise computation, the technical core: differentiate the
  three layers with `nabla_metricTraceFirstTwo0S` (trace), `totalNabla0SFun_domDomCongr` +
  `cons_apply_frontExtendEquiv` (reindexing), `nablaProd_eval` (product), then match the
  two basis double sums term by term.
* `nabla_reLower` — the field identity, via `totalNabla0S_realizes` and
  `totalNabla0SRealizes_unique`:

  ```
  ∇²(reLower T) = reLower(∇²T) + reLowerPair g₂ T (∇²g₁).
  ```

* `nabla_reLower_flux` — the same with `∇²g₁` rewritten by `nabla2_metric1` to
  `−lapDiffFlux g₁ g₂ g₁`, i.e. the defect is **`A₀₃`-algebraic**: bilinear in `T` and the
  connection-difference flux, no `∇A`, no extra derivative of `T`.
* `reLowerPair_self` — non-vacuity: at `g₁ = g₂` the defect vanishes (`metricNabla0S_self`).

## Deliverable 3 (COMPLETE): the concrete div-form commutator

* `reLowerOp` — the rank-indexed operator (`id` at rank `0`, `reLower` above it), the shape
  `lapCommFlux`/`lapCommRem`/`lapComm_eq_div_flux` consume.
* `lapCommFlux_reLower` — `lapCommFlux g₂ reLowerOp T = reLowerPair g₂ T (∇²g₁)`.
* `trace_reLower` — **`reLower` commutes with the first-two metric trace** (`reLower` acts
  on the last slot, the trace on the first two).  Proof = exchange of the two basis double
  sums (`sum_comm4`), using `traceInput_update_last` / `traceInput_last`.  This is the piece
  that makes the *remainder* explicit; without it only the flux would be concrete.
* `lapCommRem_reLower` — `lapCommRem g₂ reLowerOp T = tr_{g₂}(reLowerPair g₂ (∇²T) (∇²g₁))`.
* `lapComm_reLower_eq` / `lapComm_reLower_flux` — **the endpoint**:

  ```
  Δ₂(reLower T) − reLower(Δ₂T)
    = div₂(reLowerPair g₂ T ∇²g₁) + tr_{g₂}(reLowerPair g₂ (∇²T) ∇²g₁)
  ```

  with both carriers algebraic in `(A₀₃-flux, T, ∇²T)` after `nabla2_metric1`.  The abstract
  defect carriers of the R4 organization are retired.

Constants / norm bounds are deliberately out of scope (K2.4/K2.5 patterns; the quantitative
input is `lapDiffFlux_eval` / `fluxNormSq_le` in `ForwardUniqueRmBounds.lean`).

## Lean lessons from this pass

* **Build the permutation with `Equiv.ofLeftInverseOfCardLE`, not `Equiv.mk`.**  Only the
  `LeftInverse` obligation is then needed (`split_ifs <;> simp_all <;> omega` discharges it);
  the `right_inv` version of the same script did *not* go through (`simp_all` leaves
  `↑⟨s, _⟩` un-normalized and `omega` sees an opaque atom).  `toFun` stays definitional, so a
  `change`-based `_val` lemma (`split_ifs <;> rfl`) still works.
* **`dite`, not `ite`, in the permutation branches** — the `Fin` bound proofs need the
  branch condition in scope.
* **After `metricTraceInput_apply`, use `simp only [hv]`, never `rw [hv]`**: the else-branch
  proof depends on the index, so `rw` fails with "motive is not type correct".  This is the
  same trap `metricTraceFirstTwoField_product` documents.
* **`simp only` normalizes a discharged `dite` condition to `True`** — the follow-up must be
  `rw [dif_pos (trivial : True)]`, not `dif_pos rfl`.
* **`fin_cases p` produces `⟨0, ⋯⟩`, not `(0 : Fin 3)`** — a `change` to the numeral form is
  required before `rw`-ing a lemma stated with numerals.
* **`rw` beta-reduces its output.**  Auxiliary equations meant to be rewritten *after* a
  `rw` must be stated in beta-reduced form (`f a = b`, not `(fun x => …) a = b`).
* **Type-ascribe every `Fin.cons X (…) : Fin n → TangentSpace I x`.**  Otherwise `Fin.cons`'s
  motive `α` is guessed as `fun i => TangentSpace I i` and Lean demands
  `ChartedSpace H (Fin n)`.  That instance failure is the diagnostic signature of the
  mis-guess.
* **`Function.update_of_ne` elaborates `v` before `f`**, so `TangentSpace I x` makes it pick
  `α := M`; pass the disequality with the `Fin` index type already pinned (build it as a
  standalone `have`) instead of `?_`.
* **Four-fold sum exchange**: a small `sum_comm4` helper (four `Finset.sum_comm`s, two of
  them under `Finset.sum_congr`) is far cleaner than fighting `Finset.sum_comm` in place.
* The `Tensor0SSpace`-vs-CMM instance diamond did not bite; `A.toMultilinearMap.map_update_sum`
  + `Tensor0SSpace.map_update_smul` (the `tensor02_expand` idiom) works verbatim at rank `s`.
* Elaboration cost is modest (~22 s focused check); no `synthInstance.maxHeartbeats` bump was
  needed anywhere in this file.
* Style linters that only fire in the module *build* (not in the focused check): `show` that
  changes the goal must be `change`, and an unused `[DecidableEq Idx]` must be dropped in
  favour of `classical`.

## Reuse / adaptation record

* **Reused directly:** `sharpFlat`, `mixLow_eq_rm04`, `nabla2_metric1`, `lapCommFlux`,
  `lapCommRem`, `lapComm_eq_div_flux`, `metricNabla0S_self`, `raiseAt`, `raiseAt_eq`,
  `raiseAt_lower` (`ForwardUniqueRmBridge.lean`); `metricNabla0S`, `covDiv0SField`,
  `roughLap0SField`, `lapDiffFlux` (`ForwardUniqueRmDiff.lean`); `metricTraceFirstTwoField`
  (+ `_apply`, `_eq_sum`, `_add`), `metricTraceInput_apply`, `nabla_metricTraceFirstTwo0S`
  (`MetricTrace/NablaTraceGen.lean`); `totalNabla0SFun_domDomCongr`,
  `cons_apply_frontExtendEquiv`, `totalNabla0SRealizes_unique` (`NablaDomDomCongr.lean`);
  `nabla0SFun_product_eval`, `tensor0SField_product_apply` (`ContractionLeibniz.lean`);
  `basisInvMetric`, `basisInvMetric_real`, `tangentFlatEquiv_gen` (`CotangentRiemannian.lean`);
  `metricTensorField_apply` (`MetricCompatibility.lean`); `metricRm04At`, `riemannOp`, `vec3`,
  `vec4`, `metricCov`, `leviCivitaConnectionOfMetric_isMetricCompatible`,
  `…_contMDiffCovariantDerivativeLocally_one`.
* **Inspected and deliberately NOT used:** `metricTraceFirstTwoField_product` /
  `_domDomCongr_gen` — they *can* express `(tr A) ⊗ g₁` as a trace of `A ⊗ g₁`, but that route
  still bottoms out in the same double-trace exchange, so `trace_reLower` was proved directly
  from the basis expansions instead of routing through two more `finCongr`/lift permutations.
  No general trace framework was built: the ruling stop-signal did not fire.

## Relocation TODO for the campaign-end cleanup

* `traceField_eq_sum` (general-basis evaluation of `metricTraceFirstTwoField`) belongs next to
  `metricTraceFirstTwoField_eq_sum` in `Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`; it is
  pure trace API with no Ricci-flow content.
* `nablaProd_eval` belongs next to `nabla0SFun_product_eval` in
  `Tensor/RSTensor/ContractionLeibniz.lean` (it is the arbitrary-slot form of that lemma).
* `slot_expand`, `sum_comm4`, `update_cons_last`, `cons_last`, `cons2_vec3` are generic
  (multilinear / `Fin` / `Finset`) helpers and belong in those layers.
* `metricCov_one` duplicates a one-line `simpa`; make the `_one` form public in
  `Geometry/Curvature/Metric.lean` instead.
* `reLower` / `reLowerPair` themselves are two-metric objects and belong where they are.

## Status / next target

K2.6 is now complete (K2.6b deliverable 1 + this brick's deliverables 1–3), and nothing in
this file is conditional on an unproved hypothesis.  The next Route-K targets are unchanged:
K2.7 / the IBP wiring, then K4 (`forwardUniqueRate_le` assembly) and the K5 closure kit.
