# `StarSum2` — design + the brick-1 blocker (2026-06-10)

Goal was the five BBS bricks: `StarSum2` predicate + `.add`, `.bound`, `.nabla`, the `E_k`
recursion, and the `IteratedRmTowerOn` wiring.  **Returned after 5 attempts stuck on brick 1
(the predicate even elaborating).**  The math design is sound; the blocker is purely Lean
instance plumbing.  No code is committed (the non-compiling `StarSum2.lean` was deleted).

## The intended design (sound — keep for next attempt)

Inductive family on `(k : ℕ) → Tensor0SField (4+k)`:
```
inductive StarSum2 (S t) : (k:ℕ) → Tensor0SField (4+k) → Prop
  | zero (k)                : StarSum2 k 0
  | add  {k} {A B}          : StarSum2 k A → StarSum2 k B → StarSum2 k (A + B)
  | smul {k} (c) {A}        : StarSum2 k A → StarSum2 k (c • A)
  | reindex {k} (σ) {A}     : StarSum2 k A → StarSum2 k (domDomCongr σ A)
  | base (a b) (σ)          : StarSum2 (a+b) (starBaseField a b σ)
```
`starBaseField a b σ := metricTraceFirstTwoField g (metricTraceFirstTwoField g
  (domDomCongr σ (product (∇ᵃRm) (∇ᵇRm))))` — the double metric trace of a slot-reindexed
`∇ᵃRm ⊗ ∇ᵇRm`, rank `4+(a+b)`, `σ : Fin ((4+a)+(4+b)) ≃ Fin ((4+(a+b)+2)+2)`.

- **brick 1 `.add`** = the `add` constructor (free once it elaborates).
- **brick 2 `.bound`**: induct on the derivation → `∃ C ≥ 0, ∀ x (g-orthonormal), ‖T‖ ≤
  C·Σⱼ √(wⱼ)√(w_{k−j})` (`wⱼ = |∇ʲRm|²`).  zero→C=0, add→C_A+C_B, smul c→|c|·C, reindex→C,
  base→`card²` via `abs_curvatureAction0SAt_orthoBasis_le` (done). The existential `C`
  absorbs coefficient/term-count growth cleanly.
- **brick 3 `.nabla`** = `StarSum2 k T → StarSum2 (k+1) (totalNabla0S T)`, induct on the
  derivation; the `base` case commutes `∇` through both traces (`nabla_metricTraceFirstTwo0S`,
  done) + `domDomCongr` (`totalNabla0SRealizes_domDomCongr`) + product Leibniz
  (`nabla0SFun_product_eval`) ⟹ `base (a+1) b σ' + base a (b+1) σ''` (the slot-algebra is the
  same shape as the verified `traceRicWit` in `UhlenbeckBaseProducer.lean`).
- **brick 4 `E_k ∈ StarSum2 k`**: one-step peeling `E_k = ∇E_{k-1} + (∂ₜΓ)∗T_{k-1} −
  [Δ,∇]T_{k-1}`, base `E_0 = Rm∗Rm` (Uhlenbeck), close by induction using brick 3 + the done
  single-step commutator `spatialComm_nablaKRm_split`.
- **brick 5 wiring**: feed brick 2's bound into `IteratedRmTowerOn.starBound`, and (with
  `nablaKRm04Reaction_orthoBasis_eq_compContract`) the reaction into `heatEq`.

## THE BLOCKER (brick 1 — Lean instance synthesis, NOT math)

`0`/`+`/`•` (`OfNat`/`HAdd`/`HSMul`) on the **generic-rank** `Tensor0SField (4 + k)` fail to
synthesize their `ContMDiffVectorBundle ∞` module instance in this file's context.  Error:
`failed to synthesize OfNat (Tensor0SField ∞ (4 + k)) 0` (and `HAdd`/`HSMul`).

Five attempts, all the same failure:
1. raw `inductive … (A + B)` / `… 0`;
2. `include hMinf hM1 hM2 hMinf1 hEc` to force the manifold instances in;
3. `stZeroField`/`stAddField`/`stSmulField` `def` wrappers with `letI := tensor0SBundle_topology`;
4. + `letI := TangentBundle.contMDiffVectorBundle` + `letI := tensor0SBundle_smooth`;
5. plain `def` bodies (no `letI`), mirroring `TotalNabla0SRealizes.add` which *does* compile
   with generic-`s` `α + β`.

Diagnostic facts:
- the SAME ops work at **concrete** rank (`knField` at `2+2` in `UhlenbeckBaseProducer.lean`);
- they work for **generic `s`** in the lighter `Tensor/` layer
  (`TotalNabla0SRealizes.add`, `metricTraceFirstTwoField_add/_zero`, `NablaTraceGen.lean`);
- they fail for **generic `4+k` in this heavy RicciFlow import context**.
- `Tensor0SField` is an `abbrev` carrying `letI := tensor0SBundle_topology s` internally; the
  module also needs `tensor0SBundle_smooth` (needs `[IsManifold I (∞+1) M]`, present).

**ROOT CAUSE — fully isolated by minimal repros (2026-06-10).** Throwaway test files (deleted)
walked it down to the real cause.  WRONG guesses, each ruled out by repro:
- `[InnerProductSpace Real E]` diamond — removing it does NOT fix it;
- rank shape `s+2` vs `4+k` — both fail equally;
- instances-in-scope — explicit `[IsManifold I 1/2/(∞+1) M]` in the signature does NOT fix it;
- theorem-vs-def — a *theorem* with `(0 : Tensor0SField (s+2))` ALSO fails in the importing file
  (while the identical `metricTraceFirstTwoField_zero` compiles *inside* `NablaTraceGen`);
- `open`s — adding `open DifferentialGeometry.Tensor.Coordinates` does NOT fix it.

**CONFIRMED CAUSE = instance-synthesis PERFORMANCE pathology.** With `set_option maxHeartbeats
1000000` + `synthInstance.maxHeartbeats 1000000`, synthesizing `OfNat (Tensor0SField (s+2)) 0`
gives **`(deterministic) timeout at whnf, maximum number of heartbeats (1000000)`** — i.e. the
search does *pathologically expensive `whnf` reductions* (unfolding the bundle/`ContMDiffSection`
definitions) and runs out of fuel; it is NOT a missing instance.  Inside `NablaTraceGen` (low in
the import tree) the same search is fast; once the BBS chain (`RmRealizationBridgeAllK` and below)
is imported, some candidate instance makes the search explode.  A bigger heartbeat is not a real
fix (1M already overshoots; `maxHeartbeats 4000000` per declaration would make the file
uncompilable).

## Fix routes for next attempt (in priority order)
A. **Find & fix the pathological instance.** In a file importing `RmRealizationBridgeAllK`, run
   `set_option trace.Meta.synthInstance true in example : Tensor0SField (s+2) := 0` and read the
   trace to see which candidate instance the search keeps unfolding (the loop/blowup).  Likely a
   bundle `local instance`/`letI` that escaped a section and now offers a non-canonical
   `TopologicalSpace`/`VectorBundle` path the synthesizer keeps trying.  Fix = scope it, lower its
   priority, or give the canonical one higher priority.  This is the clean root fix and likely helps
   the whole BBS layer's compile times.
B. **Bypass synthesis: provide the module instance explicitly.** `letI : Zero (Tensor0SField (4+k))
   := <explicit ContMDiffSection zero>` (and similarly `AddCommGroup`/`Module`) so the `0`/`+`/`•`
   never trigger the expensive search.  Needs the exact instance path written by hand once; reusable
   via the `stZeroField`/`stAddField`/`stSmulField` helpers.
C. **Avoid raw module ops entirely.** Carry the closures through the realizer `TotalNabla0SRealizes`
   (already elaborated in the healthy `HigherOrder` layer) so `StarSum2` never writes `0`/`+`/`•` on
   `Tensor0SField` in the heavy context.

This is a Lean-environment performance bug, separable from the (sound) math design above — a good
candidate for a focused `trace.Meta.synthInstance` session or a Lean-expert/Pro consult.

The verified upstream pieces (`traceRicWit`-style slot algebra, `nabla_metricTraceFirstTwo0S`,
`spatialComm_nablaKRm_split`, `abs_curvatureAction0SAt_orthoBasis_le`, the orthonormal collapse)
all remain ready; only the predicate's hosting layer is the open question.
