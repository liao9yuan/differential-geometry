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

**ROOT CAUSE — ISOLATED by minimal repro (2026-06-10).** A throwaway test file `def diag (s) :
Tensor0SField (s+2) := 0` (since deleted) pins it down:
- WRONG guesses (each ruled out by the repro): the `[InnerProductSpace Real E]` diamond (removing
  it does NOT fix it); the rank shape `s+2` vs `4+k` (both fail equally); instances-in-scope
  (adding `[IsManifold I 1/2/(∞+1) M]` explicitly to the `def` signature does NOT fix it).
- **CONFIRMED**: it is the **import context**. `metricTraceFirstTwoField_zero` — the *identical*
  `(0 : Tensor0SField (s+2))` with the same explicit instances — compiles inside `NablaTraceGen`.
  The repro file differs only by `import …StarSum.NablaReactionAllK`.  So **some instance in the
  `NablaReactionAllK` import chain breaks generic-rank `Tensor0SField` `Zero`/module synthesis**
  (a shadowing/orphan/`local instance` that escaped its section, or a competing bundle instance).
  The light `NablaTraceGen` context is healthy; the heavy BBS context is not.

## Fix routes for next attempt (in priority order)
A. **Find the culprit import.** Bisect: a file importing only `NablaTraceGen` + `RmRealizationBridgeAllK`
   (for `nablaKRm04Field`) — does `(0 : Tensor0SField (s+2))` still compile?  Walk the
   `NablaReactionAllK` import list until `0` breaks; the last-added import is the culprit.  Then run
   `set_option trace.Meta.synthInstance true` on `(0 : Tensor0SField (s+2))` there to see which bad
   instance is chosen, and fix it (likely a `local instance`/`attribute [instance]` that should be
   scoped, or a `letI` leaking a non-canonical bundle topology).
B. **Avoid raw module ops in the heavy context.** Host `StarSum2` so it never writes `0`/`+`/`•` on
   `Tensor0SField` directly in the broken context: state the closures through the realizer
   `TotalNabla0SRealizes` (whose `+`/`•` are already elaborated in the healthy `HigherOrder` layer),
   or carry an explicit finite `List`/`Finset` of base terms summed via a helper proved in the light
   layer.  This sidesteps the broken environment without first finding the culprit.

The verified upstream pieces (`traceRicWit`-style slot algebra, `nabla_metricTraceFirstTwo0S`,
`spatialComm_nablaKRm_split`, `abs_curvatureAction0SAt_orthoBasis_le`, the orthonormal collapse)
all remain ready; only the predicate's hosting layer is the open question.
