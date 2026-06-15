# Component Eval API Plan

## Goal

Retire downstream uses of
`set_option backward.isDefEq.respectTransparency false` that only exist because
component evaluation unfolds through tensor representation internals:
`component0S`, `componentRS`, `coordComponent0SAt`, `coordComponentRSAt`,
`basisTensor0S`, and arity-specific `Fin.cons`/`vec` encodings.

This should make downstream proofs use stable component API lemmas instead of
unfolding Hom representations, basis tensors, or coordinate-frame internals.

## Live Evidence

Current audit on 2026-06-14:

- `DifferentialGeometry/Tensor`: 66 files with the transparency hack.
- `DifferentialGeometry/Geometry/Flow/RicciFlow`: 37 files.
- `DifferentialGeometry/Geometry/Curvature`: 31 files.
- Whole `DifferentialGeometry`: 443 files, 564 occurrences.

Natural API layer:

- `DifferentialGeometry/Tensor/RSTensor/CoordinateBasis.lean`
- `DifferentialGeometry/Tensor/RSTensor/Coordinates/CoordinateBasis.lean`
- `DifferentialGeometry/Tensor/RSTensor/Components.lean`
- `DifferentialGeometry/Tensor/RSTensor/Coordinates/Components.lean`
- coordinate-frame wrappers in
  `DifferentialGeometry/Geometry/Coordinates/CoordinateFrame.lean`

Already present and reusable:

- `component0S_apply`
- `basisTensor0S_component`
- `basisTensor0S_apply`
- `tensor0S_apply_eq_sum`
- `component0S_add`, `component0S_smul`, `component0S_product`
- `componentRS_apply`, `componentRS_apply_input_eq_sum`
- `ext0S_basis`, `extRS_basis`
- `coordComponent0SAt_apply`, `coordComponentRSAt_apply`
- pointwise coordinate bridges
  `tensor0SModelAt_coordComponent0SAt` and
  `tensorRSModelAt_coordComponentRSAt`

## Missing Lemma Families

Add canonical lemmas at the lowest natural layer.

1. Slot-congruence lemmas:
   - `component0S_congr_slots`
   - `componentRS_congr_slots`
   - coordinate-frame versions for `coordComponent0SAt` and `coordComponentRSAt`
   These should let downstream proofs rewrite a slot map equality without
   unfolding `Fin.cons`.

2. Arity apply lemmas:
   - `component0S_slots0_apply`
   - `component0S_slots1_apply`
   - `component0S_slots2_apply`
   - `component0S_slots3_apply`
   - `component0S_slots4_apply`
   plus coordinate-frame analogues.
   The RHS should be the direct tensor application to the expected tuple, using
   the existing project slot/vector conventions. These lemmas should replace
   local `fin_cases` proofs that normalize `Fin.cons`.

3. Coordinate-frame component extensionality:
   - `coordExt0SAt`
   - `coordExtRSAt`
   These should be thin wrappers over `ext0S_basis` and `extRS_basis` using
   `coordinateFrameAt_toBasis`.

4. Mixed tensor input lemmas:
   - expose the Hom-input basis tensor through `componentRS` without requiring
     users to mention `basisTensor0S`;
   - expose the input-expansion formula as a public theorem in both generic and
     real-specialized namespaces.

5. Product and contraction apply lemmas:
   - ensure product, scalar multiplication, sums, `domDomCongr`, and common
     contraction/trace component evaluations have theorem-form rewrite lemmas.
   - These should state the structural component result, not rely on `rfl`.

## Implementation Order

1. Start in `Tensor/RSTensor/Coordinates/CoordinateBasis.lean` and
   `Tensor/RSTensor/Coordinates/Components.lean`.
2. Add the generic `CoordBasis` lemmas first, then mirror or specialize to the
   Real-facing files only when downstream imports require it.
3. Add coordinate-frame wrappers in `Geometry/Coordinates/CoordinateFrame.lean`
   or the closest existing coordinate component bridge file.
4. Pick one downstream transparency-heavy file as a validation target:
   `Geometry/Coordinates/NablaComponents/Tensor0S.lean` is a good first test
   because it uses coordinate components structurally without Ricci-flow
   algebra.
5. Once that target is green without `respectTransparency false`, remove the
   hack from a small batch of downstream files that use only the newly-added
   lemmas.
6. Repeat in batches: Tensor core first, then Curvature, then RicciFlow.

## Stop Conditions

Stop and report if:

- a desired lemma cannot be stated without exposing `TensorRSSpace` as a Hom
  implementation detail;
- Lean requires changing public tensor definitions instead of adding theorem
  lemmas;
- an arity lemma needs many ad hoc `Fin` normalizations that indicate the slot
  conventions themselves need a named API;
- removing the transparency option breaks proofs for reasons unrelated to
  component evaluation.

## Verification

For every batch:

- claim edited Lean files with `scripts/lake-locked.ps1`;
- focused-check the edited API files;
- focused-check at least one downstream file whose transparency hack was
  removed;
- only run targeted builds after API files are green and downstream imports
  need refreshed `.olean`s;
- update the same-name Markdown note for every edited Lean file.

## Claude Target

The first concrete implementation target is a small API batch:

- slot-congruence lemmas for `component0S`, `componentRS`,
  `coordComponent0SAt`, and `coordComponentRSAt`;
- coordinate-frame extensionality wrappers;
- one downstream removal of `respectTransparency false` from
  `Geometry/Coordinates/NablaComponents/Tensor0S.lean`.

## 2026-06-14 — First batch executed (lemmas DONE; validation target was a MISMATCH)

**API lemmas added + focused-check GREEN** (all additive `rw`/`ext_basis` wrappers, lowest natural layer):

| lemma | file | layer |
|---|---|---|
| `component0S_congr_slots` | `Tensor/RSTensor/Coordinates/CoordinateBasis.lean` | generic 𝕜 |
| `componentRS_gen_congr_slots` | `Tensor/RSTensor/Components.lean` | generic 𝕜 |
| `componentRS_congr_slots` | `Tensor/RSTensor/Coordinates/Components.lean` | Real |
| `coordComponent0SAt_congr_slots`, `coordComponentRSAt_congr_slots`, `coordExt0SAt`, `coordExtRSAt` | `Geometry/Coordinates/CoordinateFrame.lean` | coord-frame |

The `coordExt0SAt`/`coordExtRSAt` wrappers are `ext0S_basis` / `extRS_basis_gen` at `coordinateFrameAt_toBasis`
(note: `coordComponentRSAt` is built on `componentRS_gen`, so its ext/congr use the **`_gen`** layer, not the
Real `componentRS`).  `coordComponent*` delta-unfolds to `component*` cleanly, so the wrappers need no
transparency hack themselves.

**⚠ VALIDATION TARGET MISMATCH — `Geometry/Coordinates/NablaComponents/Tensor0S.lean` cannot validate this batch.**
That file has **8** `respectTransparency false` blocks, but a grep + body audit shows **none** is caused by
component-eval (`component0S`/`componentRS`/`coordComponent*`/`basisTensor0S`) unfolding — the file does not use
that API at all.  All 8 are `Tensor0SSpace.toModel` / `tensor0SSpace_continuousLinearEquiv` / bundle-trivialization
/ `tensor0SBundle_topology` / `nabla0S_reg` reductions.  Empirically removing all 8 (then `git checkout`-reverted)
gave **`synthInstanceFailed`** at ~16 sites (e.g. lines 405/632/712/877/944/970) + a `rfl` failure at
`nabla0SCoord_apply` — i.e. the hacks let **instance synthesis** unfold through the `(0,s)` tensor **bundle topology**,
a different root cause from the component-eval API.  So per the stop condition, the planned lemmas are added but the
removal step was NOT done on this file (the lemmas are irrelevant to its hacks).

**Next-pass guidance:**
1. Validate this batch against a file that ACTUALLY uses `coordComponent0SAt`/`component0S`/`componentRS` +
   `respectTransparency false` and proves a tensor equality / rewrites slot maps (those are where `coordExt*` /
   `*_congr_slots` remove the hack).  Grep for files importing the component API with the option set.
2. `Tensor0S.lean`'s hacks are a SEPARATE workstream: they need a **bundle-topology instance / `toModel`-eval**
   lemma family (`Tensor0SSpace.toModel` application + `tensor0SBundle_topology` instance exposure), not the
   component-eval API.  Add that to the "Missing Lemma Families" list as a distinct item before retrying it.

## 2026-06-14 — Second pass: VALIDATED on `NablaComponents/TensorRS/ApplyInput.lean` (1 block removed)

Re-targeted the validation at a file that genuinely uses the basis-tensor/component API.  Outcome: **2 → 1**
transparency blocks; the component-eval API + one tiny missing apply lemma cleanly remove the component block.

**New API lemma:** `Tensor0SSpace.constInChart_apply` in `Tensor/RSTensor/Basis.lean` (its home layer, next to
`trivializationAt_apply`).  Theorem-form evaluation of the fixed-chart constant section:
`(constInChart s x₀ β x) v = β (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i))`.
Compiles **green without any transparency option** — the hack was never about constInChart's bundle defeq, only
about the downstream raw `rw [Tensor0SSpace.constInChart]` failing to match the wrapped term.  This is the
canonical "_apply lemma hides representation internals" fix.  (Add `constInChart_apply` to the "Already present"
list for future passes.)

**Block removed:** `constInChart_basisTensor0S_coordFrame` — rewritten via `ext0S_basis` + `basisTensor0S_component`
(RHS, no `basisTensor0S` unfold) + `component0S_apply` + `constInChart_apply` + `coordinateFrameAt_basis_continuousLinearMapAt`
+ model-basis Kronecker (`continuousMultilinearMap_basis_repr` + `Module.Basis.repr_self` + `Finsupp.single_apply`).

**Block kept (stop condition, bundle):** `tensorRS_eval_constInChart_coordinateFrame_contMDiffAt` — a `ContMDiffAt`
smoothness theorem; removing its hack gives `synthInstanceFailed` at the `TensorRSModel`/`Tensor0SModel` bundle
`TotalSpace`/`ContMDiffAt` instance sites (same family as `Tensor0S.lean`).  Belongs to the bundle-topology
workstream, not component-eval.

**Takeaway for the batch sweep:** component-eval blocks (those that `rw`/`simp` through `component0S`/`componentRS`/
`basisTensor0S`/`constInChart` evaluation) ARE removable with this API; bundle-smoothness blocks (`ContMDiffAt` of
bundle sections, `synthInstanceFailed` through bundle topology) are NOT — triage downstream files by that signal

## 2026-06-14 — Third pass: `TensorRS/ModelBridge.lean` component/model block removed

Validated the same pattern against
`Geometry/Coordinates/NablaComponents/TensorRS/ModelBridge.lean`, which had two
transparency wrappers.

**Block removed:** `tensorRSModelAt_coordComponentRSAt`.  The stale wrapper was on
a pointwise model/component identity.  The proof now changes the raw tensor-model
input side to the public `Tensor0SSpace.constInChart` surface, then uses
`constInChart_apply`, `ext0S_basis`, `basisTensor0S_component`, and the center
tangent-coordinate normalization
`TangentBundle.continuousLinearMapAt_trivializationAt_eq_core` +
`coordChange_self`.  Focused verification passed.

**Block kept (stop condition, model/topology):** `modelDeriv_eq_coordDerivRSAt`.
Empirically removing the wrapper exposes `TensorRSModel` normed-space,
topology, and fiber-bundle instance mismatches in the derivative/smoothness
bridge.  This is the same bundle/model-topology class as the kept
`ApplyInput.lean` smoothness block, not a component-eval problem.

**Sibling consumer audit:** `MetricTrace/Connection.lean`,
`Entropy/F/ChartTrace.lean`, and `Entropy/F/ConnectionTrace.lean` do not carry
local `respectTransparency false` wrappers in the inspected `constInChart`
consumer paths.  `MetricTrace/Connection.lean` consumes the now-clean
`constInChart_basisTensor0S_coordFrame`; `Entropy/F/ConnectionTrace.lean` has
ordinary component-simplification debt but no transparency wrapper to retire in
this batch.
before attempting removal.

## 2026-06-14 — Fourth pass: `MetricTrace/NablaTraceGen.lean` (1 component block removed, 9 → 8)

**Block removed:** `metricTraceFirstTwoField_eq_sum` — the pointwise coordinate formula.  Its hack was **stale**:
the proof is a pure pointwise `rw`-chain (`metricTraceFirstTwoField_apply` / `metricTraceFirstTwo0STensor_apply`
/ `metricTraceFirstTwo0SAt_eq_sum_basis`) with no `letI …bundle_topology`, no `DFunLike.ext`, no `ContMDiffAt`.
Removed and focused-check green; no new API lemma needed (the existing `_apply`/`_eq_sum_basis` lemmas match
without the transparency option).

**Blocks kept (bundle-section, load-bearing) — 8:** the `…Field` smooth-section defs and the field-level algebra
identities `_add`/`_smul`/`_zero`/`_domDomCongr_gen`/`_product` + `nablaRealizes_metricTraceFirstTwo`.  Tested
empirically: removing the 5 algebra hacks → `synthInstanceFailed` at the `Tensor0SField` statement type-class
binders + `rewrite failed` once `tensor0SBundle_topology` is unpinned (the file's own NOTE documents this `OfNat 0`
/ bundle-`Zero` synthesis-at-statement-time issue).  Restored.

**Refined triage signal (PER-THEOREM, not per-file):** component-eval and bundle-section transparency blocks
coexist in the same file.  Classify each block by its PROOF SHAPE:
- **component-eval (hack often stale/removable):** pointwise `=` at a point; proof is `rw`/`simp` through
  `_apply` / `_component` / `_eq_sum` / `component0S` / `componentRS` / `coordComponent` / `basisTensor0S` /
  `constInChart_apply`; NO `letI …bundle_topology`, NO `DFunLike.ext`/section ext, NO `ContMDiffAt`.
- **bundle-section (keep):** statement binds smooth `…Field`/`ContMDiffSection` or proves `ContMDiffAt`; proof
  needs `letI tensor0SBundle_topology`/`tensorRSBundle_topology` + `DFunLike.ext` / `contMDiff_…_iff_coord` /
  `trivializationAt` / `compContinuousLinearMap`; removing the hack → `synthInstanceFailed` at the field/bundle
  type-class sites.

**Inventory note (this area):** the `Geometry/Coordinates/NablaComponents` siblings are now exhausted for
component-eval blocks — `Basic.lean` (`modelDeriv_eq_coordDeriv0SAt`, derivative bridge), `OneForm/Smoothness.lean`
(4× `…contMDiffAt`), `Tensor0S.lean` (8× bundle topology) are all bundle-class; `ApplyInput`/`ModelBridge` done.
`Tensor/RSTensor/Coordinates/{Field,TensorRSModelEvalBasis}.lean` use FILE-LEVEL blanket options on
bundle/field-definition modules (not per-theorem component blocks).  Remaining per-theorem `…false in` candidates
to triage next: `MetricTrace/NablaTrace02.lean` (3, all `freeze…Field` — likely bundle), `MetricTrace/Trace04.lean`
(1, `trace04Field` — bundle), `Curvature/Riemann/Basic/Sections.lean` (5), and the `NablaOnTensors/Regularity/*`
+ `LocalFrameRegularity`/`Derivation` files (names suggest smoothness/bundle).

## 2026-06-14 — Fifth pass: `HCGCompactness/RicBoundGoodFrame.lean` (2 component blocks removed, 3 → 1)

**2 blocks removed (component-eval, both STALE):** `compL2_tower_le` and `sqrt_tower_le_compL2` — the good-frame
component `ℓ²` tower bounds.  Their component-eval core is `rw [component0S_apply]; … rw [IsLocalFrameOn.toBasisAt_coe];
rfl` (pointwise frame-component evaluation) wrapped in `Real.sqrt`/`pow` inequality algebra — no `letI bundle_topology`,
no `ContMDiffAt`.  The hacks were unnecessary; removed, focused-check green, no new API lemma.  (The file's own note
claimed `compL2_tower_le` "Needs the same `respectTransparency false` as B5" — that was stale; corrected in
`RicBoundGoodFrame.md`.)

**Block kept (bundle):** `ricCompField_mdiffOn` — `ContMDiffOn` smoothness producer for the realized Ricci frame
components.

**Triage confirmations this pass** (all matched the per-theorem proof-shape signal):
- `Curvature/Riemann/Basic/Sections.lean` (5): ALL bundle — `riemannCurvatureAt_contMDiff`/`riemannCurvature04At_contMDiff`
  (`contMDiff` + `letI …Bundle_topology`) and `rm13Section`/`rm04Section`/`ricciSection` (smooth-section `def`s).  Skip.
- `Connection/Chart/NablaComponents/Basic.lean` (1) + `Geometry/Coordinates/NablaComponents/Basic.lean` (1):
  `modelDeriv_eq_coordDeriv0SAt` — `mfderiv` derivative bridge with `letI tensor0SBundle_topology/_fiber/_vector`.  Bundle/derivative.
- `Tensor/Multilinear/{Tensor,Fiber}.lean`, `Tensor/Mixed/DualFiber.lean` (1 each): bundle-fiber `LinearEquiv`s via
  dimension counting / topology-diamond routing.  Bundle.
- `Connection/ChartFrame/ChartLieBracket.lean` (3): `mfderiv`↔`fderiv` chart-derivative bridges.  Derivative class.
- `Connection/LeviCivita/Curvature/Realized.lean`: `canRicField` (section equality → bundle); `nabla0SFun_perm`
  (pointwise slot identity but pulls in `tensor0SField_eval_smooth_slots_contMDiffAt`/`extDerivFun` → derivative class).
- `Connection/TensorNabla/IteratedTensorCovDeriv.lean` (1): `tensor03Cov_sub` — covariant-derivative subtractivity on
  an explicit (0,3) CLM-tower; pointwise algebra but NOT `component0S`/basis eval (out of strict scope; untested).

**Running total (item-4 component-eval removals): 5 blocks** — `ApplyInput.constInChart_basisTensor0S_coordFrame`,
`ModelBridge.tensorRSModelAt_coordComponentRSAt`, `NablaTraceGen.metricTraceFirstTwoField_eq_sum`,
`RicBoundGoodFrame.{compL2_tower_le, sqrt_tower_le_compL2}` + 1 new API lemma (`constInChart_apply`).
