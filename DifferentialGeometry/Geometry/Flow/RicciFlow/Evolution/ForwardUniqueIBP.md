# ForwardUniqueIBP.lean — brick K2.7 (forward-uniqueness lane)

**Status: OUTCOME (A). 389 lines, 9 public + 3 private declarations, 0 `sorry`.**
Focused check green, targeted `build` green (8862 jobs), zero warnings in this file.
`#print axioms` on all nine public declarations: exactly `propext, Classical.choice,
Quot.sound`. Hardened hygiene sweep clean (no `axiom`/`instance`/`notation`/`opaque`/
`macro`/`elab`/`syntax`, in any modifier-prefixed form).

## What this file provides

The lane speaks `Tensor0SField … s` with `metricNabla0S` / `covDiv0SField`
(`ForwardUniqueRmDiff.lean`). The Green/IBP layer speaks `SmoothCcTensor g 0 s` with
`covGrad` / `covDivergence`. This file is the dictionary.

1. `ccLift0S g T : SmoothCcTensor g 0 s` — the lift. Section = `unitScalarRSLiftCₛ T`;
   compact support = `HasCompactSupport.of_compactSpace _`. Evaluation lemmas
   `ccLift0S_toSection` (`rfl`), `ccLift0S_unit`, `ccLift0S_unitModel`.
   **No smoothness hypothesis is needed**: `Tensor0SField … ∞ s` *is*
   `Cₛ^∞⟮I; Tensor0SModel s ℝ E, fun y => Tensor0SSpace s I y⟯`, which is exactly the input
   type of `unitScalarRSLiftCₛ`, and that lemma discharges smoothness of the lift itself.
   So the only inputs are the lane's own field plus the standing `[CompactSpace M]`.
2. `covDerivLift_unit` — `(∇^{RS}_v (lift T))(x)(unit)(slots) = metricNabla0S g T x (cons v slots)`.
   `covDivLift_unit` — `(covDivergence g s (lift V))(x)(unit) = covDiv0SField g V x`.
   Bundled forms: `covGradLift_eq`, `covDivLift_eq` (equalities of `SmoothCcTensor`).
3. `l2Inner_nabla_eq_neg_div` — the K4 entry point, in lane currency:
   `⟨∇^g T, V⟩_{L²(g)} = −⟨T, div_g V⟩_{L²(g)}`.
   `l2Inner_nabla_self_eq_neg_lap` — the Dirichlet partner
   `⟨∇^g T, ∇^g T⟩ = −⟨T, Δ_g T⟩` with `Δ_g = roughLap0SField g` (free specialisation at
   `V := metricNabla0S g T`, since `roughLap0SField = covDiv0SField ∘ metricNabla0S` by
   definition).

The conventions did agree, as pre-checked: both sides contract the new derivative slot
against the tensor's slot `0`. The identification needed no convention repair.

## THE COST — `[InnerProductSpace ℝ E]` taint (report to planner)

This file carries `[InnerProductSpace ℝ E]`, `[NeZero (Module.finrank ℝ E)]`,
`[Module.Finite ℝ E]`, `[CompactSpace M]`, `[I.Boundaryless]`, `[BoundarylessManifold I M]`
— none of which the rest of the lane has. **This is forced, not chosen.** Verified by
`#check`: `covDivergence` and `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`
both carry `[InnerProductSpace ℝ E]` in their signatures, because their orthonormal frame
`smoothOrthoFrame_orthonormal_at_center` is built in the model space. So the K2.7
identification statement **cannot be typed** without it. Consequences:

* Any K4 consumer of `l2Inner_nabla_eq_neg_div` inherits the taint.
* Declare `[InnerProductSpace ℝ E]` and let `NormedSpace ℝ E` be *derived*
  (`InnerProductSpace.toNormedSpace`). Do **not** declare both — that is a real diamond.
* Campaign-end dedup item (joins №3/№8's list): the `omit` campaign belongs on the
  Green/IBP producers (`TensorCovDivergence.lean`'s variable block and the
  `smoothOrthoFrame` orthonormality producer), not here.

## Lean lessons (durable)

* **`Tensor0SSpace` has its OWN `FunLike` instance** (`tensor0SSpace_instFunLike`,
  `Tensor/RSTensor/Defs.lean:144`), separate from `ContinuousMultilinearMap`'s. Consequence:
  `ContinuousMultilinearMap.ext` on a `Tensor0SSpace` goal produces an application through
  the **CMM** coercion, while any lemma you state about `Tensor0SSpace` elements uses the
  **Tensor0SSpace** one. `rw` then fails with "did not find an occurrence" on terms that
  print *identically*. **Fix: use `DFunLike.ext _ _ fun m => ?_`, not
  `ContinuousMultilinearMap.ext`,** when the goal type is `Tensor0SSpace`. This cost a full
  debug cycle; the identical-looking pattern/target is the diagnostic signature.
* **Sum-crossing at `TensorRSSpace`.** `ContinuousLinearMap.sum_apply` will not fire on a
  `Finset.sum` elaborated at `TensorRSSpace 0 s I x`. Force the sum to elaborate at the CLM
  type by ascribing each summand:
  `∑ i, (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from …)`; the resulting
  `hraw : (covDivergence …).toSection x = ∑ …` is still `rfl`, and `rw [hraw,
  ContinuousLinearMap.sum_apply]` then works. (Idiom copied from
  `CovDivergenceRoughLaplacianCommutation.lean:145`.)
* For the analogous sum at `Tensor0SSpace`, a 6-line private `tensor0SSum_apply` by
  `Finset.cons_induction_on` with `rfl` steps is cheaper and far more robust than the
  `← toModelL_apply / map_sum / ContinuousMultilinearMap.sum_apply` dance — *provided* the
  ambient ext is `DFunLike.ext` so the coercion paths agree.
* **`show … from` is `letFun`** (prints as `have this := …; this`). Harmless for `exact`/
  term-mode, but it is what blocks `rw` when the *inner* sum instance is wrong. Do not
  blame the wrapper before checking the instance.
* Avoid `rw` under a FunLike application when rewriting the *function*; use
  `congrArg (fun A : Tensor0SSpace s I x => A slots) key |>.trans …` instead. Used in
  `covDerivLift_unit`.
* Beta-reduction: `metricInverseInBasis_of_orthonormal` returns the gInv as the *lambda*
  `fun a k => if a = k then 1 else 0`; after `metricTraceFirstTwo0SAt_eq_sum_basis` the goal
  has `(fun a k => …) i j` unreduced and `rw [if_pos …]` cannot see the `ite`. Insert a
  `change` first.
* Direct-`lean` axiom audit needs **Windows-style** `LEAN_PATH` entries (`E:/…`), not msys
  `/e/…`; the latter fails with "unknown module prefix".

## Reused, not reinvented (per project search rule)

* `unitScalarRSLiftCₛ` + `unitScalarRSLiftSection_apply_unit`
  (`Connection/ChartTensorNabla/Agreement/Tensor0SRSCovariantDerivativeAgreement.lean`).
* `covDeriv_unit_eval_eq_genVal` (`Geometry/Curvature/CovGradRoughLap/GradientField.lean:257`)
  — the RS→0S unit-transport; **better than** the agreement theorem
  `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative` for this purpose because it
  works for an arbitrary section, not only for a lift.
* `nabla0SFun_eq_tensor0SCovariantDerivative` (`…/Agreement/Nabla0SFunAgreement.lean:338`)
  and `totalNabla0SFun_apply_section` (`Tensor/RSTensor/NablaOnTensors/HigherOrder.lean:231`)
  — the two halves of `metricNabla0S ↔ tensor0SCovariantDerivative`. The three-step chain is
  the same one `HCGCompactness/MetricCovDerivBridge.lean:100-152` uses; that file was the
  route template.
* `metricInverseInBasis_of_orthonormal` (`Geometry/Curvature/Components/RicciTrace.lean:31`)
  — public; no need to reprove the lane's private `onFrame_inv`
  (`ForwardUniqueRmBounds.lean:95`). **Dedup note:** `ForwardUniqueRmBounds.onFrame_inv` is
  now a redundant private copy of this public lemma.
* `smoothCcTensor_ext_of_unitModel` + `unitModel`
  (`Analysis/Spectral/Tensor/CovGrad/RicciDeTurckLinearization.lean:125`,
  `…/CovGradSlotPermutationNaturality.lean:94`) — the only clean way to prove two
  `SmoothCcTensor`s equal; avoids hand-rolling "a `TensorRSSpace 0 s` element is determined
  by its value at the unit".
* `covGrad_apply_unit_eval_genVal` + `tensorCovDerivAt_def` — `covGrad`'s unit evaluation.

Only genuinely new private helpers: `tensor0SSum_apply`, `orthoBasisAt` (a local replica of
the **private** `centeredFrame_basis_exists`, `TensorCovDivergence.lean:963` — candidate for
promotion to public in the Green/IBP layer), `traceFirstTwo_eq_frame_sum`
(g-trace of slots 0,1 = orthonormal diagonal frame sum; **this one deserves promotion** to
`Geometry/Operator/RoughLaplacian.lean` next to `metricTraceFirstTwo0SAt_eq_sum_basis`, since
it is generic and reusable).

## Remaining risk / next

* No mathematical frontier left in this brick.
* The `[InnerProductSpace ℝ E]` inheritance is the one design decision the planner must
  ratify before K4 builds on `l2Inner_nabla_eq_neg_div`.
* If K4 wants the pairing against a *lane-native* L² inner product rather than
  `tensorL2Inner … (ccLift0S …).toFun`, add a thin `Tensor0SField`-level L² pairing
  abbreviation plus a `rfl`-lemma to this file; do not restate the IBP.
