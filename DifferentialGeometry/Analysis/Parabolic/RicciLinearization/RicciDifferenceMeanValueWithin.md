# `RicciDifferenceMeanValueWithin.lean` — ruling R12, the half-open-slab tower

## 2026-07-26: delivered, 0 sorry, 3-axiom clean

New **additive** file.  `RicciDifferenceMeanValue.lean` was not touched, and neither were the
four `private` helpers of `Evolution/ForwardUniqueDensReg.lean` (R12(b) permission not used —
see §"What was reused vs re-proved").

## What the file is for

The forward-uniqueness black box (B) supplies its chart-Gram regularity on a **half-open**
slab, `ContMDiffOn … (Ico a b ×ˢ baseSet)` — one-sided in time at the initial time `a`
(`Evolution/ExtendViaUniqueness.lean`, `ricci_flow_forward_unique`'s `h1smooth`/`h2smooth`).
The settled tower `GenJointGram → gen_joint_christoffel → gen_joint_riemann` demands a
**two-sided** `ContDiffAt` in `(s, y)` at every `s₀` of the time set, so it cannot be fed at
`s₀ = a`.  That was the single blocker recorded in `Evolution/ForwardUniqueSup.md`
§"The closed-edge blocker": every remaining `ForwardUniqueSlab` field needs
`sup_{Icc a c × M}` of a curvature-type background quantity, and the extreme-value theorem
needs joint continuity up to the **closed** edge.

## Why it re-threads (the mathematics)

Every step of the tower differentiates **only in the spatial variable**.  So in
`ContDiffWithinAt.fderivWithin_apply` the parameter set is `s := S ×ˢ U` and the
differentiation set is `t := U`; unique differentiability is required of `U` **only**.  With
`U = interior (extChartAt I α).target` (open) this is free, and the time set `S` is completely
arbitrary — no `IsOpen`, no `UniqueDiffOn`, no `Icc`/`Ico` shape assumption anywhere in the
file.  `fderivWithin ℝ · U = fderiv ℝ ·` on the open `U` then returns the tower's own
`partialDeriv`.

That is the whole content of the closed-edge fix.  It is why the ruling's estimate ("routine")
was right.

## Chain map: original ↔ Within

| `RicciDifferenceMeanValue.lean` (`ContDiffAt`) | this file (`ContDiffWithinAt`) |
| --- | --- |
| `gen_joint_partialDeriv` (via `ContDiffAt.fderiv`) | `partialDerivWithin` (via `ContDiffWithinAt.fderivWithin_apply`) + `partialDeriv_of_isOpen` |
| `GenJointGram` (`:401`) | `GenJointGramOn` |
| — | `genJointGramOn_of_gen` (two-sided ⟹ within) |
| `gen_joint_invGram` (`:476`) | `invGramWithin` |
| `gen_joint_gramBracket` (`:600`) | `bracketWithin` |
| `gen_joint_christoffel` (`:619`) | **`christoffelWithin`** |
| `gen_joint_partial_christoffel` (`:673`) | `partChristWithin` |
| `gen_joint_riemann` (`:683`) | **`riemannWithin`** |
| `gen_joint_ricci` (`:707`, `private`) | `ricciWithin` (public) |
| `genGram_of_joint` (DensReg, `private`, needs `IsOpen J`) | `genGramOn_of_field` (public, `J` arbitrary) |
| `jointOnM` (DensReg, `private`) | `jointOnMWithin` |
| `christJoint` / `riemJoint` (DensReg, `private`) | `christWithinM` / `riemWithinM` |
| — | `christSlabCont` / `riemSlabCont`, `christSlabContAt` / `riemSlabContAt` |

Ten of the eleven mirrored proofs are line-for-line the original with `ContDiffAt →
ContDiffWithinAt`, `contDiffAt_const → contDiffWithinAt_const`, `ContDiffAt.sum →
ContDiffWithinAt.sum`, `contDiffAt_prod → contDiffWithinAt_prod`, `ContDiffAt.comp →
ContDiffAt.comp_contDiffWithinAt`.  All the algebra (Cramer determinant/adjugate expansion,
Koszul bracket, `Γ = ½ G⁻¹ S`, `R = ∂Γ − ∂Γ + ΓΓ`) is unchanged: it is set-independent.

**No chain step failed to re-thread.**  The only genuinely new proof is `partialDerivWithin`.

## The compatibility guard

`christWithin_of_open` / `riemWithin_of_open` take `IsOpen S` and return exactly
`gen_joint_christoffel` / `gen_joint_riemann`'s `ContDiffAt` conclusions, by
`ContDiffWithinAt.contDiffAt` against `(hS.prod isOpen_interior).mem_nhds`.  Together with
`genJointGramOn_of_gen` (input direction) this is a full round trip: nothing was lost or
weakened in the re-threading.  The composed round trip was machine-checked as a scratch
`example` with the original's verbatim signature, as were two more guards:

* (B)'s verbatim `h1smooth` field feeds `christSlabCont` / `riemSlabCont` directly;
* `christSlabContAt` has the `slabBound`-shaped `ContinuousWithinAt … (Icc a c ×ˢ univ)` type.

## What was reused vs re-proved

* **Reused unchanged** (imported from the settled parent / Mathlib): `chartGramOnE`,
  `chartInvGramOnE`, `gramBracket`, `chartChristoffel`, `chartRiemannTensor`,
  `chartRicciTensor`, `chartChristoffel_eq_sum_invGramOnE_bracket`, `chartGramMatrix_det_pos`,
  `partialDeriv`, `extChartAt_target_subset_interior_of_boundaryless`,
  `trivializationAt_baseSet_eq_chartAt_source`, `GenJointGram` (for the guard).
* **Re-proved in `Within` form** (structurally forced, cannot be adapted): the eleven rows of
  the table above.
* **`ForwardUniqueDensReg.lean`'s four `private` helpers were NOT made public.**  R12(b)
  allowed it, but reuse would have shortened nothing: `genGram_of_joint` carries the very
  `IsOpen J` hypothesis this file exists to remove, and `jointOnM` / `christJoint` /
  `riemJoint` are the two-sided statements.  All four had to be restated anyway, so the
  minimal-diff choice was to leave that settled file untouched.

## Consumer surface for `Evolution/ForwardUniqueSup.lean`

`christSlabCont` / `riemSlabCont` take `hcb : c < b` plus **exactly** (B)'s field
(`ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ) ∞ (fun p => chartGramMatrix (g p.1) x₀ p.2 i j)
(Ico a b ×ˢ baseSet)`) and return `ContinuousOn … (Icc a c ×ˢ baseSet)`.
`christSlabContAt` / `riemSlabContAt` restate that at the chart centre within
`Icc a c ×ˢ univ`, which is `slabBound`'s own set.

Chart quantities cannot be `ContinuousOn` on `Icc a c ×ˢ univ` (a chart does not cover `M`),
so the `univ` form is necessarily the pointwise-at-the-diagonal one — the same design as
`normSq0S_jointContMDiffOn`'s `hA` hypothesis, which is stated at `(t, x₀)` with the chart
centred at `x₀` for exactly this reason.

## The remaining step to a background sup (NOT done here, and out of R12's scope)

`normSq0S_jointContMDiffOn` (`ForwardUniqueDensReg.lean:216`) — the brick that turns chart
components into an intrinsic `|A|²_{g t}` — still carries `hJ : IsOpen J`.  It uses `hJ` in
exactly two places, both routine to re-thread:

* `hnhd : J ×ˢ e.baseSet ∈ nhds (t, x₀)`, consumed by `.contMDiffAt hnhd`;
* the same `hnhd` in `filter_upwards` for the `normSq0S_eq_coord` local identity.

Both become `𝓝[J ×ˢ univ] (t, x₀)` memberships, which hold for **any** `J` because
`J ×ˢ baseSet = (J ×ˢ univ) ∩ (Prod.snd ⁻¹' baseSet)` and `baseSet` is an open neighbourhood of
the chart centre — this file's private `slabBase_nhdsWithin` is that argument, specialized to
`Icc a c`.  Then `connChartJoint` / `rmChartJoint` re-thread against `christWithinM` /
`riemWithinM`, and `slabBound` finally fires.  That is one file's work in
`ForwardUniqueDensReg.lean`, which was left untouched here.

## Lean lessons from this pass

* `ContDiffWithinAt.fderivWithin_apply` (Mathlib `Analysis/Calculus/ContDiff/Comp.lean`) is
  the right entry point, not `ContDiffWithinAt.fderivWithin`: taking the constant map
  `k := fun _ => chartModelBasis E q` as its third argument produces the *scalar* directional
  derivative directly and skips a `ContinuousLinearMap.apply` composition step.
  `hmn : m + 1 ≤ n` is discharged by `le_refl _` at `m = n = ∞`, exactly as in the original.
* The inner-uncurry argument is cleaner as `ContDiff … |>.contDiffWithinAt` than as a
  `ContDiffWithinAt` composition: `((contDiff_fst.comp contDiff_fst).prodMk
  contDiff_snd).contDiffWithinAt` avoids threading a second set through `.comp`.
* **Closing and re-opening a namespace drops every `open` issued inside it.**  A first draft
  split the file into two `namespace RicciLinearization` blocks; the second block lost
  `open …Integral.Measure` etc., and with `autoImplicit` on (the default in this subtree)
  `chartGramMatrix` silently became an auto-bound *variable* instead of erroring on the
  identifier.  The tell is a goal display containing `chartGramMatrix : x✝¹` and cascading
  "Invalid argument name `I` for function" errors.  Fix: one namespace block, `section`s for
  local `variable`s, and `set_option autoImplicit false` at the top of the file.
* `⟨fun … , fun _ hs _ hx => hG.2 hs hx⟩` does not bind strict-implicit binders the way it
  reads; `refine ⟨…, ?_⟩ ; intro s₀ hs x hx` does.  The tell is "argument `hs` has type `M`".
* Restructuring the `variable` block (dropping `[CompactSpace M] [T2Space M]
  [SigmaCompactSpace M]` entirely, and scoping `[I.Boundaryless]` to the consumer `section`)
  removed all but five `unusedSectionVars` warnings; the remaining five are `omit … in` lines.

## Verification

Focused check green and warning-free; targeted module build green; zero `sorry`.
`#print axioms` on all thirteen public endpoints (`partialDerivWithin`, `christoffelWithin`,
`riemannWithin`, `ricciWithin`, `christWithin_of_open`, `riemWithin_of_open`,
`genGramOn_of_field`, `christWithinM`, `riemWithinM`, `christSlabCont`, `riemSlabCont`,
`christSlabContAt`, `riemSlabContAt`) returns exactly `[propext, Classical.choice, Quot.sound]`.
The four guard `example`s type-check.

613 lines.  **Not** wired into the root aggregate — that is the planner's step, as for the
other lane files.

## Accounting

`christoffelWithin` / `riemannWithin` and the `ContinuousOn` corollary: 100% (proved, sorry-free).
The R12 gate they were asked to open is fully open.

This is **one input layer** of the (B) forward-uniqueness endgame, not the endgame.  In whole-
project terms: the closed-edge blocker of `ForwardUniqueSup.md` §"Next targets" item 1 is
discharged for the Christoffel/Riemann tower itself; the background-norm sups it unblocks
(`volLe`'s regularity input, `fluxLe`'s three constants, `reactLe`'s `sup |Ric₁|`, three of
`adotLe`'s four) are still **0%** — each additionally needs the `normSq0S_jointContMDiffOn`
re-thread described above plus its own carrier wiring.  `ForwardUniqueSlab` remains
unconstructed; `ricci_flow_forward_unique` (`ExtendViaUniqueness.lean`) remains a `sorry`.
