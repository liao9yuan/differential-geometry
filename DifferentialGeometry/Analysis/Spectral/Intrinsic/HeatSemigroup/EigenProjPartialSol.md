# EigenProjPartialSol.lean — adapters B + C: the truncated nonlinearity solves on the same horizon, and its fixed point converges

`PSTOP_PROPOSITION.md` §10 adapters B and C (planner No. 128/129/130).  Status:
**both complete, sorry-free, axiom-clean.**  Each checked green first try.

> **2026-08-04 — READ THIS BEFORE REUSING THIS FILE.**  Everything here is
> stated over `partial_sol_const`, i.e. for a **globally Lipschitz**
> nonlinearity.  The `(N)` campaign's order-one solve is `partial_sol_tame`
> (`LowRegDenseSolve.lean:461`, `UnifClassBounds.lean:368`) and `lowregNfun` is
> provably NOT Lipschitz on its state ball, so `projN_lip`, `projN_single`,
> `forceMap_dist_le`, `projFix_dist_le`, `projFix_le_two` and
> `proj_partial_sol` cannot be instantiated there.  Use the tame twins in
> `EigenProjTameSol.lean` instead.  The Lipschitz-free lemmas — `projNfun`,
> `projN_zero`, `projFix_tendsto`, `projField_tendsto`, `projForce_fixed`,
> `projField_fixed` — ARE reused by the tame lane verbatim (`projN_nemytskii`
> is not: it mentions `nemytskiiOn`, so it has a tame twin).
> No file in the repo currently imports this one.

## Adapter B — what is proved

* `projNfun g₀ a N Nfun := fun u => Π_N (Nfun u)` — the spectrally truncated
  nonlinearity, on the *same* lower-order state ball `lowerState g₀ a R`.
* `projN_lip` — `LipschitzWith L Nfun → LipschitzWith L (projNfun …)` (the
  truncation is `1`-Lipschitz: `spatialProj_lip` from adapter A).
* `projN_zero` — the static bound `‖Nfun ⟨0,_⟩‖ ≤ D` passes with the same `D`.
* `projN_single` — the two-arm difference bound passes with the same `C₁, C₂`
  (one `map_sub` plus `norm_spatialEigenProj_apply_le`).
* `proj_partial_sol` — the capstone: `partial_sol_const` applied to
  `projNfun`.  The statement is written out in full so that the horizon is
  visibly the **identical closed form**

    `T₀ = min 1 (min (1/(64(C₂+1)²)) ((R/4)/(2(D+1)))²)`,

  with the same forcing radius `‖gforce‖ ≤ R/4` and the same state ball — and
  every constant free of the truncation level `N`.  `hsmall : C₁·R ≤ 1/8` is
  unchanged because `C₁` is.

So the projected (Galerkin) system is not a new solve: it is `partial_sol_const`
with `Π_N ∘ Nfun` in place of `Nfun`.  This is the Lean form of the §6.1 claim
"same radius, same horizon, `N`-free" — an identity, not an analogy.

## Home / layering

The file bridges the projector (`HeatSemigroup/`) and the ball-restricted
forcing fixed point (`…/TensorMaximalRegularity/PartialForcingFixedPoint.lean`),
which is the layer where adapter C (fixed-point stability) also belongs:
C's inputs `nemytskiiOn_mixed`, `maxRegDuhamelSolField_dist_le` and
`timeL2EigenProj_tendsto` are all in scope here.  Putting B beside
`partial_sol_const` instead would have forced the projector import down into
`Analysis/Parabolic/QuasiLinear/`, i.e. below `HeatSemigroup/`, inverting the
existing layering (`GalerkinForcingTimeL2Limit` already imports both this way).

## Lean notes

* `partial_sol_const` takes the four slots in the order
  `(Nfun) (hLip) (C₁ C₂ D) (hD) (hzero) (hsmall) (hsingle)`; `hzero` mentions
  the *specific* membership proof `zero_mem_lowerState g₀ a hR.le`, so
  `projN_zero` has to be stated against that same term.
* `simp only [projNfun, map_sub]` is the way to move between
  `Π(Nfun u) - Π(Nfun u')` and `Π(Nfun u - Nfun u')`; a `show` there trips
  `linter.style.show` (the goal genuinely changes).
* `LipschitzWith.comp` gives `1 * L`; `simpa [projNfun, Function.comp_def]`
  closes the `one_mul`.

## Adapter C — fixed-point stability and the Galerkin identification

The §7 design, realized.  Seven declarations, no new frontier:

* `projN_nemytskii` — the bridge that makes the whole thing collapse:
  `nemytskiiOn (Π_N ∘ Nfun) f = Π_N (nemytskiiOn Nfun f)`.  The projector acts
  pointwise in time, so truncating before or after the Nemytskii operator is the
  same map.  Consequence used below: at the *unprojected* fixed point `f_*`, the
  projected map evaluates to `Π_N f_*`, so the inhomogeneity of the two
  fixed-point equations is exactly the truncation defect of `f_*`.
* `forceMap_dist_le` — the contraction estimate `partial_sol_const` runs
  internally and does not export:
  `‖Φ F − Φ F'‖ ≤ (C₁R(1+T) + C₂·2√T)·‖F − F'‖`.
  Re-derived, not copied: the retraction `ρt` is dropped (both fixed points lie
  in the `R/4` ball where it is the identity), and the state-membership proofs
  become hypotheses, which is why the ball bounds do not appear at all.  Inputs
  are exactly the three public ones §7 named — `nemytskiiOn_mixed`,
  `maxRegDuhamelSolField_dist_le`, `maxRegDuhamelSolFieldHa1_dist_le` (through
  `timeL2Inclusion_maxRegDuhamelSolField`).
* `lamHalf` (private) — `Λ ≤ 1/2` from `hsmall : C₁R ≤ 1/8` and the horizon cap
  `T ≤ 1/(64(C₂+1)²)`, one quarter per arm.  Mirrors `partial_sol_const`'s
  `harm1`/`harm2` verbatim.
* `projFix_dist_le` — **the stability bound**
  `‖f_N − f_*‖ ≤ (1 − Λ)⁻¹ ‖Π_N f_* − f_*‖`, `Λ = C₁R(1+T) + C₂·2√T`.
  Hypotheses are *precisely* `partial_sol_const`'s / `proj_partial_sol`'s
  outputs: the two force-ball bounds `‖·‖ ≤ R/4` and the two a.e. Nemytskii
  identities.  The state memberships are re-derived internally from the ball
  bounds via `field_mem_lower`, so the caller passes nothing extra.
* `projFix_le_two` — the same with the absolute constant `2`; the modulus does
  not depend on `N`, `T`, `R`, `C₁` or `C₂`.
* `projFix_tendsto` — `f_N → f_*` in `timeL2`, from any bound of the shape
  `‖f_N − f_*‖ ≤ K‖Π_N f_* − f_*‖` plus `timeL2EigenProj_tendsto`.  Stated at a
  generic scale `σ` with an abstract `K`, so it carries no duplicate hypothesis
  block and is reusable for any projected family.
* `projField_tendsto` — the field-level corollary: the trajectories converge in
  the solve's own norm `L²([0,T]; H^{a+2})`, since `maxRegDuhamelSolField … 0` is
  `(1+T)`-Lipschitz in the forcing.  **This is the input the E1′/Z energy
  assembly consumes**: convergence is in `L²_t H^{a+2}`, not `C_t H^{a+2}`.
* `projForce_fixed`, `projField_fixed` — the `V_N`-valuedness at the
  *trajectory*: a forcing that is a.e. a value of `projNfun` satisfies
  `Π_N gforce = gforce` (by `spatialProj_idem`), and then `projDuhamel_zero`
  gives `Π_N field = field` at the gained regularity `H^{a+2}`.  Stated against
  an arbitrary `u : ℝ → lowerState g₀ a R` rather than `aeSetLift`, so
  `proj_partial_sol`'s output instantiates it directly.

The arithmetic of the stability step, for the record: with `x = Ψ_N f_N = f_N`
and `Ψ_N f_* = Π_N f_*`,

    ‖f_N − f_*‖ ≤ ‖f_N − Π_N f_*‖ + ‖Π_N f_* − f_*‖
              = ‖Ψ_N f_N − Ψ_N f_*‖ + ‖Π_N f_* − f_*‖
              ≤ Λ‖f_N − f_*‖ + ‖Π_N f_* − f_*‖,

and `1 − Λ ≥ 1/2 > 0` divides.  No compactness, no weak-* extraction, no
uniqueness theorem — §7's ruling in Lean.

## Lean notes (adapter C)

* `partial_sol_const`'s output gives the fixed-point equation as an *a.e.
  identity of functions* (`gforce =ᵐ fun t => Nfun (aeSetLift …)`), not as an
  identity of `timeL2` elements.  `MeasureTheory.Lp.ext ((nemytskiiOn_coeFn …
  ).trans h.symm)` is the one-line upgrade, and it is what lets `rw` fire on the
  contraction estimate afterwards.
* Do **not** try to `set` the Duhamel field to shorten the statements: `set` with
  a lambda does not fold the beta-redex `maxRegDuhamelSolField … fstar` that the
  hypotheses actually contain.  Writing the term out is longer but robust.
* The `hf` arguments of `nemytskiiOn` are `Prop`s, so proof irrelevance makes any
  two membership proofs interchangeable — but `rw` still needs the *syntactic*
  proof term to match, so pass the same `hSs`/`hSN` everywhere.
* `inv_mul_eq_div` + `le_div_iff₀` + `nlinarith` is the rearrangement of
  `d ≤ Λd + e` into `d ≤ (1−Λ)⁻¹ e`; plain `linarith` fails because `Λ*d` and
  `d*Λ` are distinct atoms.
* `projField_tendsto` is the only declaration in the file that does not touch the
  projector, so it needs `omit [BoundarylessManifold I M] in`.

## Verification

Focused checks clean on both files; targeted module builds green in dependency
order (`EigenProjDuhamel` 9227 jobs → `EigenProjPartialSol` 9541).  Axiom census
of all nine new public declarations (`spatialProj_idem` plus adapter C's eight):
`propext, Classical.choice, Quot.sound` only — zero `sorryAx`.  No
`maxHeartbeats`; file at 582 lines.

## Layering debt (deliberate)

`forceMap_dist_le` is a statement about `partial_sol_const`'s forcing map with no
projector in it, so its canonical home is beside `nemytskiiOn_mixed` in
`…/TensorMaximalRegularity/PartialForcingFixedPoint.lean`.  It is parked here
because that file was declared read-only for this brick (the contraction had to
be re-derived, not extracted).  Adapter C is its only consumer; the move is pure
cut-and-paste if `PartialForcingFixedPoint.lean` is ever opened for edit.
