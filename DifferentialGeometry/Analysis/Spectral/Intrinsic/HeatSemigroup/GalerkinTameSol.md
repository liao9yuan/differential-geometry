# GalerkinTameSol.lean — notes

Status: **GREEN, sorry-free, axiom-clean** (all declarations
`[propext, Classical.choice, Quot.sound]`).  Created 2026-08-04 as brick (1) of
the (N) campaign's front-2 Galerkin lane.

## What this file is

The `V_S` Galerkin ODE system for a nonlinearity that is only **tame** (three
arms, the third carrying the ambient `H^{a+2}` norm) on the state ball
`lowerState g₀ a R`, i.e. NOT globally Lipschitz.  It is the low-regularity
counterpart of `deTurckGalerkin_solution_existsSymm`
(`GalerkinParabolicEnergyDeTurck.lean:733`), whose `2·finrank ℝ E + 10 ≤ a`
gate is about a genuinely different (globally Lipschitz) nonlinearity and must
**not** be lowered.

## The mathematical route that worked

The whole brick turns on one observation.

* `tame_lip_balls` (`TameForcingFixedPoint.lean:64`) converts the three-arm
  estimate into `LipschitzOnWith K Nfun {x ∈ D | ‖x‖_{a+2} ≤ r}` for each `r`.
  So the only thing missing is a **top-norm** bound on the argument.
* On a truncation `V_S` with `1 + λᵢ ≤ κ`, `‖u‖_{a+2} ≤ √κ ‖u‖_{a+1}`
  (`galTopNormLe`).  Hence the state ball, which bounds only `‖·‖_{a+1}`, IS
  top-norm bounded on `V_S`, with radius `√κ · R`.
* Therefore the *whole* state ball, not some smaller `H^{a+2}` ball, is the
  region on which the Lipschitz constant exists.

That fixes the design of the retraction.  It must be an `H^{a+1}` retraction
(the state ball is an `H^{a+1}` ball), because:

* the ODE solution has an `N`-uniform `L^∞_t H^{a+1}` bound available from
  parabolic maximal regularity, but **only an `N`-dependent** `L^∞_t H^{a+2}`
  bound (`L²_t H^{a+2} ∩ H¹_t H^a ↪ C_t H^{a+1}`, and no better).  An
  `H^{a+2}` retraction would be inert only on an `N`-dependent region and would
  be useless to brick (3).

The `H^{a+1}` retraction is `galTameRetr w = min 1 (R / ‖J (Emb w)‖) • w`.  Two
free facts make it cheap:

* it is **conjugate** to the existing `ballRetraction` on `H^{a+1}`
  (`galTameRetr_view`), by linearity of `J ∘ Emb`; so `ballRetraction`'s
  `_mem_closedBall`, `lipschitzWith_`, `_eq_self_of_mem` all transfer;
* `‖w‖_{Euclid} ≤ ‖J (Emb w)‖_{a+1}` (`galCoordNormLe`), because every Sobolev
  weight at a non-negative exponent is `≥ 1`.  This antilipschitz bound is what
  transports the retraction's `H^{a+1}` `1`-Lipschitz property back to
  coordinates, and it also gives `‖J(Emb w)‖ = 0 ⟹ w = 0`, closing the
  degenerate branch of the inertness lemma.

The field is then `−Λ w + Π_S N(retract w)`, globally Lipschitz
(`galTameField_lip`) with a global affine bound (`galTameField_aff`, the
constant term only — the retraction caps `N` entirely), and
`forward_solution_of_lipschitzWith_affineBound`
(`Analysis/ODE/GlobalLipschitzAffineExistence.lean`, gate-free) gives a
solution on the **whole** `[0, T]` for every `T`, with no smallness.

## Export inventory

Norm comparisons: `galLowView` (abbrev), `galEmbedCombo`, `galViewComboC`,
`galViewCombo`, `galCoordNormLe`, `galTopNormLe`, `galEmbTopLe`.

Retraction: `galTameRetr`, `galTameStateC`, `galTameState_eq`,
`galTameStateC_emb`, `galTameRetr_view`, `galTameRetr_mem`,
`galTameStateC_mem`, `galTameRetr_eq`, `galTameStateC_eq`, `galTameRetr_top`,
`galTameState_lip`.

Field: `galTameBall`, `galTameRetr_ball`, `galTameField`, `galTameField_apply`,
`galTameField_lip`, `galTameField_aff`.

System: `galTameForce`, `galTameForce_apply`, `galTameForce_eq`,
`galTameForce_contOn`, `galTameSolOne`, `galTamePerMode`.

## M2a / M2b — the two adapters over `galTameForce` (2026-08-04)

Both landed as designed in `ShortTime/M2_FORCING_PLAN.md` §3, no route change.

* `galTameForce_contOn` (M2a) — continuity in `t` of the forcing coordinate
  along a continuous coefficient family.  **Route B of the plan, as written**:
  `galTameField_lip` gives `LipschitzWith K' (galTameField …)`, hence a
  continuous field; the forcing is that field's `i`-th coordinate plus the
  diagonal term put back,
  `F(c t) i = (galTameField … (w t)) ⟨i,hi⟩ + λᵢ · c t i` on `S`, and
  `continuousOn_const` off `S`.  Route A (the `GalerkinLimitUniformMass.lean:33`
  mirror through `galTameState_lip` + subtype continuity) was never needed.
* `galTamePerMode` (M2b) — the mechanical port of the private
  `galerkinPerMode_eq_perModeConvSymm` (`GalerkinLimitUniformMass.lean:70`)
  with the `ha_super` binder deleted; it compiled on the first attempt.  Only
  `perModeConv` needed a namespace: `open
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity in`, since this
  file does not open `MaximalRegularity` (the import is in cone via
  `GalerkinParabolicEnergyDeTurck → Plancherel → PerMode`; **zero import
  churn**).
* `galTameStateC_emb` — the one new bridge the plan did not list.
  `galTameState_eq` runs coordinates → coefficient family and lands on
  `fun i => if h : i ∈ S then w ⟨i,h⟩ else 0`, not on the caller's `c`; the
  bridge is the converse reading, and its content is that `galTameStateC`
  only sees `c` through `finiteEigenComboHs … S c`, i.e. only on `S`.  It is
  stated for the canonical coordinate vector
  `(EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c j.1)`.

Signature note for the consumers: both adapters take `hK : LipschitzOnWith K
Nfun (galTameBall …)`, matching `galTameField_lip`/`galTameField_aff` — the
weakest-hypothesis form — **not** `galTameSolOne`'s `A B C Rt + htame`.  A call
site holding the tame estimate gets `hK` by the same five-line `obtain` that
`galTameSolOne` runs internally (`tame_lip_balls … Nfun 0 id isometry_id rfl
(galLowView g₀ a) A B C Rt hA hB hC hRt htame (Real.sqrt κ * R)`); it is not a
new obligation.  Satisfiability at `a = 1` is already witnessed in the tree:
`ShortTime/LowRegGalerkinSol.lean:155–166` supplies `hκ0`, `hκ` and that same
`htame` to `galTameSolOne` for `S = eigenIdxFinset g₀ N`, and `lowregGalSol`'s
own four conjuncts are exactly `galTamePerMode`'s `hcont`, `hderiv` and
`hzero`.

## Honest limitation (read before brick (3))

`galTameSolOne` reports the ODE with the forcing evaluated at the **retracted**
state.  `galTameForce_eq` discharges the retraction the moment the state
satisfies `‖J (combo of U N t)‖_{a+1} ≤ R` — the true state-ball condition, and
`N`-uniform.  Producing that bound is *not* done here.  It is a Grönwall
argument on `d/dt ‖U‖²_{a+1}`:

    ½ d/dt ‖U‖²_{a+1} = −‖U‖²_{a+2} + ‖U‖²_{a+1} + ⟨U, f⟩_{a+1}
                      ≤ −‖U‖²_{a+2} + ‖U‖²_{a+1} + ‖U‖_{a+2}‖f‖_a

with `‖f‖_a ≤ D' + (A·Rt + C·R)‖U‖_{a+2}` and `A·Rt + C·R ≤ 1/8` from the two
smallness certificates (`lowregOuterRad_small`, `lowregStateRad_small`), so the
`‖U‖_{a+2}` terms absorb into `−‖U‖²_{a+2}` and Grönwall gives
`‖U(t)‖²_{a+1} ≤ D'²(e^{2t} − 1)`, `N`-uniformly, hence the ball for
`T ≲ log(1 + R²/D'²)/2`.  That is a genuinely separate brick (call it 1b), and
its horizon condition would have to be calibrated against `lowregHorizon`.

## Lean lessons

* `abbrev galLowView` is reducible, so `lowerState`'s inline
  `tensorHsInclusion …` membership goals close with `change`, and the campaign's
  `htame` (written with the inline inclusion) is accepted verbatim by the
  generic `htame` written with `galLowView`.  Proof irrelevance handles the two
  different `(a:ℝ)+1 ≤ (a:ℝ)+2` proof terms.
* `set L := f.comp g with hL` does NOT re-fold later rewrites.  Prove
  `hLapp : ∀ x, L x = f (g x) := fun _ => rfl` and rewrite with that instead of
  fighting `ContinuousLinearMap.comp_apply`.
* Subtype congruence under a function: `congr 1; congr 1; exact Subtype.ext h`
  fails (metavariables).  State the subtype equation as a `have`
  (`… = ⟨…, …⟩ := Subtype.ext h`) and `rw` it.
* `norm_nonneg _` for a `ContinuousLinearMap` picks the wrong `Norm` instance
  path; name the operator (`norm_nonneg Rst`).
* `galerkinCoordEmbed_coeff` produces a `dite`, `finiteEigenComboHs_coeff` an
  `ite`; the negative branch needs BOTH `if_neg` and `dif_neg`.
* `w ⟨i, h⟩` for `w : EuclideanSpace ℝ {i // i ∈ S}` elaborates to
  `w.ofLp ⟨i, h⟩`, which is what `EuclideanSpace.proj` produces, so the two
  forms bridge by `rfl`.
* The `show` style linter fires on goal-changing `show`; use `change`.
* `ContinuousOn.add` returns `ContinuousOn (f + g)`, so the goal handed to
  `ContinuousOn.congr` afterwards is `… = (f + g) t`, not `… = f t + g t`.
  `simp only [Pi.add_apply]` first; otherwise every subsequent `rw` misses.
* `rw`'s trailing `rfl` is weaker than `rfl`.  After
  `rw [galTameField_apply, hsub]` the residue
  `-(↑⟨i,hi⟩).lambda * (…).ofLp ⟨i,hi⟩ = -i.lambda * c t i` (projection of a
  constructor, plus the `EuclideanSpace.equiv.symm` application) is left open;
  an explicit `rfl` closes it.  Do not reach for `ring` there — its atom
  matching would have to see through both.
* To rewrite `galTameStateC` under a changed coefficient family, do not try to
  `congr` (the two families genuinely differ off `S`).  Prove the restricted
  congruence as a local `∀ c', (∀ i ∈ S, c' i = c i) → …` and close the
  instantiation with `exact key _ (fun i hi => dif_pos hi)` — the `dite`
  redex is discharged by defeq, so the lambda never has to be written out.

## Verification

Focused check green; targeted build green (9573 jobs).  Axiom census (scratch
`#print axioms` file outside the repo, run under `lake env lean` after the
targeted build): `galTameStateC_emb`, `galTameForce_contOn`, `galTamePerMode`
and `galTameSolOne` each `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`.  No file outside `GalerkinTameSol.lean` was touched.
