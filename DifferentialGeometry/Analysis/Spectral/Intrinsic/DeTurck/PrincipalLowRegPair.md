# PrincipalLowRegPair

## Goal

Construct the adjacent-scale `H3 → H1` realization of the same
inverse-cometric principal correction used by `lowRegPrincipal : H4 → H2`,
then prove one small `H2` metric ball controls both operators and their
Sobolev-inclusion commuting square.

## Current state

- `lowRegPrincipalLo` is the canonical `H3 → H1` completion of the same
  inverse-cometric principal correction as `lowRegPrincipal : H4 → H2`.
- `principalLo_core` identifies it on smooth tensors with
  `deTurckPrincipalCometricArm`.
- `principal_pair_norm` gives one positive spectral `H2` metric radius and
  linear operator-norm bounds for both adjacent-scale operators.
- `principal_comm` proves the high/low Sobolev-inclusion commuting square on
  one positive spectral `H2` metric ball.
- The proof constructs the `H1` perturbation directly from the existing
  fixed-order `H2 × H1 → H1` action estimate, then transfers the inverse by an
  exact intertwining identity. No extra geometric decomposition or higher
  metric regularity is introduced.

Focused verification and the targeted exact module refresh pass with no
`sorry`, `admit`, `axiom`, `whnf`, or trace diagnostics.

## Project accounting

- This adjacent principal-pair module: complete (100%).
- The public uniform-existence theorem `(N) ricci_flow_unif_existence`:
  unstated/unproved (0%).
- Its dedicated low-regularity machinery, including parallel residual work:
  approximately 97%; the remaining theorem-level work is the completed
  coefficient-state maps, time realization, and final evolution assembly.

## Addendum 2026-07-30: `principalLo_cont`

The Lane-B time layer needed the `H3 → H1` principal correction to be strongly
measurable along the solution's `H2` state field, i.e. it needed *continuity*
of `lowRegPrincipalLo` on a ball.  There is no `invPerturbH1_lip` here, and the
obvious move — porting the ~100-line `invPerturbH2_lip` from
`PrincipalNeumannH2` — is unnecessary: on the ball `1 + perturbH1 g T` is a
unit, so `NormedRing.inverse_continuousAt` already gives what is needed.
`principalLo_cont` states `∃ ρ > 0, ContinuousOn (lowRegPrincipalLo g) {‖T‖ ≤ ρ}`
and is about 40 lines.

Two traps recorded:

* Writing `have hu : IsUnit (1 + perturbH1 g T)` elaborates `IsUnit` at
  `ContinuousLinearMap.monoidWithZero`, which does **not** unify with the
  `NormedRing.toRing.toMonoidWithZero` that `NormedRing.inverse_continuousAt`
  demands.  Build the unit inside the `NormedRing` context instead:
  `Units.oneSub (-perturbH1 g T) h`, then `rw [Units.val_oneSub, sub_neg_eq_add]`.
* `ContinuousAt.comp` must be given `(f := …)` explicitly.  Left to itself,
  higher-order unification splits `fun S => 1 + perturbH1 g S` as
  `HAdd.hAdd 1 ∘ perturbH1 g` and the composition fails.

The sandwich `B ↦ traceH1 ∘ B ∘ hessianH1` is continuous by two
`ContinuousLinearMap.compL … |>.continuous₂` steps.

Verification: focused check and targeted module build passed; the declaration
is axiom-clean.
