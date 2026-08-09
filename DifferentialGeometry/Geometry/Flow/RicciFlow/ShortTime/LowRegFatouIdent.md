# LowRegFatouIdent — F2 FATOU-IDENT (+ F3 FATOU-L2H3)

**Status: green, sorry-free, censused.**  F2 (2026-08-05) and F3 (2026-08-05,
same day) both landed; verification passed on both passes.  `lowregFatouPack`
is now conditional on **GAP-ADAPTH only**.

Status: **COMPLETE, sorry-free** (2026-08-05).  Verification passed: focused
check green and warning-free, targeted build of the module green, census green
with `[propext, Classical.choice, Quot.sound]` only for all nine new public
declarations.

## What this file is

The keystone of the campaign's Fatou stage.  `lowregRung3`
(`ShortTime/LowRegRungThree.lean`) quantifies its trajectory `U` universally,
so instead of constructing a Galerkin ODE solution and identifying it with the
projected sequence (the discarded "JOINT-IDENT" route, which needed ODE
uniqueness), the rung is **instantiated directly** at

    lowregProjMode g₀ fseq N t i = perModeConv λᵢ (timeModeCoeff (fseq N) i) t

where `fseq` comes from `lowreg_proj_tendsto` / `lowreg_projMode_tendsto`.
`galTamePerMode` and `lowregGalSol` are therefore **off the critical path**
(sound banked API, not used here).

## The chain, as realized

* `hUinit` = `perModeConv_zero_left` (one line).
* `hUcont` = `continuousOn_perModeConv_timeL2` (one line; needs only `0 ≤ T`).
* `hUderiv` (`lowregModeDeriv`) is the real work, and splits into
  - `lowregFieldCombo` — the **spatial** identification.  `projField_fixed`
    (fed the package's a.e. Nemytskii conjunct) says the Duhamel field is
    `Π_N`-fixed; `ContinuousLinearMap.coeFn_compLpL` drops that to a pointwise
    a.e. statement; `spatialEigenProj_apply` turns a fixed state into
    `finiteEigenComboHs` of its own coefficients; and
    `timeModeCoeff_eq_perModeConv_forcing` (PUBLIC, a-generic — **reused, not
    re-proved**) identifies those coefficients with the mode convolutions.
    The "all coordinates at once" step is finite, not countable:
    `finiteEigenComboHs` only reads `eigenIdxFinset g₀ N`, so
    `Filter.eventually_all_finset` suffices.
  - `lowregForceMode` — the a.e. per-mode forcing identity.  `timeModeCoeff_coeFn`
    + package conjunct 3 + `spatialProj_coeff` + `aeSetLift_coe_ae` (with
    package conjunct 2) + `Subtype.ext` + `galTameForce_eq`.  `galTameForce_eq`'s
    `hc` is produced by rewriting the a.e. state ball (conjunct 2) along
    `lowregFieldCombo` — confirming №165's ruling that conjunct 2, not the
    rung, is `hc`'s producer.
  - `lowregForceCont` — the continuity gate.  `tame_lip_balls` at the package's
    own constants (`A := Ctop`, `B := B0`, `C := B1`, `Rt := lowregOuterRad`,
    ball radius `√(N+1)·R`) then `galTameForce_contOn`; `hκ` is
    `mem_eigenIdxFinset` + `linarith`.  Mirrors `galTameSolOne`'s prelude.

## The one a.e.-to-∀ seam, and how it crosses

`perModeConv_hasDerivAt` needs a **globally** `Continuous` forcing, but the
package only pins the forcing down a.e. on `[0,T]`.  Crossing:

1. `Set.IccExtend hT.le` of the (ContinuousOn) Galerkin forcing gives a global
   continuous representative `F` (`Continuous.Icc_extend'` on `.restrict`).
2. `F =ᵐ timeModeCoeff (fseq N) i` on `Icc 0 T`, so `perModeConv_timeL2_congr`
   gives the **pointwise** identity `lowregProjMode … s i = perModeConv λ F s`
   for every `s ∈ Icc 0 T`.  This is the designed crossing and it worked with
   no friction.
3. The rung asks for `HasDerivWithinAt … (Set.Ici t) t`, a set that leaves the
   slab.  Because `t ∈ Ico 0 T` is *interior on the right*, `Icc 0 T` is a
   neighbourhood of `t` within `Set.Ici t`
   (`nhdsWithin_le_nhds (Iio_mem_nhds ht.2)` ∩ `self_mem_nhdsWithin`), so
   `HasDerivWithinAt.congr_of_eventuallyEq` transfers the derivative.
   **This is the step to remember**: a slab-only identity still yields the
   rung's `Ici t` right-derivative, purely because `hUderiv` is quantified over
   `Ico 0 T` and not `Icc 0 T`.

## `hL2H3`: the shape chosen, and why

    hL2H3 : ∀ N, ∫ t, galerkinEnergy (eigenIdxFinset g₀ N)
              (lowregProjMode g₀ fseq N) 3 t ∂(timeMeasure T) ≤ Bd

i.e. the **Bochner integral against `timeMeasure T`**, not an interval
integral.  Rationale: F3's route (№165) computes
`E₃(c) =ᵃᵉ ‖field‖²_{H³}` and then `∫ ∂(timeMeasure T) = ‖field‖²_{timeL2}`,
so this is literally what F3 produces — no conversion on the producer side.
The consumer-side conversion to the rung's `Pr` block is three rewrites
(`timeMeasure` is *definitionally* `volume.restrict (Icc 0 T)`;
`integral_Icc_eq_integral_Ioc`; `intervalIntegral.integral_of_le`) and needs no
integrability hypothesis.

`Pr` is built here, not assumed: `Pr N t := ∫ s in 0..t, EE N s` with
`EE N := IccExtend` of the energy.  FTC (`integral_hasDerivAt_right`) gives
`hPrderiv` and `hPrcont`; `hPrbd` is `integral_add_adjacent_intervals` plus
nonnegativity of the tail.  The same `IccExtend` idiom as the forcing.

## F3 (2026-08-05): `hL2H3` DISCHARGED — `lowregL2H3`

    lowregL2H3 : ‖fseq N‖ ≤ b →
      ∫ t, galerkinEnergy (eigenIdxFinset g₀ N)
        (lowregProjMode g₀ fseq N) 3 t ∂(timeMeasure T) ≤ ((1+T)·b)²

stated at a **free** bound `b` (weakest assumptions), not hard-wired to `R/4`;
`lowregFatouPack` instantiates `b := R/4` from package conjunct 6.  Hypotheses
are exactly `lowregFieldCombo`'s: `hT`, `hT1`, and the a.e. Nemytskii identity
`fseq N =ᵐ projNfun … ∘ u` for *some* `u : ℝ → lowerState g₀ 1 R`.  No
nonnegativity of `b` is needed and none is asked for.

Three steps, no analysis of its own:

1. **a.e. pointwise** — `lowregFieldCombo` (already in this file, reused, not
   redone) then `finiteEigenCombo_spectral_normSq`
   (`Garding/EigenCombination.lean:406–411`) gives
   `E₃(c)(t) = ‖field t‖²`.  The exponent match is
   `((1:ℕ):ℝ) + 2 = (3:ℝ)` (`hexp`, `norm_num`), rewritten **only in the rpow
   exponent** after the normSq rewrite — never in the `tensorHs` type index,
   which would be a motive trap.  After that the two sides are
   `simp only [galerkinEnergy, tensorSobolevWeight]`-identical.
2. **integrate** — `MeasureTheory.integral_congr_ae` (no integrability
   hypothesis), then `norm_sq_eq_integral` for the timeL2 norm.
3. **maximal regularity** — `norm_maxRegDuhamelSolField_zero_le`
   (statement at `DeTurck/DeTurckQuasilinearExistence.lean:217–220`; the
   `TameForcingFixedPoint.lean:518/:893` occurrences are CALL SITES, not the
   statement), then `nlinarith [norm_nonneg fld, hle]` to square.

**The one trap, and the fix.**  `rw [norm_sq_eq_integral fld, timeMeasure]`
fails with *"Failed to rewrite using equation theorems for `timeMeasure`"*: the
first `rw`'s trailing `rfl` already closes the goal up to the `timeMeasure`
unfolding, so there is nothing left for the second rewrite to act on, yet the
error is reported as a rewrite failure rather than "no goals".  Use the term
form `(norm_sq_eq_integral fld).symm` instead — `exact`-level defeq unfolds
`timeMeasure` silently.  (Contrast `lowregFatouE3`'s `hTint`, where
`rw […, timeMeasure, …]` *does* work because a further rewrite follows.)

## Honest inputs still carried

* **GAP-ADAPTH** — the rung's absorption inequality
  `Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1` stays an explicit hypothesis inside the
  produced `∀ ε` statement.  Nothing in the Fatou stage discharges it.  It is
  now the **only** condition on `lowregFatouPack`.
* ~~`hL2H3`~~ — discharged (F3, above).
* σ-scope: this delivers the σ ≤ 3 instance only; `lowreg_loMass` (∀σ) stays
  gated on rungs 4–5.

## Interface note (revised by F3; supersedes the F2 wording)

`lowregFatouPack` feeds `lowregFatouE3` straight from
`lowreg_projMode_tendsto`, which is the compile-time proof that F1's widening
lands exactly where F2 needs it: the package's `_htame` (spelled with
`tensorHsInclusion`) unifies with this file's `galLowView` spelling because
`galLowView` is an `abbrev` for that inclusion — no adapter needed.  The six
per-`N` conjuncts are consumed positionally as `(hpack N).2.1` (state ball),
`(hpack N).2.2.1` (Nemytskii) and `(hpack N).2.2.2.2.2` (forcing ball).

**Why the `∀ Bd, … →` antecedent was REMOVED.**  F2 left `lowregFatouPack`
indexed by an undischarged `Bd`.  That shape is not consumable: the pack's
`fseq` is existentially bound, and the pack exported neither conjunct 6
(`‖fseq N‖ ≤ R/4`, the seed that squares to `Bd`) nor the Nemytskii conjunct
(`lowregL2H3`'s input), so **no** consumer of the pack could discharge the
antecedent — and re-destructuring `lowreg_projMode_tendsto` outside the pack
yields an *incomparable* witness tuple (the documented trap that motivated F1's
widening in the first place).  The fix taken here is neither "widen further"
nor "destructure twice": the single destructure already inside
`lowregFatouPack` has every handle, so `lowregL2H3` is applied **there**, at
`Bd := ((1+T)·(R/4))²`, and the antecedent is deleted.  The pack is now
unconditional except for GAP-ADAPTH, which is what F4 consumes.

## Layering note (deliberate, recorded)

`lowregForceCont`'s `tame_lip_balls` → `galTameForce_contOn` prelude is a
`HeatSemigroup/GalerkinTameSol.lean`-layer fact and is duplicated (in the
`lowregNfun` instance only) from `galTameSolOne`'s opening.  It was kept local
rather than extracted upstream to avoid claiming and rebuilding a shared
analysis module for a six-line reuse.  If a third consumer appears, extract
`∃ K, LipschitzOnWith K Nfun (galTameBall g₀ a R κ)` into `GalerkinTameSol.lean`.

## What F3 did NOT need

The sanctioned fourth widening of `lowreg_proj_tendsto` / `lowreg_projMode_tendsto`
for `D`/`hzero`/`hTτ` was **not** taken: `norm_maxRegDuhamelSolField_zero_le` is
already a closed-horizon statement whose only `T`-hypotheses are `0 < T` and
`T ≤ 1`, both of which the pack's caller supplies.  The horizon cap `hTτ` never
enters F3.  Leave the package at three widenings.

## Next

* **F4 FATOU-ASSEMBLE** — done, in the sibling `LowRegFatouMass.lean`
  (`lowregMassLow`).  See that file's note.
* Beyond the Fatou stage: rungs 4–5 (general-`k` regrouping + a
  dissipation-export engine variant) are what carry `σ ≤ 3` to `∀σ`, i.e. what
  `lowreg_loMass` still needs.  Per-metric GAP-ORDER and GAP-ADAPTH are now
  discharged by the explicit package; class-uniform calibration remains separate.

## 2026-08-05: exact adapted Fatou package

`lowregFatouE3At` consumes an explicit `IsRung3Ord` certificate plus one proved
absorption budget.  `lowregFatouPackAt` takes `IsAdaptedLowSolve`, obtains its
literal projected sequence through `lowreg_projMode_at`, and invokes the stored
ordered continuation at the package's calibrated budget.  Thus its `H³` Fatou
bound has no remaining conditional gate and no reselected constants.  The old
generic theorems remain compatibility wrappers.  Focused verification passed,
warning-free, and the targeted module refresh passed.
