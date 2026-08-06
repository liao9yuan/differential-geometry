# LowRegAllOrderJet.lean — notes

Brick B1 (+ B2, B5) of `LOWREG_BOOTSTRAP_PLAN.md` ("front 2", the fixed-horizon
endpoint bootstrap).  Written 2026-08-02, checkout
`E:\testdifferential-geometry-ste-align`, branch `codex/short-time-existence-align`.

## Role

Feed the closed `(1, 2)` low-regularity rung into the already sorry-free
joint-smoothness endpoint
`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
(`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean:1311`)
at the Sobolev index `a = 2`, on the horizon that `lowreg_solve_two`
(`ShortTime/LowRegApplyTwo.lean:472`) reports — no horizon shrink anywhere in the
chain.  The endpoint's `hC` slot is filled by `hs2_opBound_at_two`
(`MaxRegSolutionJointlySmooth.lean:1593`), which until now had zero consumers.

## Declarations (line numbers as of 2026-08-03; 820 lines total)

| line | name | status |
|---|---|---|
| 105 | `tensorHsCongr_coeff` | proved; canonical home is `SobolevScale/ExponentCongr.lean` (not claimed by this brick) |
| 119 | `lowregNsec` | the concrete `Nsec` = symmetrized smooth DeTurck remainder |
| 148 | `coord_eq_smoothN` | private; proved; the `a = 2` analogue of `realizedForcingCoord_eq_smoothNSymm` |
| 421 | `lowreg_forceJetMass` | historical frontier; now proved |
| 478 | `lowreg_allOrderJet` | proved; historical dependency now discharged |
| 659 | `lowreg_joint_smooth` | proved; independent of the frontier |
| 768 | `lowreg_joint_of_re` | proved; historical dependency now discharged |

## Sorry census

**Historical snapshot, superseded by the dated closure entries at the end of
this file.**  The implementation now has no proof-body `sorry` in this chain.

## The posit design choice: ONE leaf, not the supercritical two

The plan's builder brief asked for a verbatim mirror of the supercritical split —
(A) `deTurckForcing_solCoeff_jetSpectralMass` (interior-time smoothing of the
solution field) and (B) `deTurckSobolevNHa2_jetSpectralMass_preserving`
(order-preserving jet-mass smoothness of the Nemytskii), with
`deTurckSobolevNHa2Symm` replaced by `liftHiN`.  **(B) is unwritable at `a = 2`
as a true standalone statement**, for a structural reason:

* there is no intrinsic `H⁴ → H²` Ricci–DeTurck Nemytskii operator in the tree
  (`deTurckSobolevNHa2` exists only under `2·finrank ℝ E + 10 ≤ a`);
* the only high-scale nonlinearity at the closed rung is the frozen split
  `liftHiN` (`ShortTime/LowRegForceHi.lean:132`), and its first-order arm `FHi`
  is an **unconstrained existential** inside `IsRealizedTwo`
  (`LowRegApplyTwo.lean:90`): the package binds `FHi` with no continuity, no
  bound, and no smooth-core formula.  For a general such `FHi`,
  "jet-mass preserving" is simply false.

Reinstating the needed properties means re-importing the `refold_aff` /
`lowA2_small` producer bundle, which `lowreg_solve_two` consumes and discards, so
a split (B) would either be false or have no consumer.  `LOWREG_BOOTSTRAP_PLAN.md`
§8.1 explicitly sanctions the fallback ("if the two-posit split is unwritable at
`a = 2`, collapse to a single named leaf"), and the project rule "at most one
genuine mathematical frontier visible" points the same way.  So (A′) and (B′) are
composed into the single leaf `lowreg_forceJetMass`, stated at exactly the
strength `lowreg_allOrderJet` consumes, hypothesised on the low-lane fixed-point
identity (`IsRealizedTwo`'s last conjunct = `force_hi_id`'s conclusion) so it is
not vacuous.

Truth argument, recorded in the Lean docstring: zero datum + smooth background ⟹
classical small-data quasilinear interior-time smoothing up to `t = 0`; the
order-generic raw material is `tensorHeatSemigroupHs_opNorm_le`
(`Parabolic/TensorHeatEquation/SmoothingHs.lean:791`) and `heatPower_opNorm_le`
(`Heat/Semigroup/SpectralBounds.lean:524`), and carrying them to the corner is
legitimate because `staticForce g g σ` (`ShortTime/LowRegLiftNTerm.lean:142`)
exists at arbitrary real `σ`, so the inhomogeneity costs no order at `t = 0`.
Why it is not proved: `a = 2` sits below every supporting estimate in the tree
(§8.1).

## Risks that materialised, and how they were handled

* **Risk 2 / §8.2 (`hball_full` on the full `Icc 0 T`) — folded, as instructed.**
  It is a conjunct of `lowreg_forceJetMass`, stated in the endpoint's exact shape
  (arbitrary smooth `S` pinned to the carrier, `‖smoothCcToTensorHs ((2:ℝ)+2) S‖ ≤ R₀`),
  with `R₀` produced existentially by the leaf.  Note for a future prover: the
  supercritical lane shrinks the horizon here only because it must hit a
  *pre-fixed* realizability radius; since the endpoint takes `R₀` implicitly, a
  proof of the leaf may choose `R₀` from the mass majorant
  (`perModeConv_allOrder_timeDeriv_spectralMass_le` at `j = 0`, `τ = (2:ℝ)+2`,
  then `R₀ := √(∑ Cmaj)`), which needs **no** horizon shrink.  The radius is only
  constrained from above by whatever `hForce` (brick B3) will need.
* **Risk 3 (exponent transports) — mostly dissolved.**  `((2:ℕ):ℝ)` IS
  definitionally `(2:ℝ)` in this Mathlib (`Nat.cast_ofNat` is `rfl` for `ℝ`), so
  `MaxRegSolutionSpace (2:ℝ) T` sits in the endpoint's `MaxRegSolutionSpace ((2:ℕ):ℝ) T`
  slot with no transport at all, and `Nat.cast_nonneg 2` unifies with
  `(show (0:ℝ) ≤ (2:ℝ) by norm_num)` by proof irrelevance.  Verified by an
  explicit `rfl` probe before writing anything.  `2+2` vs `4` is NOT free: the
  file keeps `(2:ℝ)+2` wherever the endpoint does and uses `tensorHsCongr` only
  at the one junction where `liftHiN`'s domain is literally `tensorHs … (4:ℝ)`;
  `tensorHsCongr_coeff` (proved by `cases h; rfl`) is the one bookkeeping lemma
  needed.
* **§8.3 `hfloor` and brick B3 `hForce` — NOT producible from `IsRealizedTwo`;
  left as visible hypotheses.**  See next section.

## SUPERSEDED (2026-08-03): the section below described the pre-widening state

`IsRealizedTwo` was widened on 2026-08-03 (`LowRegApplyTwo.md`, brick 7) and
`hForce` is now **discharged**.  See "2026-08-03, brick 8" at the end of this
file for the current state.  The section immediately below is kept because it
records the diagnosis that produced the widening.

## What `IsRealizedTwo` cannot supply (the honest gap)

`lowreg_joint_smooth` / `lowreg_joint_of_re` keep two slots as explicit
hypotheses.  Both are genuine producer-side gaps, not new mathematics:

1. `hfloor : √T · ‖u.deriv‖ ≤ 1/(2C)`.  `IsRealizedTwo` carries **no norm bound
   at the high scale**: its derivative clause is
   `timeDeriv u.lo = timeScaleLaplacian 2 u.hiL2 + fHi`, and neither `‖u.hiL2‖`
   nor `‖fHi‖` is bounded anywhere in the package (`lowreg_solve_two` caps
   `‖f‖ ≤ P/4` at the LOW scale, internally, and does not export it).  Stated
   against `(hs2_opBound_at_two hDim g).choose`, so the dim-3 producer is the one
   that fixes `C`.
2. `hForce` (brick B3).  The route
   `force_hi_id → hiN_lowreg → lowreg_N_affine → lowRegN_on_smooth` needs
   `hR : 0 < R`, `hreal`, `hNcont`, `hcore`, `hA2cont`, `hA2core`, `FLo`,
   `hFLo`, `hFcore`, `hA2sq`, `hFComm`, **and** the `lowerState g 1 R`
   membership of the pinned smooth state — eleven-plus items that
   `lowreg_solve_two` obtains from `refold_aff` / `lowA2_small` / `radialA2_lip`
   / `lowRegN_outer` and then discards.  Separately, the supercritical model
   proof `realizedForcingCoord_eq_smoothNSymm`
   (`MaxRegSolutionJointlySmooth.lean:664`) upgrades a.e. equality to
   everywhere-on-`Ico` through `Measure.eqOn_Ico_of_ae_eq`, and its RHS
   continuity comes from `deTurckSobolevNHa2Symm_lipschitzWith` — the `a = 2`
   analogue is continuity of `liftHiN`, i.e. exactly `hA2Hicont` + `hFHi`, again
   not in `IsRealizedTwo`.

**Smallest unblocking step for a follow-up brick:** either (i) widen
`IsRealizedTwo` (`LowRegApplyTwo.lean:90`) to export `Continuous FHi`, the
second-order continuity `hA2Hicont`, the two commuting squares `hA2sq`/`hFComm`,
the low-scale radius `R` with `hreal`, and `‖fHi‖`'s bound — the package already
has all of them in scope at the `lowreg_apply_two` call site; or (ii) state B3
directly at the `lowreg_solve_two` level, i.e. prove a
`lowreg_solve_two_with_wiring` that returns `IsRealizedTwo` **and** the two
obligations.  (i) is the smaller edit and is the recommended one; it touches only
`LowRegApplyTwo.lean` and its single producer `lowreg_apply_two`.

## Route notes / reusable Lean facts learned

* `carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict`
  (`Parabolic/QuasiLinear/TensorMaximalRegularity/PointwiseSpectralCoordinate.lean:267`)
  is the right engine for the endpoint's `hf_id`: it wants only an *everywhere*
  representative `F` of the forcing with **coordinate-wise** continuity on
  `Icc 0 T` (not `Hᵃ`-continuity).  Building `F` from the smooth coordinate
  family is three lines: `tensorHs_of_spectralMass_majorant` fed
  `fun i => fc i (projIcc 0 T hT.le t)` with the `j = 0`, `τ = 2` majorant.
  `projIcc` keeps it defined off `[0,T]` without any junk-value case split.
  Continuity lemma is root-namespace `continuous_projIcc` (NOT `Set.…`).
* `timeH1.ext` + `maxRegDuhamelMap_init` + `maxRegDuhamelMap_timeDeriv_eq` turn
  `IsRealizedTwo`'s trace/derivative conjuncts into
  `u.lo = maxRegDuhamelMap (2:ℝ) hT hT1 0 fHi` in ~12 lines (plan brick B2,
  "routine" — confirmed routine).
* `timeMeasure T` unfolds to `volume.restrict (Icc 0 T)` transparently enough
  that `filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc]` works
  against a `timeMeasure`-indexed goal with no `show`/`unfold`.
* Opening both `Analysis.Parabolic.TensorSpectral` and
  `Analysis.Parabolic.TensorHeatEquation` makes `TensorEigenIdx` ambiguous.  Do
  not blanket-open `TensorSpectral` in files that mention `TensorEigenIdx`; use
  `open … (symmS) in` per declaration, as `MaxRegSolutionJointlySmooth.lean` does.
* `set_option … in` must precede the docstring, not sit between docstring and
  `theorem` (parse error "unexpected token 'set_option'; expected 'lemma'").
* `F_RHS` / `Nsec` / `hRepr` are deliberately left generic in
  `lowreg_joint_smooth`: the concrete Ricci–DeTurck `hRepr` is a ~55-line block
  inside `deTurckRicci_solution_with_jointReg`
  (`ShortTime/DeTurckInitialDataExistence.lean:92`), order-free but not exported
  as a named lemma.  Extracting it there (a one-file edit) is the right B6 move;
  copying it here was refused as duplication.

## Verification

Focused file check: PASSED (one `sorry` warning, no other warnings).
Targeted module build `+DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegAllOrderJet`:
PASSED, "Build completed successfully", single `declaration uses 'sorry'` at 151.

## Honest progress

* `(N)` (`Evolution/ExtendViaUniqueness.lean:80`): **0 %** — still unstated as a
  proof.  Unchanged by this brick.
* Front 2 (the fixed-horizon endpoint bootstrap): the endpoint chain above the
  forcing package was already ~90 % and sorry-free; this brick supplies the
  package interface and the `a = 2` instantiation, so front 2 is now
  **one named analytic leaf + two named wiring obligations** away from closed.
  Call it ~55 % of front 2 done, with the remaining 45 % split roughly
  35 % `lowreg_forceJetMass` (a genuine multi-session parabolic-regularity
  layer) and 10 % B3/§8.3 wiring (an `IsRealizedTwo` widening, routine).
* `(N)`'s dedicated machinery: ~85 % → ~86 %.
* Whole HCG compactness project: low single digits, unchanged.

## 2026-08-03, brick 8 — `hForce` DISCHARGED, `hfloor` survives (and is not a packaging gap)

Follow-up to the widening of `IsRealizedTwo` (`LowRegApplyTwo.md`, brick 7).

### What was added here

* `lowregNsec` — the concrete `Nsec` the endpoint slot needs:
  `deTurckSmoothRemainder g g (symmS g S) hδ_lt (gFibreOpBound_symmS g S hδ)`.
  This is exactly the supercritical lane's `Nsec`, just named.
* `coord_eq_smoothN` (private) — the `a = 2` analogue of the supercritical
  `realizedForcingCoord_eq_smoothNSymm`.  Given the widened certificates and a
  smooth family `F` pinned to the carrier in `L²` on `Icc 0 T`, it proves
  `fc i t = coeff of Nsec (F t)` for every `t ∈ Ico 0 T`.
* `lowreg_allOrderJet` — one extra conclusion conjunct (the endpoint's `hForce`,
  with the `hball` hypothesis **dropped**: the `L²` pin alone suffices), and one
  extra hypothesis `hDim` (needed by `lowreg_N_affine`).
* `lowreg_joint_of_re` — `Nsec` is no longer a parameter (it is `lowregNsec g`),
  the `hForce` implication is gone, and `fc`/`R₀` no longer need to be reported.

### The route that worked (and the two false starts avoided)

The obvious route "identify `liftHiN` at the `H⁴` smooth state with
`deTurckSmoothN … 2`" needs *continuity of `liftHiN`* and hence `H⁴`-continuity
of `t ↦ smoothCcToTensorHs g 4 (F t)`.  Both were avoidable:

* **Inclusions preserve eigen-coordinates** (`tensorHsInclusion_coeff_apply`,
  `rfl`).  So the coefficients of `liftHiN … v` equal those of
  `refoldBaseN … (incl₃₄ v)` by `hiN_incl` alone, and the whole upgrade can be
  run one scale lower, at `H³`, where `refoldBaseN_cont` already exists.
  No `liftHiN` continuity lemma had to be written.
* **`R₀ ≤ R` is not needed.**  The state-ball membership of `F t` is obtained
  from `h_pin` (which forces `smoothCcToTensorHs g 2 (F t) = timeH1.toFun u t`)
  plus the newly exported a.e. bound `‖timeH1.toFun u t‖ ≤ R`, upgraded to every
  `t ∈ Ico 0 T`.  Trying to route it through the endpoint's `hball` (radius
  `R₀`, produced existentially by the frontier) would have needed `R₀ ≤ R`,
  which no producer supplies — and `hball_full` is monotone the wrong way, so
  `R₀` cannot simply be shrunk.

The a.e.-to-everywhere upgrades are both `MeasureTheory.Measure.eqOn_Ico_of_ae_eq`:
once on `fc i` versus the `refoldBaseN` coordinate (continuity from
`tensorHs_continuousOn_of_coeff_of_higher_mass` at `σ = 3`,
`σ' = 3 + weylSobolevExp + 1`, fed by `perModeConv_allOrder_timeDeriv_spectralMass_le`
at `k = 0`), and once on `min ‖toFun u ·‖ R` versus `‖toFun u ·‖` (continuity
from `timeH1.continuousOn_toFun`) to turn the a.e. state-ball bound into an
everywhere-on-`Ico` one.  `min_eq_left_iff.mp` then reads off the inequality.
The private supercritical helper `realizedSol_solField_continuousOn_Ha2` is a
~20-line wrapper of the public `tensorHs_continuousOn_of_coeff_of_higher_mass`;
it was re-derived here rather than de-privatised (that file is not claimed).

### Final visible hypotheses of `lowreg_joint_of_re`

`hDim`, `g`, `F_RHS`, `hRepr` (now stated against `lowregNsec`), `hρ`, `hδ0`,
`hδ_le`, `hreal'`, `hT`, `hT1`, `f`, `hre`.  Conclusion:

```
∃ u : MaxRegSolutionSpace (2:ℝ) T,
  √T · ‖u.deriv‖ ≤ 1/(2·(hs2_opBound_at_two hDim g).choose) →
  ∃ F δ' hδ_lt hδ', F 0 = 0 ∧ (L² pin to u on Icc 0 T)
                    ∧ (Ico-slab PDE, HasDerivWithinAt … (Ici 0))
                    ∧ JointChartGramSmooth T
```

So exactly two obligations remain above this file: the frontier
`lowreg_forceJetMass`, and `hfloor`.  `hRepr` is deliberately still a
hypothesis (brick B6, out of scope here).

### Why `hfloor` cannot be discharged here — the precise missing fact

`u.deriv = timeScaleLaplacian 2 u.hiL2 + fHi`, and `IsRealizedTwo` carries no
size bound at the high scale.  Closing it needs, in order:

1. a Neumann bound `‖fHi‖ ≤ ‖liftForceHi g g T‖ / (1 - κ)` from the exported
   fixed-point conjunct `fHi = nonautL2Map … fHi + liftForceHi g g T`, where
   `κ = (C2Hi:ℝ)(1+T) + 2√(1+T)‖hA1Hi.toLp (refoldAffA1Hi …)‖ < 1` is the
   contraction certificate `hsmallHi` — **in scope inside `lowreg_apply_two`
   but not currently exported**;
2. `‖liftForceHi g g T‖ ≤ √T · ‖staticForce g g 2‖` (the forcing is constant in
   time), plus the maximal-regularity bound for `maxRegDuhamelSolField` and an
   operator bound for `timeScaleLaplacian`, giving `‖u.deriv‖ ≤ √T · K(g)`;
3. therefore `√T‖u.deriv‖ ≤ T·K(g)`, and `hfloor` becomes `T ≤ 1/(2·C·K(g))`.

Step 3 is the point: **`hfloor` is a smallness condition on `T` itself**.  For an
arbitrary `T` admitting an `IsRealizedTwo` package it is false, so no amount of
further widening discharges it at this level.  It has to be folded into the
horizon `T₀` that `lowreg_solve_two` reports — i.e. a change to
`lowreg_solve_two`'s statement, which is a separate brick.  That is why it is
left visible and why nothing was posited for it here.

### Verification

Focused check GREEN for both files; targeted builds
`+…LowRegApplyTwo` then `+…LowRegAllOrderJet` GREEN ("Build completed
successfully").  Sorry census over both files: exactly one, the frontier body.
No new `sorry`/`admit`/`axiom`, no heartbeat option.

### Lean notes from this brick

* `ContinuousOn.min` does not exist; `ContinuousOn.inf` does, and unifies with
  `min` for `ℝ` by `rfl` (so `ContinuousOn.inf h continuousOn_const` typechecks
  against a `fun s => min … R` goal).
* `Set.EqOn f g s` applied at a point leaves a beta-redex when `g` is a lambda;
  `refine (heqOn i ht).trans ?_` then needs a `change` (not `show` — the style
  linter rejects a `show` that changes the goal) to expose the head for `rw`.
* `smoothN_wd` (`LowRegDenseN.lean`) is the tool for the `δ`-mismatch between
  the package's own `δ` and the caller's `δ'`: metric realization does not
  depend on the fibre-bound witness.

### Honest progress (updated)

* `(N)` (`Evolution/ExtendViaUniqueness.lean:80`): **0 %** — still unstated as a
  proof.  Unchanged by this brick.
* Front 2: was "one named analytic leaf + two named wiring obligations".  One of
  the two wiring obligations is now discharged, and the other is shown to be a
  horizon-shrink task in `lowreg_solve_two` rather than a packaging gap.  Call
  front 2 ~62 % done (up from ~55 %), with the remaining ~38 % split ~35 %
  `lowreg_forceJetMass` (unchanged: a genuine multi-session parabolic-regularity
  layer) and ~3 % the `hfloor` horizon fold.
* `(N)`'s dedicated machinery: ~86 % → ~87 %.
* Whole HCG compactness project: low single digits, unchanged.

## 2026-08-03, brick 9 — `hfloor` DISCHARGED; front 2 is now ONE frontier + `hRepr`

Follow-up to brick 8, whose §"Why `hfloor` cannot be discharged here" is the
spec this brick implemented.  The producer side is in `LowRegApplyTwo.md`,
brick 9; here is the consumer side.

### What was added / changed here

* `lowreg_allOrderJet` — gains the implicit `{Kf}` (its `hre` is now
  `IsRealizedTwo … f Kf`) and one extra reported conjunct, the package's
  forcing floor `√T·‖fHi‖ ≤ Kf`, forwarded verbatim.  Nothing else moved; the
  `obtain` pattern for `hre` gains one trailing name.
* `lowreg_joint_of_re` — the `hfloor` implication is **gone** from its
  conclusion.  It now takes `{Kf}` plus
  `hKfC : Kf ≤ 1/(4·(hs2_opBound_at_two hDim g).choose)`, and its conclusion is
  a plain `∃ u F δ' hδ_lt hδ', …` (the carrier moved inside the same `∃`-chain
  as `F`, so the caller no longer has to discharge anything).
* `lowreg_joint_two` — NEW, the self-contained front-2 endpoint:
  `lowreg_solve_two` at `Kf := 1/(4C)` composed with `lowreg_joint_of_re`.
  Only `hDim`, `g`, `F_RHS`, `hRepr` are inputs; it reports `B2 ≥ 0` and, for
  every contraction level `c ∈ [B2, 1)`, a positive `T₀` on whose horizons the
  `(N)`-shaped triple holds.

### The `hfloor` discharge, in Lean terms

The carrier is `maxRegDuhamelMap 2 hT hT1 0 fHi` (this was already reported as
`hduh`), so `maxRegDuhamelMap_deriv` splits `u.deriv` into
`maxRegHomogeneousDerivField 2 T 0 + maximalRegularityDerivField 2 hT.le fHi`.
The first summand is `0` (`maxRegHomogeneousDerivField_norm_le` at `u₀ = 0`
gives `‖·‖ ≤ √T·‖0‖`), the second is `≤ 2‖fHi‖`
(`maximalRegularityDerivField_norm_le`).  Hence `‖u.deriv‖ ≤ 2‖fHi‖` and
`√T‖u.deriv‖ ≤ 2·(√T‖fHi‖) ≤ 2Kf ≤ 1/(2C)`.

**No `timeScaleLaplacian` operator norm was needed.**  The obvious route through
`u.deriv = timeScaleLaplacian 2 u.hiL2 + fHi` (the `IsRealizedTwo` conjunct)
would have required an `H⁴ → H²` bound for the rough Laplacian *and* the
maximal-regularity bound for `u.hiL2`; the Duhamel derivative split gives the
same estimate with the sharp constant `2` and two existing lemmas.  That is the
one route choice worth remembering from this brick.

### Final visible hypotheses

`lowreg_joint_two`: `hDim`, `g`, `F_RHS`, `hRepr`.  Nothing else.

So above this file the front-2 chain has exactly TWO open items:

1. the frontier `lowreg_forceJetMass` (`:421`, the single `sorry`) — the
   all-order interior-time smoothing at `a = 2`;
2. `hRepr` (brick B6) — extraction of the order-free Ricci–DeTurck
   representation block from `deTurckRicci_solution_with_jointReg`
   (`ShortTime/DeTurckInitialDataExistence.lean`).

### Lean notes from this brick

* `linarith`/`nlinarith` without `only` in a wide-context theorem is a real
  performance hazard — see `LowRegApplyTwo.md` brick 9.
* When a conclusion changes from `∃ u, P → Q` to `∃ u F …, Q`, the terminal
  `exact <endpoint call>` needs an explicit `⟨u, …⟩`; the error is a `Type
  mismatch` between `Exists.{max …}` (over `F`) and `Exists.{1}` (over `u`),
  which reads confusingly until one notices the universe levels.
* A `∀ {T} (hT : 0 < T) …` binder whose name does not occur in the conclusion
  trips `linter.unusedVariables`; rename to `_hT` rather than disabling the
  linter (the hypothesis is still an explicit argument).

### Verification

Focused check GREEN; targeted build
`+DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegAllOrderJet`
GREEN ("Build completed successfully"), single `declaration uses 'sorry'` at
:421.

### Honest progress (updated)

* `(N)` (`Evolution/ExtendViaUniqueness.lean:80`): **0 %** — still unstated as a
  proof.  Unchanged by this brick.
* Front 2 (the fixed-horizon endpoint bootstrap): was ~62 %.  The `hfloor`
  horizon fold is done and the endpoint is now self-contained, so front 2 is
  ~65 %, with the remaining ~35 % essentially all `lowreg_forceJetMass` (a
  genuine multi-session parabolic-regularity layer) plus the small `hRepr`
  extraction.
* `(N)`'s dedicated machinery: ~87 % → ~88 %.
* Whole HCG compactness project: low single digits, unchanged.

---

## 2026-08-03, bricks F2–F5 — `lowreg_forceJetMass` PROVED; the frontier is now purely SPATIAL

Plan: `ShortTime/FORCEJETMASS_PLAN.md` §6 (bricks F2, F3, F4, F5).  Result: GREEN
for all four.  The composite frontier `lowreg_forceJetMass` no longer carries a
`sorry`; the file's single `sorry` is the new named leaf `lowreg_spatialMass`,
which contains **no time derivative at all**.

### The deliverable — (S1₂) as stated in Lean

```
theorem lowreg_spatialMass (g) {ρ δ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3)
    (hreal') (FHi) {T} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs g 0 2 (2:ℝ)) T)
    (hfix : fHi =ᵐ[timeMeasure T] fun t => liftHiN g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr … (maxRegDuhamelSolField 2 hT hT1 0 fHi t)))
    (σ : ℝ) :
    ∃ Cσ, ∀ t ∈ Icc 0 T,
      Summable (fun i => tensorSobolevWeight i σ *
        (perModeConv λᵢ (timeModeCoeff fHi i) t)^2) ∧
      ∑' i, tensorSobolevWeight i σ *
        (perModeConv λᵢ (timeModeCoeff fHi i) t)^2 ≤ Cσ
```

It is *exactly* the `hspatial` hypothesis of the supercritical
`deTurckForcing_finiteOrderSmoothDriverSymm`
(`HeatSemigroup/ForcingCoordinateTimeRegularity.lean`), instantiated at `a = 2` and
pinned to the low lane's trajectory by `hfix`.  Brick F6 has to prove exactly this
and nothing else.

### What landed

New declarations in `LowRegAllOrderJet.lean` (cite by NAME, line numbers move):

* `liftN_smoothN_coeff` (private) — **F2**, the state-level bridge:
  `(liftHiN … (smoothCcToTensorHs g 4 S)).coeff i = (deTurckSmoothN g g 2 (symmS g S) …).coeff i`
  for a smooth `S` with `‖smoothCcToTensorHs g 2 S‖ ≤ R`.  Route: `hiN_incl` →
  `lowreg_N_affine` → `lowRegN_on_smooth` → `smoothN_wd` → `deTurckSmoothN_coeff`,
  i.e. exactly the chain `coord_eq_smoothN` already used, hoisted out of it.
* `lowreg_forceJetStep` (private) — **F3a**, one rung; the `a = 2` analogue of
  `deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving` on the FULL `T`.
* `lowreg_forceDriver` (private) — **F3b**, the induction on `k`; the `a = 2`
  analogue of `deTurckForcing_finiteOrderSmoothDriverSymm`, **with both horizon
  shrinks deleted**.
* `carrier_coeff_pmConv` (private) — the carrier's per-mode Duhamel identity on the
  closed slab, factored out of `lowreg_allOrderJet` (now used twice: for
  `hball_full` inside `lowreg_forceJetMass`, and for `hf_id` in `lowreg_allOrderJet`).
* `lowreg_spatialMass` — the FRONTIER (`sorry`).
* `lowreg_forceJetMass` — now PROVED; **F4** (diagonal glue) and **F5**
  (`hball_full`) are its proof body.

Design decision taken (plan §6 Design note): **option (i)** — `lowreg_forceJetMass`
was widened to carry `hDim, hR, hρ, hRρ, hδlt, hreal, hNcont, hcoreN, hA2cont,
hA2core, FLo, hFLo, hFLoCore, hA2sq, hFComm` plus the a.e. state ball `hballU`.
All are available at the single call site from the widened `IsRealizedTwo`; the
call site now also builds `hballD` from `ucs.link` + `hhiL2` + `hballU`.

### Promotions (api-gap)

In `HeatSemigroup/ForcingCoordinateTimeRegularity.lean`, `private` removed from five
declarations in the `SymmSCoefficientBlockTransfer` section, names and namespace
unchanged, docstrings added:

* `exists_smoothCcPath_realizing_coeff` (the (S2) reconstruction, PATH form)
* `symmCoeffPath`, `symmCoeffPath_contDiff`, `symmCoeffPath_realizes`,
  `symmCoeffPath_spectralMass` (risk 7.4's `symmS` jet-mass transport)

**Deviation from the plan's §6/§7.5 instruction, recorded deliberately.**  The plan
asked for the promotion of `exists_smoothCcTensor_of_allOrder_spectralMass_local`
(`ForcingFiniteOrderTimeRegularity.lean`).  That declaration is the *pointwise*
form; `exists_smoothCcPath_realizing_coeff` is the *path* form the driver actually
consumes, and it lives in the same file as the `symmS` transport that had to be
promoted anyway.  Promoting the path form is the strictly smaller change: one file
touched instead of two, and no third copy created.  The pointwise duplicate in
`DeTurckRemainderPathTimeJet.lean` was left alone.
`ForcingFiniteOrderTimeRegularity.lean` was claimed but NOT edited.

### The key structural insight (worth remembering)

The supercritical lane has TWO parallel towers: the raw one (`deTurckSobolevNHa2*`)
and the symmetrized one (`*Symm`, inside `SymmSCoefficientBlockTransfer`).  The low
lane's nonlinearity `lowregNsec` has `symmS` baked in, so it is the **Symm** tower
that transplants, not the raw one — and the whole `symmS` coefficient-transport
machinery (`symmCoeffPath`) is already written, order-generic and sorry-free.  The
`a = 2` step then lands on `deTurckSmoothN g g 2 (symmS g (F t))`, which is
*literally* what the F2 bridge produces.  No analogue of
`deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS` is needed at `a = 2`, because
there is no completed operator to identify with the core.

### Lean facts learned in this pass

* `IsCompactOperator` is a `Prop`, so `hCompact g` (the `Garding` abbrev used inside
  `ForcingCoordinateTimeRegularity`) and `tensorResolventL2_isCompactOperator g 0 2`
  are interchangeable by proof irrelevance.  No bridging lemma is needed when
  transplanting between the two files.
* `deTurckSmoothN g g a S hδ_lt hδ` has an `a`-independent `.coeff`, so
  `(… g g 1 …).coeff i = (… g g 2 …).coeff i` is closed by a bare `rfl` — the
  `smoothN_wd` rewrite only has to fix the `δ`-certificate, not the order.  That
  final `rfl` is easy to forget: the `rw` chain leaves the goal open and the error
  is reported at the *declaration* line, not at the tactic.
* `omit [X] in` must precede the docstring, not sit between docstring and `theorem`
  (otherwise: `unexpected token 'omit'; expected 'lemma'`).
* A hypothesis of the form `∀ …, ∀ {δ'} …` passed as data is fragile; making `δ'`
  explicit in the `hbridge` bundle avoided any implicit-binder elaboration games.
* Passing a proved lemma as an explicit hypothesis bundle (`hbridge`) instead of
  re-listing fifteen producer certificates on every middle-layer lemma keeps the
  driver honest (it needs exactly the bridge) and the signatures short.

### Verification

Focused check of `LowRegAllOrderJet.lean`: GREEN, exactly one
`declaration uses 'sorry'` (at `lowreg_spatialMass`).  Focused check and targeted
module build of `ForcingCoordinateTimeRegularity.lean` after the promotions: GREEN.
Targeted module build of `LowRegAllOrderJet`: GREEN.

### Honest progress (updated)

* `lowreg_spatialMass` (= brick F6, the only remaining analytic content of front 2's
  forcing package): **0 %** — stated, not proved.
* `lowreg_forceJetMass`: its wiring is **complete**, conditional only on the above.
  Before this pass it was 0 % (a bare `sorry`).
* Front 2's dedicated forcing machinery: the transplantable stack is now fully
  wired (the plan's §10 estimate was ≈60 %).  What remains is entirely F6.
* `(N)` (`Evolution/ExtendViaUniqueness.lean:80`): **0 %**, unchanged — stated, not
  proved.  This pass moved no `(N)` mathematics.
* Front 2 overall: ~70 % (was ~65 %).  The gain is wiring, not analysis.
* Whole HCG compactness project: low single digits, unchanged.

---

## 2026-08-03, option-(b) brick B1 — the call site now feeds a STATE bound

Planner ruling No. 106; design `OPTIONB_FLOOR_PLAN.md` §6.  This file is the
SINGLE repo-wide call site of
`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii` (grep
verified), and B1 swapped that engine's `hfloor` slot for
`hstate : ∀ t ∈ Icc 0 T, ‖timeH1.toFun u t‖ ≤ 1/(2C)`.

Change here is two lines inside `lowreg_joint_smooth` (`:1553-1556`):

```lean
  have hinit : u.init = 0 := by have := htrace; rwa [timeH1.trace0_apply] at this
  … hf_id _ hC_pos hC (u.state_le_of_sqrt_floor hinit hfloor) hR₀_pos hball_full hForce
```

plus a docstring sentence at `:1467-1471`.  **`lowreg_joint_smooth`'s public
statement is unchanged** — it still takes `hfloor : √T·‖u.deriv‖ ≤ 1/(2·C)` and
still reports the same conclusion.  The old floor simply reaches the engine
through the shim `TimeSobolev.timeH1.state_le_of_sqrt_floor`
(`Analysis/Parabolic/TimeSobolev/TimeH1Modulus.lean:136`), which is the very
`calc` that used to sit inside the engine.  So B1 is invisible downstream: no
consumer of this file changed, and bricks B3–B5 can land later without a
green-tree gap.

The `hfloor` slot itself is NOT deleted here — that is brick B5, which will
replace it by the everywhere state bound produced from `IsRealizedTwo`'s `hballU`
conjunct via the new `timeH1.norm_le_of_ae_le` (brick B2, landed in the same
module).  `norm_le_of_ae_le` is the `Icc` upgrade of the `min`-truncation trick
already used in this file at `:334-348`; the closed endpoint `t = T` is covered
(`Measure.eqOn_Icc_of_ae_eq` with `hne : (0:ℝ) ≠ T`), so the option-(a) fallback
trigger of `OPTIONB_FLOOR_PLAN.md` §8 did NOT fire.

### Verification

**GREEN.**  Focused check passed; targeted module rebuild passed.  The only
`sorry` reported is the pre-existing `lowreg_spatialMass` (`:1028`), untouched.
`#print axioms` on `lowreg_joint_smooth` = `[propext, Classical.choice,
Quot.sound]`, identical to the baseline census taken before the edit — it stays
`sorryAx`-free and independent of `lowreg_spatialMass`.

### Honest accounting

0% new mathematics in this file (a shim insertion).  (N) stays **0%**; front 2
unchanged at ~70%.  Option (b) is 2 of 5 bricks landed, and the two landed ones
are the refactor half — the mathematically visible payoff (dropping
`‖staticForce g g 2‖` from the horizon) arrives only with B3/B4/B5.

---

## 2026-08-03, brick S0 — the frontier was FALSE; it is now honestly stated

Brick S0 of `F6_ESTIMATE_RECON.md` §7.6/§7.7 (planner entry No. 108).  Pure
statement surgery on `lowreg_spatialMass`: no proof was attempted and none
landed, the `sorry` is unchanged.

### What was wrong

`lowreg_spatialMass` bound `FHi` with **no hypothesis and no state ball** while
concluding an all-`σ` spectral-mass bound on the trajectory.  Since `liftHiN`'s
third summand is `FHi (ι₃₄ v) (lowRadialH3 …)`, choosing `FHi x := ⟪·, e⟫ • w`
with `w ∈ H² ∖ H³` plants a permanently-`H²` component in the trajectory and the
`σ`-weighted mass diverges for large `σ`.  The statement was not merely unproved
— it was unprovable.

### What changed

Three binder additions, copied from `lowreg_forceDriver` (which already consumes
exactly these):

* the implicit group became `{R ρ δ : ℝ}` and `hRρ : R ≤ ρ` joined `hρ`;
* `hbridge` and `hballU` were inserted **between `hfix` and `(σ : ℝ)`** — the
  position §7.7 prescribes;
* `open …TensorSpectral (symmS) in` had to be added above the frontier, because
  `hbridge` mentions `symmS` and this file does not open it at file scope (each
  consumer opens it locally).

The unique call site (inside `lowreg_forceJetMass`) gained `hRρ`, `hbridge`,
`hballU`; `hbridge` was already built there as a `have` from
`liftN_smoothN_coeff`, and `hballU` is already one of that theorem's binders, so
no producer work was needed.  The FRONTIER docstring and the module-header bullet
now say why the two hypotheses are part of the statement.  `hRρ` is genuinely
load-bearing for the eventual proof: the fibre-smallness certificate `hreal'` is
stated at radius `ρ`, and the Galerkin argument must apply it to states in the
`R`-ball.

No other statement in the file moved; `lowreg_forceJetMass`,
`lowreg_forceDriver`, `lowreg_allOrderJet`, `lowreg_joint_smooth` are unchanged.
Grep confirmed, before and after, that `lowreg_spatialMass` has exactly one
consumer repo-wide.

### Verification

**GREEN**, first try, no route failures.  Focused check passed.  Sorry census:
exactly one `declaration uses sorry`, on the widened `lowreg_spatialMass`.
Axiom census taken **before** the edit and repeated after, identical in both:
`lowreg_spatialMass`, `lowreg_forceJetMass`, `lowreg_allOrderJet`,
`lowreg_joint_two` all `[propext, sorryAx, Classical.choice, Quot.sound]`;
`lowreg_joint_smooth` `[propext, Classical.choice, Quot.sound]` (still
`sorryAx`-free and independent of the frontier).

### Lean note

`#print axioms` DOES print through `lake env lean` / `lake-locked check` in this
checkout, contrary to an older lesson note.  A temporary `#print axioms` block
inside the namespace, removed afterwards, is a cheap way to take a before/after
axiom census on a file whose full build is expensive.

### Honest accounting

**0% new mathematics.**  S0 converts a false statement into a true-target
statement at zero proof cost; the frontier is still **0% proved**.  Everything
that used to be reported as "conditional on `lowreg_spatialMass`" was, until
today, conditional on something unprovable — that is the only real change in the
tree's meaning.  (N) `ricci_flow_unif_existence`: **0%**.

## 2026-08-04, option-(b) brick B5 — the endpoint reads the STATE, GREEN

Ruling No. 106 / `OPTIONB_FLOOR_PLAN.md` §6, the last of B3/B4/B5.  Brick 9's
`hfloor` route (recorded above) is now fully retired: the engine slot is fed by
the trajectory's own state bound, never by a derivative proxy.

### What changed

* `lowreg_allOrderJet`: `{Kf}` → `{Rcap}`, and its last conclusion conjunct
  `Real.sqrt T * ‖fHi‖ ≤ Kf` becomes
  `∀ t ∈ Set.Icc (0:ℝ) T, ‖timeH1.toFun u t‖ ≤ Rcap`.  Three lines produce it:

  ```lean
  have hstateU : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun ucs.lo t‖ ≤ Rcap :=
    ucs.lo.norm_le_of_ae_le hT
      (by filter_upwards [hballU] with t ht using ht.trans hRcapLe)
  ```

  i.e. B2's producer (`TimeH1Modulus.lean:156`) applied to the package's a.e.
  ball composed with the new `R ≤ Rcap` conjunct.  `hballU` keeps its other
  consumers (`hballD`, `coord_eq_smoothN`), so nothing else moved.
* `lowreg_joint_smooth`: the slot `hfloor : √T·‖u.deriv‖ ≤ 1/(2C)` becomes
  `hstate : ∀ t ∈ Icc 0 T, ‖timeH1.toFun u t‖ ≤ 1/(2C)`, passed straight to the
  engine.  The B1 shim `u.state_le_of_sqrt_floor hinit hfloor` and the local
  `hinit` are gone.  `state_le_of_sqrt_floor` itself STAYS — it is public
  `timeH1` API with its own docstring; only this call site disappears.
* `lowreg_joint_of_re`: `hKfC : Kf ≤ 1/(4C)` → `hRcapC : Rcap ≤ 1/(2C)`, and the
  whole `hderiv` / `hfloor` derivation (the `maxRegDuhamelMap_deriv` +
  `maxRegHomogeneousDerivField_norm_le` + `maximalRegularityDerivField_norm_le`
  chain giving `‖u.deriv‖ ≤ 2‖fHi‖`, ~30 lines) is deleted in favour of

  ```lean
  fun t ht => (hstateU t ht).trans hRcapC
  ```

  The `obtain ⟨hC_pos, -⟩ := … .choose_spec` there is now unused and removed.
* `lowreg_joint_two`: instantiates `Rcap := 1/(2C)` instead of `Kf := 1/(4C)`;
  the final `le_rfl` still discharges the cap.  Public statement UNCHANGED.

### Why the factor is `1/(2C)` and not `1/(4C)`

`1/(4C)` was a *forcing* level: it had to survive `‖u.deriv‖ ≤ 2‖fHi‖`, which
costs a factor 2.  The state bound is compared with the engine's slot directly,
so the cap is the engine's own constant `1/(2C)`.  Read the factor off
`MaxRegSolutionJointlySmooth.lean:1349`, not off the old floor.

### Verification

Targeted build GREEN first try, [9985/9985], zero errors.  The only `sorry`
warning is `:1047` — `lowreg_spatialMass`, the single pre-existing campaign
frontier (its `sorry` is at `:1088`).  Axiom census, unchanged from before:

* `lowreg_joint_smooth`: `[propext, Classical.choice, Quot.sound]` —
  **`sorryAx`-free**;
* `lowreg_forceJetMass`, `lowreg_allOrderJet`, `lowreg_joint_of_re`,
  `lowreg_joint_two`: `sorryAx` **only** through `lowreg_spatialMass`.

### Grep-proof that the order-2 static force left the horizon

`lowregFloorHorizon`: zero occurrences repo-wide in `.lean`.  `staticForce`:
zero occurrences in `LowRegApplyTwo.lean` and `LowRegAllOrderJet.lean`.  What
survives, and why it is harmless:

* `LowRegLiftNTerm.lean` — the `def staticForce` itself, `liftForceHi`, and
  `norm_liftForceHi_le` (whose `hD : ‖staticForce g₀ g_bg 2‖ ≤ D` is now the
  only `‖staticForce … 2‖` in the tree).  `norm_liftForceHi_le` has **no
  consumers**; it is unused API, not a horizon.
* `LowRegForceHi.lean:144,215,284` — `staticForce … 2` as an OBJECT inside the
  frozen split `liftHiN` and its inclusion naturality.  The high forcing still
  contains the static field; nothing bounds its norm any more.

So `‖staticForce … 2‖` appears in **no** horizon, radius, or existence formula.

### Honest accounting

**0% new mathematics** in this brick either: B3/B4/B5 delete a redundant route
and re-route a slot.  What they DO change is the horizon's dependency: `τ₀` is
now closed in `(Ctop, B0, B1, D, ρ, P, C)` with `D` the ORDER-1 force number, so
front 3's item (C)1 is dissolved in Lean and not merely in design.  The residual
noted in the plan's §9 is unchanged: `C` is still
`(hs2_opBound_at_two hDim g).choose`, an opaque witness — exposing it is front
3's brick G3, untouched here.  (N) `ricci_flow_unif_existence`: **0%**.

## 2026-08-04, brick S0-bis + Z — the frontier moved from `a = 2` down to `a = 1`

### What changed

`lowreg_spatialMass` is **no longer the `sorry`**.  It is now proved outright,
sorry-free, from a new named leaf `lowreg_loMass` which states the same thing
about the **order-one** forcing.  The whole content of the step is that the
conclusion is *inclusion-invariant*:

* `hincl` (the shape `force_hi_id` uses) says `fLo` is the pointwise scale
  inclusion of `fHi`, hence `timeL2Inclusion … fHi = fLo` by `Lp.ext`;
* `timeModeCoeff_timeL2Inclusion` then gives
  `timeModeCoeff fLo i = timeModeCoeff fHi i` **as elements of `L²(0,T)`**, so
  the two `perModeConv` families are literally the same functions of `t` and
  the mass statements are interchangeable by `simp only [hmode]`.

The widening list (planner-approved, ledger No. 132) landed as three arguments
rather than a dozen: `fLo`, `hincl`, and `hlo : IsLowSolve g hT hT1 fLo`.
`IsLowSolve` (new, `ShortTime/UnifClassBounds.lean`) is the whole
`lowreg_partial_sol_of_bounds` bundle packaged as a *property of its forcing* —
background metric, threshold, the six numbers, the four producer certificates,
the horizon cap, the forcing ball `‖fLo‖ ≤ lowregStateRad …/4`, and the a.e.
Nemytskii identity along `fLo`'s own Duhamel field, with everything but `fLo`
existentially bound.

### The propagation, and why the top endpoint is unchanged

`lowreg_spatialMass` → `lowreg_forceJetMass` → `lowreg_allOrderJet` →
`lowreg_joint_of_re` each gained `fLo` plus (at the two lower levels) `hincl`,
(at the two upper levels) the transport `hfLo : ∀ᵐ t, f t = tensorHsCongr … (fLo t)`,
and `hlo`.  `lowreg_allOrderJet` rebuilds `hincl` from `hfLo` and the pointwise
inclusion conjunct of `IsRealizedTwo` (previously discarded as `-` in the big
`obtain`; it is conjunct 7, now named `hfInc`) by `tensorHsCongr_incl` +
injectivity of the isometry `tensorHsCongr` — the same three lines as
`force_hi_id`'s ending.

`lowreg_solve_two` (`ShortTime/LowRegApplyTwo.lean`) now exports
`∃ f fLo, IsRealizedTwo … ∧ (∀ᵐ t, f t = tensorHsCongr … (fLo t)) ∧ IsLowSolve …`.
Both new components are FREE at that call site: `f` is literally
`tensorHsCongrL … gforce`, so `hfae` (already there at `:725`) is the transport,
and `isLowSolve_of_sol` packages the arguments and results of the
`lowreg_partial_sol_of_bounds` call at `:711` verbatim.  Consequently
**`lowreg_joint_two`'s statement did not change at all**, and `lowreg_solve_two`
is still axiom-clean — the honest-input audit for the widening is discharged,
not deferred.

### The blocker for `lowreg_loMass` — TWO gaps, one of them new

`lowreg_loMass` is 0% and did not move.  Beyond the analytic derivation, a
**second, independent and previously unrecorded gap** was found while wiring:

**The identification layer does not apply to the campaign's solver.**
`EigenProjPartialSol.lean` (adapter B/C: `proj_partial_sol`, `forceMap_dist_le`,
`projFix_dist_le`, `projFix_le_two`) is stated over `partial_sol_const`, whose
nonlinearity is **globally Lipschitz** (`hLip : LipschitzWith L Nfun`, needed to
form `nemytskiiOn`).  The campaign's order-one solve is `partial_sol_tame`, and
`lowregNfun` is **not** Lipschitz:

* `lowerState g₀ a R = lowerBall J R = {x | ‖J x‖ ≤ R}` bounds only the
  `H^{a+1}` norm, never the ambient `H^{a+2}` one;
* the third arm of the tame estimate is `B1·(‖u‖+‖v‖)·‖J(u−v)‖` with `‖u‖` the
  `H^{a+2}` norm — unbounded on that set.  (`partial_sol_const`'s two-arm
  `hsingle` *does* imply Lipschitz, `L = C₁R + C₂‖J‖`; that is exactly the arm
  the quasilinear DeTurck nonlinearity adds and `partial_sol_const` cannot
  express.)

So `projFix_le_two` cannot be instantiated at the campaign data as adapter C's
hand-off assumed.  `partial_sol_tame` *does* build the contraction internally
(`Λ` at `TameForcingFixedPoint.lean:534`, `hΨ_lip` at `:831`, `Λ ≤ 1/2` at
`:575`) but exports none of it, and its `L²` Nemytskii is the local
`(memLp_tame …).toLp`, with `memLp_tame` `private`.

The missing API is therefore: a public tame Nemytskii (`nemytskiiTameOn` +
`coeFn`) beside `nemytskiiOn` in
`…/TensorMaximalRegularity/LocalNemytskii.lean`, then tame analogues of
`projN_nemytskii`, `forceMap_dist_le`, `projFix_dist_le`, `projFix_le_two`, and
a `proj_partial_sol_tame` (which is just `partial_sol_tame` at `projNfun`, since
`‖Π_N x‖ ≤ ‖x‖` gives the tame estimate with the same constants and `Π_N ∘ N`
is continuous).  That is one adapter-C-sized brick.  **This is a design choice
for the planner** — the alternative is to re-derive the campaign's `a = 1`
estimate in `partial_sol_const`'s two-arm shape, which the quasilinear structure
appears to forbid.

The second gap is the one session 1 already scoped: the DeTurck rung derivation
at base order 1, calibrated into the `(α, β, D)` of `two_mul_sum_ladder_le`
(`α < 1` is the absorption) and fed to `galerkin_energy_l1_bound`, then
`fatou_sq_mass`.  Untouched.

### Verification

Focused checks green on all three edited Lean files; targeted module builds
green in dependency order (`UnifClassBounds` → `LowRegApplyTwo` 9984 jobs →
`LowRegAllOrderJet` 9985 jobs).  Axiom census: `isLowSolve_of_sol`,
`lowreg_solve_two` and `lowreg_joint_smooth` are `[propext, Classical.choice,
Quot.sound]`; `lowreg_loMass` and everything above it carry `sorryAx`.  Sorry
census of `LowRegAllOrderJet.lean`: **1**, at `lowreg_loMass` — the file's only
one, as before, but one scale lower.  No `maxHeartbeats`, no git.

### Lean notes worth keeping

* `timeL2Inclusion` is a plain `def` over `compLpL`, so `rw [h1]` against a
  `coeFn_compLpL` hypothesis fails on the *syntactic* mismatch
  `↑↑((timeL2Inclusion ⋯) fHi) t` vs `↑↑((compLpL …) fHi) t`.  `exact h1.trans h2`
  closes it — `exact` unfolds the `def` at default transparency.  Do not reach
  for `simp [timeL2Inclusion]`.
* Keep `a` symbolic: the order-one objects are spelled `((1 : ℕ) : ℝ)` and are
  NOT interchangeable with the literal `1` (the scale sits in a type index).
  `IsLowSolve`, `lowreg_loMass` and the transport all use `((1 : ℕ) : ℝ)`; only
  `IsRealizedTwo`'s `f` sits at the literal `(1 : ℝ)`, which is precisely why
  `hfLo` exists.
* `tensorHsCongr` is a `≃ₗᵢ`, so `.injective` is available directly — no
  `tensorHsCongr_injective` lemma is needed (and none exists).

### Honest accounting

`lowreg_spatialMass` went from 0% to **proved** (its content was the transport,
which is real but small).  `lowreg_loMass`, the leaf that now carries the
mathematics, is **0%**.  Front 2's spatialMass chain is therefore NOT complete
and the campaign sorry census did NOT drop to (N) alone.  (N)
`ricci_flow_unif_existence`: **0%**, unchanged.

## 2026-08-04, tame identification layer + Z session 3

### What landed elsewhere, and what it buys `lowreg_loMass`

The second gap diagnosed by session 2 — the identification layer being stated
over `partial_sol_const` while the campaign solves with `partial_sol_tame` — is
**closed**.  Three files, all axiom-clean:

* `TensorMaximalRegularity/LocalNemytskii.lean`: public `timeL2_norm_le_four`,
  `memLp_tame`, `nemytskiiTameOn`, `nemytskiiTameOn_coeFn`.
* `TensorMaximalRegularity/TameForcingFixedPoint.lean`: `nemytskiiTame`,
  `nemytskiiTame_coeFn`, and **`tameMap_dist_le`** — the contraction
  `partial_sol_tame` previously ran internally and did not export.
* `HeatSemigroup/EigenProjTameSol.lean` (new): `projN_cont`, `projN_tame`,
  `proj_partial_sol_tame`, `projN_nemytskiiTame`, `projFixTame_dist_le`,
  `projFixTame_le_two`.

Instantiated at the campaign data in `ShortTime/LowRegGalerkinIdent.lean` (new):
`lowreg_proj_tendsto` exhibits `fLo` as the `L²([0,T]; H^1)` limit of
`Π_N`-fixed forcings, and `lowreg_projMode_tendsto` descends that to every
eigen-coordinate at every `t ∈ Icc 0 T`.  The latter is literally the
convergence hypothesis of `fatou_sq_mass`.  `lowreg_loMass`'s docstring was
updated to record this; the file now imports `LowRegGalerkinIdent`.

### What `lowreg_loMass` still needs — and it is NOT small

`fatou_sq_mass` takes two inputs.  The convergence half is now proved.  The
other half — an `N`-uniform bound on
`∑_{i ∈ eigenIdxFinset N} w_σ(i)·(perModeConv λᵢ (timeModeCoeff (fseq N) i) t)²`
— is the whole analytic frontier, and it needs three order-one producers that
exist today only above the Lipschitz gate `2·finrank ℝ E + 10 ≤ a`
(`≥ 16` in dimension three), listed with their high-order analogues in
`ShortTime/LowRegGalerkinIdent.md`: the `V_N` Galerkin ODE system for
`lowregNfun`, the identification of its coordinates with `perModeConv`, and the
per-scale closure at base order `1`.  The `(α, β, D)` calibration of
`two_mul_sum_ladder_le` sits *after* the third of these and was again **not
reached**, so there is still no `(α, β, D)` outcome to report.

### Honest accounting (2026-08-04, session 3)

`lowreg_loMass` is still **0%** and still the single `sorry` of this file
(`:1052` after the added import).  What moved is its *machinery*: the
identification half of the pipeline went from unreachable (session 2's blocker)
to proved and instantiated.  The campaign sorry census did **NOT** drop to (N)
alone: `lowreg_loMass`, `lowreg_spatialMass`, `lowreg_forceJetMass`,
`lowreg_allOrderJet`, `lowreg_joint_of_re` and `lowreg_joint_two` all still
carry `sorryAx`.  (N) `ricci_flow_unif_existence`: **0%**, unchanged, still
stated-and-unproved at `Evolution/ExtendViaUniqueness.lean:80` with its `sorry`
at `:98`.

## J0a (2026-08-04): `hDim` on the two mass theorems

`lowreg_loMass` and `lowreg_spatialMass` each gained a leading
`(hDim : Module.finrank ℝ E = 3)`.  The conclusions are untouched.  Propagation
was one argument at two call sites (`lowreg_spatialMass` → `lowreg_loMass`, and
`lowreg_forceJetMass` → `lowreg_spatialMass`, both of which already bound `hDim`).
The endpoint at the tail of the file already carried `hDim`.

Also: the `lowreg_solve_two` call now supplies the new fibre-threshold parameter
`thr := deTurckArmContractionThreshold'' (finrank ℝ E)` with its positivity and
`≤ 1/3` proofs — behaviour identical, but the choice is now visible at the call
site, which is where J0b will re-choose it from the ladder constant `κ`.

`lowreg_loMass` is still `sorry`.  The widening is what makes the eventual proof
STATABLE (dimension three is needed by every ladder and tower it must call); it
proves nothing by itself.

## J4-rung-3 (2026-08-04): NOT DELIVERED — precise narrowing

The dispatched framing was "the engine `two_mul_sum_ladder_le` needs only
`(α, β, D)` supplied".  Grep says that under-counts by three pieces.  Recording
the census so the next brick does not re-derive it.

**The pairing budget at k = 3 does NOT fail** (the dispatch's STOP condition is
NOT met).  Rung `k = 3`, `σ = 3`: the engine wants
`‖fd‖_{H^{σ−1}} ≤ α‖u‖_{H^{σ+1}} + β‖u‖_{H^σ}`, i.e. `H²  ≤ α·H⁴ + β·H³`.  That is
EXACTLY `n_diff_hm_rung`'s shape read at `m = k−1 = 2`.  And `c0_jet_tower_quad`
at `i = 2` has window `range (i+2) = range 4`, i.e. state jets `j ≤ 3`, inside
`E₃` and strictly below `E₄` — PSTOP §6.3's displayed pairing, confirmed.

**What exists (verified, no work needed).**
* engine `two_mul_sum_ladder_le` (`Sobolev/Tensor/CrossScaleCauchySchwarz.lean`),
  ZERO consumers — built for exactly this job.  Its RHS
  `(2α+ε)E_{σ+1} + (β²/ε)E_σ + 2D√E_σ` maps onto the `hclosure` slot by
  `Cδ = 2α+ε`, `Cmid k + A N t = β²/ε`, `seed k = 2D`;
* the consumer slot itself, now `N`-indexed (J5, this brick);
* the `H^m` ladders `a2_ladder` / `a1_ladder` / `n_diff_hm_rung`;
* the ball-free towers `c0_jet_tower_quad`, `selfLow_jet_quad` (J3);
* spectral norm = weighted sum for FINITE combos:
  `finiteEigenCombo_spectral_normSq`, `finiteEigenComboHs_norm_eq_sqrt_spectral`
  (`Garding/EigenComboGardingReduction.lean`).

**What is missing (the three real pieces).**
* **(M1) Finset-form Bessel truncation.**  `∑_{i∈S} w i σ (v.coeff i)² ≤ ‖v‖²_{H^σ}`
  for general `v`.  Only the SINGLE-mode `weight_mul_coeff_sq_le_normSq`
  (`Spectral/Intrinsic/TensorHsInterpolationLimit.lean`) exists; no Finset-sum
  form in the tree.  This is what converts "the ladder bounds
  `‖𝒩(U)−𝒩(0)‖_{H²}`" into the engine's `hladder` left-hand side.  Small,
  reusable, canonical home is next to the single-mode lemma.  Do this first.
* **(M2) a low-lane Galerkin forcing at `a = 1`.**  `deTurckGalerkinForcingSymm`
  (`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean:58`) is defined through
  `deTurckSobolevNHa2Symm`, which only EXISTS above the Lipschitz gate
  (`deTurckSobolevNHa2_exists_of_super`, `2·finrank+10 ≤ a`).  At `a = 1` the
  object is `lowregNfun`/`lowRegN`, and no mode-coordinate forcing function is
  defined for it.  Without it the rung-3 closure has no `Fseq` to be stated
  ABOUT — this is the second of the three order-one producers listed in
  `lowreg_loMass`'s own docstring, and it is a prerequisite, not a detail.
* **(M3) ball-free (quad) ladders.**  `a2_ladder` / `a1_ladder` / `n_diff_hm_rung`
  all carry `‖T‖_{H^{a+2}} ≤ R₀` with `3 ≤ a` (resp. `2 ≤ a`), i.e. an H⁵ (resp.
  H⁴) ball — precisely what rung 3 must avoid.  J3 delivered the ball-free
  `c0_jet_tower_quad`, but the ladders ABOVE it were not re-derived on it:
  `a1_ladder` still calls `c0_jet_tower` + the private `coeffCap`
  (`DeTurck/LowRegLadderRung.lean:321`), which turns a tower into a fibre cap via
  `(1 + (C2·R₀)²)`.
  The quad route is feasible and dimension three is why: `coeffCap`'s window is
  `range (finrank/2 + 2) = range 3`, i.e. state jets `j ≤ 2` — so only the H²
  STATE BALL (PSTOP §6.1(i)) is needed, never H⁵, with the extra
  `K2·‖T‖²_{H³}` term carrying the `L²_tH³` (PSTOP §6.1(ii)) dependence that
  becomes the `A N t` coefficient.  This is exactly why J5 had to land first.

**Over-count check, run in both directions.**  `c2_jet_tower`
(`LowRegLadderRung.lean:145`) BINDS `a`, `R₀`, `hball`, but its conclusion is
already ball-free in shape and its proof goes through `topKer_jet g`, which takes
only `hDim` and `g`.  The ball there looks VESTIGIAL, so the a₂ arm's ball
dependence is likely in `appCc_cap_hs_le`, not in the C2 tower.  Confirm this
before pricing M3 — it may make the a₂ half of M3 nearly free.

**Why nothing was stated.**  A rung-3 closure written now would need M1+M2+M3 as
three fresh hypotheses.  That is the frontier-wrapper failure mode CLAUDE.md
forbids ("at most one genuine mathematical frontier", "no adapter theorems whose
main content is turning the current goal into new hypotheses").  The honest next
brick is M1 alone (small, reusable, unblocks the transport), then M3, then M2.

**M3 refinement (grep-verified, same session).**  The a₂ arm's H⁵ ball is NOT in
`c2_jet_tower` — it is in `appCc_cap_hs_le` (`DeTurck/LowRegLadderRung.lean:78`),
whose gate is `max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`, i.e. `a ≥ 3` in dimension
three, and whose ball is `‖T₀‖_{H^{a+2}} ≤ R₀` ⟹ H⁵.  `c2_jet_tower` binds
`a`, `R₀`, `hball` but proves its (already ball-free) conclusion through
`topKer_jet g`, which takes only `hDim` and `g`.
So M3 splits: the a₂ half needs `appCc_cap_hs_le` re-read at a smaller `a`
(or a quad sibling), and the a₁ half needs `c0_jet_tower_quad` threaded through
the private `coeffCap`.  Neither is blocked; both are unwritten.

## 2026-08-05: explicit adapted package threaded through front two

`lowreg_loMass` now consumes `IsAdaptedLowSolve`, and that exact package is
threaded unchanged through `lowreg_spatialMass`, `lowreg_forceJetMass`,
`lowreg_allOrderJet`, and `lowreg_joint_of_re`.  The unique producer
`lowreg_joint_two` now calls `lowreg_solve_adapt` at the endpoint cap; the
producer's `min` simultaneously preserves that cap and the calibrated
absorption cap.

The `σ ≤ 3` branch of `lowreg_loMass` is a proved call to `lowregMassLowAt`.
The single remaining `sorry` is now confined to `3 < σ`, where rungs 4–5 and
the general-`k` dissipation export are still missing.  Focused verification of
the whole file and its targeted module refresh passed; the only diagnostic is
the intentional `sorry` warning.

Honest denominator: `lowreg_loMass` as an all-real-σ theorem remains unproved
(0%); its σ≤3 branch is closed.  The explicit-package/GAP-ADAPTH machinery is
complete for one metric, while class-uniform calibration remains separate.
The `(N)` theorem remains unproved (0%); whole HCG remains about 3%.

## 2026-08-05: all-real low-mass frontier closed

This section supersedes the status immediately above.  `lowreg_loMass` is now a
proved call to `lowregAllMassAt` for every real exponent.  The proof keeps one
projected sequence through its ODE, fixed fifth-energy cap, all higher energies,
and Fatou limit; it neither reselects a path nor performs rung induction.

The source chain `lowreg_spatialMass` → `lowreg_forceJetMass` →
`lowreg_allOrderJet` → `lowreg_joint_of_re` → `lowreg_joint_two` therefore has
no residual low-mass frontier.  Focused checks and direct module refreshes
passed warning-free; the widened axiom census is recorded separately.

Honest denominator: `lowreg_loMass` theorem 100%, and its dedicated all-real
machinery 100%.  The chain remains a per-metric self-background producer;
`ricci_flow_unif_existence` is stated but still unproved from it (0%), because one
threshold, radius, and horizon must be hoisted before `∀ g₀`.  Whole HCG
compactness remains about 3%.

## 2026-08-05: positive per-metric joint endpoint

`lowreg_joint_open` calls the strict adapted producer, chooses the midpoint
`(B2 + 1) / 2` internally, and returns one positive horizon carrying the full
all-order joint endpoint.  Unlike the compatibility route, the theorem no
longer asks a caller to supply a contraction level whose interval might be
empty.

Focused verification and the targeted module refresh passed warning-free.  The
endpoint is complete for each fixed metric (with the representation identity as
its explicit geometric input).  It is not `(N)`: the horizon is selected after
the metric, while `ricci_flow_unif_existence` requires one positive horizon
chosen before the whole metric class.
