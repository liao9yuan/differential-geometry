# LowRegApplyTwo — plan (written 2026-08-02, pre-implementation)

Target: new final-assembly file `LowRegApplyTwo.lean`, one theorem
`lowreg_apply_two` — the `(aLo, aHi) = (1, 2)` instantiation of
`lowreg_realize_two` with the refold-route families.  This is the junction
brick that turns the hypothesis-parameterized Lane-C C2 into a concrete
realized `CrossScaleField` along the actual `lowreg_partial_sol` trajectory.
Import layer: above `LowRegLiftHfLo`, `LowRegLiftNTerm`, `LowRegLiftSmall`,
`LowRegRealizeTwo` (final assembly above all producers).

## Input map (producer → realize_two slot, all GREEN today)

- `lowreg_partial_sol` (`LowRegDenseSolve.lean:298`, specialized `g_bg := g₀`)
  → trajectory `gforce`, `hforce` (a.e. Nemytskii identity), `hball`
  (`∀ᵐ t, field t ∈ lowerState g₀ 1 R` — hence the a.e. `H3` bound with
  `B3 := R`), `Continuous Nfun`, `Continuous coreN`, `‖gforce‖ ≤ R/4`.
- `lowreg_hfLo` (`LowRegLiftHfLo.lean`) → the `hfLo` fixed-point slot verbatim
  (families `lowAffA2` / `refoldAffA1`, forcing `liftForceLo`).
- `lowreg_hfLo_data` (extended by the 2026-08-02 Hi-export brick) → the SAME
  `FLo` plus `FHi`-side family `refoldAffA1Hi`, `MemLp` both sides, toLp
  bounds `≤ L*‖u‖ + √T*Z` both sides, explicit `Z L ≥ 0`, a.e. uniform
  bounds, and the pointwise commuting square
  `∀ t, incl ∘ AHi t = ALo t ∘ incl` → slots `A1Hi/hA1Hi/A1Lo/hA1Lo` and
  `hA1compat`.
- `liftA2Two` / `liftA2Two_data` (`LowRegRealizeTwo.lean`) → `A2Hi/hA2Hi` with
  uniform bound `C * ρ` → `C2Hi`; unconditional.
- A2 compat (`hA2compat`): route depends on the identification finding between
  `lowAffA2` (from `lowA2Lo`) and the low side of the `lowRegA2Total` square
  (`lowRegA2TotalLo`, `TensorMaximalRegularity/LowRegOperatorTime.lean`) —
  RESOLVE FIRST, see Risks.
- `liftForceHi` / `liftForceLo` / `lift_force_incl` (`LowRegLiftNTerm.lean`)
  → `f0Hi / f0Lo / hf0` verbatim.
- `lift_smallness` (or `lift_small_two_bd`) + `lift_small_le`
  (`LowRegLiftSmall.lean:193/230/246`) → `hsmallHi ∧ hsmallLo`.  Chain:
  `‖u‖_{L²ₜ} ≤ √T * B3` from the a.e. ball bound (`norm_toLp_le_bd`), then
  `lift_small_le` turns `≤ L*‖u‖ + √T*Z` into `≤ (L*B3 + Z)*√T =: M*√T`;
  choose `c` with `C2Hi, C2Lo ≤ c < 1` by shrinking `ρ` against the fixed
  `liftA2Two` constant `C` (`c := C*ρ ∨ max` of the two lane bounds), and take
  `T ≤ lowregLiftHorizon c M` as an explicit hypothesis of the theorem (the
  endpoint chooses the horizon; do NOT try to produce the shrink internally).

## Statement sketch

Hypotheses: `hDim`, `g`; the `lowreg_hfLo_data` hypothesis block (R ρ δ T
bounds, `hreal/hreal'`, the four continuity/core-formula inputs, `B2`-bound
for `lowA2Lo`, trajectory `f`, `hball`, `hforce`, `B3` ball); smallness side
conditions (`hc : C2-bounds ≤ c`, `hc1 : c < 1`, `hM`, `hTle : T ≤
lowregLiftHorizon c M`).  Conclusion: the `lowreg_realize_two` ∃-package at
`aLo = 1, aHi = 2` for the concrete families (CrossScaleField `u`, `fHi`,
zero trace, clean equation, fixed points both scales, forcing inclusions,
carrier/representative pins).

Exponent discipline: realize_two spells scales as `aHi + 1 = (2:ℝ)+1` etc.;
producers spell `(3:ℝ)`.  Transport with `tensorHsCongrL` + the free
`congrOp_aemeas/memLp/norm_le` lemmas (`cases` on the exponent equality —
LowRegRealizeTwo.md "Lean lessons"); `subst`-first idiom for `hlo`.

## Risks / open items (resolve before or during implementation)

1. **RESOLVED (ruling, 2026-08-02).** `hA2compat`: the §3 finding shows
   `lowAffA2 ≠ lowRegA2TotalLo` with three real differences (missing
   principal summand `lowRegA2TimeLo`; extra radial factor; `incl32 ∘
   affState` vs `lowRegStateL2` states, equal only a.e.).  Since realize_two's
   `A2Lo` slot is FORCED to be the term in the proved `hfLo` equation
   (= `lowAffA2`), the ready-made `lowRegA2TotalLo_data` square CANNOT be
   cited and `liftA2Two` is NOT the A2Hi of this instantiation.  Route: build
   the Hi sibling `lowAffA2Hi` from `lowA2Hi`
   (`DeTurck/DeTurckRemainderLowBaseTime.lean:1555`) with the same radial
   factor at the `aHi` scale, plus measurability, a `C2Hi` uniform bound, and
   its own compat square with `lowAffA2` — structurally the same work
   `refoldAffA1Hi`/`refoldAffA1_compat` did for the first-order arm.  The
   square should factor as (radial-scalar commutes with inclusion) ∘
   (completed a2 Hi/Lo square); locate the completed a2 square or derive it
   from the smooth-core a2 pair (`a2_pair_lip` / `radialA2_*` idiom) — if the
   smooth-core a2 pair estimate is genuinely missing, STOP and name it.
2. `C2Lo` for `lowAffA2` is exported as an abstract `NNReal` by
   `lowreg_hfLo_data`; the smallness needs `C2Lo ≤ c` — thread the `B2`
   pointwise bound (`‖lowA2Lo v‖ ≤ B2`) through instead if the abstract
   constant is inconvenient.
3. `hf0` orientation: `lift_force_incl` must match realize_two's
   `timeL2Inclusion … f0Hi = f0Lo` exactly (NTerm fit-tested this against
   lift_two — re-check against realize_two's spelling only).
4. Two-line follow-up flagged by the Hi-export brick: `Continuous FLo`, the
   `FLo` core formula, and the `FLo` affine bound are consumed internally by
   `lowreg_hfLo_data` but not re-exported; add them while in the file.

## Realized shape (2026-08-02) — differs from the sketch in one place

The sketch above asked for `M` and `hTle : T ≤ lowregLiftHorizon c M` as plain
explicit hypotheses.  That is **not statable**: the first-order size constant is
`max (Z + L * B3) B1`, and `Z`, `L`, `B1` are produced by `refold_time` /
`refoldAffA1_data` *after* `T` and the trajectory `f` are fixed, so no
hypothesis of the outer theorem can mention them.  The horizon condition is
therefore stated after the packet is produced:

```text
… (all hfLo_data hypotheses) (the three lowA2Hi hypotheses),
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ {c} (0 ≤ c) (c < 1) (B2 ≤ c) (B2Hi ≤ c) (T ≤ lowregLiftHorizon c K),
      ∃ FHi C2Hi hA2Hi hC2Hi hA1Hi uHi fHi u, (the realize_two package)
```

This keeps the horizon an explicit input (the endpoint still chooses `T`; no
shrink is performed internally) while staying honest about where `K` comes from.
The consumer's obligation is unchanged in substance: pick `T` small enough for
the constant the packet reports at that `T`.

`FHi, C2Hi, hA2Hi, hC2Hi, hA1Hi` are existentially quantified in the conclusion
for the same reason `lowreg_hfLo_data` quantifies its analogues: they appear as
*data* arguments of `nonautL2Map` inside the high-scale fixed-point equation.

## Honest-input audit of the three new `lowA2Hi` hypotheses

`Continuous (lowA2Hi …)`, `∀ v, ‖lowA2Hi … v‖ ≤ B2Hi` and the completed
`H²`-state square are **jointly satisfiable by one existing proved theorem**:
`lowA2_small` (`TensorMaximalRegularity/LowRegOperatorTime.lean:667`), which
delivers all three plus the two low-side analogues (`hA2cont`, `hA2bd` with
`B2 := C * ρ`) on a shrunken radius, ultimately from `radialA2_lip`
(`DeTurck/DeTurckRemainderLowBaseTimeA2.lean:370`).  Shrinking `ρ` against its
`C` is also the intended lever for `B2 ≤ c` and `B2Hi ≤ c`.  Caveat for the
wiring brick: `lowA2_small` states its two uniform bounds through the
`show a2Op … from …` operator-norm idiom, so the call site may need the same
ascription.

## Status

- 2026-08-02, brick 2a — **GREEN** (`LowRegLiftHfLo.lean`, 1264 lines).
  New: `lowAffA2Hi` (313), `lowAffA2Hi_le` (337), `lowAffA2Hi_data` (378),
  `lowAffA2_compat` (450), private `loH4` (51); `stateField` (73) promoted from
  `private` to public; `lowreg_hfLo_data` (1120) additionally exports
  `Continuous FLo`, the `FLo` core formula, the `FLo` affine bound and
  `(C2 : ℝ) = B2`.  Risk 1 discharged: the completed a2 square was *found*, not
  rebuilt — see `LowRegLiftHfLo.md`, third pass.  Risk 2 discharged by the
  `(C2 : ℝ) = B2` export.  Risk 4 done.
- 2026-08-02, brick 2b — **GREEN** (`LowRegApplyTwo.lean`, 255 lines, one
  public theorem `lowreg_apply_two` at line 82).  Risk 3 discharged:
  `lift_force_incl` fits `lowreg_realize_two`'s `hf0` verbatim.  No `sorry`,
  `admit`, `axiom` or `set_option`; focused check and targeted build both green.
- 2026-08-02, brick 3 — **GREEN** (547 lines).  `lowreg_solve_two` (line 412)
  runs the whole `(1, 2)` realization along the *actual* solver trajectory; see
  the next section.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
- 2026-08-02, brick 4 — **GREEN** (553 lines).  `B3` **dissolved**: the
  `L^∞_t H³` slot is gone from the whole chain and the smallness runs on the
  `L²_t` maximal-regularity estimate instead.  See the brick-4 section below.
  Axiom-clean.
- `ricci_flow_unif_existence`: still **0%** (stated, proof not started).  This
  lane is wiring plus the smallness arithmetic, not new analysis.

## 2026-08-02, brick 3 — the solved endpoint `lowreg_solve_two`, GREEN

New in this file (line numbers current):

- `IsRealizedTwo` (273) — the conclusion of `lowreg_apply_two` as a named
  `Prop`, so the solved endpoint can state it without repeating the
  existential.  Definitionally the same formula, so `exact happly …` closes it.
- `congrLp_self` (347, private) — the time-`L²` lift of a *reflexive* exponent
  transport is the identity.  Canonical home: beside `tensorHsCongrL` in
  `SobolevScale/ExponentCongr.lean`, once that file sees the time-`L²` layer.
- `duhamel_congr` (361, private) — `maxRegDuhamelSolField` with zero initial
  datum commutes with the exponent transport of its forcing (`cases h`, then
  `congrLp_self` twice).  Canonical home: beside `maxRegDuhamelSolField` in
  `TensorMaximalRegularity/SolutionSpace.lean`.
- `a2Lo_congr` (378, private) — `LowBaseActionData.a2Lo` depends on the bundle
  only through `C2` (dense-range induction + `a2Lo_core`).  Canonical home:
  beside `a2Lo_core` in `DeTurck/DeTurckRemainderLowBaseA2.lean`.
- `lowreg_solve_two` (412) — the endpoint.  Import added:
  `ShortTime/UnifClassBounds`.

### Producer → discharged slot

| slot of `lowreg_apply_two` | producer |
| --- | --- |
| `δ`, `hδ0`, `hδ_le`, `hδ` | `deTurckArmContractionThreshold''_pos / _le_third' / _lt_one'` |
| `hreal` (at `R`, smoothCc spelling) | `realize_at_thr` → `lowregRealRad` |
| `hreal'` (at `ρ`, `ccTensorToHs` spelling) | `realize_at_thr` + `norm_smoothCc_congr` + `smoothCcToTensorHs_eq_ccToHs` |
| `hNcont` | `lowreg_bounds_exist` (its `Continuous (lowregNfun …)`, defeq to `lowRegN`) |
| `hcore` | `lowRegN_outer` at `Q = R` (`lowreg_bounds_exist` drops this conjunct) |
| `hA2cont`, `hA2bd`, `hA2Hicont`, `hA2Hibd`, `hA2sq` | `lowA2_small` (`B2 = B2Hi = C * ρ`) |
| `hA2core` | `radialA2_lip` (fourth conjunct) + `a2Lo_congr` with an `rfl` `C2` step |
| `R`, `hR`, `hRρ` | `lowregStateRad …` + `lowregStateRad_pos` + `lowregStateRad_le_P` |
| `f`, `hball`, `hforce` | `lowreg_partial_sol_of_bounds` + `duhamel_congr` |
| `T₀` | `lowregHorizon …` + `lowregHorizon_pos` |

### The radius cap (why `lowreg_partial_sol` itself cannot be used)

`lowreg_apply_two` needs `R ≤ ρ ≤ ρ₀`, and `ρ` is forced to be the radius
`lowA2_small` returns.  `lowreg_partial_sol` chooses its own state radius `R`
with no cap, so it can never be wired.  The fix is the six-number pair
`lowreg_bounds_exist` + `lowreg_partial_sol_of_bounds` (`UnifClassBounds.lean`)
run at the realization radius `P := min ρ ρN`: then
`R = lowregStateRad … P ≤ P ≤ ρ` by `lowregStateRad_le_P`.  Radii are chosen in
the order `ρ₀` (from `lowreg_apply_two`) → `Pr` (`realize_at_thr`) → `ρN`
(`lowRegN_outer`) → `ρL` (`radialA2_lip`) → `ρ` (`lowA2_small`) → `P`, each a
`min` of the ones before, so every consumer's cap holds.

### Remaining inputs of `lowreg_solve_two` (SUPERSEDED by brick 4)

Only `hDim` and `g` are hypotheses.  The conclusion reports `ρ, δ, hreal', T₀,
B2` and then asks the caller for

1. `T` with `0 < T ≤ T₀`, `T ≤ 1`;
2. ~~`B3 ≥ 0` and the a.e. `H³` trajectory bound~~ — **removed in brick 4**;
3. `c` with `0 ≤ c < 1`, `B2 ≤ c`, and `T ≤ lowregLiftHorizon c K` for the `K`
   the packet reports — **replaced in brick 4** by `6A < 1 - c` and
   `T ≤ lowregLiftHorizon' c Z`.

### Gap found: the `B3` slot is an `L^∞_t H³` bound (SUPERSEDED by brick 4)

The diagnosis below is correct; the conclusion drawn from it — that the lift
"genuinely needs a `√T`-smallness" — is **wrong**, and brick 4 removes the slot
without any `√T` decay.  Kept for the record.

`hball3` asks for an a.e.-in-time bound on the `H³` norm of the low trajectory.
Maximal regularity gives that trajectory only in `L²_t H³`
(`partial_sol_tame` exports the ball `field t ∈ lowerState g 1 R`, which is an
`H²` bound, and `‖gforce‖ ≤ R / 4`, an `L²_t H¹` bound) — nothing in the solver
chain produces an `L^∞_t H³` bound, and it is false for a general `L²_t H³`
field.  It is *not* removable by switching to the `toLp` route either: the
smallness needs `‖duhH3‖_{L²_t H³} ≲ √T · B3`, and maximal regularity only
gives `≲ ‖f‖_{L²_t H¹} ≤ R / 4`, which does not shrink with `T`.  So the
`(1, 2)` lift's contraction genuinely needs a `√T`-smallness (equivalently an
`L^∞_t H³`-type) input on the low trajectory.  Two honest routes for a later
brick: prove `‖duhH3‖_{L²_t H³} → 0` as `T → 0` *for the fixed-point family*
(the forcing itself is `T`-dependent, so this is not the naive dominated
convergence statement), or restate the `B3` slot of `lowreg_hfLo_data` as that
`√T` bound.  Nothing downstream of this brick can discharge it.

### Lean lessons

- `((1 : ℕ) : ℝ)` is **not** definitionally `(1 : ℝ)` (probed: `rfl` fails, and
  the two `timeL2 (tensorHs g 0 2 ·)` spaces are not interchangeable).  The
  `lowreg_partial_sol` → `lowreg_apply_two` bridge therefore needs the real
  transport `duhamel_congr`; `stateField` is exactly its left-hand side, so
  `stateField g hT hT1 f = field` is an *equality* of `Lp` elements, not just an
  a.e. one, and `rw` moves `hball` / `hforce` verbatim.
- `rfl` on `(refoldCore …).a2Lo = (lowCoreData …).a2Lo` is a **kernel
  deterministic timeout**, even though the `C2` fields are `rfl`-equal
  (`refold_c2` does exactly that).  Do the `rfl` at the `C2` level and lift it
  with `a2Lo_congr`; never at the completed-operator level.
- `rcases`/`obtain` `-` on a witness that later components *depend on* (the
  `C : NNReal` of `radialA2_lip`, the `Ctop B0 B1` of `lowRegN_outer`) silently
  drops the dependent components too — the symptom is `unknown identifier` at
  the use site, not an error at the `obtain`.  Name every depended-upon witness.
- `lowregNfun … = lowRegN g g hR hδ hreal` needs an explicit `rfl` after
  `rw`; `rw` will not close it, since the identification is delta plus proof
  irrelevance.
- `lowA2_small`'s `show a2Op … from …` ascriptions leave no residue: the
  bounds apply directly to the `‖lowA2Lo … v‖ ≤ B2` slot, no ascription needed
  at the call site (the caveat recorded in the honest-input audit does not
  bite).

## Lean lessons from this brick

- `lift_small_of_bd` / `lift_small_two_bd` are stated over an abstract
  `{Z : Type*} [NormedAddCommGroup Z]`, and the coefficient families live in
  *operator* spaces.  Passing the `MemLp` witness first does **not** determine
  `Z`: Lean postpones the argument because the instance metavariable is still
  open, and the a.e.-bound argument then fails with
  `@norm ?m … NormedAddCommGroup.toNorm` versus
  `ContinuousLinearMap.hasOpNorm`.  Fix: pass `(Z := …)` and `(A1 := …)` by
  name.  Pre-stating the bound as a `have` is *not* enough.
- Two separate `lift_small_of_bd` calls are preferable to one
  `lift_small_two_bd`: with two open operator-space metavariables the same
  postponement bites twice.
- `lowreg_realize_two` is applied with `(aLo := (1 : ℝ)) (aHi := (2 : ℝ))`
  supplied by name; all six order proofs are then plain `show … by norm_num`,
  and proof irrelevance makes them match the `tensorHsInclusion` arguments
  spelled in the conclusion.  No `subst` gymnastics is needed on this side —
  the `subst`-first idiom of `LowRegRealizeTwo.md` is internal to that file.
- A public theorem whose hypothesis block mentions a `private` definition is
  unusable from any other module.  `stateField` was in that state; check for it
  when an endpoint's hypothesis block is copied into a consumer.

## 2026-08-02, brick 4 — `B3` dissolved, the `L²ₜ` smallness route, GREEN

Implements the ROUTE RULING of planner update No. 94.  The `L^∞_t H³` slot is
gone from `lowreg_hfLo_data`, `lowreg_apply_two`, `IsRealizedTwo` and
`lowreg_solve_two`.

### The core maximal-regularity estimate — FOUND, not missing

`norm_maxRegDuhamelSolField_zero_le`
(`Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:217`):

```
‖maxRegDuhamelSolField a hT hT1 (0 : Hᵃ⁺²) F‖ ≤ (1 + T) * ‖F‖
```

i.e. the zero-initial Duhamel map is bounded `L²ₜHᵃ → L²ₜHᵃ⁺²` with a constant
that is `T`-dependent only benignly (`≤ 2` on `T ≤ 1`).  Its proof is
`maximalRegularitySolField_norm_le` plus the vanishing homogeneous part.  Its
`duhH3` spelling is `norm_duhH3_le` (`LowRegLiftHfLo.lean:153`), obtained from
it by `norm_congrLp` (`LowRegLiftHfLo.lean:136`), the isometry of the exponent
transport at the time-`L²` level.  **No new analysis was needed.**

### The new smallness shape

`memLp_clm_affine` gives, unconditionally, `‖toLp A1‖ ≤ L‖duhH3 f‖ + √T·Z` on
both scales.  Composing with `norm_duhH3_le` and `T ≤ 1`:

```
‖toLp A1‖ ≤ A + √T·Z,   A := 2·L·‖f‖.
```

Only the second summand is small in `T`.  `A` is a *radius-side* smallness,
structurally the same as the second-order bound `C₂ ≤ c`, so it is capped by a
`T`-free margin, not by the horizon.  New in `LowRegLiftSmall.lean`:

- `lowregLiftHorizon' (c Z) = min 1 (min ((1-c)/(4(c+1))) ((1-c)²/(144(Z+1)²)))`
  (line 282), with `_le_one` (285) and `_pos` (291).  Budget split:
  `c·T ≤ (1-c)/4` from the first cap, `3√T·Z ≤ (1-c)/4` from the second,
  leaving `(1-c)/2` for the `3A` term.
- `lift_aff_arith` (304) — the arithmetic: from `C ≤ c`, `0 ≤ V ≤ A + √T·Z`,
  `6A < 1 - c` and `T ≤ lowregLiftHorizon' c Z`, conclude
  `C(1+T) + 2√(1+T)·V < 1`.  Style copied from `lift_small_arith`; the final
  step is `linarith` once `√(1+T) ≤ 3/2` and the two caps are `have`s.
- `lift_small_aff` (350) — the `toLp` wrapper.  Its type variable is named `Y`,
  not `Z`, because `Z` is now the zeroth-order *constant*.

The old `lowregLiftHorizon` / `lift_small_arith` / `lift_small_of_bd` family is
untouched and still exported; it is simply not what this lane uses any more.

### Final hypothesis list of `lowreg_solve_two` (line 424)

`(hDim : finrank ℝ E = 3) (g : SmoothRiemannianMetric I M)` — unchanged, still
the only hypotheses.  Conclusion reports `ρ, δ, hρ, hδ0, hδ_le, hreal', T₀, B2`
with `0 < T₀`, `0 ≤ B2`, and for every `0 < T ≤ T₀`, `T ≤ 1` produces `f` with

```
IsRealizedTwo g hρ hδ0 hδ_le hreal' hT hT1 f B2 B2
```

and **nothing else**.  `IsRealizedTwo` (line 281) now opens with
`∃ A Z, 0 ≤ A ∧ 0 ≤ Z ∧ ∀ {c}, 0 ≤ c → c < 1 → B2 ≤ c → B2 ≤ c →
6*A < 1 - c → T ≤ lowregLiftHorizon' c Z → …`.

So the consumer obligations are now exactly: pick `c` with `B2 ≤ c < 1` and
`6A < 1 - c`, then shrink `T` to `lowregLiftHorizon' c Z`.  Both are inequalities
between reported reals — no analytic input is left.

### Which knob discharges the margin `6A < 1 - c`

`A = 2L‖f‖`, and the solver exports `‖gforce‖ ≤ R/4` with
`R = lowregStateRad Ctop B1 ρout P ≤ P` (`lowregStateRad_le_P`), so
`A ≤ L·R/2 ≤ L·P/2`.  `P` is a free `min` in the Finding-1 cascade, so the
margin is met by capping `P`.

ORDERING OBSTRUCTION (the honest reason this cap is not inside
`lowreg_solve_two` yet): `L` is bound *inside* `lowreg_hfLo_data`'s conclusion,
because `refold_time` (`LowRegBgA1Refold.lean:324`) quantifies `∃ Z L` **after**
its state argument `u : timeL2 H³ T`.  So `L` is not in scope at the point where
`P` is chosen.  The smallest unblocking step is to hoist `Z, L` in `refold_time`
above the `(u : timeL2 …)` binder — they are the affine-growth constants of
`FHi`/`FLo`, which are built from `ρ, δ, hreal` only, so this should be a
re-ordering of the existential, not new mathematics.  Once hoisted,
`lowreg_solve_two` can take a target `η > 0`, cap `P ≤ η/L`, and report
`A ≤ η` — turning the margin into a caller-choosable smallness.

### Decls changed

`LowRegLiftSmall.lean` (263 → 362): +`lowregLiftHorizon'`,
+`lowregLiftHorizon'_le_one`, +`lowregLiftHorizon'_pos`, +`lift_aff_arith`,
+`lift_small_aff`.  Nothing removed.

`LowRegLiftHfLo.lean` (1264 → 1304): +`norm_congrLp` (136), +`norm_duhH3_le`
(153), +`refoldAffA1Hi_memLp` (814); `refoldAffA1Hi_data` (839) reproved from
it; `refoldAffA1_data` (648) and `refoldAffA1Hi_data` given `L^∞_t H³` WARNING
docstrings (both are now unused in the tree); `lowreg_hfLo_data` (1175) lost the
`B3` binder, its two `B3` hypotheses, the `Z + L*B3` a.e. conjunct and the
`∃ B1` conjunct.

`LowRegApplyTwo.lean` (547 → 553): `lowreg_apply_two` (87) lost the `B3` binder
and its two hypotheses, and now reports `∃ A Z` with the margin + primed horizon
instead of `∃ K` with `lowregLiftHorizon`; the proof drops `lift_small_of_bd`
and both `hbd*` steps for `lift_small_aff` on the two `hnorm*` bounds;
`IsRealizedTwo` (281) mirrors that change; `lowreg_solve_two` (424) lost its
`∀ {B3} …` layer.

### Lean notes from this brick

- `norm_congrLp` deliberately avoids `cases h`.  At a non-`rfl` exponent
  equality the `subst` route forces the `h = rfl` proof-irrelevance dance of
  `congrLp_self`; going through `Lp.norm_def` + `eLpNorm_congr_norm_ae` +
  `coeFn_compLpL` + `norm_tensorHsCongr` needs no case analysis at all and works
  uniformly.
- `L·‖duhH3 f‖ ≤ 2L‖f‖` is `linarith`-shaped once you feed it
  `mul_le_mul_of_nonneg_left norm_duhH3_le hL` **and** the explicit product
  `0 ≤ (1 - T)·(L‖f‖)`; without the second term the monomial `T·L·‖f‖` has
  nothing to cancel against.
- `lift_small_aff` still needs `(Y := …)` and `(A1 := …)` by name, for the same
  operator-space metavariable reason recorded for `lift_small_of_bd` below.

## Earlier status (pre-implementation, kept for the record)

- 2026-08-02: Hi-export brick LANDED (HfLo 1053 lines, GREEN, olean fresh):
  `lowreg_hfLo_data` now exports explicit `Z L`, `FHi` with continuity /
  core formula / affine bound, `refoldAffA1Hi` with `MemLp`, both toLp
  bounds `≤ L*‖duhH3 …‖ + √T*Z`, the a.e. Hi uniform bound `≤ Z + L*B3`,
  and the verbatim `hA1compat` square at `(aLo, aHi) = (1, 2)`.
- Next: brick 2a (`lowAffA2Hi` + square, per Risk 1 route) then 2b (the
  `lowreg_apply_two` assembly in this file's Lean sibling).
- `ricci_flow_unif_existence`: 0% (unstated).  This brick is wiring, not new
  mathematics; it closes the Lane-B/C junction modulo the A2-compat item.

## 2026-08-02, brick 5 — the ordering obstruction RESOLVED, GREEN

Brick 4 left one frontier: the margin `6A < 1 - c` could not be discharged
inside `lowreg_solve_two` because the affine growth constant `L` was bound
*inside* `lowreg_hfLo_data`, after the trajectory.  It is now hoisted all the
way up, and `lowreg_solve_two` discharges **both** smallness conditions itself.

### The hoist, lane by lane (no new mathematics — it was pure quantifier order)

| layer | before | after |
| --- | --- | --- |
| `LowRegBgC0Time` | `c0_time` (`∃ Z L` after `u`) | `c0_pack` (`:322`) — the private `c0_ext_pair` promoted verbatim; `c0_time` deleted |
| `LowRegBgC1Time` | `c1_bg_time` (`∃ Z L` after `u`) | `c1_bg_pack` (`:763`) — `c1_bg_time` minus `T`/`u`/time conjuncts, plus the u-free square; `c1_ext_pair` stays private (its core formulas use the private `c1Part`) |
| `LowRegBgA1Refold` | `refold_time` | `refold_aff` (`:331`) — the same lane sum, u-free, with the u-free square |
| `LowRegLiftHfLo` | `lowreg_hfLo_data` produced `∃ Z L FHi FLo` | `lowreg_hfLo_data` (`:1117`) **takes** them |
| `LowRegApplyTwo` | `lowreg_apply_two` produced `∃ A Z` + `∀ c` | `lowreg_apply_two` (`:171`) takes `Z, L, c` and the two smallness hypotheses |

The u-free halves **already existed** for the C0 lane (`c0_ext_pair`) and
essentially for the C1 lane (`c1_ext_pair`); nothing had to be extracted from a
`u`-dependent construction.  No wrapper was kept anywhere: every consumer chain
in this stack is single-consumer, so the old statements were deleted outright
rather than retained as shims.

### `IsRealizedTwo` is now the bare package (`:84`)

It lost the `∃ A Z, 0 ≤ A ∧ 0 ≤ Z ∧ ∀ {c} …` prefix, the `B2 B2Hi` parameters
and all six smallness hypotheses; those are hypotheses of `lowreg_apply_two`
now.  The package body itself never mentioned `c`, `A` or `Z`.  The `def` also
moved *above* `lowreg_apply_two`, which now states its conclusion as
`IsRealizedTwo …` instead of repeating the 55-line existential.

### Final shape of `lowreg_solve_two` (`:383`)

```
theorem lowreg_solve_two (hDim : finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) :
    ∃ (ρ δ : ℝ) (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3) (hreal' : …) (B2 : ℝ),
      0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ f, IsRealizedTwo g hρ hδ0 hδ_le hreal' hT hT1 f
```

The caller now picks **only** `c` (with `B2 ≤ c < 1`) and `T ≤ T₀`.  No margin
obligation, no `lowregLiftHorizon'` obligation, no `Z`, no `A`: the horizon
constant is folded into the reported `T₀ := min (lowregHorizon …)
(lowregLiftHorizon' c Z)`.  Note the quantifier order is now
`ρ, B2 → c → T₀ → T → f`: `T₀` genuinely depends on `c`, because the realization
radius does.

### How the margin is discharged

`c` is bound before the realization radius is chosen, so the third cap can use
it:

```
P := min (min ρ ρN) ((1 - c) / (6 * (L + 1)))
```

Then `‖f‖ = ‖gforce‖` (`norm_congrLp`) `≤ lowregStateRad … P / 4 ≤ P/4`
(`lowregStateRad_le_P` + the last conjunct of `lowreg_partial_sol_of_bounds`),
so `12L‖f‖ ≤ 3(LP)`, while `P·(6(L+1)) ≤ 1-c` gives `6(LP) + 6P ≤ 1-c` with
`P > 0` and `LP ≥ 0`.  `linarith` closes `6·(2L‖f‖) < 1 - c` from those four
facts — all monomials are linear in the atoms `L*P`, `P`, `c`, `L*‖f‖`.

`L = 0` is harmless (then the margin is `0 < 1-c`); the `+1` in `6(L+1)` is only
there to keep the quotient well-defined and positive.

### Decls added / removed

- added: `c0_pack`, `c1_bg_pack`, `refold_aff` (each replacing one deleted
  `*_time`); nothing else.
- removed: `c0_time`, `c1_bg_time`, `refold_time`, `refoldAffA1_data`,
  `refoldAffA1Hi_data` (the last two dead since brick 4, both carrying
  `L^∞_t H³` WARNING docstrings).
- `refoldAffA1_compat` (`LowRegLiftHfLo:790`) changed hypothesis: the u-free
  square instead of the time-level one.
- `hFHiCore` dropped from `lowreg_hfLo_data` / `lowreg_apply_two` (unused by
  both; still exported by `refold_aff`).

Net: the five files went 3953 → 3507 lines with no proof obligation added.

### Verification

Focused check + targeted `lake build` GREEN for all five modules, in dependency
order.  `lowreg_solve_two`, `lowreg_apply_two`, `refold_aff`, `c0_pack`,
`c1_bg_pack`, `lowreg_hfLo_data` all report exactly
`[propext, Classical.choice, Quot.sound]`.  `set_option
synthInstance.maxHeartbeats 1000000` is no longer present anywhere in the five
files (the old `refold_time` needed it; `refold_aff` does not).

### Consumer obligations of this lane, final

`lowreg_solve_two` has hypotheses `hDim, g` and nothing else.  Its consumer owes
two inequalities between reals the theorem itself reports: `B2 ≤ c`, `c < 1`,
and then `0 < T ≤ T₀`, `T ≤ 1`.  There is no remaining analytic input and no
remaining ordering residue in this lane.

## 2026-08-02, brick 6 — `IsRealizedTwo` carries the high Nemytskii identity, GREEN

Ruling No. 96 (Lane C, C3 at `aHi = 2`).  `IsRealizedTwo` gained **one**
conjunct, the last one:

```
fHi =ᵐ[timeMeasure T]
  fun t => liftHiN g hρ.le hδ0 hδ_le hreal' FHi
    (tensorHsCongr g 0 2 (2+2 = 4) (u.hiL2 t))
```

`liftHiN` is the frozen split `N v = N 0 + A₂(v) v + A₁(v) v` at an `H⁴` state
(`ShortTime/LowRegForceHi.lean`); `hiN_lowreg` there is the `H⁴` form of the
`N₂` slot of `lowreg_force_id`.  So the realized `(1,2)` package now says, in
addition to the six equations and the pins, that the high forcing **is** the
genuine Ricci–DeTurck nonlinearity evaluated along the lifted trajectory.

### Why a conjunct and not a corollary

`IsRealizedTwo` existentially binds `FHi`, `fHi` and `u`.  A corollary
consuming the package cannot *name* them in its conclusion; it would have to
re-open the existential and re-close it with a twelve-conjunct payload, i.e.
duplicate the whole definition.  `IsRealizedTwo` has no consumer outside this
file (checked by grep), so extending it is surgical, and `lowreg_solve_two`
transmits the new conjunct with no change to its statement or proof.

### The pin, and where each piece comes from

The new conjunct needs the `H⁴` field to be pinned to the low `H³` state.  The
chain, all a.e. in `timeMeasure T`:

1. `u.link` : `incl_{2 ≤ 2+2}(u.hiL2 t) = u.lo.toFun t`.
2. conjunct 11, `∀ t ∈ Icc 0 T` : `incl_{2 ≤ 2+1}(u.repr t) = u.lo.toFun t`
   (lifted to a.e. by `ae_restrict_mem measurableSet_Icc`, since
   `timeMeasure T = volume.restrict (Icc 0 T)`).
3. `tensorHsInclusion_trans_apply` + injectivity ⟹
   `incl_{2+1 ≤ 2+2}(u.hiL2 t) = u.repr t`.
4. conjunct 12 : `incl_{1+2 ≤ 2+1}(u.repr t) = maxRegDuhamelSolField 1 … t`.
5. `aeSetLift_coe_ae` (needs `hball`) + the `compLpL` coercion of `stateField`
   ⟹ `(state t).1 = congr_{1+2 = (1ℕ)+2}(maxRegDuhamelSolField 1 … t)`.

Both sides of the pin then reduce to `congr_{2+1 = 3}(u.repr t)` by
`tensorHsCongr_incl` (twice), one local transport-transitivity `have`, and
`tensorHsInclusion_refl_apply`.  The forcing identity itself is then three
lines: `hincl`, `hforce`, `hiN_lowreg`, injectivity of `incl_{1≤2}`.

### Decls changed

- `IsRealizedTwo` — one conjunct added (and its docstring).
- `lowreg_apply_two` — final `exact ⟨…, hpacket⟩` replaced by an `obtain` of
  the twelve conjuncts plus a `refine` leaving the new one as a goal; ~55 lines
  of pin plumbing added.  No new hypothesis: `hball`, `hforce`, `hDim`, `hRρ`,
  `hA2sq`, `hFComm`, `hFLo`, `hFLoCore`, `hNcont`, `hcoreN`, `hA2cont`,
  `hA2core` were all already parameters.
- `lowreg_solve_two` — unchanged; it reports the stronger package for free.
- new import: `ShortTime.LowRegForceHi` (a leaf until now; it sits below this
  file and above `LowRegRealizeTwo` / `LowRegLiftAffine`).

### Verification

Focused check GREEN; targeted `lake build
+DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegApplyTwo` GREEN
(9951 jobs), no warnings from this file or from `LowRegForceHi`.  No `sorry`,
no heartbeat option added.

### Lean note

Appending `∧ …` after a conjunct whose right-hand side ends in a `fun t => …`
lambda puts the `∧` **inside the lambda**.  The elaboration error appears as
`argument … has type tensorHs g 0 2 (1+2) but is expected to have type Prop`,
pointing at the *previous* conjunct.  Parenthesise the previous conjunct.

## 2026-08-03, brick 7 — `IsRealizedTwo` widened to carry the producer certificates, GREEN

The `a = 2` consumer (`ShortTime/LowRegAllOrderJet.lean`) could not build the
endpoint's `hForce` slot because the package exposed `FHi` as an
*unconstrained* existential: no continuity, no smooth-core formula, no
commuting square, and no low-scale radius.  `lowreg_apply_two` already had all
of that in scope and discarded it.  This brick re-exports it.

### New `∃`-binders (appended after `u`)

`FLo`, `R`, `hR : 0 < R`, `hreal` (the `R`-radius realization at
`smoothCcToTensorHs g (((1:ℕ):ℝ)+1)`).

### New conjuncts (appended, conjuncts 14–25; the first thirteen are byte-stable)

`R ≤ ρ`; `Continuous (lowRegN g g hR _ hreal)`; `Continuous (coreN g g _ hreal)`;
`Continuous (lowA2Lo …)`; the `lowA2Lo` smooth-core formula against
`refoldCore`; `Continuous (lowA2Hi …)`; `Continuous FHi`; `Continuous FLo`; the
`FLo` smooth-core formula against `c0CoreData`/`oneCore`; the second-order
square `hA2sq`; the first-order square `hFComm`; and
`∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R`.

The `δ < 1` proof the two nonlinearity continuities need is spelled
`lt_of_le_of_lt hδ_le (by norm_num : (1:ℝ)/3 < 1)` inside the `def`; consumers
may supply any `δ < 1` proof (proof irrelevance).

### The only new mathematics: the carrier state-ball conjunct

`hball` is stated for `stateField g hT hT1 f`; the consumer needs it for the
carrier `u.lo.toFun`.  The bridge is a five-step `calc` inside
`lowreg_apply_two`, using `hreprpin` (the `H³` representative pins to the
carrier), `hreprae` (the representative is the order-one Duhamel field a.e.),
`tensorHsInclusion_trans_apply`, `norm_incl_congr`
(`LowRegRealizeTwo.lean`, exactly the exponent-transport-under-inclusion norm
lemma this needed) and `hsf`.  `hstate`/`hsf`/`hctrans` were hoisted above the
final `refine` so the new conjunct can be discharged before it.

### `lowreg_solve_two`

Unchanged — every new item was already an argument it passes to
`lowreg_apply_two`.  It reports the stronger package for free.

### Verification

Focused check GREEN; targeted `build +…LowRegApplyTwo` GREEN, no warnings from
this file.  No `sorry`, no heartbeat option.

### Lean note (cost one wasted compile)

After editing a `def` that a downstream file destructures with `obtain`, the
downstream focused check reads the **stale `.olean`**.  The symptom is not
"unknown constant" but a *misaligned* `rcases` pattern: the extra patterns are
pushed onto the last visible conjunct and `rcases` calls `cases` on it,
reporting `Dependent elimination failed … at case Eq.refl` with the *unfolded*
`Filter.EventuallyEq` (`some 0 = μ {x | …}ᶜ`).  Run the targeted upstream
`build +Module` before checking the consumer.

## 2026-08-03, brick 9 — the forcing floor `√T‖fHi‖ ≤ Kf`, GREEN

Brick 8 left `hfloor` (`√T·‖u.deriv‖ ≤ 1/(2C)`) as the last visible obligation
of `lowreg_joint_of_re` and diagnosed it as a *smallness condition on `T`*, to
be folded into the horizon this file reports.  This brick does that fold.

### The chain, in one line

`u.deriv = ∂_t (Duhamel 0 fHi)`, so `‖u.deriv‖ ≤ 2‖fHi‖`; `fHi` solves
`fHi = nonautL2Map … fHi + liftForceHi g g T`, so a Neumann bound at the uniform
contraction gap `q` gives `q‖fHi‖ ≤ ‖liftForceHi‖ ≤ ‖staticForce g g 2‖·√T`;
hence `√T‖fHi‖ ≤ ‖SF‖·T/q`, and `T ≤ Kf·q/‖SF‖` makes it `≤ Kf`.

### What was added here

* `lowregFloorHorizon g c Kf := Kf(1-c)/(4(‖staticForce g g 2‖+1))` and
  `lowregFloorHorizon_pos`.  The `+1` in the denominator avoids a positivity
  side condition on the frozen forcing.
* `nonautL2Map_zero` (private) — the map fixes the origin.  Both arms need it:
  `maxRegHomogeneousSolField_norm_le` at `u₀ = 0` and
  `maximalRegularitySolField_norm_le` at `f = 0` give `‖·‖ ≤ 0`, and
  `a1L2Term_norm` at `f = 0` does the same for the first-order arm.  `timeOp` is
  a CLM so `map_zero` finishes.  Its canonical home is
  `TensorMaximalRegularity/NonautonomousL2.lean` beside `nonautL2_dist_le`; kept
  private here so that shared module stays untouched.
* `norm_fix_le` (private) — the **Neumann bound**.  From
  `nonautL2_dist_le` (the Lipschitz constant is
  `(C2)(1+T) + 2√(1+T)‖A1‖_{L²}`) plus `nonautL2Map_zero`, any solution of
  `x = N x + b` with the constant `≤ 1 - q` obeys `q‖x‖ ≤ ‖b‖`.
  The strict condition `… < 1` used to *build* the fixed point is useless here:
  it bounds nothing.
* `IsRealizedTwo` gains the parameter `(Kf : ℝ)` (appended after `f`) and the
  final conjunct `√T·‖fHi‖ ≤ Kf`.  All earlier binders/conjuncts byte-stable.
* `lowreg_apply_two`: `hmargin` strengthened to `6·(2L‖f‖) ≤ (1-c)/2` and one
  new hypothesis `hTfloor : T ≤ lowregFloorHorizon g c Kf`.
* `lowreg_solve_two`: gains `{Kf} (hKf : 0 < Kf)`, and `T₀` gains the third
  `min` factor `lowregFloorHorizon g c Kf`.

### Why the margin had to be halved (the real design point)

`lift_aff_arith` concludes only `κ < 1`, which gives **no** bound on `1/(1-κ)`,
so no Neumann bound.  The budget split inside it is
`κ ≤ c + (1-c)/4 [cT] + 3A + (1-c)/4 [3√T Z]`, i.e. `1-κ ≥ (1-c)/2 - 3A`.  With
only `6A < 1-c` that lower bound is not uniform.  With `6A ≤ (1-c)/2` it becomes
`1-κ ≥ (1-c)/4`, a `T`-free gap.  The new
`lift_aff_margin` (`LowRegLiftSmall.lean`, canonical home beside
`lift_aff_arith`) states exactly that; `hsmallHi` is now derived from it by
`linarith` and `lift_small_aff` is used only at the low rung.

The halved margin costs nothing: `lowreg_solve_two` already proved it, since
`‖f‖ ≤ P/4` and `P·6(L+1) ≤ 1-c` give `12L‖f‖ ≤ 3LP ≤ (1-c)/2` — the old proof
threw the factor 2 away in a `linarith`.

### Why `Kf` is a parameter and not `1/(4C)`

`C = (hs2_opBound_at_two hDim g).choose` is the *endpoint* fibre constant.
Hard-wiring it here would make the Lane-C realization package depend on the
joint-smoothness layer.  Taking the floor level as a parameter keeps this file
layer-neutral: the consumer names the level, the solver shrinks the horizon to
meet it.  `LowRegAllOrderJet.lowreg_joint_two` instantiates `Kf := 1/(4C)`.

### Lean notes

* `linarith`/`nlinarith` **without `only`** scan the whole local context.  In
  `lowreg_apply_two` (dozens of real-valued hypotheses) that turned an
  otherwise-cheap step into a `(deterministic) timeout at whnf` reported at the
  *declaration* line, not at the tactic.  Every arithmetic step in the new block
  uses `linarith only [...]`; the file went from failing at 78s to green at 37s.
  Prefer `linarith only` in any tactic block inside a wide-context theorem.
* `omit [Inst] in` must precede the **docstring**, exactly like `set_option … in`
  ("unexpected token 'omit'; expected 'lemma'" otherwise).
* `field_simp` on `2·(1/(4C)) = 1/(2C)` leaves `2 ^ 2 = 4`; follow it with
  `norm_num`.

### Verification

Focused checks GREEN for `LowRegLiftSmall`, `LowRegApplyTwo`, `LowRegAllOrderJet`;
targeted builds of all three GREEN ("Build completed successfully").  No new
`sorry`/`admit`/`axiom`, no heartbeat option.  Sorry census over the three files:
exactly one, the frontier `lowreg_forceJetMass`.

## 2026-08-04, option-(b) bricks B3 + B4 — the floor is DELETED, GREEN

Ruling No. 106 / `OPTIONB_FLOOR_PLAN.md` §6.  Brick 9 above (the forcing floor)
is **reverted by design**: the smallness it bought is relocated from the horizon
to the radius, and with it `‖staticForce g g 2‖` leaves this file entirely.

### What changed

* `IsRealizedTwo`'s parameter `Kf` is renamed `Rcap` and its last conjunct
  `Real.sqrt T * ‖fHi‖ ≤ Kf` is replaced by **`R ≤ Rcap`**.  Nothing else in the
  40-field existential moved; the a.e. state ball `∀ᵐ t, ‖u.lo.toFun t‖ ≤ R`
  immediately before it is untouched, and the pair of them is now the package's
  whole smallness content.
* Deleted outright: `lowregFloorHorizon`, `lowregFloorHorizon_pos`, and the two
  privates that existed only to feed them — `nonautL2Map_zero` and the Neumann
  bound `norm_fix_le` (75 lines).  `norm_liftForceHi_le`
  (`LowRegLiftNTerm.lean:259`) loses its only consumer and stays as unused API;
  it is now the ONLY place in the tree where `‖staticForce … 2‖` is even named,
  and it is named as a hypothesis variable, not inside a formula.
* `lowreg_apply_two`: `hTfloor` → `hRcap : R ≤ Rcap` (same slot position), the
  `hfloorHi` block deleted, `hRcap` forwarded verbatim into the existential.
* `lowreg_solve_two`: `{Kf} (hKf : 0 < Kf)` → `{Rcap} (hRcap : 0 < Rcap)`; the
  reported `T₀` loses its third `min` factor and is back to
  `min (lowregHorizon Ctop B0 B1 D ρout P) (lowregLiftHorizon' c Z)`.

### The `P`-cap arithmetic (the one identified failure mode — it composed)

```lean
set P : ℝ := min (min (min ρ ρN) ((1 - c) / (6 * (L + 1)))) Rcap
```

Every pre-existing constraint on `P` is an UPPER bound, so a fourth `min`
component costs nothing: each `hP*` fact gains one `le_trans` through the new
`hPle0 : P ≤ min (min ρ ρN) ((1-c)/(6(L+1)))`, and `hPpos` gains one `lt_min`
against `hRcap`.  The cap discharges as a two-step chain

```lean
hRP.trans hPcap : lowregStateRad Ctop B1 ρout P ≤ P ≤ Rcap
```

with `hRP := lowregStateRad_le_P hPpos.le` (already in scope) and
`hPcap := min_le_right _ _`.  No inequality had to be re-derived, no positivity
argument changed shape, and the `hmargin` chain (`‖f‖ ≤ P/4`, `P·6(L+1) ≤ 1-c`)
is untouched because it reads `P` only through `hPc`.  **The `(a)`-fallback
trigger's surviving limb never fired.**

### Cost

`τ₀` shrinks: `lowregHorizon`'s `(R/4/(2(D+1)))²` factor now sees the smaller
`R ≤ Rcap`.  It stays positive (`lowregHorizon_pos`, unchanged hypotheses) and
the horizon is monotone in the radius.  `D` is the ORDER-1 force number, already
class-bounded — so the horizon's individual-metric content strictly decreased.

### Lean notes

* `set x := e with h` keeps `x` defeq to `e`, so a three-deep `min` still takes
  `min_le_left`/`min_le_right` directly at each level; only the composition
  needed spelling out.
* Deleting a private theorem that a docstring still cites is a silent
  documentation rot — grep the prose for the name too, not just the code
  (`norm_fix_le` was cited in two docstrings, `hTfloor` in one).

### Verification

Targeted build of `LowRegApplyTwo` GREEN, [9984/9984], zero errors.  Zero
textual `sorry` in the file.  `#print axioms`: `lowreg_apply_two` and
`lowreg_solve_two` are both `[propext, Classical.choice, Quot.sound]` —
`sorryAx`-free, unchanged from before the edit.

Tooling: the run needed several restarts because the guarded build kept killing
lean on a single `FreePhysicalMemory < 0.4 GB` sample.  That threshold is BELOW
this machine's normal working point for the heavy modules
(`DeTurckRemainderLowBaseLip` completes in 239 s while sitting at 0.30 GB free);
`FreeVirtualMemory` — the real OOM predictor — never went below 5.2 GB in any
run.  Debouncing the physical limb and keeping the commit limb hard is what let
the build finish.

## 2026-08-04, brick S0-bis — `lowreg_solve_two` exports its order-one partner

The conclusion changed from `∃ f, IsRealizedTwo … f Rcap` to

```
∃ (f : timeL2 (tensorHs g 0 2 (1:ℝ)) T)
  (fLo : timeL2 (tensorHs g 0 2 ((1:ℕ):ℝ)) T),
  IsRealizedTwo … f Rcap ∧
  (∀ᵐ t ∂timeMeasure T, f t = tensorHsCongr g 0 2 (‹((1:ℕ):ℝ) = (1:ℝ)›) (fLo t)) ∧
  IsLowSolve g hT hT1 fLo
```

Both new components cost **nothing**: `fLo` is the `gforce` that
`lowreg_partial_sol_of_bounds` already produces at `:711`, the transport is the
`hfae` that was already proved at `:725` (`f` is defined as
`(tensorHsCongrL …).compLpL … gforce`), and `IsLowSolve` is
`isLowSolve_of_sol` applied to the same arguments and the same two results
(`hgf`, `hforce`).  The theorem stays axiom-clean.

Proof-shape note: the old `refine ⟨f, ?_⟩` right after `set f := …` had to move
to the end, because `hfae` is proved *after* it.  The tail is now
`refine ⟨f, gforce, lowreg_apply_two …, hfae, ?_⟩` followed by the
`isLowSolve_of_sol` application — the intermediate `have`s elaborate unchanged
since none of them depends on the goal.

Why: everything above this file that wants an *energy* estimate on the
trajectory has to work at the scale where the contraction lives.  The `H²` lift
forgets the fixed-point equation and the nonlinearity's constants.  See
`ShortTime/LowRegAllOrderJet.md` (2026-08-04); `lowreg_joint_two`'s statement was
NOT changed, so this widening is invisible above the chain.

## J0a (2026-08-04): the fibre threshold is a parameter of `lowreg_solve_two`

**Status: DONE, sorry-free.**  `lowreg_solve_two` gained
`{thr : ℝ} (hthr : 0 < thr) (hthr3 : thr ≤ 1/3)`.  The three `have`s that used to
pin the threshold at `deTurckArmContractionThreshold'' (finrank ℝ E)` are now
`hδ0 := hthr.le`, `hδ_le := hthr3`, `hδ := lt_of_le_of_lt hthr3 (by norm_num)`,
and `realize_at_thr` is replaced by `realize_at_delta … hthr`.  The CONCLUSION is
unchanged — `δ` stays existentially bound, and is now instantiated to `thr`.

Name note: `thr`, not `δ★`/`δ*` — ASCII, no shadowing of the existential `δ` in
the conclusion.

Why this was the only real pin.  Everything else in the chain was already
`δ`-generic and needed no edit: `refold_aff`, `radialA2_lip`, `lowA2_small`,
`lowRegN_outer`, `lowreg_bounds_exist` all bind `{δ}` with `0 ≤ δ ≤ 1/3` (or
`δ < 1`).  The single hard-coded witness lived in `realize_at_thr`'s `(θ/C, θ)`.
Confirmed by grep before editing, and confirmed by the check afterwards: three
type ascriptions (`hrealcap`, `hrealL`, `hreal'`) were the entire body churn.

One call site (`LowRegAllOrderJet.lean`, `lowreg_joint_solve`-side), which supplies
`thr := deTurckArmContractionThreshold'' (finrank ℝ E)` and keeps behaviour
identical.  When J0b lands, that call site is where `δ★` gets chosen from `κ`
instead — no producer change will be needed.

`isLowSolve_of_sol` call updated: one fewer metric argument, three more
certificates (`hδ0`, `hδ_le`, `hcoreN`).  `hcoreN` — already in context from
`lowRegN_outer` — closes the `hcore` slot by DEFINITIONAL PROOF IRRELEVANCE
(`realizeOfLE g le_rfl hrealR` vs `hrealR`); a bare `exact` suffices.
Verification: focused check green.

## 2026-08-05 — exact-witness producer

The heavy solve proof now lives in `lowreg_solve_two_at`.  Unlike the former
existential result, it exposes the supplied threshold `thr` literally and
returns the exact `Ctop,B0,B1,D,ρout,P` used to construct an `IsLowSolveAt`,
including `lowregStateRad ... ≤ Rcap`.  The old `lowreg_solve_two` statement is
preserved as a thin projection through `IsLowSolveAt.toIsLowSolve`.

Focused verification passed without warnings.  The targeted module refresh
also passed; it was long because the exported declaration sits above the full
short-time dependency cone.  No analytic estimate changed.  The endpoint
theorems remain 0%; this is witness-retention machinery for GAP-ADAPTH.

## 2026-08-05 - strict contraction package

`lowreg_solve_open` is now the proof-bearing producer.  It uses the
radius-flexible second-order estimate and returns the actual coefficient floor
`B2` together with `0 <= B2` and the non-vacuity certificate `B2 < 1`.
Therefore every requested contraction level in `[B2,1)` has a positive solve
horizon.  The older `lowreg_solve_two_at` remains as a compatibility projection
that forgets only the strict inequality.

Focused verification and the direct module refresh passed warning-free.  This
closes the per-metric contraction-admissibility gap; it does not yet provide one
coefficient floor or one horizon uniformly over a metric class.
