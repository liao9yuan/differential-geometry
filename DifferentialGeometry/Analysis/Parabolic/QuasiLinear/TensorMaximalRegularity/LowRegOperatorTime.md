# LowRegOperatorTime

## Role

Lane B of the `(N)` `ricci_flow_unif_existence` endgame: the *time-level*
operator-valued fields of the low-base Ricci--DeTurck action along the
order-one (`a = 1`) solution produced by `lowreg_partial_sol`.  Built on the
verified template `ShortTime/LowRegPrincipalTime.lean`
(`lowRegStateL2` / `lowRegState_ae_le` / `lowRegA2Time` / `lowRegA2_data`).

Consumers: `nonautL2_lift` (through Lane C's `ShortTime/LowRegLiftTwo.lean`)
needs a strongly measurable, time-`L²` first-order family `A1` and a strongly
measurable, uniformly *small* complete second-order family `A2`.

## What is in the file (all sorry-free)

* `lowRegA1Time` — `t ↦ lowA1Hi g … (solution field t)`, the genuine first-order
  low-base action as an `H3 →L H2` field.  The state fed in is the **full `H3`
  field**, not its `H2` inclusion, because `lowA1Hi` is an `H3`-state
  coefficient.  The exponent mismatch `(1 : ℝ) + 2` vs `(3 : ℝ)` is bridged by
  `tensorHsCongr` (`SobolevScale/ExponentCongr.lean`), reused rather than
  redefined.
* `lowRegA1_memLp` — strong measurability, the pointwise operator bound, and
  `MemLp … 2 (timeMeasure T)`.  The `MemLp` half is `memLp_clm_affine`
  (`NonautonomousL2Cross.lean`) applied to the solution's own `L²_t H3` field;
  this is exactly where the **affine** (not degree-six) growth is consumed.
* `lowRegA2Total` — `lowRegA2Time + lowA2Hi (state t)`, i.e. principal plus the
  extra second-order arm.  This is the family downstream must consume;
  `lowRegA2Time` alone is only the principal part.
* `a2Hi_total_le` (private) — a continuous completed coefficient map that reads
  off the smooth core and is bounded there is bounded everywhere (density).
* `lowA2_small` (was `lowA2Hi_small`) — `∃ ρ C`, on which **both** `lowA2Hi`
  and `lowA2Lo` are continuous, both satisfy `‖… v‖ ≤ C * ρ` for **every**
  state `v` (the cutoff is inside the map), and they satisfy the `∀ v`
  commuting inclusion square.  Sourced from `c2_h2_small` via `radialA2_pair`,
  continuity and square from `radialA2_lip`.
* `a2Lo_total_le` (private) — the `H3 → H1` sibling of `a2Hi_total_le`.
* `lowRegA2Total_data` — strong measurability plus the uniform a.e. bound
  `‖lowRegA2Total … t‖ ≤ C * ρ`, on one radius that also controls the state
  ball of `lowRegA2_data`.

### Added for the two Lane-B gaps the Lane-C realize pass located

Gap (i), the **completed** first-order commuting square:

* `coreLip`, `highCorePair` (private) — the smooth-core Lipschitz plumbing, the
  `H3`-state analogue of `subtype_norm_lip` / `a2HiCore_pair`.
* `lowA1_lip` — the missing `radialA1_lip`: Lipschitzness of the *completed*
  `lowA1Hi` / `lowA1Lo`, their smooth-core read-offs, and the `∀ v` square
  `incl₁₂ ∘ lowA1Hi v = lowA1Lo v ∘ incl₂₃`.  Route: `dense_lipschitz` plus
  `DenseRange.induction_on` against `isClosed_eq`, with `radialA1_pair`'s
  smooth-core square as the core case — exactly the `radialA2_lip` idiom.
* `lowA1_square` — the `∀ v` square alone, in the shape `liftA1Two` needs.
* `lowRegA1TimeLo`, `lowRegA1_square` — the low first-order operator field
  along the order-one solution and its square, holding at **every** `t`.
* `lowRegA1Lo_memLp` — the `hA1Lo : MemLp A1Lo 2` input, the mirror of
  `lowRegA1_memLp`.

Gap (ii), the low sibling of the principal second-order family:

* `lowRegA2TimeLo` — `lowRegPrincipalLo` along the *same* ball lift that
  `lowRegA2Time` uses, post-composed with `tensorHsCongrL` to normalize the
  bottom exponent from `((1 : ℕ) : ℝ)` to `(1 : ℝ)`.
* `lowRegA2Lo_data` — strong measurability, the linear bound `C * R`, and the
  `∀ t` square with `lowRegA2Time`.
* `lowRegA2TotalLo`, `lowRegA2TotalLo_data` — the complete low family
  (`lowRegA2TimeLo + lowA2Lo (state t)`), its measurability and `C * ρ` bound,
  and the **total** `∀ t` square with `lowRegA2Total`.

## Hypothesis parameters deliberately deferred (Lane A owes these)

`lowRegA1_memLp` takes two hypotheses about the **completed** first-order
coefficient map `lowA1Hi g hρ hδ0 hδ_le hreal`:

* `hcont : Continuous (lowA1Hi …)`
* `hlin  : ∀ v, ‖lowA1Hi … v‖ ≤ Φ * (1 + ‖v‖)` (affine in the `H3` state norm)

Both are consequences of one Lipschitz estimate `LipschitzWith C (lowA1Hi …)`:
continuity is `LipschitzWith.continuous`, and the affine bound is the triangle
inequality at the zero state with `Φ := max ‖lowA1Hi … 0‖ C`.  That estimate is
the A2/A3/A4 output of Lane A; `DeTurckRemainderLowBaseTimeA1.md` records the
same fact ("the total A1 state-map continuity and measurability theorem is
still pending the final geometric pair estimate").

Why they could not be discharged here: the only one-state A1 bound in the tree
is `radialA1_pair` / `remainder_low_pair`, whose envelope is
`C√(K (1 + J3 T)^6)` — degree six.  With that envelope `memLp_clm_affine` does
not apply and the `MemLp` conclusion is **false**, so hard-wiring it would have
produced a wrong theorem.  The A2 side needed no such hypothesis: `radialA2_lip`
(Lipschitz) and `radialA2_pair` (smallness) both exist, so `lowA2_small` is
unconditional.

`lowA1_lip` / `lowA1_square` take the same debt in its sharpest form: two
smooth-core Lipschitz estimates

* `hHiPair : ‖(lowCoreData … T).a1Hi − (lowCoreData … U).a1Hi‖ ≤ C ‖T − U‖_{H3}`
* `hLoPair : ‖(lowCoreData … T).a1Lo − (lowCoreData … U).a1Lo‖ ≤ C ‖T − U‖_{H3}`

i.e. the first-order sibling of `a2_pair_lip` (`DeTurckRemainderLowBaseC2Lip`).
**UPDATE (2026-07-30): `hHiPair` is unsatisfiable, so `lowA1_lip`,
`lowA1_square` and `lowRegA1_square` are vacuous.**  `a1Hi` is `H³ → H²`, so its
coefficient is read at the `H²` jet, which costs the *third* jet of the state;
`lowCoreData`'s cutoff `lowRadial` bounds only the spectral `H²` size and leaves
the third jet free.  The coefficient difference contains the sharp cross term
`(P(g_T⁻¹) - P(g_U⁻¹)) ∗ ∇T` — the `B1 · A · D2` slot of `c1Diff_tame` — and the
family `T` oscillatory with `‖T‖_{H²} ≤ ρ/2`, `‖T‖_{H³} = A → ∞`, `U = T + εV`
with `V` a fixed low-frequency bump gives left side `≍ εA` against right side
`≍ Cε`.  No uniform `C` exists.  `hLoPair` is by contrast plausibly true
(`a1Lo` reads its coefficient at the `H¹` jet, which the `H²` ball does control)
but is not derivable from the tree's lossy `c0Diff_tame` / `c1Diff_tame`.

The honest estimate now exists: `c1_pair_lip` / `a1_pair_lip` in
`Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderLowBaseA1Pair.lean`
(modulus `K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N)`; see that file's `.md` for
the two items still needed to make the square instantiable — an `A₄`/`D₄`-free
sharpening, and a dense-extension lemma for locally Lipschitz core maps, since
the conclusion can then only be `Continuous`, never `LipschitzWith`).

The original (now superseded) reasoning was:

This is genuinely necessary and **not** a packaging artefact: `lowA1Hi` and
`lowA1Lo` are `Dense.extend`s, and a `Dense.extend` of a discontinuous core map
carries no information at all (it is a `limUnder` of a non-convergent filter),
so no dense-extension argument can produce the `∀ v` square without continuity
of the core maps.  The square is therefore conditional on exactly one estimate
and nothing else.  Note the modulus is taken against the **`H3`** size of the
state difference (one order weaker than the `H2` modulus `a2_pair_lip`
achieves), because `lowA1Hi`/`lowA1Lo` are completed over the `H3` smooth core;
`a1_diff` reduces it further to a two-jet estimate on the coefficient
difference `C0 − C0'`, `C1 − C1'`, i.e. to a missing `c1_pair_lip` alongside
the existing `c2_pair_lip`.  `DeTurckRemainderLowBaseC1Lip.lean` is the
in-flight file for that estimate.

## Lessons

* **Cross-module private operator abbreviations block instance search.**
  `DeTurckRemainderLowBaseTime.lean` declares `lowA1Hi`/`lowA2Hi` with codomains
  `private abbrev lowA1HiOp` / `lowA2HiOp`.  From another module, `‖lowA1Hi … v‖`,
  `Continuous.norm`, `norm_nonneg`, `dist_eq_norm` all fail with
  `failed to synthesize SeminormedAddGroup (lowA2HiOp✝ g)` (typeclass heartbeat
  timeout).  `set_option backward.isDefEq.respectTransparency false` does **not**
  help, and a plain `(e : T)` type ascription does **not** help either — Lean
  keeps the inferred type.  What works is `show T from e`, which really retypes.
  The proper root fix is to drop `private` from those four operator abbreviations
  in `DeTurckRemainderLowBaseTime.lean` (a public `def` should not have a private
  abbreviation in its signature); until then every downstream file must use
  `show … from`.
* Continuous-linear-map norms live on `ContinuousLinearMap.hasOpNorm`, which does
  **not** unify with `SeminormedAddGroup.toNorm ?inst` when the instance is a
  metavariable.  Use `ContinuousLinearMap.opNorm_add_le` instead of `norm_add_le`,
  and `Continuous.comp (continuous_norm (E := <explicit CLM type>)) hF` instead of
  `hF.norm`.
* **Radius matching by nesting, not by `min`.**  `radialA2_pair` fixes its own
  radius, so it cannot simply be intersected with `radialA2_lip`'s.  Run
  `radialA2_lip` at `ρ₀` first, then run `radialA2_pair` *inside* the radius it
  returns; the result lands at a single radius where both hold.  The same trick
  chains `principalTime_data`'s radius in `lowRegA2Total_data` (`min ρ₀ ρP` first,
  then the A2 chain inside it).  Proof irrelevance makes the three different
  `hreal'` proof terms interchangeable, so no transport lemma is needed.
* `add_le_add_right h _` in this Mathlib adds on the **left**; use
  `add_le_add h le_rfl` when the varying summand is on the left.
* Reuse note: `tensorHsCongr` / `tensorHsCongrL`
  (`Analysis/Spectral/Tensor/SobolevScale/ExponentCongr.lean`, added by a
  concurrent lane) is the canonical `(1 : ℝ) + 2 = 3` scale transport.  A local
  `orderOneH3Iso` was written first and then deleted in favour of it.
* **The bottom exponent of the principal pair is spelled `((1 : ℕ) : ℝ)`.**
  `PrincipalLowRegPair.lean` writes `rank2H1 g := tensorHs g 0 2 ((1 : ℕ) : ℝ)`,
  and `((1 : ℕ) : ℝ) = (1 : ℝ)` is **not** `rfl` (checked).  Everything on the
  `lowA2Lo` / `lowreg_lift_two` side lives at `(1 : ℝ)`, so the low principal
  arm must be transported.  Codomain transport needed a new
  `norm_congr_comp` (`‖congrL ∘ L‖ = ‖L‖`) next to the existing domain-side
  `opNorm_comp_congr_le` in `ExponentCongr.lean`, and the square is moved by
  `tensorHsCongrL_incl` with `hbd := rfl` plus `tensorHsCongrL_refl` /
  `comp_id`.
* **The `show … from` lesson bites harder two abbreviations deep.**  Instance
  search for `SeminormedAddCommGroup (LowBaseTimeInternal.A1HiOp g)` times out
  (`A1HiOp → lowA1HiOp → CLM type`).  Binding the core maps to local `let`s at
  the *unfolded* operator types (`a1Op`, `a1LoOp`) fixes every downstream
  `LipschitzWith` / `Continuous` / `Dense.extend_eq` goal at once, and then the
  `change Dense.extend …` steps that the A2 file needs become unnecessary —
  plain `exact` closes them by delta.
* **`Ring.inverse` continuity beats a Lipschitz estimate.**  The low principal
  time family only needs *continuity* of `lowRegPrincipalLo` for strong
  measurability.  There is no `invPerturbH1_lip` in the tree and copying the
  100-line `invPerturbH2_lip` would have been the obvious move; instead, on the
  ball `1 + perturbH1 g T` is a unit and `NormedRing.inverse_continuousAt` gives
  continuity for free.  New lemma `principalLo_cont` in `PrincipalLowRegPair`.
  Trap: writing `have hu : IsUnit (1 + perturbH1 g T)` picks
  `ContinuousLinearMap.monoidWithZero`, which does **not** unify with
  `NormedRing.toRing.toMonoidWithZero` that `inverse_continuousAt` wants.  Build
  the unit with `Units.oneSub … : Rˣ` (stated in the `NormedRing` context)
  and rewrite by `Units.val_oneSub`, `sub_neg_eq_add`.  Also give
  `ContinuousAt.comp` its `(f := …)` explicitly: higher-order unification
  happily mis-splits `fun S => 1 + perturbH1 g S` as `HAdd.hAdd 1 ∘ perturbH1 g`.

## Placement caveat

The file sits in `Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/` but
imports `Geometry/Flow/RicciFlow/ShortTime/LowRegPrincipalTime.lean`, which is a
strictly higher layer (it transitively imports this directory).  There is no
Lean import cycle today, but the natural home is
`Geometry/Flow/RicciFlow/ShortTime/` next to `LowRegPrincipalTime.lean` and
`LowRegLiftTwo.lean`; moving it there before anything in
`TensorMaximalRegularity/` needs to import it would avoid a real cycle later.

## Verification

Focused check, a real targeted module build (also of the downstream
`ShortTime/LowRegRealizeTwo`), and `#print axioms` on all thirteen new
declarations all passed; the file contains no `sorry` and everything is
axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

## Project accounting

* `ricci_flow_unif_existence` (the `(N)` endpoint, `ExtendViaUniqueness.lean:80`):
  still one `sorry`, **0% done**.
* Its dedicated machinery: the Lane B time-realization bricks are complete
  (`lowRegA1Time`, `lowRegA1_memLp`, `lowRegA2Total`, `lowA2_small`,
  `lowRegA2Total_data`) and now so are both adjacent-scale **compatibility
  squares** that `lowreg_lift_two` consumes (`lowRegA1_square`,
  `lowRegA2TotalLo_data`).  The A2 half of the `nonautL2_lift` input bundle —
  measurability, smallness, and the square, on **one** radius — is
  unconditional.  The A1 half remains conditional on the Lane A estimates
  (`hcont`/`hlin` for `MemLp`, `hHiPair`/`hLoPair` for the square); those are
  now the same single missing object, a first-order `a2_pair_lip`.
* Of the three Lane-B gaps that `ShortTime/LowRegRealizeTwo.md` recorded,
  (1) the completed `a1` square and (2) the low principal `a2` family + square
  are **closed** here.  (3) horizon smallness `hsmallHi`/`hsmallLo` is still
  open and is now the only *packaging* obstruction left in Lane B.
* Lane B is roughly one of the fourteen bricks on the critical path
  A1a → A1b → A2 → A3 → A4 → B1 → C0 → C1 → C2 → C3 → D1 → D2 → D3 → F1, with the
  independent uniformity lane E1–E3 running in parallel; the two genuinely open
  pieces nearest to this file are Lane A's `selfLow_pair_h2` (the H2 order-zero
  pair estimate) and Lane C's `lowreg_force_id`.
