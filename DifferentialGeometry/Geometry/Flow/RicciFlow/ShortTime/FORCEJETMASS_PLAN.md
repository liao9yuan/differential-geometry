# `lowreg_forceJetMass` — attack plan for front 2's single analytic frontier

Target: `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegAllOrderJet.lean:421`
(the file's one `sorry`, at `:450`).  Parent plan: `LOWREG_BOOTSTRAP_PLAN.md`
(brick B1); campaign anchor: `UNIF_EXISTENCE_PLAN2.md` No. 98.

Written 2026-08-03 by the front-2 frontier recon pass.  **No Lean edited, no file
claimed, no Lake process run.**

---

## 0. Headline

`LOWREG_BOOTSTRAP_PLAN.md` §6 and §9 say the supercritical template rests on **two
honest `sorry`s**, POSIT (A) `deTurckForcing_solCoeff_jetSpectralMass` and POSIT (B)
`deTurckSobolevNHa2_jetSpectralMass_preserving`.  **That is stale.**  Both were
discharged (commits `358687842`, `b369c07f0`, `272498f86`); `grep -rnw sorry` over
`Analysis/Spectral/Intrinsic/HeatSemigroup/` and `.../DeTurck/` returns **zero code
`sorry`s** — only stale prose in `ForcingCoordinateTimeRegularity.lean:38,46,80`
still calling them "Honest `sorry`".

So the question "how did the supercritical template close the self-reference?" has a
concrete answer in the tree, and — the decisive finding of this recon — **three of its
four stages are already order-generic**, one of them only because `ha_super` is a
*vestigial* hypothesis there.  §8.1's verdict ("`a = 2` is a band with no supporting
estimates at all") is therefore too pessimistic by a wide margin.

---

## 1. The leaf, verbatim

`lowreg_forceJetMass` (`:421`) takes the low-lane fixed point

```lean
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ hδ0 hδ_le hreal' FHi
        (tensorHsCongr … (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs … ((2 : ℝ) + 2)) fHi t)))
```

and must produce, on the **full unshrunk** `T`:

1. `R₀ > 0` with `hball_full`: `∀ t ∈ Set.Icc 0 T`, every `S : SmoothCcTensor g 0 2`
   whose `toL2` is the carrier at `t` has `‖smoothCcToTensorHs g ((2:ℝ)+2) S‖ ≤ R₀`;
2. `fc : TensorEigenIdx g 0 2 → ℝ → ℝ` with `JetSpectralMassControl g fc T` and
   `∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i`.

`JetSpectralMassControl` (`HeatSemigroup/SmoothCoordinateJetPreservation.lean:77`) is
exactly the two-field conjunction `(∀ i, ContDiff ℝ ∞ (φ i)) ∧ (all-`(j,τ)` summable
pointwise majorant on `Icc 0 T`)` — i.e. **precisely** the hypothesis pair
`hf_smooth` / `hforcing_mass` of the per-mode engine
`perModeConv_allOrder_timeDeriv_spectralMass_le`
(`HeatSemigroup/MaxRegInteriorTimeSmoothing.lean:196`).  Nothing more is asked of the
forcing package: the solution side is already closed and order-generic.

`liftHiN` (`ShortTime/LowRegForceHi.lean:132`) is the frozen split

```lean
  staticForce g g 2
    + lowA2Hi g … (incl₂₄ v) (radialCLM g … ρ (incl₂₄ v) v)
    + FHi (incl₃₄ v) (lowRadialH3 g ρ (incl₃₄ v))
```

— a constant, plus two pairings whose **coefficient slot** is a lower view of the same
state and whose **state slot** is a nonlinear retraction of it (so: neither bilinear nor
affine in `v`).  `lowA2Hi`/`lowA2Lo` are `Dense.extend`-completed and are `LipschitzWith C`
on a shrunken radius (`radialA2_lip`, `DeTurckRemainderLowBaseTimeA2.lean:370`, downgraded
to `Continuous` by `lowA2_small`, `LowRegOperatorTime.lean:668`); `FHi` is an unconstrained
existential inside `IsRealizedTwo` carrying only `Continuous FHi` and `‖FHi x‖ ≤ Z + L‖x‖`
(`refold_aff`, `LowRegBgA1Refold.lean:331`).  **There is no Fréchet-differentiability-in-state
lemma anywhere in the tree** for any of `lowA2Hi`, `lowA2Lo`, `FHi`, `FLo`, `lowRegN`,
`liftHiN`, `refoldBaseN` (exhaustive grep for `HasFDerivAt|ContDiff|DifferentiableAt|fderiv|
IsBoundedBilinearMap` co-occurring with those names: zero hits).  So `∂ₜᵏ(liftHiN ∘ u)` by
chain rule is dead on arrival.  §4 shows it is also unnecessary.

---

## 2. How the supercritical template closes the self-reference (THE answer)

Five stages, none of which differentiates the nonlinearity in the state.

**(S1) An a-priori ALL-σ *spatial* spectral-mass bound on the solution, by Galerkin.**
`deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm`
(`HeatSemigroup/GalerkinLimitUniformMass.lean:1125`) gives, for **every real `σ`**, a
`t`-uniform bound on `∑' i, w_i^σ · (perModeConv λᵢ (timeModeCoeff gforce i) t)²`.
Proof = finite-dimensional Galerkin ODE + per-scale energy closure + Grönwall + Fatou.
No time-derivatives anywhere; no Fréchet derivative of the nonlinearity.

**(S2) All-σ spatial mass ⟹ a genuinely SMOOTH section.**
`exists_smoothCcTensor_of_allOrder_spectralMass_local`
(`HeatSemigroup/ForcingFiniteOrderTimeRegularity.lean:513`, and a twin at
`DeTurckRemainderPathTimeJet.lean:38`) turns an all-order spectral-mass majorant into
an honest `S : SmoothCcTensor g₀ 0 2` with the prescribed coefficients.  **Completely
order-generic and metric-generic** — no `a`, no `ha_super`.

**(S3) On a smooth path the nonlinearity's time-jets come from the CHART chain rule,
not from state-derivatives.**  `deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection`
(`ForcingFiniteOrderTimeRegularity.lean:4980`) takes a smooth path
`F : ℝ → SmoothCcTensor g₀ 0 2`, a `C^k` coordinate family `φ` pinned to it, and
finite-order mass, and returns `C^k` coordinates `ψ` for `deTurckSmoothRemainder g₀ g_bg (F t)`
with all jets `j ≤ k` realized by explicit smooth sections `Rjet j t`.  Its engine is
the `anisoOn_realize_*` chain (`:3170`–`:3519`: Gram det/adjugate/inverse, Christoffel,
DeTurck vector field, Ricci, DeTurck RHS) — joint `C^k`-in-`(t,x)` on chart components.
**`(a : ℕ)` and `ha_super` do not occur anywhere in its proof body** (`grep -n ha_super`
gives hits at `:4982` then nothing until `:5118`; the `set_option linter.unusedVariables
false in` above it is the tell).  The same holds for **three more** members of the layer:
its wrapper `deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` (`:5116`, `ha_super`
used only to pass down), and the all-order twins
`deTurckRemainder_path_timeJet_section` (`SmoothCoordinateJetPreservation.lean:132`) and
`deTurckSmoothN_path_coeff_jetSpectralMass` (`:215`) — `grep -n ha_super` on that file
shows `:134`, then `:217`, then `:247` (the pass-down), and nothing inside either body.
**All four are order-generic today.**

**(S4) Finite order ⟹ all orders by an a.e.-agreement DIAGONAL, not by C^∞ of anything.**
The finite-order layer is genuinely needed and is not a stylistic choice: the all-order
producer (`SmoothCoordinateJetPreservation.lean:215`) demands the *input* coordinates
already be `C^∞` with all-order mass, which is the circularity itself.
`deTurckForcing_finiteOrderSmoothDriver` (`ForcingFiniteOrderTimeRegularity.lean:5409`)
breaks it by an **induction on `k`** (`:5468`ff): base `k = 0` needs only continuity of the
solution coordinates (from (S1) via `deTurckForcing_solCoeff_continuous_smallTimeBase`,
`:41`); step `k → k+1` feeds the previous rung's forcing regularity through the per-mode
convolution (S5) to get the solution at `k+1`, then (S3) to get the forcing at `k+1`.
`maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMass`
(`ForcingCoordinateTimeRegularity.lean:119`) then notes all `F k` agree a.e. hence `EqOn`
on `Icc` (continuity + `Measure.eqOn_of_ae_eq`), concludes `F 0` is `ContDiffOn ℝ ∞`, and
globally extends by `contDiffOn_Icc_scalar_globalExtend`.  Pure bookkeeping.

**(S5) Per-mode ODE recursion trades 2 spatial orders per time-derivative.**
`perModeConv_iteratedDeriv_succ_finiteOrder` (`:284`) /
`perModeConv_allOrder_timeDeriv_spectralMass_le` (`MaxRegInteriorTimeSmoothing.lean:196`),
both order-generic and already sorry-free.

**Where `ha_super` is REAL.**  Only two places: (i) the *identification* of the completed
Nemytskii with its smooth core on the realizability ball
(`deTurckSobolevNHa2_eq_smoothN`, `deTurckSobolevNHa2_exists_of_super`, used at
`:5367`,`:5374`,`:5399`); (ii) the **per-scale energy closure**
`deTurckGalerkin_forcing_dissipation_perScaleSymm`
(`GalerkinParabolicEnergyDeTurck.lean:1390`, gated `4·finrank+10 ≤ a`, internally
weakening to `2·finrank+10 ≤ a` at `:1407` for the all-orders tame splitting).
Note the closure is **`U`-generic and ball-free** — confinement is internal to the
retracted `deTurckSobolevNHa2Symm`.  The Grönwall engine it feeds,
`galerkin_energy_uniform_bound_perScale` (`GalerkinParabolicEnergy.lean:220`), has
**no metric, no `a`, no nonlinearity at all**: `σ₀ : ℝ` is free.

---

## 3. What survives at `a = 2`

**HAVE (already in the import cone — `LowRegAllOrderJet.lean` imports
`MaxRegSolutionJointlySmooth`, which imports `ForcingTimeBootstrap` →
`ForcingCoordinateTimeRegularity` → `ForcingFiniteOrderTimeRegularity` +
`GalerkinLimitUniformMass`.  No import churn is needed.)**

| item | file:line | order-generic? |
|---|---|---|
| `perModeConv_allOrder_timeDeriv_spectralMass_le` | `MaxRegInteriorTimeSmoothing.lean:196` | yes |
| `galerkin_energy_uniform_bound_perScale` | `GalerkinParabolicEnergy.lean:220` | yes (`σ₀ : ℝ` free) |
| `exists_smoothCcTensor_of_allOrder_spectralMass_local` | `ForcingFiniteOrderTimeRegularity.lean:513` | yes (`private`) |
| `deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection` | `:4980` | **yes — `ha_super` vestigial** |
| `deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` | `:5116` | **yes — `ha_super` vestigial** |
| `deTurckSmoothN`, `deTurckSmoothRemainder` | `DeTurck/SobolevNonlinearityExistence.lean:109` | yes — `a` sets only the output *type*; coefficients are `a`-independent (`deTurckSmoothN_coeff`, `:131`) |
| the a=2 Nemytskii↔smooth-core identity **along the trajectory** | `LowRegAllOrderJet.lean:148` (`coord_eq_smoothN`), proved | — |
| `lowregNsec g S = deTurckSmoothRemainder g g (symmS g S)` | `LowRegAllOrderJet.lean:119` | — |
| the low lane's **global** realizability (`hreal'`, `δ ≤ 1/3`, all `‖·‖_{H²} ≤ ρ`) | leaf hypotheses | full `[0,T]`, no shrink |
| `√T‖fHi‖ ≤ Kf`, `hforce_id`, continuity certificates | widened `IsRealizedTwo` (No. 98) | full `[0,T]` |

**ABSENT.**
* No state-Fréchet derivative of `lowA2Hi` / `FHi` anywhere (and `FHi` is an
  unconstrained existential — §1).  *Not needed*: see §4.
* No `H⁴ → H²` **retracted completed** Nemytskii at `a = 2` (No. 98's ruling; the only
  ones are gated `2·finrank+10 ≤ a`).
* **The one real gap:** no `a = 2` analogue of (S1), i.e. no
  `∀ σ, ∃ Cσ, ∀ t ∈ Icc 0 T, ∑' i w_i^σ (perModeConv λᵢ (fHi-coeff) t)² ≤ Cσ`.
* The supercritical (S1)→(S4) chain also **shrinks the horizon twice** (`d₀` at
  `ForcingFiniteOrderTimeRegularity.lean:41`, `d₂` via
  `tensorHs_smallTime_norm_le_of_perModeConv`).  Both shrinks exist purely to enter the
  realizability ball; at `a = 2` the ball is a hypothesis on **all** of `[0,T]`, so
  **neither shrink transplants — and neither is needed.**

---

## 4. Route assessment

**(R-a) Coefficient-freeze + joint induction — REJECT as stated, but its goal is
achieved for free.**  Evidence against the literal form: `liftHiN`'s coefficient slots
are `lowA2Hi(incl₂₄ v)` and `FHi(incl₃₄ v)`; `∂ₜᵏ` of the product needs
`∂ₜ`-derivatives of those *along the trajectory*, i.e. a derivative of the completed
map in its state argument — absent, and unobtainable for `FHi`.  Evidence that the
goal is already met: `coord_eq_smoothN` (`LowRegAllOrderJet.lean:148`, **proved,
sorry-free**) shows that along the trajectory the `liftHiN` coordinates ARE the
coordinates of the genuine smooth remainder `lowregNsec g (F t) =
deTurckSmoothRemainder g g (symmS g (F t))`, via `hiN_incl` → `lowreg_N_affine` →
`lowRegN_on_smooth` → `smoothN_wd` → `deTurckSmoothN_coeff` (`:344`–`:372`).  So the
frozen split's unconstrained arm **dissolves** the moment a pinned smooth family `F`
exists.  Freezing is not needed; identification is stronger and already owned.

**(R-b) Smooth-core approximation + limit in the majorants — REJECT.**  There is no
limit theorem for `JetSpectralMassControl` in the tree (`grep`: only producers and
consumers), and the majorants are pointwise-in-`t` sup bounds, which do not pass to
weak limits without exactly the uniform-in-approximation estimate that (S1) already
provides more directly.  Superseded by R-d.

**(R-c) Admit a σ-generic completed coefficient layer (the No. 94 ladder wall) —
NOT required.**  The supercritical closure needed neither a chain of fixed points
(§3a's forbidden shape) nor a `+1` coupling (§3b's stall).  It used a **finite-dimensional
Galerkin energy ladder**: the approximants are finite eigen-combinations, hence smooth
at every order, so no completed `H^{σ+2} → H^σ` operator is ever formed.  Keep R-c as
the *stop-signal*, not the route (§8).

**(R-d) TRANSPLANT the supercritical template — ADOPT.**  Concretely:
(S2)+(S3)+(S4)+(S5) transplant with **zero new mathematics** (S3 needs only the
deletion of a vestigial hypothesis); the a=2 Nemytskii↔core identity replacing
`deTurckSobolevNHa2_eq_smoothN` is **already proved** as `coord_eq_smoothN`'s core
step; the horizon shrinks are **dropped**, not transplanted, because the low lane's
ball is global.  What remains is exactly **(S1) at base order 2**.

**VERDICT.**  The frontier is not "all-order time-regularity of a self-referential
forcing".  After R-d it is one purely **spatial**, time-derivative-free statement:

> **(S1₂)** For every real `σ` there is `Cσ` with
> `∀ t ∈ Icc 0 T, ∑' i, w_i^σ · (perModeConv λᵢ (timeModeCoeff fHi i) t)² ≤ Cσ`,
> for the low-lane trajectory of `hfix`.

and its intended proof is the Galerkin energy ladder, whose Grönwall engine
(`GalerkinParabolicEnergy.lean:220`) is already order-generic and sorry-free.  The
single genuinely new estimate is the **per-scale dissipation closure at base order 2**
(the a=2 analogue of `GalerkinParabolicEnergyDeTurck.lean:1390`).

---

## 5. The `hball_full` half — the reduction is REAL

Claim to verify: `hball_full` follows from `JetSpectralMassControl g fc T` + the pin,
with **no horizon shrink**.  It does.

1. `perModeConv_allOrder_timeDeriv_spectralMass_le` at `k = 0`, `σ = 4` gives a summable
   `Cmaj` with `w_i^4 · (perModeConv λᵢ (fc i) t)² ≤ Cmaj i` for all `t ∈ Icc 0 T`.
2. The carrier's coordinates are `perModeConv λᵢ (fc i)` — that is exactly the `hf_id`
   slot `lowreg_allOrderJet` already produces (`LowRegAllOrderJet.lean:504`–`:510`), via
   `carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict`, upgraded a.e.→everywhere by
   `timeH1.continuousOn_toFun` against continuity of `perModeConv`.
3. For `S` with `toL2 S = tensorHsToL2 (carrier t)`, `smoothCcToTensorHs_coeff` gives
   `(smoothCcToTensorHs g 4 S).coeff i = perModeConv λᵢ (fc i) t`, so
   `‖smoothCcToTensorHs g 4 S‖² = ∑' w_i^4 (…)² ≤ ∑' Cmaj i` by
   `tensorHs.norm_eq_sqrt_tsum` + `Summable.tsum_le_tsum` (the exact pattern already run
   at `ForcingFiniteOrderTimeRegularity.lean:5095`–`:5102`).
4. `R₀ := Real.sqrt (∑' i, Cmaj i) + 1` gives `0 < R₀`.

Extra step beyond "free": only the a.e.→everywhere upgrade in (2).  Difficulty:
**routine**.  This confirms the note recorded in `LOWREG_BOOTSTRAP_PLAN.md` §Status
("a prover may choose `R₀` from the mass majorant and so needs **no** horizon shrink").

---

## 6. Bricks (ordered)

| # | brick | statement sketch | producers | difficulty |
|---|---|---|---|---|
| **F1** | **De-vestigialize the smooth-core jet layer** (4 declarations, 2 files).  Drop `(a : ℕ)`+`ha_super` from `deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection` (`ForcingFiniteOrderTimeRegularity.lean:4980`) and from `deTurckRemainder_path_timeJet_section` (`SmoothCoordinateJetPreservation.lean:132`); drop `ha_super` only (keep `a`, named in both conclusions) from `deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` (`:5116`) and `deTurckSmoothN_path_coeff_jetSpectralMass` (`:215`); fix call sites `:5147`, `:5384`, `:247`. | — | already-proved bodies | **routine** (one focused check per file decides it) |
| **F2** | **The state-level bridge is ALREADY PROVED — reuse, do not rebuild.**  `force_hi_smooth` (`ShortTime/LowRegForceHi.lean:65`) concludes exactly `fHi =ᵐ fun t => deTurckSmoothN g g 2 (symmS g (F t)) …` **given a smooth family `F` pinned to the trajectory plus the ball** — which is precisely what (S1₂)+(S2) manufactures.  Its own header (`:14`–`:16`, `:370`–`:372`) records that the solver produces no such family; that objection is exactly what (S1₂) removes.  See the design note below. | `force_hi_smooth`; fallback = `coord_eq_smoothN`'s `:344`–`:372` chain (`hiN_incl` → `lowreg_N_affine` → `lowRegN_on_smooth` → `smoothN_wd` → `deTurckSmoothN_coeff`) | **routine** |
| **F3** | **`lowreg_forcing_finiteOrderDriver`** — a=2 analogue of `deTurckForcing_finiteOrderSmoothDriver` (`:5409`) **on the full `T`**: from (S1₂) produce, for each `k`, `C^k` coordinates with `j ≤ k` mass on `Icc 0 T` and the a.e. pin.  Replace `deTurckSobolevNHa2_eq_smoothN` by F2; delete both shrinks (`d`, `d₂`) using the low lane's global ball. | F1, F2, `exists_smoothCcTensor_of_allOrder_spectralMass_local` (promote to non-`private` or re-derive) | **design + api-gap** |
| **F4** | **Diagonal glue** — transplant `ForcingCoordinateTimeRegularity.lean:119`'s body (a.e.⟹`EqOn`⟹`ContDiffOn ∞`⟹`contDiffOn_Icc_scalar_globalExtend`) to give `JetSpectralMassControl g fc T`. | F3 | **routine** |
| **F5** | **`hball_full`** — §5's four steps. | F4 + `lowreg_allOrderJet`'s existing `hf_id` route | **routine** |
| **F6** | **(S1₂): the per-scale Galerkin energy closure at base order 2** — a=2 analogue of `deTurckGalerkin_forcing_dissipation_perScaleSymm` (`GalerkinParabolicEnergyDeTurck.lean:1390`) feeding the order-generic `galerkin_energy_uniform_bound_perScale` (`GalerkinParabolicEnergy.lean:220`), plus the a=2 Galerkin existence and per-mode convergence rungs. | new | **math-wall — the whole remaining content** |

`lowreg_forceJetMass` = F4 ∧ F5, conditional on F6.  F1–F5 are wiring; **F6 is the leaf**.

**Design note (decide before F2, it changes a public statement).**  `force_hi_smooth`
needs the low-lane certificates `hR`, `hreal`, `hcore`, `hstate`, `hforce`, `hincl` — and
`lowreg_forceJetMass` (`:421`) currently takes **only** `hfix`.  All of them ARE in scope
at the single call site: `lowreg_allOrderJet` (`:481`) destructures `IsRealizedTwo` at
`:536`–`:539` and the 2026-08-03 widening put `R`, `hR`, `hreal`, `hNcont`, `hcoreN`,
`hA2cont`, `hA2core`, `FLo`, `hFLo`, `hFLoCore`, `hA2sq`, `hFComm`, `∀ᵐ t, ‖u.lo.toFun t‖ ≤ R`
and `√T‖fHi‖ ≤ Kf` into the predicate (`LowRegApplyTwo.lean:185`–`:219`).  So the choice
is: **(i)** widen the leaf's hypotheses to carry them (cheap, honest, mirrors what the
widening was for), or **(ii)** keep the leaf minimal and re-derive the bridge from `hfix`
alone through `coord_eq_smoothN`'s state-level chain.  Prefer **(i)** — option (ii) buys
nothing and duplicates a proved route.  Note this does NOT weaken the leaf: `hfix` alone
already pins it to a trajectory that exists, and the added certificates are all
consequences of the same `IsRealizedTwo`.

---

## 7. Risk register

**7.1 F1 may not be free — `ha_super` could re-enter transitively.  (top risk)**
Evidence for vestigiality is strong (`grep -n ha_super` on
`ForcingFiniteOrderTimeRegularity.lean` shows `:4982` then nothing until `:5118`; the
conclusion of `:4980` names `deTurckSmoothRemainder`, which carries no `a`).  But the
proof body calls ~30 `private` `anisoOn_*` / `spectralPathFO_*` lemmas (`:1116`–`:4527`)
which were *written* in the supercritical section and may carry `a` in their own
statements.  **Mitigation:** F1 is deliberately first precisely because one focused
check settles it.  If it fails, the failure message names the exact lemma that is
genuinely order-gated — which is the information the whole plan turns on.

**7.2 F6 is the `2·finrank + 10` tame splitting returning at base order 2 — math-wall.**
`GalerkinParabolicEnergyDeTurck.lean:1407` weakens `4·finrank+10 ≤ a` to
`2·finrank+10 ≤ a` and feeds `exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame`
(`DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean:9271`), whose `εwrap ≤ 32·C³·δ/(1−δ)`
is uniform in the rung `k` but whose *base* order must be supercritical.  At `a = 2` the
state control is `H⁴`, which in dim 3 embeds in `C^{2,1/2}` — mathematically ample for a
second-order operator's coefficients, so the estimate is **true**; it is simply not the
one written.  Honest classification: **new estimate needed at base order 2, not a
missing theory**.  Do not attempt F6 before F1–F5 have fixed its exact statement.

**7.3 The a=2 Galerkin forcing has to be *defined*.**  `deTurckGalerkinForcingSymm`
(`GalerkinParabolicEnergyDeTurck.lean:58`) is built from the *retracted completed*
`deTurckSobolevNHa2Symm`, which does not exist at `a = 2` (No. 98).  But Galerkin states
are `finiteEigenComboHs` — **smooth** — so the a=2 version can be built directly from
`deTurckSmoothN g g (2+k)` (`SobolevNonlinearityExistence.lean:109`, order-generic) with
confinement enforced on the finite-dimensional coefficient space.  Verify this before F6;
if it fails, F6's shape changes.

**7.4 `symmS` transport.**  `lowregNsec` pre-composes with `symmS`; the supercritical
tree needed a whole `SymmSCoefficientBlockTransfer` section
(`ForcingCoordinateTimeRegularity.lean:198`ff: `eigenBlockFinset`, `swapEigenCoeff`,
Bessel + Weyl two-weight majorant) to move jet mass across the symmetrizer's block
coefficients.  Budget for reusing it; it is `private`.

**7.5 `private`-ness.**  `exists_smoothCcTensor_of_allOrder_spectralMass_local` (`:513`)
and the `anisoOn_*` chain are `private` and duplicated (`DeTurckRemainderPathTimeJet.lean:38`).
F3 will need at least one promotion.  Prefer promoting the existing declaration over a
third copy.

**7.6 Stale prose.**  `ForcingCoordinateTimeRegularity.lean:30`–`:84` still advertises
POSITs (A)/(B) as "Honest `sorry`"; `LOWREG_BOOTSTRAP_PLAN.md` §6/§9 repeats it.  A
builder who trusts either will conclude the template is unproved and rebuild it.  Fix
both when F1 lands.

---

## 8. Stop-signal (campaign three-route-error budget)

Declare `lowreg_forceJetMass` a **route error** and hand back to the planner iff **both**:

* **F1 fails** — `ha_super` is genuinely load-bearing inside the `anisoOn_*` /
  `spectralPathFO_*` chain, so the smooth-core finite-order jet layer does **not** exist
  at `a = 2`; **and**
* **F6 is unstatable** — the per-scale dissipation at base order 2 cannot be written
  without an `H^{σ+2} → H^σ` completed coefficient family at generic σ.

That conjunction is exactly R-c: the No. 94-era σ-generic ladder wall returning through
the back door.  Record it as the obstruction and stop.  Any *single* failure is not a
stop: F1 failing still leaves the Galerkin half; F6 failing still leaves F1–F5 as
permanently useful wiring that reduces the leaf to one named spatial statement.

---

## 9. Builder brief — FIRST DISPATCHABLE BRICK (F1)

> In `E:\testdifferential-geometry-ste-align` (branch `codex/short-time-existence-align`),
> claim `DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/SmoothCoordinateJetPreservation.lean`
> and `.../ForcingFiniteOrderTimeRegularity.lean`.
>
> Test the hypothesis that the smooth-core time-jet layer is order-generic.  Do the
> smaller file first — it is the same experiment at a tenth of the size.
>
> 1. `SmoothCoordinateJetPreservation.lean`: in `deTurckRemainder_path_timeJet_section`
>    (`:132`) delete `(a : ℕ)` and `(ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)`; in
>    `deTurckSmoothN_path_coeff_jetSpectralMass` (`:215`) delete only `ha_super` (**keep
>    `(a : ℕ)`** — its conclusion names `deTurckSmoothN g₀ g_bg a (F t) …`); fix the call
>    at `:247`.  Focused-check.  `grep -n ha_super` currently shows `:134`, `:217`, `:247`
>    with nothing in between, i.e. neither body uses it.
> 2. `ForcingFiniteOrderTimeRegularity.lean`: same surgery on
>    `deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection` (`:4980`, drop both)
>    and `deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass` (`:5116`, drop `ha_super`
>    only); fix calls at `:5147` and `:5384`.  Focused-check.
>
> Use `scripts/lake-locked.ps1 check -Token <tok> -Files … -NoLakeLock`.
>
> **If GREEN:** the entire chart-level chain rule that produces finite-order time-jets of
> the Ricci–DeTurck remainder along a smooth path is available at `a = 2`, and front 2's
> frontier collapses to the single spatial statement (S1₂) of §4.  Report that, then
> proceed to F2.
> **If RED:** report the *exact* first `private` lemma whose statement genuinely needs
> `a`.  Do not repair it, do not weaken it, do not add a hypothesis — the identity of
> that lemma is the deliverable, and it decides §8's first stop-condition.
>
> **Do NOT** touch `LowRegAllOrderJet.lean` in this brick; do NOT attempt F6; do NOT add
> a `sorry` anywhere.  Record findings in the two same-name `.md` notes (create
> `SmoothCoordinateJetPreservation.md`, `ForcingFiniteOrderTimeRegularity.md`) and update
> `FORCEJETMASS_PLAN.md` §Status.
>
> While there, fix the stale prose flagged in §7.6: `ForcingCoordinateTimeRegularity.lean:38`,
> `:46`, `:80`–`:84` still advertise POSIT (A)/(B) as "Honest `sorry`" and the file as
> `sorry`-carrying; both were discharged (commits `358687842`, `b369c07f0`).  Docstring-only
> edit, no statement changes.

---

## 10. Honest denominators

* **`(N)`** (`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`) — **0 %**:
  stated, not proved.  Unchanged by this recon (recon moves no mathematics).
* **`lowreg_forceJetMass` itself — 0 %.**  Not one line of its proof exists.
* **Its dedicated machinery — was assessed at ~0 % ("no supporting estimates at all",
  §8.1); this recon revises that to ≈ 60 %** of the *transplantable* stack:
  (S2)/(S4)/(S5) order-generic and proved; (S3) proved and order-generic modulo one
  hypothesis deletion (F1, unverified); the a=2 Nemytskii↔core identity proved
  (`coord_eq_smoothN`); the Grönwall engine order-generic and proved.  The missing ~40 %
  is F3+F6, of which F6 (the base-order-2 per-scale closure) is essentially all the
  mathematics.
* **Front 2** — ~65 % (No. 98), unchanged: the reduction is a re-scoping, not progress.
  What changed is the *classification* of the remaining 35 %: from "a band with no
  supporting estimates" to "one spatial energy estimate at base order 2, plus wiring".
* **Whole HCG compactness project** — low single digits, unchanged.

---

## 11. Status

* **2026-08-03 — plan written.**  Recon only: no Lean edited, no file claimed, no Lake
  process run.  Nothing is build-verified; every claim here is a `grep`/read result.
* Key finding: `LOWREG_BOOTSTRAP_PLAN.md` §6/§9 is stale — the supercritical POSITs (A)
  and (B) are proved, and the supercritical smooth-core jet layer appears order-generic
  (four declarations carrying a vestigial `ha_super`).
* **2026-08-03 — F1 DONE, GREEN.**  `ha_super` deleted from all four declarations (plus
  the unused `(a : ℕ)` from the two whose conclusions do not name it); four in-file call
  sites fixed (`:247`, `:483`, `:5147`, `:5384` — `:483` was not in §9's list).  Focused
  check green on both files; both targeted module builds green.  No third file affected.
  **Risk 7.1 is refuted**: the `anisoOn_*`/`spectralPathFO_*` block (`:1116`–`:4527`)
  contains zero `ha_super`.  Boundary established: the completed-operator *realizability*
  layer is order-gated, the smooth-core *jet* layer above it is not.  §8's stop-signal is
  therefore closed permanently — R-c cannot return by this door whatever F6 does.
  Details in the two same-name `.md` notes and the F1 executor report in
  `UNIF_EXISTENCE_PLAN2.md`.  §7.6's stale prose was NOT fixed (out of the brick's claim).
* **2026-08-03 — F2, F3, F4, F5 DONE, GREEN.**  `lowreg_forceJetMass` is **proved**;
  the file's single `sorry` is now the named spatial leaf `lowreg_spatialMass`
  (= (S1₂) of §4, verbatim the `hspatial` hypothesis of
  `deTurckForcing_finiteOrderSmoothDriverSymm` instantiated at `a = 2` and pinned to
  the low-lane trajectory by `hfix`).  Details in
  `ShortTime/LowRegAllOrderJet.md` and
  `HeatSemigroup/ForcingCoordinateTimeRegularity.md`.

  - **F2** — took option **(i)** of §6's Design note: `lowreg_forceJetMass` widened
    to carry `hDim, hR, hρ, hRρ, hδlt, hreal, hNcont, hcoreN, hA2cont, hA2core, FLo,
    hFLo, hFLoCore, hA2sq, hFComm` and the a.e. state ball `hballU`; the single call
    site in `lowreg_allOrderJet` supplies all of them from the widened
    `IsRealizedTwo` (`hballD` is built from `ucs.link` + `hhiL2` + `hballU`).  The
    bridge itself is a NEW private lemma `liftN_smoothN_coeff`, not `force_hi_smooth`
    — see the correction below.
  - **F3** — `lowreg_forceJetStep` (one rung) + `lowreg_forceDriver` (the induction
    on `k`), on the FULL horizon.  **Both horizon shrinks deleted**, as predicted.
    `deTurckSobolevNHa2_eq_smoothN` replaced by the F2 bridge.
  - **F4** — the diagonal glue, transplanted from
    `maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMassSymm`, now the middle of
    `lowreg_forceJetMass`'s body.
  - **F5** — `hball_full` exactly per §5's four steps, `R₀ := √(∑' Cmaj) + 1` from the
    `σ = (2:ℝ)+2`, `j = 0` majorant; the a.e.→everywhere upgrade is factored into the
    new private lemma `carrier_coeff_pmConv` (reused by `lowreg_allOrderJet` for
    `hf_id`, removing ~50 lines of duplication).

  **§6 F2-row correction (important for future readers).**  The row claimed
  `force_hi_smooth` (`ShortTime/LowRegForceHi.lean:65`) could be reused directly.  It
  cannot: its `hforce` slot is the *low* `lowRegN`-shaped identity at `H¹`, whereas
  `IsRealizedTwo` exports the *frozen-split* identity `fHi =ᵐ liftHiN(…)`.  Getting
  from one to the other is precisely the `hiN_incl → lowreg_N_affine` chain, so the
  plan's own "fallback" was the actual route.  It was implemented as a standalone
  pointwise lemma so that both `coord_eq_smoothN` and the new driver can use it.

  **§7.4 (`symmS` transport) materialised, and §7.5's promotion target moved.**  The
  low lane's `lowregNsec` has `symmS` baked in, so it is the supercritical **Symm**
  tower (`ForcingCoordinateTimeRegularity.lean`'s `SymmSCoefficientBlockTransfer`),
  not the raw `deTurckSobolevNHa2` tower, that transplants.  Five declarations were
  promoted there (`exists_smoothCcPath_realizing_coeff`, `symmCoeffPath`,
  `symmCoeffPath_contDiff`, `symmCoeffPath_realizes`, `symmCoeffPath_spectralMass`);
  no Bessel/Weyl majorant was re-derived.  `exists_smoothCcTensor_of_allOrder_
  spectralMass_local` (`ForcingFiniteOrderTimeRegularity.lean:513`) was **not**
  promoted — the path form above supersedes it for this consumer and lives in the
  file that had to be edited anyway.  `ForcingFiniteOrderTimeRegularity.lean` was
  claimed but not edited.

  Sorry census over all edited files after the pass: **exactly one**,
  `lowreg_spatialMass`.  Focused checks GREEN on both edited Lean files; targeted
  module builds GREEN.

* **NEXT: brick F6** (§6, §7.2–§7.3) — prove `lowreg_spatialMass`.  It is now the
  only mathematics left in front 2's forcing package, and its statement is frozen by
  what `lowreg_forceDriver` consumes, so F6 can be attacked without touching anything
  above it.  Route: the `a = 2` Galerkin energy ladder into the order-generic Grönwall
  engine `galerkin_energy_uniform_bound_perScale` (`GalerkinParabolicEnergy.lean:220`);
  verify §7.3 first (the `a = 2` Galerkin forcing must be built from
  `deTurckSmoothN g g (2+k)` on the finite eigen-combination space, since
  `deTurckSobolevNHa2Symm` does not exist at `a = 2`).
