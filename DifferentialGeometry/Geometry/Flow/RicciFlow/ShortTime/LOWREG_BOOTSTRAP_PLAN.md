# Front 2 — the a-posteriori fixed-horizon endpoint bootstrap (plan)

Recon 2026-08-02, checkout `E:\testdifferential-geometry-ste-align`, branch
`codex/short-time-existence-align`.  Read-only recon; no Lean file edited, no
file claimed.  Anchor: `UNIF_EXISTENCE_PLAN2.md` №91–96; this scopes "front 2"
of №95's candidate list.

> **CORRECTION (2026-08-03, ledger №98 era; supersedes every "two honest
> `sorry` POSITs" line below).**  The supercritical POSITs (A)/(B) named in
> this plan were ALREADY DISCHARGED before this plan was written (zero code
> sorries under `HeatSemigroup/` and `DeTurck/`; the templates' module
> docstrings are stale).  The closure mechanism never differentiates the
> nonlinearity in the state — see `FORCEJETMASS_PLAN.md` (2026-08-03) for
> the verified (S1)–(S5) route and the actual remaining content at `a = 2`
> (the per-scale energy closure at base order 2).  This plan's WIRING parts
> (§§4–7) were executed as bricks; `lowreg_joint_two` landed 2026-08-03.

**Headline.**  The endpoint machinery front 2 was supposed to build **already
exists and is sorry-free** — `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
(`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean:1311`)
turns a `MaxRegSolutionSpace a T` plus an all-order smooth-in-time forcing-coordinate
package into exactly the `(N)` `rr` fields (`F 0 = 0`, the `Ico`-slab PDE with
`HasDerivWithinAt … (Ici 0)`, and `JointChartGramSmooth T` = joint `C∞` on the
**closed** `Icc 0 T` slab, corner included) on the **full, unshrunk** horizon `T`.
Its `hC` slot has a purpose-built dim-3 producer at **`a = 2`** (`hs2_opBound_at_two`,
same file `:1593`) which currently has **no consumer** — `a = 2` is exactly the high
scale of the closed `(1,2)` rung.  So front 2 is *not* a ladder-building job:
it is the job of feeding the closed rung into that a = 2 entry point.

The one input with no producer at `a = 2` is the **all-order smooth-in-time
forcing-coordinate package** (`f`, `hf_smooth`, `hf_mass`, `hf_id`).  Its only
existing producer is stated at supercritical order with the *high-order* existence
horizon and rests on two honest `sorry` POSITs.  **Re-basing those two POSITs at
`a = 2` on the solver's own horizon is the whole of front 2.**

Both ladder routes named in the dispatch brief are **ruled out by evidence in the
tree** (§3): rung-via-fixed-point needs per-rung smallness (forbidden shape), and
rung-via-mass-lifting provably **stalls** because the DeTurck nonlinearity loses
**two** orders, not one.

---

## 1. The consumer contract

### 1a. What `(N)` asks for (verbatim, `Evolution/ExtendViaUniqueness.lean:80–98`)

Three `rr` fields, all on `Set.Ico (0:ℝ) τ₀ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet`:

```lean
    ∃ rr : ℝ → SmoothRiemannianMetric I M, rr 0 = g₀ ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) τ₀ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (… the now-redundant `ContinuousOn` field …) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Set.Ici 0) t)
```

Decomposition against the ruling (`FORWARD_UNIQUE_PRO_RULING.md`, §"Cost of
up-to-corner C∞ in the (N) lane", lines 120–135):

| piece | existing bridge | status |
|---|---|---|
| interior spatial `C∞` per slice | subsumed — the joint statement is stronger | n/a |
| joint `(t,x)` `C∞` **including the `t = 0` corner** | `JointChartGramSmooth` (`ShortTime/DeTurckChartRegularityFromJoint.lean:85`), on `Icc 0 T` — **stronger** than `Ico` | **HAVE** |
| the PDE field | `IsQuasilinearMetricParabolicSolution` (`Analysis/Parabolic/DeTurckRicci/QuasilinearMetricShortTimeExistence.lean:74`) — same `HasDerivWithinAt … (Ici 0)` on `Ico 0 T`, plus `g_fam 0 = g₀` | **HAVE** |
| DeTurck → Ricci gauge | `ricci_gauge_of_dt` (`ShortTime/LowRegGaugeRemoval.lean:156`), sorry-free | **HAVE** (separate lane) |
| `Λ`-uniform `τ₀` over the admissible class | none | **front 3, not front 2** |

`deTurckRicci_chartRegularity_of_jointChartGramSmooth`
(`DeTurckChartRegularityFromJoint.lean:701`) derives the whole six-conjunct
chart-regularity tail of the DeTurck headline **sorry-free** from
`JointChartGramSmooth` alone.  So the single consumer-facing datum is

```lean
theorem deTurckRicci_solution_with_jointReg (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I) (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT
```
(`ShortTime/DeTurckInitialDataExistence.lean:92`) — **already proved**, at
`a := 4·finrank ℝ E + 10`.

### 1b. Why the proved version does not serve `(N)`

Its `T` is `min (quasilinear_maxreg_solution_of_nemytskii g₀ a Nfun hLipN H2).choose 1`
(`ShortTime/QuasilinearAbstractShortTimeExistence.lean:110–113`) — the horizon of a
**high-order** Banach fixed point, depending on the order-`a` Lipschitz constants of
`Nfun`, hence on all derivatives of `g₀`.  The ruling allows per-datum higher
*constants* but requires the **lifetime** to depend only on ellipticity and
order-`≤3` bounds.  Front 2's job is therefore to reproduce the same conclusion
with `T` := the `(1,2)`-rung solver's own horizon `T₀` from
`lowreg_solve_two` (`ShortTime/LowRegApplyTwo.lean:383`), which is built from
`hDim, g` alone.

### 1c. Bridges NOT on the critical path (recon negative results)

* **`laplacianDomainPow` ↔ `tensorHs` is UNBRIDGED, and irrelevant.**
  `ChartH2kRegularity.lean:316` (`chartPushed_memWkp_two_k_of_laplacianDomainPow`) is a
  **scalar** chart-`W^{2k,2}` endpoint for the scalar Hodge-Laplacian resolvent scale
  `laplacianDomainPow` (`Analysis/Elliptic/Regularity/Iterated/Defs.lean:132`, a
  `Submodule ℝ (H1Compl g)`).  Zero files mention both symbols; `tensorHs` has 0 hits
  under `Analysis/Elliptic/`, `laplacianDomainPow` 0 hits under `Analysis/Parabolic/`,
  `Analysis/Spectral/`, `Geometry/Flow/`.  Different bundle, operator and carrier.
  **Do not attempt this bridge — the realized route (§2) does not need it.**
* **No `Ico`/corner `∞` PDE bootstrap, and none needed.**
  `Analysis/Calculus/TimeSliceBootstrap.lean:283` `contDiffOn_inf_of_pde` requires
  `IsOpen U`; the only `Icc` variant `contDiffIcc_succ` (`:230`) is **finite order**, and
  the one `∞`-at-the-corner assembly over it is the bespoke `gramSmoothIcc`
  (`HCGCompactness/FlowLimitRegularity.lean:1582`), fed by a `ConvOut` metric limit, not a
  spectral object.  The corner is reached by the spectral series route (§4).
* `AllOrderGardingConstant.lean:1169` gives a Gårding constant **per order** (`C` inside
  `∀ k`), not order-uniform, and its consumers transitively depend on `sorryAx`.
* The embedding layer (`IteratedSobolevEmbedding.lean:367`
  `contDiffOn_of_forall_memWkp_two`; `TensorSuperCriticalReconstruct.lean:1427`, `∀ k`
  chart-`W^{2k,2}` ⟹ `SmoothCcTensor`, **proved unconditionally**) is already consumed
  *inside* the spectral apex.  Nothing to re-derive.

---

## 2. The realized route, end to end (what exists today)

```
  MaxRegSolutionSpace a T (u, trace0 = 0)  +  f : eigen-coord family, C∞ in t,
  Duhamel/forcing identity                    all-order (j,τ) mass majorant on Icc 0 T
                                |
   maxreg_solution_jointly_smooth_representative_of_tame_nemytskii  (:1311, sorry-free)
                                |
     F : ℝ → SmoothCcTensor, F 0 = 0, pin on Icc 0 T,
     PDE on Ico 0 T (HasDerivWithinAt … (Ici 0)),  JointChartGramSmooth T
                                |
       deTurckRicci_chartRegularity_of_jointChartGramSmooth  (sorry-free)
                                |
                    the six (N)/(A) chart-regularity fields
```

Internal apex, **sorry-free** (docstring reports `#print axioms` clean):
`jointChartGramSmooth_of_spectralSmooth_timeSmooth`
(`Analysis/Spectral/Intrinsic/HeatSemigroup/SpectralEigenSeriesJointGram.lean:1687`),
taking `T_rep : ℝ → SmoothCcTensor g 0 2` with a fibre bound `hδ_lt : δ < 1`, an
eigen-coordinate family `φ` with `∀ i, ContDiff ℝ ∞ (φ i)`, the coefficient pin
`hcoeff` on `Icc 0 T`, and the load-bearing hypothesis

```lean
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj, Summable Cmaj ∧ ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i σ * (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
```
concluding `JointChartGramSmooth T (fun t => tensorSectionRealizeMetric g (T_rep t) …)`.

The solution-side `φ` is obtained from the forcing-side `f` **sorry-free** by
`perModeConv_allOrder_timeDeriv_spectralMass_le`
(`HeatSemigroup/MaxRegInteriorTimeSmoothing.lean:196`): the per-mode ODE
`φᵢ' = fᵢ − λᵢφᵢ` trades one time-derivative for two spatial orders, so an
all-order forcing majorant gives an all-order solution majorant on `Icc 0 T`.

**Everything above `f` is done.**  The only unproduced input at `a = 2` is `f` itself.

---

## 3. The ladder — both proposed routes are ruled out

### 3a. Rung-via-fixed-point needs per-rung smallness (forbidden shape)

`lowreg_lift_two` (`ShortTime/LowRegLiftTwo.lean:169`) delegates to `nonautL2_lift`
(`Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/NonautonomousL2Lift.lean:526`),
which **constructs** the high solution by `nonautL2_forced`, a Banach fixed point at
the high scale.  Its smallness hypothesis is per-rung:

```lean
    (hsmallHi : (C2Hi : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1)
```

At rung `k` this needs `‖A₂^{(k)}‖·(1+T) < 1` with a **single** coefficient radius `ρ`
fixed before the trajectory exists (`lowreg_solve_two` chooses `ρ` from `refold_aff` /
`realize_at_thr` / `radialA2_lip` / `lowA2_small` *before* obtaining `f`,
`LowRegApplyTwo.lean:387–415`).  Since the `(1+T)` factor does not vanish as `T → 0`,
the only lever is `ρ`, and a single `ρ` cannot beat order-dependent Moser constants.
This is exactly the "re-run the fixed point per derivative order and intersect
shrinking horizons" pattern the ruling forbids.

### 3b. Rung-via-mass-lifting STALLS — the tree already says so

The unconditional, smallness-free, same-horizon engine exists —
`solField_into_all_tensorHs_interior` (`HeatSemigroup/ParabolicInteriorSmoothing.lean:326`,
file sorry-free): from `hbase : Summable (solFieldMass hT f b)` and

```lean
    (hcouple : ∀ d : ℝ, Summable (solFieldMass … hT f (d + 1)) → Summable (forcingMass … f d))
```
it produces a genuine `timeL2 (tensorHs g r s σ) T` field for **every** real `σ` on the
**same** `T`.  But `hcouple` is a **`+1`** coupling and the DeTurck remainder loses **`+2`**.
`ForcingTimeBootstrap.lean`'s own header (lines 22–36) states this verbatim:

> "the naive one-order interior-smoothing bootstrap of `ParabolicInteriorSmoothing.lean`
> (`solFieldMass_summable_all`, fed a `+1` coupling `solFieldMass (d+1) → forcingMass d`)
> STALLS: its net advance per step is parabolic-gain (`+2`) − coupling-loss (`+2`) `= 0`"

`PrincipalPartMatch.lean` (§"Scope (honest)") confirms it establishes only the
**symbol-level** principal-part match and explicitly does **not** assemble an operator
`N : tensorHs (a+1) → tensorHs a`.  Every realized Nemytskii in the tree is `+2`:
`deTurckSobolevNHa2` / `deTurckSobolevNHa2Symm : tensorHs g₀ 0 2 (a+2) → tensorHs g₀ 0 2 a`
(`DeTurck/SobolevNonlinearityExistence.lean:2323`, `:2783`), `lowRegN : H³ → H¹`,
`liftHiN : H⁴ → H²` (`ShortTime/LowRegForceHi.lean:132`).

**Ruling: do not attempt to prove a `+1` coupling.**  It would require the operator-level
first-order bound that `PrincipalPartMatch.lean` documents as blocked by two further
obstructions (`RHSPointwiseLipschitz.lean` `O1`/`O2`) plus a type-level obstruction.

### 3c. The gain mechanisms that DO exist (raw material for §6's POSITs)

Two smallness-free, **fully order-generic** layers are present — the raw material a
proof of the posited interior-time smoothing would use:
`tensorHeatSemigroupHs_opNorm_le` (`Analysis/Parabolic/TensorHeatEquation/SmoothingHs.lean:791`),
`‖e^{tΔ_∇}‖_{H^a→H^b} ≤ √(tensorSmoothingConst (b−a))·t^{−(b−a)/2}` for arbitrary real
`a ≤ b`, `0 < t ≤ 1`, with the cross-scale semigroup law (`:824`, `:850`); and
`heatPower_opNorm_le` (`Analysis/Heat/Semigroup/SpectralBounds.lean:524`),
`‖Δ^k e^{tΔ}‖ ≤ (k/t)^k e^{−k}`, generic `k : ℕ`, every `t > 0`.
They break the `+2` neutrality at the price of a `t^{−·/2}` weight, i.e. interior-in-time.
Carrying them **to the corner** is legitimate here because the datum is **zero**
(`u.repr 0 = 0`) and `staticForce g₀ g_bg σ` exists at **arbitrary real `σ`**
(`ShortTime/LowRegLiftNTerm.lean:142`, unconstrained `(σ : ℝ)`; `staticForce_incl`/`_congr`
generic at `:150`/`:158`).  This is why (A′) is *true*, not merely convenient.

There is also a genuine **all-orders tame splitting**,
`exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame`
(`DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean:9271`, sibling `:4803`):
`N(T₀) − N(0) = principalCometricArm + third + tame` with, for **every** `k : ℕ`,
`‖third‖_{a+k−1} ≤ εwrap·‖T₀‖_{a+k+1} + Cthird k·‖T₀‖_{a+k}` and
`‖tame‖_{a+k−1} ≤ Ctame k·‖T₀‖_{a+k}`, where `εwrap ≤ 32·deTurckArmFibreConst³·(δ/(1−δ))`
depends on the **fibre smallness `δ` alone, uniformly in `k`**, with the state constrained
only by the fixed `H^{a+2}` radius `R₀`.  That is the Nash–Moser shape a real ladder needs
— gated on `2·finrank ℝ E + 10 ≤ a` (`a ≥ 16` in dim 3).  See §8.1: it does **not** reach
`a = 2`.

### 3d. What the linear layer *does* give for free

Not needed for the recommended route, but worth recording: the cross-scale linear
Duhamel compatibility is smallness-free and one-line-provable, because inclusion is
mode-transparent (`timeModeCoeff_timeL2Inclusion`,
`MaximalRegularity/TimeL2InterpolationLimit.lean:89`) and the Duhamel field is diagonal
(`maximalRegularitySolField_timeModeCoeff = solModeCoeff`,
`MaximalRegularity/Operator.lean:491`, and `solModeCoeff` depends on `a` only through
the type, `:88`).  `timeModeCoeff_injective` (`Plancherel.lean:551`) closes it.  Only
the **existence** of the high-scale forcing needs the fixed point.

---

## 4. The corner — already solved, no new machinery

`JointChartGramSmooth T` is stated on `Set.Icc 0 T ×ˢ baseSet`, i.e. **through** the
corner — *stronger* than `(N)`'s `Ico 0 τ₀`.  It is reached by the spectral eigen-series
route, not a time-slice PDE bootstrap: the realized chart-Gram entry is **affine** in
`T_rep t`, so joint smoothness reduces to `hmodemass`.  `t = 0` compatibility is free
because `u.repr 0 = 0` / `timeH1.trace0 u.lo = 0` (both `IsRealizedTwo` conjuncts,
`LowRegApplyTwo.lean:90`) and the background is smooth; `F 0 = 0` falls out of the
endpoint.  `SpectralEigenSeriesJointGram.lean` also records that the *weaker* time-**continuity**
hypothesis is **false as an input** (counterexample `T_rep t = |t|·S₀`), so time-**smoothness**
of the coordinates is not negotiable.

---

## 5. VERDICT

**Route: re-base the existing endpoint chain at `a = 2` on the solver's horizon.**
Not a ladder, not a chart-level Ladyzhenskaya argument.

Rationale: (i) the entire endpoint chain above the forcing-coordinate package is
already sorry-free and lands the exact `(N)` fields on the **unshrunk** horizon
(§2); (ii) both ladder shapes are ruled out by evidence already in the tree (§3);
(iii) `hs2_opBound_at_two` (`MaxRegSolutionJointlySmooth.lean:1593`) is a
purpose-built, dim-3, **consumerless** producer for the tame endpoint's `hC` slot at
exactly `a = 2`, which is exactly the high scale of the closed `(1,2)` rung — the
architecture was designed for this join and never wired; (iv) the honest-input surface
then becomes two named classical parabolic facts stated **on the right horizon**,
instead of an unstated black box.

**Alternatives considered and rejected.**
*Route S — keep the supercritical order, fix the horizon later.*  Rejected: the
supercritical `T` is the lifetime of a fixed point whose Lipschitz data is the order-`a`
Nemytskii constant, so `T = T(‖g₀‖_{H^{a+2}})`.  The ruling permits per-datum higher
*constants* but requires the **lifetime** to depend only on ellipticity and order-`≤3`
bounds.  Extending the high regularity from the supercritical `T_a` up to the low
lane's `τ₀` by continuation needs an a-priori high-order bound on the whole
`[0, τ₀)` — strictly harder than (A′).
*Route L — chart-level Ladyzhenskaya.*  Rejected: it would re-enter through the
`Analysis/Elliptic` `laplacianDomainPow` lane, which is scalar and **provably unbridged**
to `tensorHs` (§1c), and would duplicate the already-sorry-free
`SpectralEigenSeriesJointGram` apex.

---

## 6. Hypothesis-by-hypothesis production map (tame endpoint at `a = 2`)

Target: `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
(`MaxRegSolutionJointlySmooth.lean:1311`), instantiated at `g₀ := g`, `a := 2`,
`T := ` the horizon of `lowreg_solve_two`.

| slot | producer | status |
|---|---|---|
| `u : MaxRegSolutionSpace (2:ℝ) T` | `IsRealizedTwo`'s `uHi`, with `u.lo = uHi` | **HAVE** |
| `htrace : timeH1.trace0 _ T u = 0` | `IsRealizedTwo` conjunct 4 | **HAVE** |
| `F_RHS := deTurckRicciRHS g_bg`, `Nsec := deTurckSmoothRemainder`, `hRepr` | the `hRepr` proof at `DeTurckInitialDataExistence.lean:99–110` is **order-free** — copy the instantiation | **HAVE** |
| `C`, `hC_pos`, `hC` | `hs2_opBound_at_two hDim g` (`MaxRegSolutionJointlySmooth.lean:1593`) | **HAVE (dim 3)** |
| `hfloor : Real.sqrt T * ‖u.deriv‖ ≤ 1/(2*C)` | `‖u.deriv‖` is bounded by the forcing norm `≤ P/4` where `P` is the solver's capped realization radius; shrink `P` (a state-radius cap, *not* a horizon cap) or `T ≤ T₀` | **routine, but verify** — §8.3 |
| `R₀`, `hball_full` on **all** of `Icc 0 T` | no producer; `SmallTimeSmoothness.lean:117` / `realizedSol_solField_smallnessHorizon_Ha2Symm` give only a short `d₂` | **GAP** — §8.2 |
| `f`, `hf_smooth`, `hf_mass` (all `(j,τ)`, on `Icc 0 T`) | only `deTurckForcing_smoothTimeCoordinateFamilySymm` (`ForcingTimeBootstrap.lean:199`), supercritical + high-order horizon, resting on POSITs (A)/(B) | **THE GAP** — §7 B1 |
| `hf_id` | linear Duhamel per-mode identity (`maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv`) + `IsRealizedTwo`'s `u.hiL2 = maxRegDuhamelSolField 2 hT hT1 0 fHi` | **glue** |
| `hForce` | `force_hi_id` (`fHi =ᵐ liftHiN ∘ (u.hiL2)`, `IsRealizedTwo` last conjunct) + `hiN_incl`/`hiN_lowreg` (`LowRegForceHi.lean:166`,`:299`) + `lowRegN_on_smooth` (`LowRegSmoothBridge.lean:82`) | **adapter, real work** — §8.3–8.5 |
| `u = maxRegDuhamelMap 2 hT hT1 0 fHi` (needed if routing through `deTurckRicci_forcingBootstrap_symm`) | `timeH1` `@[ext]` (`TimeSobolev/TimeH1.lean:192`) + `maxRegDuhamelMap_init`/`_deriv` (`SolutionSpace.lean:624`,`:651`) against `IsRealizedTwo`'s trace/timeDeriv conjuncts | **routine** |

The two honest POSITs to re-base (currently at supercritical `a`, in
`HeatSemigroup/ForcingCoordinateTimeRegularity.lean`, the file's only two code
`sorry`s):

* **(A)** `deTurckForcing_solCoeff_jetSpectralMass` — all-order interior-time smoothing
  of the zero-datum solution field at eigen-coordinate level, plus the a-priori
  realizability-ball bound `‖u t‖_{H^{a+2}} ≤ deTurckRealizabilityRadius` on `[0,T]`;
* **(B)** `deTurckSobolevNHa2_jetSpectralMass_preserving` — order-preserving smoothness
  of the Nemytskii forcing on in-ball data.

Everything between them and `f` is sorry-free glue
(`deTurckForcing_timeModeCoeff_smooth_allOrderJetSymm` `:1226`,
`deTurckForcing_smoothCoordinate_aeTimeJetSymm` `:1257`).

---

## 7. Bricks (ordered)

**B1 (FIRST, dispatchable). `lowreg_allOrderJet` — the re-based forcing-coordinate
package at `a = 2`.**
Home: **new** `ShortTime/LowRegAllOrderJet.lean` (must see `LowRegApplyTwo`,
`LowRegForceHi`, and `HeatSemigroup/MaxRegInteriorTimeSmoothing`).
Statement sketch: from `IsRealizedTwo g hρ hδ0 hδ_le hreal' hT hT1 f` produce
`∃ fc : TensorEigenIdx g 0 2 → ℝ → ℝ`, `(∀ i, ContDiff ℝ ∞ (fc i))`, the all-`(j,τ)`
summable majorant on `Icc 0 T`, and the a.e. pin `fc i =ᵐ fun t => (fHi t).coeff i`.
Two honest `sorry`s, (A′) and (B′), pinned to `force_hi_id` so neither is vacuous.
Difficulty: **design** (statement shape) + **math-wall** (the two POSITs).

| brick | content | difficulty |
|---|---|---|
| **B2** | `hf_id` (linear per-mode Duhamel identity) + `hduh` (`timeH1` `@[ext]` against `maxRegDuhamelMap_init`/`_deriv`), same file | routine |
| **B3** | `hForce` at `a = 2`: "`fc i t` = the `i`-th coefficient of `deTurckSmoothRemainder` on any pinned in-ball smooth family".  Route `force_hi_id` → `hiN_lowreg` → `lowreg_N_affine` (`LowRegLiftAffine.lean:318`) → `lowRegN_on_smooth` → `lowCore_split` | api-gap |
| **B4** | `R₀`/`hball_full` on the full slab — fold into B1's (A′), see §8.2 | api-gap |
| **B5** | `lowreg_jointGram`, **new** `ShortTime/LowRegJointGram.lean`: instantiate the tame endpoint; conclude `IsQuasilinearMetricParabolicSolution (deTurckRicciRHS g) g T g_DT ∧ JointChartGramSmooth T g_DT` at the solver's `T` | routine after B1–B4 |
| **B6** | rewire `deTurckRicci_solution_with_jointReg` (`DeTurckInitialDataExistence.lean:92`) to the horizon-parametrized version, keeping the supercritical proof as fallback; then front 3 | routine |

---

## 8. Risk register

### 8.1 B1's POSITs are the real content, and `a = 2` is BELOW every in-tree estimate — **math-wall**

Top risk, sharper than first expected.  **Every** supporting estimate in the tree sits
either at the `(1,2)` rung with literal exponents `1,2,3,4` — `lowA2Hi/lowA2Lo/lowA1Hi/lowA1Lo`
(`DeTurck/DeTurckRemainderLowBaseTime.lean:1555/1569/1718/1732`), `lowA2_small`
(`LowRegOperatorTime.lean:668`), `c0_pack`/`c1_bg_pack`/`refold_aff`
(`LowRegBgC0Time.lean:322`/`LowRegBgC1Time.lean:763`/`LowRegBgA1Refold.lean:331`), the five
`H2Pair` classes and `selfLow_pair_h2` (`DeTurckRemainderLowBaseH2Pair.lean:5806`) — or
**above `2·finrank ℝ E + 10 ≤ a`** (`deTurckSmoothN_ballLipschitz_Ha2`,
`SobolevNonlinearityExistence.lean:2026`; the all-orders tame splitting, §3c).  The one
classical-shape tame estimate, `smoothN_h1_tame` (`ShortTime/LowRegCoreTame.lean:201`,
top-order difference carrying `Ctop·R` with `R` the **low `H²`** radius), is at `a = 1`.

So `a = 2` is a **band with no supporting estimates at all**.  (A′)/(B′) are still *true*
(smooth zero datum on a closed manifold ⟹ smooth up to `t = 0`; §3c is the raw material),
but nothing in the tree can be reused to prove them there.  Classification: **mathematical
obstruction**, matching the ruling's "medium-sized dedicated endpoint-bootstrap layer".
*State* them honestly; do not prove them in this pass.  **Do not** widen the honest-input
surface beyond these two and **do not** raise the base order by adding rungs (§3a's
forbidden shape).  If the two-posit split is unwritable at `a = 2`, collapse to a
**single** named leaf.

### 8.2 `hball_full` on `Icc 0 T` is not free — **api-gap**

The tame endpoint wants `‖S‖_{H⁴} ≤ R₀` for **every** `t ∈ Icc 0 T` and every smooth
`S` representing `u t`.  From the `(1,2)` rung we have `u.hiL2 ∈ L²ₜH⁴` and
`u.lo ∈ timeH1(H²)` (hence `C⁰ₜH²` by `timeH1.continuousOn_toFun`,
`TimeSobolev/TimeH1.lean:293`) — **no sup-in-`t` `H⁴` bound**.  Note the hypothesis is
an *implication* from "S represents `u t`", so it is vacuous where no smooth
representative exists; the honest reading is that `R₀` must come out of (A′)'s
realizability-ball clause.  **Fold `hball_full` into (A′) rather than proving it
separately.**  Watch this: getting it wrong makes B1 vacuous.

### 8.3–8.5 Smaller risks

* **`hfloor` (`√T·‖u.deriv‖ ≤ 1/(2C)`, `C` from `hs2_opBound_at_two`) — check early.**
  `lowreg_solve_two` already caps its realization radius `P` and reports `‖f‖ ≤ P/4`, but
  `IsRealizedTwo`'s derivative clause is `timeDeriv u.lo = timeScaleLaplacian 2 u.hiL2 + fHi`,
  so `‖u.deriv‖` involves `‖u.hiL2‖_{H⁴}` too.  If radius-shrinking does not suffice this
  becomes a horizon condition — acceptable (one-time, order-independent) provided it is
  folded into `T₀` and **never re-imposed per order**.
* **`hForce` quantifies over *arbitrary* pinned in-ball families**, not one chosen `F`.
  `lowreg_N_affine` / `hiN_lowreg` are **state-level on the whole `H³`/`H⁴` ball`, which is
  the right shape; the trap is the exponent transport (`((1:ℕ):ℝ)` vs `(1:ℝ)`, `2+2` vs `4`).
  Do it **once**, at the top, on `fHi` (`LOWREG_HFLO_BRIDGE_PLAN.md` §3 idiom).
* **dim-3 pin.** `hs2_opBound_at_two` and `lowreg_solve_two` both need
  `hDim : finrank ℝ E = 3`; `(N)` is dimension-free.  Record the scope restriction; do not
  silently generalize.

### 8.6 Checked and cleared (not risks)

`laplacianDomainPow` ↔ `tensorHs` (§1c); a reusable `contDiffIcc_inf_of_pde` (§4);
order-uniform Gårding constants; `TensorSuperCriticalReconstruct` (proved unconditionally,
`:1427`); the corner (already `Icc`); `hRepr` (order-free); cross-scale linear Duhamel
compat (free, §3d).

---

## 9. Builder brief (self-contained, brick B1)

> In `E:\testdifferential-geometry-ste-align` (branch `codex/short-time-existence-align`),
> create `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegAllOrderJet.lean`
> and state the **re-based all-order forcing-coordinate package at `a = 2`** for the
> trajectory produced by `lowreg_solve_two` (`ShortTime/LowRegApplyTwo.lean:383`).
>
> Consume `IsRealizedTwo` (`LowRegApplyTwo.lean:90`) — in particular its last conjunct
> `fHi =ᵐ fun t => liftHiN g … FHi (tensorHsCongr … (u.hiL2 t))` — and produce
> `∃ fc : TensorEigenIdx g 0 2 → ℝ → ℝ` with
> `(∀ i, ContDiff ℝ ∞ (fc i))`, the all-order majorant
> `∀ (j : ℕ) (τ : ℝ), 0 ≤ τ → ∃ B, Summable B ∧ ∀ i, ∀ t ∈ Set.Icc (0:ℝ) T,
> tensorSobolevWeight i τ * (iteratedDeriv j (fc i) t)^2 ≤ B i`,
> the a.e. pin `∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i`, and a
> realizability-ball clause `∀ t ∈ Icc 0 T, ‖u.hiL2 t‖ ≤ R₀` (see §8.2 — fold the ball
> into this statement, do **not** leave `hball_full` to a separate brick).
>
> **Mirror the existing supercritical split exactly**: two honest `sorry`s named
> `lowreg_solCoeff_jetMass` (A′) and `lowreg_liftHiN_jetMass_preserving` (B′),
> modelled verbatim on `deTurckForcing_solCoeff_jetSpectralMass` and
> `deTurckSobolevNHa2_jetSpectralMass_preserving`
> (`Analysis/Spectral/Intrinsic/HeatSemigroup/ForcingCoordinateTimeRegularity.lean`,
> header lines 30–47 describe both), but **pinned to the low-lane forcing identity** so
> neither is vacuous, and with `deTurckSobolevNHa2Symm` replaced by `liftHiN`
> (`ShortTime/LowRegForceHi.lean:132`).  Then re-run the sorry-free glue of
> `deTurckForcing_timeModeCoeff_smooth_allOrderJetSymm` (`:1226`) and
> `deTurckForcing_smoothCoordinate_aeTimeJetSymm` (`:1257`) at `a = 2`; both are pure
> `timeModeCoeff_coeFn` bookkeeping (`MaximalRegularity/Plancherel.lean:206`).
>
> **Do NOT** attempt a `+1` coupling for `ParabolicInteriorSmoothing.solField_into_all_tensorHs_interior`
> (`:326`): `ForcingTimeBootstrap.lean` header lines 22–36 record that it stalls at
> net advance `0`, and `DeTurck/PrincipalPartMatch.lean` §"Scope (honest)" records that
> the operator-level first-order bound is not available.  **Do NOT** iterate
> `lowreg_lift_two` to higher rungs: its `hsmallHi` (`LowRegLiftTwo.lean:183–184`) is a
> per-rung contraction condition and that is the shape the `(N)` discharge ruling forbids.
>
> Read §8.1 first: `a = 2` sits below **every** supporting estimate in the tree, which is
> expected and is exactly why (A′)/(B′) are honest inputs.  Do **not** discharge them, do
> **not** add a rung, do **not** introduce a third posit; if the split is unwritable at
> `a = 2`, collapse to a single named leaf and report.
>
> Verify with a focused `scripts/lake-locked.ps1 check … -NoLakeLock`, then a targeted
> `build -NoLakeLock +…LowRegAllOrderJet`.  Record findings in `LowRegAllOrderJet.md`.

---

## Status

* **2026-08-02 — B1 (+B2, B4, B5) LANDED.**  `ShortTime/LowRegAllOrderJet.lean`,
  notes in `LowRegAllOrderJet.md`.  Focused check and targeted module build both
  GREEN; sorry census = exactly one.
  * `lowreg_forceJetMass` (`:151`) — the **single** honest frontier.  §9's
    two-posit mirror was NOT written: (B′) is unwritable at `a = 2` as a true
    standalone statement, because the only high-scale nonlinearity is the frozen
    split `liftHiN` whose arm `FHi` is an unconstrained existential inside
    `IsRealizedTwo`.  §8.1's own fallback ("collapse to a single named leaf") was
    taken; the leaf is pinned to the low-lane forcing identity so it is not
    vacuous, and it carries the folded `R₀`/`hball_full` clause of §8.2.
  * `lowreg_allOrderJet` (`:203`) — the package (B1 + B2's `hduh`/`hf_id` +
    B4's ball), on the full unshrunk horizon.
  * `lowreg_joint_smooth` (`:362`) — B5, the endpoint at `a = 2`, **first
    consumer of `hs2_opBound_at_two`**; sorry-free and frontier-independent.
  * `lowreg_joint_of_re` (`:462`) — the composition from `IsRealizedTwo`.
  * §8.3 `hfloor` and B3 `hForce` stay VISIBLE hypotheses: `IsRealizedTwo` exports
    no high-scale norm bound and none of the `refold_aff`/`lowA2_small`
    continuity/square/radius data that `hiN_lowreg` needs.
* **NEXT TARGET (before B3 itself): widen `IsRealizedTwo`**
  (`LowRegApplyTwo.lean:90`) to export `Continuous FHi`, `hA2Hicont`, `hA2sq`,
  `hFComm`, the low radius `R` with `hreal`, and the forcing-norm cap — all six
  are already in scope at its single producer `lowreg_apply_two`.  That one-file
  edit makes B3 and §8.3 provable in place; B6 then extracts the order-free
  `hRepr` block of `deTurckRicci_solution_with_jointReg` into a named lemma.
* Risk-register outcome: Risk 3 mostly dissolved (`((2:ℕ):ℝ)` is *definitionally*
  `(2:ℝ)`, so the `MaxRegSolutionSpace` slot needs no transport at all; only
  `2+2` vs `4` needs `tensorHsCongr`, at one junction).  Risk 2 folded as
  planned, with a note that a prover may choose `R₀` from the mass majorant and
  so needs **no** horizon shrink there.  Risk 8.1 confirmed.
* Written 2026-08-02 by the front-2 recon pass.  No Lean edited, no file claimed.
* Buildable **now** down to the two named POSITs: B1 can land today with (A′)/(B′) as
  honest `sorry`s, and B2–B5 are then wiring against sorry-free machinery.
* Honest denominators: `(N)` (`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`)
  is **0 %** — unstated as a proof.  Its dedicated machinery ≈ 85 % (unchanged by this
  recon; the recon *re-scoped* front 2 from "build a ladder" to "wire an existing
  endpoint", which is a large de-risking but moves no mathematics).  Front 2 itself:
  the endpoint chain above the forcing package is ~90 % done and sorry-free; the
  forcing package at `a = 2` is **0 %**.  Whole HCG compactness project: low single digits.
