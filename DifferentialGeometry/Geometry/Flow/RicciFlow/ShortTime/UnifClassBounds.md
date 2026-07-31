# UnifClassBounds — Stage 0 engine-constant audit for black box (N)

Audit executed 2026-07-20 (Opus 4.8 executor) in worktree
`C:/Users/liao9/.codex/worktrees/e87b/...`, branch `codex/analytic-producers-e87b`.
Deliverable of Stage 0 of `UNIF_EXISTENCE_PLAN.md`. **No Lean edits.**

Task: trace the existence time `T` through the engine into the analytic stack, list
every `g₀`-dependent quantity it consumes (file / lemma / constant / bounding class
datum), fix the minimal jet order `A(n)` for the data-norm input, check that the
Lemma-3.11 producers exist at every `a ≤ A(n)`, and ratify or refute route R1.

---

## 0. Headline (lead finding — read before Stage 1)

**R1 (uniformize the existing engine) is still the correct strategic route, but its
Stage-1 AND Stage-2 scoping in the plan is wrong: the work is genuine new analysis,
not a `Λ`-threading rewiring, AND there is a second, deeper obstruction the plan did
not see.**

Two independent obstructions were found, both fatal to the plan as written:

1. **(Stage-1 premise is false.)** Every `g₀`-dependent scalar in the *explicit*
   part of the time, `T₀`, is a non-constructive `Classical.choose` of a `g₀`-intrinsic
   Sobolev-scale quantity (norm-equivalence constants `Ca·Cb`, Sobolev embedding radius
   `R₀`, Sobolev-multiplication constant `K`). There is **no explicit formula to thread
   `Λ` through** and **no pre-existing uniform cross-metric Sobolev layer**. Making them
   class-uniform = building that layer at order `A(n) = 4·finrank+12`. The plan's
   "Reuse the existing per-`g₀` producer proofs — the work is threading `Λ` through them,
   not new analysis" is factually incorrect.

2. **(The returned time is not `T₀`, and its extra caps have no floor.)** The engine
   does **not** return `T₀`. It returns
   `T₁ = min(T₀, d/2, d₂, d₂F)` from
   `maxreg_solution_jointly_smooth_representative_of_nemytskii`, whose conclusion is a
   bare `∃ T₁, 0 < T₁ ∧ T₁ ≤ T ∧ …`. Here `d` is a δ pulled from a **qualitative**
   `ContinuousWithinAt (timeH1.toFun u) … 0` (MaxRegSolutionJointlySmooth.lean:1138) —
   the time for the maximal-regularity solution to stay fibre-small near `t=0` — and
   `d₂, d₂F` are existential horizons from the forcing bootstrap. **None has a
   quantitative lower bound anywhere in the current API.** So even granting order-`A(n)`
   jets and uniform `C₁,C₂,‖Nfun 0‖`, the *returned* time still has no floor.

Consequence: R1 needs (a) a uniform cross-metric Sobolev-calculus layer at order
`A(n)` (Stage 1's real content), **and** (b) explicit, class-uniform time floors in the
joint-smoothness representative + forcing-bootstrap layer (a new frontier the plan's
Stage 2 assumed away). Neither exists. This matches — and sharpens — the
`ExtendViaUniqueness.md` 2026-07-18 audit line "still lacks uniform cross-metric Sobolev
constants … and same-horizon smoothing."

**Stage-1 producers were NOT written**: none of (e1)-(e4) can be landed sorry-free
against the current API, and CLAUDE.md forbids polished sorry-backed producer names that
masquerade as completed API. Awaiting planner acceptance of the re-scope (Stage 0 STOP
point per the plan).

---

## 1. The existence time, traced end to end

Engine `quasilinear_strictlyParabolic_2ndOrder_shortTimeExistence`
(`ShortTime/QuasilinearAbstractShortTimeExistence.lean`):

- line 113 `set T := min (quasilinear_maxreg_solution_of_nemytskii g₀ a Nfun hLipN H2).choose 1`.
  Since the maxreg time already satisfies `T₀ = min 1 (…)`, this `T = T₀`.
- line 166 `refine ⟨T₁, …⟩` — the **returned** time is `T₁ ≤ T₀`, obtained at line 163
  from `maxreg_solution_jointly_smooth_representative_of_nemytskii`.

### 1a. `T₀` — explicit Duhamel/fixed-point time
`quasilinear_maxreg_solution_of_nemytskii`
(`Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:701`), conclusion:

```
T₀ = min 1 (min (1 / (64·(C₂+1)²))
                ((1 / (16·(C₁+1)) / (2·(‖Nfun 0‖+1)))²))
```

with `C₁ = H2.choose`, `C₂ = H2.choose_spec.choose`, `‖Nfun 0‖` the zero-forcing norm
in `tensorHs g₀ 0 2 a`. **The Lipschitz constant `L` does NOT enter the time.** The
formula is antitone in `(C₁, C₂, ‖Nfun 0‖)` and pins `T₀` exactly (every `.choose`
witness equals it), so a class-uniform `(C₁≤C₁*, C₂≤C₂*, ‖Nfun 0‖≤D*)` would give a
positive `T₀`-floor — IF those three could be bounded (they can't yet; §2).

### 1b. `T₁` — actually returned time (caps `T₀`)
`maxreg_solution_jointly_smooth_representative_of_nemytskii`
(`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean:957`),
proof line 1141: `T₁ := min (min (min T (d/2)) d₂) d₂F`, conclusion exposes only
`0 < T₁ ∧ T₁ ≤ T`.

| cap | origin | line | floor available? |
|---|---|---|---|
| `T₀` | Duhamel formula (§1a) | — | explicit, but in un-bounded existential constants |
| `d/2` | `d` = δ of `ContinuousWithinAt (timeH1.toFun u) (Icc 0 T) 0` at tol `1/(2C)`, `C` from `ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy` | 1131-1138 | **NONE** (qualitative continuity δ; solution- and `g₀`-dependent) |
| `d₂` | `hHorizon` (engine `hForce` output = `deTurckRicci_forcingBootstrap_symm`) | 1140 | **NONE** (existential horizon) |
| `d₂F` | convolution/mass horizon (engine `hForce`) | 979 (hyp) | **NONE** (existential horizon) |

---

## 2. `g₀`-dependent quantities the time consumes (the audit table)

Producers wired by `deTurckRicci_solution_with_jointReg`
(`ShortTime/DeTurckInitialDataExistence.lean:148-162`), Sobolev order `a = 4·finrank+10`.

| # | quantity | where produced (file:line) | form | bounding class datum needed | uniform now? |
|---|---|---|---|---|---|
| e2 | `‖Nfun 0‖` = `‖deTurckSobolevNHa2Symm g₀ g_bg a 0‖` in `H^a_{g₀}` (≈ `-2Ric(g₀)`+conn. corr.) | def `SobolevNonlinearityExistence.lean:2783` | `H^a_{g₀}` norm of a Ric-order term | order-`(a+2)` = order-`A(n)` jets of `g₀` **in the `g₀`-spectral `H^a` norm** | **NO** |
| e3 | `C₂ = K·Csym1` | `..._mixed_lipschitz_pointwise_aux`, `SobolevNonlinearityExistence.lean:3322` (esp. 3371-3374) | product of `.choose`s | uniform `K`, `Csym1` | **NO** |
| e3 | `C₁ = K·Csym1·Csym2·(1 + 1/R₀)` | same, 3372-3373 | product of `.choose`s incl. `1/R₀` | uniform `K`, `Csym1`, `Csym2`, `R₀`⁻¹ | **NO** |
| — | `Csym1, Csym2` = `symmS` op-norm on `H^{a+1}, H^{a+2}_{g₀}` | `exists_norm_smoothCcToTensorHs_symmS_le`, `:2727` → `Ca·Cb` | `.choose` of `H^s`↔Σ‖∇ʲ·‖ norm-equiv constants (`:2731-2734`) | uniform `H^s`-vs-covariant-grad equivalence over class | **NO** |
| e1 | `R₀` = elliptic/contraction radius, `H^{a+2}→` fibre-small | `deTurckSobolevNHa2_exists_of_super`, `:2346` → `sobolevBall_smooth_fibreSmall_of_threshold :2175` | `.choose` | uniform `H^{a+2}→C⁰` Sobolev embedding | **NO** |
| e3 | `K` = ball-Lipschitz of `deTurckSmoothN` | `deTurckSmoothN_ballLipschitz_Ha2_dataWeighted_of_symm`, `:2050` → `smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm :2079` | `.choose` | uniform Sobolev multiplication (algebra) | **NO** |
| e1 | qualitative parabolicity `IsStrictlyParabolicMetricRHS` | `deTurckRicciRHS_isStrictlyParabolic_at_self`, `RHSStrictParabolic.lean:553` | proved ∀ `g₀` | none (qualitative; holds already) | yes (but does not floor the time) |
| e4 | forcing bootstrap → `d₂,d₂F,f,R₀'` horizons | `deTurckRicci_forcingBootstrap_symm`, `MaxRegSolutionJointlySmooth.lean:874` | existential horizons | uniform horizon floors (see §1b) | **NO** |
| — | `d` (near-initial fibre-smallness time) | `MaxRegSolutionJointlySmooth.lean:1131-1138` | δ of qualitative continuity | quantitative near-`t=0` stability rate, class-uniform | **NO** |

Every non-qualitative row is a `Classical.choose` of a `g₀`-intrinsic Sobolev-scale
quantity. The `_uniform` lemmas that exist in `Analysis/` are **single-metric**
chart-cover uniformity (e.g. `MeasureBridgeUniform`, `..._riemannianMeasure_uniform`),
NOT uniformity over a *class of metrics*. No cross-metric layer was found.

---

## 3. Minimal data-norm jet order `A(n)`

`Nfun : tensorHs g₀ 0 2 (a+2) → tensorHs g₀ 0 2 a`, `a = 4·finrank+10`. `‖Nfun 0‖`
lives in `H^a_{g₀}` and is a Ricci-order term (two derivatives of `g₀`). Bounding its
`H^a` norm needs `a+2` derivatives of `g₀`:

> **A(n) = a + 2 = 4·finrank + 12** (matches the plan's `A(n) ≈ 4n+12`).

Caveat that the plan did not flag: `A(n)` derivatives are needed **in the `g₀`-spectral
`H^a` norm**, whereas (N)'s hypothesis `MetricCovDerivOrderBoundOn` gives **pointwise
covariant** bounds w.r.t. `gBase`. Converting the latter to the former is itself part of
the missing cross-metric layer (§2), not a free `C^k ⊆ H^k` step.

---

## 4. Lemma-3.11 producers at `a ≤ A(n)` — order check

`MetricCovDerivOrderBoundOn K a h gRef C := ∀ x∈K, metricCovDerivNorm a h gRef x ≤ C`
(`HCGCompactness/AllTimesBounds.lean:691`) — order `a : ℕ` is a **free parameter, no cap
at 3**. `MetricCovDerivOrderBoundOnWindow` (`:773`) and `metricCovOrderWindow_of_pointwise`
(`:793`), `metricCovOrderWindow_of_evolution` (`:4415`) likewise take arbitrary `a`.

> **Input side OK:** the Lemma-3.11 producers exist and are stated at every `a ≤ A(n)`.
> Only (N)'s statement artificially caps at `a ≤ 3` (`ExtendViaUniqueness.lean:79`). The
> plan's proposed statement change (`a ≤ 3` → `a ≤ A(n)`) is well-supported on the input
> side and is necessary but **not sufficient** (§2 obstruction remains after the change).

---

## 5. Verdict

- **Time formula:** found and explicit for `T₀`; the *returned* time `T₁ ≤ T₀` is a
  min with three floor-less caps (`d/2, d₂, d₂F`).
- **T-determining constants:** `C₁, C₂, ‖Nfun 0‖` (explicit part), plus horizons
  `d, d₂, d₂F`. All non-qualitative ones are un-bounded existentials.
- **`A(n) = 4·finrank + 12`**, needed in the `g₀`-spectral `H^a` norm.
- **Lemma-3.11 producers exist at all `a ≤ A(n)`**; (N)'s `a ≤ 3` cap is the only block
  on the input side.
- **Route R1:** not refuted as a strategy, but **its Stage-1 (thread `Λ`) and Stage-2
  (expose `T ≥ φ`) are both under-scoped.** Real content = (i) a uniform cross-metric
  Sobolev-calculus layer at order `A(n)` (norm-equivalence, `H^{a+2}→C⁰` embedding,
  multiplication, symmetrization op-norm — all class-uniform); (ii) explicit class-uniform
  time floors for `maxreg_solution_jointly_smooth_representative_of_nemytskii` and the
  forcing bootstrap, including a quantitative near-`t=0` stability rate replacing the
  qualitative `d`.

### Smallest next machinery lemma (if planner ratifies R1 as a multi-session analytic lane)
A **class-uniform cross-metric `H^s` norm comparison** at order `s = A(n)`:
for `g₀` `Λ`-comparable to `gBase` with order-`A(n)` covariant jets bounded by `Λ`,
`‖·‖_{H^s_{g₀}} ≍_{Λ,n} ‖·‖_{H^s_{gBase}}`. Every constant in §2 (`Ca,Cb,K,R₀`) then
transfers from the FIXED `gBase` scale (where they are single existentials) to `g₀`
with `Λ`-controlled loss. Without it, none of (e1)-(e4) is landable.

### Route note for the planner
The cleaner long-run route may be to run the engine on a **fixed `gBase`-Sobolev scale**
(coefficients vary with `g₀`, function spaces fixed) rather than the current
`g₀`-intrinsic `tensorHs g₀` scale — that dissolves the cross-metric problem but requires
re-deriving the maximal-regularity engine on a fixed scale (large; overlaps R2's lane).
Recommend the planner weigh "uniform cross-metric layer (§5(i)) + quantitative-floor
layer (§5(ii))" vs "fixed-scale re-derivation" before Stage 1 is unblocked.

---

# UnifClassBounds.lean — brick E8a (the six-number refactor)

Written 2026-07-30.  `UnifClassBounds.lean` now exists (451 lines, sorry-free,
axiom-clean: only `propext / Classical.choice / Quot.sound`).  Note that §0–§5
above audit the **`a = 4n+10` engine** (`quasilinear_..._shortTimeExistence`),
whose horizon really does sit behind un-floored caps `d, d₂, d₂F`.  E8a is about
the **`a = 1` low-regularity solve** (`lowreg_partial_sol`), a *different*
endpoint whose horizon is the bare `partial_sol_tame` floor with no extra caps.
For that endpoint the six-number reduction is exact.

## What is in the file

Scalar layer (no manifold hypotheses at all — plain `ℝ` functions):

- `lowregOuterRad Ctop ρ P = min (ρ/2) (min (P/2) (1/(32*(Ctop+1))))` — the
  coefficient-freezing radius `Q` chosen at `LowRegDenseSolve.lean:339`.
- `lowregStateRad Ctop B1 ρ P = min (lowregOuterRad Ctop ρ P / 2) (1/(32*(B1+1)))`
  — the solver state radius `R` chosen at `:368`.
- `lowregHorizon Ctop B0 B1 D ρ P =`
  `min 1 (min (1/(64*(B0+1)^2)) ((lowregStateRad Ctop B1 ρ P / 4 / (2*(D+1)))^2))`
  — `partial_sol_tame`'s floor (`TameForcingFixedPoint.lean:483`) evaluated at
  `B = B0` and `R = lowregStateRad`.  This is `τ₀`.
- support lemmas: `_le_rho / _le_P / _le_cap / _pos / _small` for both radii
  (`_small` = the two contraction caps `Ctop*Q ≤ 1/16`, `B1*R ≤ 1/16`),
  `lowregHorizon_pos`, `lowregHorizon_le_one`, and the three monotonicity
  lemmas `lowregOuterRad_mono / lowregStateRad_mono / lowregHorizon_mono`
  (primed = worse inputs: larger `Ctop,B0,B1,D`, smaller `ρ,P` ⟹ smaller `τ₀`).

Geometry layer:

- `lowregRealRad` — restriction of a realization bound from radius `P` to
  `lowregStateRad` (thin wrapper on `realizeOfLE`; only needs `0 ≤ P`).
- `lowregNfun g₀ g_bg hδ hCtop hB1 hρ hP hreal` — the dense nonlinearity
  `lowRegN` on the state ball of the *closed* radius.
- `lowreg_partial_sol_of_bounds` — the endpoint.  Hypotheses: `hδ : δ < 1`,
  signs `0 ≤ Ctop, B0, B1`, `0 < ρ, P`, the realization bound at radius `P`,
  `hcont`, the three-arm tame estimate `htame` with coefficients
  `(Ctop * lowregOuterRad Ctop ρ P, B0, B1)`, and `hzero : ‖Nfun 0‖ ≤ D`.
  Conclusion: for every `0 < T ≤ lowregHorizon Ctop B0 B1 D ρ P` with `T ≤ 1`
  the Duhamel/max-reg solution exists, stays in
  `lowerState g₀ 1 (lowregStateRad Ctop B1 ρ P)`, and has
  `‖gforce‖ ≤ lowregStateRad Ctop B1 ρ P / 4`.
- `lowreg_bounds_exist` — the honest-input check: for every `g₀` (given
  `hDim : finrank = 3` and a realization bound at radius `P`) the existing
  producers `lowRegN_outer` do supply `Ctop, B0, B1, D, ρ` satisfying every
  hypothesis above.  So the refactor recovers `lowreg_partial_sol` with the
  opaque `∃ T₀` replaced by the closed `lowregHorizon`.

## Design decisions (and why)

1. **`δ` is a parameter, not `deTurckArmContractionThreshold''`.**  The
   original fixes `δ = θ(n)` only because its private `realize_at_thr` produces
   exactly that.  Since the realization bound is now a hypothesis, keeping `δ`
   generic costs nothing; Lane E instantiates `δ := θ(n)`, which is
   dimension-only and therefore already class-uniform.
2. **`R` is closed, not chosen.**  The original picks
   `R = min (Q/2) (1/(32*(B1 Q + 1)))` at the *actual* `B1 Q`.  Taking `R` at
   the *bound* `B1` is still admissible (`B1 Q ≤ B1` and
   `R ≤ 1/(32*(B1+1))` still give `B1 Q * R ≤ 1/32 ≤ 1/16`), so the state
   radius becomes class-uniform too — which E8b needs, since `‖gforce‖ ≤ R/4`.
3. **`htame` is stated at the two specific radii**, not `∀ Q ≤ ρ`.  Weakest
   hypothesis, and it is what makes `lowreg_bounds_exist` provable: an
   `∀ Q ≤ ρ` form would need `B0' Q ≤ B0` for every admissible `Q`, which the
   producer does not give (`B0', B1'` are arbitrary functions of `Q`).
4. **`hD : 0 ≤ D` dropped** — it follows from `hzero` by `norm_nonneg`.
   `Continuous (coreN …)` dropped from both hypotheses and conclusion — it was
   only carried through the original statement and has no Lean consumer.
5. **`hDim : finrank = 3` is NOT needed** by `lowreg_partial_sol_of_bounds`
   (only by `lowreg_bounds_exist`, which calls the producer).

## Deviation from the brick spec

The spec said "the proof body is the existing one with the obtains replaced by
the hypotheses".  That is what happened, with one addition: `lowreg_bounds_exist`
was written as well, so that the parameterization is *checked* against the live
producers rather than merely asserted.  The one thing that could **not** be done
in this file is re-deriving `lowreg_partial_sol` itself: its realization input
comes from `realize_at_thr`, which is `private` in `LowRegDenseSolve.lean`.
`lowreg_bounds_exist` therefore takes the radius-`P` realization bound as a
hypothesis instead.  If Lane E wants a literal `lowreg_partial_sol` corollary,
the smallest fix is to drop `private` from `realize_at_thr` (it is already the
statement "`P = θ/Cop` works"), which is also the natural home for E's lower
bound on `P`.

## What Lane E must now produce (E1–E7 ⟹ E8b)

Six class-uniform numbers, nothing else:

| number | direction | current producer | file |
|---|---|---|---|
| `Ctop` | upper | `lowRegN_outer` ⟵ `coreN_tame` ⟵ `rem_h1_tame` | `LowRegCoreTame.lean:104` |
| `B0`   | upper | same (`B0 Q = Clow + Ccoef*(Z0+O0)`) | same |
| `B1`   | upper | same (`B1 Q = Ccoef*(Z1+O1)`) | same |
| `D`    | upper | `‖lowregNfun … 0‖` = `H¹` norm of the DeTurck nonlinearity at `0` | — |
| `ρ`    | lower | `lowRegN_outer` | `LowRegDenseSolve.lean:188` |
| `P`    | lower | `realize_at_thr`, `P = θ(n)/Cop` | `LowRegDenseSolve.lean:43` |

Then `lowregHorizon_mono` + `lowregHorizon_pos` give the uniform `τ₀ > 0`.

## Verification

Focused check green; targeted module build
`+…ShortTime.UnifClassBounds` green (whole 9670-job dependency closure built,
0 errors, no warnings attributable to this file); `#print axioms` on
`lowreg_partial_sol_of_bounds`, `lowreg_bounds_exist`, `lowregHorizon_pos`,
`lowregHorizon_mono` shows only `propext, Classical.choice, Quot.sound`.

## Lean lessons

- `rw [hT₀eq, hBcoe]` leaves `lowregHorizon … = min 1 (…)`; `rw`'s trailing
  `rfl` runs at reducible transparency and does **not** unfold a plain `def`.
  An explicit `rfl` tactic (default transparency) closes it.  Worth remembering
  whenever a closed-form `def` has to be matched against an engine's exported
  equation.
- Realization bounds (`gFibreOpBound …`) are `Prop`, so `lowRegN g₀ g_bg hR hδ
  hreal` is definitionally independent of *which* proof is supplied.  That is
  what lets `lowreg_bounds_exist` discharge `hcont`/`htame` by a bare `exact`
  against the producer's output even though the producer builds its realization
  via `realizeOfLE` and the statement builds it via `lowregRealRad`.

## Status
- 2026-07-20: Stage 0 audit COMPLETE. Stage 1 NOT started (blocked; see §0/§5). STOP for
  planner acceptance of the re-scope. No `.lean` written (no sorry-free producer exists).
- 2026-07-24: the R1τ item-6 narrow class-uniform packet (the §5 "smallest next machinery
  lemma" made narrow to 3 orders) is reconnoitred in `ShortTime/UNIF_ITEM6_RECON.md` — spine
  S1 = the `Λ`-uniform `g₀`-side spectral↔covariant Gårding constant (`DirichletSpectralBochnerGap`
  re-derivation; the one HARD level, no high-order min-max transfer), with S0/S1b/S2/S3/S4
  routine-to-medium and inheriting it.
- 2026-07-30: brick E8a DONE — UnifClassBounds.lean written (lowregOuterRad /
  lowregStateRad / lowregHorizon + lowreg_partial_sol_of_bounds +
  lowreg_bounds_exist), sorry-free, targeted module build green.  Lane E's
  remaining work is now exactly 'bound six numbers'; see the E8a section above.
