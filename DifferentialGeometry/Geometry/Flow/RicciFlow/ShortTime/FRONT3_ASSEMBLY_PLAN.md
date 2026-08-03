# FRONT 3 — the class-uniform `τ₀` assembly plan for black box (N)

Read-only recon, 2026-08-03.  Companion to `LOWREG_BOOTSTRAP_PLAN.md` (front 2)
and `FORCEJETMASS_PLAN.md` (front 2's leaf).  Nothing here is build-verified:
no Lean was edited, no file claimed, no Lake process run.

Anchor ledger: `UNIF_EXISTENCE_PLAN2.md` (entries No. 70+).  Prior recorded
state for this exact job: `UnifClassBounds.md` §"What Lane E must now produce
(E1–E7 ⟹ E8b)" — front 3 IS that section, finished and re-measured.

---

## 0. Headline

**The class layer is not missing; it is written and half-instantiated.**
`UnifClassBounds.lean` already re-states the whole low-regularity solve as a
function of **six real numbers** and proves the horizon monotone in them
(`lowregHorizon_mono`, `:186`).  Its own docstring (`:395–397`) says verbatim:

> Making the horizon class-uniform is exactly the problem of bounding these five
> numbers (and `P` from below) uniformly over a class of metrics.

Two of the six (`D`, `P`) are **already closed formulas in `(gBase, Λ, n)`** with
proved producers.  Three (`Ctop, B0, B1`) plus `ρ` are individual but sit on
`_of_jets`-shaped producers whose inputs are exactly the `Λ`-class currency.  One
constant — `‖staticForce g g 2‖` inside `lowregFloorHorizon` — needs covariant
`2`-jets of the static DeTurck field, i.e. metric jets to order **4**, which
**exceeds (N)'s own `∀ a ≤ 3` hypothesis budget** (`ExtendViaUniqueness.lean:85`).
That is front 3's one genuine design decision.

**Two campaign narratives are refuted by measurement in this pass** (instances
nine and ten of the standing over-count):

1. **The Weyl citation-sorry is NOT on (N)'s dependency path.**  Import closure
   over the whole tree: `weyl_pointwise_diagonalKernel_bound_of_closed`
   (`WeylEigenvalueCountingBound.lean:115`) is reachable from exactly **three**
   modules — `RealizeTransport`, `SolutionC2Continuous`, `DeTurckRicciPde` — and
   **none** of them is in the import closure of `LowRegAllOrderJet`,
   `LowRegApplyTwo`, `UnifNZeroBound`, `UnifRealizeRadius`,
   `DeTurckInitialDataExistence`, `ShortTimeExistence`, `ConjugatingDiffeoFamily`
   or `ExtendViaUniqueness`.  §6.
2. **The docstring's "finite chart-centre family `S`" is not in (N)'s statement.**
   (N) quantifies `∀ (x₀ : M)` (`ExtendViaUniqueness.lean:87`), and the engine's
   `JointChartGramSmooth` (`DeTurckChartRegularityFromJoint.lean:85–90`) is
   `∀ (α : M)` on the **closed** `Icc 0 T`.  No good-set atlas is needed; the
   docstring is aspirational prose and should be corrected, not implemented.  §5.

---

## 1. The contract, verbatim

`theorem ricci_flow_unif_existence` — `Evolution/ExtendViaUniqueness.lean:80`,
`sorry` at `:98`.  For a fixed `gBase`:

```
∀ Λ, 1 ≤ Λ → ∃ τ₀, 0 < τ₀ ∧
  ∀ g₀ : SmoothRiemannianMetric I M,
    (∀ x v, Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ Λ * gBase.inner x v v) →      -- (i)  :83–84
    (∀ a : ℕ, a ≤ 3 → MetricCovDerivOrderBoundOn Set.univ a g₀ gBase Λ) →  -- (ii) :85
    ∃ rr : ℝ → SmoothRiemannianMetric I M, rr 0 = g₀ ∧
      (chart-Gram jointly C∞ on Ico 0 τ₀ ×ˢ baseSet, ∀ x₀ i j)   -- :87–90
    ∧ (chart-Gram ContinuousOn same slab)                        -- :91–94
    ∧ (∀ t ∈ Ico 0 τ₀, HasDerivWithinAt … (-2 * ricciTensor (rr t) x v w) (Ici 0) t)  -- :95–97
```

Note the ORDER: `∃ τ₀` precedes `∀ g₀`.  Everything else — `rr`, its fields — is
per-`g₀` and may stay existential.

---

## 2. Production map — the single-metric chain as it stands

`lowreg_solve_two` (`LowRegApplyTwo.lean:723`) with proof-body citations:

| line | call | reports |
|---|---|---|
| `:744` | `refold_aff hDim g` | `ρA`; then `hpack` at `:788` gives `Z, L, FHi, FLo` |
| `:745` | `realize_at_thr hDim g` | `Pr` (realization radius at the DeTurck threshold) |
| `:746` | `lowRegN_outer hDim g g hδ0 hδ` | `ρN, CtopN, B0N, B1N` |
| `:760` | `radialA2_lip hDim g hcap …` | `ρL, CL` |
| `:768` | `lowA2_small hDim g hρL …` | `ρ, C` (second-order smallness `‖lowA2‖ ≤ C·ρ`) |
| `:792` | — | `B2 := C * ρ` (the reported contraction floor) |
| `:797` | — | `P := min (min ρ ρN) ((1-c)/(6*(L+1)))` |
| `:807` | `lowreg_bounds_exist hDim g g hδ0 hδ hPpos hrealP` | `Ctop, B0, B1, D, ρout` |
| `:816` | — | `T₀ := min (min (lowregHorizon Ctop B0 B1 D ρout P) (lowregLiftHorizon' c Z)) (lowregFloorHorizon g c Kf)` |

Above it: `lowreg_joint_two` (`LowRegAllOrderJet.lean`, `:1661` at the time of
writing) runs `lowreg_solve_two` at `Kf := 1/(4·C₂)` and returns the (N)
`rr`-field shapes — `F 0 = 0`, `Ico`-slab PDE against a caller-supplied `F_RHS`,
and `JointChartGramSmooth T (fun t => tensorSectionRealizeMetric g (F t) …)` —
modulo the frontier `lowreg_forceJetMass` (`:1070`) and the routine `hRepr`.

> **Line-number caveat.**  `LowRegAllOrderJet.lean` is under active edit by the
> front-2 implementation lane; its line numbers moved during this pass
> (`lowreg_joint_two` 1676→1661, `lowreg_forceJetMass` 1068→1070, and a
> restated `(S1₂)` frontier appeared near `:973`).  **Cite it by declaration
> name, never by line.**  Every other file cited in this plan is stable.

Closed scalars (`UnifClassBounds.lean`): `lowregOuterRad` `:71`, `lowregStateRad`
`:77`, `lowregHorizon` `:83`; `lowregHorizon_pos` `:156`, `lowregHorizon_mono`
`:186`.  Consumer `lowreg_partial_sol_of_bounds` `:263` takes the six numbers as
HYPOTHESES — it is already class-shaped and needs no change.

---

## 3. Constant genealogy — the (A)/(B)/(C) split

### (A) Already class-uniform: closed in `(gBase, Λ, n)`, producer exists

| constant | closed form | producer |
|---|---|---|
| `D` | `nZeroC Ksup Λ volBase n` (`UnifNZeroBound.lean:417`) | `nZero_lowregNfun` `:551` (⟸ `staticN_h1_le` `:430`, `nZero_unif` `:526`) |
| `Ksup` (input to `D`) | `ksupZeroC + ksupOneC` | **`unifKsupLeOne`** (`UnifDeTurckRHSOne.lean:1538`) — the model `∃ Kstar` BEFORE `∀ g₀` |
| `P` | `unifRealizeRad Cpt Fc d = θ(d)/hs2OpC Cpt Fc d` (`H2PointwiseUnif.lean:346`) | `realize_at_unif` `:360`, `unifRealizeRad_pos` `:349`, `hs2_op_bound_unif` `:278`; horizon consequence `lowregHorizon_unif_pos` (`UnifRealizeRadius.lean:43`) |
| `Cpt` (input to `P`) | `morreyUnifConst Λ (baseMorreyConst gBase 0 s) Kjet n s` | **`fibreMorrey_unif_base`** (`SobolevEmbeddingUnif.lean:350`), general form `:240` |
| `Fc` (input to `P`) | curvature-jet family at `gBase` | `exists_rmJetSups` / `unifRmSecSup` (`UnifCurvaturePack.lean:292`, `:326`) |

**Stale-doc correction:** `H2PointwiseUnif.lean:31` still says "brick E4 is not
landed".  It IS landed — `fibreMorrey_unif_base` exists and is exactly the
`hmorrey` slot in constant-exposed form.  Only its `Kjet` (the `gBase`↔`g₀`
covariant-jet transfer constant) remains an abstract input; that is a (B) item,
not a hole.

### (B) Individual, but bounded through hypotheses (i)+(ii); constant-exposed sibling NOT yet written

| constant | current producer | why class-bounded |
|---|---|---|
| `Ctop`, `B0 Q`, `B1 Q`, `ρ` | `lowRegN_outer` (`LowRegDenseSolve.lean:188`) ⟸ `coreN_outer` `:115` ⟸ `rem_h1_tame` (`LowRegCoreTame.lean:104`) ⟸ `rem_h1_of_jets` (`LowRegRemainderH1.lean:183`) + `rhs0_path_tame` `:62` + `rhs1_path_tame` | the name is the route: the constants are built from **covariant-jet envelopes** of `(g₀, g_bg)` — the same currency `unifRmJetOne` / `unifKsupLeOne` / `UnifCurvaturePack` already deliver from (i)+(ii) |
| `Z`, `L` | `refold_aff` (`LowRegBgA1Refold.lean:331`) = `c0_pack g` (`LowRegBgC0Time.lean:322`) + `c1_bg_pack g gB` (`LowRegBgC1Time.lean:763`) | same; `c1_bg_pack` **already carries an arbitrary background `gB`** |
| `C` (and hence `B2 = C·ρ`, and the admissible contraction level `c`) | `lowA2_small` (`LowRegOperatorTime.lean:668`) ⟸ `radialA2_lip` (`DeTurckRemainderLowBaseTimeA2.lean:370`) | `‖lowA2‖ ≤ C·ρ` is monotone in `ρ`: a class-uniform upper `C*` plus a class-uniform `ρ*` makes `B2*` as small as wanted, then `c := max B2* (1/2)`; `lowregHorizon` only *decreases* with `ρ`, so shrinking is free |
| `Kjet` | (input of `fibreMorrey_unif_base`) | pure `MetricCovDerivOrderBoundOn` content of (ii) |

These are brick **E7** of `UnifClassBounds.md`'s table.  They are the BULK of
front 3's work but contain no new mathematics beyond re-exposing constants that
the existing proofs already build from jet envelopes.

### (C) Genuinely individual, no class route visible

1. **`‖staticForce g g 2‖` inside `lowregFloorHorizon`** (`LowRegApplyTwo.lean:228–231`):
   ```
   lowregFloorHorizon g c Kf = Kf * (1 - c) / (4 * (‖staticForce g g 2‖ + 1))
   ```
   `staticForce g₀ g_bg σ = smoothCcToTensorHs g₀ σ (deTurckRHSSection g_bg g₀)`
   (`LowRegLiftNTerm.lean:142`).  An UPPER bound on the `σ = 2` spectral norm gives
   the LOWER horizon bound we need — the direction is right — but the `H²` norm
   consumes covariant `j ≤ 2` jets of `deTurckRHSSection`, i.e. an
   `unifKsupLeTwo`, i.e. metric jets to **order 4**.  (N)'s budget is `∀ a ≤ 3`
   (`ExtendViaUniqueness.lean:85`), and No. 97 already ruled that the `a = 1`
   curvature envelope consumes all three.  **Design decision required** (§8, R1).
2. **The DeTurck-background hard-wiring `g_bg := g₀`.**  Every class-uniform
   producer is stated at `g_bg := gBase` — `nZero_unif`'s docstring
   (`UnifNZeroBound.lean:29–32`) says so explicitly ("this is where the ratified
   instantiation `g_bg := gBase` matters: only the two metrics `g₀` and `gBase`
   of the `Λ`-class enter `N(0)`"), and `unifKsupLeOne` is literally about
   `deTurckRHSSection gBase g₀`.  The refold packet is now widened —
   `refold_aff_bg g gB` (`LowRegBgA1Refold.lean:345`) on `oneCoreBg g gB`
   (`:56`), brick G1 DONE 2026-08-03, with the single-metric `refold_aff` kept
   as its diagonal (`:488`) — but `lowreg_solve_two` still calls
   `lowRegN_outer … g g` (`:746`) and `lowreg_bounds_exist … g g` (`:809`).
   Widening the rest is **mechanical but load-bearing**: without it, none of
   (A) applies.  Brick G2.
3. **`lowreg_forceJetMass`** (`LowRegAllOrderJet.lean`, front 2's frontier).  It
   is a front-3 PRECONDITION, not a front-3 item: its conclusion is qualitative
   (`∃ C_σ` per metric), so a per-metric proof costs front 3 nothing extra.

---

## 4. The quantifier restructuring (the design, in five sentences)

The `g₀`-spectral machinery — `tensorHs g₀ 0 2 σ`, `metricH3 g₀`,
`SmoothCcTensor g₀ 0 2`, the eigenbasis, `MaxRegSolutionSpace` — is indexed by
`g₀` and **must not** be hoisted; nothing in (N) asks it to be, because (N) only
demands one real number before `∀ g₀`.  What must be hoisted is exactly the ten
plain reals `Ctop, B0, B1, D, ρ, P, Z, L, C, Kf`, all of which live in `ℝ` and are
independent of the `g₀`-indexed spaces.  So the target is a strict
`unifKsupLeOne`-shaped restatement — `∃ (reals), ∀ g₀, (i) → (ii) → (the per-g₀
producer conclusions hold at those reals)` — and the natural name is
**`lowreg_bounds_unif`**, the `∃`-before-`∀` sibling of `lowreg_bounds_exist`
(`UnifClassBounds.lean:384`), followed by **`lowreg_solve_unif`**, the sibling of
`lowreg_solve_two` reporting `τ₀ := lowregHorizon Ctop* B0* B1* D* ρ* P*` chosen
before `∀ g₀`.  The engine below needs **zero change**: `lowreg_partial_sol_of_bounds`
(`:263`) already takes the six numbers as hypotheses, and `lowregHorizon_mono`
(`:186`) + `lowregHorizon_pos` (`:156`) convert class bounds into the single
positive floor — which is precisely what `UnifClassBounds.lean` was built for and
never wired.

---

## 5. The S-atlas and the `rr` packaging — the gap IS only packaging

**Atlas: nothing to do.**  (N) `:87` quantifies `∀ (x₀ : M)`;
`JointChartGramSmooth T g_DT` (`DeTurckChartRegularityFromJoint.lean:85–90`) is
`∀ (α : M) (i j), ContMDiffOn … (Icc 0 T ×ˢ baseSet_α)` — every centre, and the
CLOSED slab, i.e. strictly stronger than `Ico 0 τ₀`.  Conjunct 2 (`ContinuousOn`)
is `.continuousOn` of conjunct 1.  The `(N)` docstring's finite family `S`
(`:63–65`) has no counterpart in the statement; correct the docstring.

**Metric anchoring.**  `rr t := tensorSectionRealizeMetric g₀ (F t) hδ_lt (hδ' t)`
(`Analysis/…/MetricRealization/TensorHsRealize.lean:460`), whose defining simp
lemma is `tensorSectionRealizeMetric_inner` `:469`:
`(…).inner x v w = g.inner x v w + ccTensorBilinSymm g T x v w`.
`rr 0 = g₀` follows from `F 0 = 0` via `realizeMetric_zero`
(`UnifNZeroBound.lean:185`) plus `smoothRiemannianMetric_ext_inner`
(`DeTurckRealizedSolutionFamily.lean:100`); the pattern is already run at
`QuasilinearAbstractShortTimeExistence.lean:167`.

**The PDE conjunct is the only real assembly step, and its template is verbatim.**
`lowreg_joint_two` gives the **DeTurck** PDE (`F_RHS := deTurckRicciRHS gBase`,
pinned by `hRepr`); (N) demands `-2 Ric`.  The conversion is the existing
Hamilton–DeTurck conjugation, and it is **horizon-preserving**:
`conjugating_diffeo_family_jointsmooth` (`ShortTimeAssembly/ConjugatingDiffeoFamily.lean:78`)
closes at `:127` with `refine ⟨T_DT, hDT, le_refl _, …⟩` — `T = T_DT`, no shrink.
`short_time_joint` (`ShortTimeExistence.lean:72`) is the finished, sorry-free
assembly of exactly (N)'s three conjuncts from
`(IsQuasilinearMetricParabolicSolution, JointChartGramSmooth)`, and every step in
its body takes the background `g_bg` as a parameter (`conjugating_flow_flat_data
g_DT g_bg …`, `conjugating_flow_t0_continuity_data …`,
`ricci_flow_pde_at_zero`), so `g_bg := gBase` goes through.  The route is
therefore: `lowreg_joint_two` (at `gBase`, at `τ₀`) →
`deTurckRicci_chartRegularity_of_jointChartGramSmooth`
(`DeTurckChartRegularityFromJoint.lean:701`, six-conjunct tail, sorry-free) →
`conjugating_diffeo_family_jointsmooth` → `short_time_joint`'s body.

---

## 6. The Weyl policy — MEASURED OFF THE PATH

Method: transitive import closure over all `DifferentialGeometry/*.lean`.
`weyl_pointwise_diagonalKernel_bound_of_closed` (`WeylEigenvalueCountingBound.lean:115`)
is reachable from **exactly three** modules in the tree —
`ShortTime/RealizeTransport` (consumes it at `:90` and `:118`),
`ShortTime/SolutionC2Continuous`, `ShortTime/DeTurckRicciPde`.  Measured
`Weyl ∈ closure?` on the front-2/front-3 path: `LowRegAllOrderJet` **False**,
`LowRegApplyTwo` **False**, `UnifNZeroBound` **False**, `UnifRealizeRadius`
**False**, `UnifDeTurckRHSOne` **False**, `DeTurckInitialDataExistence` **False**,
`MaxRegSolutionJointlySmooth` **False**, `DeTurckRealizedSolutionFamily` **False**,
`ShortTimeExistence` **False**, `ConjugatingDiffeoFamily` **False**,
`ExtendViaUniqueness` **False**.

Root cause of the stale narrative: the smooth-representative gate used to need
Weyl and was **re-proved Weyl-free** — `spectralSmoothRealizesAsSmooth_holds`
(`HeatSemigroup/SpectralSmoothRepresentativeRealize.lean:478`), docstring
`:466–477`: "No Weyl eigenvalue-counting / heat-trace input enters."  Every
front-2 consumer goes through that gate, not through `RealizeTransport`.

**Recommendation.**
* **Do not** thread a named Weyl hypothesis into (N)'s statement.  It would be a
  fake frontier — a polished public assumption the proof never uses — exactly
  what the project rules forbid.
* **Do not** commission a discharge.  The estimate is a full local-Weyl-law
  development (on-diagonal reproducing-kernel asymptotics for the tensor
  connection-Laplacian); weeks-to-months, and it buys (N) nothing.
* **Do** correct the two stale self-descriptions: `WeylEigenvalueCountingBound.lean:59–61`
  ("the only `sorry` on the short-time-existence dependency path") and
  No. 97's ADDENDUM item 2 ("IT IS on the path").  Both pre-date the Weyl-free
  gate.  Leave the `sorry` as a cited classical input serving the three legacy
  realize modules.
* **Honest caveat.**  Import closure is a sound over-approximation of module
  reachability, not of axiom use.  The definitive check is `#print axioms` on the
  finished (N), which a read-only pass cannot run.  Record it as the acceptance
  gate for the final brick.

---

## 7. Bricks (ordered)

**G1 — background widening of the refold packet.**  **DONE 2026-08-03 (GREEN).**
`oneCoreBg g gB` (`LowRegBgA1Refold.lean:56`), `oneCore g := oneCoreBg g g`
(`:71`), `refold_aff_bg hDim g gB` (`:345`) routing `c0_pack g` (background-free)
+ `c1_bg_pack g gB` (`LowRegBgC1Time.lean:763`, already two-metric), and
`refold_aff hDim g` (`:488`) kept as a theorem whose statement is
**byte-identical** to the old one, proved term-mode by `refold_aff_bg hDim g g`
— a diagonal *instance*, not a redefinition, because the packet's conclusion is
carried as a hypothesis by seven downstream theorems that all name `oneCore` in
their statements.  Gate passed with zero downstream edits: focused checks of
`LowRegLiftAffine` (only direct importer), `LowRegLiftHfLo` and `LowRegApplyTwo`
(the `refold_aff` call site, `:744`) all green.  The predicted failure signal —
a `g g`-dependent `rfl` in the `a1Lo_congr` layer — did not appear
(`a1Lo_core_any`, `a1_comm_any` are background-agnostic), so G2's "routine but
wide" estimate stands.  Report: `UNIF_EXISTENCE_PLAN2.md` №101.

**G2 — background widening of the solve chain.**  Thread `g_bg` through
`IsRealizedTwo` (`LowRegApplyTwo.lean:107`), `lowreg_apply_two` (`:342`),
`lowreg_solve_two` (`:723`), `lowreg_joint_two` (`LowRegAllOrderJet.lean`):
replace the `g g` at `:746` and `:809` by `g gB`.  Nothing mathematical moves —
`lowRegN`, `coreN`, `deTurckSmoothN`, `lowreg_bounds_exist` are all already
two-metric.  *Routine but wide (two of the largest files); coordinate with the
sibling agent holding `LowRegAllOrderJet.lean`.*

**G3 — `lowreg_bounds_unif`: the E7 packet.**  `∃ Ctop* B0* B1* ρ*` before
`∀ g₀`, discharging `lowreg_bounds_exist`'s conclusion at those numbers from (i)
+ (ii).  Work backwards through `lowRegN_outer` → `coreN_outer` → `rem_h1_tame`
→ `rem_h1_of_jets` / `rhs0_path_tame` / `rhs1_path_tame`, replacing each `∃ C`
by a closed formula in `(Λ, gBase-jets, n)` in the `UnifCurvaturePack` currency.
*API-gap; the bulk of front 3.  Expect one constant-exposed sibling per producer,
mirroring how `hs2_op_bound` → `hs2_op_bound_unif` was done.*

**G4 — `Kjet` and `C*` discharge.**  The jet-transfer constant of
`fibreMorrey_unif_base` and the `lowA2_small` contraction constant, from (ii).
Then `P* := unifRealizeRad Cpt* Fc* n` and `c* := max (C*·ρ*) (1/2)`.  *API-gap.*

**G5 — the `lowregFloorHorizon` ruling.**  Either (a) an `unifKsupLeTwo` (needs
`a ≤ 4` in (N)'s hypotheses — a change to (N)'s own statement, user decision), or
(b) re-derive the forcing floor against a `σ ≤ 1` norm so `nZeroC` suffices, or
(c) fold `Kf` differently so `staticForce` never enters the horizon.  *Design.*

**G6 — `lowreg_solve_unif` + the (N) endpoint.**  `τ₀ := lowregHorizon …` by
`lowregHorizon_mono`/`_pos`; then §5's four-step assembly.  Acceptance:
`#print axioms ricci_flow_unif_existence` shows only
`propext, Classical.choice, Quot.sound` (plus, until front 2 closes,
`lowreg_forceJetMass`).  *Wiring.*

---

## 8. Risk register

**R1 (HIGH, design) — the `∀ a ≤ 3` budget vs `lowregFloorHorizon`.**
`LowRegApplyTwo.lean:228–231` puts `‖staticForce g g 2‖` in the horizon; bounding
it uniformly needs `Ksup` at `j ≤ 2`, hence metric jets to order 4, hence a
change to `ExtendViaUniqueness.lean:85`.  No. 97 already flagged the budget as
fully consumed by the `a = 1` envelope.  Mitigation: attack (b)/(c) of G5 before
proposing a statement change; `staticForce_incl` (`LowRegLiftNTerm.lean:150`)
lowers the order but in the wrong direction for a norm bound, so (b) is a real
estimate, not a rewrite.

**R2 (MEDIUM, API-gap) — G3 is a producer sweep, not one lemma.**  `rem_h1_tame`
(`LowRegCoreTame.lean:104`) obtains `ρ, Ctop, Clow, Ccoef` from `rem_h1_of_jets`
(`LowRegRemainderH1.lean:183`) and `Z0/Z1/O0/O1` from two path-tame producers
(`:62`, and `rhs1_path_tame`), each of which is itself an `∃ C`.  Every one needs
a constant-exposed sibling.  Mitigation: do them in dependency order, deepest
first; the `hs2_op_bound → hs2_op_bound_unif` pair is the worked template.

**R3 (MEDIUM, coordination) — G2 touches files under active edit.**
`LowRegAllOrderJet.lean` and `LowRegApplyTwo.lean` are owned by the front-2
implementation lane right now.  Mitigation: land G1 (a different file) first,
and claim G2's files only after front 2's leaf lands.

**R4 (LOW–MEDIUM, verification) — import closure ≠ axiom closure.**  §6's Weyl
verdict is a static reachability argument.  Mitigation: make `#print axioms` on
the finished endpoint the acceptance gate of G6; if Weyl reappears, the culprit
will be a NEW import added during G2/G6, and the fix is to route around
`RealizeTransport` rather than to adopt the sorry.

---

## 9. Stop-signal — what would make front 3 a genuine route error

Only this conjunction: **G3 stalls because some `_of_jets` producer's constant
provably depends on `g₀`-data of order > 3 that (ii) cannot bound**, AND G5's
options (b)/(c) both fail, so `lowregFloorHorizon` also demands order 4.  That
conjunction means the low-regularity horizon is genuinely a function of jets
beyond (N)'s budget, i.e. the `a = 2` re-base cannot serve (N) and either (N)'s
hypotheses must be raised to `∀ a ≤ 4` or the whole front-2 route is
mis-targeted.  Either failure alone is not a stop: G3 alone is an API sweep, G5
alone is a bounded design decision.

---

## 10. Builder brief — FIRST DISPATCHABLE BRICK (G1) — **EXECUTED 2026-08-03, GREEN**

*(Kept verbatim below as the record of what was dispatched.  Outcome: as
predicted, except that `refold_aff` was preserved as a diagonal **instance
theorem** with a byte-identical statement rather than redefined, which is what
made the "no downstream call site changes" claim literally true.  See §7 G1 and
`UNIF_EXISTENCE_PLAN2.md` №101.)*


*File:* `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegBgA1Refold.lean`
(not held by the sibling lane).

*What exists:* `oneCore` (`:54`) is `LowBaseActionData g` with
`C1 := (lowCoreDataBg g g hρ hδ0 hδ_le hreal T).C1`, `C0 = C2 = 0`.  `refold_aff`
(`:331`) takes one metric and internally runs `c0_pack g` (`LowRegBgC0Time.lean:322`,
background-free) and `c1_bg_pack g g` (`LowRegBgC1Time.lean:763`, which ALREADY
takes `(g gB)`).

*Do:* add `oneCoreBg g gB … := (lowCoreDataBg g gB …).C1` and
`refold_aff_bg (hDim) (g gB)` with the same conclusion shape as `refold_aff`
(`∃ ρ0 > 0, ∀ ρ ≤ ρ0 …, ∃ Z L FHi FLo, continuity + core identities + affine
growth + the inclusion square`), proved by `c0_pack g` + `c1_bg_pack g gB`
exactly as `refold_aff`'s body does from `:376` (`refine ⟨ρ0, hρ0, ?_⟩`) on.
Redefine
`oneCore g := oneCoreBg g g` and `refold_aff := refold_aff_bg … g g` so no
downstream call site changes.

*Verify:* focused check of `LowRegBgA1Refold.lean` only
(`scripts/lake-locked.ps1 check … -NoLakeLock`).  No targeted build needed unless
a downstream file reads the new names.

*Success:* file green, `refold_aff` still typechecks at every existing call site
(`LowRegApplyTwo.lean:744`).  *Failure signal:* if `lowCoreDataBg`'s two-metric
slot turns out to be used at `g g` for a reason (e.g. a `rfl`-level identity in
`a1Lo_congr`), stop and report — that would mean the background widening is not
mechanical and G2's cost estimate is wrong.

---

## 11. Honest denominators

* `ricci_flow_unif_existence` (**(N)**, `Evolution/ExtendViaUniqueness.lean:80`,
  sorry `:98`): **0%** — stated, not one line of proof.  Unchanged by this pass.
* **Front 3** (this plan's scope — the class-uniform `τ₀` layer + the (N)
  assembly): **~28%** of its own machinery, and almost all of that number is
  inherited, not earned here.  Earned: `D` and `P` closed with proved producers,
  `E4` landed, the six-number engine and its monotonicity written, the
  conjugation measured horizon-preserving, the atlas requirement and the Weyl
  requirement both eliminated, and (2026-08-03) **G1 built** — the smallest of
  the six bricks, one file, no mathematics moved.  Missing: G2–G6, i.e. the
  entire E7 sweep and the R1 ruling.
* **Front 2** (`lowreg_joint_two` and its one leaf): ~65%, unchanged.
* **(N)'s dedicated machinery overall**: ~88%, unchanged — this pass removed two
  phantom requirements and re-classified constants; it moved **no mathematics**.
* **Whole HCG compactness project**: low single digits.

---

## 12. Status

2026-08-03 — recon complete, plan written.  **G1 built and green**
(`LowRegBgA1Refold.lean`, `refold_aff_bg` at `:345`, diagonal preserved
byte-for-byte, zero downstream edits; report `UNIF_EXISTENCE_PLAN2.md` №101).
Next concrete action: **G2** — thread `g_bg` through `IsRealizedTwo`
(`LowRegApplyTwo.lean:107`), `lowreg_apply_two` (`:342`), `lowreg_solve_two`
(`:723`, the `g g` at `:746` and `:809`) and `lowreg_joint_two`, claiming those
files only after front 2's leaf lands (R3).  Blocking decision for the user:
**R1 / brick G5** — whether (N)'s hypothesis budget may rise from `∀ a ≤ 3` to
`∀ a ≤ 4`, or whether the forcing floor must be re-derived at `σ ≤ 1`.
