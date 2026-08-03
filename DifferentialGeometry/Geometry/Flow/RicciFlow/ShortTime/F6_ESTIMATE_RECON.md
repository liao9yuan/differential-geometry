# F6 estimate-side reconnaissance (base order 2)

Read-only recon, 2026-08-03.  Scope: the **estimate** half of brick F6 in
`FORCEJETMASS_PLAN.md` §6 — the per-scale Galerkin energy closure at base order 2.
Deliberately **does not pin the (S1₂) statement** (a sibling brick owns that); every
finding below is about what the supercritical closure consumes and what exists at
low order, both of which are independent of how (S1₂) is finally phrased.

No Lean was run.  Every claim carries a `file:line`.  Two whole-repo scans were used
(declaration/binder scan and a name-based call-reachability closure from the F6
target); both are over-approximations and are flagged as such where they matter.

---

## 1. The supercritical dissipation chain, end to end

### 1.1 Layer map (target → norm-level estimate)

`deTurckGalerkin_forcing_dissipation_perScaleSymm`
(`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean:1390`, gate `4·finrank+10 ≤ a`).

| # | declaration | file:line | gate | what it does |
|---|---|---|---|---|
| L0 | `deTurckGalerkin_forcing_dissipation_perScaleSymm` | `GalerkinParabolicEnergyDeTurck.lean:1390` | 4n+10 | final closure fed to Grönwall |
| L1 | `deTurckGalerkinForcingSymm_tame_diff_mass_perScale` | `:1265` | 4n+10 | squares the split, absorbs `Cδ₀<1` into `(1+Cδ₀²)/2` |
| L1' | `deTurckGalerkinForcingSymm_seed_mass` | `:1361` | 2n+10 | the `N(0)` seed mass |
| L2 | `deTurckSobolevNHa2_diff_sobolevSplit_perScale'` | `:961` | 4n+10 | moves the split onto `finiteEigenCombo` states |
| L3 | `deTurckSmoothRemainder_spectralCoercive_split'` | `:824` | 4n+10 | restricts a **norm** bound to a Finset of modes |
| **L4** | **`deTurckSmoothRemainderDiff_ballUniform_spectralSplit_of_symm`** | **`DeTurck/DeTurckRemainderRealizeBallUniformSplit.lean:204`** | 4n+10 | **the estimate itself, in plain `H^σ` norms** |
| L5 | `exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame` | `DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean:9271` | 2n+10 | three-arm decomposition + `εwrap` cap |

**L4 is the whole mathematical content.**  Its conclusion (`:219`–`:236`) is
norm-level and carries no spectral machinery at all:

```
‖N(T₀) − N(0)‖_{H^{a+k−1}}  ≤  Cδ₀ · ‖T₀‖_{H^{a+k+1}}  +  Crem k · ‖T₀‖_{H^{a+k}}
```

with `0 ≤ Cδ₀ < 1` **uniform in `k`**, for every symmetric `T₀` in the `H^{a+2}`
ball of radius `R₀`, where `N = deTurckSmoothRemainder g₀ g_bg`.

Everything from L3 up is **gate-free bookkeeping wearing a gated signature**: L3
restricts to a Finset and re-reads `smoothCcToTensorHs … .coeff`, L2 rewrites the
state as `finiteEigenCombo`, L1 squares and applies Young, L0 splits off the seed.

### 1.2 Gate-free lemmas actually used in L0's body

`two_mul_sum_crossScale_le_eps` (`Sobolev/Tensor/CrossScaleCauchySchwarz.lean:98`, the
`2⟨u,v⟩ ≤ ε‖u‖²_{σ+1} + ε⁻¹‖v‖²_{σ−1}` cross-scale Cauchy–Schwarz);
`two_mul_sum_sameScale_le_sqrt` (`:177`, seed term); `galerkinEnergy` /
`galerkinEnergy_nonneg` (`GalerkinParabolicEnergy.lean:38`,`:43`);
`finiteEigenComboHs_coeff` (`Garding/EigenCombination.lean:379`);
`deTurckGalerkinForcingSymm_apply` (`GalerkinParabolicEnergyDeTurck.lean:550`);
`mass_le_of_sqrt_split` (`:491`); `Real.sq_sqrt`; `nlinarith`.

None of these sees `a`.  **The `a`-dependence of L0 is entirely inherited from L1/L1'.**

### 1.3 What the gate buys, and the first load-bearing use

L5's proof (`DeTurckRemainderPrincipalArmOpNorm.lean:9309`–`:9319`) forwards
`ha_super` into three producers and never uses it itself:

* `exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le` (`:4803`)
* `exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le` (`:5129`)
* `exists_smoothCcToTensorHs_appCc_armZeroTwoArmCoeff_opNorm_le` (`:9209`)

Following those down, the gate is forwarded again through
`appCc_armZeroTwoArmCoeff_opNorm_core` (`:9147`) → `appCc_armZeroTwoArm_spectralCore`
(`:9070`) → `bal_top`/`bal_top_odd`/`bal_Etrans` (`:7779`,`:8033`,`:8600`) →
`bal_block1`/`bal_block23` (`:7287`,`:7468`) → **`bal_gridcore` (`:6981`)**.

**First load-bearing use: `DeTurckRemainderPrincipalArmOpNorm.lean:7188`–`:7200`,
inside `bal_gridcore`.**  Verbatim:

```lean
      · have hSB : ¬ (dc + i + w + 2 * q + 1 ≤ a + 2) := hSA
        ...
            have hu_le : l + dw ≤ γ' := by omega
```

with, from the statement/preamble, `w = finrank ℝ E / 2 + 2` (`:7029`),
`γ' = j + 2*q + 3` (`:7030`), `hdw : dw ≤ finrank ℝ E / 2 + 3` (`:6985`),
`hdc : dc ≤ 1` (`:6984`), and the branch predicate
`SApred i := dc + i + w + 2*q + 1 ≤ a + 2` (`:7031`).

**What the gate buys.**  `bal_gridcore` splits a coefficient×data product grid by
`SApred`: on the `SApred` branch the coefficient jet index fits inside the ball's
derivative budget `a+2` and the coefficient factor is bounded by `R₀`; on the
`¬SApred` branch the gate `2n+10 ≤ a` forces `i + 2q` to already exceed `≈ 3n/2 + 9`,
which is what makes the **data**'s C⁰-embedding window `dw ≤ n/2 + 3` fit under the
output order `γ' = j + 2q + 3`.  So the gate is a **derivative-budget / bookkeeping
inequality that lets one Moser grid be split without any branch needing more than
`a+2` derivatives** — *not* an embedding threshold.

Corroborating: the same budget shape recurs at
`SobolevNonlinearityExistence.lean:2183` (`hm_le : m ≤ a + 2 := by omega` with
`m = 2·finrank + 4`), the fibre-smallness producer.

**The embedding it protects is itself gate-free.**
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`) takes **no** hypothesis
on `a`:

```lean
theorem exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq … x (T.toSection x) ≤
          C ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g r s j T‖ ^ 2
```

"supercritical" in the name = the fixed window `n/2 + 2`, not a gate.
**In dim 3 that window is `3/2 + 2 = 3`, i.e. exactly `L²`-jets `j ≤ 2`, i.e. exactly
`H²` control** — the sharp `H²(M³) ⊂ C^0` case.

---

## 2. The a = 2 replacement: existing pattern, not first of its kind

**Verdict: an existing low-order pattern to mirror EXISTS and is substantial.
The a = 2 dissipation is not the first of its kind — but the existing low-order
lemmas are at FIXED orders, and the missing piece is the `k`-indexed ladder.**

### 2.1 The dim-3 / low-order inventory (all gate-free, `hDim : finrank ℝ E = 3`)

| lemma | file:line | shape |
|---|---|---|
| `hs2_fiber_sq` | `Spectral/Tensor/Estimates/H2Pointwise.lean:166` | pointwise fibre norm² ≤ C²‖T‖²_{H²} (dim 3) |
| `hs2_low2` | `H2Pointwise.lean:210` | `H²` controls the first-two-jet square-sum |
| `hs3_grad_low2` | `H2Pointwise.lean:229` | `H³` controls pointwise gradient |
| `hs2_op_bound` | `H2Pointwise.lean:323` | `gFibreOpBound g (ccTensorBilinSymm g T) (C‖T‖_{H²})` |
| `hs2_opBound_at_two` | `HeatSemigroup/MaxRegSolutionJointlySmooth.lean:1593` | the same, repackaged at Sobolev index `a = 2` |
| `appCc_h2_h2_h2` | `Estimates/H2H4Principal.lean:31` | the `H²` jet is a **Banach algebra** for operator-field application (dim 3) |
| **`appCc_h2_h4_h2`** | **`H2H4Principal.lean:55`** | **`‖appCc Φ (∇²U)‖_{H²} ≤ C·A·‖U‖_{H⁴}` for `Φ` with `H²` jet ≤ A** |
| `appCc_h2_h3_h1`, `appCc_c1_h2_h1`, `appCc_h2_h2_h1`, `appCc_h2_cov_h1`, `appCc_h3_h1` | `Estimates/H2H3Principal.lean:189,346,491,528,696` | the `H¹`-output family |
| `appCc_h1_h2_h1`; `appCc_h2_h3_h2` | `Estimates/H1H2AppCc.lean:48`; `H2H3FirstOrder.lean:29` | lowest rung; first-order arm |
| `appRS_h2_h2_h2`, `appRS_h1_h2_h1`, `appRS_h2_h1_h1` | `Estimates/H1H2AppCcRS.lean:769,390,569` | mixed-valence versions |
| `principal_coeff_h2`; `principal_arm_h2` | `DeTurck/PrincipalCoeffH2.lean:418`; `:589` | cometric coefficient on the `H²` ball; `H³` input |
| **`principal_arm_h4_h2`** | **`PrincipalCoeffH2.lean:622`** | **`‖PrincipalArm(g₁)U‖_{H²} ≤ C‖T‖_{H²}‖U‖_{H⁴}` on the `H²` ρ-ball** |
| `lowRegPrincipal_norm`, `lowRegPrincipal_lip` | `DeTurck/PrincipalLowRegH2.lean:121`,`:160` | low-reg principal operator norm/Lipschitz |
| `a2_pair`, `a2Hi_core`, `a2Lo_core`, `a2_comm`, `a2_diff` | `DeTurck/DeTurckRemainderLowBaseA2.lean:72,198,211,245,289` | the a = 2 arm-2 splitting |
| `armSuccH2`, `arm2H2`, `hatBddH2`, `hatPairH2`, `armBddH2`, `jetSix` | `DeTurck/DeTurckRemainderLowBaseH2Cov.lean:268,282,313,345,431,393` | a = 2 arm envelopes |

There are ~17 further `DeTurck/DeTurckRemainderLowBase*.lean` files in the same
dim-3 low-base family.

### 2.2 Why `hs2_opBound_at_two` is the right precedent

`hs2_op_bound`'s proof (`H2Pointwise.lean:330`) crosses the low-order gap exactly
the way F6 must: it calls `hs2_fiber_sq` at order 2, whose own calc step
(`H2Pointwise.lean:304`–`:311`) reads `∑ j ∈ Finset.range 3, ‖∇^j V‖²` — i.e. it
instantiates the **same** sharp window `n/2 + 2 = 3` that
`SobolevEmbeddingSharpC0JetSum.lean:717` provides, and then uses `hs_le_jet` /
`hsJet_le` to convert jets ↔ spectral norm.  It never touches `bal_gridcore` and
never needs a budget inequality, because at a fixed order there is nothing to split.

Contrast with the supercritical producer `sobolevBall_smooth_fibreSmall_of_threshold`
(`SobolevNonlinearityExistence.lean:2175`), which routes through
`ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy` at order `m = 2·finrank + 4`
(= 10 in dim 3).  **`hs2_op_bound` gets the same conclusion at order 2** — an
8-order saving, and the reason a = 2 is viable at all.

### 2.3 The two gate-free order-generic bridges F6 will lean on

`hsJet_le` (`Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean:834`) and
`hs_le_jet` (`:855`) give, for **every** `n : ℕ`, the two-way equivalence between
`‖·‖_{H^n}` (spectral) and `∑_{j≤n}‖∇^j ·‖_{L²}` (covariant jets), with no gate.
Since the dissipation's scales are `σ = a + k` with `a, k : ℕ`, these nat-order
bridges suffice — the whole a = 2 ladder can be stated and proved in **jet** form
and transported to spectral form at the end.

### 2.4 What is genuinely missing

Every low-order lemma above is at a **fixed** order (H¹/H²/H³/H⁴).  L4 needs a
**family in `k`** with a `Cδ₀ < 1` that does not degrade as `k → ∞`:

```
∀ k, ‖N(T) − N(0)‖_{H^{k+1}} ≤ Cδ₀‖T‖_{H^{k+3}} + C_k‖T‖_{H^{k+2}},   Cδ₀ < 1
```

on the `H⁴` ball (`= H^{a+2}` at `a = 2`).  `appCc_h2_h4_h2` is precisely the
`k = 1` rung of the top-order half; `principal_arm_h4_h2` is the `k = 1` rung with
the smallness factor made explicit.  **The new content is the induction in `k`, not
the base estimate.**  The margin at a = 2 is sharp: `H⁴(M³) ⊂ C^{2,1/2}` supplies
exactly `‖∇²T‖_{C⁰}`, which is exactly the factor the Moser splitting needs on the
low-order branch — zero slack, so the proof must be written with the sharp window,
not a lossy one.

---

## 3. The Galerkin scaffold at a = 2

### 3.1 (a) The smooth core of a finite eigen-combination — EXISTS, and is duplicated

* `eigenSmooth` = `eigenvectorSmooth g 0 2 i` : `SmoothCcTensor g 0 2`
  (`Garding/EigenCombination.lean:95`).
* `finiteEigenCombo F c = ∑ i ∈ F, c i • eigenSmooth i : SmoothCcTensor g 0 2`
  (`EigenCombination.lean:102`) — **the packaged smooth object**, with
  `finiteEigenCombo_contMDiff` (`:117`) giving `C^∞` of its section, plus
  `finiteEigenCombo_toL2` (`:134`), `_tensorL2Coeff` (`:174`), `_l2NormSq` (`:350`),
  `_spectral_normSq` (`:406`), `_weakSolution` (`:224`).
* `finiteEigenComboHs F c σ` (`EigenCombination.lean:364`) is the `H^σ` element with
  indicator coordinates; `finiteEigenComboHs_coeff` (`:379`), `_coeff_eq` (`:388`),
  `finiteEigenComboHs_norm_eq_sqrt_spectral`
  (`Garding/EigenComboGardingReduction.lean:256`).
* **The pin exists, twice, both `private`, both gate-free 4-line proofs:**
  `finiteEigenComboHs_eq_smoothCcToTensorHs`
  (`GalerkinParabolicEnergyDeTurck.lean:529`) and its verbatim clone
  `gscr_finiteEigenComboHs_eq_smoothCcToTensorHs` (`:808`):

```lean
    finiteEigenComboHs g₀ S c σ = smoothCcToTensorHs g₀ σ (finiteEigenCombo g₀ S c)
```

  **Action for F6: promote ONE of these into `Garding/EigenCombination.lean` as
  public and delete the other** (§7.5-style duplication, already 2 copies).
* Also available: `finiteEigenComboHs_tensorHsToL2_eq`
  (`HeatSemigroup/SpectralSmoothRepresentativeRealize.lean:123`).

§7.3's premise is therefore **verified**: Galerkin states are genuinely smooth and
already have a public-able bridge to the `H^σ` scale at every real `σ`.

`deTurckSmoothN` (`DeTurck/SobolevNonlinearityExistence.lean:109`) is order-generic —
its own docstring (`:100`–`:108`) says "valid at every real order … the **continuous,
non-gated** Ricci–DeTurck remainder on the smooth representatives", and
`deTurckSmoothN_coeff` (`:125`) shows the coordinates do not mention `a` (only the
output *type* does).  So the a = 2 Galerkin forcing can indeed be defined as
`(deTurckSmoothN g₀ g_bg 2 (finiteEigenCombo S w) hδ_lt hδ).coeff i`.

**One real design obligation surfaces here.**  `deTurckSmoothN` requires a
fibre-smallness side condition `hδ : gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`
with `δ < 1`, which fails for large `w`.  The supercritical route removed this by
using the *retracted completed* operator; at a = 2 the substitute is
`radialScaleSmooth` (`SobolevNonlinearityExistence.lean:2265`) +
`norm_smoothCcToTensorHs_radialScaleSmooth_le` (`:2271`) — already used as the
`htie` device at `GalerkinParabolicEnergyDeTurck.lean:973`–`:980` — with
`hs2_opBound_at_two` (`MaxRegSolutionJointlySmooth.lean:1593`) supplying the δ.

### 3.2 (b) Reuse inventory: order-generic vs supercritical-specific

**`HeatSemigroup/GalerkinParabolicEnergy.lean` — 11/11 declarations gate-free.
Zero occurrences of `finrank ℝ E + 10` in the file.  Reuse verbatim.**

| declaration | line | note |
|---|---|---|
| `lambda_mul_tensorSobolevWeight` | 26 | |
| `galerkinEnergy` (def) | 38 | |
| `galerkinEnergy_nonneg` / `_continuousOn` / `_hasDerivWithinAt` | 43 / 53 / 62 | |
| `galerkinEnergy_deriv_identity` | 80 | |
| `galerkinEnergy_hasDerivWithinAt_ode` | 108 | |
| `energy_hierarchy_explicit_bound` / `_perScale` | 126 / 173 | Grönwall hierarchy |
| **`galerkin_energy_uniform_bound_perScale`** | **220** | `σ₀ : ℝ` free, no metric, no `a`, no nonlinearity — takes `hclosure` as a hypothesis |
| `galerkin_energy_uniform_bound` | 297 | |

**`GalerkinParabolicEnergyDeTurck.lean` — mixed.**

* Gate-free / reusable: `galerkinCoordEmbedLM`/`Embed`/`Restrict`/`DiagLM`/`Diag`/
  `Field` (`:79`–`:172`), `galerkinCoordFieldSymm_apply` (`:550`),
  `mass_le_of_sqrt_split` (`:491`), `gscr_eigenIdxFinset_lambda_closed` (`:793`),
  both `finiteEigenComboHs_eq_smoothCcToTensorHs` copies.
* Supercritical-specific (must be rebuilt at a = 2): everything that names
  `deTurckSobolevNHa2` / `deTurckSobolevNHa2Symm` — `galerkinCoordField_lipschitzWith`
  (`:193`), `_affineBound` (`:215`), `deTurckGalerkin_solution_exists_single(Symm)`
  (`:275`,`:644`), `deTurckGalerkin_solution_exists(Symm)` (`:377`,`:746`),
  `deTurckGalerkinForcing_seed_mass` (`:416`), the two `deTurckSobolevNHa2Symm_*_eq`
  (`:1215`,`:1234`), and L0–L2.
* The ODE engine underneath is gate-free:
  `forward_solution_of_lipschitzWith_affineBound` (used at `:684`).  At a = 2, on a
  **finite-dimensional** coefficient space all `H^σ` norms are equivalent, so the
  Lipschitz + affine bound for `w ↦ deTurckSmoothN 2 (finiteEigenCombo S w)` is an
  `N`-dependent (not uniform) fact — acceptable, since only the *energy* estimate has
  to be `N`-uniform.

**`HeatSemigroup/GalerkinLimitUniformMass.lean` — supercritical-specific, reusable
*shape* but not *body*.**  All 14 substantive declarations (`:33`, `:70`, `:165`,
`:187`, `:289`, `:401`, `:463`, `:472`, `:482`, `:494`, `:551`, `:562`, `:649`,
`:902`) are gated at 2n+10 and built on the retracted `deTurckSobolevNHa2Symm`;
`galerkinSol_tendsto_solField_perModeConvSymm` (`:1051`) and (S1) itself,
`deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm` (`:1125`), are 4n+10.
Only `symmForce_contraction_coeff_le_half` (`:416`) is gate-free.

---

## 4. Vestigial-sweep scoping (28 declarations) — with a correction to F1

Scan: 403 declarations in `DifferentialGeometry/` bind a `2n+10` / `4n+10`
hypothesis; **exactly 28** never mention the binder again in their own block —
matching F1's count.  But the F1 framing needs a correction:

> **Only 11 of the 28 carry `set_option linter.unusedVariables false in`.  The other
> 17 have `omega` / `linarith` in the body (or `by omega` inside the statement), and
> for those the binder is consumed *silently* — `bal_gridcore` is the proof that at
> least one of them is genuinely load-bearing (§1.3).  "Binder not named" is NOT
> evidence of vestigiality when the marker is absent.**

Legend: **marker** = `set_option linter.unusedVariables false in` immediately above
the declaration (strong evidence of true vestigiality).  **chain** = reachable from
`deTurckGalerkin_forcing_dissipation_perScaleSymm` by a name-based call closure
(over-approximating; `DOWNSTREAM` = provably not a dependency because its file
imports the F6 file).

| declaration | file:line | marker | gate | F6 chain |
|---|---|---|---|---|
| `exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform` | RicciThreeArmAppCc.lean:2575 | yes | 2n+10 | ON-CHAIN |
| `exists_Csob_sub_pointwise_jet3_le` | RicciThreeArmAppCc.lean:2677 | NO | 2n+10 | off-chain |
| `exists_ricciArmOrder0BgRCommCoeffField_realizedFam_rfns_ballUniform` | RicciThreeArmCorrectionFieldBound.lean:812 | yes | 2n+10 | ON-CHAIN |
| `exists_Csob_convexPerturbation_pointwise_C2_le` | ConvexPerturbationPointwiseC2.lean:67 | NO | 2n+10 | ON-CHAIN |
| `cometricCastG0_order0sup_jetL2_radiusFree` | DeTurckVFJetRadiusFree.lean:66 | yes | 2n+10 | off-chain |
| `sharpFlatEndoCc_lowOrder_jetL2_radiusFree` | DeTurckVFJetRadiusFree.lean:428 | yes | 2n+10 | off-chain |
| `connDiffSection_lowOrder_jetL2_radiusFree` | DeTurckVFJetRadiusFree.lean:581 | yes | 2n+10 | off-chain |
| `wOmega_lowOrder_jetL2_radiusFree` | DeTurckVFJetRadiusFree.lean:1117 | yes | 2n+10 | off-chain |
| `connDiff_L2_topsep_rf` | DeTurckVFJetRadiusFree.lean:1424 | yes | 2n+10 | off-chain |
| `wAlphaB_L2_perOrder_rf` | DeTurckVFJetRadiusFree.lean:2128 | yes | 2n+10 | off-chain |
| `lc0AMix_perOrder_rf` | LieCorr0CoeffDiffRadiusFree.lean:2956 | yes | 2n+10 | off-chain |
| `arm_covGrad_coeffLower_l2_tame` | DeTurckPrincipalArmEnergyCrossTerm.lean:1429 | NO | 4n+10 | ON-CHAIN |
| `deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow` | DeTurckRemainderHigherOrderTame.lean:604 | NO | 2n+10 | ON-CHAIN |
| `exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le` | DeTurckRemainderPrincipalArmOpNorm.lean:1202 | NO | 2n+10 | ON-CHAIN |
| `exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder` | …ArmOpNorm.lean:4170 | NO | 2n+10 | ON-CHAIN |
| `exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder` | …ArmOpNorm.lean:4441 | NO | 2n+10 | ON-CHAIN |
| `exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_zero` | …ArmOpNorm.lean:4875 | NO | 2n+10 | ON-CHAIN |
| `exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_succ` | …ArmOpNorm.lean:5055 | NO | 2n+10 | ON-CHAIN |
| **`bal_gridcore`** | **…ArmOpNorm.lean:6981** | **NO** | 2n+10 | **ON-CHAIN — LOAD-BEARING (§1.3)** |
| `bal_top` | …ArmOpNorm.lean:7779 | NO | 2n+10 | ON-CHAIN |
| `bal_top_odd` | …ArmOpNorm.lean:8033 | NO | 2n+10 | ON-CHAIN |
| `deTurckArmDiff_supercritical_pointwise_jet_le` | DeTurckRemainderTameLipschitz.lean:1255 | NO | 2n+10 | off-chain |
| `deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow` | …TameLipschitz.lean:33534 | NO | 2n+10 | ON-CHAIN |
| `deTurckSmoothRemainderDiff_connLapResidual_topCoeff_crude_ballUniform` | …TameLipschitz.lean:33820 | yes | 2n+10 | ON-CHAIN |
| `sobolevBall_smooth_fibreSmall` | SobolevNonlinearityExistence.lean:2123 | NO | 2n+10 | off-chain |
| `sobolevBall_smooth_fibreSmall_of_threshold` | SobolevNonlinearityExistence.lean:2175 | NO | 2n+10 | ON-CHAIN (gate used at `:2183`) |
| `galerkinSol_tendsto_solField_perModeConvSymm` | GalerkinLimitUniformMass.lean:1051 | NO | 4n+10 | DOWNSTREAM (gate used via `by omega` **in the statement**, `:1059`,`:1062`,`:1067`) |
| `maxreg_solution_jointly_smooth_representative_of_nemytskii` | MaxRegSolutionJointlySmooth.lean:964 | yes | 2n+10 | DOWNSTREAM |

**Scoping conclusion.**  De-vestigializing does **not** shrink F6's gated surface in
any useful way:

* The three genuinely-safe (marker + on-chain) candidates —
  `exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform`,
  `exists_ricciArmOrder0BgRCommCoeffField_realizedFam_rfns_ballUniform`,
  `deTurckSmoothRemainderDiff_connLapResidual_topCoeff_crude_ballUniform` — are
  coefficient-envelope producers whose gate is passed *around* rather than *through*
  the grid split; removing their binders leaves L4 still gated by `bal_gridcore`.
* The 8 marker+off-chain `DeTurckVFJetRadiusFree` / `LieCorr0CoeffDiffRadiusFree`
  entries (already "radius-free" by design) are free wins for repo hygiene but
  irrelevant to F6.
* No deletions performed.  Nothing in this report should be acted on without the
  focused check F1 already schedules.

---

## 5. Verdict: sub-brick decomposition of the estimate side

### 5.1 Sub-bricks (in dependency order)

| # | sub-brick | what it is | difficulty |
|---|---|---|---|
| **E0** | **norm-level a = 2 split.**  The a = 2 analogue of `deTurckSmoothRemainderDiff_ballUniform_spectralSplit_of_symm` (`DeTurckRemainderRealizeBallUniformSplit.lean:204`): `∀ k, ‖N(T)−N(0)‖_{H^{k+1}} ≤ Cδ₀‖T‖_{H^{k+3}} + C_k‖T‖_{H^{k+2}}` with `Cδ₀ < 1` uniform in `k`, on the dim-3 `H⁴` (or `H²`) ball. | **the whole math wall** |
| E0a | three-arm decomposition at a = 2 (analogue of `…ArmOpNorm.lean:9271`), reusing `principal_arm_h4_h2` (`PrincipalCoeffH2.lean:622`) for the principal arm and `a2_diff`/`a2_comm` (`DeTurckRemainderLowBaseA2.lean:289`,`:245`) for the split. | design + estimate |
| E0b | the **`k`-ladder**: promote `appCc_h2_h4_h2` (`H2H4Principal.lean:55`) from the fixed pair `(H², H⁴, H²)` to `(H², H^{k+3}, H^{k+1})` with a `k`-uniform top constant.  Base rungs `k = 0,1` already exist. | **the induction — genuinely new** |
| E0c | Moser envelope for the coefficient jets at base 2 (analogue of the `bal_*` grid, but with `w = 3` and ball `H⁴` — no budget predicate needed, since there is no `a` to exceed). | estimate |
| E1 | fibre-smallness / retraction at a = 2: `hs2_opBound_at_two` (`MaxRegSolutionJointlySmooth.lean:1593`) + `radialScaleSmooth` (`SobolevNonlinearityExistence.lean:2265`) in place of `sobolevBall_smooth_fibreSmall_of_threshold`. | routine |
| E2 | spectral wrapper stack: re-derive L3/L2/L1/L0 at a = 2.  **Mechanical** — the four bodies use only `two_mul_sum_crossScale_le_eps`, `two_mul_sum_sameScale_le_sqrt`, `finiteEigenComboHs_coeff`, `galerkinEnergy_nonneg`, Young/`nlinarith`, all gate-free. | routine (transcription) |
| E3 | promote `finiteEigenComboHs_eq_smoothCcToTensorHs` (`GalerkinParabolicEnergyDeTurck.lean:529`) into `Garding/EigenCombination.lean`, delete the `:808` clone. | trivial |
| E4 | a = 2 Galerkin ODE existence: rebuild `deTurckGalerkin_solution_exists*Symm` on `deTurckSmoothN 2 ∘ finiteEigenCombo` + radial retraction, feeding the gate-free `forward_solution_of_lipschitzWith_affineBound`. | routine + one design choice (retraction norm) |
| E5 | plug into `galerkin_energy_uniform_bound_perScale` (`GalerkinParabolicEnergy.lean:220`) — verbatim, `σ₀ = 2`. | free |

### 5.1a STATUS (updated 2026-08-03)

**E0's `k = 0` rung is DONE, sorry-free.**
`n_diff_h1_rung`, `Analysis/Spectral/Intrinsic/DeTurck/LowRegDissipRung.lean:76`
(note: `LowRegDissipRung.md`).  Focused check and one targeted module build both
clean; no `maxHeartbeats` bump.

Statement realized (all norms `‖ccTensorToHs g₀ 2 (σ : ℝ) ·‖`, `N = deTurckSmoothRemainder g₀ g₀ ·`):

```
∀ R₀, ∃ ρ Cδ₀ C₀, 0 < ρ ∧ 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ 0 ≤ C₀ ∧
  ∀ T symmetric, δ ≤ 1/3 + the two gFibreOpBound certificates,
    ‖T‖_{H²} ≤ ρ → ‖T‖_{H³} ≤ R₀ →
      ‖N T − N 0‖_{H¹} ≤ Cδ₀‖T‖_{H³} + C₀‖T‖_{H²}
```

`Cδ₀ = Capp·Cc2·ρ` with `ρ = min ρ₂ (1/(2(Capp·Cc2+1)))` — the contraction is
bought purely by shrinking the `H²` ball.  `C₀` depends on `R₀` only.

**Correction to §5.2's route.**  The two halves named there
(`principal_arm_h2` + `appCc_h2_h3_h1`) are *not* what assembles.  Routing the
top arm through `deTurckPrincipalCometricArm` leaves an unproducible third arm
`a₂ T − Arm T` at low order.  The clean route is the canonical zero-based split
itself:

* identity: `lowData_split` (`…LowBaseAction.lean:3841`) —
  `N T − N 0 = a₂ T + a₁ T`, an **order-free** smooth-core identity;
* top arm: `c2_h2_small` (`:13268`) gives `C2` pointwise **and** `H²`-jet small
  (`≤ Cc2‖T‖_{H²}`), fed to `appCc_h2_h3_h1` (`Estimates/H2H3Principal.lean:189`);
* lower arm: `lowData_a1_coeff` (`:13609`) + `a1_h2_h1` (`:13189`), then the
  jet↔spectral bridges `hsJet_le` / `hs_le_jet`.

`remainder_diag_h2` (`:13555`) is the wrong producer for the ladder: its `a₁`
clause is an `H²` bound in terms of `‖T‖_{H³}`, not an `H¹` bound in terms of
`‖T‖_{H²}`.

**Early signal on E0b (§5.1's `k`-ladder), from the assembly.**  Positive on the
decomposition, and it re-scopes E0b:

* the split identity carries no order at all, so rung `k` is *literally*
  "apply an `appCc_·_h(k+3)_h(k+1)` estimate to `C2` and an
  `appCc_·_h(k+2)_h(k+1)` estimate to `C0, C1`".  No new algebra at any rung.
* the `k = 0` contraction rides on `c2_h2_small`'s **jet** clause, which is
  small only because two derivatives of `C2` cost two derivatives of `T` and
  `‖T‖_{H²} ≤ ρ`.  At rung `k` the same route needs the `H^{k+2}` jet of `C2`,
  which costs `‖T‖_{H^{k+2}} ≤ R₀` — bounded, not small.  So a *naive* rung `k`
  gives `Cδ₀(k) ≈ Capp(k)·Cc2(k)·R₀ ≥ 1`.
* the escape is already stocked: `lowData_split`'s second clause caps the
  **pointwise** fibre norm of `C2` by `κ·δ/(1−δ)²` with `κ` free of `T`, `δ` and
  any order — a genuinely `k`-free small quantity.  §5.3 clause 1 is therefore
  **not** established; nothing forces the degradation except the current shape
  of the `appCc` family.
* **E0b's real content, restated**: add the *split-envelope* member of the
  `appCc` family at the `Tensor/Estimates/` layer,
  `‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k (‖Φ‖_{C⁰}‖U‖_{H^{k+3}} + ‖Φ‖_{H^{k+1}}‖U‖_{H^{k+2}})`,
  pairing each coefficient norm with its own data order.  Every existing member
  takes one envelope `A` for both; the only two-constant member,
  `appCc_c1_h2_h1` (`H2H3Principal.lean:346`), *adds* the constants
  (`C(A+B)‖U‖_{H²}`).  Second sub-brick: the `k`-generic analogue of
  `c2_h2_small`'s jet clause (an `H^{k+1}`-jet envelope for `C2`).

Per §5.3 this is a normal estimate gap, **not** a route obstruction.

### 5.1b E0b STATUS: **DONE** (2026-08-03)

**The split-envelope member exists, sorry-free and axiom-clean.**
New file `Analysis/Spectral/Tensor/Estimates/AppCcSplitEnvelope.lean`
(note: `AppCcSplitEnvelope.md`).  Focused check and one targeted module build
both clean; `#print axioms` on both public theorems gives only
`propext, Classical.choice, Quot.sound`.  No `maxHeartbeats` bump.

* `appCc_split_env` (`:110`) — order-generic, **dimension-free, gate-free**:
  ```
  ‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k * (A ‖U‖_{H^{k+3}} + B Λ)
  ```
  `A` = pointwise fibre bound on `Φ`, `B` = `L²` jet of `Φ` through order `k+1`,
  `Λ` = pointwise fibre bound on `∇²U`.  This is the pairing §5.1a asked for:
  the `C⁰` factor multiplies the **top** order, the jet factor does not.
* `appCc_split_hs` (`:276`) — dim-3 corollary, the literal §5.1a shape
  `C·(A‖U‖_{H^{m+3}} + B‖U‖_{H^{m+2}})`, at the rungs `m = k + 2`.

**Correction to §5.1a's E0b statement.**  The literal target is achievable only
for `m ≥ 2`, and this is *not* a route defect: at `m = 0` it is **false**.  The
grid cell `∇Φ · ∇²U` is only `L^{3/2}` when `Φ ∈ H¹ ∩ L^∞` and `U ∈ H³` (dim 3),
which is exactly why the existing `m = 0` member `appCc_h2_h3_h1` demands the
`H²` jet of `Φ`.  Rungs `m = 0, 1` are already covered by `appCc_h2_h3_h1` /
`appCc_h2_h4_h2`, so the ladder is complete at every rung.  Sobolev-window
arithmetic: the gate-free sharp `C⁰` window has width `finrank/2 + 2 = 3` in
dim 3, so `‖∇²U‖_{C⁰} ≲ ‖U‖_{H⁴}` — two orders, hence `m ≥ 2`.

**No new inequality was needed.**  The order-generic Leibniz split
(`appCc_iteratedCovGrad_diagonalProductGrid_le`,
`OperatorFieldFibreNormJet.lean:885`) and its integrated Gagliardo–Nirenberg
companion (`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`,
`RemainderCoeffPerOrderJetEnvelopes.lean:862`) already existed; the split is
just reading the two-arm bound asymmetrically.  `MoserTameProduct.lean:110` was
rejected — it needs `Cᵏ` coefficient hypotheses and carries a real `sorry`.

**§5.3 clause 1 remains OPEN, and E0b does not close it.**  `C k` is *not*
`k`-uniform: it carries `√(appCcGdiag j)` summed over `j < k+2`, and
`appCcGdiag j = (2(n+1))^j`, so `C k ≳ (2(n+1))^{(k+1)/2}`.  E0b delivers the
*shape* that lets `lowData_split`'s `k`-free pointwise cap on `C2` multiply the
top order — which is what §5.1a identified as the missing ingredient — but a
`k`-uniform `Cδ₀` additionally needs a grid weight better than `appCcGdiag`
(sharper Leibniz bookkeeping at the `OperatorFieldFibreNormJet` layer) or a
`k`-uniform reformulation of the ladder.  This is now the single sharpest open
question for E0/E0a.

**Still open, unchanged:** the second sub-brick named in §5.1a — the `k`-generic
analogue of `c2_h2_small`'s jet clause (an `H^{m+1}`-jet envelope for `C2`;
`m = 0` is `c2_h2_small`, `DeTurckRemainderLowBaseAction.lean:13268`).  Without
it there is no producer for `B`.

### 5.1c E0a′ STATUS: ladder LANDED, **§5.3 clause 1 refuted** (2026-08-03)

New file `Analysis/Spectral/Intrinsic/DeTurck/LowRegLadderRung.lean` (note:
`LowRegLadderRung.md`).  Focused check and one targeted module build clean.
**Sorry census: exactly one, the named frontier `c2_jet_tower`.**

* `a2_ladder` (`:192`) — the ladder for the low-base second-order arm, at
  **every** rung `m`, with the top constant free of `m`:
  ```
  ‖(lowBaseData g₀ g₀ T …).a2 T‖_{H^m}
      ≤ κ·(δ/(1−δ)²)·‖T‖_{H^{m+2}} + Clower m·‖T‖_{H^{m+1}}
  ```
  gated `finrank ℝ E + 5 ≤ a`, on the ball `‖T‖_{H^{a+2}} ≤ R₀`, for
  `0 ≤ δ ≤ 1/3`.  `κ` is exactly `lowData_split`'s cap constant, so one
  smallness threshold on `δ` contracts every rung at once.
* `appCc_cap_hs_le` (`:75`) — **axiom-clean**, no `sorry` — the `m`-form of the
  order-generic engine `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`
  (`ConnLapCommutatorCoefficientTame.lean:1323`), read on the resolvent family
  at `p = 0` and closed with the constant-one spectral shift
  `smoothCcToTensorHs_rawTensorConnLapSmooth_le`.  Gate `n+5 ≤ a` and top
  constant `εC` — versus `2n+10 ≤ a` and `√(n³)·εC` for the shipped wrapper
  `…ArmOpNorm.lean:5129`, whose `_le_zero` half never uses its gate and whose
  `_le_succ` half forwards it through one `by omega`.

**§5.3 clause 1 is now refuted.**  A `k`-uniform top constant for the
base-order-2 dissipation exists and is realized in Lean; the `appCcGdiag`
degradation was a property of E0b's Leibniz-grid route only, exactly as
`L4_UNIFORMITY_AUTOPSY.md` predicted.  Clauses 2 and 3 stay moot.

**Correction to the autopsy §3.3 target, clause (c).**  The `H^{a+2}` ball is
*not* replaceable by the dim-3 sharp `H³` ball, and the `n+5 ≤ a` gate is not
re-derivable at `a = 2`: it is arithmetically **false** there.  In
`master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:469`) region
one needs the numeric budget `t + (w−1) + dc ≤ a+2`, i.e. `4+2+3 = 9 ≤ a+2` in
dim 3 at the `(dc,dd) = (3,2)` call site — `a ≥ 7`, reading `9 ≤ 4` at `a = 2`.
Log-convexity (`hs_extreme_interp`) rescues region two but not region one, which
has no `f γ` on the right to trade against.  Parameterizing the leaf's split
threshold `t` brings the bottom to **`a = 3` (ball `H⁵`)**, no further; that
edits a `private` statement inside a supercritical file and is its own brick.

**Remaining for E0/E0a:** (a) `c2_jet_tower` — the `A.C2` all-order jet tower
under path integrals, the single genuine estimate left (autopsy risk 1);
(b) ~~optionally the `a = 3` ball-order brick above~~ — **DONE, see §5.1d**;
(c) E1′, the Galerkin wiring into `lowreg_spatialMass`.

### 5.1d E0a″ STATUS: the `a ≥ 3` threshold brick **DONE** (2026-08-03)

The clause-(b) brick of §5.1c is landed.  The split threshold `t` of the leaf
`master_appCc_jet_le_sharp`
(`Sobolev/TensorHilbert/ConnLapCommutatorCoefficientTame.lean:475`) is now a
**parameter** rather than the hard-wired `finrank ℝ E / 2 + 3`, carrying the two
honest budget hypotheses that the split actually consumes:

```
ht1 : t + finrank ℝ E / 2 + 1 + dc ≤ a + 2     -- region 1 (i ≤ t), numeric sup bound
ht2 : finrank ℝ E / 2 + 1 + dd ≤ t + 4         -- region 2 (t < i), log-convexity trade
```

The gate `finrank ℝ E + 5 ≤ a` is **gone from the whole chain** — `ht1`/`ht2`
alone discharge all three budget `omega`s in the leaf (`hbound`, `hβγ`,
`hsum_ok`).  Because each of the six call sites may now choose its own `t`, the
three public theorems of that file (`exists_appCc_covGradCoeff_secondCovGrad_l2_le`,
`exists_rawConnLap_appCc_secondCovGrad_commutator_Hs_family_le`,
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`) now gate on the sharp,
dimension-general

```
max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a          -- dim 3: 3 ≤ a
```

`a2_ladder` therefore reads `hDim : finrank ℝ E = 3` together with **`ha : 3 ≤ a`**,
i.e. the a-priori ball drops `H^{10} → H⁵`.  `appCc_cap_hs_le` carries the
dimension-general gate and stays **axiom-clean**; the file's sorry census is
still exactly one (`c2_jet_tower`).  The `k`-uniform **top constant is unchanged**
— `t` moves cost only between `S1`/`S2`, which feed `Cm` → `CEcomm` → `ClowerFn`,
i.e. the *lower*-order constant.  That was the point of the brick: threshold slack
was bought with rung-dependent lower-order cost, never with the top constant.

This makes §5.1c's `a = 3` bottom real, and confirms the E0a′ arithmetic: the two
`master_…` call sites need `0 ≤ t ≤ a−3` at `(dc,dd) = (3,2)` and `1 ≤ t ≤ a−2` at
`(2,3)`; at `a = 3` those windows are the single points `t = 0` and `t = 1`.  A
*single* global `t` would have needed `a ≥ 4` — per-call-site choice is what buys
the last order.

### 5.1e E0a‴ STATUS: `c2_jet_tower` **PROVED**, frontier moved inside the integral (2026-08-03)

New file `Analysis/Spectral/Intrinsic/DeTurck/LowRegC2JetTower.lean` (note:
`LowRegC2JetTower.md`).  `LowRegLadderRung.lean` now has **no `sorry` at all**;
`c2_jet_tower` (`:144`) is a proved theorem.  Campaign sorry census still
exactly ONE, now `topKer_jet` (`LowRegC2JetTower.lean:212`).

**What was proved.**  `path_add_sub_jet` (`:78`), axiom-clean:

```
hcap : ∀ t ∈ Icc 0 1, lowJetSq g n (Φ t + Ψ t − C) ≤ Λ
⊢ lowJetSq g n (∫₀¹Φ + ∫₀¹Ψ − C) ≤ Λ          -- same Λ, every order n
```

**Correction to §5 risk 1 of the autopsy.**  The differentiation-under-the-integral
step is *not* the new content: `path_jetL2_le`
(`Tensor/CovGrad/ParametricJetIntegral.lean:331`) and the genuine `∇ⁱ∫ = ∫∇ⁱ`
commutation `icg_path_comm` (`:291`) already exist and are **order-generic**.
The only missing piece was the additive rearrangement
`∫Φ + ∫Ψ − C = ∫(Φ + Ψ − C)`, whose two existing copies are unusable — one is
`private` in the other-lane-claimed `DeTurckRemainderLowBaseAction.lean`
(`path_add_sub_h2`), the other is fibre-pointwise not jet (`path_add_sub_cap`,
`LowRegPathSplit.lean:334`).  Re-derived from public API in ~25 lines.  One more
"framework wall" that was already stocked — grep the order-generic layer before
believing a per-order claim.

**Second correction: `c2_jet_tower`'s `H^{a+2}` ball is vestigial.**  `a2_ladder`
calls it without forwarding `ha : 3 ≤ a`, so `a` is arbitrary and at `a = 0` the
ball supplies no low-order control.  The real input is `hδ_le : δ ≤ 1/3`, since
`gFibreOpBound g (ccTensorBilinSymm g T) δ` unfolds to
`|T(v,w)| ≤ δ|v|_g|w|_g` pointwise, i.e. `‖T‖_{L^∞} ≤ 1/3` — exactly the
Moser/Gagliardo–Nirenberg input.  `topKer_jet` is stated **ball-free**.

**Producer inventory for the moved frontier (measured).**  `topKernel_eq` splits
the integrand into three summands with *non-uniform* status:

* `lieRefold2` — all-order tower **already exists**, in literally the right
  shape: `exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow`
  (`RicciLinearization/RiemannCoefficientPalatiniRefold.lean:18865`), 3rd clause.
* `ricciTop = appCcRS g 4 4 2 (daTrans g gm T) (dagTopOp g gm)` and the metric
  deviation `Φmet(gm) − Φmet(g)` — **no all-order producer**.  `ricciTop_h2`
  (`…LowBaseAction.lean:9656`) and `phi_dev_h2` (`LowRegPathSplit.lean:461`) are
  built from fixed-order-two private helpers (`full_slot_h2_low`, `app_h2_mul`,
  `curvMono_h2`, `connLow_h2_low`).

**PLANNER DECISION required.**  The `lieRefold2` producer gates on
`2·finrank ℝ E + 10 ≤ a` (dim 3: `a ≥ 16`) and consumes a *pointwise jet window*
`∀ j ≤ a+2, ‖∇ʲT‖ ≤ R`, not an `L^∞` bound.  Reusing it therefore means
re-gating `topKer_jet` → `c2_jet_tower` → `a2_ladder` to `a ≥ 16`, which
**undoes the `a ≥ 3` bottom that §5.1d just bought** (`H⁵` → `H^{18}`).  The
alternative is to prove all three summands ball-free by the Moser route,
keeping `a ≥ 3`.  Recommendation: keep `a ≥ 3` and pay the Moser route — the
`a ≥ 16` ball is worse than the `H^{10}` the threshold brick already improved on.

**Smallest next statement** (the next brick's unit): an all-order `appCcRS`
product jet estimate at the `Tensor/Estimates/` layer,
`‖∇ⁱ(appCcRS g a b c A B)‖² ≲ C i · (∑_{p≤i}‖∇^pA‖²)(∑_{q≤i}‖∇^qB‖²)`, plus
all-order jet windows for `daTrans`, `dagTopOp` and
`deTurckPhiMetTotal ∘ realizedFam` — the general-`i` replacements for
`app_h2_mul`, `full_slot_h2_low`, `curvMono_h2`, `connLow_h2_low`.  This is its
own multi-session estimate brick, not an API gap.

### 5.1f TK1 STATUS: **DONE**, and it was a stocked wall (2026-08-03)

TK1 — the all-order `appCcRS` product jet estimate of ruling No. 104 — is
**GREEN**.  New file `Analysis/Spectral/Tensor/Estimates/AppCcRSJetMul.lean`
(note: `AppCcRSJetMul.md`), three declarations, **zero `sorry`, all
axiom-clean**, no `maxHeartbeats` bump.  All three are generic in the valences
`(p, r, c)`, so coverage of `topKernel_eq`'s summands — including
`ricciTop = appCcRS g 4 4 2 …` — is total.

Writing `Sₙ X := ∑_{j ∈ range (n+1)} ‖∇ʲ X‖²` (= `lowJetSq g n X` unfolded):

* `appRS_hn_sup` (`:83`) — the **engine**, Moser pairing, **gate-free and
  dimension-free**, sharp in the jet order:
  `Sₙ(appCcRS g p r c Φ W) ≤ C n * (B²·SₙΦ + A²·SₙW)` with `A`, `B` pointwise
  fibre bounds for `Φ`, `W`.
* `appCcRS_jet_mul` (`:196`) — the product form the ruling asked for,
  `Sₙ(appCcRS g p r c Φ W) ≤ C n * SₙΦ * SₙW`, gated at
  `finrank ℝ E / 2 + 1 ≤ n` (dim 3: `2 ≤ n`).  General-`i` replacement for the
  private `app_h2_mul`, which is its `n = 2` case.
* `appRS_hn_hn_hn` (`:266`) — the family's `(A, B)` envelope shape at `2 ≤ n`;
  at `n = 2` it *is* `appRS_h2_h2_h2`.

**The brick was scoped as multi-session; it was neither multi-session nor an API
gap.**  It is a ~200-line composition of four facts already in the tree, every
one of them order-generic *and* arity-generic:
`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
(`MetricArmCoeffJetTower.lean:2361`),
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
(`RemainderCoeffPerOrderJetEnvelopes.lean:862`),
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`SobolevEmbeddingSharpC0JetSum.lean:717`), and — underneath the grid —
`iteratedCovGrad_appCcRS_eq` (`IteratedAppCcLeibniz.lean:90`), the full covariant
Leibniz expansion of `appCcRS` at arbitrary order.  **Stocked-wall instance
thirteen.**

The sharpest form of the lesson this time: `appRS_h2_h2_h2`'s *proof* was
already the general theorem.  Its internal `hterm` is proved for arbitrary `i`;
`hi : i < 3` is consumed only by `Finset.range_mono`, to shrink the running jet
window into the fixed one.  Only the `Finset.range 3` in the **statement** was
order-two.  So: before believing a per-order claim, read the fixed-order
member's proof, not just its statement.

**One gate is real and must be respected downstream.**  `appCcRS_jet_mul`'s
`2 ≤ n` (dim 3) is mathematically necessary, not routing debris: at `n = 0` the
claim is `L²·L² ⊆ L²`, false; `H¹` in dim 3 is not an algebra either.  TK3
should therefore assemble `topKer_jet` through the **gate-free engine**
`appRS_hn_sup`, not through the product form — the engine's `L∞` slot is exactly
what `hδg` with `δ ≤ 1/3` supplies, and it costs no jet orders, so it fits
`topKer_jet`'s `∑_{j < i+2}‖∇ʲT‖²` budget at every `i` including `i = 0`.  The
product form would overrun that budget at `i = 0`.

Remaining in the ruling's sequence: **TK2** (all-order jet windows for `daTrans`,
`dagTopOp`, `deTurckPhiMetTotal ∘ realizedFam`) and **TK3** (the three-summand
assembly).  TK2 is now the load-bearing unknown: TK1 removed the product
calculus, not the operator-family windows, and those windows are where the
`realizedFam` metric dependence actually lives.

### 5.1g TK2 STATUS: **DONE**, all three families, ball-free (2026-08-03)

TK2 — the all-order jet windows for the operator families of ruling No. 104 —
is **GREEN**.  New file
`Analysis/Spectral/Intrinsic/DeTurck/LowRegOpJetWindows.lean` (note:
`LowRegOpJetWindows.md`), 1050 lines, 34 declarations, **zero `sorry`, zero
`axiom`, no `maxHeartbeats` bump, no linter warnings**.  Campaign sorry census
unchanged at exactly ONE (`topKer_jet`): TK2, like TK1, was a producer brick.

**All three families landed, each with derivative offset `w = 0`.**  Since
`topKer_jet`'s budget `∑_{j ∈ range (i+2)}` is `w = 1`, **every family has a
full order of slack** — nothing to absorb in TK3's budget arithmetic.

| family | window | replaces |
|---|---|---|
| `daTrans` | `moserWin_daTrans` (`:890`) | inline `hTrans` of `ricciTop_h2` |
| `dagTopOp` | `moserWin_dagTop` (`:792`) | inline `hDag` of `ricciTop_h2` |
| `deTurckPhiMetTotal ∘ realizedFam` | `moserWin_phiDev` (`:967`) | `phi_dev_h2` |

plus the assembled `moserWin_ricciTop` (`:918`, the ball-free `ricciTop_h2`) and
the supporting tower `moserWin_sharp`/`_fullSlot`/`_gInvDiff`/`_connLow`/
`_daWeight`/`_curvMono` — the general-`i` replacements for `sharp_h2_low`,
`full_slot_h2_low`, `inv_coeff_h2`, `connLow_h2_low`, `curvMono_h2`.

**The device that made it affine.**  A single predicate
`IsMoserWin g T A S X` = (pointwise fibre bound `S`) ∧ (affine jet envelope
`A n · (1 + lowJetSq g n T)`).  Carrying the `L∞` half *alongside* the jet half
is the whole trick: `appRS_hn_sup` multiplies each arm's `L∞` bound by the
other arm's `L2` jet, so **a product of two windows is again a window**, and
affinity is preserved with no ball and no order gate.  This is precisely what
the fixed-order-two route could not do — `ricciTop_h2` gets `C·jetΦ·jetW` and
must assume `lowJetSq g 2 P ≤ 1` to linearize.  TK1's routing instruction (use
the engine, not the product form) was therefore not just a budget optimization:
it is what removes the ball.

**Stocked-wall instance fourteen, twice over.**
(i) `sharpFlatEndoCc_lowOrder_jetL2_radiusFree` (`DeTurckVFJetRadiusFree.lean:428`)
is *already all-order*: its cap `a` is a free parameter with conclusion
`∀ i ≤ a+1`, so `a := 2·finrank+10+n` gives every order.  The privates
`sharp_h2_low` and `sharp_h3_rf` are byte-identical invocations differing only
in `2` vs `3`.
(ii) The `private` `curvMono_pair` (~190 lines of index work) that made family
`daTrans` look expensive **has a public wrapper**, `LowBaseInternal.curvMono_eq`
(`…LowBaseAction.lean:8985`), in the file's *second* `LowBaseInternal` block,
together with the public `monoPerm`.  The file has two disjoint public-export
blocks (`:3372–3835` and `:8976–9008`); grepping only the first is what produced
the "no all-order producer" reading in §5.1e.  New rule to carry: in
`…LowBaseAction.lean`, grep **both** `LowBaseInternal` blocks before declaring a
helper unreachable.

**Correction to §5.1e's inventory.**  "`ricciTop` and the metric deviation have
no all-order producer" was right about the *producers* but wrong about the
difficulty: the metric-deviation half's per-order producers
(`traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2` and its
`ricciArmPrincipalCoeff` sibling, `RemainderCoeffL2JetMoser.lean:199,365`) were
already order-generic; the only gap was a ball-free window for their common
factor `gInvDiffSlotCoeff`, which is one `moserWin_sub` away from the sharp
engine (`moserWin_gInvDiff`, `:717`).

**What TK3 still owes.**  Only `lieRefold2`'s Moser window (deliberately out of
TK2's scope — ruling No. 104's inventory names three families, not four) and
the `IsPathPert` discharge along the radial path.  `moserWin_curvMono` is
stated over a *general* window argument, so it applies to `lieRefold2`'s
monomials verbatim; the one difference is that `lieRefold2`'s second metric
argument is the moving `gm`, so `lieCovPair g gm` is not a constant and needs
its own window (`LowBaseInternal.pairTrace_eq`, `:9000`, factors it into two
`pureTrace`s).  Full handoff in `LowRegOpJetWindows.md`.

### 5.1h TK3 STATUS: **DONE** — `topKer_jet` proved, `a2_ladder` UNCONDITIONAL (2026-08-03)

TK3 — the assembly of `topKer_jet` from TK1's product engine and TK2's family
windows — is **GREEN**.  `topKer_jet`
(`Analysis/Spectral/Intrinsic/DeTurck/LowRegC2JetTower.lean:196`) is proved,
sorry-free and axiom-clean, and with it `c2_jet_tower` and **`a2_ladder`**
(`LowRegLadderRung.lean:144`, `:232`) become **unconditional**.

**The F6 estimate chain now has ZERO `sorry`.**  Campaign sorry census after
this brick: the only remaining campaign `sorry` is `lowreg_spatialMass`
(`ShortTime/LowRegAllOrderJet.lean:1053`), which is upstream of this chain and
is brick E1′'s target.  (Outside the campaign: the Weyl citation-`sorry` at
`ShortTime/WeylEigenvalueCountingBound.lean:115`, policy pending, and
`Sobolev/TensorHilbert/Rellich.lean:63`.)

**What TK3 actually had to do.**  The handoff listed two producer jobs; both
were cheap.  The expensive item was a *quantifier-order* problem the handoff
did not name:

1. **`T`-uniformity (the real work).**  `topKer_jet` produces `Kk` **before**
   `T` — its consumer `c2_jet_tower` is written that way, and a state-dependent
   constant would defeat the ladder.  Every TK2 family window, however, bound
   `T` as a parameter *before* its `∃ A S`, i.e. `∀ T, ∃ A`, which does not
   give `∃ A, ∀ T`.  All the constants were already morally state-free
   (`moserWin_const` bounds background objects, `moserWin_appRS`'s `C` comes
   from `appRS_hn_sup g p r c`, `moserWin_self`'s envelope is `1`,
   `moserWin_sharp`'s comes from the radius-free engine), so TK3 hoisted `T`
   inside the existential in twelve statements (`moserWin_const`, `_appRS`,
   `_sharp`, `_fullSlot`, `_gInvDiff`, `_connLow`, `_dagTop`, `_daWeight`,
   `_curvMono`, `_daTrans`, `_ricciTop`, `_phiDev`).  Each proof needed only
   `intro T` moved past `refine ⟨…⟩` and the `T` argument dropped from the
   corresponding calls; the refactor checked clean on the first pass.  **Rule
   to carry: fix a window predicate's quantifier order from the final
   consumer's signature, not from the local statement.**
2. **`lieRefold2`'s Moser window — fifteenth stocked wall.**  The "moving second
   metric" difficulty dissolves: `LowBaseInternal.pairTrace_eq` factors
   `lieCovPair g gm` into two `pureTrace g gm k`, and `pureTrace_split`
   (`CurvatureCoefficientDifferenceJetTower.lean:6477`) factors each into a
   background double trace times `slotInsertEndoCc g (k+1)
   (gInvDiffRaisedEndoField g gm)` — the *same* inverse-difference endomorphism
   `moserWin_gInvDiff` already windows, at a different slot.  So TK3 split
   `moserWin_gInvDiff` into `moserWin_gInvSlot k` plus a three-line corollary,
   and got `moserWin_pureTr` → `moserWin_lieCovP` → `moserWin_monoMov` →
   `moserWin_lieRef2` for two `moserWin_appRS` steps each.  Nothing new about
   tensor calculus.  (A window for `symmS g T` was also needed and is free:
   `iteratedCovGrad_symmS_eq` plus the public per-order permutation isometry
   `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection`, so `symmS g T`
   inherits `T`'s window with the *same* constants and without assuming `T`
   symmetric.)
3. **The `IsPathPert` discharge** (`pathPert_rad`) is ~30 lines: along the
   radial path the perturbation is `s • T` (`convexPerturbation g T 0 s`), so
   the fibre bound is `convexPerturbation_gFibreOpBound_abs` with
   `|1−s|δ + |s|δ = δ` — exactly `lieRefold2_cap`'s step — the tie is
   `realizedFam_inner_of_mem ∘ Icc_subset_realizedSmallSet`, and both
   dominations are `s² ≤ 1`.  That single lemma is the entire source of
   `s`-uniformity: **no constant anywhere in the chain mentions `s`.**

**Budget, as predicted.**  All windows are `w = 0` against a `w = 1` budget, so
the last step of the assembly literally throws away a whole order via one
`Finset.sum_le_sum_of_subset_of_nonneg`.  The realized constant is
`Kk i = |2(2(A_lie i + A_phi i) + 4·A_ric i)|`; the absolute value exists only
so that `∀ i, 0 ≤ Kk i` is provable before `T` is introduced (window
nonnegativity, `moserWin_nnA`, needs a window instance and hence a state).

**Verification.**  Focused checks clean on both edited files, no warnings; one
targeted module build each of `…DeTurck.LowRegOpJetWindows` and
`…DeTurck.LowRegLadderRung` (the latter covering `LowRegC2JetTower`) succeeded.
Axiom census clean (`propext, Classical.choice, Quot.sound`) on `topKer_jet`,
`c2_jet_tower`, `a2_ladder`, `path_add_sub_jet`, `moserWin_lieRef2`,
`moserWin_lieCovP`, `moserWin_monoMov`, `moserWin_pureTr`, `moserWin_symmS`,
`pathPert_rad`, `moserWin_ricciTop`, `moserWin_phiDev`.  No `maxHeartbeats`
added.

### 5.2 First estimate sub-brick, once (S1₂)'s statement lands

**E0's `k = 0` rung, stated norm-level and dim-3-explicit:**

> On a closed 3-manifold, for `g₀` and the `H²` ρ-ball, there are `Cδ₀ < 1` and `C₀`
> with `‖N(T) − N(0)‖_{H¹} ≤ Cδ₀‖T‖_{H³} + C₀‖T‖_{H²}` for every symmetric
> `T : SmoothCcTensor g₀ 0 2` with `‖T‖_{H⁴} ≤ R₀`.

Reasons to start here: (i) it is the exact `k = 0` instance of the only inequality
F6 actually needs; (ii) it is *below* the (S1₂) statement, so it stays valid however
that statement is finally phrased; (iii) its two halves already exist —
`principal_arm_h2` (`PrincipalCoeffH2.lean:589`, `H³ → H²`) and `appCc_h2_h3_h1`
(`H2H3Principal.lean:189`, the `H¹`-output family) — so it is an *assembly*, and
whether it assembles cleanly is the single best early signal for whether E0b's
induction will close.  Only after it is green should E0b (the `k`-ladder) begin.

### 5.3 Precise failure shape that constitutes a route obstruction

Per the campaign stop-signal, F6 is a **route error** only if the base-order-2
dissipation is *unstatable*.  Concretely, the obstruction has landed iff **all
three** hold:

1. **E0b's constant degrades.**  The `k`-ladder can only be closed with a top
   constant `Cδ₀(k)` that grows with `k` (e.g. because the `H²`-algebra constant of
   `appCc_h2_h2_h2` (`H2H4Principal.lean:31`) enters once per rung), so no
   `Cδ₀ < 1` uniform in `k` exists — and hence
   `galerkin_energy_uniform_bound_perScale`'s `hCδ : Cδ < 2` cannot be met at any
   rung beyond a finite one.
2. **The repair requires a σ-generic completed coefficient family.**  I.e. the only
   way to recover `k`-uniformity is a bounded `H^{σ+2} → H^σ` *completed* (not
   smooth-core) Nemytskii/coefficient operator at generic real `σ`, which No. 98
   ruled out at `a = 2` — every existing one is gated `2·finrank + 10 ≤ a`.
3. **The smooth-core route cannot substitute**, i.e. the estimate genuinely fails on
   `finiteEigenCombo` states and not merely in the completed setting.

Anything short of that — a missing fixed-order lemma, a `k`-dependent `C_k` on the
**lower** order (which is allowed: L4's `Crem : ℕ → ℝ` is already `k`-dependent), a
Moser envelope that needs one more jet, or an awkward retraction — is a normal
estimate gap, not an obstruction.

Note the two clauses of `FORCEJETMASS_PLAN.md` §8 are *independent*.  §1.3 shows the
F1 clause is already partly decided against a cheap outcome (`bal_gridcore` is
load-bearing), but that says nothing about F6: the a = 2 route does not go through
`bal_gridcore` at all — with `a` gone there is no budget predicate to split on.

---

## 6. Open questions this recon did NOT settle

* Whether `Cδ₀` in E0b can be made `k`-uniform.  **This is the whole risk.**  Not
  answerable by grep; needs the `k = 0` and `k = 1` rungs written out.
* Whether `exists_smoothCcTensor_of_allOrder_spectralMass_local`
  (`ForcingFiniteOrderTimeRegularity.lean:513`, `private`, call sites `:4461`,
  `:5042`) should be promoted or re-derived — that file is mid-edit by a sibling
  agent and was not read beyond the declaration line.
* The correct retraction norm at a = 2 (`H²` ball, matching the low lane's `hreal'`,
  vs `H⁴` ball, matching `radialScaleSmooth g₀ 2`).  `principal_arm_h4_h2` uses the
  `H²` ball with `H⁴` data, suggesting `H²` for the retraction and `H⁴` only as the
  a-priori data class.
  **SETTLED in §7.6 below — and the answer is neither: the ladder forces `H⁵`.**

---

## 7. Assembly sequence to `lowreg_spatialMass` (2026-08-03)

Read-only recon, after TK3 closed the F6 estimate chain (§5.1h).  Numbered §7
because §6 was already taken; this is the section the planner asked for as "§6
assembly sequence".  Scope: the complete brick sequence from today's state to
`lowreg_spatialMass` (`ShortTime/LowRegAllOrderJet.lean:1053`) **proved**.

### 7.1 What is actually below the frontier

`lowreg_spatialMass`'s docstring names its own template:
`deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm`
(`HeatSemigroup/GalerkinLimitUniformMass.lean:1125`).  That template's proof body
(`:1152`–`:1218`) uses **exactly five** ingredients and nothing else:

| # | ingredient | file:line | `a = 2` status |
|---|---|---|---|
| G1 | `deTurckGalerkin_solution_existsSymm` (Galerkin ODE) | `GalerkinParabolicEnergyDeTurck.lean:746` | rebuild (E4) |
| G2 | `deTurckGalerkin_forcing_closure_perScaleSymm` (per-scale closure) | `:1512` | rebuild (E0c/E2) — **the estimate** |
| G3 | `galerkin_energy_uniform_bound_perScale` (Grönwall hierarchy) | `GalerkinParabolicEnergy.lean:220` | **reuse verbatim, `σ₀ : ℝ` free** (E5) |
| G4 | `galerkinSol_tendsto_solField_perModeConvSymm` (Galerkin → `perModeConv`) | `GalerkinLimitUniformMass.lean:1051` | rebuild — **the second-largest brick** |
| G5 | `fatou_sq_mass` | `Intrinsic/GalerkinCompactness.lean:28` | **reuse verbatim, gate-free** |

plus one weight-domination step (`Real.rpow_le_rpow_of_exponent_le` on
`σ ≤ a + k`) that is three lines of pure assembly.  So the σ-uniformity in the
conclusion is bought **entirely** by the per-scale hierarchy: `Cδ < 2` at every
rung `k`, which is precisely what `a2_ladder` now supplies.

### 7.2 BLOCKER FOUND: the frontier statement is missing two hypotheses

**This must be fixed before any estimate brick is dispatched.**

`lowreg_spatialMass` (`:1028`–`:1053`) binds

```lean
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
```

with **no hypothesis on `FHi` at all**, and no state ball.  `liftHiN`
(`ShortTime/LowRegForceHi.lean:132`) is
`staticForce g g 2 + lowA2Hi … v + FHi (ι₃₄ v) (lowRadialH3 …)`, so the third
summand is an arbitrary `H²`-valued map.  Take `FHi x := ⟨·, e⟩ • w` with
`w ∈ H² \ H³`: the trajectory then carries a genuine `H²`-only component and
`Summable (fun i => weight i σ * (perModeConv …)²)` fails for σ large.  The
statement is therefore **not merely unproved — it is false as written.**

The unique call site already has the repair in scope.  `lowreg_forceJetMass`
(`:1089`) builds

```lean
  have hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1) (hδ' : gFibreOpBound … δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN … FHi (smoothCcToTensorHs g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt …).coeff i
```

at `:1166`–`:1180`, and carries `hballU` (`:1144`), and passes **both** to
`lowreg_forceDriver` (`:763`, `:782`) — but at `:1184` passes **neither** to
`lowreg_spatialMass`.  `hbridge` is exactly the tie that replaces the
supercritical `htie`/retraction device: it says `liftHiN … FHi` *is* the
smooth-core `deTurckSmoothN g g 2` on the ball, which is the only reason a
Galerkin argument can be run at all.

**Brick S0 (must be first): widen `lowreg_spatialMass`'s signature by `hbridge`
and `hballU`, copied verbatim from `lowreg_forceDriver`'s binders, and add the
two arguments at the `:1184` call site.**  Pure statement surgery, `sorry`
retained, tree stays green.  Honest-input instance; recorded as **stocked-wall
instance seventeen** in the "the repair was already in scope at the call site"
sense — the difference from instances 13–16 is that here what was stocked is a
*hypothesis*, not a producer.

### 7.3 Item-by-item census (E0c, E1–E5, restated against today's tree)

| item | statement gist | stocked | gap |
|---|---|---|---|
| **E0c** | Moser envelope for the coefficient jets at base 2 | **~90%** | superseded: `c2_jet_tower` (`LowRegC2JetTower.lean:144`) IS the `C2` envelope, proved; only the `C0`/`C1` envelopes remain, and those are §7.4's A1 bricks.  No separate E0c brick. |
| **E0d (new)** | the `a₁` ladder `‖a₁ T‖_{H^m} ≤ C m ‖T‖_{H^{m+1}}` | ~55% (engine + window algebra + path layer all exist) | needs `C0`/`C1` all-order Moser windows + the `Hs` assembly.  §7.4. |
| **E0e (new)** | `n_diff_hm_rung`: `‖N T − N 0‖_{H^m} ≤ Cδ₀‖T‖_{H^{m+2}} + C m ‖T‖_{H^{m+1}}` at every `m` | ~70% | one `norm_add_le` over `lowData_split` + `a2_ladder` + E0d.  Assembly only. |
| **E1** | fibre-smallness at a = 2 | **100%** | `hs2_opBound_at_two` (`MaxRegSolutionJointlySmooth.lean:1590`) + `radialScaleSmooth` (`SobolevNonlinearityExistence.lean:2265`) + `norm_smoothCcToTensorHs_radialScaleSmooth_le` (`:2271`) all exist.  Wiring only. |
| **E2** | spectral wrapper stack L3→L0 at a = 2 | ~10% built, ~100% *shape*-stocked | mechanical transcription of `:824`/`:961`/`:1265`/`:1361`/`:1512` with `deTurckSobolevNHa2Symm ↦ deTurckSmoothN g g 2 ∘ radialScaleSmooth`; every tool the bodies use is gate-free (§1.2).  Four files' worth of *shape*, zero new mathematics. |
| **E3** | promote `finiteEigenComboHs_eq_smoothCcToTensorHs` | 0% (trivial) | two `private` clones at `GalerkinParabolicEnergyDeTurck.lean:529` and `:808`; promote one to `Garding/EigenCombination.lean`, delete the other. |
| **E4** | a = 2 Galerkin ODE existence | ~40% | `forward_solution_of_lipschitzWith_affineBound` (`Analysis/ODE/GlobalLipschitzAffineExistence.lean:12`) is gate-free; `galerkinCoordEmbed/Restrict/Diag/Field` (`:79`–`:172`) are gate-free.  Missing: the `N`-dependent Lipschitz + affine bound for `w ↦ deTurckSmoothN g g 2 (radialScale (finiteEigenCombo S w))`. |
| **E5** | plug into the Grönwall engine | **100%** | `galerkin_energy_uniform_bound_perScale` verbatim, `σ₀ := (2 : ℝ)`. |
| **G4** | Galerkin coordinates → `perModeConv (timeModeCoeff fHi i)` | ~15% | `tendsto_perModeConv_of_tendsto_timeL2` (`GalerkinForcingTimeL2Limit.lean:209`) and `fatou_sq_mass` are gate-free; the 14 supporting privates of `GalerkinLimitUniformMass.lean` (`:33`–`:902`) are all built on the retracted completed operator and must be re-derived from `hbridge`.  **This is the largest single unbuilt item.** |

Pure assembly (quantifier bookkeeping / triangle inequalities): E0e, E3, E5, the
weight-domination step, and the `hLHS_eq`/`hsplit` layers of E2.
Real estimates: E0d only.  Everything else is *construction* (E4, G4) — new
definitions and their basic properties, not new inequalities.

### 7.4 The a₁-arm verdict: SAME mechanism, strictly easier, no new tower design

> **REFUTED (planner annotation, 2026-08-03, ledger No. 111).**  The
> A1a/A1b implementation (executor report in `UNIF_EXISTENCE_PLAN3.md`)
> showed the `IsMoserWin` vocabulary CANNOT express the C0/C1 summands:
> both contain the bare `∇P` (`connDiffSection gm g`), which has no
> order-0 fibre cap from `δ ≤ 1/3` (the certificate caps `P`, not
> `∇P`), and `appRS_hn_sup` needs caps on BOTH factors.  This section
> read the derivative COUNT correctly and the CAP AVAILABILITY
> incorrectly; the C2 arm was special (refold made it
> metric-algebraic).  The correct route is the radius-free per-order
> currency (`antidiagonalTupleGrid_integral_radiusFree` engines);
> §7.6 rows A1a/A1b are re-scoped behind brick A1-CUR — see ledger
> No. 111.  Towers `c1_jet_tower`/`c0_jet_tower` ARE stated and landed
> (over integrand sorries `low1Ker_jet`/`selfLow_jet`), and
> `selfLow_split` is the mandatory regrouping — a frontier on
> `rhsSelfLow`'s literal summands at `range (i+2)` would be FALSE.

`LowBaseActionData.a1` (`DeTurckRemainderLowBaseAction.lean:3330`) is

```lean
  appCc g 2 2 A.C0 W + appCc g 3 2 A.C1 (iteratedCovGrad g 0 2 1 W)
```

so the a₁ arm carries **one** derivative of the state where a₂ carries two.  In
the ladder `‖N T − N 0‖_{H^m} ≤ Cδ₀‖T‖_{H^{m+2}} + C m ‖T‖_{H^{m+1}}` the whole
a₁ arm therefore lands in the **lower** slot `H^{m+1}`, where an `m`-dependent,
`R₀`-dependent constant is *allowed* (§5.3 explicitly permits it; L4's `Crem` is
already `ℕ → ℝ`).

**Consequence: the a₁ arm needs no smallness, no `Cδ₀ < 1`, and none of the
commutator/resolvent machinery.**  `oneMinusConnLapSmoothIter`,
`master_appCc_jet_le_sharp` and `appCc_cap_hs_le` are *not* on its route.  (They
would in fact be the wrong tool: `master_appCc_jet_le_sharp`'s conclusion loses
three orders — `Cm q * ‖(1−Δ)^p T₀‖_{H^{q+3}}` (`ConnLapCommutatorCoefficientTame.lean:496`) —
which the resolvent commutator repays and a bare first-order arm cannot.)

The right route is TK1+TK2's, verbatim:

* engine: `appRS_hn_sup` (`Estimates/AppCcRSJetMul.lean:83`) — gate-free,
  dimension-free, arity-generic, `Sₙ(appCcRS Φ W) ≤ C n (B² SₙΦ + A² SₙW)`;
* window algebra: `IsMoserWin g T A S X` (`DeTurck/LowRegOpJetWindows.lean:106`)
  = pointwise cap `S` **and** affine jet envelope `A n (1 + lowJetSq g n T)`,
  closed under `moserWin_add/_sub/_smul/_const/_appRS/_slot/_dom/_reindex/`
  `_rsperm/_endoIns/_self` (`:175`–`:538`).  Because a window carries the `L^∞`
  half alongside the `L²` half, a product of windows is a window — this is what
  gives **both** the pointwise cap the a₁ arm needs for its `B` and the jet tower
  it needs for its `SₙΦ`, in one object;
* path layer: `path_add_sub_jet` (`LowRegC2JetTower.lean:78`) and
  `path_jetL2_le` (`Tensor/CovGrad/ParametricJetIntegral.lean:331`), both
  order-generic, both already used by `c2_jet_tower`;
* `pathPert_rad` (`LowRegOpJetWindows.lean:1278`) discharges `IsPathPert` along
  the radial path and is *shared* — it is `s`-uniform and coefficient-agnostic.

The two coefficients are path integrals of small, already-vocabulary integrands:

* `A.C0 = selfLowInt g g T … + phiMetCurvCoeff g g g` (`:3355`), with integrand
  `rhsSelfLow` (`:3658`) `= (-2)•ricciSafeLow g gm (s•T) + deTurckLieCoeffField g gm g_bg`
  `+ lieCorr0Field g gm g_bg − edgeLiePairFam g T … lieRefoldQ lieRefoldEps s`
  — four summands, the last in the *same* `lieRefold` vocabulary TK3 already
  windowed (`moserWin_lieRef2`, `moserWin_monoMov`, `moserWin_lieCovP`);
  the constant summand is one `moserWin_const`.
* `A.C1 = rhsLow1PathIntegral g g T 0 …` (`DeTurckCoefficients/RHSPathIntegral.lean:167`),
  integrand `rhsLow1Coeff` (`RHSThreeArmCancel.lean:300`)
  `= (-2)•linearizedRicciConnDiffOrder1Coeff g₀ T T' hδ hδ' s + deTurckLieArm1Coeff g₀ (realizedFam …) g_bg`
  — **two** summands.

**Partial stock, with a de-gating opportunity.**  All-order producers for *both*
`C1` summands already exist:
`linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic`
(`Sobolev/TensorHilbert/RicciConnDiffOrder1TameEnvelope.lean:1240`) — whose
conclusion `(∀ x, rfns ≤ Λ²) ∧ ∀ l, ‖∇ˡ …‖² ≤ K l (1 + ∑_{j<l+2}‖∇ʲP‖²)` **is
literally `IsMoserWin` unfolded** — and
`deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
(`Sobolev/TensorHilbert/DeTurckLieArm1CoeffL2JetBound.lean:4917`).  Both gate at
`2·finrank ℝ E + 10 ≤ a` (dim 3: `a ≥ 16`) and both are ball-based.  This is
**exactly** the situation TK3 faced with `lieRefold2`'s producer, and ruling
No. 104's decision applies unchanged: **do not re-gate the ladder to `a ≥ 16`;
pay the Moser route and keep `a ≥ 3`.**  Worth one cheap probe first, though —
the `:1240` producer's gate is passed straight through to
`connDiffContrInsertionField_…_generic` (`:982`), the same forwarding pattern
that `appCc_cap_hs_le` (§5.1c) de-gated for free.

**Consumer signature that fixes the quantifier order** (TK3's rule).  The a₁
tower's consumer is the new `a1_ladder`, which must mirror `a2_ladder`
(`LowRegLadderRung.lean:232`) exactly — constants before the state:

```lean
theorem c2_jet_tower
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x), ccTensorBilin g T x u v = ccTensorBilin g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound g (ccTensorBilinSymm g T) δ)
        (hδZ : gFibreOpBound g (ccTensorBilinSymm g (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ, ‖iteratedCovGrad g 4 2 i (lowBaseData g g T … ).C2‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad g 0 2 j T‖ ^ 2)
```

(`LowRegC2JetTower.lean:144`–`:164`, elaborated form; instance arguments elided.)
The `C0`/`C1` towers must be stated in this shape with `4 2 i … .C2` replaced by
`2 2 i … .C0` and `3 2 i … .C1` — same `∃ Kc, ∀ T` order, same
`range (i + 2)` budget (TK2's windows are all `w = 0`, so there is again a full
order of slack).

### 7.5 The one genuine design risk: the ball order

`a2_ladder` reads `ha : 3 ≤ a` on the a-priori ball `‖T‖_{H^{a+2}} ≤ R₀`, i.e.
**`H⁵` at the bottom**, and this is *not* cosmetic: `master_appCc_jet_le_sharp`
uses `hballf` at `f (i + m + dc)` (`ConnLapCommutatorCoefficientTame.lean:564`)
with `m < finrank/2 + 2 = 3` and `i ≤ t`, and again inside `hs_extreme_interp`
(`:719`); at `a = 3, t = 0, dc = 3` that reaches `f 5`.

But the a = 2 lane's trajectory control is `H²` (`hballU`) and its maximal
regularity gives `C_t H³ ∩ L²_t H⁴` — **never `H⁵`**.  So the supercritical
device (retract with `radialScaleSmooth g₀ a R₀`, then use `hgforce` to show the
retraction is inert along the true trajectory) does **not** transplant: at
`a = 2` there is no `H⁵` a-priori bound on the trajectory to make a `H⁵`
retraction inert.

Three candidate resolutions, in increasing cost:

1. **Retract at `H⁵`, keep the retraction in the limit.**  The Galerkin scheme
   and the energy hierarchy run unconditionally; the limit solves the
   *retracted* equation.  Identify it with `fHi` using `hbridge` **plus** a
   separate argument that the trajectory's `H⁵` norm stays `≤ R₀`.  That extra
   argument is a genuine continuous-induction / maximal-time brick — the only
   place in the whole sequence where a new analytic idea is required.
2. **Bootstrap inside the hierarchy.**  Note the ball is a *fixed* low order
   (`H⁵`), independent of the rung `m`, so only the bottom three scales are
   circular; close them by continuity in `t` (the energies are `ContinuousOn`,
   `galerkinEnergy_continuousOn`) with a first-exit-time argument.  Cheaper than
   (1) but still an analytic brick.
3. **Lower the ball order in the engine.**  Re-examine whether `hs_extreme_interp`
   at `:719` can trade against `f (a+2)` differently; the `a ≥ 3` bottom was
   already bought once by parameterizing `t` (§5.1d).  A second such pass would
   have to reach `a = 1` (`H³` ball) to match `C_t H³`.  §5.1c's arithmetic says
   the two `master_…` call sites need `0 ≤ t ≤ a−3` and `1 ≤ t ≤ a−2`, which is
   empty below `a = 3`.  **Assessed: blocked, do not spend a session on it.**

**Recommendation: (2), with (1) as the fallback.**  Either way this is a
*design ruling the planner should make before E2/G4 are dispatched*, not an
executor choice.  It is the successor of §6's "correct retraction norm" open
question, now sharpened: the answer is `H⁵`, and the cost is a bootstrap.

### 7.6 Brick sequence

| # | brick | target file | difficulty | depends |
|---|---|---|---|---|
| **S0** | widen `lowreg_spatialMass` by `hbridge` + `hballU`; wire `:1184` | `ShortTime/LowRegAllOrderJet.lean` | routine (statement surgery) | — |
| A1a | `IsMoserWin` for `rhsLow1Coeff`'s two summands; `c1_jet_tower` | new `DeTurck/LowRegC01JetTower.lean` | missing API lemma → real estimate | — |
| A1b | `IsMoserWin` for `rhsSelfLow`'s four summands; `c0_jet_tower` | same file | real estimate | A1a (shares the window vocabulary) |
| A1c | `a1_ladder` (`‖a₁ T‖_{H^m} ≤ C m ‖T‖_{H^{m+1}}`) | `DeTurck/LowRegLadderRung.lean` | routine (engine + `hsJet_le`/`hs_le_jet`) | A1a, A1b |
| A1d | `n_diff_hm_rung` (E0e: full `N T − N 0` ladder at every `m`) | `DeTurck/LowRegLadderRung.lean` | routine assembly | A1c, `a2_ladder` |
| **R0** | **PLANNER RULING** on §7.5 (ball order / bootstrap) | — | design | A1d (informs the shape) |
| E3 | promote `finiteEigenComboHs_eq_smoothCcToTensorHs`, delete clone | `Garding/EigenCombination.lean` | trivial | — (dispatchable in parallel) |
| E1′a | a = 2 spectral wrappers L3→L1 (`_spectralCoercive_split'`, `_sobolevSplit_perScale'`, `_tame_diff_mass_perScale`, `_seed_mass`) | new `HeatSemigroup/LowRegGalerkinEnergy.lean` | routine (transcription) | A1d, R0, E3 |
| E1′b | a = 2 `..._forcing_dissipation_perScale` + `..._forcing_closure_perScale` (L0) | same file | routine | E1′a |
| E4 | a = 2 Galerkin ODE existence on `deTurckSmoothN g g 2 ∘ radialScaleSmooth ∘ finiteEigenCombo` | same file | missing API + one design choice | E3 |
| G4 | a = 2 `galerkinSol_tendsto_solField_perModeConv` from `hbridge` | new `HeatSemigroup/LowRegGalerkinLimit.lean` | **largest brick**; construction + limit analysis | E4, S0 |
| Z | `lowreg_spatialMass` assembly (5 ingredients + weight domination) | `ShortTime/LowRegAllOrderJet.lean` | routine | all |

#### 7.6a STATUS: S0 and E3 both **DONE** (2026-08-03)

* **S0 — DONE.**  `lowreg_spatialMass` now binds `{R ρ δ : ℝ}`, `hRρ : R ≤ ρ`,
  and `hbridge` + `hballU` between `hfix` and `(σ : ℝ)`, exactly as §7.7
  prescribes; the `:1184` call site passes all three.  One extra edit §7.7 did
  not anticipate: the frontier needed
  `open …Analysis.Parabolic.TensorSpectral (symmS) in` above it, because
  `hbridge` mentions `symmS` and this file opens it per-declaration rather than
  at file scope.  Green first try, sorry census still exactly one, axiom census
  unchanged.  **The frontier is now honestly stated and still 0% proved.**
* **E3 — DONE, but §7.6's target file was wrong.**  `Garding/EigenCombination.lean`
  **cannot** host the bridge: `smoothCcToTensorHs` is defined in
  `DeTurck/DeTurckRemainderDefs.lean`, which *imports* `Garding.EigenCombination`.
  The lemma landed in `DeTurckRemainderDefs.lean` — the lowest module where both
  sides are in scope, and the canonical home of the right-hand side — as public
  `finiteEigenComboHs_eq` (short name, project budget).  Both private clones in
  `GalerkinParabolicEnergyDeTurck.lean` are deleted and their two live uses
  rewired; the `:529` clone turned out to have **zero** uses (the apparent hits
  were substring matches on the `gscr_` sibling).

### 7.7 First dispatchable brick

**S0.**  It is first because every later brick's statement depends on the
frontier's final signature, and because it converts a false statement into a
true one at zero proof cost.

* *Consumer signature (verbatim, `LowRegAllOrderJet.lean:763`–`:786`)* — copy
  `lowreg_forceDriver`'s `hbridge` binder (`:763`–`:773`) and `hballU` binder
  (`:782`–`:786`) into `lowreg_spatialMass` between `hfix` and `(σ : ℝ)`.
  `lowreg_forceDriver` binds `{R ρ δ : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ) …`; the
  frontier currently binds only `{ρ δ : ℝ} (hρ : 0 < ρ)`, so `R` and `hRρ` come
  in with `hbridge`.
* *Producer inventory*: nothing new — `lowreg_forceJetMass` already has
  `hbridge` in scope as a `have` at `:1166` and `hballU` as its own binder at
  `:1144`; the `:1184` call gains two arguments.
* *Verification recipe*: focused check of `LowRegAllOrderJet.lean` only.  The
  file's real-`sorry` count must stay exactly one; no other file changes.

Immediately parallelizable with S0: **E3** (different file, no dependency).

**A1a is the first mathematical brick**, and is dispatchable as soon as S0
lands.  Handoff data: consumer = `a1_ladder`, whose shape is `a2_ladder`
(`LowRegLadderRung.lean:232`) with `.a2`/`m+2` replaced by `.a1`/`m+1` and the
top constant deleted; the tower statement is `c2_jet_tower`'s (quoted in §7.4)
with valence `3 2` and field `.C1`.  Producer inventory: `appRS_hn_sup`
(`AppCcRSJetMul.lean:83`), the eleven `moserWin_*` closure lemmas
(`LowRegOpJetWindows.lean:175`–`:538`), `moserWin_gInvSlot` (`:811`),
`moserWin_connLow` (`:874`), `moserWin_curvMono` (`:966`), `pathPert_rad`
(`:1278`), `path_jetL2_le` (`ParametricJetIntegral.lean:331`),
`rhsLow1_path_joint` (`RHSThreeArmCancel.lean:333`),
`rhsLow1PathIntegral` (`RHSPathIntegral.lean:167`), and — as the cheap probe —
the two gated all-order producers named in §7.4.

### 7.8 Sequencing constraints (file ownership)

* `ShortTime/LowRegAllOrderJet.lean` — currently being edited by the
  floor-deletion lane (brick B1, near `:1550`).  **S0 and Z touch this file and
  must be sequenced after B1 releases it.**
* `ShortTime/LowRegApplyTwo.lean` — queued bricks B3/B4 of the floor-deletion
  design edit it.  **No brick in this sequence touches it**; the `IsRealizedTwo`
  conjunct swap is independent of the spatial-mass closure, so B3/B4 and A1a–A1d
  can run concurrently.
* `DeTurck/LowRegLadderRung.lean`, `DeTurck/LowRegOpJetWindows.lean`,
  `DeTurck/LowRegC2JetTower.lean` — owned by this lane, currently idle.
* `DeTurckRemainderLowBaseAction.lean` is **other-lane-claimed**; A1a/A1b must
  re-derive from the public API (both `LowBaseInternal` export blocks,
  `:3372`–`:3835` and `:8976`–`:9008`) rather than un-privatizing
  `lowC0_h2_rf` (`:12161`) / `lowC1_h2_rf` (`:13080`).

### 7.9 Honest denominators (2026-08-03, after this recon)

Nothing new was proved; this is a read-only design pass.

* **`lowreg_spatialMass`: 0% proved, and currently FALSE as stated** (§7.2).
  With S0 applied it becomes an honest ~0%-proved frontier.
* **F6 as a whole: ≈ 72%** — unchanged from No. 107.  The estimate chain is
  100%; what this recon adds is that the *remaining* 28% is now itemized and
  contains exactly **one** new real estimate (E0d = A1a–A1c), **one** design
  ruling (R0), and **two** constructions (E4, G4).  It does not contain a second
  `k`-uniformity-style wall.
* **Front 2 (fixed-horizon bootstrap): ≈ 53%** — unchanged.  `lowreg_spatialMass`
  is the last `sorry` on front 2, so its closure is worth the remaining ~47%
  *minus* the floor-deletion bricks B1–B5; call the spatial-mass closure
  **≈ 40 of front 2's 47 remaining points**, i.e. it is essentially the whole
  rest of front 2.
* **After `lowreg_spatialMass`, front 2 still needs**: the floor-deletion
  sequence B1–B5 (`OPTIONB_FLOOR_PLAN.md`) and nothing else on the estimate
  side.  Verified by grep: `LowRegAllOrderJet.lean` has exactly one real `sorry`
  (`:1053`; all other textual hits are docstrings), `LowRegApplyTwo.lean` has
  zero, and `lowreg_joint_two` / `lowreg_joint_smooth` are sorry-free — the
  engine wiring claim holds.
* **(N) `ricci_flow_unif_existence`: 0%** — stated at
  `Evolution/ExtendViaUniqueness.lean:80`, proof not started.  Its dedicated
  machinery ≈ 92%.
* **Whole HCG compactness project: low single digits.**
