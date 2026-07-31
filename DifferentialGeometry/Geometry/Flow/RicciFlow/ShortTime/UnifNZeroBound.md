# UnifNZeroBound.lean — brick E6 (the `D`-number of the six-number horizon)

Status: **LANDED, sorry-free, axiom-clean** (14 public declarations, 484 lines).
Verification: focused check green; targeted module build green; axiom probe green
(`propext, Classical.choice, Quot.sound` only for every declaration).

## What the brick had to produce

`lowreg_partial_sol_of_bounds` (`UnifClassBounds.lean`) takes

```
hzero : ‖lowregNfun g₀ g_bg hδ hCtop hB1 hρ hP hreal ⟨0, _⟩‖ ≤ D
```

with the norm taken in `tensorHs g₀ 0 2 ((1 : ℕ) : ℝ)` — the spectral `H¹(g₀)` currency.
Per-metric, `D` is *defined* to be that norm (`LowRegDenseSolve.lean:454`), so it carries no
class information.  E6 replaces it by a closed number in `(gBase`-data`, Λ, finrank ℝ E)`.

## The route that worked

1. **`N(0)` is a static field.**  `lowRegN = Dense.extend (smoothCore_dense) coreN`, and `0`
   lies in the smooth core (`zero_mem_smoothCore`), so `Dense.extend_eq` (needs continuity of
   `coreN`) gives `N(0) = coreN ⟨0, _⟩`.  The chosen smooth representative of the zero state
   is spectrally zero, and `norm_smoothCcToTensorHs_symmS_le` forces its symmetrization to be
   spectrally zero too, so `smoothN_wd` replaces it by the honest `0 : SmoothCcTensor`.
   Then at `T = 0`:
   * `realizeMetric_zero` : `tensorSectionRealizeMetric g₀ 0 _ _ = g₀`
     (`ccTensorBilin_zero_weight` + `smoothRiemannianMetric_ext_inner`);
   * `rawTensorConnLapSmooth_zero` : the connection Laplacian kills `0`
     (from `rawTensorConnLapSmooth_sub` at `(0,0)`);
   * hence `deTurckRem_zero` : `deTurckSmoothRemainder g₀ g_bg 0 = deTurckRHSSection g_bg g₀`.

   The exact Lean object of the mission statement is therefore
   **`deTurckRHSSection g_bg g₀ : SmoothCcTensor g₀ 0 2`**
   (`Geometry/Flow/RicciFlow/DeTurckRHSSection.lean:224`), whose fibre value is
   `deTurckRicciRHS g_bg g₀ x (v 0) (v 1)` — Ricci of `g₀` plus the `g_bg`-DeTurck
   Lie-derivative term, *no* Laplacian.  With `g_bg := gBase` only two metrics appear, which
   is exactly why the ratified instantiation matters.

   `nZero_eq_static` packages this: `lowRegN … ⟨0,_⟩ = smoothCcToTensorHs g₀ 1
   (deTurckRHSSection g_bg g₀)`.

2. **Spectral `H¹` → covariant `1`-jets.**  `hsCovsum_smoothCc` (E1×E2, easy direction).
   *Discovery worth keeping*: at spectral order `1` its closed constant evaluates to a bare
   `√2` — `hsCovsumC Fc d 1 = √(2^0 · (modeJetC 0 + modeJetC 1))` and both mode constants are
   the empty Laplacian iterate `iterRawLapC _ _ 0 _ = 1`.  So E6 inherits **no** dependence on
   the curvature-jet family `Fc` or on the dimension through the Gårding side; `hcurv` is
   carried only because `hsCovsum_smoothCc`'s *statement* demands it (`hsCovsumC_one`).

3. **Jets → `L²(g₀)` from a fibre sup bound.**  `smoothCc_norm_le_of_fibreSq`:
   `‖S‖_{L²(g)} ≤ K·√(vol_g M)` from `riemannianFiberNormSq ≤ K²` pointwise.  Route:
   `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq` + `integral_mono_of_nonneg` against the
   constant (only the *upper* function needs integrability, so no continuity of the integrand
   is required) + `IsFiniteMeasure` from `CompactSpace`.

4. **`vol_{g₀} → vol_{gBase}`.**  `volReal_cross_le`: the `ℝ`-valued face of
   `volumeMeasure_cross_le` (`HCGCompactness/UnifCovSumCross.lean:1389`), factor `√(Λ^n)`.

Assembled:

```
nZeroC Ksup Λ volBase n = √2 · (2 · (Ksup · √(√(Λ^n) · volBase)))
```

`staticN_h1_le` proves the `H¹` bound on the static field; `nZero_unif` is the `lowRegN` face;
`nZero_lowregNfun` is the six-number face, literally the `hzero` slot of
`lowreg_partial_sol_of_bounds` at `D := nZeroC …`.

## Parameterized inputs (the honest frontier)

* **`Ksup`** — `∀ j ≤ 1, ∀ x, riemannianFiberNormSq g₀ 0 (2+j) x (∇^j(deTurckRHSSection gBase g₀) x)
  ≤ Ksup²`.  This is the *only* genuinely geometric input and it is Lane-E-adjacent (E3 at
  order `≤ 1`): the fibre norm of the static Ricci–DeTurck field and of its first covariant
  derivative.  Metric jets of order `≤ 3` against `gBase` suffice for it mathematically
  (Riemann = 2 metric derivatives, `∇Riemann` one more, plus the connection-difference terms
  of the DeTurck vector field), comfortably inside E0's `a ≤ 6` budget.  Taken as a hypothesis
  in the shape a Λ-class producer will deliver, exactly as `H2PointwiseUnif.lean` takes `Cpt`.
  **No such bound exists in the tree today** — this is the remaining E6 debt.
* **`hcurv`** — `UnifBochnerGap`'s abstract Weitzenböck-defect hypothesis (E3's other face).
  Structurally required by `hsCovsum_smoothCc`; the constant it yields here is `√2`.
* **`hcore`** — `Continuous (coreN g₀ gBase hδ hreal)`, produced by `lowRegN_outer` alongside
  `Ctop, B0, B1, ρ`.  Not a new frontier: it is the same producer E7 already consumes.
* **`hEq`** — `MetricUniformEquivalentOn Set.univ gBase g₀ Λ`, the class comparability.

## Reuse ledger

Reused directly, not reproved: `hsCovsum_smoothCc` / `hsCovsumC` (E1+E2),
`volumeMeasure_cross_le` (S0 volume brick), `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq`,
`riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace`, `smoothN_wd`, `coreRep_spec`,
`coreSymm_h2`, `norm_smoothCcToTensorHs_symmS_le`, `smoothCcToTensorHs_sub`,
`rawTensorConnLapSmooth_sub`, `ccTensorBilin_zero_weight`, `smoothRiemannianMetric_ext_inner`,
`lowregRealRad` / `lowregStateRad_pos` (E8a).

## Layer notes / deferred relocations

* `smoothCc_norm_le_of_fibreSq` is a rank-generic `L²` fact whose canonical home is
  `Analysis/Integration/L2/SmoothSections/`.  Kept local to avoid invalidating that low-level
  module while other lanes build.
* `hsCovsumC_one`, `smoothCcToTensorHs_zero`, `rawTensorConnLapSmooth_zero` are evaluation
  lemmas whose canonical homes are `UnifBochnerGap.lean`,
  `DeTurck/SobolevNonlinearityExistence.lean` and
  `RawConnLapL2SobolevBounds/RawTensorConnLapIterL2WtwokTwoBound.lean` respectively; same
  reason.

## Lessons

* `omit … in` must precede the docstring, not sit between docstring and `theorem`.
* `tensorHs` / `tensorHs.ext` live in `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation`,
  not in `TensorSpectral`; opening only the latter gives "unknown identifier `tensorHs`".
* `Dense.extend_eq` needs continuity of the *core* function, which `lowreg_partial_sol_of_bounds`
  does not carry (it only carries continuity of the extension) — hence `hcore` as a hypothesis.
* A targeted build of `UnifCovSumCross` failed once with "no such file or directory" on its own
  `.olean` while other agents' builds were running (the known transient olean-eviction /
  thread-exhaustion false-fail); a retry at `-LeanThreads 3` was green.

## Next concrete target

The `Ksup` producer: a Λ-class bound on `riemannianFiberNormSq g₀ 0 (2+j) x
(∇^j(deTurckRHSSection gBase g₀) x)` for `j ≤ 1`, from comparability plus
`MetricCovDerivOrderBoundOn` at orders `≤ 3`.  Order-`0` inputs already exist
(`unifCurvatureSup_singleLink` for `1 ≤ Λ < 2`,
`exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`,
`exists_norm_covGrad_connDiffSection_le_of_jetEnvelope`); the missing pieces are the DeTurck
vector-field term and the `j = 1` covariant derivative, plus the fibre-norm packaging.
