# UnifNZeroBound.lean — brick E6 (the `D`-number of the six-number horizon)

Status: **LANDED; curvature-free order-one revision verified GREEN**.
Focused and exact verification passed.  Direct axiom audits of
`staticN_h1_le`, `nZero_unif`, and `nZero_lowregNfun` report only
`propext`, `Classical.choice`, and `Quot.sound`; the source has no `sorry`,
`admit`, or new axiom declaration.

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

2. **Spectral `H¹` → covariant `1`-jets, without curvature.**  The private
   `hsOne_sq` specializes the public coefficient identities `rawIter_tsum` and
   `covIter_tsum` at the empty rough-Laplacian iterate and proves the exact
   identity

   ```
   ‖S‖_{H¹(g₀)}² = ‖S‖_{L²(g₀)}² + ‖∇S‖_{L²(g₀)}².
   ```

   Hence `‖S‖_{H¹} ≤ ‖S‖ + ‖∇S‖`, which is harmlessly enlarged by the old
   factor `√2` so `nZeroC` does not change.  The former `Fc/hFc/hcurv`
   parameters were artifacts of invoking the arbitrary-order Bochner wrapper;
   they are now absent from `staticN_h1_le`, `nZero_unif`, and
   `nZero_lowregNfun`.

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

* **`Ksup`** — `∀ j ≤ 1, ∀ x, riemannianFiberNormSq g₀ 0 (2+j) x
  (∇^j(deTurckRHSSection gBase g₀) x) ≤ Ksup²`.  The geometric estimate is
  proved in `UnifDeTurckRHSOne.unifKsupLow`, but its current public quantifier
  order is only `∀ g₀, ∃ K`.  A uniform horizon needs `∃ Kstar, ∀ g₀`.
  Therefore the remaining E6 debt is not another curvature estimate: it is the
  explicit-constant extraction and quantifier correction of that producer.
  The current producer also assumes `Λ < 2`; this is only the staged
  sub-two class, not the final endpoint for arbitrary `Λ ≥ 1`.
* **`hcore`** — `Continuous (coreN g₀ gBase hδ hreal)`, produced by `lowRegN_outer` alongside
  `Ctop, B0, B1, ρ`.  Not a new frontier: it is the same producer E7 already consumes.
* **`hEq`** — `MetricUniformEquivalentOn Set.univ gBase g₀ Λ`, the class comparability.

## Reuse ledger

Reused directly, not reproved: `rawIter_tsum`, `covIter_tsum`,
`ccToHs_norm_sq`, `norm_ccHs_eq_smoothHs`,
`volumeMeasure_cross_le` (S0 volume brick), `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq`,
`riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace`, `smoothN_wd`, `coreRep_spec`,
`coreSymm_h2`, `norm_smoothCcToTensorHs_symmS_le`, `smoothCcToTensorHs_sub`,
`rawTensorConnLapSmooth_sub`, `ccTensorBilin_zero_weight`, `smoothRiemannianMetric_ext_inner`,
`lowregRealRad` / `lowregStateRad_pos` (E8a).

## Layer notes / deferred relocations

* `smoothCc_norm_le_of_fibreSq` is a rank-generic `L²` fact whose canonical home is
  `Analysis/Integration/L2/SmoothSections/`.  Kept local to avoid invalidating that low-level
  module while other lanes build.
* `hsOne_sq` is kept private because the rank-generic public spectral
  coefficient identities already provide its reusable algebra, while importing
  the existing high-level odd-ladder wrapper here pulled a 46k-line DeTurck
  module into the exact refresh path.
* `smoothCcToTensorHs_zero` and `rawTensorConnLapSmooth_zero` are evaluation
  lemmas whose canonical homes are `DeTurck/SobolevNonlinearityExistence.lean`
  and `RawConnLapL2SobolevBounds/RawTensorConnLapIterL2WtwokTwoBound.lean`
  respectively; they remain local for the same surgical-change reason.

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

Prove `unifKsupLeOne` with `∃ Kstar` before `∀ g₀` for arbitrary `Λ ≥ 1`.
Keeping `Λ < 2` and only reordering the witness requires two API extractions:
the dimension bound `rfns_idEndo_le` and the explicit constants behind
`iterCovG1_three`.  That staged result is not the final theorem.

Removing `Λ < 2` requires a finite-order, nonperturbative assembly from the
existing `A₀/A₁/A₂` connection-difference estimates.  First extract the
arbitrary-`Λ` `A₀` estimate as `connDiff_gJet_le`; then combine it with
`covDerivConnDiff_gJet_le`, `covDConnDiff2_gJet_le`,
`riemannSec_difference`, and `unifCurvatureSup_singleLink_of_diff`.
This avoids the perturbative coefficient grid and the currently incomplete
convex-subdivision route.  Only after `unifKsupLeOne` may a high-level sibling
state the common `Dstar` before the class member `g₀`.
