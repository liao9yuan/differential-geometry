# EigenProjDuhamel.lean — adapter A: the spectral truncation commutes with the Duhamel family

`PSTOP_PROPOSITION.md` §10 adapter A (planner No. 128/129), the only
load-bearing adapter of the re-scoped Galerkin lane.  Status: **complete,
sorry-free, axiom-clean.**

## What is proved

Everything is modewise; nothing here is an estimate.  Write `Π_N^σ` for
`spatialEigenProj g σ N` and `Π_N^{σ,T}` for its pointwise action
`timeL2EigenProj g σ T N` on `L²([0,T]; H^σ)`.

* `spatialProj_coeff` — `(Π_N^σ W).coeff i = if i ∈ eigenIdxFinset g N then W.coeff i else 0`.
* `spatialProj_lip` — `LipschitzWith 1 (Π_N^σ)` (the form adapter B needs;
  the norm bound `norm_spatialEigenProj_le_one` already existed).
* `timeProj_modeCoeff` — the same indicator formula for `timeModeCoeff` of a
  truncated time-`L²` field.
* `proj_solModeCoeff`, `proj_derivModeCoeff`, `proj_homModeCoeff` — the three
  per-mode Duhamel coordinates of truncated data (`solModeCoeff`,
  `derivModeCoeff`, `homModeCoeff`) are the truncations of the coordinates.
* `proj_solField_comm` —
  `maximalRegularitySolField a hT (Π_N^a f) = Π_N^{a+2} (maximalRegularitySolField a hT f)`.
  Note the exponent bookkeeping: the truncation on the right acts at the gained
  regularity `a+2`.
* `proj_derivField_comm` — same for `maximalRegularityDerivField` (exponent `a`
  on both sides).
* `proj_homField_comm` — same for `maxRegHomogeneousSolField`, with the initial
  datum truncated at `a+2`.
* `proj_duhamel_comm` —
  `maxRegDuhamelSolField a hT hT1 (Π_N^{a+2} u₀) (Π_N^a f) = Π_N^{a+2} (maxRegDuhamelSolField a hT hT1 u₀ f)`
  (one `map_add` over the two arms).
* `projDuhamel_zero` — the `u₀ = 0` specialization, i.e. the form the forcing
  fixed point (`partial_sol_const`, zero seed) actually consumes.
* `proj_maxRegOp_deriv` — the map level: `timeH1.timeDeriv` of
  `maximalRegularityOp` commutes with the truncation.  There is no projector on
  `timeH1`; the trace is `0` for either forcing (`maximalRegularityOp_trace0`),
  so the derivative statement is the whole content and no new object was
  introduced.
* `projSol_mode_zero` — **the `V_N`-valuedness corollary the energy identity
  needs**: for `i ∉ eigenIdxFinset g N`,
  `timeModeCoeff (maximalRegularitySolField a hT (Π_N^a f)) i = 0`.
* `projSol_fixed` — its operator form:
  `Π_N^{a+2} (maximalRegularitySolField a hT (Π_N^a f)) = maximalRegularitySolField a hT (Π_N^a f)`.

## Route

The solve is mode-diagonal (`solModeCoeff hT f i = perModeConvL2 λᵢ … (timeModeCoeff f i)`,
a function of the mode `i` alone) and the truncation is diagonal, so the
commutation is `timeModeCoeff_injective` plus one `if`-split per lemma.  The
template is `ShortTime/LowRegSymmPreserve.lean`
(`symmHs_solField_comm` / `symmHs_duhamel_comm`), which does exactly this for
the block-diagonal spectral symmetrizer; the projector case is strictly easier
(diagonal, not block-diagonal, so no `eigenBlock` sums).

Reused, not reproved: `maximalRegularitySolField_timeModeCoeff`,
`maximalRegularityDerivField_timeModeCoeff`,
`maxRegHomogeneousSolField_timeModeCoeff`, `timeModeCoeff_injective`,
`timeModeCoeff_coeFn`, `ContinuousLinearMap.coeFn_compLpL`,
`finiteEigenComboHs_coeff`, `norm_spatialEigenProj_apply_le`.

## Lean lessons (cost me three iterations)

* **`TensorEigenIdx` is ambiguous** if both
  `Analysis.Parabolic.TensorSpectral` and
  `Analysis.Parabolic.TensorHeatEquation` are opened — they each declare one.
  The Duhamel API uses the `TensorHeatEquation` one.  `LowRegSymmPreserve.lean`
  solves this by fully qualifying every occurrence; the cheaper fix used here is
  `open …TensorSpectral hiding TensorEigenIdx` (TensorSpectral is still needed
  for `tensorResolventL2`).
* **`if i ∈ (F : Finset (TensorEigenIdx …))` has no `Decidable` instance.**  The
  eigen-index type carries no `DecidableEq`.  Statements containing that `if`
  need `open scoped Classical in` **before the docstring** (`open … in` between
  the docstring and the `theorem` is a parse error).  This is the same idiom as
  `Garding/EigenCombination.lean`.
* Inside this namespace (`…PDE.RicciFlow.IntrinsicSpectral`) write
  `timeH1.timeDeriv` and `coeFn_ofContinuousOn`, **not**
  `TimeSobolev.timeH1.timeDeriv`: the `TimeSobolev.` prefix only resolves from
  inside `DifferentialGeometry.Analysis.Parabolic.*`.
* Truncate the check output at your peril: `Select-Object -Last 60` hid five of
  eight errors and produced two rounds of misdiagnosis.  Filter on
  `Select-String "error|warning"` instead.

## Home / layering

`spatialProj_coeff` and `spatialProj_lip` are about `spatialEigenProj` and their
canonical home is beside the definition in `TimeL2EigenProjection.lean`.  They
are deliberately kept here instead: that module has a live downstream chain
(`GalerkinForcingTimeL2Limit` → `GalerkinLimitUniformMass` →
`ForcingCoordinateTimeRegularity`, `ShortTime/LowRegAllOrderJet`), and
`LowRegAllOrderJet.lean` is in flight in another lane.  Moving them later is a
pure cut-and-paste plus that rebuild; neither is tagged `@[simp]`, so no
downstream simp set changes either way.

## Verification

Focused check clean (no warnings); targeted module build green; axiom census of
all 14 declarations: `propext, Classical.choice, Quot.sound` only.  No
`maxHeartbeats`, no `sorry`.

## What adapter C took from here — DONE (2026-08-04)

`projDuhamel_zero` + `projSol_fixed` were the two solver-side facts.  The
remaining step for "the projected trajectory is `V_N`-valued" at the *fixed
point* has since been closed: `spatialProj_idem` was added here (idempotence of
the truncation, three lines from `spatialProj_coeff` plus `tensorHs.ext`), and
`EigenProjPartialSol.lean`'s `projForce_fixed` / `projField_fixed` turn the a.e.
identity `gforce =ᵐ Π_N(Nfun …)` into `Π_N gforce = gforce` and then, via
`projDuhamel_zero`, into `Π_N field = field` at `H^{a+2}`.

`spatialProj_idem` sits with the rest of the `spatialProj_*` family, i.e. in the
same parked position as `spatialProj_coeff` / `spatialProj_lip`: canonical home
is beside `spatialEigenProj` in `TimeL2EigenProjection.lean`, deferred only
because that file has a live downstream chain in another lane.  Move all three
together when that chain is quiet.  None is `@[simp]`.
