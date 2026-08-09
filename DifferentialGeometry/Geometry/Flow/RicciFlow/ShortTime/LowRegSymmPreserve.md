# LowRegSymmPreserve

Lane C of the `(N)` / `ricci_flow_unif_existence` endgame: the **symmetry
preservation** brick, i.e. the honest producer of the `hsymm` input that
`lowRadial_eq_self_along_sol` (in `LowRegLiftTwo.lean`) consumes.

## What is in this file

L² / eigenbasis layer (the real content):

* `eigenBlock g i` — the eigenvalue block of an eigen-index, a **Finset**
  (`TensorEigenIdx = Σ μ, Fin (finrank (eigenspace μ))`, so the fibre over a
  fixed eigenvalue is finite); `mem_eigenBlock`, `lambda_of_mem_eigenBlock`.
* `symmMat g i j` — the eigenbasis matrix of spectral symmetrization.
* `symmMat_eq_zero` — the matrix vanishes off the block.
* `toL2_symmS_eigen_eq_sum`, `symmS_toL2_coeff` — the finite block expansion of
  smooth slot symmetrization in the eigenbasis.
* `symmHs_coeff` — **the main reusable statement**: `symmHs` is block diagonal,
  `(symmHs u).coeff i = ∑ j ∈ eigenBlock i, symmMat i j * u.coeff j`, for every
  `u : tensorHs g 0 2 σ`, `σ ≥ 0`.
* `isClosed_symmFixed`, `symmHs_smoothCc_eq_self` — two small bridges: the
  spectrally symmetric states are closed (so symmetry survives a continuous
  dense extension), and a slot-symmetric *smooth* tensor embeds to a spectrally
  symmetric state.

Time-`L²` layer:

* `symmTimeL2` (pointwise action of `symmHs` on `L²([0,T]; Hˢ)`),
  `symmTimeL2_coeFn`, `symmTimeL2_eq_self_iff`, `timeModeCoeff_symmTimeL2`.
* `symmHs_homModeCoeff`, `symmHs_solModeCoeff` — commutation per mode.
* `symmHs_homField_comm`, `symmHs_solField_comm`, `symmHs_duhamel_comm` —
  commutation with `maxRegHomogeneousSolField`, `maximalRegularitySolField` and
  `maxRegDuhamelSolField`.
* `duhamel_symm_ae` — the Duhamel field of symmetric data is a.e. spectrally
  symmetric.
* `lowreg_sol_symm` — the same at the zero initial datum used by
  `lowreg_partial_sol`: symmetric forcing ⟹ a.e. symmetric solution field.

All declarations are sorry-free.  A real targeted module build passed
(`build -NoLakeLock +…LowRegSymmPreserve`; the focused `lake env lean` result
alone is not trusted), and `#print axioms` on `symmHs_coeff`,
`symmHs_duhamel_comm`, `lowreg_sol_symm` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Mathematical findings

**The commutation is not abstract — it needs eigenblock preservation.** The
whole maximal-regularity machinery is *diagonal* in the rough-Laplacian
eigenbasis: `homModeCoeff u₀ i` is `t ↦ e^{-λᵢ t} · u₀.coeff i` and
`solModeCoeff f i` is `perModeConvL2 λᵢ (timeModeCoeff f i)`.  A bounded
operator commutes with such a family iff it does not mix different eigenvalues.
`symmHs` is defined by density from `symmS` and carries no coefficient formula,
so the commutation genuinely had to be *proved*, not massaged.

**Where the input came from.**  `SlotSwapEquivariance.lean` already contains the
decisive fact: `tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne` says the
slot swap of an eigensection is orthogonal to every eigenvector with a different
eigenvalue label — that is slot-swap equivariance of the rough connection
Laplacian.  Since `symmS = ½(id + swap)`, the same holds for `symmS`.

**Why finiteness matters.**  `TensorEigenIdx` is `Σ μ, Fin (finrank …)`, so a
block is a `Finset`.  That turns the block expansion into a *finite* sum and
avoids `tsum`/Parseval entirely: the whole route is
`⟪toL2 (symmS eᵢ), toL2 X⟫`, expand `toL2 (symmS eᵢ)` as a finite eigenbasis
combination, pair term by term.  Attempting the same with an infinite spectral
expansion, or by trying to run the density argument through the semigroup
(`e^{tΔ} X` is not in the range of `ccToHsLin`), does not close.

**Route that does not work.** Density in the *source* alone is not enough for
`symmHs ∘ e^{tΔ} = e^{tΔ} ∘ symmHs`: for `u` in the smooth core, `symmHs u`
stays in the core but `e^{tΔ} u` need not, so `symmHs (e^{tΔ} u)` cannot be
evaluated by `symmHs_core`.  The coefficient formula `symmHs_coeff` is what
removes this asymmetry, and it is the piece worth keeping.

## What is still an input (flagged)

`lowreg_sol_symm` consumes `∀ᵐ t, symmHs (f t) = f t` for the forcing `f`.  For
`lowreg_partial_sol` the forcing is `Nfun (field t)` with
`Nfun = lowRegN g₀ g_bg …`, and `lowRegN` is `Dense.extend` of
`coreN x = deTurckSmoothN g₀ g_bg 1 (symmS g₀ (coreRep g₀ x)) …`.  So the
missing statement is the **smooth-tensor** symmetry

```
symmS g₀ (deTurckSmoothRemainder g₀ g_bg (symmS g₀ T)) =
  deTurckSmoothRemainder g₀ g_bg (symmS g₀ T)
```

(`deTurckSmoothRemainder = deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`), after which
`symmHs_smoothCc_eq_self` lifts it to the spectral scale and
`isClosed_symmFixed` propagates it through the dense extension to `lowRegN`.
*Update (2026-07-30, `LowRegRHSSymm.lean`): **both of these are now closed.***

* `symmS_remSymmS` proves exactly the displayed smooth-tensor identity, and
  `symmHs_smoothN` / `symmHs_coreN` / `symmHs_lowRegN` lift it through
  `symmHs_smoothCc_eq_self` and `isClosed_symmFixed` to the dense extension
  `lowRegN`.  `lowreg_force_symm` is the `hf` hypothesis discharged, and
  `lowreg_sol_symm_rhs` is `lowreg_sol_symm` without it.  The route was *not*
  `domDomCongrSection` algebra: it goes through a bilinear-form extensionality
  lemma `ccTensor_ext_bilin` plus `bilin_ddc_swap`.
* The exponent normalization is closed too: `symmHs_congr` (`cases`-and-`rfl`
  naturality against `tensorHsCongr`) and `lowreg_sol_symm_h3` deliver symmetry
  at the literal `(3 : ℝ)` used by the `lowRadial*` layer.

See `LowRegRHSSymm.md`.  The only remaining hypotheses on that side are the two
continuity facts and the forcing identification that `lowreg_partial_sol`
already exports.

## Lean lessons

* `TensorEigenIdx` is **ambiguous** when both
  `Analysis.Parabolic.TensorSpectral` and
  `Analysis.Parabolic.TensorHeatEquation` are open.  Write the full
  `Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx …`, as
  `SlotSwapEquivariance.lean` does.
* A block `Finset` over a sigma type is cleanest as
  `Finset.map ⟨Sigma.mk i.1, sigma_mk_injective⟩ Finset.univ`: this needs no
  `DecidableEq` and lets every statement quantify over plain `TensorEigenIdx`
  instead of the dependent `Fin (finrank …)` fibre.
* An `if _ ∈ Finset then` in a *statement* needs `open scoped Classical in`
  before the declaration; a `classical` inside the proof is too late.
* `Filter.eventually_all_finset` takes the `Finset` **explicitly** (and its
  binder is literally named `I`, which collides with the model-with-corners
  variable): use `(Filter.eventually_all_finset _).2`.
* `omit [C] in` must come *before* the docstring, not between docstring and
  `theorem`.
* `MeasureTheory.Lp` has no `coeFn_sum`; a five-line `Finset.induction_on`
  helper (`coeFn_smul_sum`) built from `Lp.coeFn_add` / `Lp.coeFn_smul` covers
  every use here.
* `perModeConvL2 lam hlam hT` carries `hlam : 0 ≤ lam`; transporting `lam`
  along an equality is `subst h; rfl` (proof irrelevance), packaged as
  `perModeConv_congr`.
* Seven small helpers of `SlotSwapEquivariance.lean` are `private`
  (`tensorL2_ext_of_coeff_eq`, `eigenbasis_eq_toL2_eigenSmooth`,
  `inner_toL2_domDomCongrSection_swap`, `toL2_symmS_eq`,
  `tensorL2Coeff_toL2_domDomCongrSection_swap`,
  `tensorL2Coeff_sum_smul_eigenbasis`, `eq_sum_of_tensorL2Coeff_support`).
  They are reproved locally here (~55 lines).  De-privatizing them upstream
  would be the right cleanup, but it forces a rebuild of the whole DeTurck
  low-base chain and was judged too disruptive mid-session.

## Progress

* `ricci_flow_unif_existence` / `(N)`: still **unstated in Lean, 0 %**.  Nothing
  here changes that.
* The symmetry brick itself: the analytic half — that spectral symmetrization
  commutes with the heat semigroup and with the whole Duhamel solution map — is
  **done and axiom-clean**.  What remained (nonlinearity-side symmetry,
  dense-extension and exponent-transport wiring) was closed the same day in
  `LowRegRHSSymm.lean`; the brick is now ≈ 95 %.
* Lane C brick C0 (`lowRadial_eq_self_along_sol`): its `hsymm` input is no
  longer a frontier — `lowreg_sol_symm_h3` has exactly its shape.
* `(N)` dedicated machinery overall: this file moved it from roughly 72 % to
  roughly 73 %; `LowRegRHSSymm.lean` moved it to roughly 75 %.  The endpoint
  theorem stays at 0 %.
