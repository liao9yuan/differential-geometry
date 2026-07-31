# LowRegRHSSymm

Lane C of the `(N)` / `ricci_flow_unif_existence` endgame: the **forcing-side**
half of the symmetry brick.  `LowRegSymmPreserve.lean` proved the solver half
(spectral symmetrization commutes with the whole Duhamel machinery) and left
one explicit input open — that the smooth Ricci–DeTurck remainder of a
symmetrized tensor is itself slot-symmetric.  This file closes it and wires the
result all the way to `lowRadial_eq_self_along_sol`'s `hsymm`.

## What is in this file

Rank-two slot-swap dictionary (reusable):

* `ccTensor_ext_bilin` — a `SmoothCcTensor g 0 2` is determined by its extracted
  bilinear form `ccTensorBilin`.  This is the extensionality lemma the whole
  file runs on: `smoothCcTensor_ext_of_unitModel` composed with
  `unitModel_eq_ccTensorBilin_local`.
* `bilin_ddc_swap` — the slot swap transposes that form.
* `ddc_swap_swap`, `ddc_swap_sub` — involution and subtractivity of the swap,
  both proved by the bilinear extensionality above.
* `symmS_of_swap`, `swap_symmS`, `symmS_idem`, `swap_of_symmS` — `symmS` is the
  slot-swap fixed-point projection; `bilin_symm_of_symmS` reads a `symmS`-fixed
  tensor back as a symmetric bilinear form.

The mathematics:

* `swap_deTurckRHSArm` — **the Ricci–DeTurck arm is slot-symmetric for every
  fibre-small `T`** (no symmetry hypothesis on `T`).
* `swap_smoothRem` / `symmS_smoothRem` — the smooth remainder
  `deTurckSmoothRemainder g₀ g_bg T = arm − Δ_∇ T` of a slot-symmetric `T` is
  slot-symmetric.
* `symmS_remSymmS` — the exact shape the nonlinearity uses (argument already
  symmetrized, so *no* hypothesis survives).
* `bilin_smoothRem_symm` — the bilinear-form restatement.

Spectral lift and endpoints:

* `smoothN_eq_embed`, `symmHs_smoothN` — the smooth nonlinearity is the spectral
  embedding of the remainder, hence a fixed point of `symmHs`.
* `symmHs_coreN`, `symmHs_lowRegN` — the same for `coreN` and for its dense
  extension `lowRegN` (density + `isClosed_symmFixed` + the two continuity facts
  that `lowreg_partial_sol` already exports).
* `lowreg_force_symm` — the `hf` hypothesis of `lowreg_sol_symm`, discharged.
* `lowreg_sol_symm_rhs` — `lowreg_sol_symm` with that hypothesis gone.
* `symmHs_congr`, `lowreg_sol_symm_h3` — the same at the literal exponent
  `(3 : ℝ)`, i.e. literally the `hsymm` input of `lowRadial_eq_self_along_sol`.

All declarations are sorry-free.  A real targeted module build passed
(`build -NoLakeLock +…LowRegRHSSymm`; the focused `lake env lean` result alone
is not trusted), and `#print axioms` on `ccTensor_ext_bilin`,
`swap_deTurckRHSArm`, `symmS_smoothRem`, `symmS_remSymmS`, `symmHs_lowRegN`,
`lowreg_sol_symm_rhs`, `lowreg_sol_symm_h3` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Mathematical findings

**The two summands are symmetric for completely different reasons.**  The
remainder is `deTurckRHSArmG0 g₀ g_bg T − rawTensorConnLapSmooth g₀ 0 2 T`.

* The arm is `deTurckRHSSection g_bg (g₀ + T)` re-tagged to `g₀`; its unit-model
  value is the *bilinear form* `deTurckRicciRHS g_bg (g₀ + T)`, symmetric
  because `Ric` is (`ricciTensor_symm`) and `𝓛_W g` is
  (`lieDerivMetric_isPointwiseSymm`).  This holds for **every** `T`, symmetric
  or not — the symmetry of the arm never sees `T`.
* The Laplacian term is symmetric only because `T` is: the mechanism is slot-swap
  *equivariance*, `rawTensorConnLapSmooth_domDomCongrSection`, already available
  in `SlotSwapEquivariance.lean` (it is the same lemma that powers the eigenblock
  argument of `LowRegSymmPreserve.lean`).

So the whole content is the bilinear-form ⟹ tensor bridge on the arm; there is
no new geometry.

**The bridge that makes it short: bilinear extensionality.**  Rather than doing
`unitModel`/`domDomCongr` algebra by hand, prove once that a `(0,2)`-tensor is
determined by `ccTensorBilin` (`ccTensor_ext_bilin`) and that the swap transposes
it (`bilin_ddc_swap`).  Every subsequent slot-swap identity — involution,
subtractivity, `swap_symmS`, the arm symmetry — is then a two-line bilinear
computation.  The first attempt went through `unitModel` additivity/homogeneity
instead and stalled (see the Lean lessons); the bilinear route is strictly
shorter and needs no extra bundle instances.

## Lean lessons

* **`ContMDiffSection.coe_add` / `coe_smul` do not elaborate here.**  Copying the
  upstream `unitModel_add` / `unitModel_smul` private proofs into this file fails
  with `failed to synthesize FiberBundle (TensorRSModel 0 s ℝ E) …`: those proofs
  work only in files that have the tensor-bundle `letI` instances in scope
  (`Tensor0SBundle.tensor0SBundle_topology`, `TangentBundle.contMDiffVectorBundle`).
  Do not port them; route rank-two slot algebra through `ccTensorBilin` instead.
* **`open …Analysis.Parabolic.TensorHeatEquation` is not optional.**  Without it,
  `tensorHs` still *resolves* but `tensorHs (I := I) (M := M)` fails with
  “Invalid argument name `I` for function”, and `tensorHs.ext` is an unknown
  identifier.  Opening it fixed four otherwise inexplicable errors at once.
  Opening it together with `…TensorSpectral` is safe as long as `TensorEigenIdx`
  is not used unqualified.
* `ContinuousMultilinearMap.domDomCongr_apply` produces `f (v ∘ σ)` in Mathlib,
  but after `rw` the goal displays `fun i => v (σ i)`; instantiate the helper
  lemma at `fun i => v (σ i)`, not at `v ∘ σ`, or `rw` will not match.
* `deTurckSmoothRemainder = deTurckRHSArmG0 − rawTensorConnLapSmooth` is `rfl`
  (the upstream `deTurckSmoothRemainder_eq_arm_sub_connLap` is private; restating
  it locally as `rfl` costs one line).
* Naturality of `tensorHsCongr` against `symmHs` is `cases hab; rfl`: destructing
  the exponent equality turns the transport into the identity and the two
  `0 ≤ ·` proofs are definitionally irrelevant.
* `show` that changes the goal now triggers `linter.style.show`; use `change`.

## What is still an input (flagged)

`symmHs_lowRegN` and everything above it consume
`Continuous (lowRegN …)` and `Continuous (coreN …)`.  These are **not** new
frontiers: `lowreg_partial_sol` (`LowRegDenseSolve.lean`) exports both in its
existential package, so a consumer that already holds a `lowreg_partial_sol`
witness discharges them by destructuring.  They are carried as hypotheses here
only to avoid importing the dimension-three existence assembly.

`lowreg_sol_symm_h3` additionally takes the identification of the forcing with
`lowRegN` along a state path (`hforce`), which is again literally one of the
conjuncts `lowreg_partial_sol` produces, and the exponent equality
`((1 : ℕ) : ℝ) + 2 = 3` (`by norm_num`).

Nothing about the *symmetry* of the Ricci–DeTurck forcing is assumed any more.

## Canonical-home note

`symmHs_congr` is a general `symmHs`-vs-`tensorHsCongr` naturality shim and does
not belong to the DeTurck remainder story; it lives here only because this is
currently the lowest module importing both `SobolevScale/ExponentCongr.lean` and
the `symmHs` layer (`DeTurckRemainderLowBaseTime.lean`).  If more
exponent-transport lemmas for `symmHs` appear, move it to a dedicated module
beside `ExponentCongr.lean` and leave a compatibility alias.

## Progress

* `ricci_flow_unif_existence` / `(N)`: still **unstated in Lean, 0 %**.  Nothing
  here changes that.
* The symmetry brick (Lane C): the solver half was done in
  `LowRegSymmPreserve.lean`; the forcing half is done here, and the exponent
  transport to the `lowRadial*` layer is done too.  The brick is now
  **complete as a conditional statement** — call it ≈ 95 %, the missing 5 %
  being the mechanical destructuring of a `lowreg_partial_sol` witness to feed
  `hcont`/`hcore`/`hforce` at the call site.
* Lane C brick C0 (`lowRadial_eq_self_along_sol`): its `hsymm` input is no
  longer a frontier at all — `lowreg_sol_symm_h3` has exactly its shape.
* `(N)` dedicated machinery overall: this moves it from roughly 73 % to
  roughly 75 %.  The endpoint theorem stays at 0 %.
