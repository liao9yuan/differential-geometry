# EigenProjTameSol

## 2026-08-04 — created: the tame form of the Galerkin identification layer

### Why the file exists

`EigenProjPartialSol.lean` (session-1 work) identifies the Galerkin limit for
`partial_sol_const`, whose nonlinearity must be **globally Lipschitz** on the
state ball.  The `(N)` campaign's order-one solve is `partial_sol_tame`
(`LowRegDenseSolve.lean:461`, `UnifClassBounds.lean:368` — both call sites
verified by grep before any code was written), and `lowregNfun` is provably not
Lipschitz there: `lowerState g₀ a R = {x | ‖J x‖ ≤ R}` bounds only the
`H^{a+1}` norm, whereas the third arm `B1·(‖u‖+‖v‖)·‖J(u−v)‖` of the DeTurck
tame estimate carries the ambient `H^{a+2}` norm.  So `projFix_le_two` could
never be instantiated at the campaign data, and the whole session-1 layer was
unreachable.  This file is its tame twin.

### What is in it (all axiom-clean)

* `projN_cont` — `Π_N ∘ Nfun` is continuous.
* `projN_tame` — `Π_N ∘ Nfun` obeys the **same** three-arm estimate with the
  **same** `A, B, C`.  The whole content is `‖Π_N x‖ ≤ ‖x‖`
  (`norm_spatialEigenProj_apply_le`), applied after `map_sub`.
* `proj_partial_sol_tame` — the projected tame solve, on the identical
  closed-form horizon `T₀ = min 1 (min (1/(64(B+1)²)) (((R/4)/(2(D+1)))²))`,
  same forcing ball `R/4`, every constant free of `N`.  One-liner from
  `partial_sol_tame` at `projNfun` (reusing `projN_zero` from the const file —
  it carries no Lipschitz hypothesis).
* `projN_nemytskiiTame` — truncating before or after the tame Nemytskii
  operator agrees.
* `lamHalfTame` (private) — `Λ ≤ 1/2` from `A·R ≤ 1/16`, `C·R ≤ 1/16`,
  `T ≤ 1/(64(B+1)²)`, at `ρ = R/4`.  Copied arm-by-arm from
  `partial_sol_tame`'s internal bound (`1/8 + 1/4 + 1/8`).
* `projFixTame_dist_le`, `projFixTame_le_two` — the stability bound
  `‖f_N − f_*‖ ≤ (1 − Λ)⁻¹‖Π_N f_* − f_*‖` and its `K = 2` form.

### What was REUSED unchanged, not re-proved

`projFix_tendsto`, `projField_tendsto`, `projForce_fixed` and `projField_fixed`
in `EigenProjPartialSol.lean` carry **no** Lipschitz hypothesis (checked
declaration by declaration), so the tame lane uses them verbatim.  Likewise
`projNfun` and `projN_zero`.  Only the five genuinely estimate-bearing lemmas
needed tame twins.

### Lean lessons

* `gcongr` discharges the `harm3` side goals by itself here (`hR : 0 ≤ R` and
  the `Real.sqrt (1+T) ≤ 2` / `1+T ≤ 2` facts are in context); adding
  `· positivity` bullets after it is a "No goals to be solved" error.
* `positivity` will not close
  `0 ≤ 2·C·(R/4)·√(1+T)·(1+T)` (it cannot see `hR`, `hT`); use explicit
  `mul_nonneg` chains.  `nlinarith [hT.le]` also fails on that product.
* Mirror `EigenProjPartialSol.lean`'s opens exactly, including
  `open … TensorSpectral hiding TensorEigenIdx` (the standing `TensorEigenIdx`
  ambiguity trap).

### Build caveat (not caused here)

A bare `lake build` does not finish in this checkout: its default target pulls in
`DeclIndex`, which globs `TensorMaximalRegularity/TimeTameFixedPoint.lean`, a
pre-existing broken leaf of the forward-uniqueness lane (no `.olean`, last
edited 2026-07-25, explicitly excluded from the root aggregate per
`ShortTime/FORWARD_UNIQUE_PLAN.md`).  Verify with `+DifferentialGeometry` plus
targeted modules instead.

### Honest accounting

This file is *machinery*, not an endpoint.  It makes the Galerkin
identification available at the campaign's own solver; the analytic frontier
(`lowreg_loMass`) is untouched by it.  See
`ShortTime/LowRegGalerkinIdent.md` for the instantiation and
`ShortTime/LowRegAllOrderJet.md` for what is still missing.
