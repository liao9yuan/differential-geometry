# H2PointwiseUnif.lean — bricks E2 + E5 of the (N) endgame Lane E

Status 2026-07-30: **landed, sorry-free, axiom-clean** (only `propext`,
`Classical.choice`, `Quot.sound`).  Verification: focused check green, targeted module
build green, `#print axioms` clean on every public declaration.

## What this file is for

Lane E's goal is a `Λ`-uniform horizon floor `τ0(gBase, Λ) > 0` for the low-regularity
Ricci–DeTurck solve.  `UnifClassBounds.lean` (brick E8a) reduced that to six numbers, one of
which is the metric-realization radius `P`.  Per metric `P` came from `realize_at_thr`
(`ShortTime/LowRegDenseSolve.lean`), whose radius is `θ(n)/C` with `C` the
`Classical.choose` witness of `hs2_op_bound` — so as it stood `P` was a source of
`g₀`-dependence and could not floor anything.

This file makes `P` a closed number.

## Contents

### Brick E2 — the rank-`(0,2)` `smoothCcToTensorHs` face

* `ccHs_eq_smoothHs` / `norm_ccHs_eq_smoothHs`: `ccTensorToHs g₀ 2 σ T = smoothCcToTensorHs
  g₀ σ T`.  Both embeddings are *defined* by the same eigenbasis coordinates, so the proof is
  `tensorHs.ext (funext fun _ => rfl)`.
* `hsCovsum_smoothCc`, `covsumHs_smoothCc`: E1's constant-exposed endpoints
  `hsCovsum_unif_const` / `covsum_hs_unif_const` (`SobolevScale/UnifBochnerGap.lean`)
  restated at rank `(0,2)` in the currency the DeTurck stack speaks.  Same closed constants
  `hsCovsumC Fc d n` / `covsumHsC Fc d n`; the proof is `rw [← norm_ccHs_eq_smoothHs]`.

### Brick E5 — the class-uniform `H²` → fibre-operator bound

Closed constants (functions of `(Cpt, Fc, d)` only — no metric, no `∃`, no `Classical.choose`):

```
hs2FibreC Cpt Fc d = Cpt * covsumHsC Fc d 2
hs2OpC    Cpt Fc d = hs2FibreC Cpt Fc d + 1          -- the `+1` mirrors hs2_op_bound's `C0+1`
unifRealizeRad Cpt Fc d = deTurckArmContractionThreshold'' d / hs2OpC Cpt Fc d
```

* `hs2_fiber_sq_unif` — sibling of `hs2_fiber_sq`, constant `hs2FibreC`, rank-generic in `s`.
* `gFibreOp_of_fiberSq` — the reusable half of `hs2_op_bound`: a uniform pointwise fibre
  bound `|T|_g(x) ≤ K` gives `gFibreOpBound g (ccTensorBilinSymm g T) K`.  Extracted rather
  than copied, so the per-metric and class-uniform routes share the Cauchy–Schwarz +
  symmetrization algebra.
* `hs2_op_bound_unif` / `hs2_op_smoothCc_unif` — the E5 endpoint in both currencies.
* `unifRealizeRad_pos`, `realize_at_unif` — the class-uniform sibling of `realize_at_thr`.
  `realize_at_unif`'s conclusion is *verbatim* the `hreal` hypothesis of
  `lowreg_partial_sol_of_bounds` at `P := unifRealizeRad Cpt Fc (finrank ℝ E)` and
  `δ := deTurckArmContractionThreshold'' (finrank ℝ E)`; `unifRealizeRad_pos` is its `hP`.

## Parameterized input (honest)

The **fibre-Morrey constant `Cpt` is a hypothesis, not a producer**: brick E4
(`fibreMorrey_unif`, a `Λ`-uniform sibling of
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`,
`Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`) has NOT landed — there is no
`UnifSharpC0JetSum.lean` in the tree.  `hmorrey` is therefore stated verbatim in that
theorem's shape (`Cpt^2 * ∑_{j < finrank/2 + 2} ‖∇^j T‖²`, NOT pre-specialized to
`range 3`), so E4's producer drops in with no restatement.  Until E4 lands, `unifRealizeRad`
is uniform *given* a class-uniform `Cpt`.

The curvature input `hcurv` is E1's abstract Weitzenböck-defect hypothesis, discharged by
brick E3 (open, the hard geometric brick).

## Lessons / route notes

* The `smoothCcToTensorHs` ↔ `ccTensorToHs` identification is `rfl`-level and there are now
  FOUR copies in the tree: `smoothHs_eq_ccHs` (private, `ShortTime/LowRegCoreTame.lean:42`),
  an inline `htwo` in `realize_at_thr` (`ShortTime/LowRegDenseSolve.lean:58`), an inline
  `heq` in `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs`
  (`SobolevScale/IteratedCovGradHsJetBound.lean:1029`), and the public `ccHs_eq_smoothHs`
  here.  The canonical home is `IteratedCovGradHsJetBound.lean` — it defines `ccTensorToHs`
  AND already imports `DeTurckRemainderDefs`, so both sides are in scope there.  Deliberately
  NOT moved: that file sits under most of the DeTurck/ShortTime tree and editing it would
  invalidate other lanes' `.olean`s mid-session.  Deferred cleanup.
* `H2Pointwise` does not carry `[BoundarylessManifold I M]`, `UnifBochnerGap` does; this file
  carries it (E1's endpoints need it), so `gFibreOp_of_fiberSq` — which does not — needs an
  explicit `omit [BoundarylessManifold I M] in`, stacked ABOVE the
  `attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup … in` that the fibre
  norm manipulation requires.  Stacking the two `… in` combinators works.
* `hs2_fiber_sq_unif` needs no sign hypothesis on `Cpt` (only `Cpt^2` appears); the
  `unusedVariables` linter caught the gratuitous `hCpt` and it was dropped.
* No layer inversion: this file lives beside `H2Pointwise.lean` and imports only
  `Estimates/H2Pointwise` and `SobolevScale/UnifBochnerGap`.  `smoothCcToTensorHs`,
  `gFibreOpBound`, `ccTensorBilinSymm` and `deTurckArmContractionThreshold''` are already in
  scope transitively (`IteratedCovGradHsJetBound` imports `DeTurckRemainderDefs`), so no
  DeTurck-side import was needed.
* The root aggregator `DifferentialGeometry.lean` is stale for lane work (neither
  `UnifBochnerGap` nor any recent Lane-E/Lane-B leaf is listed); new leaves were not added to
  it.  Verification is by targeted module build.

## Next

E5 is done modulo E4.  The remaining `g₀`-dependence of the horizon is entirely in the five
numbers `Ctop, B0, B1, D, ρ` (bricks E6/E7) plus the two inputs `Cpt` (E4) and `Fc` (E3).
Consumer side: `ShortTime/UnifRealizeRadius.lean`.
