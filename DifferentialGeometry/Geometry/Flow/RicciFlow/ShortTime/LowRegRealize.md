# LowRegRealize

## 2026-07-27

Source implementation contains no `sorry`, `admit`, axiom, or replacement
hypothesis; focused verification passed after the namespace migration.

`lowreg_realize_h2` is the direct lower-order realization bridge: an `H2`
spectral tensor whose realized smooth perturbation has the required
pointwise operator bound produces a smooth metric.  `lowreg_realize` retains
the corresponding `H3` entry point.

The new `H2` form is the relevant one for a maximal-regularity solution,
because the state ball is controlled pointwise in time only in the lower
norm.  This file does not yet supply the concrete tame nonlinearity or the
uniform-family lifetime, so `ricci_flow_unif_existence` remains 0%.

## J0a (2026-08-04): `realize_at_delta` — one realization lemma, three instances

**Status: DONE, sorry-free.**  The `H²` metric-realization proof existed THREE
times, each pinning the fibre bound at `deTurckArmContractionThreshold''`:
`lowreg_realize_h2` (here), `lowreg_realize` (here), `realize_at_thr`
(`LowRegDenseSolve.lean`).  All three are now instances of

```
realize_at_delta (hDim : finrank ℝ E = 3) (g) {δ} (hδ : 0 < δ) :
  ∃ R, 0 < R ∧ ∀ T, ‖smoothCcToTensorHs g (((1:ℕ):ℝ)+1) T‖ ≤ R →
    gFibreOpBound g (ccTensorBilinSymm g T) δ
```

with witness `R := δ / C` from `hs2_op_bound`.  Keeping `δ` a parameter is the
POINT: it lets a caller choose the fibre threshold AFTER the ladders' contraction
constants are fixed, which is what the absorption `κ·δ/(1−δ)² < 1` will need
(J0b).  The radius shrinks with `δ`, and in `lowreg_solve_two` the realization
radius enters `P` only as one more `min` component, so a smaller radius is
absorbed with no structural change.

**PLACEMENT CORRECTION to `POSTTAME_J0J5_PLAN.md` §A.6.1.**  The plan put
`realize_at_delta` in `LowRegDenseSolve.lean` "next to `realize_at_thr`" while
also asking that all three copies fold onto it.  Those are incompatible:
`LowRegDenseSolve.lean` IMPORTS `LowRegRealize.lean`, so a lemma in the former
cannot serve the latter's two copies.  It lives here, in the lowest file that has
`hs2_op_bound` — the canonical home, and the only placement that folds all three.

`lowreg_realize` (the `H³` reading) folds through `ccToHs_norm_mono` plus the two
`ext i; rfl` bridges between `ccTensorToHs` and `smoothCcToTensorHs`.  Both
`lowreg_realize_h2` and `lowreg_realize` have ZERO consumers in the tree — the
fold is pure de-duplication, and their `ℝ × ℝ` packaging was left untouched.

Index gotcha worth keeping: `(((1:ℕ):ℝ) + 1)` and `(2:ℝ)` are NOT syntactically
equal; every crossing needs `rw [Nat.cast_one, show (1:ℝ)+1 = 2 by norm_num]`.
Verification: focused check green; targeted `.olean` refresh needed before the
downstream `realize_at_thr` fold could be checked.
