# DeTurckLieCoeffL2JetBound.lean — DLb field top-separated wrapper (in-flight)

## Scope (session 2, 2026-07-24)

Downstream **field** lift of the DLb insert-level top-separated producers.  Adds three
declarations after the existing ballUniform field wrapper (`~:244`), all `R`-free:

- `normSq_iCG_dlbField_le` (private, generic over `g₁`): the per-order `×4·finrank` transport
  `‖∇ⁱ deTurckLieDLbCoeffField‖² ≤ 4·finrank·‖∇ⁱ deTurckLieWEndoInsert‖²`.  Splits the `(2,2)` field
  into two slotInsert/reindex pieces via `deTurckLieDLbCoeffField_eq_slotInsert_sum` (:47), bounds
  each by `finrank·‖∇ⁱ wEndoInsert‖²` (`normSq_iteratedCovGrad_le_scaled_of_pointwise` +
  `rfns_iteratedCovGrad_dlbSlotZero_le`/`dlbSlotOne_le`), and closes with `sq_le_two_add` giving
  `2·(finrank·W + finrank·W) = 4·finrank·W` (`le_of_eq (by ring)`).  This mirrors the ballUniform
  wrapper's core but keeps `‖∇ⁱ wEndoInsert‖²` as the RHS instead of a fixed `F i`, so BOTH field
  endpoints reuse it.
- `deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_topSeparated` — thin: obtain the insert
  perOrder bound, then `le_trans (normSq_iCG_dlbField_le …) (mul_le_mul_of_nonneg_left hins …)` and
  `ring` to distribute `4·finrank·(Ktop·X + Kc·Y) = (4·finrank·Ktop)·X + (4·finrank·Kc)·Y`.
  `Ktop_field = 4·finrank·Ktop_insert`.
- `deTurckLieDLbCoeffField_realizedFam_jetL2_summed_topSeparated` — sums `normSq_iCG_dlbField_le`
  over `range (a+1)` (`Finset.mul_sum` + `sum_le_sum`) against the insert-SUMMED bound.  This
  **avoids** the vector-field-file's private `jetL2_sum_lowShift` (inaccessible downstream); no new
  summation lemma needed in this file.

## SHAPES

Match the DLa field siblings `deTurckLieDLaCoeffField_realizedFam_jetL2_{perOrder,summed}_topSeparated`
(`DeTurckLieKernelL2JetBound.lean:5680/5966`): per-order `Ktop·(‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²) +
Kc i·(1+∑_{j<i+3}(…))`; summed both windows `a+3`, single `Kc`.  Quantifier order s-before-i.

## Constant discipline

Field `Ktop = 4·finrank·Ktop_insert` is `R`-free (finrank is g₀-level; `Ktop_insert` is the
insert-level `2·ΛClow 0·Ktop_xi`, `R`-free).  `R` only in `Kc`.

## Status

Code written; whole-file check + axiom audit of the two field endpoints pending the vector-field
module olean refresh (heavy build).  Insert-level producers verified green (see
`DeTurckVectorFieldL2JetBound.md`).
