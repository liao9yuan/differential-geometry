# DifferentiatedSourceK

## Target

Prove the all-order source-regularity producer `homDiff_memWkp`: if `u` belongs
to `W^{m+2,2}(Omega)`, then the canonical source obtained by differentiating its
homogeneous divergence-form equation belongs to `W^{m,2}(Omega)`.

## Route

- `homDiffSource` is already the finite sum of two kinds of products: a smooth
  second coefficient derivative times a first weak derivative of `u`, and a
  smooth first coefficient derivative times a canonical second weak derivative
  of `u`.
- Two applications of `MemWkp.chosenWeakPartial_mem`, together with one
  `MemWkp.le_of_le`, lower `u in W^{m+2,2}` to the required `W^{m,2}` factors.
- `MemWkp.smul_smooth_bounded` preserves `W^{m,2}` under each smooth
  coefficient. The coefficient bounds are produced internally on the compact
  closure by the existing uniform iterated-derivative bound theorem.
- `MemWkp.add` and finite sums assemble the source without expanding
  multi-indices or weak derivatives.

The public statement adds no explicit derivative bound, predicate, or frontier
assumption. `DifferentiatedSourceW1.homDiff_memW1` is retained as a thin
specialization at `m = 1`.

## Verification

Focused verification and the explicit named export refresh both passed without
reported warnings.

## Blocker

No mathematical, API, elaboration, or verification blocker remains in this
producer.

## Progress estimate

- `homDiff_memWkp`: 100% as a checked declaration with a refreshed export.
- Dedicated all-order differentiated-source regularity machinery: 100%.
- The all-order homogeneous regularity bootstrap and the Cheeger--Gromoll
  splitting endpoint remain separate unstated/unproved endpoints, both 0%.
