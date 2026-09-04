# Differentiated weak equation

## Mathematical route

`homDiff_weak_eq` is the scalar-source bridge needed before applying the local
Nirenberg `W^{2,2}` estimate to a first weak derivative of a homogeneous
solution.

The proof keeps the existing public interfaces unchanged:

- an arbitrary witness for the chosen first weak derivative is replaced, only
  inside the bilinear form, by the canonical witness selected by `MemW1p`;
- `homSol_diff_id` supplies the differentiated identity on smooth compactly
  supported tests;
- `homDiff_hasDiv` identifies the coefficient-derivative vector field with the
  scalar source and fixes the sign (the resulting scalar source appears with a
  positive sign);
- `weak_eq_of_smooth` extends the identity to every `H₀¹` test;
- `weakRHS_eq_integral` converts the divergence functional to the scalar
  `L²` pairing.

No compact-manifold variational Laplacian, boundary extension, new solution
predicate, or extra coefficient-bound hypothesis is introduced.

## Reused producers

- `homSol_diff_id`
- `homDiffField_memLp`, `homDiffSource_memLp`, `homDiff_hasDiv`
- `weak_eq_of_smooth`
- `weakRHS_eq_integral`

## Verification

Focused verification passed without warnings. The exported module was then
refreshed successfully for its real downstream consumer.
