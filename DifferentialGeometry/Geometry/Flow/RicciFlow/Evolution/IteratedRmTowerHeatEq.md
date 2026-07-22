# IteratedRmTowerHeatEq

## Pointwise heat producer

`nablaKNorm_smooth` derives fixed-time spatial smoothness of every intrinsic
curvature-tower norm from the arbitrary-valence tensor norm API.
`nablaKNormDu`, `nablaKNormHess`, and `nablaKNormLap` are the canonical scalar
differential, Hessian, and intrinsic Laplacian objects.

`nablaKNormHeatAt` is the local interface needed by the BBS assembly. At one
regular time and point it chooses smooth global extensions of the supplied
tangent basis internally and discharges all scalar realization hypotheses. Its
only noncanonical inputs are the actual component time derivatives of the
inverse metric and of `nablaKRm04Field` at that point.

The older global `nablaKRm04NormHeatEquationOn_intrinsic` interface remains
available for compatibility. The pointwise theorem avoids demanding one
global basis and global derivative data when the geometric producer is local.

Focused verification passes. The next consumer is the solution-level
StarSum/Bernstein assembly combining `resStarSol` and `tailFrameTimeReg`.

## 2026-07-22 curvature-tower Kato producer

Added `towerNorm_grad_le`, the solution-specific specialization

`|∇ |∇^k Rm|²|² ≤ 4 |∇^k Rm|² |∇^(k+1) Rm|²`.

It uses the canonical `nablaKNormDu`, `nablaKRm04Field_realizes`, and the new
general covariant-tensor Kato theorem.  Focused verification passed without a
new assumption or `sorry`.

The Kato producer is complete (100%).  The corrected complete-noncompact
Bernstein estimate remains theorem-level 0%; its dedicated localization
machinery is roughly 30--35%, with quantitative parabolic cutoffs and a
dissipative localized induction still missing.  The end-to-end complete
arbitrary-dimensional Shi producer therefore remains theorem-level 0%.
