# NormalPhase status

## 2026-07-10

- `normalAccel_eq` identifies the bump-extended normal metric acceleration
  with the raised Koszul expression on the quarter normal ball.
- `normalAccel_norm` and `normalAccel_lip` are uniform in the sequence index
  and base point once a common source radius is supplied.
- `normalDiag_approx` is the reusable conditional endpoint estimate.
- `exists_normalFlow` now discharges its former trajectory assumptions.  For
  a sufficiently small ordinary phase ball it constructs exact trajectories,
  fences them in the controlled normal phase box, and proves the retained
  endpoint map `ApproximatesLinearOn` the free diagonal map.
- Focused verification passed.

The next frontier is a local-isometry/exponential naturality bridge.  The
endpoint is written in the `exp_x` normal model, while the existing generic
`diagExpIFT` is written in the ambient atlas and tangent-bundle charts; they
must be related by the normal-coordinate diffeomorphism rather than treated as
literally the same `E x E -> E x E` function.
