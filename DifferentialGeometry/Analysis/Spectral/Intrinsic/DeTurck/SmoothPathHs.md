# SmoothPathHs

## Proved source result

- `ccHs_eq_smoothHs` identifies the generic smooth covariant Sobolev
  embedding with the Ricci--DeTurck `(0,2)` embedding.
- `smoothHs_path_cd` proves that a jointly smooth `SmoothCcTensor` path is a
  smooth path in every integer spectral Sobolev space.
- `smoothHs_deriv` chooses one jointly smooth tensor time derivative and keeps
  both of its characterizations: fully evaluated fibre components have that
  ordinary derivative, and its Sobolev embedding is the strong Banach-valued
  derivative at every integer order.

The proof applies the time-dependent coefficient to a fixed rank-zero scalar
unit and reuses `ParametricAppHsTime`; it adds no topology to
`SmoothCcTensor`.

The small upstream wrapper `exists_appHsFull` records the full output already
constructed by `exists_timeDerivCc` and the completed-action proof.  It adds no
new hypothesis and makes it possible to identify the chosen derivative with a
geometric PDE right-hand side by component extensionality.

## Role in the low-regularity path

On a compact time window inside the open smooth interval of a geometric
Ricci--DeTurck solution, this supplies the continuous `H^(a+2)` path and the
continuous `H^a` derivative path needed for a strong maximal-regularity pair.
It intentionally makes no claim at a left endpoint where only `C0` metric
convergence is known.

## Verification state

Focused Lean verification is green, with no local warning and no
`sorry`/`admit`. The exact artifact refresh is still pending.

The first exact downstream attempt exposed two compatibility failures here:
the TensorRS bundle instances needed the canonical reduced-transparency
elaboration setting, and the constant scalar section had to be changed
explicitly to `1` before simplifying its action. Both are now repaired without
changing any public statement or mathematical assumption.

Forward uniqueness is already complete elsewhere; this file is now an upstream
producer for the moving-edge estimate used by the uniform low-regularity
existence route. The black-box theorem `ricci_flow_unif_existence` remains
unproved (0 percent); its dedicated machinery remains approximately 84--87
percent complete.
