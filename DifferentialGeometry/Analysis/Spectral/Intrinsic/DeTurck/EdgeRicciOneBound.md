# EdgeRicciOneBound

## Current source state

`EdgeRicciOneBound.lean` contains a placeholder-free proof of the closed-edge
order-one Ricci estimate.  The current source passes focused verification
without a local diagnostic and its named exact artifact is GREEN.

The file exports:

- `ricci1Ker_rfns`: the exact five-arm order-one kernel has fibre norm square
  at most `46` times that of `connDiffContrInsertionField`;
- `ricci1Coeff_rfns`: after the moving four-trace contraction, the concrete
  coefficient is pointwise bounded by a carrier-dependent constant times
  `|nabla P|^2`; and
- `ricci1_path_le`: on `P = s W`, after shrinking a carrier-dependent `C0`
  radius, the signed order-one Ricci energy term costs at most
  `(1/8) * ||nabla W||^2`.

No derivative above `nabla W` occurs.  The proof uses the fixed-metric
connection-difference fibre bound, the order-zero four-trace grid at
derivative order zero, pointwise Cauchy--Schwarz, and spatial integration.

## Why the five-arm split is local

The canonical expansion exists in
`RicciConnDiffOrder1TameEnvelope.lean`, but its theorem
`kernelField_eq_neg_arm_combination` and its sharp arm permutations are
private implementation details.  The public tame-envelope wrapper requires a
high-jet radius and is therefore inadmissible at the closed edge.  This file
reproves only the finite five-arm identity.  The current repair reuses public
`permCoeff` and unfolds the five-arm split pointwise; this avoids the known
mixed-bundle topology diamond caused by section extensionality.

## Verification and downstream status

- Source placeholders (`sorry`, `admit`, axiom): none.
- Focused Lean check: GREEN with no local diagnostic.
- Named exact artifact: GREEN.
- Exact `ricci_flow_forward_unique`: complete and axiom-clean.
- `extends_of_rmBounded`: unchanged.  This producer removes only the Ricci
  order-one child of the visible closed-edge pairing.  The remaining adjacent
  child is the non-Ricci DeTurck lower-arm pairing and final rate packaging.
