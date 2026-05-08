# Local Coordinate Tensor Proofs

This folder should use local coordinates as an evaluation layer, not as the
definition of tensorial objects.

## Design

- Define tensor operations intrinsically on fibers first.
- State coordinate formulas with a genuine pointwise basis:
  `basis : Module.Basis Idx Real (TangentSpace I x)`.
- Use local frames only after converting them to pointwise bases via
  `hframe.toBasisAt hx`.
- Keep inverse metric hypotheses basis-level:
  `MetricInverseInBasis g x basis gInv`.
- Prove arbitrary-frame formulas only through a bridge that supplies a basis.
  A raw finite family of tangent vectors is not enough for tensor coordinate
  identities.

The current model example is:

- `Tensor0SBundle.normSq0S_two_eq_coord`
- `RicciFlower.Realized.normSq02_eq_coord`

The first theorem proves the intrinsic `(0,2)` norm-square formula in a basis.
The second theorem specializes it to local-frame components by using
`metricInverseInBasis_of_frame`.

## Proof Pattern

For a tensor formula in local coordinates:

1. Define the tensor expression intrinsically.
2. Prove a basis-coordinate theorem in the tensor layer.
3. In a realized/local-frame file, convert the local frame to a basis using
   `hframe.toBasisAt hx`.
4. Convert frame inverse-metric hypotheses to `MetricInverseInBasis`.
5. Rewrite local-frame components with `IsLocalFrameOn.toBasisAt_coe`.

This keeps coordinate formulas robust under overlap changes: two different
frames give the same scalar because both coordinate sums equal the same
intrinsic tensor expression.

## Basis Trick

The useful Lean bridge from intrinsic metric contractions to coordinates is:

- reconstruct basis coefficients using inverse metric contractions;
- expand traces with `LinearMap.trace_eq_matrix_trace`;
- rewrite matrix diagonal entries with `LinearMap.toMatrix_apply`;
- translate the metric adjoint back with `MetricFiberData.adjoint_inner`;
- use `cotangentMetricData_inner_eq_coord` for the remaining covariant slot.

In `normSq0S_two_eq_coord`, this appears as:

- `basis_repr_eq_sum_inv_inner`;
- `hom_normSq_eq_basis`;
- `tensor0S_curry_one_apply`;
- `cotangentMetricData_inner_eq_coord`.

The key idea is that the Hom/Hilbert-Schmidt norm of the curried `(0,2)`
tensor reduces to

```text
sum_i sum_k gInv i k * inner_cotangent (A(e_i, -)) (A(e_k, -)).
```

Then the cotangent coordinate theorem expands the second slot, giving the
standard four-index expression.

## Later Use

For Bochner, Ricci norm, curvature contractions, and evolution calculations,
prefer this order:

- prove the intrinsic tensor object or scalar first;
- prove the basis coordinate formula in `Tensor/RSTensor`;
- consume it in `Realized/*` or `Coordinates/*` using `hframe.toBasisAt hx`;
- keep hard geometric producer facts as explicit hypotheses until the
  Levi-Civita/time-evolution infrastructure proves them.

If a proof gets stuck, stop at a precise basis-level theorem. Do not replace an
intrinsic definition by a coordinate definition just to make downstream algebra
typecheck.
