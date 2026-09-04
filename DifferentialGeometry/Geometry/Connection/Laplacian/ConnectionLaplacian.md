# ConnectionLaplacian

## `cov_zero_of_frob`

The new pointwise theorem states that if the Frobenius square of the
Levi-Civita covariant derivative of a vector field vanishes at a point, then
the full covariant-derivative continuous linear map vanishes there.  It does
not require the vector field to be smooth.

The proof uses only the finite sum defining `frobeniusSq_grad_vector`,
positivity of the Riemannian metric, and the center values of
`smoothOrthoFrame`.  A private `smoothFrameBasis` helper packages those center
vectors as a basis: orthonormality gives linear independence and the cardinality
equals the tangent-space finrank.  Vanishing of a sum of nonnegative metric
squares then kills the covariant derivative on every basis vector, and
linearity kills it on an arbitrary tangent vector.

No boundaryless, separation, sigma-compactness, or smoothness assumption on the
vector field is used.  The positive-dimension `NeZero` instance is genuinely
needed by `smoothOrthoFrame` and by the nonempty finite frame sum; the theorem
and private helper retain it while omitting the other ambient section
assumptions.

The first focused check reached only the missing positive-dimension instances.
After restoring those genuinely necessary instances, the corrected source
passed its focused check without warnings and its explicitly named module
refresh completed successfully.  `cov_zero_of_frob` is therefore a verified
producer.  It remains dedicated infrastructure for the splitting chain; the
supplied-line splitting theorem itself is still unstated and 0% complete.
