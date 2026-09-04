# Raw branch-energy Hessian producer

## Status

rawBranch_hess_pos is warning-free focused GREEN. It is a raw
complete-extension producer: it proves strict positivity of the Hessian of the
actual branchEnergy for every ExpInvBranch at a nonzero target direction.
It does not state a Jensen or distance wrapper.

The lower bridge rawExt_no_conj is warning-free focused GREEN. It
proves nonconjugacy for a fenced raw complete-extension launch below the raw
curvature conjugacy scale. The native IsConjVec and expMapIntrinsic declarations
already carry the ambient positive-finrank instance, so the bridge honestly
uses that existing CGT-section instance rather than adding a new hypothesis or
creating a parallel zero-dimensional API. The private Jacobi proof is now the
same native-dimensional statement as its public bridge.

The launch definition is explicitly dimension-neutral: its complete-extension
construction uses only the metric-norm and completeness interfaces. The private
Jacobi helper and public bridge each omit the unused tangent-bundle separation
instance, and the completed focused verification is warning-free.

## Route

rawExtLaunch supplies the complete-extension geodesic. The private
rawExt_quad_le transports the raw pullback curvature quadratic estimate across
the rawAgree ball using rawExt_restrict and rawExt_inner. For a transverse
Jacobi field, rawBranch_pair_pos combines the branch's native nonconjugacy
certificate with the Jacobi index-form positivity API. The public theorem
decomposes an arbitrary direction into this transverse component and the radial
component, whose branch-energy Hessian is computed directly.

The proof uses the raw curvature, extension, and native Jacobi/index-form
interfaces only; it does not depend on CGTWhiteheadJensen.

rawExt_no_conj follows the first-interior-maximum argument for a vanishing
Jacobi field: obtain a regular short interior point from the zero-vector
branch, rescale at a positive maximum of its squared norm, transfer the raw
quadratic curvature estimate through rawExt_quad_le, and contradict native
Jacobi index-form positivity. It uses the branch API only at the zero vector,
not as an endpoint nonconjugacy premise.

## Frontier

This closes the branch-energy Hessian brick. The later actual
half-squared-distance strict-Jensen endpoint still needs its separate raw
distance/branch-selection consumer chain; this file deliberately does not
replace it with branch energy.

The raw strict-Jensen theorem itself is not yet stated (0%). The verified
branch-energy Hessian brick is complete for its own scope, and rawExt_no_conj
is verified infrastructure. The actual-distance germ and strict-Jensen consumer
remain separate, unstated work.

The pinned consumer exposed an API-only leak: `rawExt_no_conj` inherited base
`T2Space` and `SigmaCompactSpace` through the raw pullback curvature chain.
After weakening the generic target-side curvature naturality signature, this
file now omits those two base instances and retains the already-present
tangent-bundle separation instance used by the raw pullback layer.  The
mathematical proof is unchanged.  This weakest-signature adjustment is
warning-free focused GREEN after removing the now-unused Sigma instance from
the two branch-Hessian consumers.
