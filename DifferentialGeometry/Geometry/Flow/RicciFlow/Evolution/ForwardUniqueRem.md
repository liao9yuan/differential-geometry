# ForwardUniqueRem — R13 tensorization layer

## Status

The generic remainder tensorization and norm-estimate layer is complete.
Focused verification and the targeted export refresh both pass, the file is
warning-free, and it contains no `sorry`.

This is a genuine partial closure of R13, not the final `hrem` producer:

- R13 generic tensorization/re-lowering layer in this file: **100%**.
- Argument-free `hrem`: **0%** until the remaining tensor product/re-lowering
  bounds are assembled into the actual slab field.
- `ricci_flow_forward_unique`: **0%** until its theorem body is replaced and
  checked; its dedicated forward-uniqueness machinery remains approximately
  **90%** at this point.
- Whole HCG compactness project: approximately **10%**.

## Checked results

- `lowOfComp_ext` proves that `lowOfComp` reconstructs an arbitrary `(0,4)`
  tensor from its components in any basis.
- `lowerTri_low` turns an arbitrary lowering of a trilinear vector-valued map
  into a genuine `(0,4)` tensor with explicit basis components.
- `rmDotRem_low` eliminates the raw `rmDotRem` component array. Its tensor is
  the intrinsic `lapDiffRem`, minus the tensorized Uhlenbeck quadratic
  difference and tensorized Ricci-drift difference.
- `gapDot_uhl` eliminates the bare `uhlRm2Vec` from `gapDot`. The result is the
  difference of two explicit `lowOfComp` tensors: the
  `2 (Ric₁ - Ric₂) * Rm₂` term and the metric-difference pairing with the
  explicit `uhlRaisedDeriv` right-hand side.
- `rmDotRemSq_le` gives a pointwise squared-norm estimate for the reconstructed
  `rmDotRem`. Its spatial contribution uses the existing
  `rmRemNormSq_le`; the remaining hypotheses are norms of the now-genuine
  quadratic and drift tensors.

## Additional checked results

- `reLowerDefSq_le` writes the last-slot re-lowering defect as a trace of the
  product with the metric difference and gives its pointwise product bound.
- `metricDiffSwap_le` transports the reversed metric-difference norm through
  the standard two-sided metric-equivalence API.
- `roughLapSq_le` controls a rough Laplacian by the full second covariant
  derivative whose rank-six closed-slab bound is now available.
- `lowerTriSq_le` realizes arbitrary lowering of a trilinear family as one
  trace of a permuted tensor product.
- `lowerTriDiffSq_le` identifies lowering by the metric difference with the
  negative re-lowering defect, reusing `reLowerDefSq_le`.
- `lowerTriSwapSq_le` combines that estimate with two-sided metric comparison,
  so a `g₁-g₂` lowering is controlled by the `g₂`-own-lowered speed.
- `ownRmDiffSq_le` turns the two own-lowered curvature inputs of the
  Uhlenbeck quadratic block into `rmDiffSq` plus the metric lowering gap.
- `traceProdSq_le` is the rank-generic norm bound for a traced, slot-permuted
  tensor product; it is the primitive needed by the `B` and drift arms.
- `uhlSpeed_low` identifies the own-metric lowering of the actual
  `uhlRm2Vec` with the complete rough-Laplacian, `B`, drift, and
  Ricci-lowering component right-hand side.

## Rank correction

The spatial remainder estimate deliberately records both background inputs:

- rank `5`: `|∇Rm₂|²`;
- rank `6`: the full `|∇²Rm₂|²`.

The second input was not replaced by a rough-Laplacian bound. A
`roughLap(Rm₂)` sup alone does not discharge `rmRemNormSq_le`.

## Remaining exact frontier

The raw-carrier and generic norm-algebra obstructions in this file are gone.
The quadratic, Ricci-drift, and own-flow speed estimates now live in the
separate `ForwardUniqueQuad`, `ForwardUniqueDrift`, and `ForwardUniqueSpeed`
layers.  The remaining work is solution-specific: identify those invariant
tensors with the `fu*` component families, take the already available
closed-slab suprema, and assemble the actual `sdecRemFam` estimate in
`ForwardUniqueWiring`.

## Proof-route lesson

The useful abstraction was reconstruction from basis components, not component
enumeration. An attempted reuse of the lane-local `normSq0S_smul` pulled in its
unrelated compact-manifold section context; expanding the fiber inner product
locally gave the same scaling identity under the weaker assumptions of this
module.
