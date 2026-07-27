# ForwardUniqueRem — R13 tensorization layer

## Status

The new module is focused-check and targeted-build green, warning-free, and
contains no `sorry`.  All five public endpoints have exactly
`[propext, Classical.choice, Quot.sound]`.

This is a genuine partial closure of R13, not the final `hrem` producer:

- R13 raw-carrier evaluation/tensorization layer: approximately **55%**.
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

## Rank correction

The spatial remainder estimate deliberately records both background inputs:

- rank `5`: `|∇Rm₂|²`;
- rank `6`: the full `|∇²Rm₂|²`.

The second input was not replaced by a rough-Laplacian bound. A
`roughLap(Rm₂)` sup alone does not discharge `rmRemNormSq_le`.

## Remaining exact frontier

The raw-carrier obstruction is gone. The remaining work is norm algebra on
genuine tensors:

1. bound the tensorized Uhlenbeck `B` difference by curvature-difference and
   background-curvature norms;
2. use `driftDiff_split` to bound the tensorized Ricci drift by Ricci and
   curvature differences against background factors;
3. expand the second tensor in `gapDot_uhl` through `uhlRaisedDeriv` and bound
   its rough-Laplacian, quadratic, drift, and Ricci-lowering terms;
4. prove the missing pointwise norm bound for
   `(reLower g₂ g₁ (roughLap₁ P) - roughLap₁ P) x`;
5. combine those with the existing `reLowerPairSq_le` and trace bound.

The last trace summand is already in the established product/trace API. The
re-lowering defect in item 4 is the smallest distinct API gap after the new
evaluation identities.

## Proof-route lesson

The useful abstraction was reconstruction from basis components, not component
enumeration. An attempted reuse of the lane-local `normSq0S_smul` pulled in its
unrelated compact-manifold section context; expanding the fiber inner product
locally gave the same scaling identity under the weaker assumptions of this
module.
