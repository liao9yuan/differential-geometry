# BranchRadius

## 2026-07-23 fixed-first selected inverse calculus

The canonical branch radius keeps the selected-branch center independent of
the later fixed source point.  The file now defines `branchEnergy` and
`branchRadius` and proves:

- `exp_inv_mfderiv`, the differential of the selected fixed-first inverse is a
  right inverse of the intrinsic exponential differential;
- `inv_exp_mfderiv`, the corresponding left-inverse identity on the selected
  source;
- `branchRadius_infAt` and `branchRadius_open`, all-order smoothness of the
  branch radius at every selected nonzero launch vector, including an explicit
  open endpoint neighborhood;
- `grad_branchEnergy` and `grad_branchRadius`, the intrinsic first-variation
  formulas obtained from `intrinsic_gauss`;
- `branchRadius_ray`, the exact affine radial identity along a selected ray.

These proofs use only the open selected branch, intrinsic exponential
smoothness, and the canonical fixed-first coordinate readout.  They do not add
`ConnectedSpace`, a raw exponential-domain hypothesis, or a quantitative
radius.  Focused verification passed with no local placeholders, and the new
module's exact artifact is current.

The fixed-first inverse calculus in this file is complete (100%), and Layer A
of the radial-Laplacian route is complete (100%).  This is producer
infrastructure: the radial-Laplacian endpoint is accounted separately until
its own theorem is proved and verified.  Whole HCG supporting machinery
remains roughly 60%, while unconditional `compactnessSol` remains 0%.
