# DiagInvBranch

## 2026-07-11 selected-branch interface

`DiagInvBranch` is the generic explicit branch object recommended by the HCG
normal-branch review.  It records one `OpenPartialHomeomorph`, membership of the
zero tangent vector in its source, equality of its forward map with intrinsic
`diagExp` on that source, and all-order smoothness of its inverse on the target.
Quantitative radii deliberately remain producer data rather than record fields.

The file also proves the reusable consequences `right_inv`, `left_inv`,
`proj_eq`, `exp_eq`, `center_mem`, and `center_inv`; no duplicate inverse-law or
projection fields are stored.  `inv_eq_normal_lt` additionally identifies any
selected branch inverse with the moving normal chart inside the existing named
`expDiffeoRadius`, using only the branch inverse laws.  Focused verification
passed without warnings or local `sorry`s.

This closes the generic branch-interface brick (100%).  It does not yet provide
the quantitative radius needed by a concrete configuration.  The standard and
transported HCG branches, their readout domains, and finite-family containment
are now checked elsewhere.  The concrete `StepB1RawInput` producer and textbook
B1 theorem remain 0%; Step-B/B1 machinery is about 77%, Chapter 4 machinery
about 74%, and whole-HCG machinery about 51%.
