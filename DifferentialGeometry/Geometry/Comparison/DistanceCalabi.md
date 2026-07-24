# DistanceCalabi.lean

## 2026-07-23 — broken paths and the terminal Calabi branch

- This canonical comparison-layer module packages the routine metric and
  inverse-branch facts needed before constructing a Calabi distance support.
- `edistOf_le_arcLength` installs the supplied smooth metric locally and reuses
  the checked geodesic-layer path-length comparison.
- `edistOf_le_two_arcs` combines the one-arc result with the Riemannian extended
  distance triangle inequality at the common endpoint.
- `calabi_tail_of` starts from the finite-distance Hopf–Rinow minimizing
  witness, follows its intrinsic velocity lift, and uses openness of a supplied
  `DiagInvBranch` to choose `0 < s₀ < 1`.  Continuation and spray homogeneity
  prove that the scaled remaining velocity exponentiates to the endpoint;
  `DiagInvBranch.inv_eq_of_exp` then identifies the selected inverse.  The
  theorem also records that the endpoint pair lies in the branch target
  domain, which is the openness seam needed by the later local support.
- The proof uses a private connectivity-free continuity lemma for fiberwise
  scalar multiplication along a continuous total-space curve.
- `exists_calabi_tail` specializes the preceding result to `stdBranch`.
- No Ricci-flow, connectedness, injectivity-radius, or cut-locus hypothesis is
  introduced.  Completeness occurs only in the Hopf–Rinow terminal-tail result;
  the two broken-path estimates remain completeness-free.
- The whole module, including the `stdBranch` corollary, is focused GREEN with
  zero diagnostics, and its exact targeted refresh is GREEN (`3807/3807`).

Accounting: the elementary broken-path metric brick and terminal inverse-branch
selection are 100%; together they are about 10% of the spatial Calabi-support
producer.  The public `scaledDist_calabiUpperSupport_of_sol` theorem remains
0%; Route B-prime producer machinery remains about 35%; unconditional
`compactnessSol` remains 0%; whole HCG support remains about 60%.
