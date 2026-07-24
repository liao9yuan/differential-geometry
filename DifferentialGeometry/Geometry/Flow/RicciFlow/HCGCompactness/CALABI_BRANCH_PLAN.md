# Calabi fixed-first branch plan

## Architecture ruling (2026-07-24)

The approved route fixes the early split at `s₀ = 1 / 4`:

```text
finite-distance minimizing geodesic O → x
  → early point p = γ(1/4)
  → nonconjugacy of the long tail p → x and a short extension past time 1
  → fixed-first inverse branch of expₚ at the nonzero tail vector
  → intrinsic Jacobi/Bishop comparison on the whole tail
  → checked branch Laplacian–mean identity
  → ρ(y) = d(O,p) + branchRadiusₚ(y)
  → local distance upper support
```

The endpoint comparison must use some `b > 1`; the checked
`curveMean_le_hyp` concludes only for `t ∈ Set.Ioo 0 b`.  Dimension one is a
separate `Fin 0` branch and must not be hidden behind `0 < finrank ℝ E - 1`.

## Canonical API

Add `Geometry/Exponential/ExpInvBranch.lean`.

- `ExpInvBranch` is a fixed-first `PartialDiffeomorph` inverse branch for
  `expMapIntrinsic g hEnorm p`.
- `branch_of_not_conj` constructs it at an arbitrary nonconjugate vector.
- `ExpInvBranch.not_conj` reads derivative injectivity back from a selected
  source point.
- `DiagInvBranch.fixed` is the compatibility projection used by existing
  zero-section/moving-base consumers.

`DiagInvBranch` remains unchanged as the stronger zero-section object.  Do not
glue an unrelated zero branch to a nonzero branch, and do not create a second
branch-radius/Hessian hierarchy.

## Dependency order

1. **Fixed-first inverse**
   - `ExpInvBranch`
   - the minimal manifold-derivative/chart-IFT bridge
   - `branch_of_not_conj`
   - `ExpInvBranch.not_conj`
   - `DiagInvBranch.fixed`
2. **Fixed-first calculus migration**
   - `BranchRadius`
   - `EndpointShape`
   - `RadialLaplacian`
   - existing diagonal consumers continue through `.fixed`
3. **Minimizing-tail nonconjugacy**
   - `conjVec_reverse`
   - `tail_not_conj_of_min`
   - `tail_no_conj`
4. **Whole-tail intrinsic comparison**
   - intrinsic Jacobi evaluation and raw pole-germ agreement
   - `exists_intrMean`
   - explicit `finrank ℝ E - 1 = 0` branch
5. **Calabi assembly**
   - `ExpInvBranch.edist_le_radius`
   - `CalabiTailData`
   - `exists_calabiTail`
   - `calabiDist_support`

Only after the fixed-metric support theorem is checked should
`Evolution/DistanceBarrier.lean` add time differentiation and the
solution-generated barrier-cutoff family.

## Constraints

- No `ConnectedSpace M`, endpoint injectivity-radius, cut-time, branch, or
  nonconjugacy assumption in the final support theorem.
- No raw/C²-radius assumption along the long tail.
- No HCG/C4 import below the flow layer.
- Keep the fixed-metric calculation intrinsic away from the pole; raw
  coordinates are used only for the pole germ.
- The branch path only needs to bound distance by its length.  It need not be
  locally minimizing for nearby endpoints.

## Live status

- `ExpInvBranch`, `branch_of_not_conj`, and `ExpInvBranch.not_conj`: theorem
  and dedicated IFT machinery **100%**, focused/exact green.
- `DiagInvBranch.fixed`: theorem **100%**, focused/exact green.
- `minExp_of_ne_top`: theorem and finite-pair Hopf--Rinow machinery **100%**,
  focused green with no `ConnectedSpace M`; the former long theorem is now a
  compatibility wrapper.
- Fixed-first calculus migration: `BranchRadius`,
  `ExpInvBranch.edist_le_radius`, `EndpointShape`, `RadialLaplacian`,
  `DiagInvFixed`, and `CartanLocal` are focused green. The first three
  proof-owning modules are exact-current; the final compatibility refreshes
  remain to be coordinated. The underlying radial Hessian/Laplacian
  mathematics remains **100%**.
- `conjVec_reverse`: theorem and dedicated reversal machinery **100%**,
  focused/exact green.  The shifted-tail theorems remain theorem-level **0%**
  while the canonical negative-index-form producer is generalized from
  `[0,1]` to `[0,L]`; that lower repair is mechanical and source-active.
- `exists_intrMean`: theorem and dedicated whole-tail intrinsic comparison
  machinery **100%**, focused green, including the explicit empty `Fin 0`
  branch.  Its lint-clean exact refresh is in the current narrow build window.
- `CalabiTailData`: statement **100%**, focused green.
- `exists_calabiTail` and `calabiDist_support`: statements and proof drafts are
  now present, but theorem-level **0%** until their first focused check is
  green.  The exact minimizing-subsegment helper and the neighborhood-local
  Laplacian/gradient APIs are focused green; dedicated fixed-metric support
  machinery is about **75%**.
- Selected Route B-prime complete-Shi producer machinery: about **50%**.
- Dedicated P4 consumer/assembly machinery: about **98%**.
- Whole HCG supporting machinery: about **60%**.
- Unconditional `compactnessSol`: theorem-level **0%**.

Update this section after each focused-green producer.  A checked helper does
not change theorem-level completion until the named endpoint itself is stated
and proved.
