# SourceAllOrder

## Mathematical route

`srcSol_memWkp_on` is the all-order scalar Nirenberg interior producer.  Its
proof is a structural induction on the source order `m`.

- At order zero, `srcSol_memW2_on` supplies the local `W^{2,2}` estimate.
- At a successor order, local compactness supplies one open intermediate domain
  `U` with `closure V ⊆ U` and compact `closure U ⊆ Omega`.
- The induction hypothesis first raises `u` to `W^{m+2,2}(U)`.
- `srcEq_restrict` restricts the actual scalar-source weak equation to `U`.
- For each first weak derivative, `srcDiff_weak_eq` produces the weak equation
  with source
  `chosenWeakPartial' 2 l f U + rho * homDiffSource B u U l`.
  The first summand is in `W^{m,2}` by the source hypothesis, while
  `homDiff_memWkp` supplies the same regularity for the coefficient source.
- A second use of the induction hypothesis raises every first weak derivative
  to `W^{m+2,2}(V)`.  `chosenWeakPartial'_mono_set_ae` and
  `MemWkp_congr_ae` identify the derivative chosen on `U` with the canonical
  derivative chosen on `V`; `MemWkp_succ` then assembles `W^{m+3,2}(V)`.

No multi-index hierarchy, new predicate, or extra hypothesis is introduced.

## Reuse

The proof uses only `DifferentialGeometry`-native producers:
`srcSol_memW2_on`, `srcEq_restrict`, `srcDiff_weak_eq`,
`homDiff_memWkp`, the existing Sobolev restriction/a.e.-congruence API, and
Mathlib's precompact intermediate-open theorem.  The reference trees were not
imported or copied.

## Verification

The first focused pass reached the complete proof and found only two recursive
application mismatches: `B`, `rho`, their positivity proof, and `hc` stay fixed
across the induction, so they are not explicit arguments of the recursive
hypothesis.  Both calls now use named domain/function arguments and pass the
corresponding coefficient identity immediately after the weak equation.

The corrected file passed a warning-free focused check.  Its explicit named
module refresh also passed, so downstream modules can consume
`srcSol_memWkp_on` without a stale artifact.  No mathematical, assumption, or
native-API blocker remains in this producer.
