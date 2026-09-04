# SecondVariationMinimiser

## P1a completeness-free index-form bridge (2026-09-01)

- Mathematical route: split the second-variation argument from the construction
  of a realizing variation.  `indexForm_nonneg_var` starts from an already given
  globally smooth, endpoint-fixed variation of a minimizing unit geodesic and
  proves nonnegativity of the index form of its variation field.
- Reuse: the proof is the existing first/second variation route, followed by the
  germ-local transfer of the index-form integrand on the open interval.  No new
  geometric assumption or parallel index-form API is introduced.
- Realization: `indexForm_nonneg_of_minimising_geodesic` now uses the native
  compact-support-flow producer `exists_var_fix_ends`.  That producer realizes
  the field without ambient manifold completeness, so the old intrinsic
  exponential construction is no longer on this theorem's dependency path.
- Weakest assumptions: the wrapper no longer asks for `IsMetricNorm`, ambient
  completeness, or a separate smoothness proof for the base curve; smoothness
  of the supplied tangent-bundle field already contains the needed base data.
- Verification: warning-free focused GREEN for both `indexForm_nonneg_var` and
  the refactored `indexForm_nonneg_of_minimising_geodesic`.  The first pass had
  exposed only an explicit regularity-level coercion and inherited unused
  section instances; both were repaired locally.  The explicitly named module
  refresh then passed.  It replayed unrelated dependency linter warnings, but
  the target module itself remained clean; no broad build was run.
- P1a accounting: this is dedicated machinery for the still-unstated final
  compact-closure Bishop endpoint.  It does not change that endpoint from 0%.
