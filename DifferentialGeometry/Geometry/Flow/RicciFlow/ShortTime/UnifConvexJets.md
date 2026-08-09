# UnifConvexJets

## 2026-08-06: explicit curvature-action and convex-jet packages

`CurvActionData` stores the rank-two and rank-three order-zero curvature-action constants.
`IsCurvActionUnif gBase Λ K` is the proof package that fixes those constants before the class
metric varies and supplies both `IsCurvAction0` instances for every metric with the prescribed
uniform equivalence and metric jets through order three.

`ConvexJetData` and `IsConvexJetUnif` are the corresponding data/proof split for simultaneous
convex-path `H²` and `H³` covariant-jet bounds.  The theorem `convex_h23_of_act` constructs the
second package from the first using `covsum_hs_two`, `covsum_hs_three`, and convexity of the
spectral norm.  `convex_jets_of_act` is the existential consumer wrapper.

Focused verification passed with no warnings and no `sorry` in this module.  A
temporary in-source axiom census for the package producers and the class-first
wrappers reported only `propext`, `Classical.choice`, and `Quot.sound`.

The thin class adapter is now complete: `class_curv_actions` packages
`unifCurvAction0_of` and `unifCurvAction3_of`, `convex_h23_unif` feeds that
packet into the finite convex-path comparison, and the two existential wrappers
choose packages from fixed-background curvature caps.  The target module
artifact was refreshed successfully after the dependency repair.

The refresh still replayed the heavy curvature dependency closure, but the
changed memory conditions allowed it to finish.  Future routine checks should
continue to use focused source verification; another target refresh is only
needed after an exported declaration changes.

Progress accounting:

- `convex_h23_of_act`: 100% (proved and focused-check green).
- Explicit curvature-action-to-convex package layer: 100%.
- Metric-class instantiation of `IsCurvActionUnif` and `IsConvexJetUnif`: 100%.
- `lowreg_bounds_unif`: 0% (not yet stated and proved).
- `ricci_flow_unif_existence`: 0% (not yet proved; this module is dedicated machinery only).
- Dedicated uniform-existence machinery: approximately 95%; whole HCG compactness project:
  approximately 3%.
