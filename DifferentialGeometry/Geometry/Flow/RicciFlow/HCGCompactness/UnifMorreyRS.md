# UnifMorreyRS

## Status (2026-08-06)

This file fixes the public mixed Morrey interface in dimension three while
remaining generic in the tensor valence `(r,s)`.

- `morreyRSC` is an explicit function of the fixed background, `Λ`, and the
  valence.  It contains the reverse first/second metric-jet caps and the fixed
  background Morrey constant; it never depends on the variable class metric.
- `morreyRSC_nonneg` records the sign needed by later cap packages.
- `morreyRS_unif` has the required class-first quantifier order and the fixed
  three-term window `j=0,1,2`.

The lower-layer slot-permutation frontier is now closed, so the assembly is
complete without changing its public statement.  Focused verification passed
without warnings or `sorry`.  `morreyRS_unif` was axiom-audited and uses only
the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with
no `sorryAx`.

Progress: `morreyRS_unif` and its dedicated mixed-Morrey machinery are 100%
complete.  This is a producer for the later class-first tame packet, not the
uniform-existence endpoint: `ricci_flow_unif_existence` remains unproved (0%),
and the whole HCG compactness project remains approximately 3% complete.
