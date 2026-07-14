# Uniform scalar nonautonomous pairings

## 2026-07-14 one-slab source closure

The source now contains the complete intended one-slab chain:

- `cc_comm_unif` gives a support-independent principal commutator constant at
  each order;
- `cc_conn_unif` derives time-uniform `connTraceCoeff` jets from the same
  `metricDiff_slab` metric envelope and gives the first-order pairing bound;
- `cc_lap_unif` intersects the commutator, connection, and quarter-smallness
  slabs, preserves `T - s ∈ D.regular`, and has the fixed top coefficient
  `1 / 3`;
- `cc_a2_unif` converts this to the finite scalar Galerkin normal form with top
  coefficient `5 / 3` and quantifier order
  `tau`, regular-time arm, `n`, `Cmid`, time, mode set, spectral vector.

The constants are independent of spectral support, its cardinality, and the
Galerkin cutoff.  The proof uses `appRS_jet_bdd` and `fixed_jet_bdd` as the two
small coefficient-envelope combinators, the public connection-difference
product-grid estimate, balanced pairing, the scalar Dirichlet gap, and the
existing finite spectral pairing identity.  It adds no consumer assumptions
and does not use `HasLocallyConstantChartAt`.

Verification has not yet run for this file.  Shared-worktree object-file builds
were deliberately stopped after concurrent Lean writers raced on upstream
objects; verification must be resumed serially.  This is currently a tooling
verification frontier, not a known mathematical or API gap.  Until focused
verification succeeds, `cc_a2_unif` is not counted as a completed theorem.

Honest accounting: `cc_a2_unif` theorem completion is 0% pending Lean
verification, while its dedicated source machinery is about 95%.  The
downstream `scalar_crit_tame` theorem is source-written but likewise remains 0%
complete pending verification; its dedicated source machinery is about 96%.
Perelman no-local-collapsing and `ham3_noncollapse` remain theorem-level 0%,
with about 42% dedicated analytic machinery.  Whole HCG machinery is about
54%, with its endpoint theorems at 0%.
