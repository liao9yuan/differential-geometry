# `ScratchIdentCensus.lean` — notes

This scratch module is the ShortTime campaign axiom census.  On 2026-08-05 it
was widened from 31 to 33 declarations by adding `galArmMassOrd` and
`lowregRung3Ord` after GAP-ORDER landed.

Verification passed.  Every printed declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.

## 2026-08-05: explicit-package census

The census now prints 47 declarations.  The 13 new proved declarations cover
the exact solve constructor/projection, ordered package, absorption lemma,
adapted producer, exact projection and mode convergence, exact Fatou endpoint,
exact σ≤3 mass theorem, and the two renamed operator-window jet lemmas.  Every
one reports only `[propext, Classical.choice, Quot.sound]`.

`lowreg_loMass` is printed separately as the expected frontier control and
reports `sorryAx`: its σ≤3 branch is proved, while its `3 < σ` branch remains
the single explicit `sorry`.  Verification passed.

## 2026-08-05: ordered higher-package census

The census now prints 53 declarations.  The six additions are
`galArmMass4Ord`, `lowregRung4Ord`, `IsRung4Ord`, `lowregRung4Pack`,
`IsHmRungOrd`, and `lowregHmPack`.  The full focused census passed; all six
depend only on `propext`, `Classical.choice`, and `Quot.sound`.  The separately
printed `lowreg_loMass` remains the unique expected `sorryAx` control.

## 2026-08-05: all-real, strict-open, and uniform-interface census

This section supersedes the earlier frontier-control statements above.  The
census now prints 80 declarations, including the same-witness rung-five and
higher-rung chain, the all-real `lowreg_loMass`, the positive strict-contraction
endpoints `lowreg_solve_open`, `lowreg_adapt_open`, and `lowreg_joint_open`, the
explicit class boundary `LowRegGateData` / `IsLowGateUnif`, the reusable
`deTurck_rem_repr` bridge, and the concrete per-metric `lowreg_dt_open` endpoint.

Verification passed.  All 80 declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.  In particular,
`lowreg_loMass` is no longer a frontier control: both its low- and high-order
branches are proved.
