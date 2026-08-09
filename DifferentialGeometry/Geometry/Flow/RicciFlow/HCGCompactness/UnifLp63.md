# Class-uniform finite-volume L6 to L3 comparison

`fiberLp3_le_6_unif` fixes a rank-independent coefficient before the class
metric varies.  It combines the explicit total-volume factor from
`fiberLp3_le_6` with the existing two-sided real-volume comparison; no metric
jet assumptions are needed.

Focused verification passed with four Lean threads and no warnings.  A
temporary axiom census reported only `propext`, `Classical.choice`, and
`Quot.sound`; the print was removed.  This is a numerical provider for the
mixed `H¹ × H² → H¹` application estimate, not the final low-regularity tame
producer.
