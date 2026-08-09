# Class-first lower Ricci--DeTurck path estimate

`lower_jet_unif` assembles the class-first order-zero and differentiated
application cells with coefficient `C₀ + C₁`.  Unlike the older metricwise
`lower_jet_h1`, no extra pointwise Morrey enlargement is needed: both arms
already generate their pointwise estimates internally from the supplied jet
radii.

The theorem is dimension-three and consumes metric jets through order three.
Focused verification passed with four Lean threads and no warnings.  A
temporary axiom census reported only `propext`, `Classical.choice`, and
`Quot.sound`; the print was removed.  This is the lower application wrapper,
not yet the full low-regularity tame packet.
