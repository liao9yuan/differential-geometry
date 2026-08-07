# Class-first mixed H1-H2 application estimate

`appRS_h1_unif` is the dimension-three, generic-rank class producer for an
`H¹` operator field acting on an `H²` mixed passenger into `H¹`.  It composes
the uniform mixed Morrey constant, two uniform mixed `H¹ -> L⁶` constants,
the rank-independent class `L⁶ -> L³` volume cap, and the metric-local
`appRS_h1_of` kernel.

`appRS_h2_unif` supplies the complementary class-first orientation, with an
`H²` operator field acting on an `H¹` passenger.  It uses the same class
Morrey, `H¹ -> L⁶`, finite-volume `L⁶ -> L³`, and supplied-provider layers.
This orientation is required by the fixed-curvature and curvature-passenger
branches without asking for a second curvature derivative.

Only metric jets of orders one and two occur in the public interface.  Focused
verification passed with four Lean threads and no warnings.  A temporary axiom
census reported only `propext`, `Classical.choice`, and `Quot.sound`; the print
was removed.
