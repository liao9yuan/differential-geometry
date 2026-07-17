# EntropyJensen

## 2026-07-16 probability Jensen layer

`withDensity_prob`, `int_log_le_moment`, and `entropy_le_moment` are checked
without warnings or a local `sorry`.  Together they turn the normalized
density `v ^ 2` into a probability measure, apply Jensen to `exp`, and return
the entropy-moment estimate on the original measure.  The proof obtains the
needed measurability from `Integrable (v ^ 2)`; it does not add an
`AEMeasurable v` consumer assumption.

These three measure-theoretic producers are **100%**.  They are inputs to the
closed-manifold log-Sobolev theorem, not a no-local-collapsing endpoint.
