# WEstimate

## 2026-07-16 positive-amplitude normal form

`w_square_form` is checked.  For a positive smooth amplitude `v`, it rewrites
the potential-form functional with density `v^2` into the exact sum of the
Dirichlet term, scalar-curvature term, entropy term `-v^2 log(v^2)`, and the
Perelman prefactor constant.  The proof uses the public base-measure normal
form and `square_pot_energy`; it does not introduce a log-Sobolev or cutoff
assumption.

Focused verification passed without warnings or a new `sorry`.  The W
amplitude normal form is **100%**.  The fixed-metric W lower-bound theorem is
still **0%**; its next missing producer is the entropy Jensen/log-Sobolev
estimate.  Perelman no-local-collapsing and `ham3_noncollapse` remain
theorem-level **0%**.

## 2026-07-16 fixed-metric closure

The Jensen, intrinsic Sobolev, log-Sobolev, and prefactor producers are now
checked, and `w_fixed_lower` uses this normal form to prove the actual
fixed-metric canonical W lower bound.  `w_square_form` remains **100%** and the
fixed-metric lower-bound theorem is now separately **100%**.  The next
substantial producer is the quantitative intrinsic ball cutoff; no-local-
collapsing and `ham3_noncollapse` remain theorem-level **0%**.
