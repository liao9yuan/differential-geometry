# MovingMass

## Current status

Source-written and not yet focused-checked because a shared named Lean build is
still active.

The file proves a genuine mass-only perturbation theorem in the existing
tensor maximal-regularity graph space.  A strongly measurable family
`B(t) : H^a -> H^a` with essential operator norm at most `C` contributes the
forcing `B(t) u_t`.  The existing time-operator lift and maximal-regularity
bound give contraction rate `2 C`, hence a unique fixed point when `2 C < 1`,
with the prescribed initial trace.  No derivative of the mass coefficient is
used.

## Exact limitation

This does not yet solve the low-regularity harmonic-map gauge at the `C0`
initial edge.  Its prescribed divergence-flux arm is generated from an
`L-infinity` flux and is controlled by the Koch--Lamm weighted-gradient and
Carleson norms.  That carrier does not in general put `u_t` in
`L2_t H^0_x`; it naturally gives only a negative-order/distributional time
derivative.  Conversely, the current `L2` maximal-regularity potential has no
proved map into the rough `C0 + sqrt(t) grad + Carleson` carrier.  Therefore
adding an `L2` time derivative to the rough norm does not close the combined
mass-and-flux problem.

The faithful next producer is a direct estimate for the full nonautonomous
operator

`rho u_t - div(A grad u)`

with `rho-1` and `A-I` small in `L-infinity`, keeping the spatial term in
divergence form.  Treating `(rho-1) u_t` as an ordinary rough source would move
the analytic frontier and is not used here.
