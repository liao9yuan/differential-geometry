# CoerciveBilinInverse

## 2026-07-10

Added `IsCoercive.symm_norm_le`: an explicit coercivity inequality
`c * ||v|| * ||v|| <= B v v` gives the Lax--Milgram inverse bound
`||B^{-1} xi|| <= c^{-1} * ||xi||`.

This is the first quantitative metric brick for the Route-A moving
inverse-exponential construction.  It is a genuine consequence of the lower
quadratic metric bound, not a new producer assumption.  Focused verification
passed.
