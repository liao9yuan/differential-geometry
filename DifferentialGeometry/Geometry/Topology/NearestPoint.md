# Local nearest points

`NearestPoint.lean` isolates the proper-metric input used by the convex-stratum
construction.  A locally closed set has a neighborhood of each of its points
such that every nearby query point admits a genuine distance minimizer on the
set.

The proof writes the locally closed set as an open set intersected with a
closed set.  Properness supplies a nearest point on the closed carrier.  After
halving a ball contained in the open part, the triangle inequality forces that
nearest point back into the locally closed set, so it minimizes on the original
set as well.

This is a generic topology/metric producer.  It does not construct the maximal
smooth stratum and does not assert the Soul theorem.  Focused verification
passed without warnings, as did the targeted module build, root aggregate
check, and direct axiom inspection.  The endpoint depends only on `propext`,
`Classical.choice`, and `Quot.sound`; the current full-project build is pending.
