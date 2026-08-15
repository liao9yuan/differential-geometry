# Convex stratum growth

`exists_slice_succ` is the local dimension-growth theorem used in Sakai's
maximal-stratum construction.  If an embedded `d`-slice `N` lies in a totally
convex set `C`, and a point of `N` is approached by points of `C \ N`, then
every prescribed neighborhood of that point contains a nonempty embedded
`(d + 1)`-slice lying in `C`.

The proof installs the metric determined by the complete Riemannian metric,
uses a uniform diagonal inverse-exponential branch, chooses a nearest point on
the locally closed slice, and pulls the slice into framed normal coordinates.
The nearest-point condition makes the radial coordinate transverse to the
slice.  The finite-dimensional cone theorem then raises the dimension, while
total convexity keeps the cone inside `C`.  Choosing the cone parameter near
the endpoint places the resulting slice in the requested neighborhood.

## Verification

Focused verification, the targeted module build, and the root aggregate check
passed.  Direct axiom inspection shows that the public theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`; it does not depend on
`sorryAx`.  The current full-project build is pending.

## Frontier and progress

This completes the local slice-growth brick, not the dense-stratum theorem.
`exists_convex_stratum` and the Soul theorem remain unstated and therefore 0%
complete.  Dedicated smooth-stratum machinery is now about 45%; the next
substantial producer is maximal-dimension assembly: prove that the union of
maximal embedded slices is relatively open, connected, dense, and totally
geodesic in the compact totally convex core.  Dedicated Soul machinery is
approximately 38--40%, the whole B1 lane remains approximately 22--25%, and
the whole post-HCG Poincare program remains approximately 15--20%.
