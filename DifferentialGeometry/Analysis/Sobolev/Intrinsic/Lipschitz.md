# Intrinsic Lipschitz weak Green identity

## 2026-08-29: noncompact compact-test producer

`lip_green_comp` proves Green's first identity for a globally
intrinsic-Lipschitz scalar function against a compactly supported smooth vector
field on a boundaryless, Hausdorff, sigma-compact manifold.  Unlike the older
compact-manifold `global_lip_ibp` route, it assumes neither `CompactSpace M` nor
a global bound on the scalar function.

The proof chooses a smooth compactly supported cutoff equal to one near the
test field's support and retains only the finitely many partition-of-unity
charts meeting that support.  In each chart, `chart_mul_lip` makes the cutoff
product globally Lipschitz after zero extension.  Rademacher differentiability,
`chart_local_ibp_lip`, and `chart_int_eq_volume` give the local identity and
transport it back to Riemannian volume.  Local finiteness of the partition and
the cutoff's neighborhood equality identify the finite sum of tangent actions
with the tangent action on the original scalar function almost everywhere.

`chart_lip_ae_mdiff` is kept private: it is only the local Rademacher bridge
from the zero-extended chart pullback to manifold differentiability.

Focused verification passed without warnings.  No new axiom, instance,
notation, global boundedness hypothesis, or theorem-shaped placeholder was
introduced.  A named refresh is required only because the distance
distributional consumer now genuinely uses `lip_green_comp`.

This completes the noncompact weak-Green producer itself.  It is dedicated
machinery for the P1c distance-Laplacian endpoint; that formal endpoint remains
0% until the radial pairing and final distributional inequality are stated and
proved.
