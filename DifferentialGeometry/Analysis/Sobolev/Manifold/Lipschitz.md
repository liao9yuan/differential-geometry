# `Lipschitz.lean`

## `chart_mul_lip`

The noncompact compact-multiplier producer is now proved:

```lean
theorem chart_mul_lip
    [T2Space M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (α : M) {a u : M → ℝ} {L : ℝ≥0}
    (ha : ContMDiff I 𝓘(ℝ) ∞ a)
    (ha_cs : HasCompactSupport a)
    (ha_supp : tsupport a ⊆ (chartAt H α).source)
    (hu : ∀ x y, edist (u x) (u y) ≤ L * riemannianEDistOf g x y) :
    ∃ C : ℝ≥0, LipschitzWith C
      (chartPullZero α (fun x => a x * u x))
```

The proof uses the existing `chartPushedRaw`/`chartPullZero` representations,
`chart_inv_edist_le`, compact support of the multiplier, smooth compact-support
Lipschitz control, and `Euclidean.lip_of_local_comp`.  It does not assume a
global bound for `u`, `CompactSpace M`, or `SigmaCompactSpace M`.  The amplitude
bound needed by `lip_of_local_comp` is obtained only after multiplying by `a`,
from continuity and compact support of the product.

The existing private `chart_lip_ae_mdiff` proof in
`Analysis/Sobolev/Intrinsic/Lipschitz.lean` confirms the immediate downstream
route: `LipschitzWith.ae_differentiableAt`, then `ae_chart_of_haar`, then
`mdiff_of_pull`.  Thus this theorem supplies chart-local almost-everywhere
manifold differentiability for `a * u` without compactness of the manifold.

Focused verification passed without warnings.  No downstream module refresh
was performed.

## `raw_memW1p_of_lip`

The chart-cutoff route has now been parameterized for every intrinsically
Lipschitz real-valued function.  It chooses a compactly supported smooth bump
which is one near the chart center, applies `chart_mul_lip`, transfers the
result through `toEuclidean`, uses the Euclidean
`memW1p_ball_of_lip` producer on a finite chart ball, and removes the cutoff by
almost-everywhere congruence where the bump is one.

This extraction replaces the geometry-specific cutoff block formerly in
`BusemannLineEnergy`.  The new theorem passed warning-free focused verification
and its named module refresh is green; the shortened Busemann consumer also
passed focused verification.  No new compactness, boundedness, or splitting
assumption was introduced.

## Scope accounting

- `chart_mul_lip`: theorem complete (100%).
- Noncompact signed weak-Green theorem: not stated or proved here (0%); this
  closes only its compact-multiplier chart-Lipschitz/a.e.-differentiability
  input.  The Green identity and global compact-support assembly remain
  separate producers.
- Morgan--Tian P1c distributional-distance endpoint: not stated or proved by
  this change (0%).  This file contributes one local analytic bridge only.
- `raw_memW1p_of_lip`: formally stated, proved, focused-green, and
  named-refresh green (**100% verified-complete** as this local producer).
- Cheeger--Gromoll splitting theorem: unstated (**0%**); dedicated machinery
  remains about **35--40%** until the pending local producers verify.
- Whole P1c machinery: about **60--65%**.  Whole P0--P9 infrastructure remains
  about **15--25%**, and the final Poincare endpoint remains **0%**.

There is no known mathematical or API blocker in this file.
