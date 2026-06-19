# Lemma45F4.lean — MSM135 Corollary II endpoint (`lemma45_corII`, F4)

The book-facing F4 endpoint that F5/F6/Step B consume: Cor II with the intrinsic
Lemma I `hF3` **discharged from the approximate-isometry data**, so consumers
need no `hF3` hypothesis. Stated 2026-06-11; elaborates green with ONE expected
`sorry`.

## The narrow `sorry` (honest, mechanical — NOT new mathematics)

The real math is done and green elsewhere:
- `lemma45_F3` (Lemma45Engine) — Lemma I, component `compL2` form;
- `compL2_tower_eq_gen` + `hF3_term` (Lemma45Intrinsic) — the intrinsic lift (the
  former frontier);
- `lemma45_cor_II_of_intrinsic` (Lemma45Covariant) — Cor II from `hF3`.

The `sorry` is the assembly: produce a g-ON frame at each `x ∈ u` (apply
`exists_goodFrame_compBound` with `gRef := g`), discharge `lemma45_F3`'s per-frame
inputs, ∃-collect `hF3_term` into `hF3`, feed `lemma45_cor_II_of_intrinsic`.
Deferred while the good-frame producer (`RicBoundGoodFrame.lean`) is finalized in
the parallel ric_bound track (it was dirty/uncommitted at the time of writing).

## Statement (consumers depend only on this)

`lemma45_corII (hu) (g gRef) (T : Tensor0SField q₂) (p eps) (heps0 heps1)
  (hequiv : C⁻¹gRef ≤ g ≤ CgRef on u, C = 1+eps)
  (hgK : √normSq0S gRef (∇_gRef^j g) ≤ eps, 1≤j≤p, on u)
  : ∃ Cc ≥ 0, ∀ x ∈ u, ∀ 0 < r ≤ p,
     √normSq0S g (∇_g^r T) ≤ √((1+eps)^{q₂+r})·(√normSq0S gRef (∇_gRef^r T) +
        eps·Cc·Σ_{k<r} √normSq0S gRef (∇_gRef^k T))`.

Imports only `MetricCovDerivLinear` + `Comparison` (committed); the discharge will
add `Lemma45Covariant` + `Lemma45Intrinsic` + `RicBoundGoodFrame`.

## What consumes it: F5 (Composition I, C^p)

Same-domain, three metrics on a common domain. Apply `lemma45_corII` with
`g:=g₀, gRef:=g₁, T:=g₂−g₁`; triangle through `g₁`; the lower-order terms via the
approx data + `compEpsAccum` (ApproxIsometryComp, green). Pieces present:
`sqrt_normSq0S_add_le` (fiber Minkowski, basis form), `iterCov_add`.
**Confirmed: F5/F6 need only F4, not the absent map-level pullback-naturality**
(the project is same-domain throughout, so Cor II applies directly to the metric
difference — no `Φ*`-of-tensor, no `∇_{Φ*h}(Φ*T)=Φ*(∇_h T)`).
