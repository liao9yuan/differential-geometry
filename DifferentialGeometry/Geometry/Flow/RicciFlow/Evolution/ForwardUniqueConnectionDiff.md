# ForwardUniqueConnectionDiff — K1 of the forward-uniqueness (Route K) campaign

Lane: `ricci_flow_forward_unique` (`ShortTime/FORWARD_UNIQUE_PLAN.md`; ruling =
`ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §5, brick K1).

## 2026-07-25 — K1 VERIFIED GREEN (first attempt)

- `christoffelEvolutionDiffInFrameOn`: two `ChristoffelEvolutionEquationInFrameOn`
  hypotheses for `S₁`, `S₂` in a COMMON local frame subtract to the
  `HasDerivWithinAt` fact for `Γ(S₁)^k_{ij} − Γ(S₂)^k_{ij}` with derivative
  `RHS₁ − RHS₂`.  Proof is exactly `(h₁ …).sub (h₂ …)` — no star-sum API, no new
  class, no wrapper assumption, as the ruling prescribed.
- `christoffelDiff_coeff`: pointwise identification of the component difference
  with `hframe.coeff k x` applied to the connection-difference vector
  `(∇¹_{e_i} e_j − ∇²_{e_i} e_j)(x)`.  Pure linearity (`map_sub` of the Mathlib
  `IsLocalFrameOn.coeff` fiberwise linear map); no `x ∈ u` hypothesis needed.
  Note: the pre-existing `connectionDiffLoweredInFrame`
  (`Evolution/Connection/Components.lean`) compares ONE solution at two times,
  not two solutions — so the identification target here is the frame
  coefficient of the two-solution difference vector directly; later bricks
  lower it with `g₁` to the `A₀₃` carrier.
- Neither ruling STOP signal fired: the two evolution hypotheses instantiate
  with a common frame as-is, and no global-frame/atlas construction was needed.
- Verification: focused check green; targeted `lake build +…ForwardUniqueConnectionDiff`
  green; `#print axioms` = exactly `[propext, Classical.choice, Quot.sound]`
  for both theorems.  (Verification passed.)

## Next (K1-corollary, NOT started)

The pointwise squared bound `|∂ₜA₀₃|²_{g₁} ≤ C(|h₀₂|² + |A₀₃|² + |∇¹S₀₄|²)`,
consuming inverse-metric difference, connection-difference-on-tensors, and
Ricci-as-curvature-trace lemmas (ruling §5 K1 tail); then K2
(`rmDiffLowered_evolution_div_bound`, the dominant brick — watch its two STOP
gates), K3 (energy differentiation).
