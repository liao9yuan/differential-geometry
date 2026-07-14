# ParametricScalarSmulJet

## Route

The scalar multiplier is represented by the rank-zero mixed coefficient
obtained by scaling the canonical rank-zero identity. Its `appCc` action is
proved equal to `scalarSmul` after full application. This lets
`smul_jet_unif` reuse `param_app_jet`, avoiding a second iterated Leibniz
calculus.

The spacetime smoothness proof cannot use ordinary `smul_section`: the family
covers `Prod.fst : M × ℝ → M`, not the identity map.  The private
`joint_rs_smul` helper instead opens the total-space smoothness criterion and
performs scalar multiplication only in a local trivialization.  This is the
same established normal form used by existing joint tensor-family producers.

## Frontier

The source theorem is stated and proved without solution-specific assumptions.
Static review repaired the model-with-corners notation to the project-standard
`𝓘`. Focused verification awaits a stable shared dependency chain; the
duplicate writer was stopped rather than extending the concurrent build queue.

Endpoint theorem: 0%. Dedicated A1 scalar-multiplier machinery: about 85%
until the focused check confirms the rank-zero action and joint-family bridge.
