# Moving-frame genuine-field fibre energy

## 2026-08-05: supplied curvature-cap trace bound

`genuineTrace_le_of` is the public structural form of the existing pure-Riemann moving-frame trace
estimate. Given a supplied rank-`s` tensor-curvature coefficient `C ≥ 0`, it proves the trace bound
with coefficient

```text
(finrank ℝ E) * ((finrank ℝ E) * C).
```

The proof is the previously checked moving-frame/Parseval argument; the compactness-based
existential theorem now chooses its uniform coefficient and delegates to this supplied-cap form.
No new analytic frontier or alternate tensor API was introduced.

The focused check and direct upstream-module refresh both passed. `genuineTrace_le_of` is therefore
confirmed complete (100%) as a structural leaf. It is only one lower producer for the rank-two
`p = 0` curvature-action endpoint; that endpoint is tracked separately and remains unconfirmed until
its own focused check passes. The overall `(N)` uniform-existence theorem remains 0% proved.
