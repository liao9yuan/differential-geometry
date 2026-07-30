# Stage inverse-velocity convergence

## 2026-07-29 provider-neutral replay

`invVelSub_conv_on` now consumes `MetricCompactCore`, which is the actual data
used by the provider-native H6 route. The legacy `invVelSub_conv` wrapper
passes `inp.toCore` explicitly and preserves its public call shape.

Focused and exact verification are GREEN (`4124/4124`). This is a consumer
interface migration, not a new inverse-velocity assumption.
