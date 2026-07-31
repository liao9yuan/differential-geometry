# LowRegLiftHfLo

## Status (2026-07-30)

GREEN and placeholder-free.  The module contains the exact low affine split
used by `lowreg_lift_two`.

The second-order family `lowAffA2` and first-order family `lowAffA1` retain the
same radial maps as `lowBaseA`.  Their self-application therefore equals the
zero-based low action without adding a second principal arm.

The operator packets are now internal:

- `lowAffA2_data` supplies strong measurability and an `NNReal` pointwise
  operator bound from the banked continuous uniformly bounded completed A2
  coefficient.
- `lowAffA1_data` supplies strong measurability, `MemLp`, and a uniform
  pointwise M-bound along an a.e. bounded `H3` Duhamel trajectory.
- `lowreg_hfLo_data` combines both packets with the exact fixed-point identity,
  on one radius aligned with the D4-free first-order pair producer.

The first-order packet deliberately does not use the false global affine
envelope.  Its honest extra input is a pointwise `H3` trajectory bound; the
ball-local coefficient bound then gives `MemLp` on the finite time interval.

Focused and exact verification passed.  No `sorry`, `admit`, `axiom`, `whnf`,
or trace declaration remains.

## Project position

`ricci_flow_unif_existence` itself remains unstated here and 0% complete at its
endpoint placeholder.  This closes the D4-free low first-order/hfLo/M-witness
brick; dedicated uniform-existence machinery is approximately 78%.  The next
mathematical frontier is the field-level Palatini difference identity feeding
the `a = 1` envelope and class-uniform `Ksup` at `j = 1`.

