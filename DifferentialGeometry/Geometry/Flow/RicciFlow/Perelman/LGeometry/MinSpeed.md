# Minimizing L-ray speed identity

## Status

`lMinSpeed_eq` is the canonical positive-time identity for the ordinary
L-exponential ray.  It combines `IsLMinVec` cost realization,
`lLength_sqrt`, `redLength_mul`, `lK_ray_energy`, and `lExp_vel_sqrt`; it
uses no curvature-sign or Harnack assumption.

Focused verification is GREEN.  Its axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; the declaration adds no `sorry`,
`admit`, or project axiom.

The identity itself is 100% complete.  It is one reusable producer in the
P2b reduced-geometry package, whose umbrella theorem remains unstated at 0%
while its dedicated machinery is roughly 64--68%.  Compact ordinary-flow P2a,
including `smooth_nlc`, remains closed at 100%.  The Harnack sign estimate that
turns this identity into the ancient scale-sharp speed bound belongs to P3.
