# PointedConvergence

## Role

This module is the fixed-curve, smooth pointed-flow assembly layer for
book12's reduced-action convergence input.  It does not address varying
minimizers, reduced-distance convergence, Gaussian tightness, or surgery.

## Native route

`ConvOut.mapKin_convOn` combines the extended-metric producer
`ConvOut.kinetic_convOn` with compact exhaustion.  On the eventual growing
compact set the bump is one, so `gSeqExt_inner_of_mem` reduces the extended
metric to `srcMetric`; `lKinetic_map` then identifies that source kinetic form
with the kinetic form of the actually transported curve.

No global curve into a varying source subtype is required, and no new
reference-speed or curvature hypothesis is introduced.

`lLength_conv_curve` adds the scalar producer, common compact confinement,
the transported kinetic producer, local density measurability, and the
dominated-convergence adapter.  Its curve is fixed and `C¹`; the time interval
is compact and mapped into the common regular slab.  The limit metric is
identified explicitly with `ConvOut.gInf` on that slab.

## Verification

`ConvOut.mapKin_convOn` and `lLength_conv_curve` are warning-free focused green.
The module's named refresh is current, and both declarations are included in
the unified P2 axiom audit.  They depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The assembly check exposed one local instance boundary: `Phi` targets
`L.atTime 0`, while the limit solution is stored on `L.M`.  The proof installs
both records' definitionally equal stored manifold instances explicitly and
uses direct subsequence indices; no new instance or stronger public hypothesis
was introduced.

This is 100% completion of the fixed `C¹` curve action-convergence endpoint.
It is not the book's full varying-minimizer, reduced-distance, Gaussian-tail,
or no-mass-loss theorem; those endpoints remain unstated and 0%.
