# VelocityLift

## Role

This file provides the chart-independent tangent-bundle velocity lift of an ordinary geodesic.
It is a geodesic-layer bridge from the pointwise geodesic equation to the global geodesic vector
field; it does not establish raw exponential-domain coverage or the compact-ball Bishop endpoint.

## Route

On an open geodesic interval, chart regularity makes the base curve smooth. In the tangent chart
centered at the lifted point, the velocity lift is locally the phase curve consisting of the charted
base curve and its first derivative. The two derivative fields in `HasGeodesicEquationAt` therefore
give the tangent-chart derivative directly, and its algebraic equation identifies that derivative
with the global `geodesicVectorField`.

The proof reuses the existing chart-coordinate bridge for `mfderiv (1)`, the tangent-chart
decomposition of `chartPushLift`, and the open-set geodesic regularity theorem. It does not import
an Exponential module or duplicate the phase-ODE uniqueness proof from intrinsic exponential-map
continuity.

## Verification

The focused file verification passed without errors. The proof is sorry-free and introduces no
axioms. No downstream module refresh was needed because this file has no consumer yet.
