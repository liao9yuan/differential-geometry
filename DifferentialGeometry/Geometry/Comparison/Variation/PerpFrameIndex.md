# PerpFrameIndex

## Purpose

This module is the geometric realization bridge for the abstract negative
index-form direction used in the minimizing-implies-no-interior-conjugate
argument.  Coefficients live in `EuclideanSpace`, not the sup-norm plain
function space, so the abstract Hilbert index form has the intended sum inner
product.

## Current state

Focused verification passes without warnings.  The module now supplies:

- the finite-frame lift and the symmetric smooth curvature operator;
- smoothness, perpendicularity, endpoint, pointwise, and integrated
  index-form identifications for lifted coefficient fields;
- a pointwise expansion theorem for a complete orthonormal frame of the
  perpendicular space, including the one-dimensional empty-frame case;
- coefficient reconstruction and preservation of nonzeroness;
- the exact first-order coefficient Jacobi ODE in a parallel frame; and
- perpendicularity of a globally differentiable Jacobi field that vanishes at
  two distinct times.

The remaining geometric frontier is not a frame calculation.  It is the final
assembly: rescale a conjugate-vector variation to the original minimizing
geodesic, use the nonzero initial coefficient derivative to obtain a
nontrivial coefficient solution, feed that solution through the checked
negative smooth index-form producer, lift it through the frame, and contradict
the minimizing-geodesic index-form nonnegativity theorem.

## Project accounting

The N-d endpoint theorem remains unstated and therefore 0%.  This file is one
dedicated geometric bridge inside N-d machinery; it does not by itself prove
that a minimizing geodesic has no interior conjugate vector.  With the abstract
negative and smoothing package already complete, dedicated N-d machinery is
approximately 82--86%; Route B machinery is approximately 84--88%; the full
V1--V3 volume-comparison/CGT producer program remains approximately 48--52%.
