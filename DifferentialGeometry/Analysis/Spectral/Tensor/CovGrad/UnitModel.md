# UnitModel

## Purpose

This module is the low-level home of `unitTensor` and `unitModel`, the
canonical unit evaluation used throughout the intrinsic tensor readout API.

## Status

The declarations were moved unchanged from
`CovGradSlotPermutationNaturality.lean`.  The split removes the slot
permutation, metric-compatibility, and Laplacian dependency chain from
consumers that only need unit evaluation.  Focused verification passes without
warnings.  The narrow artifact refresh is pending while another lane's
targeted build is active.
