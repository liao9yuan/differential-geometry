# Homogeneous

## Goal

This module is the compact-free witness-native Euclidean H2 producer for local
homogeneous De Giorgi solutions whose principal coefficient agrees near the
cutoff with a positive multiple of a smooth global coefficient.

## Native route

1. `homSol_dq_bound` calls `hom_master_nonsmooth`; the resulting whole-space
   witness is allowed to depend on the chosen difference-quotient direction.
2. The outer domain is `thickening (R0 + 1) (tsupport eta)`. The nonsmooth
   Friedrichs-Korn estimate and `stdTest_sq_bound` discharge the two analytic
   inputs to the quantitative master inequality. `dq_norm_of_sum` converts its
   integral sum bound to a component `L2` seminorm bound.
3. Pointwise agreement of the global and local weak gradients throughout the
   closed translation room transports the difference quotient back to the
   fixed local witness on `V`.
4. `homSol_second` applies the local difference-quotient weak-limit theorem.
5. `homSol_memW2` restricts the original witness to `V`, proves each displayed
   gradient component lies in `W1,2(V)`, and applies `MemWkp.two_of_wit`.

## Current status

All three public endpoints are source-written and warning-free under focused
verification, with no additional compatibility assumptions or frontier
predicates. The targeted named module refresh also passed. The earlier missing
`StandardTestSquareBound` object was refreshed upstream and is no longer a
blocker.

## Progress

The three theorem endpoints are 100% source-written and verified, and their
dedicated producer machinery is 100% complete at this module boundary. This
closes the homogeneous Euclidean H2 producer phase. It is one layer of the
broader P1c H2 chain; downstream comparison-theorem assembly is not implemented
by this module, so this result does not change that separate endpoint's own
completion percentage.
