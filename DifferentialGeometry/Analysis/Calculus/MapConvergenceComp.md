# MapConvergenceComp

## 2026-07-15 canonical placement

The generic moving-composition theorem and fixed constant/product/finite-Pi/CLM
closures now live in the analysis calculus layer. The new
`MapCInfConvOnCompacts.ringInv` composes convergence with smooth Banach-algebra
inversion on the open unit locus; it introduces no metric-specific input.

Focused verification passed, and the old HCG import path remains a checked
compatibility module. A proposed fully generic bilinear closure was discarded
after it caused unnecessary elaboration cost; the spray proof instead composes
the existing APIs at concrete finite-dimensional types.
