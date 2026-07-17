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

## 2026-07-16 finite varying-domain extraction

`exists_cInf_finite` is the canonical finite-family diagonal at the analysis
layer. Each member may have its own domain and may refine any already selected
strict subsequence. The proof recursively extracts one member and preserves all
earlier limits through `MapCInfConvOnCompacts.comp_tendsto_atTop`; it introduces
no HCG-specific data or extra compactness assumption.

Focused verification passed. This generic extraction API is complete. It is
supporting machinery only: the concrete `NormalMetricConv` producer and
`StepB1RawInput` remain separate downstream theorems.

The extractor also preserves an arbitrary predicate on each selected limit,
so geometric consumers retain smoothness and metric equivalence together with
convergence. Its index assumption is the minimal `Finite` instance; the proof
installs a local `Fintype`. Focused verification and the targeted refresh
passed.

## 2026-07-16 three-index tail

`MapCInfConvOnCompacts.three_tail` turns convergence along every triple of
reindexings tending to infinity into one common tail in all three indices, for
each compact core, finite derivative order, and positive tolerance.  Its proof
is the direct bad-triple diagonal argument, so it adds no smoothness or
geometry assumption.  Focused verification passed.

This closes the generic quantifier-order brick needed by the moving-reference
center route.  It does not itself construct the HCG center family or the
`StepB1RawInput` producer; those theorem endpoints remain 0%.
