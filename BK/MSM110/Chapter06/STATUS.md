# MSM110 Chapter 6.1 Status

Source: `C:/Users/liao9/Downloads/MSM110_clean01.tex`, Chapter 6,
Section 1, "The evolution of curvature under the Ricci flow".

## Ricci-Flow Evolution Equations

| LaTeX label | BK wrapper | Canonical RicciFlower theorem | Status |
| --- | --- | --- | --- |
| Ricci-flow inverse metric specialization | `BK.MSM110.Chapter06.Section01.eq_inverse_metric_ricci_flow` | `RicciFlower.RicciFlow.evol_inverse_metric_inFrame` | Proved in fixed-frame component form from the inverse-metric component regularity package. |
| `eq:christoffel_symbols_ricci_flow` | `BK.MSM110.Chapter06.Section01.eq_christoffel_symbols_ricci_flow` | `RicciFlower.RicciFlow.evol_christoffel_inFrame` | Proved in fixed-frame component form from spacetime-smooth metric components and the Ricci-flow metric equation. |
| `eq:riemann_curvature_three_one_ricci_flow_one` | `BK.MSM110.Chapter06.Section01.eq_riemann_curvature_three_one_ricci_flow_one_local` | `RicciFlower.RicciFlow.riemann13VariationFormulaInFrameOnLocal_of_christoffelEvolution` | Partially covered: local coordinate-frame producer on `{x0}`, with explicit fixed-base mixed-derivative regularity. The global display equation remains a frontier. |
| `eq:ricci_tensor_ricci_flow_one` | `BK.MSM110.Chapter06.Section01.eq_ricci_tensor_ricci_flow_one_local_from_christoffel` | `RicciFlower.RicciFlow.ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution` | Local coordinate-frame Ricci variation is now composed from Christoffel evolution and the local Riemann trace. |
| `eq:ricci_tensor_ricci_flow_two` | `BK.MSM110.Chapter06.Section01.eq_ricci_tensor_ricci_flow_two_local` and `BK.MSM110.Chapter06.Section01.eq_ricci_tensor_ricci_flow_two` | `RicciFlower.RicciFlow.ricciEvolutionEquationInFrameOnLocal_of_variation_commutators` and `RicciFlower.RicciFlow.evol_ricci_inFrame_of_variation_commutators` | Proved in local and global fixed-frame component forms, assuming the Ricci variation formula and contracted commutator reduction. |
| `eq:scalar_curvature_ricci_flow_one` | input hypothesis to `BK.MSM110.Chapter06.Section01.eq_scalar_curv_evolu` | `RicciFlower.RicciFlow.ScalarPreBianchiEvolutionEquationOn` | Recorded as the pre-Bianchi scalar evolution interface. |
| scalar contracted-Bianchi algebra | `BK.MSM110.Chapter06.Section01.scalar_contracted_bianchi_reduction` | `RicciFlower.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi` | Proves the algebraic reduction from the second-derivative contracted-Bianchi trace `Q = (1/2) ΔR`. |
| `eq:scalar_curv_evolu` | `BK.MSM110.Chapter06.Section01.eq_scalar_curv_evolu` | `RicciFlower.RicciFlow.msm110_ch6_1_scalar_curvature_evolution` | Proved from the pre-Bianchi scalar evolution plus the contracted-Bianchi reduction. |
| `eq:evolution_of_volume_element` | `BK.MSM110.Chapter06.Section01.eq_evolution_of_volume_element_integrated` and `BK.MSM110.Chapter06.Section01.total_volume_evolution_ricci_flow` | `RicciFlower.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar` and `RicciFlower.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv` | Proved in the current measure-integrated API. This is not yet a literal pointwise density theorem. |

## Deferred Frontiers

- Deriving the scalar second-derivative contracted-Bianchi trace from the current realized Bianchi API.
- Proving the full `RicciContractedCommutatorsInFrame` package from the realized commutator/Bianchi API.
- Proving the global Riemann `(3,1)` display equation with the MSM110 sign and slot conventions.
- Deriving fixed-base Christoffel mixed-derivative regularity from manifold-level spacetime smoothness.
- Deriving the three-dimensional Ricci reaction formula from the Riemann decomposition.
- Applying tensor maximum principles to Ricci positivity.
