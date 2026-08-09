# Palatini

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 3.  Palatini representation of the lowered difference, the perturbation-sharp endomorphism, the diagonal product-grid bounds, and the mixed Riemann bi-contraction fields.

- 2257 lines; 22 public declarations at `Integral.Connection` level, 24 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `Lowered`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le`
  - `slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace`
  - `rfns_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le`
  - `rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le`
  - `riemannMixedKernelBilin`
  - `riemannMixedKernelBilin_apply`
  - `riemannMixedSummandFib`
  - `riemannMixedSummandFib_toModel`
  - `riemannMixedBiContrFibFixedFrame`
  - `riemannMixedBiContrFibFixedFrame_toModel`
  - `mixedKernelScalar_global`
  - `riemannMixedKernelBilin_homSection_contMDiff`
  - `riemannMixedBiContrFibFixedFrame_apply_section_contMDiff`
  - `riemannMixedBiContrFibFixedFrame_contMDiff`
  - `frameRiemannMixedKernel`
  - `frameRiemannMixedKernel_apply`
  - `riemannMixedBiContrFib`
  - `riemannMixedBiContrFib_eq_fixedFrame_on_nbhd`
  - `riemannMixedBiContrFib_contMDiff`
  - `ricciArmOrder0RiemannMixedCoeff`
  - `ricciArmOrder0RiemannMixedCoeff_toSection`
  - `ricciArmOrder0RiemannMixedCoeff_self`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
