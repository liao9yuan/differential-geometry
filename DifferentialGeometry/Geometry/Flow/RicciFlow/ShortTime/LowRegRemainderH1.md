# Low-regularity Ricci--DeTurck remainder

## Verified result

- `rem_h0_lip` subtracts the fixed background connection Laplacian from the
  Ricci--DeTurck RHS difference and proves a uniform spectral `H2 -> H0` bound.
- Its focused verification passes without local warnings or sorries.

## Mixed estimate assembly

Route A is now the canonical route. `RHSPathIntegral.rhsArm_sub_eq_paths`
provides the exact full Ricci+DeTurck three-arm identity, while
`LowRegPathSplit.top_path_ball_h1` gives the small top arm and
`LowRegPathLower.lower_coeff_h1` controls the lower two arms.

`rem_h1_of_bounds` has been written as the final Sobolev assembly theorem. It
assumes only the natural concrete bounds on `rhsLow0PathIntegral` and
`rhsLow1PathIntegral`: pointwise plus one covariant derivative for the
zero-order coefficient, and pointwise plus the covariant jet through order two
for the one-order coefficient. Its conclusion is

`Ctop * R * ||T-T'||_H3 + (Clow + Ccoef * (B0+B0'+B1)) * ||T-T'||_H2`.

Thus the only coefficient multiplying the `H3` difference is the small
spectral `H2` ball radius. No high Sobolev order or high-`a` hypothesis appears.

The theorem source is not yet counted as complete: its focused check is
waiting on the active named upstream refresh for the new path/cancellation
import chain. Until that check passes, `rem_h1_of_bounds` remains theorem-level
0% despite the complete proof term in the source.

## Remaining producer

The single analytic frontier is to derive the four concrete lower-path bounds
uniformly from the low-regularity metric data. Using the existing generic
path-integral transfer API, it is enough to prove along `realizedFam`:

1. a uniform pointwise and order-one covariant `L2` bound for `rhsLow0Coeff`;
2. a uniform pointwise and order-two covariant `L2` jet bound for
   `rhsLow1Coeff`.

The existing public coefficient estimates with
`a >= 2 * dim + 10` cannot close this frontier. The low-regularity producer
must instead use the dimension-three `C3`/`LowRegCoeff` Gram and ellipticity
bounds, inherited along the convex realized metric segment. Once those family
bounds exist, `riemannianFiberNormSq_pathIntegralCoeffField_le_sq` and
`path_jetL2_le` transfer them to exactly the hypotheses of
`rem_h1_of_bounds`.

A later routine adapter must identify a metric deviation
`metricDifferenceCcTensor gBase g` with its realized metric and discharge
symmetry/fibre-smallness from the local `H2` ball. This is not the analytic
frontier and should not be mixed into the coefficient proof.

## Honest accounting

- `rem_h0_lip`: theorem 100%.
- `rem_h1_of_bounds`: source proof written, theorem 0% until focused
  verification; dedicated assembly machinery approximately 98%.
- Unconditional mixed `H3 -> H1` estimate from `IsLowRegCoeff`: theorem not
  stated/proved, 0%; dedicated machinery approximately 84%.
- Uniform low-regularity Ricci--DeTurck existence theorem: not stated/proved,
  0%; dedicated machinery approximately 45%.
- Whole HCG machinery remains approximately 60%; endpoint compactness
  theorems remain 0% until stated and proved.
