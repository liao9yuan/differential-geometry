import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Base
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.O1Alg
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.LieValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.M0Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.M0Gen1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.M0Gen2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Master
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.BoundsA
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.BoundsB
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.TameL2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.TameJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Refold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Dim1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Kernel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Envelope

/-!
# The intrinsic covariant-`L²` ball-Lipschitz bound on the DeTurck–Ricci remainder difference

This file builds the **covariant-gradient iterate `L²` core** of the smooth-ball Lipschitz
estimate for the genuine Ricci–DeTurck remainder difference — the spatial half of the existence
forcing estimate `deTurckSobolevNHa2_mixed_lipschitz` (the spectral `H^σ` translation is the
concurrently-built interior-elliptic/Gårding tower's job and is **not** attempted here —
everything stays in the `iteratedCovGrad`/`tensorL2Norm` world).

## The estimate

For `g₀`-fibre-small smooth perturbations `T, T' : SmoothCcTensor g₀ 0 2` in a covariant-`L²`
ball of radius `R` (`∑_{j ≤ a+2} ‖∇^j T‖_{L²} ≤ R`, idem `T'`), every order-`q` (`q ≤ a`)
covariant-gradient iterate `L²` norm of the genuine remainder difference

  `D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`
      `( = deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T − [same for T'] )`

obeys the **ball-uniform integrated tame bound**

  `‖∇^q D‖_{L²} ≤ C · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²})`,

with a single nonnegative constant `C` outside the `∀ T T'` quantifier (uniform over the
fibre-small radius-`R` ball).  The bound vanishes as `T − T' → 0`, so it is a genuine
Lipschitz estimate, not a static envelope.

## The intrinsic single-column route (chart-jet-free at the headline)

The sealed remainder difference splits definitionally as
`D = (RHSarm T − RHSarm T') − Δ_∇(T − T')`, where `RHSarm := deTurckRHSArmG0` carries the genuine
Ricci/Lie/inverse-Gram Nemytskii content.  The route reads **only** `iteratedCovGrad`,
`riemannianFiberNormSq` and `tensorL2Norm` at the headline:

* the order-`0` pointwise fibre-norm domination `deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform`,
  assembled from the three endpoint coefficient `C⁰` operator sups
  (`deTurckRHSArmDiff_threeArm_coeffC0_ballUniform`) and the supercritical `H^{a+2} ↪ C²` section
  embedding `deTurckArmDiff_supercritical_pointwise_jet_le`;
* the top-order-`a` integrated covariant-`L²` tame `deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform`,
  the single-column integration via `l2RootSum_of_pointwise_iteratedCovGrad_jet` of the ball-uniform
  pointwise covariant-jet column `deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform`
  (the genuine chart→intrinsic Nemytskii content, reaching the chart-Gram realize-difference bridge
  `chartDeTurckRicciRHS_realize_seminorm_le_bareChartJetContentOnE_ballUniform` only through the
  reverse fibre-norm/raw-component bridge, never an order-`(a+2)` `L^∞` cometric jet at the headline);
* the two endpoints plus the Gagliardo–Nirenberg interpolation of the intermediate orders
  (`deTurckRHSArmDiff_endpoints_l2_tame_ballUniform`, `deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform`).

The headline existence-arm wrapper `deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz` adds the
linear connection-Laplacian arm (`deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform`,
`rawTensorConnLapSmooth_iteratedCovGrad_l2_tame`); the order-`d` single-arm column form is
`deTurckRemainderDiff_iteratedCovGradSum_ballBound_order`.

## Module layout

Umbrella module.  The mathematics lives in the chunk modules
imported above; this file exists so that the module path
`DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz`
keeps re-exporting the whole API to its downstream consumers.

The monolith (46927 lines) could no longer be elaborated in a
single Lean process — the import closure alone costs 3.5 GB and
the body added a further ~0.117 GB per 1000 lines, projecting
~8.8-9.0 GB against a ~8.7 GB runway.  It was split at
section/abstraction seams, with the two geometry-free
index-algebra layers (`O1Abstract`, `M0Abstract`, 16.7k lines)
moved to modules with minimal imports so that they no longer pay
the geometric baseline at all.  Chunk map, dependency graph and
measured peaks: `DeTurckRemainderTameLipschitz.md`.
-/

