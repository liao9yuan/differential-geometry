/-
The second isolated open analytic input of the Ricci-flow short-time-existence
development: the quasilinear-parabolicity / Gårding frontier for the genuine
geometric Ricci–DeTurck remainder.

This file holds two declarations:

* a fully proven bridge `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`
  identifying the symmetric bilinear form extracted from the smooth tensor
  section `deTurckRHSSection g_bg g` with the Ricci–DeTurck right-hand side
  `deTurckRicciRHS g_bg g` (relying on the symmetry of the latter, proved here as
  `deTurckRicciRHS_symm`); and

* the single deferred classical input `deturck_geometric_nonlinearity_hscale_lipschitz`
  — the local Lipschitz estimate, on the carrier Sobolev scale `H^{a+1} → Hᵃ`, of
  the GENUINE geometric DeTurck remainder section
  `deTurckRemainderSection g_bg · = deTurckRHSSection g_bg (g_bg + h(·)) − Δ_∇ T_·`
  (the `deTurckRHSSection`-based remainder, NOT the finite-support-gated
  `deTurckGeometricN`).  This is the analytic Gårding / quasilinear-parabolicity
  input (heat-kernel parametrix / coercive principal-part estimate) that is not
  present in Mathlib; it is the companion of the local Weyl law
  `local_weyl_eigenvalue_counting_bound`.
-/
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Symmetry of the Ricci–DeTurck right-hand side

`deTurckRicciRHS g_bg g = −2 · Ric(g) + 𝓛_{W(g, g_bg)} g` is a sum of two
*symmetric* `(0,2)`-tensors: the Ricci tensor is symmetric (`ricciTensor_symm`)
and the metric Lie derivative is symmetric (`lieDerivMetric_isPointwiseSymm`),
the latter being the genuine `(0,2)`-tensor symmetry of `𝓛_W g`. -/

/-- **The Ricci–DeTurck right-hand side is a symmetric bilinear form:**
`deTurckRicciRHS g_bg g x v w = deTurckRicciRHS g_bg g x w v`. -/
theorem deTurckRicciRHS_symm
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w =
      deTurckRicciRHS (I := I) g_bg g x w v := by
  -- Unfold `deTurckRicciRHS` into its two summands and distribute the
  -- continuous-linear sum/scalar applications over both tangent slots; the
  -- `lieDerivMetricClm` upgrade is read off by `lieDerivMetricClm_apply`.
  simp only [deTurckRicciRHS, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lieDerivMetricClm_apply]
  -- The Ricci summand is symmetric by `ricciTensor_symm`; the Lie-derivative
  -- summand is symmetric by `lieDerivMetric_isPointwiseSymm`.
  rw [ricciTensor_symm (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w,
    DeTurck.lieDerivMetric_isPointwiseSymm (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (DeTurck.deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w]

/-! ## The symmetric bilinear extraction of the Ricci–DeTurck section

The smooth `(0,2)`-tensor section `deTurckRHSSection g_bg g` was built so that its
model value recovers the Ricci–DeTurck bilinear form
(`deTurckRHSSection_toModel_apply`).  The symmetric bilinear form extracted from
that section (`ccTensorBilinSymm`) therefore agrees with `deTurckRicciRHS g_bg g`,
the symmetrization being a no-op because `deTurckRicciRHS` is already symmetric. -/

/-- The Ricci–DeTurck section `deTurckRHSSection g_bg g`, re-tagged from the
type-level metric tag `g` to the background tag `g_bg`.  The metric tag is a pure
type-level parameter (it does not appear in the carrier data, see `SmoothCcTensor`
in `Integral/L2/SmoothSections/Defs.lean`), so the underlying smooth section is
unchanged. -/
noncomputable def deTurckRHSSectionBg (g_bg g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2 where
  toSection := (deTurckRHSSection (I := I) g_bg g).toSection
  hasCompactSupport := (deTurckRHSSection (I := I) g_bg g).hasCompactSupport

@[simp] theorem deTurckRHSSectionBg_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSectionBg (I := I) g_bg g).toSection =
      (deTurckRHSSection (I := I) g_bg g).toSection := rfl

/-- The model value of the re-tagged Ricci–DeTurck section recovers
`deTurckRicciRHS g_bg g` (transported from `deTurckRHSSection_toModel_apply`
through the `rfl`-identical underlying section). -/
theorem deTurckRHSSectionBg_toModel_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((deTurckRHSSectionBg (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSSection_toModel_apply (I := I) g_bg g x v

/-- **The extracted symmetric bilinear form of the Ricci–DeTurck section is the
Ricci–DeTurck right-hand side.**  Evaluating `ccTensorBilinSymm` on the smooth
tensor section `deTurckRHSSection g_bg g` (re-tagged to `g_bg`) reproduces
`deTurckRicciRHS g_bg g` pointwise: the model value of the section recovers
`deTurckRicciRHS` (`deTurckRHSSection_toModel_apply`), and the symmetrization is a
no-op since `deTurckRicciRHS` is symmetric (`deTurckRicciRHS_symm`). -/
theorem deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g_bg (deTurckRHSSectionBg (I := I) g_bg g) x v w =
      deTurckRicciRHS (I := I) g_bg g x v w := by
  -- `ccTensorBilinSymm = ½ (B v w + B w v)` with `B = ccTensorBilin`.
  rw [ccTensorBilinSymm_apply]
  -- `ccTensorBilin T x v w = ccTensorModel T x ![v, w] = toModel (T.toSection x …) ![v, w]`.
  rw [ccTensorBilin_apply, ccTensorBilin_apply]
  unfold ccTensorModel
  rw [ccTensorMultilinear_apply]
  -- The model value of the Ricci–DeTurck section recovers `deTurckRicciRHS`.
  rw [deTurckRHSSectionBg_toModel_apply, deTurckRHSSectionBg_toModel_apply]
  -- `![v, w] 0 = v`, `![v, w] 1 = w` (and the swapped pair); the symmetrization
  -- collapses by `deTurckRicciRHS_symm`.
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [deTurckRicciRHS_symm (I := I) g_bg g x w v]
  ring

/-! ## The deferred quasilinear-parabolicity / Gårding input

The maximal-regularity engine `deTurckRemainder_strong_shortTime_exists`
(`DeTurckRemainderStrongExists.lean`) consumes a locally Lipschitz lower-order
nonlinearity `N : H^{a+1} → Hᵃ` in the form of a `LipschitzOnWith` bound on a
closed `H^{a+1}`-ball about the included initial datum.  For the GENUINE geometric
Ricci–DeTurck nonlinearity the eigenbasis coordinates of `N(u)` are the `L²`
coordinates of the remainder section

  `deTurckRemainderSection g_bg u
     = deTurckRHSSection g_bg (g_bg + h_sym(u)) − rawTensorConnLapSmooth g_bg 0 2 T_u`,

so the Lipschitz bound on `N` is, per mode, the weighted square-summable estimate
on the coordinate differences of that section — exactly the shape established for
the continuous realize-anchored nonlinearity in `deturckN_hscale_lipschitz`'s
`hNsec_lip` hypothesis, but now for the `deTurckRHSSection`-based remainder
section itself.  Establishing this estimate is the classical
quasilinear-parabolicity / Gårding coercivity of the gauge-cancelled DeTurck
operator (heat-kernel parametrix / principal-part match with the rough
Laplacian); it is not present in Mathlib.

This is the SECOND deferred classical input, the companion of the local Weyl law
`local_weyl_eigenvalue_counting_bound`. -/

/-- **THE single deferred quasilinear-parabolicity / Gårding input** — the local
Lipschitz estimate, on the carrier spectral Sobolev scale `H^{a+1} → Hᵃ`, of the
GENUINE geometric Ricci–DeTurck remainder section `deTurckRemainderSection g_bg ·`
(the `deTurckRHSSection`-based remainder, NOT the finite-support-gated
`deTurckGeometricN`).

Stated in the precise weighted per-mode form consumed by the engine
`deTurckRemainder_strong_shortTime_exists`: there is a Lipschitz constant `K` and a
positive radius `R` so that on the closed `H^{a+1}`-ball about the included initial
datum `u₀`, the weighted `ℓ²` sum of the squared eigenbasis-coordinate differences
of the remainder section's `L²` image is dominated by `(K · dist u u')²`.  This is
the order-2 Gårding coercivity / principal-part match of the gauge-cancelled
DeTurck operator with the rough Laplacian, a classical theorem (heat-kernel
parametrix) NOT present in Mathlib; it is the ONLY analytic `sorry` on the
short-time-existence graph besides the local Weyl law
`local_weyl_eigenvalue_counting_bound`, and is its direct companion. -/
theorem deturck_geometric_nonlinearity_hscale_lipschitz
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) :
    ∃ (K : ℝ≥0) (R : ℝ), 0 < R ∧
      ∀ u u' : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
        u ∈ Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R →
        u' ∈ Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R →
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2 =>
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g_bg 0 2)
                  (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)
                    - SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u')) i) ^ 2)
          ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g_bg 0 2,
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
                (tensorL2Coeff_ofCompact (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g_bg 0 2)
                    (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)
                      - SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u')) i) ^ 2)
              ≤ ((K : ℝ) * dist u u') ^ 2 := sorry

end DifferentialGeometry.PDE.RicciFlow
