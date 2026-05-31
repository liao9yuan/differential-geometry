/-
Proven bridge material relating the smooth Ricci–DeTurck section to the
Ricci–DeTurck right-hand side.

This file holds two fully proven declarations:

* `deTurckRicciRHS_symm` — the Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg g`
  is a symmetric bilinear form; and
* `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS` — the symmetric bilinear
  form extracted (via `ccTensorBilinSymm`) from the smooth tensor section
  `deTurckRHSSection g_bg g` equals `deTurckRicciRHS g_bg g`.

(A quasilinear-parabolicity / Gårding Lipschitz `sorry` for the geometric remainder
previously lived here; it was removed because every faithful, non-vacuous form of the
*whole-ball* Lipschitz estimate requires realizing arbitrary `H^{a+1}`-ball elements as
genuine smooth metrics — the chart-free order-2 elliptic-regularity gate, a separate
open sub-program rather than a standalone classical input.  The route-agnostic crux
`deturck_ricci_flow_parabolic_short_time_existence` does not transit it and is best discharged by the
classical maximal-regularity approach, which does not use this estimate.)
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

end DifferentialGeometry.PDE.RicciFlow
