import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCovSumCross

/-!
# The class-uniform zero-state forcing bound (item-6 brick E6)

`lowreg_partial_sol_of_bounds` (`ShortTime/UnifClassBounds.lean`) drives the order-one
low-regularity Ricci--DeTurck solve by six numbers, of which `D` is the size of the
nonlinearity at the zero state:

```
hzero : ‖lowregNfun g₀ g_bg … ⟨0, _⟩‖ ≤ D
```

the norm being the spectral `H¹(g₀)` norm of `tensorHs g₀ 0 2 ((1 : ℕ) : ℝ)`.  For a single
metric `D` is *defined* to be that norm (`LowRegDenseSolve.lean`), which is useless for a
class-level horizon floor.  This file replaces it by a closed number.

## What `N(0)` actually is

`lowRegN` is the dense extension of `coreN`, and the zero state lies in the smooth core, so
`N(0) = coreN 0 = deTurckSmoothN g₀ g_bg 1 0`.  At the zero perturbation the realized metric
is `g₀` itself and the connection Laplacian of `0` vanishes, so the genuine remainder collapses
to the **static** Ricci--DeTurck field

```
deTurckSmoothRemainder g₀ g_bg 0 = deTurckRHSSection g_bg g₀
```

(`deTurckRem_zero`): Ricci of `g₀` plus the `g_bg`-DeTurck vector-field term, with **no**
Laplacian and **no** third metric.  This is where the ratified instantiation `g_bg := gBase`
matters: only the two metrics `g₀` and `gBase` of the `Λ`-class enter `N(0)`.

## The bound

The private curvature-free identity `hsOne_sq`, obtained directly from
`rawIter_tsum` and `covIter_tsum` at the empty rough-Laplacian iterate, identifies
the spectral `H¹` norm squared with the sum of the squared `L²` norms of the zero-
and one-jets.  Thus the `H¹` norm is bounded by the covariant `1`-jet sum without
invoking the all-order Bochner curvature hypothesis.  Each jet is then converted from a fibre sup bound
to an `L²(g₀)` norm (`smoothCc_norm_le_of_fibreSq`) and the `g₀`-volume is compared with the
`gBase`-volume by `volumeMeasure_cross_le` (`volReal_cross_le`, factor `√(Λ^n)`).  The result
is the closed

```
nZeroC Ksup Λ volBase n = √2 · (2 · (Ksup · √(√(Λ^n) · volBase)))
```

with `volBase` the total `gBase`-volume, `Λ` the comparability constant and `n = finrank ℝ E`.

## Parameterized inputs (flagged)

* `Ksup` — the pointwise bound on the fibre norms of `∇^{g₀,j}(deTurckRHSSection gBase g₀)`
  for `j ≤ 1`.  This is the *static* geometric input: curvature of `g₀` and one covariant
  derivative of the connection-difference/DeTurck vector field, all `Λ`-class data.  It is
  brick E3's (order `≤ 1`) output and is taken here as an explicit hypothesis, exactly as
  `H2PointwiseUnif.lean` takes the fibre-Morrey constant `Cpt`.  Metric jets of order `≤ 3`
  suffice for it (Riemann costs two metric derivatives, `∇Riemann` one more), well inside the
  `a ≤ 6` budget of brick E0.
* `hcore` — continuity of `coreN`, produced alongside `Ctop, B0, B1, ρ` by `lowRegN_outer`.

## Main statements

* `smoothCc_norm_le_of_fibreSq` — `L²` from a uniform fibre bound on a closed manifold.
* `volReal_cross_le` — real-valued total-volume comparison of `Λ`-comparable metrics.
* `deTurckRem_zero` / `nZero_eq_static` — `N(0)` is the static field `deTurckRHSSection g_bg g₀`.
* `nZeroC` — the closed constant.
* `staticN_h1_le` — the `H¹(g₀)` bound on the static field.
* `nZero_unif` / `nZero_lowregNfun` — the `hzero` slot of `lowreg_partial_sol_of_bounds`,
  discharged by `nZeroC`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### `L²` from a uniform fibre bound

The canonical home of this lemma is the `L²` smooth-section layer
(`Analysis/Integration/L2/SmoothSections/`); it is kept here to avoid invalidating that
low-level module while other lanes build. -/

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **`L²` norm from a uniform fibre bound on a closed manifold.**  A smooth compactly
supported tensor whose Riemannian fibre norm is everywhere `≤ K` has `L²(g)` norm at most
`K · √(vol_g M)`. -/
theorem smoothCc_norm_le_of_fibreSq (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {K : ℝ} (hK : 0 ≤ K)
    (hS : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) ≤ K ^ 2) :
    ‖S‖ ≤ K *
      Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hvol : 0 ≤ (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ :=
    ENNReal.toReal_nonneg
  have hsq : ‖S‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [SmoothCcTensor.norm_def S]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s
      (fun x => S.toSection x)
  have hint : ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ * K ^ 2 := by
    have hle := MeasureTheory.integral_mono_of_nonneg
      (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (f := fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))
      (g := fun _ : M => K ^ 2)
      (Filter.Eventually.of_forall
        (fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _))
      (MeasureTheory.integrable_const _)
      (Filter.Eventually.of_forall hS)
    simpa only [MeasureTheory.integral_const, smul_eq_mul] using hle
  have hfinal : ‖S‖ ^ 2 ≤
      (K * Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ)) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt hvol, mul_comm (K ^ 2)]
    exact hint
  have hsqrt := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (norm_nonneg S),
    Real.sqrt_sq (mul_nonneg hK (Real.sqrt_nonneg _))] at hsqrt

/-! ### Total-volume comparison -/

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **Real-valued total-volume comparison.**  The `ℝ`-valued face of `volumeMeasure_cross_le`
on a closed manifold: `Λ`-comparable metrics have total volumes within `√(Λ^n)`. -/
theorem volReal_cross_le (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ) :
    (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ ≤
      Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) gBase) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) gBase
  have hmeas := (volumeMeasure_cross_le (I := I) (M := M) gBase g₀ hEq).1
  have hpt := Measure.le_iff'.mp hmeas Set.univ
  rw [Measure.smul_apply, smul_eq_mul] at hpt
  have hne : ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) *
      (riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have htoReal := ENNReal.toReal_mono hne hpt
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at htoReal
  exact htoReal

/-! ### The zero state and the static Ricci--DeTurck field -/

/-- The spectral embedding of the zero smooth tensor is zero. -/
theorem smoothCcToTensorHs_zero (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  have h := smoothCcToTensorHs_sub (I := I) (M := M) g₀ σ
    (0 : SmoothCcTensor g₀ 0 2) (0 : SmoothCcTensor g₀ 0 2)
  rwa [sub_self, sub_self] at h

/-- The zero state belongs to the smooth core of every state ball. -/
theorem zero_mem_smoothCore (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R) :
    (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) ∈
      smoothCore (I := I) (M := M) g₀ R := by
  change (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) ∈
    Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2))
  exact ⟨0, smoothCcToTensorHs_zero (I := I) (M := M) g₀ _⟩

/-- The realized metric of the zero perturbation is the base metric itself. -/
theorem realizeMetric_zero (g₀ : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : δ < 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    tensorSectionRealizeMetric (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) hδ hb = g₀ := by
  refine smoothRiemannianMetric_ext_inner (fun x v w => ?_)
  rw [tensorSectionRealizeMetric_inner, ccTensorBilinSymm_apply,
    ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  ring

/-- The bundled connection Laplacian kills the zero tensor. -/
theorem rawTensorConnLapSmooth_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s
    (0 : SmoothCcTensor g r s) (0 : SmoothCcTensor g r s)
  rwa [sub_self, sub_self] at h

/-- **The Ricci--DeTurck remainder at the zero perturbation is the static field.**

At `T = 0` the realized metric is `g₀` and the connection Laplacian vanishes, so the genuine
smooth remainder is exactly the Ricci--DeTurck right-hand side of `g₀` against the background
`g_bg` — a curvature-order object with no Laplacian and no third metric. -/
theorem deTurckRem_zero (g₀ g_bg : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : δ < 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ hb =
      deTurckRHSSection (I := I) g_bg g₀ := by
  have hg := realizeMetric_zero (I := I) (M := M) g₀ hδ hb
  have hlap :
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2)).toSection = 0 := by
    rw [rawTensorConnLapSmooth_zero]
    rfl
  refine SmoothCcTensor.ext ?_
  change
    (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)
          hδ hb)).toSection -
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2)).toSection =
    (deTurckRHSSection (I := I) g_bg g₀).toSection
  rw [hlap, sub_zero]
  exact congrArg
    (fun h : SmoothRiemannianMetric I M => (deTurckRHSSection (I := I) g_bg h).toSection) hg

/-- The smooth nonlinearity at the zero perturbation is the spectral embedding of the static
Ricci--DeTurck field. -/
theorem deTurckSmoothN_zero (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {δ : ℝ}
    (hδ : δ < 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a (0 : SmoothCcTensor g₀ 0 2) hδ hb =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckRHSSection (I := I) g_bg g₀) := by
  have hrem : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
      (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ hb) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckRHSSection (I := I) g_bg g₀) := by
    rw [deTurckRem_zero]
  refine Eq.trans ?_ hrem
  exact tensorHs.ext (funext fun _ => rfl)

/-- **`N(0)` is the static Ricci--DeTurck field.**

The genuine low-regularity nonlinearity evaluated at the zero state equals the spectral `H¹`
embedding of `deTurckRHSSection g_bg g₀`.  The continuity hypothesis is the one produced
alongside the tame coefficients by `lowRegN_outer`. -/
theorem nZero_eq_static (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 < R)
    (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal)) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (deTurckRHSSection (I := I) g_bg g₀) := by
  classical
  have hmem : (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ :
      lowerState (I := I) (M := M) g₀ 1 R) ∈ smoothCore (I := I) (M := M) g₀ R :=
    zero_mem_smoothCore (I := I) (M := M) g₀ hR.le
  have hrep : smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
      (coreRep (I := I) (M := M) g₀
        (⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :
          smoothCore (I := I) (M := M) g₀ R)) = 0 := by
    rw [coreRep_spec]
  have hsymm : smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
      (symmS (I := I) (M := M) g₀
        (coreRep (I := I) (M := M) g₀
          (⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :
            smoothCore (I := I) (M := M) g₀ R))) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) := by
    rw [smoothCcToTensorHs_zero]
    have hle := norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2)
      (coreRep (I := I) (M := M) g₀
        (⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :
          smoothCore (I := I) (M := M) g₀ R))
    rw [hrep, norm_zero] at hle
    exact norm_le_zero_iff.mp hle
  have hb0 : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ := by
    refine hreal (0 : SmoothCcTensor g₀ 0 2) ?_
    rw [smoothCcToTensorHs_zero, norm_zero]
    exact hR.le
  calc lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩
      = coreN (I := I) (M := M) g₀ g_bg hδ hreal
          ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :=
        (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore
          ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
          (symmS (I := I) (M := M) g₀
            (coreRep (I := I) (M := M) g₀
              ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩)) hδ
          (hreal _ (coreSymm_h2 (I := I) (M := M) g₀
            ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩)) := rfl
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
          (0 : SmoothCcTensor g₀ 0 2) hδ hb0 :=
        smoothN_wd (I := I) (M := M) g₀ g_bg 1 _ _ hδ _ hδ hb0 hsymm
    _ = smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckRHSSection (I := I) g_bg g₀) :=
        deTurckSmoothN_zero (I := I) (M := M) g₀ g_bg 1 hδ hb0

/-! ### Curvature-free spectral order one -/

private theorem hsOne_sq (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ^ 2 =
      ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2 := by
  classical
  have hsum0 :
      Summable (fun m :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ 0 *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 S) m) ^ 2) := by
    simpa only [pow_zero, one_mul, tensorSobolevWeight_zero, ccTensorToHs_coeff] using
      (ccTensorToHs (I := I) (M := M) g₀ 2 (0 : ℝ) S).weighted_summable
  have hsum1 :
      Summable (fun m :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ 1 *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 S) m) ^ 2) := by
    have hfull :=
      (ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ) S).weighted_summable
    refine Summable.of_nonneg_of_le ?_ ?_ hfull
    · intro m
      have hlam : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · intro m
      have hlam : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hle :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m ≤
            1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m := by
        linarith
      have hweight :
          tensorSobolevWeight (I := I) (M := M) m (1 : ℝ) =
            1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m := by
        unfold tensorSobolevWeight
        rw [Real.rpow_one]
      rw [pow_one, hweight, ccTensorToHs_coeff]
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  rw [Nat.cast_one]
  rw [← norm_ccHs_eq_smoothHs (I := I) (M := M) g₀ (1 : ℝ) S,
    ccToHs_norm_sq]
  calc
    ∑' m :
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) m (1 : ℝ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 S) m) ^ 2 =
        ∑' m, (
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 0 *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 +
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 1 *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2) := by
          refine tsum_congr (fun m => ?_)
          unfold tensorSobolevWeight
          rw [Real.rpow_one]
          ring
    _ =
        (∑' m,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 0 *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2) +
        ∑' m,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 1 *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 :=
      Summable.tsum_add hsum0 hsum1
    _ = ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2 := by
      rw [← rawIter_tsum (I := I) (M := M) g₀ 2 0 S,
        ← covIter_tsum (I := I) (M := M) g₀ 2 0 S,
        rawTensorConnLapIter_zero, SmoothCcTensor.norm_toL2]

/-! ### The closed constant -/

/-- **The closed class-uniform bound on `‖N(0)‖_{H¹}`.**

`nZeroC Ksup Λ volBase n = √2 · (2 · (Ksup · √(√(Λ^n) · volBase)))`, where `Ksup` bounds the
fibre norms of the static Ricci--DeTurck field and its first covariant derivative, `Λ` is the
comparability constant of the class, `volBase` is the total volume of the fixed background and
`n = finrank ℝ E`.  Everything on the right is `gBase`-data, `Λ` and the dimension. -/
def nZeroC (Ksup Λ volBase : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt 2 * (2 * (Ksup * Real.sqrt (Real.sqrt (Λ ^ n) * volBase)))

theorem nZeroC_nonneg {Ksup : ℝ} (hKsup : 0 ≤ Ksup) (Λ volBase : ℝ) (n : ℕ) :
    0 ≤ nZeroC Ksup Λ volBase n := by
  unfold nZeroC
  positivity

/-- **The `H¹(g₀)` bound on the static Ricci--DeTurck field.**

The spectral `H¹` norm of `deTurckRHSSection gBase g₀` is at most the closed `nZeroC`, in terms
of a fibre sup bound `Ksup` on its covariant `1`-jet, the comparability constant `Λ` and the
`gBase` volume. -/
theorem staticN_h1_le (gBase g₀ : SmoothRiemannianMetric I M)
    {Λ Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hsup : ∀ j : ℕ, j ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Ksup ^ 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (deTurckRHSSection (I := I) gBase g₀)‖ ≤
      nZeroC Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) := by
  classical
  have hvol₀nn : 0 ≤ (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ :=
    ENNReal.toReal_nonneg
  let S := deTurckRHSSection (I := I) gBase g₀
  have hjet_sq := hsOne_sq (I := I) (M := M) g₀ S
  have hcross : 0 ≤ ‖S‖ * ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hjet0 :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ≤
        ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
    apply le_of_sq_le_sq
    · rw [hjet_sq]
      nlinarith
    · positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hjet :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ≤
        Real.sqrt 2 * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
    calc
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ≤
          ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := hjet0
      _ = 1 * (‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖) := by ring
      _ ≤ Real.sqrt 2 *
          (‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖) :=
        mul_le_mul_of_nonneg_right hsqrt (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = Real.sqrt 2 * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
  have hterm : ∀ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ ≤
        Ksup * Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ) := by
    intro j hj
    have hj1 : j ≤ 1 := by
      have hj2 : j < 2 := Finset.mem_range.mp hj
      omega
    exact smoothCc_norm_le_of_fibreSq (I := I) (M := M) g₀ _ hKsup (hsup j hj1)
  have hsum : ∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ ≤
        2 * (Ksup *
          Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ)) := by
    calc ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ ≤
          ∑ _j ∈ Finset.range 2, Ksup *
            Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ) :=
          Finset.sum_le_sum hterm
      _ = 2 * (Ksup *
          Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hvolle := volReal_cross_le (I := I) (M := M) gBase g₀ hEq
  have hsqrtvol :
      Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ) ≤
      Real.sqrt (Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ) :=
    Real.sqrt_le_sqrt hvolle
  have hchain : 2 * (Ksup *
        Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ)) ≤
      2 * (Ksup * Real.sqrt (Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtvol hKsup
    linarith
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (deTurckRHSSection (I := I) gBase g₀)‖ ≤
      Real.sqrt 2 * ∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ := hjet
    _ ≤ Real.sqrt 2 * (2 * (Ksup *
        Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ))) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg 2)
    _ ≤ Real.sqrt 2 * (2 * (Ksup * Real.sqrt (Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ))) :=
        mul_le_mul_of_nonneg_left hchain (Real.sqrt_nonneg 2)
    _ = nZeroC Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) := rfl

/-- **Brick E6: the class-uniform zero-state forcing bound.**

For every metric `g₀` that is `Λ`-comparable to the fixed background `gBase` and whose static
Ricci--DeTurck field has a `Λ`-class fibre bound `Ksup` on its covariant `1`-jet, the genuine
low-regularity nonlinearity at the zero state satisfies the `H¹(g₀)` bound with the closed
constant `nZeroC`.  This is the `D`-number of the six-number horizon interface, in the exact
currency of `lowreg_partial_sol_of_bounds`'s `hzero`. -/
theorem nZero_unif (gBase g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 < R)
    (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ gBase hδ hreal))
    {Λ Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hsup : ∀ j : ℕ, j ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Ksup ^ 2) :
    ‖lowRegN (I := I) (M := M) g₀ gBase hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩‖ ≤
      nZeroC Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) := by
  rw [nZero_eq_static (I := I) (M := M) g₀ gBase hR hδ hreal hcore]
  exact staticN_h1_le (I := I) (M := M) gBase g₀ hKsup hEq hsup

/-- **The `hzero` slot of `lowreg_partial_sol_of_bounds`.**

`nZero_unif` read on the six-number nonlinearity `lowregNfun`, at `D := nZeroC …`.  Together
with `lowregHorizon_mono` this is the class-uniform upper bound on `D` that the horizon floor
consumes. -/
theorem nZero_lowregNfun (gBase g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ)
    (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ gBase hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal)))
    {Λ Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hsup : ∀ j : ℕ, j ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Ksup ^ 2) :
    ‖lowregNfun (I := I) (M := M) g₀ gBase hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad_pos hCtop hB1 hρ hP).le⟩‖ ≤
      nZeroC Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) :=
  nZero_unif (I := I) (M := M) gBase g₀ (lowregStateRad_pos hCtop hB1 hρ hP) hδ
    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal)
    hcore hKsup hEq hsup

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
