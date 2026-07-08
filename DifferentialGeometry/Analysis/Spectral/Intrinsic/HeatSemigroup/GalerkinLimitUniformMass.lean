import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinForcingTimeL2Limit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

theorem fatou_weighted_sq_mass_le {ι : Type*} (S : ℕ → Finset ι)
    (hS : Tendsto S atTop atTop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ι → ℝ) (vlim : ι → ℝ)
    (hconv : ∀ i, Tendsto (fun N => v N i) atTop (𝓝 (vlim i)))
    (B : ℝ) (hbound : ∀ N, ∑ i ∈ S N, w i * (v N i) ^ 2 ≤ B) :
    Summable (fun i => w i * (vlim i) ^ 2) ∧
      ∑' i, w i * (vlim i) ^ 2 ≤ B := by
  have hnn : ∀ i, 0 ≤ w i * (vlim i) ^ 2 := fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι, ∑ i ∈ K, w i * (vlim i) ^ 2 ≤ B := by
    intro K
    have hlim : Tendsto (fun N => ∑ i ∈ K, w i * (v N i) ^ 2) atTop
        (𝓝 (∑ i ∈ K, w i * (vlim i) ^ 2)) := by
      refine tendsto_finset_sum K (fun i _ => ?_)
      exact ((hconv i).pow 2).const_mul (w i)
    have hev : ∀ᶠ N in atTop, ∑ i ∈ K, w i * (v N i) ^ 2 ≤ B := by
      have hsub : ∀ᶠ N in atTop, K ≤ S N := hS.eventually_ge_atTop K
      filter_upwards [hsub] with N hKN
      have hKsub : K ⊆ S N := hKN
      have hmono : ∑ i ∈ K, w i * (v N i) ^ 2 ≤ ∑ i ∈ S N, w i * (v N i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hKsub
          (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      exact le_trans hmono (hbound N)
    exact le_of_tendsto hlim hev
  refine ⟨summable_of_sum_le hnn hpartial, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hpartial

/-- **Posited deferred input (`sorry`).** Per-mode Galerkin convergence for the symmetrized DeTurck
flow: the `N`-th Galerkin coordinate converges to the per-mode Duhamel convolution of the forcing
mode coefficient. Symmetric mirror of the proven raw helper `galerkinSol_tendsto_solField_perModeConv`
(snapshot `c848da47`), with `deTurckSobolevNHa2Symm`/`deTurckForceBallRadiusSymm`/
`deTurckGalerkinForcingSymm` replacing the raw nonlinearity data; its proof (the symmetrized
Galerkin-forcing time-`L²` limit) has not landed yet, so consumers transitively depend on `sorryAx`
until it does. -/
theorem galerkinSol_tendsto_solField_perModeConvSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => U N t i) atTop
      (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)) :=
  sorry

/-- Uniform-in-`N` all-order spatial spectral mass control for the symmetrized DeTurck Galerkin
limit: for each Sobolev order `σ` the weighted spectral mass of the per-mode Duhamel convolutions of
the forcing mode coefficients is bounded on `[0, T]`. Symmetric mirror of the proven raw helper
`deTurckGalerkin_solField_uniformSpatialMass_allOrder` (snapshot `c848da47`), assembled from the
symmetrized Galerkin existence, per-scale energy closure, and per-mode convergence twins by the same
Fatou weighted-mass argument; its conclusion is nonlinearity-agnostic, so this transits only the
`sorry`s of its symmetric children. -/
theorem deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ := by
  classical
  obtain ⟨U, hUcont, hUderiv, hUinit_coeff⟩ :=
    deTurckGalerkin_solution_existsSymm (I := I) (M := M) g₀ g_bg a (by omega)
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) hT.le
  have hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0 := by
    intro N i hi
    rw [hUinit_coeff N i hi]; rfl
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScaleSymm (I := I) (M := M) g₀ g_bg a ha_super
      (T := T) U hUinit
  have hUmass : ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N) ((a : ℝ) + (k : ℝ)) t ≤ Bound :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U)
      (Fseq := deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB
  intro σ
  obtain ⟨k, hk⟩ := exists_nat_ge (σ - (a : ℝ))
  have hσk : σ ≤ (a : ℝ) + (k : ℝ) := by linarith
  obtain ⟨Bound, hBound⟩ := hUmass k
  refine ⟨Bound, fun t ht => ?_⟩
  set wσ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i σ with hwσ
  have hwσ_nn : ∀ i, 0 ≤ wσ i := fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  have hweight_dom : ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) := by
    intro i
    exact Real.rpow_le_rpow_of_exponent_le
      (one_le_one_add_lambda (I := I) (M := M) i) hσk
  have hpartialbound : ∀ N,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, wσ i * (U N t i) ^ 2 ≤ Bound := by
    intro N
    have hle : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, wσ i * (U N t i) ^ 2 ≤
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (U N t i) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_right (hweight_dom i) (sq_nonneg _)
    have hgal : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t ≤ Bound :=
      hBound N t ht
    have hgal_eq : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (U N t i) ^ 2 := rfl
    rw [hgal_eq] at hgal
    exact le_trans hle hgal
  have hconv : ∀ i,
      Tendsto (fun N => U N t i) atTop
        (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t)) :=
    fun i => galerkinSol_tendsto_solField_perModeConvSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i t ht
  have hfatou := fatou_weighted_sq_mass_le
    (eigenIdxFinset (I := I) (M := M) g₀) (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    wσ hwσ_nn (fun N i => U N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t)
    (fun i => hconv i) Bound hpartialbound
  exact hfatou

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
