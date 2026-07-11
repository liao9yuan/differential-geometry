import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartGramRealizeDiffJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedCovGradChartJetPeel

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open Manifold Set Filter Topology
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma rawPullR_eq_rawCompOnE_comp (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx =
      tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ (toEuclidean (E := E)).symm := by
  funext y
  rw [tensorComponentEuclideanChart, Function.comp_apply, Function.comp_apply, Function.comp_apply, tensorChartComponentOnModel]

lemma norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) y‖ ≤
      ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m *
        ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
          (interior (extChartAt I α).target) ((toEuclidean (E := E)).symm y)‖ := by
  classical
  set e : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn

  rw [rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx]

  have hpre_open : IsOpen (e ⁻¹' O) := hO_open.preimage e.continuous
  have hy_pre : y ∈ e ⁻¹' O := hy

  have hplain : iteratedFDeriv ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ ⇑e) y =
      iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ ⇑e) (e ⁻¹' O) y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := tensorChartComponentOnModel (I := I) (M := M) g S α Jdx ∘ ⇑e) m hpre_open hy_pre).symm
  rw [hplain]

  have hcomp := e.iteratedFDerivWithin_comp_right (f := tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
    hUD (x := y) hy m
  rw [hcomp]

  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

  have he_norm : ‖(e : EuclN →L[ℝ] E)‖ = ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ := rfl
  rw [he_norm, mul_comm]

end DifferentialGeometry.PDE.RicciFlow
