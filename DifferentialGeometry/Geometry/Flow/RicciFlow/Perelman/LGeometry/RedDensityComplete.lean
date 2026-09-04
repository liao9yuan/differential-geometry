import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CompleteMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.TailActionBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Reduced-density measurability on complete flows

This module obtains target-point measurability from the complete-flow
minimizer and its smooth local upper support for L-cost.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a complete flow with uniformly bounded curvature on the backward slab,
reduced density is measurable in its target point. -/
theorem redDensity_meas_rm
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : Real) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K) :
    Measurable (fun y : M ↦ redDensity S T x y tau) := by
  have hcost : UpperSemicontinuous (fun y : M ↦ lCost S T x y tau) := by
    intro y
    let g := S.base.metric T
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
      lt_of_le_of_ne le_top
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) x y)
    obtain ⟨p, hp, _hlen⟩ :=
      DifferentialGeometry.Geometry.Riemannian.CGT.exists_flat_path
        (I := I) hxy
    let b : Real := Real.sqrt tau
    have hb : 0 < b := by simpa only [b] using Real.sqrt_pos.2 htau
    let alpha₀ : Real → M := fun s ↦ p.extend (s / b)
    have halpha₀ : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha₀ := by
      apply hp.c1.comp
      rw [contMDiff_iff_contDiff]
      fun_prop
    have ha₀ : alpha₀ 0 = x := by
      simp only [alpha₀, zero_div, Path.extend_zero]
    have hb₀ : alpha₀ (Real.sqrt tau) = y := by
      simp only [alpha₀, b, div_self hb.ne', Path.extend_one]
    obtain ⟨Z, hmin, hExp⟩ :=
      exists_lMinVec_rm (I := I) S hS K T hg tau htau hreg hRm
        x y alpha₀ halpha₀ ha₀ hb₀
    let s0 : Real := Real.sqrt tau / 2
    have hs00 : 0 < s0 := by
      exact div_pos (Real.sqrt_pos.2 htau) (by norm_num)
    have hs0b : s0 < Real.sqrt tau := by
      exact div_two_lt_of_pos (Real.sqrt_pos.2 htau)
    obtain ⟨U, hUopen, hcenter, F, hF, hFcenter, hupper⟩ :=
      exists_lCost_support (IM := I) S hS K T x hmin hreg hRm hs00 hs0b
    have hyU : y ∈ U := by
      rw [← hExp]
      exact hcenter
    have hFy : F y = lCost S T x y tau := by
      simpa only [hExp] using hFcenter
    intro A hA
    have hFA : F y < A := by simpa only [hFy] using hA
    have hFcont : ContinuousAt F y :=
      hF.continuousOn.continuousAt (hUopen.mem_nhds hyU)
    filter_upwards [hUopen.mem_nhds hyU,
      hFcont.eventually (Iio_mem_nhds hFA)] with z hzU hzF
    exact lt_of_le_of_lt (hupper z hzU) hzF
  let phi : Real → Real := fun r ↦ Real.exp
    (-r / (2 * Real.sqrt tau) -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hphi : Continuous phi := by
    dsimp only [phi]
    fun_prop
  have hphiAnti : Antitone phi := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    have hden : 0 < 2 * Real.sqrt tau :=
      mul_pos (by norm_num) (Real.sqrt_pos.2 htau)
    have hdiv : a / (2 * Real.sqrt tau) ≤ b / (2 * Real.sqrt tau) :=
      (div_le_div_iff_of_pos_right hden).2 hab
    have hneg : -b / (2 * Real.sqrt tau) ≤ -a / (2 * Real.sqrt tau) := by
      simpa only [neg_div] using neg_le_neg hdiv
    exact sub_le_sub_right
      (sub_le_sub_right hneg
        (((Module.finrank Real E : Real) / 2) * Real.log tau))
      (((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hdens : LowerSemicontinuous
      (fun y : M ↦ redDensity S T x y tau) := by
    simpa only [Function.comp_apply, phi, redDensity, redLength, neg_div] using
      hphi.comp_upperSemicontinuous_antitone hcost hphiAnti
  exact hdens.measurable

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
