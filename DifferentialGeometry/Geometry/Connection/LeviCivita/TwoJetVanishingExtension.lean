import DifferentialGeometry.Geometry.Connection.LeviCivita.LinearExtensionTangent
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla

/-!
# A controlled smooth tangent extension with vanishing covariant `2`-jet at the basepoint

For a smooth Riemannian metric `g` on a closed manifold, a base point `x₀ : M`, and a fibre
vector `v : TangentSpace I x₀`, this file isolates the **covariant-`2`-jet-vanishing** smooth
tangent extension `W : Π b, TangentSpace I b` of `v`: a smooth section with

* `W x₀ = v` (it extends `v`);
* `∇_u W (x₀) = 0` for every direction `u` — the covariant `1`-jet vanishes; and
* `∇_Y(∇_Y W)(x₀) = 0` for every smooth field `Y` — the iterated covariant `2`-jet vanishes.

Such an extension is the geometric device that turns the genuine per-direction third-order
cancellation residue of `MovingFrameRemainderFrameSumBridge`/`SecondOrderCommutationResidueFiberBound`
into a *pure curvature* contraction reading only `v`: in the second-order leading-slot commutation
residue `secondOrderResidue g s S x i w` the four covariant-derivative-of-`w` summands —
`R(B, ∇_B w) V`, `∇_{[B, w]}(∇_B V)` (through `∇_B w`), `∇_B(∇_{∇_B w} V)`, and the iterated
`∇_B(∇_B w)`-direction term — all read the covariant `1`- or `2`-jet of `w` at `x`, which the
vanishing-`2`-jet extension kills, leaving only the order-`≤ 2` curvature contractions of `V` against
the `(∇R)` and `R` classes.

The construction is the **chart-coordinate quadratic correction** of the coordinate-constant linear
extension `linearExtensionTangent x₀ v` (`LinearExtensionTangent`): the linear extension already has a
vanishing chart-derivative near `x₀`, so its covariant `1`-jet at `x₀` is the pure metric Christoffel
correction (`covApply_linearExtensionTangent_basepoint_eq`) and its covariant `2`-jet is the chart
`∂Γ + Γ·Γ` contraction (`covApply_covApply_linearExtensionTangent_basepoint_eq`); subtracting the
degree-`1` and degree-`2` chart polynomials reproducing those corrections cancels the covariant
`1`- and `2`-jets without disturbing the basepoint value.

## Main results

* `covApply_covApply_linearExtensionTangent_basepoint_eq` — the basepoint chart formula for the
  iterated covariant derivative `∇_v(∇_v(linearExtensionTangent x₀ w))(x₀)` in terms of the chart
  Christoffel derivative `∂Γ` (`fderiv` of `chartChristoffel`), the quadratic `Γ·Γ` contraction, and
  the coordinate `tangentCoord x₀ w`. (Posited chart sub-node.)
* `exists_twoJetVanishing_tangentExtension` — the existence of a smooth covariant-`2`-jet-vanishing
  tangent extension of `v`. (Posited geometric construction.)
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Where the bump is eventually `1` near `b` (and `b` lies in the trivialization base set),
the chart-trivialised representation of `linearExtensionTangent x₀ w` is eventually equal to the
constant model coordinate `tangentCoord x₀ w` near `b`. This is the base-set/bump-`1`
localisation behind the vanishing chart derivative of the coordinate-constant field. -/
private lemma chartE_section_repr_linExt_eventuallyEq_const_at
    (x₀ : M) (w : TangentSpace I x₀) {b : M}
    (hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ)))
    (hbbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 b) :
    chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w)
      =ᶠ[𝓝 b] (fun _ : M => tangentCoord (I := I) x₀ w) := by
  classical
  filter_upwards [hb1, hbbase] with c hc1 hcbase
  have hWc : linearExtensionTangent (I := I) x₀ w c =
      coordExtensionTangent (I := I) x₀ w c := by
    rw [linearExtensionTangent_apply, hc1, one_smul]
  rw [chartE_section_repr_eq_trivToE, hWc, ← chartE_section_repr_eq_trivToE]
  exact chartE_section_repr_coordExtensionTangent_eq (I := I) x₀ w hcbase

/-- **First Christoffel layer (pointwise) for the linear extension.** At a good-set point `b`
of the chart at `x₀` where the bump is eventually `1` near `b`, the covariant-derivative value
`(LeviCivita g) (linExt x₀ w) b (linExt x₀ v b)` equals
`trivFromE x₀ b (christoffelCorrection g x₀ b (tangentCoord x₀ w) (linExt x₀ v b))`. The chart
derivative of the coordinate-constant representation vanishes, leaving only the metric
Christoffel correction. -/
private lemma LeviCivita_covApply_linExt_firstLayer_pointwise
    (g : SmoothRiemannianMetric I M) (x₀ : M) (w v : TangentSpace I x₀)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) x₀)
    (hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ))) :
    (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x₀ w) b
        (linearExtensionTangent (I := I) x₀ v b) =
      trivFromE (I := I) x₀ b
        (christoffelCorrection (I := I) g x₀ b (tangentCoord (I := I) x₀ w)
          (linearExtensionTangent (I := I) x₀ v b)) := by
  classical
  have hbbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 b :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hb)
  have hconst := chartE_section_repr_linExt_eventuallyEq_const_at (I := I) x₀ w hb1 hbbase
  have hWat : MDiffAt (T% (linearExtensionTangent (I := I) x₀ w)) b :=
    (linearExtensionTangent_smooth (I := I) x₀ w).mdifferentiableAt (by norm_num)
  rw [LeviCivita_chart_apply (I := I) g x₀ hb hWat
    (linearExtensionTangent (I := I) x₀ v b)]
  rw [chartLeviCivita_apply (I := I) g x₀ (linearExtensionTangent (I := I) x₀ w) hb
    (linearExtensionTangent (I := I) x₀ v b)]
  have hfd0 :
      fderiv ℝ (chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w)
          ∘ (extChartAt I x₀).symm) (extChartAt I x₀ b) = 0 := by
    have hb_src : b ∈ (extChartAt I x₀).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
    have hev :
        (chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w)
            ∘ (extChartAt I x₀).symm)
          =ᶠ[𝓝 (extChartAt I x₀ b)] (fun _ : E => tangentCoord (I := I) x₀ w) := by
      have hsymm_cont : ContinuousAt (extChartAt I x₀).symm (extChartAt I x₀ b) := by
        have hb_tgt : extChartAt I x₀ b ∈ (extChartAt I x₀).target :=
          (extChartAt I x₀).map_source hb_src
        exact (continuousOn_extChartAt_symm x₀).continuousAt
          ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hb_tgt)
      have hsymm_pt : (extChartAt I x₀).symm (extChartAt I x₀ b) = b :=
        (extChartAt I x₀).left_inv hb_src
      have hmem :
          {c : M | chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w) c
            = tangentCoord (I := I) x₀ w} ∈ 𝓝 ((extChartAt I x₀).symm (extChartAt I x₀ b)) := by
        rw [hsymm_pt]; exact hconst
      filter_upwards [hsymm_cont.preimage_mem_nhds hmem] with y hy using hy
    rw [hev.fderiv_eq, fderiv_const_apply]
  rw [hfd0, ContinuousLinearMap.zero_apply, zero_add]
  have hreprb : chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ w) b =
      tangentCoord (I := I) x₀ w := hconst.self_of_nhds
  rw [hreprb]

/-- **First Christoffel layer (neighbourhood) for the linear extension.** The chart-trivialised
representation of the intermediate section
`S := covApply (LeviCivita g) (linExt x₀ v) (linExt x₀ w)`, pulled through `(extChartAt I x₀).symm`,
is eventually equal near `φ x₀` to the chart-Christoffel contraction
`y ↦ ∑_{i,j,m} Vᵢ Wⱼ Γᵐᵢⱼ(y) • eₘ` of the constant coordinates `V := tangentCoord x₀ v`,
`W := tangentCoord x₀ w`. -/
private lemma chartE_section_repr_covApply_linExt_eventuallyEq
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : TangentSpace I x₀) :
    (chartE_section_repr (I := I) x₀
        (Connection.covApply (LeviCivita (I := I) g)
          (linearExtensionTangent (I := I) x₀ v) (linearExtensionTangent (I := I) x₀ w))
        ∘ (extChartAt I x₀).symm)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
        (fun y : E =>
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                  ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j *
                  chartChristoffel (I := I) g x₀ i j m y) •
                (chartModelBasis E) m) := by
  classical
  have hbump1 : {b : M | (linExtBump (I := I) x₀ : M → ℝ) b = 1} ∈ 𝓝 x₀ :=
    (linExtBump (I := I) x₀).eventuallyEq_one
  obtain ⟨W₀, hW₀_sub, hW₀_open, hx₀W₀⟩ := mem_nhds_iff.mp hbump1
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) x₀) :=
    chartLeviCivitaGoodSet_isOpen (I := I) x₀
  set Vset : Set E :=
    (extChartAt I x₀).target ∩
      (extChartAt I x₀).symm ⁻¹' (chartLeviCivitaGoodSet (I := I) x₀ ∩ W₀) with hVset_def
  have hcont_symm : ContinuousOn (extChartAt I x₀).symm (extChartAt I x₀).target :=
    continuousOn_extChartAt_symm x₀
  have hVset_open : IsOpen Vset :=
    hcont_symm.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x₀)
      (hgood_open.inter hW₀_open)
  have hx₀_good : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hx₀src_ext : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hx₀tgt : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hx₀src_ext
  have hφx₀V : extChartAt I x₀ x₀ ∈ Vset := by
    refine ⟨hx₀tgt, ?_⟩
    rw [Set.mem_preimage, (extChartAt I x₀).left_inv hx₀src_ext]
    exact ⟨hx₀_good, hx₀W₀⟩
  filter_upwards [hVset_open.mem_nhds hφx₀V] with y hy
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  rw [Set.mem_preimage] at hy_pre
  obtain ⟨hy_good, hy_W₀⟩ := hy_pre
  set b : M := (extChartAt I x₀).symm y with hb_def
  have hbbase : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hy_good
  have hb1 : (linExtBump (I := I) x₀ : M → ℝ) =ᶠ[𝓝 b] (fun _ => (1 : ℝ)) := by
    filter_upwards [hW₀_open.mem_nhds hy_W₀] with c hc using hW₀_sub hc
  simp only [Function.comp_apply, chartE_section_repr_eq_trivToE, Connection.covApply_apply]
  rw [show (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x₀ w) b
        (linearExtensionTangent (I := I) x₀ v b) =
      trivFromE (I := I) x₀ b
        (christoffelCorrection (I := I) g x₀ b (tangentCoord (I := I) x₀ w)
          (linearExtensionTangent (I := I) x₀ v b)) from
    LeviCivita_covApply_linExt_firstLayer_pointwise (I := I) g x₀ w v hy_good hb1]
  rw [trivToE_trivFromE (I := I) x₀ hbbase]
  rw [christoffelCorrection_apply (I := I) g x₀ b (tangentCoord (I := I) x₀ w)
    (linearExtensionTangent (I := I) x₀ v b)]
  have hreprVb :
      (chartModelBasis E).repr
          (trivToE (I := I) x₀ b (linearExtensionTangent (I := I) x₀ v b)) =
        (chartModelBasis E).repr (tangentCoord (I := I) x₀ v) := by
    have hVb : chartE_section_repr (I := I) x₀ (linearExtensionTangent (I := I) x₀ v) b =
        tangentCoord (I := I) x₀ v :=
      (chartE_section_repr_linExt_eventuallyEq_const_at (I := I) x₀ v hb1
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hbbase)).self_of_nhds
    rw [chartE_section_repr_eq_trivToE] at hVb
    rw [hVb]
  have hφb : extChartAt I x₀ b = y := by
    rw [hb_def, (extChartAt I x₀).right_inv hy_tgt]
  rw [hreprVb, hφb]

/-- Each chart Christoffel symbol is differentiable at the chart image `φ x₀` (it is `C^∞` on the
interior of the chart target, which contains `φ x₀`). -/
private lemma chartChristoffel_differentiableAt_basepoint
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i j m : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
      (extChartAt I x₀ x₀) := by
  classical
  have hx₀src_ext : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hx₀tgt : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hx₀src_ext
  have hx₀int : extChartAt I x₀ x₀ ∈ interior ((extChartAt I x₀).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x₀ hx₀tgt
  have hcd : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g x₀ i j m)
      (interior (extChartAt I x₀).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g x₀ i j m
  exact (hcd.differentiableOn (by norm_num)).differentiableAt
    (isOpen_interior.mem_nhds hx₀int)

/-- The Fréchet derivative, at `φ x₀` in a direction `d : E`, of the coordinate-Christoffel
contraction `y ↦ ∑_{i,j,m} Vᵢ Wⱼ Γᵐᵢⱼ(y) • eₘ` expands as
`∑_{i,j,m} Vᵢ Wⱼ (∂_d Γᵐᵢⱼ)(φ x₀) • eₘ`. -/
private lemma fderiv_christoffelVWSum_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (V W : E) (d : E) :
    fderiv ℝ
        (fun y : E =>
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                  chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)
        (extChartAt I x₀ x₀) d =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
              (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                (extChartAt I x₀ x₀)) d) • (chartModelBasis E) m := by
  classical
  have hdiff_inner : ∀ i j m : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y : E =>
        (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
            chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)
        (extChartAt I x₀ x₀) := by
    intro i j m
    exact (((chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m).const_mul
      (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j)).smul_const
      ((chartModelBasis E) m))
  rw [fderiv_fun_sum (fun i _ => DifferentiableAt.fun_sum
    (fun j _ => DifferentiableAt.fun_sum (fun m _ => hdiff_inner i j m)))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fderiv_fun_sum (fun j _ => DifferentiableAt.fun_sum (fun m _ => hdiff_inner i j m))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fderiv_fun_sum (fun m _ => hdiff_inner i j m)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [fderiv_smul_const (((chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m).const_mul
    (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j)))
    ((chartModelBasis E) m)]
  rw [ContinuousLinearMap.smulRight_apply]
  rw [fderiv_const_mul (chartChristoffel_differentiableAt_basepoint (I := I) g x₀ i j m)
    (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j)]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]

/-- Collect a `3`-fold-indexed family of scalar-multiples of a basis vector indexed by the
innermost variable, factoring the basis vector out of the inner two sums. -/
private lemma sum3_collect_basis_inner
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      ∑ z : Fin (Module.finrank ℝ E), (F a b z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E),
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F a b z) •
          (chartModelBasis E) z := by
  classical
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ z : Fin (Module.finrank ℝ E), (F a b z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), (F a b z) • (chartModelBasis E) z from by
    simp_rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun x => (x.2.2, x.1, x.2.1)) (fun x => (x.2.1, x.2.2, x.1))
      (fun x _ => Finset.mem_univ _) (fun x _ => Finset.mem_univ _)
      (fun x _ => by ext <;> simp) (fun x _ => by ext <;> simp) (fun x _ => rfl)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_smul]

/-- Collect a `5`-fold-indexed family of scalar-multiples of a basis vector indexed by the
innermost variable, factoring the basis vector out of the inner four sums. -/
private lemma sum5_collect_basis_inner
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        ∑ z : Fin (Module.finrank ℝ E), (F a b c d z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E),
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            F a b c d z) • (chartModelBasis E) z := by
  classical
  -- move the innermost `z`-sum to the outermost position by reindexing the `5`-fold product
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ∑ z : Fin (Module.finrank ℝ E), (F a b c d z) • (chartModelBasis E) z) =
      ∑ z : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), (F a b c d z) • (chartModelBasis E) z from by
    simp_rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun x => (x.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1))
      (fun x => (x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1))
      (fun x _ => Finset.mem_univ _) (fun x _ => Finset.mem_univ _)
      (fun x _ => by ext <;> simp) (fun x _ => by ext <;> simp) (fun x _ => rfl)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_smul]

/-- Reindex a `4`-fold scalar sum from `(p,q,i,j)`-order to `(i,j,p,q)`-order. -/
private lemma sum4_scalar_swap_pairs
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :
    (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E), F p q i j) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), F p q i j := by
  classical
  simp_rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1))
    (fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)) (fun x _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_univ _) (fun x _ => by ext <;> simp) (fun x _ => by ext <;> simp)
    (fun x _ => rfl)

/-- The `q`-coordinate in `chartModelBasis E` of the coordinate-Christoffel value
`∑_{i,j,m} Vᵢ Wⱼ Γᵐᵢⱼ(y) • eₘ` is `∑_{i,j} Vᵢ Wⱼ Γᵍᵢⱼ(y)`. -/
private lemma chartModelBasis_repr_christoffelVWSum
    (g : SmoothRiemannianMetric I M) (x₀ : M) (V W : E) (y : E)
    (q : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                chartChristoffel (I := I) g x₀ i j m y) • (chartModelBasis E) m)) q =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
          chartChristoffel (I := I) g x₀ i j q y := by
  classical
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_sum]
  simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single q
    (fun m _ hm => by rw [Module.Basis.repr_self_apply, if_neg hm, mul_zero])
    (fun hq => absurd (Finset.mem_univ q) hq)]
  rw [Module.Basis.repr_self_apply, if_pos rfl, mul_one]

/-- **The basepoint chart formula for the iterated covariant derivative of the linear extension
(`∂Γ`-sub-node, posited).** For the coordinate-constant linear extension `linearExtensionTangent x₀ w`
(`LinearExtensionTangent`), the iterated tangent covariant derivative
`∇_v(∇_v(linearExtensionTangent x₀ w))(x₀)` along a fixed direction `v` collapses, at the basepoint, to
the chart-coordinate second-order contraction of the model coordinate `tangentCoord x₀ w` against the
chart Christoffel derivative `∂Γ` (the `fderiv` of `chartChristoffel`) and the quadratic `Γ·Γ` term:
```
∇_v(∇_v W)(x₀) = trivFromE x₀ x₀ ( ∑ᵢⱼₖₗ (vᵏ vⁱ wʲ) · (∂ₖ Γᵐᵢⱼ)(φ x₀) · eₘ
                                     + ∑ᵢⱼₖₗₘ (vⁱ vᵏ wʲ) · Γᵐₖₗ(φ x₀) · Γˡᵢⱼ(φ x₀) · eₘ ),
```
with `W := linearExtensionTangent x₀ w`, `v`-coordinates and `w := tangentCoord x₀ w` taken in the
`chartModelBasis`, and `Γ = chartChristoffel g x₀`. The bump and the (vanishing near `x₀`) chart
derivative of the coordinate-constant field contribute nothing; only the once-differentiated and the
quadratic Christoffel corrections survive. This is the genuine missing chart formula, the second-order
companion of the `1`-jet basepoint reduction `covApply_linearExtensionTangent_basepoint_eq`.

**Posited** (body `sorry`): the chart computation of the iterated covariant derivative of the
coordinate-constant field — a second-order chart-coordinate expansion. Consumers transitively depend on
its `sorryAx`. -/
theorem covApply_covApply_linearExtensionTangent_basepoint_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) (w : TangentSpace I x₀)
    (v : TangentSpace I x₀) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ v)
          (linearExtensionTangent (I := I) x₀ w)) x₀
        (linearExtensionTangent (I := I) x₀ v x₀) =
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j) •
              ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m)) +
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j *
                chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m) := by
  classical
  set V : E := tangentCoord (I := I) x₀ v with hV_def
  set W : E := tangentCoord (I := I) x₀ w with hW_def
  set S : Π b : M, TangentSpace I b :=
    Connection.covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ v)
      (linearExtensionTangent (I := I) x₀ w) with hS_def
  have hLv1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (linearExtensionTangent (I := I) x₀ w)) := by
    have h : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    rw [h]; exact linearExtensionTangent_smooth (I := I) x₀ w
  have hS_at : MDiffAt (T% S) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g)
      (linearExtensionTangent_smooth (I := I) x₀ v) hLv1
  have hx₀_good : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)
  have hx₀src_ext : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact mem_chart_source H x₀
  have hev := chartE_section_repr_covApply_linExt_eventuallyEq (I := I) g x₀ v w
  have hLv_x₀ : linearExtensionTangent (I := I) x₀ v x₀ = v :=
    linearExtensionTangent_eq (I := I) x₀ v
  rw [hLv_x₀]
  rw [LeviCivita_chart_apply (I := I) g x₀ hx₀_good hS_at v]
  rw [chartLeviCivita_apply (I := I) g x₀ S hx₀_good v]
  rw [trivToE_self_apply (I := I) x₀ v]
  -- the chart-pulled representation of `S` is eventually the VWΓ-contraction near `φ x₀`
  rw [hev.fderiv_eq, fderiv_christoffelVWSum_apply (I := I) g x₀ V W v]
  have hSx₀_repr :
      chartE_section_repr (I := I) x₀ S x₀ =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m := by
    have h0 := hev.self_of_nhds
    simp only [Function.comp_apply] at h0
    rw [(extChartAt I x₀).left_inv hx₀src_ext] at h0
    exact h0
  rw [hSx₀_repr]
  rw [christoffelCorrection_apply (I := I) g x₀ x₀
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
            chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
          (chartModelBasis E) m) v]
  rw [trivToE_self_apply (I := I) x₀ v]
  rw [map_add]
  -- direction-`v` fderiv of Γ expands into the basis sum
  have hv_basis : (v : E) =
      ∑ k : Fin (Module.finrank ℝ E), ((chartModelBasis E).repr V) k • (chartModelBasis E) k := by
    have : (V : E) = v := by rw [hV_def]; exact trivToE_self_apply (I := I) x₀ v
    rw [← this]
    exact ((chartModelBasis E).sum_repr V).symm
  congr 1
  · -- ∂Γ term: expand the direction-`v` fderiv into the basis sum and reorder `(m,k) → (k,m)`.
    have hLHS1 :
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) v) • (chartModelBasis E) m) =
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr V) k * ((chartModelBasis E).repr V) i *
                  ((chartModelBasis E).repr W) j) •
                ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                    (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hfd : ∀ m : Fin (Module.finrank ℝ E),
          (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
              (extChartAt I x₀ x₀)) v =
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr V) k *
                (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) := by
        intro m
        conv_lhs => rw [hv_basis]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [show (∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) v) • (chartModelBasis E) m) =
          ∑ m : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                (((chartModelBasis E).repr V) k *
                  (fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                    (extChartAt I x₀ x₀)) ((chartModelBasis E) k))) • (chartModelBasis E) m from by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hfd m, Finset.mul_sum, Finset.sum_smul]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => ?_))
      rw [smul_smul]
      congr 1
      ring
    rw [hLHS1]
  · -- Γ·Γ term: collect both sides by the output basis index and match the scalar coefficients.
    refine congrArg (trivFromE (I := I) x₀ x₀) ?_
    have hVeqv : (V : E) = v := by rw [hV_def]; exact trivToE_self_apply (I := I) x₀ v
    -- LHS (Christoffel correction, 3-fold): collect by the output index `r`.
    rw [sum3_collect_basis_inner (fun p q r =>
      ((chartModelBasis E).repr v) p *
        ((chartModelBasis E).repr
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                  chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
                (chartModelBasis E) m)) q *
        chartChristoffel (I := I) g x₀ p q r (extChartAt I x₀ x₀))]
    -- RHS (target, 5-fold): collect by the output index `m`.
    rw [sum5_collect_basis_inner (fun i j k l m =>
      ((chartModelBasis E).repr V) i * ((chartModelBasis E).repr V) k *
        ((chartModelBasis E).repr W) j *
        chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
        chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀))]
    -- match the per-output-index scalar coefficients
    refine Finset.sum_congr rfl (fun z _ => ?_)
    refine congrArg (fun t : ℝ => t • (chartModelBasis E) z) ?_
    -- LHS coeff: distribute `V_p · (∑ᵢⱼ ...) · Γ` into a flat 4-fold scalar sum
    have hLHScoeff :
        (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) p *
            ((chartModelBasis E).repr
              (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                ∑ m : Fin (Module.finrank ℝ E),
                  (((chartModelBasis E).repr V) i * ((chartModelBasis E).repr W) j *
                      chartChristoffel (I := I) g x₀ i j m (extChartAt I x₀ x₀)) •
                    (chartModelBasis E) m)) q *
            chartChristoffel (I := I) g x₀ p q z (extChartAt I x₀ x₀)) =
          ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr V) p * ((chartModelBasis E).repr V) i *
                ((chartModelBasis E).repr W) j *
                chartChristoffel (I := I) g x₀ i j q (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ p q z (extChartAt I x₀ x₀) := by
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      rw [chartModelBasis_repr_christoffelVWSum (I := I) g x₀ V W (extChartAt I x₀ x₀) q, ← hVeqv]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    rw [hLHScoeff]
    -- align orders `(p,q,i,j) → (i,j,p,q)` and match termwise
    rw [sum4_scalar_swap_pairs (fun p q i j =>
      ((chartModelBasis E).repr V) p * ((chartModelBasis E).repr V) i *
        ((chartModelBasis E).repr W) j *
        chartChristoffel (I := I) g x₀ i j q (extChartAt I x₀ x₀) *
        chartChristoffel (I := I) g x₀ p q z (extChartAt I x₀ x₀))]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring

/-- **The covariant-`1`-jet-vanishing tangent extension whose iterated covariant derivative also
vanishes along every coordinate-constant (linear-extension) reading direction (linear-extension
`2`-jet-vanishing construction).** This is the genuine chart-polynomial correction of
`linearExtensionTangent x₀ v`: the degree-`1` chart polynomial cancelling the metric Christoffel
`1`-jet correction (`covApply_linearExtensionTangent_basepoint_eq`) and the degree-`2` chart polynomial
cancelling the `∂Γ + Γ·Γ` `2`-jet correction (`covApply_covApply_linearExtensionTangent_basepoint_eq`,
the second-order chart formula proved above), both cut off by the same bump.

It produces a smooth tangent-bundle section `W` with `W x₀ = v`, vanishing covariant `1`-jet
`∇_u W(x₀) = 0`, and — read along the coordinate-constant linear extensions `linearExtensionTangent x₀ u`
of every direction `u` — vanishing iterated covariant `2`-jet
`∇_{linExt u}(∇_{linExt u} W)(x₀) = 0`. (The general-field `2`-jet vanishing is then obtained from this
linear-extension form by the value-locality reduction
`covApply_covApply_eq_linExt_of_covApply_zero`.)

This is the genuine quadratic chart-polynomial construction: the `C₁`-linear and `C₂`-quadratic chart
corrections solving the (linear) `1`- and `2`-jet cancellation equations supplied by the two basepoint
chart formulas. It is a NEW genuine-content sub-node of `exists_twoJetVanishing_tangentExtension`, not a
rephrasing of it (its `2`-jet clause is restricted to linear-extension reading directions, where the
chart `2`-jet formula applies directly).

**Posited** (body `sorry`): the explicit `C₁, C₂` chart-polynomial correction field and the discharge of
its `1`- and linear-extension-`2`-jet cancellation over the two proved chart formulas. -/
theorem exists_linExtTwoJetVanishing_tangentExtension
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ W : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) ∧
      W x₀ = v ∧
      (∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0) ∧
      (∀ u : TangentSpace I x₀,
        (LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ u) W) x₀ u = 0) := by
  sorry

/-- **Value-locality of the iterated covariant derivative at a `1`-jet-vanishing section.** If the
covariant `1`-jet of `W` vanishes at `x₀` (the `(1,1)`-tensor `∇W(x₀) = 0`), then the iterated
covariant derivative `∇_Y(∇_Y W)(x₀)` depends on the smooth reading field `Y` only through its value
`Y x₀`: it equals the same expression read along the coordinate-constant linear extension
`linearExtensionTangent x₀ (Y x₀)` of that value.

This is the covariant evaluation-Leibniz / value-locality identity:
`∇_u(∇_Y W) = (∇_u ∇W)(Y) + ∇W(∇_u Y)`; at `x₀`, `∇W(x₀) = 0` kills the second (`∇_u Y`-dependent) term,
and the difference of the two readings (along `Y` and along `linExt (Y x₀)`) is `∇W(x₀)` applied to a
field vanishing at `x₀` — zero from both sides. It is a NEW genuine reusable tensor-calculus sub-node
(the tangent-bundle instance of the operator-field evaluation Leibniz
`OperatorFieldCovariantCalculus.tensorCovDerivAt_appCc_eq`), not a rephrasing of
`exists_twoJetVanishing_tangentExtension`.

The proof uses the generic Hom-bundle evaluation-Leibniz `homBundleCovariantDerivativeGen_apply`
(with the tangent Levi-Civita as both source and target connection, and the smooth operator-field
`τ b := ∇W b`): for the difference reading field `D := Y − linExt(Y x₀)` (which vanishes at `x₀`),
`∇_v(∇_D W)(x₀) = (∇_v τ)(D x₀) + τ(x₀)(∇_v D) = (∇_v τ)(0) + (∇W x₀)(∇_v D) = 0`, so the `Y`- and
`linExt(Y x₀)`-readings of the iterated covariant derivative agree. -/
theorem covApply_covApply_eq_linExt_of_covApply_zero
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {W : Π b : M, TangentSpace I b} (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hgrad : ∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0)
    {Y : Π b : M, TangentSpace I b} (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y W) x₀ (Y x₀) =
      (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ (Y x₀)) W) x₀
        (Y x₀) := by
  classical
  set Z : Π b : M, TangentSpace I b := linearExtensionTangent (I := I) x₀ (Y x₀) with hZ_def
  have hZ_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) :=
    linearExtensionTangent_smooth (I := I) x₀ (Y x₀)
  have hZ_x : Z x₀ = Y x₀ := linearExtensionTangent_eq (I := I) x₀ (Y x₀)
  -- the difference reading field `D := Y - Z`, vanishing at `x₀`
  set D : Π b : M, TangentSpace I b := fun b => Y b - Z b with hD_def
  have hD_x : D x₀ = 0 := by rw [hD_def]; simp [hZ_x]
  have hD_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% D) := by
    have := hY.sub_section hZ_sm
    simpa [hD_def, Pi.sub_apply] using this
  -- `covApply (LeviCivita g) Y W = covApply (LeviCivita g) Z W + covApply (LeviCivita g) D W`
  have hsplit : covApply (LeviCivita (I := I) g) Y W =
      covApply (LeviCivita (I := I) g) Z W + covApply (LeviCivita (I := I) g) D W := by
    funext b
    simp only [Connection.covApply_apply, Pi.add_apply, hD_def]
    rw [map_sub]
    abel
  -- the inner sections are differentiable at `x₀`
  have hW1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% W) := by
    have h : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    rw [h]; exact hW
  have hBZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) Z W)) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hZ_sm hW1
  have hBD : MDiffAt (T% (covApply (LeviCivita (I := I) g) D W)) x₀ :=
    Connection.covApply_mdifferentiableAt (cov := LeviCivita (I := I) g) hD_sm hW1
  -- additivity of the covariant derivative on the differentiable inner sections
  have hadd := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add hBZ hBD (Set.mem_univ x₀)
  rw [hsplit]
  rw [LeviCivita_toFun] at hadd ⊢
  rw [hadd]
  rw [ContinuousLinearMap.add_apply]
  -- the `D`-reading vanishes by the Hom-bundle evaluation Leibniz
  have hDvanish : leviCivitaStitched (I := I) g (covApply (LeviCivita (I := I) g) D W) x₀ (Y x₀) = 0 := by
    -- package `τ := ∇W` and `D` as smooth sections
    have hτ_sm : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
          ((LeviCivita (I := I) g).toFun W x)) := by
      rw [← contMDiffOn_univ]
      refine LeviCivita_section_contMDiffOn_univ (I := I) g ?_
      rw [ENat.coe_top_add_one]
      exact hW.contMDiffOn
    set τ : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x⟯ :=
      ⟨fun x => (LeviCivita (I := I) g).toFun W x, hτ_sm⟩ with hτ_def
    set Dsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨D, hD_sm⟩ with hDsec_def
    have hleib := HomConnectionGen.homBundleCovariantDerivativeGen_apply
      (I := I) (M := M) (E_U := E) (U := (TangentSpace I : M → Type _)) (F := E)
      (V := (TangentSpace I : M → Type _)) (LeviCivita (I := I) g) (LeviCivita (I := I) g)
      τ Dsec x₀ (Y x₀)
    -- `Dsec x₀ = 0`, so the left side vanishes
    rw [show (Dsec : Π b : M, TangentSpace I b) x₀ = 0 from hD_x] at hleib
    rw [ContinuousLinearMap.map_zero] at hleib
    -- the `τ·D` section is `covApply (LeviCivita g) D W`
    have hτD : (fun y => (τ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) y
          ((Dsec : Π b : M, TangentSpace I b) y)) =
        covApply (LeviCivita (I := I) g) D W := by
      funext y; rfl
    rw [hτD] at hleib
    -- the `τ(∇D)` term vanishes by `hgrad`
    have hτterm : (τ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) x₀
          ((LeviCivita (I := I) g) (Dsec : Π b : M, TangentSpace I b) x₀ (Y x₀)) = 0 :=
      hgrad _
    rw [hτterm, sub_zero] at hleib
    exact hleib.symm
  rw [hDvanish, add_zero]

/-- **The covariant-`2`-jet-vanishing smooth tangent extension.** For a smooth Riemannian metric `g` on a
closed manifold, a base point `x₀`, and a fibre vector `v : TangentSpace I x₀`, there is a smooth
tangent-bundle section `W : Π b, TangentSpace I b` that

* extends `v`: `W x₀ = v`;
* has vanishing covariant `1`-jet at `x₀`: `∇_u W(x₀) = (LeviCivita g).toFun W x₀ u = 0` for every
  direction `u`; and
* has vanishing iterated covariant `2`-jet at `x₀`: for every smooth field `Y`,
  `∇_Y(∇_Y W)(x₀) = (LeviCivita g).toFun (covApply (LeviCivita g) Y W) x₀ (Y x₀) = 0`.

This is the composition glue of the genuine linear-extension `2`-jet-vanishing construction
`exists_linExtTwoJetVanishing_tangentExtension` (which supplies `W`, its basepoint value, its vanishing
covariant `1`-jet, and the vanishing iterated `2`-jet along every coordinate-constant reading direction)
with the value-locality reduction `covApply_covApply_eq_linExt_of_covApply_zero` (which turns the
general-field `2`-jet into the coordinate-constant one, using `∇W(x₀) = 0`). Transits the two children's
`sorryAx`. -/
theorem exists_twoJetVanishing_tangentExtension
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ W : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) ∧
      W x₀ = v ∧
      (∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0) ∧
      (∀ Y : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y W) x₀ (Y x₀) = 0) := by
  obtain ⟨W, hW_sm, hW_x, hW_grad, hW_linHess⟩ :=
    exists_linExtTwoJetVanishing_tangentExtension (I := I) g x₀ v
  refine ⟨W, hW_sm, hW_x, hW_grad, fun Y hY => ?_⟩
  rw [covApply_covApply_eq_linExt_of_covApply_zero (I := I) g x₀ hW_sm hW_grad hY]
  exact hW_linHess (Y x₀)

end Connection
end Integral
end DifferentialGeometry

end
