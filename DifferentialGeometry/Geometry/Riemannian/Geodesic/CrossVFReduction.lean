import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.GeodesicEquationBridge
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ChartTransition
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option linter.unusedSectionVars false

/-!
# Cross-chart-basepoint reduction for the geodesic vector field

This file packages the cross-VF reduction bridge: an integral curve of the
chart-fixed geodesic vector field at one basepoint `α` is, on the overlap of
chart sources, also an integral curve of the chart-fixed geodesic vector field
at a different basepoint `α'`. Combined with chart-fixed Picard–Lindelöf
existence and uniqueness, this yields the unconditional
`IsGeodesicAt → HasGeodesicEquationAt` bridge.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Spray-invariance: chart-`α` vs basepoint-free geodesic vector field

The technical core of the cross-basepoint reduction. We must show that the
second (fibre) component of the chart-`α` geodesic vector field, written in
the canonical `E × E` representation of `TangentSpace I.tangent p`, coincides
with the chart-`p.proj` Christoffel acceleration `-Γ_{p.proj}(p.snd, p.snd)`.

The plan, recorded as the helper lemmas below:

1. `tangentCoordChange_eq_chartTransitionAt`: identify the manifold Jacobian
   `tangentCoordChange I x y z` with the chart-level Jacobian
   `chartTransitionAt x y (extChartAt I x z)` (boundaryless, so
   `fderivWithin (range I) = fderiv`).
2. `secondaryTrivSndForm_eventuallyEq_applyJac`: near the chart base point,
   the closed-form fibre map `secondaryTrivSndForm α p` agrees with the
   "apply the chart-`p.proj`→`α` Jacobian to the velocity slot" map
   `z ↦ chartTransitionAt p.proj α z.1 z.2`.
3. `fderiv_applyJac_apply`: the Fréchet derivative of that apply-map, by the
   bilinear chain rule (`HasFDerivAt.clm_apply`), splits into the base
   Jacobian on the velocity slot plus the *second-derivative* correction on
   the foot slot.
4. `chartTransitionSecondDeriv_coord`: the foot-slot correction, contracted
   coordinatewise, is exactly the reverse-Jacobian-pulled
   `chartTransitionSecondDerivCorrection`.

Combining these with `chartChristoffelContraction_transform` (the contraction
form of the Christoffel transformation law) discharges the fibre match.
-/

/-- **Manifold Jacobian = chart Jacobian (boundaryless).** Re-derivation of the
identity `tangentCoordChange I x y z = chartTransitionAt x y (extChartAt I x z)`
on the chart overlap. -/
private lemma tangentCoordChange_eq_chartTransitionAt [I.Boundaryless]
    (x y : M) (z : M) :
    tangentCoordChange I x y z =
      chartTransitionAt (I := I) x y (extChartAt I x z) := by
  rw [tangentCoordChange_def, chartTransitionAt_def, chartTransitionMap_def]
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

/-- The "apply the chart-`p.proj`→`α` Jacobian to the velocity slot" map.
This is the closed form of the fibre block of the iterated-tangent transition
near the chart base point. -/
private def applyJac (α : M) (p : TangentBundle I M) (z : E × E) : E :=
  chartTransitionAt (I := I) p.proj α z.1 z.2

/-- Near the chart base point, `secondaryTrivSndForm α p` agrees with
`applyJac α p`. -/
private lemma secondaryTrivSndForm_eventuallyEq_applyJac [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    secondaryTrivSndForm (I := I) α p =ᶠ[𝓝 ((extChartAt I.tangent p) p)]
      applyJac (I := I) α p := by
  classical
  -- The first component of `extChartAt I.tangent p p` is `extChartAt I p.proj p.proj`.
  have hbp1 : ((extChartAt I.tangent p) p).1 = extChartAt I p.proj p.proj :=
    extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  -- The open set `{z | z.1 ∈ target ∧ (extChartAt I p.proj).symm z.1 ∈ chartAt H α source}`.
  set U : Set (E × E) :=
    {z : E × E | z.1 ∈ (extChartAt I p.proj).target ∧
      (extChartAt I p.proj).symm z.1 ∈ (chartAt H α).source} with hU_def
  have hUopen : IsOpen U := by
    have h1 : IsOpen ((extChartAt I p.proj).target) :=
      isOpen_extChartAt_target (I := I) p.proj
    have hcont : ContinuousOn (extChartAt I p.proj).symm (extChartAt I p.proj).target :=
      continuousOn_extChartAt_symm (I := I) p.proj
    -- `U = (Prod.fst ⁻¹' target) ∩ (Prod.fst ⁻¹' (symm ⁻¹' source))`, all open.
    have hset : U = (Prod.fst ⁻¹' (extChartAt I p.proj).target) ∩
        (Prod.fst ⁻¹' ((extChartAt I p.proj).target ∩
          (extChartAt I p.proj).symm ⁻¹' (chartAt H α).source)) := by
      ext z
      simp only [hU_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    rw [hset]
    refine (h1.preimage continuous_fst).inter ((IsOpen.preimage continuous_fst) ?_)
    exact hcont.isOpen_inter_preimage h1 (chartAt H α).open_source
  have hbp_memU : ((extChartAt I.tangent p) p) ∈ U := by
    rw [hU_def, Set.mem_setOf_eq, hbp1]
    refine ⟨(extChartAt I p.proj).map_source (mem_extChartAt_source (I := I) p.proj), ?_⟩
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source (I := I) p.proj)]
    exact hp
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hbp_memU) ?_
  intro z hz
  obtain ⟨hz_tgt, hz_src⟩ := hz
  -- `secondaryTrivSndForm α p z = tangentCoordChange I p.proj α (symm z.1) z.2`.
  unfold secondaryTrivSndForm applyJac
  -- Bridge `tangentCoordChange` → `chartTransitionAt`, then `extChartAt I p.proj (symm z.1) = z.1`.
  rw [tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α ((extChartAt I p.proj).symm z.1)]
  congr 2
  exact (extChartAt I p.proj).right_inv hz_tgt

/-- `applyJac` is differentiable at the chart base point: the foot-Jacobian
`fderiv (chartTransitionMap p.proj α)` is differentiable there. -/
private lemma differentiableAt_chartTransitionAt [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) α β z) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hsmooth : ContDiffOn ℝ ∞ (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E))
      (chartTransitionSource (I := I) α β) :=
    chartTransitionAt_smooth (I := I) α β
  exact (hsmooth.contDiffAt (h_open.mem_nhds hx)).differentiableAt (by simp)

/-- **Fréchet derivative of the apply-Jacobian map.** By the bilinear chain
rule, `fderiv (applyJac α p) bp (a, b) =
  chartTransitionAt p.proj α x₀ b + (fderiv (chartTransitionAt p.proj α ·) x₀ a) v₀`,
where `x₀ = bp.1`, `v₀ = bp.2`. -/
private lemma fderiv_applyJac_apply [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    fderiv ℝ (applyJac (I := I) α p) ((extChartAt I.tangent p) p) w =
      chartTransitionAt (I := I) p.proj α ((extChartAt I.tangent p) p).1 w.2 +
        (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          ((extChartAt I.tangent p) p).1 w.1) (((extChartAt I.tangent p) p).2) := by
  classical
  set bp := (extChartAt I.tangent p) p with hbp
  -- Source membership of `bp.1 = x₀` for the chart transition `p.proj → α`.
  have hbp1 : bp.1 = extChartAt I p.proj p.proj := by
    rw [hbp]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  have hx_src : bp.1 ∈ chartTransitionSource (I := I) p.proj α := by
    rw [hbp1]
    exact extChartAt_mem_chartTransitionSource (I := I) p.proj α
      (mem_chart_source H p.proj) hp
  -- `applyJac α p z = (c z) (u z)` with `c z = chartTransitionAt p.proj α z.1`, `u z = z.2`.
  set c : E × E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z.1 with hc
  set u : E × E → E := fun z => z.2 with hu
  -- `c` is differentiable at `bp` (composition with `fst`).
  have hcA : DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1 :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_src
  have hc_diff : DifferentiableAt ℝ c bp :=
    hcA.comp bp (differentiableAt_fst)
  have hu_diff : DifferentiableAt ℝ u bp := differentiableAt_snd
  -- The clm_apply fderiv formula.
  have hfd : fderiv ℝ (fun z => (c z) (u z)) bp =
      (c bp).comp (fderiv ℝ u bp) + (fderiv ℝ c bp).flip (u bp) :=
    fderiv_clm_apply hc_diff hu_diff
  -- `applyJac α p = fun z => (c z) (u z)`.
  have happly_eq : applyJac (I := I) α p = fun z => (c z) (u z) := by
    funext z; rfl
  rw [happly_eq, hfd]
  -- Evaluate at `w`.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  -- `fderiv u bp w = w.2`, since `u = snd`.
  have hu_fderiv : fderiv ℝ u bp = ContinuousLinearMap.snd ℝ E E := fderiv_snd
  rw [hu_fderiv]
  -- `fderiv c bp w = (fderiv A bp.1) w.1` where A = chartTransitionAt p.proj α (·).
  have hc_fderiv : fderiv ℝ c bp w =
      (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1) (w.1) := by
    have hceq : c = (fun x => chartTransitionAt (I := I) p.proj α x) ∘ Prod.fst := by
      funext z; rfl
    rw [hceq]
    rw [fderiv_comp bp hcA differentiableAt_fst]
    simp only [ContinuousLinearMap.comp_apply, fderiv_fst, ContinuousLinearMap.coe_fst']
  rw [hc_fderiv]
  -- `c bp (w.2) = chartTransitionAt p.proj α bp.1 w.2` and `u bp = bp.2`.
  rfl

/-- **Coordinate form of the foot-slot second-derivative correction.** The
`c`-th chart coordinate of the foot-slot derivative
`(fderiv (chartTransitionAt p.proj α ·) x₀ v) v` is the symmetric
second-derivative sum `∑_{i,j} (∂_i J^c_j x₀) vⁱ vʲ`, where
`J = chartTransitionJacEntry p.proj α`. -/
private lemma chartCoord_fderiv_chartTransitionAt [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (c : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoord (E := E) c
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          (extChartAt I p.proj p.proj) v) v) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) p.proj α z c j)
          (extChartAt I p.proj p.proj) *
          chartCoord (E := E) i v * chartCoord (E := E) j v := by
  classical
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set A : E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z with hA
  have hx_src : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
    extChartAt_mem_chartTransitionSource (I := I) p.proj α (mem_chart_source H p.proj) hp
  have hcA : DifferentiableAt ℝ A x₀ :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_src
  -- The evaluation CLM `eval : (E →L E) →L ℝ`, `L ↦ chartCoord c (L v)`.
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord c) with hcoordCLM
  set eval : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp (ContinuousLinearMap.apply ℝ E v) with heval
  -- `chartCoord c ((fderiv A x₀ v) v) = eval (fderiv A x₀ v)`.
  have hstep1 :
      chartCoord (E := E) c ((fderiv ℝ A x₀ v) v) = eval (fderiv ℝ A x₀ v) := by
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    rfl
  -- `eval (fderiv A x₀ v) = fderiv (eval ∘ A) x₀ v` (eval is a CLM).
  have hstep2 : eval (fderiv ℝ A x₀ v) = fderiv ℝ (fun z => eval (A z)) x₀ v := by
    have hcomp_hasD : HasFDerivAt (fun z => eval (A z))
        (eval.comp (fderiv ℝ A x₀)) x₀ :=
      eval.hasFDerivAt.comp x₀ hcA.hasFDerivAt
    rw [hcomp_hasD.fderiv]
    rfl
  -- `eval (A z) = chartCoord c (chartTransitionAt p.proj α z v) = ∑_i J^c_i(z) vⁱ`.
  have heval_eq : (fun z => eval (A z)) =
      (fun z => ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) p.proj α z c i * chartCoord (E := E) i v) := by
    funext z
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, hA,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    change chartCoord (E := E) c (chartTransitionAt (I := I) p.proj α z v) = _
    exact chartCoord_chartTransitionAt (I := I) p.proj α z v c
  rw [hstep1, hstep2, heval_eq]
  -- Differentiate the finite sum: linearity of fderiv across the Finset.sum.
  -- Each `z ↦ J^c_i(z) * vⁱ` is differentiable; `vⁱ` is a constant scalar.
  have hsum_fderiv :
      fderiv ℝ (fun z => ∑ i : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) p.proj α z c i * chartCoord (E := E) i v) x₀ v =
        ∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
            chartCoord (E := E) i v) x₀ v := by
    have hdiff : ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
          chartCoord (E := E) i v) x₀ := by
      intro i
      exact (chartTransitionJacEntry_differentiableAt (I := I) p.proj α c i hx_src).mul_const _
    rw [fderiv_fun_sum (fun i _ => hdiff i)]
    rw [ContinuousLinearMap.sum_apply]
  rw [hsum_fderiv]
  -- Each summand: `fderiv (J^c_i · vⁱ) x₀ v = (fderiv J^c_i x₀ v) · vⁱ`,
  -- and `fderiv J^c_i x₀ v = ∑_k vᵏ ∂_k J^c_i x₀`.
  -- After expansion, LHS = ∑_i (∑_k vᵏ ∂_k J^c_i) · vⁱ = ∑_i ∑_k ∂_k J^c_i · vᵏ · vⁱ.
  have hLHS_expand :
      (∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
            chartCoord (E := E) i v) x₀ v) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) p.proj α z c i) x₀ *
            chartCoord (E := E) k v * chartCoord (E := E) i v := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_mul_const (chartTransitionJacEntry_differentiableAt (I := I) p.proj α c i hx_src) _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) p.proj α c i x₀ v]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hLHS_expand]
  -- Reindex: ∑_i ∑_k ∂_k J^c_i vᵏ vⁱ = ∑_i ∑_j ∂_i J^c_j vⁱ vʲ (swap the two sums
  -- and rename (i,k) ↦ (j,i)).
  rw [Finset.sum_comm]

/-- **Pointwise chart-invariance of the geodesic spray.** At a tangent-bundle
point `p` whose foot `p.proj` lies in the chart-source at `α`, the chart-`α`
fixed geodesic vector field coincides with the basepoint-free geodesic vector
field `geodesicVectorField g p` (built in the chart centred at `p.proj`).

The first component already coincides by `geodesicVectorFieldChart_fst`
(both equal `p.snd`). The second component is the genuine content: the
chart-`α` Christoffel acceleration, pushed through the second-tangent-bundle
chart transition from `α`-coordinates to `p.proj`-coordinates, equals the
chart-`p.proj` Christoffel acceleration. This is the non-tensorial
transformation law of the Christoffel symbols (`chartChristoffelContraction_transform`)
together with the velocity-Jacobian correction encoded by the `snd`-block of
the iterated tangent-bundle transition derivative. -/
theorem geodesicVectorFieldChart_eq_geodesicVectorField
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = geodesicVectorField (I := I) g p := by
  classical
  -- Abbreviations.
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set bp := (extChartAt I.tangent p) p with hbp
  -- `bp.1 = x₀`, `bp.2 = p.snd`.
  have hbp1 : bp.1 = x₀ := by
    rw [hbp, hx₀]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  have hbp2 : bp.2 = (p.snd : E) := by
    rw [hbp]
    rw [extChartAt_tangent_apply_snd_tangentCoordChange (I := I) (q := p) (p := p)
      (mem_chart_source H p.proj)]
    exact tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj) (v := p.snd)
      (mem_extChartAt_source (I := I) p.proj)
  -- The two vector fields agree iff their `E × E` components agree.
  -- The `.1` agreement is `geodesicVectorFieldChart_fst`.
  have hfst : (geodesicVectorFieldChart (I := I) g α p : E × E).1 =
      (geodesicVectorField (I := I) g p : E × E).1 := by
    rw [geodesicVectorFieldChart_fst (I := I) g α hp]
    rfl
  -- The `.2` agreement: this is the technical core.
  have hsnd : (geodesicVectorFieldChart (I := I) g α p : E × E).2 =
      (geodesicVectorField (I := I) g p : E × E).2 := by
    -- Set `X := (gvfChart g α p).2` (the unknown).
    set X := (geodesicVectorFieldChart (I := I) g α p : E × E).2 with hX
    -- `(gvfChart g α p).1 = p.snd`.
    have hgvf1 : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = (p.snd : E) :=
      geodesicVectorFieldChart_fst (I := I) g α hp
    -- Step A. From the trivialisation identity, the secondary CLM applied to
    -- `gvfChart` returns `gvfFiber`.  Take `.2`.
    have hp_dom : p ∈ geodesicChartDomain (I := I) α := hp
    have htriv := trivializationAt_apply_geodesicVectorFieldChart
      (I := I) g α (p := p) hp_dom
    set e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
    have hp_base : p ∈ e.baseSet := by
      rw [he_def, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp_dom
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hp_base
    have hlin_at_gvf :
        (e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) =
          geodesicVectorFieldChartFiber (I := I) g α p := by
      have h2 := congrArg Prod.snd htriv
      change (e.linearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) = _
      have hh := congrFun hcoe (geodesicVectorFieldChart (I := I) g α p)
      rw [hh]; exact h2
    -- `.2` of the CLM-applied form, via `snd_continuousLinearMapAt_secondaryTriv`.
    have hsnd_clm :
        ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).2 =
          (fderivWithin ℝ (secondaryTrivSndForm (I := I) α p) (range I.tangent) bp)
            (geodesicVectorFieldChart (I := I) g α p) :=
      snd_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
        (geodesicVectorFieldChart (I := I) g α p)
    -- Combine: `(gvfFiber).2 = fderivWithin(...) (gvfChart)`.
    have hkey0 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        (fderivWithin ℝ (secondaryTrivSndForm (I := I) α p) (range I.tangent) bp)
          (geodesicVectorFieldChart (I := I) g α p) := by
      rw [← hsnd_clm, hlin_at_gvf]
    -- Step B. Replace `fderivWithin (range I.tangent)` by `fderiv` (boundaryless),
    -- and `secondaryTrivSndForm` by `applyJac` near `bp`.
    have hrangeT : (range (I.tangent) : Set (E × E)) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)
    have hfderiv_eq :
        fderivWithin ℝ (secondaryTrivSndForm (I := I) α p) (range I.tangent) bp =
          fderiv ℝ (applyJac (I := I) α p) bp := by
      rw [hrangeT, fderivWithin_univ]
      exact Filter.EventuallyEq.fderiv_eq
        (secondaryTrivSndForm_eventuallyEq_applyJac (I := I) α hp)
    rw [hfderiv_eq] at hkey0
    -- Step C. Apply the fderiv formula. `gvfChart = (p.snd, X)`.
    have hfderiv_apply :
        fderiv ℝ (applyJac (I := I) α p) bp (geodesicVectorFieldChart (I := I) g α p) =
          chartTransitionAt (I := I) p.proj α x₀ X +
            (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀ (p.snd : E))
              (p.snd : E) := by
      have := fderiv_applyJac_apply (I := I) α hp (geodesicVectorFieldChart (I := I) g α p)
      rw [this, hbp1, hbp2, hgvf1]
    rw [hfderiv_apply] at hkey0
    -- Now `hkey0 : (gvfFiber).2 = chartTransitionAt p.proj α x₀ X + Dterm`,
    -- where `Dterm := (fderiv (chartTransitionAt p.proj α ·) x₀ p.snd) p.snd`.
    set Dterm : E := (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀
      (p.snd : E)) (p.snd : E) with hDterm
    -- `(gvfFiber).2 = -Γ_α(v, v)(extChartAt I α p.proj)`, with `v = chartFiberCoord α p`.
    set v := chartFiberCoord (I := I) α p with hv
    have hfiber2 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        - chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj) := rfl
    rw [hfiber2] at hkey0
    -- Step D. The Christoffel transformation law (contraction form), with
    -- roles `α := p.proj`, `β := α`, base point `p.proj`.
    have htransform :
        chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ =
          chartTransitionAt (I := I) α p.proj
              (chartTransitionMap (I := I) p.proj α x₀)
              (chartChristoffelContraction (I := I) g α
                (chartTransitionAt (I := I) p.proj α x₀ (p.snd))
                (chartTransitionAt (I := I) p.proj α x₀ (p.snd))
                (chartTransitionMap (I := I) p.proj α x₀))
            + chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      have := chartChristoffelContraction_transform (I := I) g p.proj α
        (p := p.proj) (mem_chart_source H p.proj) hp (p.snd) (p.snd)
      rw [hx₀]; exact this
    -- Identify the pieces inside `htransform`.
    -- `chartTransitionMap p.proj α x₀ = extChartAt I α p.proj`.
    have hTx₀ : chartTransitionMap (I := I) p.proj α x₀ = extChartAt I α p.proj := by
      rw [hx₀]
      exact chartTransitionMap_apply_extChartAt (I := I) p.proj α (mem_chart_source H p.proj)
    -- `chartTransitionAt p.proj α x₀ p.snd = v = chartFiberCoord α p`.
    have hJsnd : chartTransitionAt (I := I) p.proj α x₀ (p.snd) = v := by
      rw [hv, hx₀, ← tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α p.proj]
      exact (chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp).symm
    rw [hTx₀, hJsnd] at htransform
    -- Now `htransform : Γ_{p.proj}(p.snd,p.snd)(x₀) =
    --   chartTransitionAt α p.proj (extChartAt I α p.proj) (Γ_α(v,v)(extChartAt I α p.proj))
    --     + chartTransitionSecondDerivCorrection p.proj α p.snd p.snd x₀`.
    -- Step E. The reverse-Jacobian pull of the foot-slot derivative term `Dterm`
    -- equals the `chartTransitionSecondDerivCorrection`.
    have hcorr :
        chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm =
          chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      -- Both sides are vectors in `E`; compare coordinatewise.
      refine (chartModelBasis E).ext_elem (fun k => ?_)
      -- LHS coordinate `k`: `∑_c K^k_c · chartCoord c Dterm`, with `K = J(α→p.proj)`.
      -- RHS coordinate `k`: `∑_c K^k_c · (∑_{ij} ∂_i J'^c_j x₀ vⁱ vʲ)`, `J' = J(p.proj→α)`.
      -- Use `chartCoord_chartTransitionAt` on LHS, the def on RHS, and the
      -- coordinate identity for `Dterm`.
      change chartCoord (E := E) k
          (chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm) =
        chartCoord (E := E) k
          (chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀)
      rw [chartCoord_chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm k]
      rw [chartTransitionSecondDerivCorrection_def]
      -- RHS: `chartCoord k (∑_k' (coeff k') • e_{k'}) = coeff k`.
      rw [show chartCoord (E := E) k
          (∑ k' : Fin (Module.finrank ℝ E),
            (∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k' c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i
                    (fun z => chartTransitionJacEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i (p.snd) * chartCoord (E := E) j (p.snd))) •
              chartModelBasis E k') =
          ∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i
                    (fun z => chartTransitionJacEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i (p.snd) * chartCoord (E := E) j (p.snd)) from ?_]
      · -- LHS coordinate sum, with `chartCoord c Dterm` expanded.
        rw [hTx₀]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hDterm, chartCoord_fderiv_chartTransitionAt (I := I) α hp c (p.snd)]
      · -- The chart coordinate of a basis expansion: `repr (∑ a • e_a) k = a_k`.
        rw [chartCoord_def, map_sum, Finsupp.finset_sum_apply]
        rw [Finset.sum_eq_single k]
        · rw [map_smul, Finsupp.smul_apply, (chartModelBasis E).repr_self k,
            Finsupp.single_eq_same, smul_eq_mul, mul_one]
        · intro k' _ hk'
          rw [map_smul, Finsupp.smul_apply, (chartModelBasis E).repr_self k']
          rw [Finsupp.single_eq_of_ne (Ne.symm hk'), smul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
    -- Step F. Apply the reverse Jacobian `chartTransitionAt α p.proj (extChartAt I α p.proj)`
    -- to both sides of `hkey0` and solve for `X`.
    -- Source membership for the inverse-collapse identities.
    have hx_src : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
      extChartAt_mem_chartTransitionSource (I := I) p.proj α (mem_chart_source H p.proj) hp
    -- `chartTransitionAt α p.proj (extChartAt I α p.proj) ∘ chartTransitionAt p.proj α x₀ = id`.
    have hinv : chartTransitionAt (I := I) α p.proj
        (chartTransitionMap (I := I) p.proj α x₀)
        (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      have hcomp := chartTransitionAt_comp_chartTransitionAt (I := I) p.proj α hx_src
      have := congrArg (fun L : E →L[ℝ] E => L X) hcomp
      simpa using this
    -- Apply the reverse Jacobian to `hkey0`.
    set RJ : E →L[ℝ] E := chartTransitionAt (I := I) α p.proj
      (chartTransitionMap (I := I) p.proj α x₀) with hRJ
    have happ := congrArg (fun y => RJ y) hkey0
    simp only at happ
    -- LHS: `RJ (-Γ_α(v,v)(...))`. RHS: `RJ (chartTransitionAt p.proj α x₀ X + Dterm)`.
    rw [map_add] at happ
    -- `RJ (chartTransitionAt p.proj α x₀ X) = X` via `hinv` (note `extChartAt I α p.proj = Tx₀`).
    have hRJ_X : RJ (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      rw [hRJ]; exact hinv
    rw [hRJ_X] at happ
    -- `RJ Dterm = chartTransitionSecondDerivCorrection ...` via `hcorr` (with `Tx₀`).
    have hRJ_D : RJ Dterm =
        chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      rw [hRJ, hTx₀]; exact hcorr
    rw [hRJ_D] at happ
    -- `happ : RJ (-Γ_α(v,v)(extChartAt I α p.proj)) = X + correction`.
    -- LHS: `RJ (-Γ_α(...)) = -RJ(Γ_α(...))`.
    rw [map_neg] at happ
    -- From `htransform`: `RJ (Γ_α(v,v)(...)) = Γ_{p.proj}(p.snd,p.snd)(x₀) - correction`.
    have hRJ_Gamma :
        RJ (chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj)) =
          chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ -
            chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      rw [hRJ, hTx₀]
      rw [eq_sub_iff_add_eq]
      exact htransform.symm
    rw [hRJ_Gamma] at happ
    -- `happ : -(Γ_{p.proj}(p.snd,p.snd)(x₀) - correction) = X + correction`.
    -- Solve: `X = -Γ_{p.proj}(p.snd,p.snd)(x₀)`.
    have hXval : X = - chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ := by
      -- `-(Γ - correction) = correction - Γ = -Γ + correction`, then cancel `correction`.
      rw [neg_sub, sub_eq_neg_add] at happ
      -- `happ : (-Γ) + correction = X + correction`.
      exact (add_right_cancel happ).symm
    -- Conclude: the goal is `X = (gvfField g p).2` (LHS folded by `set X`).
    rw [hXval, geodesicVectorField_snd]
  -- Assemble the two components into the `E × E` equality.
  apply Prod.ext hfst hsnd

/-- **Cross-basepoint pointwise coincidence of the chart-fixed geodesic vector
field.** At a tangent-bundle point `p` whose foot lies in both chart-sources,
the chart-`α` and chart-`α'` fixed geodesic vector fields agree as elements of
`T_p(TM)`. Both equal the basepoint-free geodesic spray
`geodesicVectorField g p` by `geodesicVectorFieldChart_eq_geodesicVectorField`. -/
theorem geodesicVectorFieldChart_eq_of_proj_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hα' : p.proj ∈ (chartAt H α').source) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g α' p := by
  rw [geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α hα,
    geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α' hα']

/-- **Cross-basepoint coincidence of the chart-fixed geodesic vector field on
integral curves.** A curve which is a local integral curve at `t₀` of the
chart-fixed geodesic vector field at one basepoint `α` is also a local
integral curve at `t₀` of the chart-fixed geodesic vector field at a
different basepoint `α'`, provided the projection of the curve at `t₀` lies
in both chart sources. -/
theorem bm_c_gc_vf_chart_coincidence
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hα : (f t₀).proj ∈ (chartAt H α).source)
    (hα' : (f t₀).proj ∈ (chartAt H α').source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α') t₀ := by
  classical
  -- The base projection is continuous at `t₀` (integral curves are continuous).
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_contAt : ContinuousAt f t₀ := hf.continuousAt
  have hproj_contAt : ContinuousAt (fun t => (f t).proj) t₀ :=
    hπ_cont.continuousAt.comp hf_contAt
  -- Eventually `(f t).proj ∈ (chartAt H α).source`.
  have hα_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα)
  -- Eventually `(f t).proj ∈ (chartAt H α').source`.
  have hα'_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α').source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α').open_source.mem_nhds hα')
  -- Transfer the `HasMFDerivAt` clause: the two vector fields agree where both
  -- foot-membership conditions hold.
  unfold IsMIntegralCurveAt at hf ⊢
  filter_upwards [hf, hα_nhds, hα'_nhds] with t htD ht_α ht_α'
  have ht_α2 : (f t).proj ∈ (chartAt H α).source := ht_α
  have ht_α'2 : (f t).proj ∈ (chartAt H α').source := ht_α'
  have hvf_eq : geodesicVectorFieldChart (I := I) g α (f t) =
      geodesicVectorFieldChart (I := I) g α' (f t) :=
    geodesicVectorFieldChart_eq_of_proj_mem (I := I) g α α' (p := f t) ht_α2 ht_α'2
  exact hvf_eq ▸ htD

/-- **Cross-VF projection-uniqueness for `IsGeodesicAt`.** From an
`IsGeodesicAt`-witness `(α, f)` of `γ` at `t₀`, construct a
chart-`γ(t₀)`-centred local integral curve `f₁` of the chart-fixed geodesic
vector field at `γ(t₀)` whose projection agrees with `γ` on a neighbourhood
of `t₀`. -/
theorem bm_c_gc_cross_vf_projection_uniqueness
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t₀).proj = γ t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ ∧
      γ =ᶠ[𝓝 t₀] (fun t => (f₁ t).proj) := by
  classical
  -- Unpack the `IsGeodesicAt` witness: chart basepoint `α`, lift `f`, and
  -- the foot-in-source clause `hα_src : (f t₀).proj ∈ (chartAt H α).source`.
  obtain ⟨α, f, hproj, hα_src, hf⟩ := hγ
  -- `(f t₀).proj = γ t₀`.
  have hft₀ : (f t₀).proj = γ t₀ := hproj t₀
  -- `(f t₀).proj` lies in the chart-source at `γ t₀` (its own chart).
  have hγt₀_src : (f t₀).proj ∈ (chartAt H (γ t₀)).source := by
    rw [hft₀]; exact mem_chart_source H (γ t₀)
  -- Build the chart-`γ(t₀)`-centred lift through the same initial tangent vector
  -- `(f t₀).snd`. Picard–Lindelöf gives the integral curve.
  obtain ⟨f₁, hf₁_init, hf₁⟩ :=
    exists_chartCenteredLift_at (I := I) g (γ t₀) ((f t₀).snd : E) t₀
  -- `(f₁ t₀).proj = γ t₀`.
  have hf₁_proj : (f₁ t₀).proj = γ t₀ := by rw [hf₁_init]
  refine ⟨f₁, hf₁_proj, hf₁, ?_⟩
  -- Move the witness `f`'s integral-curve property to basepoint `γ t₀` via the
  -- cross-basepoint coincidence, then compare with `f₁` by uniqueness.
  have hf_at_γ : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ :=
    bm_c_gc_vf_chart_coincidence (I := I) g α (γ t₀) hα_src hγt₀_src hf
  -- `f t₀ = f₁ t₀`: both are `⟨γ t₀, (f t₀).snd⟩` (foot equality + same velocity).
  have h0 : f₁ t₀ = f t₀ := by
    rw [hf₁_init]
    -- `⟨γ t₀, (f t₀).snd⟩ = f t₀` since `(f t₀).proj = γ t₀` and `f t₀ = ⟨(f t₀).proj, (f t₀).snd⟩`.
    rw [← hft₀]
  -- Uniqueness on `TM` at basepoint `γ t₀`: `f₁ =ᶠ f`.
  have hfe : f₁ =ᶠ[𝓝 t₀] f := by
    have hsrc₁ : (f₁ t₀).proj ∈ (chartAt H (γ t₀)).source := by
      rw [hf₁_proj]; exact mem_chart_source H (γ t₀)
    exact isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := γ t₀) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f) hsrc₁ hf₁ hf_at_γ h0
  -- Project the eventual equality: `γ t = (f t).proj = (f₁ t).proj`.
  filter_upwards [hfe] with t ht
  -- `ht : f₁ t = f t`; goal `γ t = (f₁ t).proj`.
  rw [ht, hproj t]

/-- **Unconditional bridge `IsGeodesicAt → HasGeodesicEquationAt`.** A local
geodesic at `t₀` satisfies the chart-coordinate second-derivative form of the
geodesic equation at `t₀`. -/
theorem IsGeodesicAt.hasGeodesicEquationAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f₁, hf₁_proj_t₀, hf₁, hcross⟩ :=
    bm_c_gc_cross_vf_projection_uniqueness (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ
  exact IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ (f₁ := f₁) hf₁ hf₁_proj_t₀ hcross

/-! ## Gluing two geodesic arcs at a matching limit point

The moving-foot geodesic equation `HasGeodesicEquationAt g γ t` is a *local*
property of `γ` at `t`: it references `γ` only through
`chartLocalCurve γ t s = extChartAt I (γ t) (γ s)`, so two curves agreeing on a
neighbourhood of `t` (with equal basepoint at `t`) satisfy it simultaneously
(`HasGeodesicEquationAt.congr_of_eventuallyEq_at`). This locality lets us glue a
left-arc geodesic `γ` (defined on `Iio T`) to a right-arc geodesic `η` (defined
on `Ioo (-δ) δ`) at the matching limit point `T`, producing a geodesic on
`Iio (T + δ)`. The match hypothesis pins down the agreement of `γ` with the
shifted right-arc `s ↦ η (s - T)` approaching `T` from the left.
-/

/-- **Per-time time-translation of the moving-foot geodesic equation.** If `η`
satisfies the geodesic equation at `t - T`, then the constant-time-translated
curve `s ↦ η (s - T)` satisfies it at `t`. At base time `t`, the chart-local
curve of the translated curve is the chart-local curve of `η` at `t - T`
precomposed with the shift `· - T`, so the two `HasDerivAt` clauses transfer via
`HasDerivAt.comp_sub_const` (derivatives are unchanged under domain translation)
and the algebraic Christoffel identity is preserved because the foot point and
velocity coincide. -/
private lemma hasGeodesicEquationAt_comp_sub_const
    {g : SmoothRiemannianMetric I M} {η : ℝ → M} {T t : ℝ}
    (h : HasGeodesicEquationAt (I := I) g η (t - T)) :
    HasGeodesicEquationAt (I := I) g (fun s => η (s - T)) t := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := h
  have hshift : chartLocalCurve (I := I) (fun s => η (s - T)) t =
      fun s => chartLocalCurve (I := I) η (t - T) (s - T) := by funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]; exact hv.comp_sub_const t T
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => chartLocalCurve (I := I) η (t - T) (s - T)) s =
          deriv (chartLocalCurve (I := I) η (t - T)) (s - T) := fun s =>
      deriv_comp_sub_const (chartLocalCurve (I := I) η (t - T)) T s
    have hev' : ∀ᶠ s in nhds t, HasDerivAt
        (chartLocalCurve (I := I) η (t - T))
        (deriv (chartLocalCurve (I := I) η (t - T)) (s - T)) (s - T) :=
      ((continuous_sub_right T).continuousAt).eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]; exact hs.comp_sub_const s T
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => chartLocalCurve (I := I) η (t - T) (s - T)) s) =
        fun s => deriv (chartLocalCurve (I := I) η (t - T)) (s - T) := by
      funext s; exact deriv_comp_sub_const (chartLocalCurve (I := I) η (t - T)) T s
    rw [hd2]; exact ha.comp_sub_const t T
  · exact hgeo

/-- **Gluing two geodesic arcs at a matching limit point.** Let `γ` be a
geodesic on `Iio T` and `η` a geodesic on `Ioo (-δ) δ` (`δ > 0`), and suppose
`γ` agrees with the shifted right-arc `s ↦ η (s - T)` on a punctured-left
neighbourhood of `T` (i.e. in `𝓝[<] T`). Then the curve obtained by following
`γ` left of `T` and the shifted `η` at and right of `T` is a geodesic on
`Iio (T + δ)`.

The proof is a pointwise check of the moving-foot geodesic equation on the glued
curve `G`. For `t < T` the curve `G` agrees with `γ` on a neighbourhood of `t`,
for `t > T` it agrees with `s ↦ η (s - T)` on a neighbourhood of `t`, and at the
matching point `t = T` it agrees with `s ↦ η (s - T)` on a full neighbourhood of
`T` (assembling the left side via the match hypothesis and the right side
directly through `nhdsLT_sup_nhdsGE`). In every case the equation transfers from
the relevant genuine geodesic by the locality lemma
`HasGeodesicEquationAt.congr_of_eventuallyEq_at`, with the right-arc data
supplied by `hasGeodesicEquationAt_comp_sub_const`. -/
theorem isGeodesicOn_glue_at_limit [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    {γ η : ℝ → M} {T δ : ℝ} (hδ : 0 < δ)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    IsGeodesicOn (I := I) g (fun t => if t < T then γ t else η (t - T))
      (Set.Iio (T + δ)) := by
  classical
  set G : ℝ → M := fun t => if t < T then γ t else η (t - T) with hG
  set ηT : ℝ → M := fun s => η (s - T) with hηT
  -- `G` agrees with `γ` on `𝓝[<] T` and with `ηT` on `𝓝[≥] T`.
  have hGγ_lt : G =ᶠ[𝓝[<] T] γ :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG]; rw [if_pos (mem_Iio.mp ht)])
  have hGηT_ge : G =ᶠ[𝓝[≥] T] ηT :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG, hηT]; rw [if_neg (not_lt.mpr (mem_Ici.mp ht))])
  -- Hence `G` agrees with `ηT` from the left (via the match), assembling to a
  -- full `𝓝 T` agreement.
  have hGηT_lt : G =ᶠ[𝓝[<] T] ηT := hGγ_lt.trans hmatch
  have hGηT_T : G =ᶠ[𝓝 T] ηT := by
    rw [← nhdsLT_sup_nhdsGE T, Filter.EventuallyEq, eventually_sup]
    exact ⟨hGηT_lt, hGηT_ge⟩
  -- Pointwise check of the geodesic equation on `Iio (T + δ)`.
  intro t ht
  rw [mem_Iio] at ht
  rcases lt_trichotomy t T with hlt | heq | hgt
  · -- `t < T`: glue agrees with `γ` near `t`; use `hγ`.
    have hGγ_t : G =ᶠ[𝓝 t] γ :=
      Filter.eventually_of_mem ((isOpen_Iio).mem_nhds hlt)
        (fun s hs => by simp only [hG]; rw [if_pos (mem_Iio.mp hs)])
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := γ) ?_ hGγ_t ?_
    · simp only [hG]; rw [if_pos hlt]
    · exact hγ t (mem_Iio.mpr hlt)
  · -- `t = T`: glue agrees with `ηT` on a full neighbourhood; use shifted `hη`.
    subst heq
    have hmem0 : t - t ∈ Set.Ioo (-δ) δ := by
      rw [sub_self]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - t) hmem0)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_T hηeq
    simp only [hG, hηT]; rw [if_neg (lt_irrefl t)]
  · -- `t > T`: glue agrees with `ηT` near `t`; use shifted `hη`.
    have hGηT_t : G =ᶠ[𝓝 t] ηT :=
      Filter.eventually_of_mem ((isOpen_Ioi).mem_nhds hgt)
        (fun s hs => by
          simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))])
    have hmem : t - T ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - T) hmem)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_t hηeq
    simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt hgt))]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
