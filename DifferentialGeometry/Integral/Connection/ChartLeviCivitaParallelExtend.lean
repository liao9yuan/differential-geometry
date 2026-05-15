import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.LeviCivitaChartTorsion

/-!
# Chart Levi-Civita applied to a chart-parallel-extended vector

Given a smooth Riemannian metric `g`, a chart center `α : M`, a basepoint `b : M`
in the chart Levi-Civita good set, a tangent vector `v ∈ TangentSpace I b` and a
tangent vector field `X`, this file establishes that

  `chartLeviCivita g α (chartParallelExtend α b v) b (X b)
    = trivFromE α b (christoffelCorrection g α b (trivToE α b v) (X b))`.

In other words, when the section input to `chartLeviCivita` is the chart-α-parallel
extension of a single tangent vector `v`, the Fréchet-derivative term in the
chart Levi-Civita formula vanishes (because the chart-trivialised representation
of `chartParallelExtend α b v` is locally constant on the trivialisation base
set), and only the Christoffel-correction term survives.

## Main results

* `chartParallelExtend_repr_eventuallyEq_const`: the chart-trivialised
  representation of `chartParallelExtend α b v`, pulled back through
  `(extChartAt I α).symm`, is eventually equal to the constant
  `trivToE α b v ∈ E` in a neighbourhood of `extChartAt I α b`.
* `chartParallelExtend_repr_pullback_fderiv_eq_zero`: as a consequence, the
  Fréchet derivative of `chartE_section_repr α (chartParallelExtend α b v) ∘
  (extChartAt I α).symm` at `extChartAt I α b` is zero.
* `chartLeviCivita_chartParallelExtend`: the headline identity, reducing
  `chartLeviCivita g α (chartParallelExtend α b v) b (X b)` to the pure
  Christoffel correction.
* `chartLeviCivita_chartParallelExtend_symm`: the same identity expressed in
  the swapped form (using torsion-free symmetry of the Christoffel correction).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Local-constancy of the chart pullback

The chart-trivialised representation of `chartParallelExtend α b v` is the
constant value `trivToE α b v ∈ E` on the trivialisation base set
`(trivializationAt E (TangentSpace I) α).baseSet`. After composition with
`(extChartAt I α).symm`, this stays constant on the preimage of the base set,
which is a neighbourhood of `extChartAt I α b` whenever `b` lies in the good
set. -/

/-- **Local constancy of the chart pullback.** For `b` in the chart Levi-Civita
good set, the chart-trivialised representation of `chartParallelExtend α b v`,
pulled back through `(extChartAt I α).symm`, is eventually equal to the
constant `trivToE α b v` in a neighbourhood of `extChartAt I α b`. -/
lemma chartParallelExtend_repr_eventuallyEq_const
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    (chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v)) ∘ (extChartAt I α).symm
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun _ : E => trivToE (I := I) α b v) := by
  classical
  -- The trivialisation base set is open in `M`.
  set U : Set M := (trivializationAt E (TangentSpace I) α).baseSet with hU_def
  have hU_open : IsOpen U :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  -- `b ∈ U` from the good-set membership.
  have hb_U : b ∈ U :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  -- `b ∈ extChartAt I α source`.
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  -- `extChartAt I α b ∈ interior of the target`.
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  -- The interior of the chart target is open and contains `extChartAt I α b`.
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  -- `(extChartAt I α).symm` is continuous at `extChartAt I α b` (the chart
  -- image is in the interior of the chart target).
  have hsymm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α b) :=
    continuousAt_extChartAt_symm' hb_src
  -- The preimage of `U` under `(extChartAt I α).symm` is a neighbourhood of
  -- `extChartAt I α b`.
  have hU_preim_nhds :
      (extChartAt I α).symm ⁻¹' U ∈ 𝓝 (extChartAt I α b) := by
    apply hsymm_cont.preimage_mem_nhds
    -- Need: `U ∈ 𝓝 ((extChartAt I α).symm (extChartAt I α b))`.
    -- `(extChartAt I α).symm (extChartAt I α b) = b` since `b` is in the source.
    have hxφ_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv hb_src
    rw [hxφ_inv]
    exact hU_open.mem_nhds hb_U
  -- The interior of the chart target is a neighbourhood of `extChartAt I α b`.
  have hint_nhds : interior ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α b) :=
    hint_open.mem_nhds hb_int
  -- On the intersection of these two neighbourhoods, the chart pullback of
  -- `chartE_section_repr α (chartParallelExtend α b v)` is constant.
  filter_upwards [hU_preim_nhds, hint_nhds] with y hy_U hy_int
  -- We need to show:
  -- `chartE_section_repr α (chartParallelExtend α b v) ((extChartAt I α).symm y)
  --   = trivToE α b v`.
  -- Since `(extChartAt I α).symm y ∈ U` (i.e., in the trivialisation base set),
  -- we apply `chartE_section_repr_chartParallelExtend`.
  change chartE_section_repr (I := I) α (chartParallelExtend (I := I) α b v)
      ((extChartAt I α).symm y) = trivToE (I := I) α b v
  exact chartE_section_repr_chartParallelExtend (I := I) α b v hy_U

/-! ## Vanishing of the Fréchet derivative

The chart pullback of the chart-trivialised representation of
`chartParallelExtend α b v` is locally constant, so its Fréchet derivative at
`extChartAt I α b` is zero. -/

/-- **Vanishing Fréchet derivative.** For `b` in the chart Levi-Civita good
set, the Fréchet derivative at `extChartAt I α b` of
`chartE_section_repr α (chartParallelExtend α b v) ∘ (extChartAt I α).symm`
is the zero CLM. -/
lemma chartParallelExtend_repr_pullback_fderiv_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    fderiv ℝ (chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
      (extChartAt I α b) = 0 := by
  classical
  -- Use the local-constancy fact to rewrite the fderiv.
  have hev :=
    chartParallelExtend_repr_eventuallyEq_const (I := I) α hb v
  rw [Filter.EventuallyEq.fderiv_eq hev]
  -- `fderiv` of a constant function is zero.
  exact fderiv_const_apply _

/-- **Vanishing Fréchet derivative, applied form.** Applying the zero CLM to
any tangent vector argument gives zero. -/
lemma chartParallelExtend_repr_pullback_fderiv_apply_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) (w : E) :
    fderiv ℝ (chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
      (extChartAt I α b) w = 0 := by
  rw [chartParallelExtend_repr_pullback_fderiv_eq_zero (I := I) α hb v]
  rfl

/-! ## The headline identity

With the Fréchet-derivative term gone, the chart Levi-Civita formula on
`chartParallelExtend α b v` reduces to the pure Christoffel-correction term.
The chart-trivialised representation at `b` is `trivToE α b v` (by
`chartE_section_repr_chartParallelExtend` with `b' = b ∈ baseSet`). -/

/-- **Chart Levi-Civita on a chart-parallel-extended vector reduces to the
Christoffel correction.** For `b` in the chart Levi-Civita good set, the chart
Levi-Civita derivative of `chartParallelExtend α b v` at `b` along `X b`
equals the chart-α Christoffel correction transported back to the tangent
space. -/
theorem chartLeviCivita_chartParallelExtend
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    chartLeviCivita (I := I) g α (chartParallelExtend (I := I) α b v) b (X b) =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b v) (X b)) := by
  classical
  -- Apply `chartLeviCivita_apply` at the good-set point.
  rw [chartLeviCivita_apply (I := I) g α
        (chartParallelExtend (I := I) α b v) hb (X b)]
  -- Identify the chart-trivialised representation of the parallel extension
  -- at `b` with `trivToE α b v` (using that `b ∈ baseSet`).
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hrepr :
      chartE_section_repr (I := I) α (chartParallelExtend (I := I) α b v) b =
        trivToE (I := I) α b v :=
    chartE_section_repr_chartParallelExtend (I := I) α b v hb_base
  -- The Fréchet derivative term vanishes by local constancy.
  have hfderiv :
      fderiv ℝ (chartE_section_repr (I := I) α
          (chartParallelExtend (I := I) α b v) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b)) = 0 :=
    chartParallelExtend_repr_pullback_fderiv_apply_eq_zero
      (I := I) α hb v (trivToE (I := I) α b (X b))
  -- Substitute both facts.
  rw [hfderiv, hrepr]
  -- Goal: `trivFromE α b (0 + christoffelCorrection g α b (trivToE α b v) (X b))`
  --     = `trivFromE α b (christoffelCorrection g α b (trivToE α b v) (X b))`.
  rw [zero_add]

/-! ### Symmetric form via Christoffel-symmetry cancellation

Using `christoffelCorrection_symm_cancel` (the torsion-free Christoffel
symmetry), the right-hand side can be re-expressed with the roles of the
section value `v` and the direction `X b` swapped. -/

/-- **Symmetric form of the headline identity.** Using torsion-free Christoffel
symmetry, the same identity can be expressed with the input vector `v` in the
CLM-argument position. -/
theorem chartLeviCivita_chartParallelExtend_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    chartLeviCivita (I := I) g α (chartParallelExtend (I := I) α b v) b (X b) =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v) := by
  classical
  rw [chartLeviCivita_chartParallelExtend (I := I) g α hb v X]
  -- Apply `christoffelCorrection_symm_cancel` with `w := v` and `v := X b`.
  congr 1
  exact (christoffelCorrection_symm_cancel (I := I) g α b v (X b)).symm

/-! ## Differentiability of the chart-parallel extension as a bundle section

The chart-parallel extension `b' ↦ chartParallelExtend α b v b'` is the constant
trivialised representation `trivToE α b v` on the trivialisation base set, hence
its total-space form is smooth (in particular, differentiable) on the base set. -/

/-- **Manifold-differentiability of `chartParallelExtend α b v` as a section** at
the basepoint `b`, on the chart Levi-Civita good set. The proof uses the fact
that the chart-trivialised representation of the parallel extension is
constantly equal to `trivToE α b v` on the trivialisation base set, and then
applies the section-differentiability criterion through the trivialisation. -/
lemma chartParallelExtend_mdifferentiableAt
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b' : M => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) b'
        (chartParallelExtend (I := I) α b v b')) b := by
  classical
  -- The trivialisation at α witnesses the section-differentiability.
  set e := trivializationAt E (TangentSpace I) α with he_def
  -- `b ∈ e.baseSet` from the good-set membership.
  have hb_base : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  -- The base set is open.
  have hbase_open : IsOpen e.baseSet := e.open_baseSet
  -- The base set is in `𝓝 b`.
  have hbase_nhds : e.baseSet ∈ 𝓝 b := hbase_open.mem_nhds hb_base
  -- The trivialised representation is locally the constant `trivToE α b v`.
  have hconst :
      (fun b' : M => (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2) =ᶠ[𝓝 b]
        (fun _ : M => trivToE (I := I) α b v) := by
    filter_upwards [hbase_nhds] with b' hb'
    -- `(e ⟨b', s b'⟩).2 = e.continuousLinearMapAt ℝ b' (s b')` on baseSet.
    -- First, `(e ⟨b', y⟩).2 = trivToE α b' y` on baseSet.
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := b') hb'
    have happ := congrFun hcoe (chartParallelExtend (I := I) α b v b')
    -- `happ : (e.linearMapAt ℝ b') (chartParallelExtend α b v b') =
    --        (e ⟨b', chartParallelExtend α b v b'⟩).2`
    change (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2 = trivToE (I := I) α b v
    rw [← happ]
    -- `(e.linearMapAt ℝ b') y = trivToE α b' y` definitionally
    -- (`trivToE := e.continuousLinearMapAt ℝ`, and `continuousLinearMapAt.toFun = linearMapAt`).
    change (trivToE (I := I) α b') (chartParallelExtend (I := I) α b v b') = trivToE (I := I) α b v
    -- `chartParallelExtend α b v b' = trivFromE α b' (trivToE α b v)`.
    change (trivToE (I := I) α b') (trivFromE (I := I) α b' (trivToE (I := I) α b v)) =
      trivToE (I := I) α b v
    exact trivToE_trivFromE (I := I) α hb' _
  -- The constant function is differentiable; transfer to the repr via `congr_of_eventuallyEq`.
  have hrep_diff :
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun b' : M => (e ⟨b', chartParallelExtend (I := I) α b v b'⟩).2) b :=
    (mdifferentiableAt_const (c := trivToE (I := I) α b v)).congr_of_eventuallyEq hconst
  -- Transfer through the section-differentiability iff.
  exact (Trivialization.mdifferentiableAt_section_iff (IB := I) e
    (fun b' : M => chartParallelExtend (I := I) α b v b') hb_base).mpr hrep_diff

end Connection
end Integral
end DifferentialGeometry
