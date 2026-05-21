import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberForwardOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Pointwise bound on the chart-trivialised first covariant derivative by the
chart-frame scalar components and their chart-coordinate Fréchet derivative

For a smooth Riemannian manifold `(M, g)` modelled on `(E, H)` with model `I`,
a chart-centre `α : M`, a fixed smooth tangent vector field `B`, and a smooth
compactly-supported `(r, s)`-tensor section `T`, this file ships a pointwise
upper bound for the model-fiber norm of the chart-α-trivialised
representation of the section
`covApply cov_RS B T = b ↦ cov_RS T b (B b)`,
in terms of the chart-coordinate Fréchet derivative and the pointwise values of
the scalar chart-frame components of `T`.

Concretely, on the chart-α partition-of-unity tsupport, for every smooth
compactly-supported `(r, s)`-tensor section `T`, the bound takes the form

  `‖tensorRSChartE_section_repr r s α (covApply cov_RS B T) b‖
      ≤ K * ∑_{Idx, Jdx}
          (‖fderiv ℝ (tensorChartComponentRaw g r s T α Idx Jdx ∘
              (extChartAt I α).symm) (extChartAt I α b)‖
            + |tensorChartComponentRaw g r s T α Idx Jdx b|)`

with `K` depending only on the metric `g`, the chart at `α`, the locality
hypothesis, the ranks `r`, `s`, and on `B`; in particular `K` is independent
of `T`.

## Strategy

1. Use the chart-frame agreement `chartTensorRSCovariantDerivative_eq_abstract`
   to identify `covApply cov_RS B T b` with the chart-frame value
   `chartTensorRSCovariantDerivative r s g α T.toSection.toFun B.toFun b` on
   the chart-α Levi-Civita good set (which contains the POU tsupport under
   `[I.Boundaryless]`).
2. Pass through the forward fiber op-norm bound
   `tensorRSChartFiberToModel_opNorm_isBounded_on_compact` to bound the
   model-fiber norm of `tensorRSChartE_section_repr r s α (covApply ...) b`
   by a constant times the fiber norm of `covApply ... b`.
3. Apply the chart-frame op-norm bound
   `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport` to bound the
   fiber norm of `chartTensorRSCovariantDerivative r s g α T B b` by

       `C * MX(B, b) * (‖fderiv (repr T ∘ symm)(extChartAt b)‖ * ‖B b‖ + ‖T b‖)`.

4. `‖B b‖` and `MX(B, b)` are bounded uniformly over the POU tsupport because
   `B` is smooth and the POU tsupport is compact.
5. Decompose `repr T = Σ_{Idx, Jdx} comp(repr T) • basis-elt`. Linearity of
   `fderiv` gives

       `fderiv (repr T ∘ symm) = Σ_{Idx, Jdx} fderiv (comp(repr T) ∘ symm) ⊗ basis-elt`.

   The bound on its operator norm by `Σ_{Idx, Jdx} ‖fderiv(scalar comp ∘ symm)‖
   * ‖basis-elt‖` follows from `norm_sum_le` and `ContinuousLinearMap.smulRight`.
6. The reverse fiber bound `tensorRSSpace_norm_le_chartRepr_norm_on_compact`
   bounds `‖T b‖` by a constant times `‖repr T b‖`, which is then bounded by
   `Σ_{Idx, Jdx} |comp(repr T b)| * ‖basis-elt‖` via the basis recovery
   `tensorRSModel_eq_sum_basis`. Each `comp(repr T b)` equals
   `tensorChartComponentRaw g r s T α Idx Jdx b` by definition.
7. Combine and absorb all uniform constants into a single `K`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Pointwise decomposition of `‖repr T b‖` by chart-frame components -/

/-- The model-fiber norm of the chart-α-trivialised representation of a smooth
compactly-supported `(r, s)`-tensor section at `b` is bounded by the sum of the
absolute values of its chart-frame components, times the basis-element norm
constant. -/
lemma reprNorm_le_sum_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M) :
    ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b| *
            tensorChartBasisNormConstant (E := E) r s := by
  classical
  set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
    r s α (fun y : M => T.toSection y) b with hR_def
  have hR_recover : R =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComponentProjection (E := E) r s Idx Jdx R •
            tensorChartBasisElement (E := E) r s Idx Jdx :=
    tensorRSModel_eq_sum_basis (E := E) r s R
  have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComponentProjection (E := E) r s Idx Jdx R =
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
    intro Idx Jdx
    rw [tensorChartComponentRaw_def]
    rfl
  change ‖R‖ ≤ _
  rw [hR_recover]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [norm_smul, Real.norm_eq_abs, hcomp_eq Idx Jdx]
  exact mul_le_mul_of_nonneg_left
    (tensorChartBasisElement_norm_le (E := E) r s Idx Jdx)
    (abs_nonneg _)

/-! ## Differentiability of chart-pulled scalar components -/

/-- Each chart-frame scalar component pulled by `(extChartAt I α).symm` is
Fréchet-differentiable at the chart-coord image of any chart-source point. -/
private lemma chart_pulled_component_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α b) := by
  classical
  -- Smoothness on chart source.
  have hsmooth_on := tensorChartComponentRaw_contMDiffOn_chart_source
    (I := I) (M := M) g r s T α Idx Jdx
  -- Compose with `(extChartAt I α).symm` (smooth on the chart target into
  -- the chart source).
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro y hy
    have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hsmooth_on.comp hsymm hmaps
  -- `extChartAt I α b ∈ (extChartAt I α).target`.
  have hb_src : b ∈ (extChartAt I α).source :=
    (extChartAt_source (I := I) α).symm ▸ hb_chart
  have hb_target : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have h_open_target : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  -- Promote ContMDiffOn → ContDiffOn on the open chart target, then to
  -- DifferentiableAt at `extChartAt I α b`.
  have hcontDiffOn : ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hcomp.contDiffOn
  have hcdAt : ContDiffWithinAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α).target (extChartAt I α b) :=
    hcontDiffOn _ hb_target
  have hwithin : DifferentiableWithinAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α).target (extChartAt I α b) :=
    hcdAt.differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open_target.mem_nhds hb_target)

/-! ## Pointwise decomposition of `‖fderiv(repr T ∘ symm)‖` by component
fderivs -/

/-- The chart-coordinate Fréchet derivative of the chart-pulled
chart-α-trivialised representation of `T.toSection` at the chart-coord point
`extChartAt I α b` has operator norm bounded by

  `Σ_{Idx, Jdx} ‖fderiv ℝ (component_Idx_Jdx ∘ symm) (extChartAt b)‖
                  * ‖basis-elt(Idx, Jdx)‖`. -/
private lemma fderiv_repr_opNorm_le_sum_fderiv_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source) :
    ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) (extChartAt I α b)‖ *
            ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ := by
  classical
  -- Rewrite the chart-pulled `repr` as a finite sum of `(scalar ∘ symm) • basis`.
  have hψ_eq :
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) =
        fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
    funext y
    set bb := (extChartAt I α).symm y
    set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
      r s α (fun z : M => T.toSection z) bb
    have hR_recover : R =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx R •
              tensorChartBasisElement (E := E) r s Idx Jdx :=
      tensorRSModel_eq_sum_basis (E := E) r s R
    have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx R =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx bb := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def]
      rfl
    change R = _
    rw [hR_recover]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [hcomp_eq Idx Jdx]
    rfl
  rw [hψ_eq]
  -- Differentiability of each scalar summand at the chart-coord point.
  have hdiff_each := fun Idx Jdx =>
    chart_pulled_component_differentiableAt (I := I) (M := M)
      g r s T α Idx Jdx hb_chart
  -- fderiv distributes over a finite sum, then each summand uses
  -- `fderiv_smul_const`.
  have hfderiv_sum :
      fderiv ℝ
        (fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
        (extChartAt I α b) =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          fderiv ℝ
            (fun y : E =>
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
            (extChartAt I α b) := by
    have hd_inner : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
          DifferentiableAt ℝ
            (fun y : E =>
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
            (extChartAt I α b) := fun Idx Jdx => (hdiff_each Idx Jdx).smul_const _
    have hd_inner_sum : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ
          (fun y : E => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
              tensorChartBasisElement (E := E) r s Idx Jdx)
          (extChartAt I α b) := fun Idx =>
      DifferentiableAt.fun_sum (fun Jdx _ => hd_inner Idx Jdx)
    rw [fderiv_fun_sum (fun Idx _ => hd_inner_sum Idx)]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    exact fderiv_fun_sum (fun Jdx _ => hd_inner Idx Jdx)
  rw [hfderiv_sum]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [fderiv_smul_const (hdiff_each Idx Jdx)]
  rw [ContinuousLinearMap.norm_smulRight_apply]

/-! ## Headline -/

/-- **Headline bound.** For a smooth Riemannian manifold `(M, g)`, a chart-
centre `α : M`, a smooth tangent vector field `B`, and a smooth compactly-
supported `(r, s)`-tensor section `T`, the model-fiber norm of the chart-α-
trivialised representation of the first covariant derivative
`covApply cov_RS B T = b ↦ cov_RS T b (B b)` at every point `b` of the chart-α
partition-of-unity tsupport is bounded by a constant times the sum, over the
multi-index pairs `(Idx, Jdx) : (Fin r → Fin n) × (Fin s → Fin n)`, of the
chart-coordinate Fréchet derivative of the chart-pulled scalar chart-frame
`(Idx, Jdx)`-component of `T` plus the absolute value of the chart-frame
`(Idx, Jdx)`-component of `T` at `b`.

The constant `K` depends only on the metric `g`, the chart at `α`, the locality
hypothesis, the ranks `r`, `s`, and on the fixed vector field `B`; it is
independent of `T` and `b`. -/
theorem chart_pulled_covApply_cov_repr_norm_le_chartComp_data
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) B.toFun
              (fun y : M => T.toSection y)) b‖ ≤
          K * ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M)
                    g r s T α Idx Jdx ∘ (extChartAt I α).symm)
                  (extChartAt I α b)‖ +
                |tensorChartComponentRaw (I := I) (M := M)
                  g r s T α Idx Jdx b|) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- Constant 1: forward fiber op-norm bound `‖triv.cLMA b‖ ≤ C_fwd`.
  obtain ⟨C_fwd, hCfwd_pos, hCfwd_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact
      (I := I) (M := M) (h_atlas := h_atlas) (r := r) (s := s) (α := α)
      (hK := hK_compact) (hKsub := hK_sub)
  have hCfwd_nn : 0 ≤ C_fwd := le_of_lt hCfwd_pos
  -- Constant 2: reverse fiber bound `‖T b‖ ≤ C_rev * ‖triv.cLMA b T‖`.
  obtain ⟨C_rev, hCrev_pos, hCrev_bound⟩ :=
    tensorRSSpace_norm_le_chartRepr_norm_on_compact
      (I := I) (M := M) (h_atlas := h_atlas) (r := r) (s := s) (α := α)
      (hK := hK_compact) (hKsub := hK_sub)
  have hCrev_nn : 0 ≤ C_rev := le_of_lt hCrev_pos
  -- Constant 3: chart-frame cov-derivative op-norm bound.
  obtain ⟨C_cov, hCcov_nn, hCcov_bound⟩ :=
    chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
      (I := I) (M := M) h_atlas g r s α
  -- Constant 4: uniform bound on `‖B.toFun b‖` over K_set via
  -- `chartJinv = trivFromE` op-norm + continuity of
  -- `chartE_section_repr α B.toFun` on the chart source.
  obtain ⟨C_Jinv, hCJinv_pos, hCJinv_bound⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub
  have hCJinv_nn : 0 ≤ C_Jinv := le_of_lt hCJinv_pos
  obtain ⟨C_B, hCB_nn, hCB_bound⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K_set,
      ‖B.toFun b‖ ≤ C := by
    have hsection_cm : ContMDiffOn I (𝓘(ℝ, E)) ∞
        (chartE_section_repr (I := I) α B.toFun) (chartAt H α).source := by
      have hsmooth_total :
          ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun x : M => TotalSpace.mk' E
              (E := fun y : M => TangentSpace I y) x (B.toFun x)) :=
        B.contMDiff
      have hbase : (trivializationAt E (TangentSpace I) α).baseSet =
          (chartAt H α).source :=
        TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
      have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
        (e := trivializationAt E (TangentSpace I) α)).mp
          hsmooth_total.contMDiffOn
      rw [hbase] at hrewrite
      refine ContMDiffOn.congr hrewrite ?_
      intro x hx
      have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [hbase]; exact hx
      change (trivializationAt E (TangentSpace I) α).linearMapAt ℝ x
        (B.toFun x) = _
      rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
    have hcont_on : ContinuousOn
        (fun b : M => ‖chartE_section_repr (I := I) α B.toFun b‖) K_set := by
      have hcont := hsection_cm.continuousOn
      exact (continuous_norm.comp_continuousOn hcont).mono hK_sub
    have hbdd_above :
        BddAbove ((fun b : M =>
          ‖chartE_section_repr (I := I) α B.toFun b‖) '' K_set) :=
      hK_compact.bddAbove_image hcont_on
    rcases hbdd_above with ⟨MB, hMB⟩
    refine ⟨C_Jinv * (max MB 0), ?_, ?_⟩
    · exact mul_nonneg hCJinv_nn (le_max_right _ _)
    · intro b hb
      have h_repr_le :
          ‖chartE_section_repr (I := I) α B.toFun b‖ ≤ max MB 0 := by
        have hb_le := hMB ⟨b, hb, rfl⟩
        exact le_trans hb_le (le_max_left _ _)
      have h_inv :
          (trivFromE (I := I) α b)
              (chartE_section_repr (I := I) α B.toFun b) = B.toFun b := by
        have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
          rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
          exact hK_sub hb
        exact trivFromE_trivToE (I := I) α (x := b) hb_base (B.toFun b)
      have h_op : ‖B.toFun b‖ ≤ ‖trivFromE (I := I) α b‖ *
          ‖chartE_section_repr (I := I) α B.toFun b‖ := by
        have h := (trivFromE (I := I) α b).le_opNorm
          (chartE_section_repr (I := I) α B.toFun b)
        rw [h_inv] at h
        exact h
      have hJinv_b : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := hCJinv_bound b hb
      have h_repr_nn : 0 ≤ ‖chartE_section_repr (I := I) α B.toFun b‖ :=
        norm_nonneg _
      have h_chain :
          ‖trivFromE (I := I) α b‖ *
              ‖chartE_section_repr (I := I) α B.toFun b‖ ≤
            C_Jinv * (max MB 0) := by
        have h_a := mul_le_mul_of_nonneg_right hJinv_b h_repr_nn
        have h_b := mul_le_mul_of_nonneg_left h_repr_le hCJinv_nn
        linarith
      linarith
  -- Polynomial factor `MX(B, b) ≤ M_pow`.
  set M_pow : ℝ := (max (1 + C_B) 1) ^ (max r s) with hM_pow_def
  have hM_pow_nn : 0 ≤ M_pow := by
    have : 0 ≤ max (1 + C_B) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  -- Basis-element norm constant.
  set K_basis : ℝ := tensorChartBasisNormConstant (E := E) r s with hK_basis_def
  have hK_basis_nn : 0 ≤ K_basis :=
    tensorChartBasisNormConstant_nonneg (E := E) r s
  -- Headline constant.
  set K_const : ℝ := C_fwd * C_cov * M_pow *
      (max C_B (C_rev) + 1) * (K_basis + 1) with hK_const_def
  have hK_const_nn : 0 ≤ K_const := by
    have h1 : 0 ≤ C_fwd * C_cov := mul_nonneg hCfwd_nn hCcov_nn
    have h2 : 0 ≤ C_fwd * C_cov * M_pow := mul_nonneg h1 hM_pow_nn
    have h3 : 0 ≤ max C_B C_rev + 1 := by
      have : 0 ≤ max C_B C_rev := le_trans hCB_nn (le_max_left _ _)
      linarith
    have h4 : 0 ≤ K_basis + 1 := by linarith
    have h5 : 0 ≤ C_fwd * C_cov * M_pow * (max C_B C_rev + 1) :=
      mul_nonneg h2 h3
    exact mul_nonneg h5 h4
  refine ⟨K_const, hK_const_nn, ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    have h_eq := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
  -- Package the smooth section as a `Cₛ^∞⟮...⟯` element.
  set Tsec : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b : M => TensorRSSpace r s I b⟯ := T.toSection with hTsec_def
  -- Agreement of chart-frame cov derivative with bundled cov derivative.
  have h_agree :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun y : M => Tsec.toFun y) B.toFun b =
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (fun y : M => Tsec.toFun y) b (B.toFun b) :=
    chartTensorRSCovariantDerivative_eq_abstract (I := I) (M := M)
      g r s α Tsec B (b := b) hb_good
  -- Tsec.toFun and T.toSection coincide as functions.
  have hTsec_toFun_eq :
      (fun y : M => Tsec.toFun y) = (fun y : M => T.toSection y) := rfl
  rw [hTsec_toFun_eq] at h_agree
  -- LHS: tensorRSChartE_section_repr ... (covApply ...) b = triv.cLMA b (covApply ... b).
  have h_repr_eq :
      tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun
          (fun y : M => T.toSection y)) b =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun y : M => T.toSection y) b (B.toFun b)) := rfl
  rw [h_repr_eq]
  -- Apply the forward fiber op-norm bound.
  have h_fwd_b := hCfwd_bound b hb
    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (fun y : M => T.toSection y) b (B.toFun b))
  -- Abbreviations.
  set N_F : ℝ := ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ with hN_F_def
  set N_T : ℝ := ‖(fun y : M => T.toSection y) b‖ with hN_T_def
  have hN_F_nn : 0 ≤ N_F := norm_nonneg _
  have hN_T_nn : 0 ≤ N_T := norm_nonneg _
  -- Cov-derivative op-norm bound at b.
  have h_cov_bound :=
    hCcov_bound (b := b) hb (fun y : M => T.toSection y) B.toFun
  -- Rewrite LHS of h_cov_bound to the bundled form via agreement.
  rw [h_agree] at h_cov_bound
  -- Chain the bounds.
  have h_chain1 :
      ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun y : M => T.toSection y) b (B.toFun b)) :
            TensorRSModel r s ℝ E)‖ ≤
        C_fwd * (C_cov * (max (1 + ‖B.toFun b‖) 1) ^ (max r s) *
          (N_F * ‖B.toFun b‖ + N_T)) :=
    le_trans h_fwd_b (mul_le_mul_of_nonneg_left h_cov_bound hCfwd_nn)
  -- Bound `‖B b‖ ≤ C_B`, `MX(B, b) ≤ M_pow`.
  have hBb_le : ‖B.toFun b‖ ≤ C_B := hCB_bound b hb
  have hMX_le :
      (max (1 + ‖B.toFun b‖) 1) ^ (max r s) ≤ M_pow := by
    have h_1plus_le : 1 + ‖B.toFun b‖ ≤ 1 + C_B := by linarith
    have h_max_nn : (0 : ℝ) ≤ max (1 + ‖B.toFun b‖) 1 :=
      le_trans zero_le_one (le_max_right _ _)
    have h_max_le : max (1 + ‖B.toFun b‖) 1 ≤ max (1 + C_B) 1 :=
      max_le_max h_1plus_le (le_refl _)
    exact pow_le_pow_left₀ h_max_nn h_max_le _
  -- Component sum abbreviations (avoid `Σ` as identifier; use `SumF`, `SumT`).
  set SumF : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) (extChartAt I α b)‖
    with hSumF_def
  set SumT : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b|
    with hSumT_def
  have hSumF_nn : 0 ≤ SumF :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => norm_nonneg _))
  have hSumT_nn : 0 ≤ SumT :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => abs_nonneg _))
  -- Bound N_F by `K_basis * SumF`.
  have hN_F_le_basis : N_F ≤ K_basis * SumF := by
    have h := fderiv_repr_opNorm_le_sum_fderiv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart
    rw [← hN_F_def] at h
    refine le_trans h ?_
    rw [hSumF_def, hK_basis_def]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Idx _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Jdx _
    have h_basis_le : ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤
        tensorChartBasisNormConstant (E := E) r s :=
      tensorChartBasisElement_norm_le (E := E) r s Idx Jdx
    have h_fnn : 0 ≤ ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M)
        g r s T α Idx Jdx ∘ (extChartAt I α).symm) (extChartAt I α b)‖ :=
      norm_nonneg _
    rw [mul_comm (tensorChartBasisNormConstant (E := E) r s) _]
    exact mul_le_mul_of_nonneg_left h_basis_le h_fnn
  -- Bound N_T by `C_rev * K_basis * SumT`.
  have hN_T_le_repr : N_T ≤ C_rev * ‖tensorRSChartE_section_repr (I := I)
      r s α (fun y : M => T.toSection y) b‖ := by
    rw [hN_T_def]
    have h := hCrev_bound b hb (T.toSection b)
    change ‖T.toSection b‖ ≤ _
    exact h
  have hN_T_le_components :
      ‖tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b‖ ≤ K_basis * SumT := by
    refine le_trans (reprNorm_le_sum_components (I := I) (M := M) g r s T α b) ?_
    rw [hSumT_def, hK_basis_def]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Idx _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Jdx _
    rw [mul_comm (tensorChartBasisNormConstant (E := E) r s) _]
  have hN_T_chain : N_T ≤ C_rev * K_basis * SumT := by
    have h_step1 : N_T ≤ C_rev * (K_basis * SumT) :=
      hN_T_le_repr.trans (mul_le_mul_of_nonneg_left hN_T_le_components hCrev_nn)
    have h_step2 : C_rev * (K_basis * SumT) = C_rev * K_basis * SumT := by ring
    linarith
  -- Combine `N_F * ‖B b‖ + N_T ≤ K_basis * max(C_B, C_rev) * (SumF + SumT)`.
  have h_inner :
      N_F * ‖B.toFun b‖ + N_T ≤
        K_basis * max C_B (C_rev) * (SumF + SumT) := by
    have h_max_nn : 0 ≤ max C_B C_rev := le_trans hCB_nn (le_max_left _ _)
    have h1 : N_F * ‖B.toFun b‖ ≤ K_basis * max C_B (C_rev) * SumF := by
      have h_a : N_F * ‖B.toFun b‖ ≤ (K_basis * SumF) * C_B := by
        have h_aa : N_F * ‖B.toFun b‖ ≤ (K_basis * SumF) * ‖B.toFun b‖ :=
          mul_le_mul_of_nonneg_right hN_F_le_basis (norm_nonneg _)
        have h_ab : (K_basis * SumF) * ‖B.toFun b‖ ≤ (K_basis * SumF) * C_B :=
          mul_le_mul_of_nonneg_left hBb_le (mul_nonneg hK_basis_nn hSumF_nn)
        linarith
      have h_b : (K_basis * SumF) * C_B ≤ (K_basis * SumF) * max C_B (C_rev) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _)
          (mul_nonneg hK_basis_nn hSumF_nn)
      have h_c : (K_basis * SumF) * max C_B (C_rev) =
          K_basis * max C_B (C_rev) * SumF := by ring
      linarith
    have h2 : N_T ≤ K_basis * max C_B (C_rev) * SumT := by
      have h_a : N_T ≤ K_basis * C_rev * SumT := by
        have h_rew : C_rev * K_basis * SumT = K_basis * C_rev * SumT := by ring
        rw [← h_rew]; exact hN_T_chain
      have h_b : K_basis * C_rev * SumT ≤ K_basis * max C_B (C_rev) * SumT :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hK_basis_nn) hSumT_nn
      linarith
    have h_split :
        K_basis * max C_B (C_rev) * (SumF + SumT) =
          K_basis * max C_B (C_rev) * SumF + K_basis * max C_B (C_rev) * SumT := by
      ring
    linarith
  -- Combine with the polynomial factor `MX ≤ M_pow`.
  have h_combined :
      C_fwd * (C_cov * (max (1 + ‖B.toFun b‖) 1) ^ (max r s) *
        (N_F * ‖B.toFun b‖ + N_T)) ≤ K_const * (SumF + SumT) := by
    have h_inner_nn : 0 ≤ N_F * ‖B.toFun b‖ + N_T := by
      have h_a : 0 ≤ N_F * ‖B.toFun b‖ := mul_nonneg hN_F_nn (norm_nonneg _)
      linarith
    have h_step1 :
        C_fwd * (C_cov * (max (1 + ‖B.toFun b‖) 1) ^ (max r s) *
          (N_F * ‖B.toFun b‖ + N_T)) ≤
          C_fwd * (C_cov * M_pow * (N_F * ‖B.toFun b‖ + N_T)) := by
      have h_factor_nn : 0 ≤ C_cov * (N_F * ‖B.toFun b‖ + N_T) :=
        mul_nonneg hCcov_nn h_inner_nn
      have h_step_a :
          C_cov * (max (1 + ‖B.toFun b‖) 1) ^ (max r s) *
              (N_F * ‖B.toFun b‖ + N_T) ≤
            C_cov * M_pow * (N_F * ‖B.toFun b‖ + N_T) := by
        have h_rew_l :
            C_cov * (max (1 + ‖B.toFun b‖) 1) ^ (max r s) *
                (N_F * ‖B.toFun b‖ + N_T) =
              C_cov * (N_F * ‖B.toFun b‖ + N_T) *
                (max (1 + ‖B.toFun b‖) 1) ^ (max r s) := by ring
        have h_rew_r :
            C_cov * M_pow * (N_F * ‖B.toFun b‖ + N_T) =
              C_cov * (N_F * ‖B.toFun b‖ + N_T) * M_pow := by ring
        rw [h_rew_l, h_rew_r]
        exact mul_le_mul_of_nonneg_left hMX_le h_factor_nn
      exact mul_le_mul_of_nonneg_left h_step_a hCfwd_nn
    have h_step2 :
        C_fwd * (C_cov * M_pow * (N_F * ‖B.toFun b‖ + N_T)) ≤
          C_fwd * (C_cov * M_pow * (K_basis * max C_B (C_rev) * (SumF + SumT))) := by
      have h_step_a :
          C_cov * M_pow * (N_F * ‖B.toFun b‖ + N_T) ≤
            C_cov * M_pow * (K_basis * max C_B (C_rev) * (SumF + SumT)) :=
        mul_le_mul_of_nonneg_left h_inner
          (mul_nonneg hCcov_nn hM_pow_nn)
      exact mul_le_mul_of_nonneg_left h_step_a hCfwd_nn
    have h_step3 :
        C_fwd * (C_cov * M_pow * (K_basis * max C_B (C_rev) * (SumF + SumT))) ≤
          K_const * (SumF + SumT) := by
      have h_max_nn : 0 ≤ max C_B C_rev := le_trans hCB_nn (le_max_left _ _)
      have h_SumFT_nn : 0 ≤ SumF + SumT := by linarith
      have h_lhs_eq :
          C_fwd * (C_cov * M_pow * (K_basis * max C_B (C_rev) * (SumF + SumT))) =
            C_fwd * C_cov * M_pow * (max C_B C_rev) * K_basis * (SumF + SumT) := by
        ring
      have h_K_const_factor :
          C_fwd * C_cov * M_pow * (max C_B C_rev) * K_basis ≤ K_const := by
        rw [hK_const_def]
        have h1 : 0 ≤ C_fwd * C_cov * M_pow := by
          have : 0 ≤ C_fwd * C_cov := mul_nonneg hCfwd_nn hCcov_nn
          exact mul_nonneg this hM_pow_nn
        have h_a : C_fwd * C_cov * M_pow * (max C_B C_rev) * K_basis ≤
            C_fwd * C_cov * M_pow * (max C_B C_rev + 1) * K_basis := by
          have h_aa : C_fwd * C_cov * M_pow * (max C_B C_rev) ≤
              C_fwd * C_cov * M_pow * (max C_B C_rev + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) h1
          exact mul_le_mul_of_nonneg_right h_aa hK_basis_nn
        have h_b : C_fwd * C_cov * M_pow * (max C_B C_rev + 1) * K_basis ≤
            C_fwd * C_cov * M_pow * (max C_B C_rev + 1) * (K_basis + 1) := by
          have h_left_nn : 0 ≤ C_fwd * C_cov * M_pow * (max C_B C_rev + 1) := by
            have : 0 ≤ max C_B C_rev + 1 := by linarith
            exact mul_nonneg h1 this
          exact mul_le_mul_of_nonneg_left (by linarith) h_left_nn
        linarith
      have h_chain :
          C_fwd * C_cov * M_pow * (max C_B C_rev) * K_basis * (SumF + SumT) ≤
            K_const * (SumF + SumT) :=
        mul_le_mul_of_nonneg_right h_K_const_factor h_SumFT_nn
      linarith
    linarith
  -- Final RHS rewrite: Σ (‖fderiv comp‖ + |comp|) = SumF + SumT.
  have h_sum_split :
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M)
                g r s T α Idx Jdx ∘ (extChartAt I α).symm)
              (extChartAt I α b)‖ +
            |tensorChartComponentRaw (I := I) (M := M)
              g r s T α Idx Jdx b|) = SumF + SumT := by
    rw [hSumF_def, hSumT_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    rw [← Finset.sum_add_distrib]
  rw [h_sum_split]
  exact le_trans h_chain1 h_combined

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chart_pulled_covApply_cov_repr_norm_le_chartComp_data
end Sanity
