import DifferentialGeometry.Geometry.Hessian
import DifferentialGeometry.Geometry.VossWeyl
import DifferentialGeometry.Integral.Measure.Family

/-!
# Trace of the chart Hessian against the inverse Gram matrix equals the Laplacian

For a smooth Riemannian metric `g` on a smooth manifold `M` and a smooth scalar
function `f : M → ℝ`, the chart Voss–Weyl formula
$$
(\Delta_g f)(x) = \frac{1}{\sqrt{\det g_\alpha(x)}}
  \sum_i \partial_i \Bigl(\sqrt{\det g_\alpha}\,
    \sum_j g^{ij}_\alpha\, \partial_j \tilde f\Bigr)(\varphi_\alpha(x))
$$
expands by Leibniz into three terms:
$$
\sum_{ij} g^{ij}\,\partial_i\partial_j \tilde f
  + \sum_{ij}(\partial_i g^{ij})\,\partial_j \tilde f
  + \frac{1}{\sqrt{\det g_\alpha}}\sum_{ij}\partial_i(\sqrt{\det g_\alpha})\,g^{ij}\,
        \partial_j \tilde f.
$$
On the other hand the chart-coordinate trace of the Hessian against the inverse
Gram matrix reads
$$
\sum_{ij} g^{ij}\,(\operatorname{Hess} f)_{ij}
  = \sum_{ij} g^{ij}\,\partial_i\partial_j \tilde f
    - \sum_{ijk} g^{ij}\,\Gamma^k_{ij}\,\partial_k \tilde f.
$$
Equating these two expressions and re-indexing the contraction `k \mapsto j`
on the trace side reduces to the *contracted Christoffel identity*
$$
\sum_{ik} g^{ik}\,\Gamma^j_{ik}
  = - \frac{1}{\sqrt{\det g_\alpha}}\sum_l
        \partial_l\bigl(\sqrt{\det g_\alpha}\cdot g^{jl}\bigr).
$$
This is the standard identity expressing the divergence of the inverse metric
"vector field" against the Riemannian volume density. It is purely algebraic in
the chart coordinates, and follows from the symmetric definition of `Γ` together
with Jacobi's formula for the derivative of the determinant. We state this
identity as a hypothesis-bearing scalar predicate `ChartContractedChristoffelOn`
and use it to derive the trace identity on the chart source.

## Main definitions

* `ChartContractedChristoffelOn g α y j` : the predicate stating the contracted
  Christoffel identity at the chart-target point `y` and free index `j`.

## Main results

* `chartHessTrace_eq_laplacian` : the chart-coordinate trace identity
  `∑_{ij} g^{ij}\,(\operatorname{Hess} f)_{ij}(x) = (\Delta_g f)(x)` derived from
  the contracted Christoffel identity, valid on the chart source under
  `[I.Boundaryless]`.
* `traceFun_hessFun_eq_chartHessTrace_of_orthonormal` : the bilinear-form-trace
  identity `traceFun (\operatorname{hessFun} g f) x = \chartHessTrace g f x`
  (using the canonical basis) under chart g-orthonormality at `x`.
* `laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted` : the Bochner /
  Lichnerowicz dimension-Laplacian inequality, discharging the `htr` hypothesis
  from the basis-naive Cauchy–Schwarz bound via the trace identity and
  orthonormality.

The trace identity is presented in two parallel forms: a chart-coordinate form
`chartHessTrace_eq_laplacian` matching the matrix expression
`∑_{ij} g^{ij}\,(\operatorname{Hess} f)_{ij}`, and a bilinear-form form
`traceFun_hessFun_eq_chartHessTrace_of_orthonormal` matching the canonical-basis
trace of `hessFun`. The latter, combined with the trace identity, discharges the
`htr` hypothesis of `laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq` directly.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- The pulled-back chart density, viewed as a scalar function on the chart
target `(extChartAt I α).target ⊆ E`. Wrapper around `chartDensityOnE`
re-exposed for naming consistency with the chart-coordinate identities of this
file. -/
abbrev densityOnE (g : SmoothRiemannianMetric I M) (α : M) : E → ℝ :=
  chartDensityOnE (I := I) g α

/-- The *contracted Christoffel identity at `y` with free index `j`*. This is
the chart-coordinate identity equating the trace of the Christoffel symbol
contracted with the inverse Gram matrix to (minus) the partial-derivative
expansion of `D · G^{j ·}`. -/
def ChartContractedChristoffelOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (y : E) (j : Fin (Module.finrank ℝ E)) : Prop :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i k y *
        chartChristoffel (I := I) g α i k j y =
    -(1 / chartDensityOnE (I := I) g α y) *
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) l
          (fun y' : E =>
            chartDensityOnE (I := I) g α y' *
              chartInvGramOnE (I := I) g α j l y') y

/-- Pointwise expansion of `chartHessTrace` in chart coordinates: the trace
splits into a "Hessian" term `∑_{ij} G^{ij}·\partial_i\partial_j f̃` and a
"Christoffel correction" term `-∑_{ijk} G^{ij}·Γ^k_{ij}·\partial_k f̃`. -/
lemma chartHessTrace_expand
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    chartHessTrace (I := I) g f x =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) -
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x i j *
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x)) := by
  classical
  rw [chartHessTrace_def]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            chartHessianTensor (I := I) g x f i j x) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            (chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x))) from ?_]
  swap
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [chartHessianTensor_def]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            (chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x))) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
            chartInvGramMatrix (I := I) g x x i j *
              (∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x)))) from ?_]
  swap
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
            chartInvGramMatrix (I := I) g x x i j *
              (∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x)))) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) -
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              (∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x))) from ?_]
  swap
  · simp only [Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- Pointwise expansion of `chartVossWeylLaplacian` by the Leibniz rule
applied to the integrand `(\sum_j G^{ij}·\partial_j f̃) · D`. -/
lemma chartVossWeylLaplacian_expand_hypBearing
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M)
    (hgrad_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y : E => gradChartCoeffOnE (I := I) g α f i y)
        (extChartAt I α x))
    (hdens_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g α) (extChartAt I α x)) :
    chartVossWeylLaplacian (I := I) g α f x =
      (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
            partialDeriv (E := E) i
              (chartDensityOnE (I := I) g α) (extChartAt I α x) +
              chartDensityOnE (I := I) g α (extChartAt I α x) *
                partialDeriv (E := E) i
                  (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x)) := by
  classical
  rw [chartVossWeylLaplacian_def]
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α f i)
          (extChartAt I α x) =
        gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
          partialDeriv (E := E) i
            (chartDensityOnE (I := I) g α) (extChartAt I α x) +
          chartDensityOnE (I := I) g α (extChartAt I α x) *
            partialDeriv (E := E) i
              (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x) := by
    intro i
    have hu : DifferentiableAt ℝ (gradChartCoeffOnE (I := I) g α f i)
        (extChartAt I α x) := hgrad_diff i
    have hv : DifferentiableAt ℝ (chartDensityOnE (I := I) g α)
        (extChartAt I α x) := hdens_diff
    change partialDeriv (E := E) i
        (fun y : E => gradChartCoeffOnE (I := I) g α f i y *
          chartDensityOnE (I := I) g α y) (extChartAt I α x) =
      gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
          partialDeriv (E := E) i (chartDensityOnE (I := I) g α) (extChartAt I α x) +
        chartDensityOnE (I := I) g α (extChartAt I α x) *
          partialDeriv (E := E) i
            (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x)
    unfold partialDeriv
    rw [fderiv_fun_mul (𝕜 := ℝ) hu hv]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (chartVossWeylIntegrand (I := I) g α f i)
              (extChartAt I α x)) =
        ∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
              partialDeriv (E := E) i
                (chartDensityOnE (I := I) g α) (extChartAt I α x) +
            chartDensityOnE (I := I) g α (extChartAt I α x) *
              partialDeriv (E := E) i
                (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x)) from
      Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [div_eq_mul_one_div]
  ring

/-- Each partial derivative of `scalarOnE` is `C^∞` on the interior of the
chart target. (The boundaryless analogue of the with-boundary version in
`WithBoundary/`. Re-exposed here because the with-boundary analogue is
internal.) -/
private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  classical
  have hf_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hf_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hf_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hf_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

/-- The pulled-back inverse Gram entry is `C^∞` on the chart target. -/
lemma chartInvGramOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartInvGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-- `gradChartCoeffOnE g α f i` is `C^∞` on the interior of the chart
target. (We use the interior so that `partialDeriv` is well-defined.) -/
lemma gradChartCoeffOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (gradChartCoeffOnE (I := I) g α f i)
      (interior (extChartAt I α).target) := by
  classical
  unfold gradChartCoeffOnE
  refine ContDiffOn.sum (fun j _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  · exact partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf j

/-- Leibniz expansion of `∂_i (gradChartCoeffOnE i)`: it splits as
`∑_j ((∂_i G^{ij})·∂_j f̃ + G^{ij}·∂_i ∂_j f̃)`. -/
lemma partialDeriv_gradChartCoeffOnE_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) i (gradChartCoeffOnE (I := I) g α f i) y =
      ∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y +
          chartInvGramOnE (I := I) g α i j y *
            chartIteratedPartialDeriv (I := I) α f i j y) := by
  classical
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  have hG : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α i j) y := by
    intro j
    have hcd_target : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
        (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α i j
    have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
        (interior (extChartAt I α).target) := hcd_target.mono interior_subset
    have hcat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α i j) y :=
      hcd_int.contDiffAt hy_nhd
    exact hcat.differentiableAt (by simp)
  have hF : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y := by
    intro j
    have hcd_int : ContDiffOn ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) :=
      partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf j
    have hcat : ContDiffAt ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y :=
      hcd_int.contDiffAt hy_nhd
    exact hcat.differentiableAt (by simp)
  have hprod : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y :=
    fun j => (hG j).fun_mul (hF j)
  have hgrad_split : partialDeriv (E := E) i
        (gradChartCoeffOnE (I := I) g α f i) y =
      ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y := by
    change (fderiv ℝ (gradChartCoeffOnE (I := I) g α f i) y) ((chartModelBasis E) i) =
        ∑ j : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y
    have h_eq_fn : (gradChartCoeffOnE (I := I) g α f i) =
        fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y' *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y' := by
      funext y'; rfl
    rw [h_eq_fn]
    rw [fderiv_fun_sum (fun j _ => hprod j)]
    rw [ContinuousLinearMap.sum_apply]
    rfl
  rw [hgrad_split]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change partialDeriv (E := E) i
        (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y =
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y +
          chartInvGramOnE (I := I) g α i j y *
            chartIteratedPartialDeriv (I := I) α f i j y
  unfold partialDeriv chartIteratedPartialDeriv
  have hF_unfolded : DifferentiableAt ℝ
      (fun y' : E => fderiv ℝ (scalarOnE (I := I) α f) y' ((chartModelBasis E) j)) y :=
    hF j
  rw [fderiv_fun_mul (𝕜 := ℝ) (hG j) hF_unfolded]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change chartInvGramOnE (I := I) g α i j y *
      ((fderiv ℝ (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y)
        ((chartModelBasis E) i)) +
      (fderiv ℝ (scalarOnE (I := I) α f) y) ((chartModelBasis E) j) *
        (fderiv ℝ (chartInvGramOnE (I := I) g α i j) y) ((chartModelBasis E) i) =
    (fderiv ℝ (chartInvGramOnE (I := I) g α i j) y) ((chartModelBasis E) i) *
        (fderiv ℝ (scalarOnE (I := I) α f) y) ((chartModelBasis E) j) +
      chartInvGramOnE (I := I) g α i j y *
        ((fderiv ℝ (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y)
          ((chartModelBasis E) i))
  ring

/-- **Chart-coordinate trace identity** for the Hessian against the inverse
Gram matrix. Hypothesis-bearing form: given the contracted Christoffel
identity at the chart-target image of `x` for every free index `j`, we obtain
$$
\sum_{ij} G^{ij}\,(\operatorname{Hess} f)_{ij}(x)
  = (\Delta_g f)(x).
$$
The proof carries out the Leibniz expansion of the chart Voss–Weyl Laplacian,
the chart-coordinate expansion of the Hessian-against-inverse-Gram trace, and
the contracted-Christoffel-identity term-rewriting on the contraction
`-∑_{ijk} G^{ij}\,Γ^k_{ij}\,\partial_k f̃`. -/
theorem chartHessTrace_eq_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  set α : M := x with hα_def
  have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H x
  have hVW : Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x :=
    voss_weyl_laplacian_formula_of_closed (I := I) g α hf hxsrc
  rw [hVW]
  rw [chartHessTrace_expand (I := I) g f x]
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hsymm_y₀ : (extChartAt I α).symm y₀ = x :=
    (extChartAt I α).left_inv hxsrc_ext
  have hG_eq : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j =
        chartInvGramOnE (I := I) g α i j y₀ := by
    intros i j
    rw [chartInvGramOnE_def]
    rw [hsymm_y₀]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x i j *
                chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartIteratedPartialDeriv (I := I) α f i j y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_eq i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x i j *
                  chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                    partialDeriv (E := E) k
                      (scalarOnE (I := I) x f) (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartChristoffel (I := I) g α i j k y₀ *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) α f) y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hG_eq i j]]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxsrc
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hy₀_int : y₀ ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hy₀_target
  have hy₀_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ :=
    isOpen_interior.mem_nhds hy₀_int
  have hgrad_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (gradChartCoeffOnE (I := I) g α f i) y₀ := by
    intro i
    have h := gradChartCoeffOnE_contDiffOn_interior (I := I) g α hf i
    exact (h.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ := by
    have hcd_target : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (extChartAt I α).target := chartDensityOnE_contDiffOn (I := I) g α
    have hcd_int : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (interior (extChartAt I α).target) := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hD_pos : 0 < chartDensity (I := I) g α x :=
    chartDensity_pos (I := I) g α hxbase
  have hD_eq : chartDensityOnE (I := I) g α y₀ = chartDensity (I := I) g α x := by
    unfold chartDensityOnE
    rw [hsymm_y₀]
  rw [chartVossWeylLaplacian_expand_hypBearing (I := I) g α f x
      hgrad_diff hdens_diff]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
              (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
                partialDeriv (E := E) i
                  (chartDensityOnE (I := I) g α) (extChartAt I α x) +
                chartDensityOnE (I := I) g α (extChartAt I α x) *
                  partialDeriv (E := E) i
                    (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x))) =
        (∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
            chartDensityOnE (I := I) g α y₀ *
              ∑ j : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialDeriv_gradChartCoeffOnE_expand (I := I) g α hf i hy₀_int]]
  have hT2_swap : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀ *
                partialDeriv (E := E) k
                  (scalarOnE (I := I) α f) y₀) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀ *
                      partialDeriv (E := E) k
                        (scalarOnE (I := I) α f) y₀) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                    (chartInvGramOnE (I := I) g α i j y₀ *
                      chartChristoffel (I := I) g α i j k y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hT2_swap]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcc k]]
  have hDens_diffAt : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    hdens_diff
  have hG_diffAt : ∀ k l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    have hcd_target := chartInvGramOnE_contDiffOn (I := I) g α k l
    have hcd_int := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hLeibniz : ∀ k l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) l
          (fun y' : E => chartDensityOnE (I := I) g α y' *
            chartInvGramOnE (I := I) g α k l y') y₀ =
        partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α k l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    unfold partialDeriv
    rw [fderiv_fun_mul (𝕜 := ℝ) hDens_diffAt (hG_diffAt k l)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀))) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 2
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hLeibniz k l]]
  have hgrad_eval : ∀ i : Fin (Module.finrank ℝ E),
      gradChartCoeffOnE (I := I) g α f i y₀ =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y₀ *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ := fun i => rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            (gradChartCoeffOnE (I := I) g α f i y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) =
        (∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hgrad_eval i]]
  have hG_sym : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i j y₀ =
        chartInvGramOnE (I := I) g α j i y₀ := by
    intro i j
    unfold chartInvGramOnE chartInvGramMatrix
    set z : M := (extChartAt I α).symm y₀
    have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α z
    have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
      hG_hermit.inv
    have hentry := hGinv_hermit.apply i j
    have hpoint : (chartGramMatrix (I := I) g α z)⁻¹ i j =
        (chartGramMatrix (I := I) g α z)⁻¹ j i := by
      have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
      rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
      exact hstar.symm
    exact hpoint
  have hDOnE_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := by
    rw [hD_eq]; exact ne_of_gt hD_pos
  have hDx_ne : chartDensity (I := I) g α x ≠ 0 := ne_of_gt hD_pos
  rw [show
      (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) =
        (1 / chartDensity (I := I) g α x) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) from by
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]]
  rw [show (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((1 / chartDensity (I := I) g α x) *
            (chartInvGramOnE (I := I) g α i j y₀ *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀) +
            (1 / chartDensity (I := I) g α x) *
              (chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k
                (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀) *
                ∑ l : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                      chartInvGramOnE (I := I) g α k l y₀ +
                    chartDensityOnE (I := I) g α y₀ *
                      partialDeriv (E := E) l
                        (chartInvGramOnE (I := I) g α k l) y₀))) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α k l y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) l
                  (chartInvGramOnE (I := I) g α k l) y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α j i y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α j i) y₀)) from by
    rw [Finset.sum_comm]]
  have h_partial_swap : ∀ i j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j i) y₀ =
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ := by
    intros i j
    have hfun_eq : chartInvGramOnE (I := I) g α j i =
        chartInvGramOnE (I := I) g α i j := by
      funext y'
      unfold chartInvGramOnE
      set z' : M := (extChartAt I α).symm y'
      have hz_hermit : (chartGramMatrix (I := I) g α z').IsHermitian :=
        chartGramMatrix_isHermitian (I := I) g α z'
      have hzinv_hermit : (chartGramMatrix (I := I) g α z')⁻¹.IsHermitian :=
        hz_hermit.inv
      have hentry := hzinv_hermit.apply i j
      have hstar_eq : (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j := by
        have hstar : star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ i j := hentry
        rw [show star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ j i from rfl] at hstar
        exact hstar
      change (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j
      exact hstar_eq
    rw [hfun_eq]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α j i y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α j i) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α i j y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α i j) y₀)) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_sym j i]
    rw [h_partial_swap i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartIteratedPartialDeriv (I := I) α f i j y₀) -
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀ -
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀))) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hD_eq]
  field_simp
  ring

/-- **Trace identity** for the bilinear form `hessFun g f`. Given that the chart
Gram inverse equals the model identity at `x` (which holds when the chart-basis
frame is g-orthonormal at `x`), the trace of `hessFun g f` against the canonical
basis equals the chart-coordinate Hessian trace `chartHessTrace g f x`. -/
theorem traceFun_hessFun_eq_chartHessTrace_of_orthonormal
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x := by
  classical
  rw [traceFun_hessFun, chartHessTrace_def]
  symm
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [h_orth i i, if_pos rfl, one_mul]
  · intro j _ hji
    have hij : ¬ i = j := fun h => hji h.symm
    rw [h_orth i j, if_neg hij, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Trace identity (matrix form)**: the chart-coordinate trace of the Hessian
tensor against the inverse Gram matrix equals the Laplace-Beltrami operator.
Hypothesis-bearing form: assumes the contracted Christoffel identity at the
chart-target image of `x`, for every free index `j`. This is an alias for the
same content as `chartHessTrace_eq_laplacian`, exposing the trace form
`∑_{ij} G^{ij}\,(\operatorname{Hess} f)_{ij} = \Delta_g f` directly. -/
theorem trace_hessFun_eq_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i j *
          chartHessianTensor (I := I) g x f i j x =
      Δ_g (I := I) g hf x := by
  have h := chartHessTrace_eq_laplacian (I := I) g hf x hcc
  rw [chartHessTrace_def] at h
  exact h

/-- **Bochner–Lichnerowicz dimension-Laplacian inequality** with the trace
hypothesis discharged via the contracted Christoffel identity and chart
g-orthonormality at `x`. -/
theorem laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have h1 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x :=
    traceFun_hessFun_eq_chartHessTrace_of_orthonormal (I := I) g f x h_orth
  have h2 : chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x :=
    chartHessTrace_eq_laplacian (I := I) g hf x hcc
  have htr : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      Δ_g (I := I) g hf x := h1.trans h2
  exact laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq
    (I := I) g hf x htr

/-- Smoothness of the chart Gram matrix entry pulled back to the chart target.
Analog of `chartInvGramOnE_contDiffOn` but for `chartGramOnE`. -/
lemma chartGramOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-- The chart Gram entry is differentiable at any point in the interior of the
chart target. -/
private lemma chartGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd_target : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hcd_target.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

/-! ### Smoothness of the chart Christoffel symbol

The chart Christoffel symbol `chartChristoffel g α i j k` is the half-times-
inverse-Gram-times-bracket scalar. The inverse Gram entries and the partial
derivatives of the Gram entries are smooth on the interior of the chart target,
and a finite sum of products of smooth functions is smooth. -/

/-- **Smoothness of `chartChristoffel`.** The chart Christoffel symbol is `C^∞`
on the interior of the chart target. -/
theorem chartChristoffel_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) := by
  classical
  -- Rewrite the chart Christoffel symbol as a sum of products in terms of
  -- `chartInvGramOnE` (smooth on the chart target, hence on its interior) and
  -- partial derivatives of `chartGramOnE` (smooth on the interior).
  have hrewrite : (chartChristoffel (I := I) g α i j k) =
      fun y : E =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
    funext y
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  have hsum_smooth :
      ContDiffOn ℝ ∞
        (fun y : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y))
        (interior (extChartAt I α).target) := by
    refine ContDiffOn.sum (fun l _ => ?_)
    refine ContDiffOn.mul ?_ ?_
    · exact (chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset
    · have hi : ContDiffOn ℝ ∞
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α l j).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α l j))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      have hj : ContDiffOn ℝ ∞
          (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l i)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α l i).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α l i))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      have hl : ContDiffOn ℝ ∞
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α i j))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      exact (hi.add hj).sub hl
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul hsum_smooth

/-- The chart inverse Gram entry is differentiable at any point in the interior
of the chart target. -/
private lemma chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α i j) y := by
  have hcd_target : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hcd_target.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

/-- The chart density (pulled back to the chart target) is differentiable at any
point in the interior of the chart target. -/
lemma chartDensityOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y := by
  have hcd_target : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
      (extChartAt I α).target := chartDensityOnE_contDiffOn (I := I) g α
  have hcd_int : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
      (interior (extChartAt I α).target) := hcd_target.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

/-! ### Lifting Jacobi's formula from `ℝ` to a spatial direction

We define the "chart-coordinate Jacobi family" by composing with the affine line
`s ↦ y₀ + s • e_l`. This produces an `ℝ → Matrix n n ℝ` family for which the
existing `Family.lean` Jacobi infrastructure applies. -/

/-- The line through `y₀` in the direction `e_l`. Smooth (in fact affine), with
derivative `e_l`. -/
private noncomputable def jacobiLine (y₀ : E) (l : Fin (Module.finrank ℝ E)) :
    ℝ → E := fun s => y₀ + s • (chartModelBasis E) l

/-- The line is differentiable, with derivative `e_l`. -/
private lemma hasDerivAt_jacobiLine (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (s : ℝ) :
    HasDerivAt (jacobiLine (E := E) y₀ l) ((chartModelBasis E) l) s := by
  -- f(s) = y₀ + s • e_l. f'(s) = e_l.
  have h₁ : HasDerivAt (fun s : ℝ => s • (chartModelBasis E) l)
      ((1 : ℝ) • (chartModelBasis E) l) s :=
    (hasDerivAt_id s).smul_const ((chartModelBasis E) l)
  have h₁' : HasDerivAt (fun s : ℝ => s • (chartModelBasis E) l)
      ((chartModelBasis E) l) s := by
    rw [show ((1 : ℝ) • (chartModelBasis E) l) = (chartModelBasis E) l from
      one_smul ℝ _] at h₁
    exact h₁
  have h₂ : HasDerivAt (fun _ : ℝ => y₀) (0 : E) s := hasDerivAt_const s y₀
  have h := h₂.add h₁'
  -- The derivative is `0 + e_l = e_l`.
  have hcoerce : (0 : E) + (chartModelBasis E) l = (chartModelBasis E) l := zero_add _
  rw [hcoerce] at h
  -- Identify `(fun _ => y₀) + (fun s => s • e_l) = jacobiLine y₀ l`.
  have hfun_eq : (fun s : ℝ => y₀ + s • (chartModelBasis E) l) =
      jacobiLine (E := E) y₀ l := by
    funext s; rfl
  -- The HasDerivAt above is for the sum function `(fun _ => y₀) + (fun s => s • e_l)`.
  have h' : HasDerivAt (fun s : ℝ => y₀ + s • (chartModelBasis E) l)
      ((chartModelBasis E) l) s := by
    have hpoint : ((fun _ : ℝ => y₀) + fun s : ℝ => s • (chartModelBasis E) l) =
        (fun s : ℝ => y₀ + s • (chartModelBasis E) l) := by
      funext s; simp [Pi.add_apply]
    rw [hpoint] at h
    exact h
  rw [← hfun_eq]
  exact h'

/-- Composing a function `F : E → ℝ` with the Jacobi line: the time derivative
at `s = 0` equals the partial derivative in direction `l`. -/
private lemma hasDerivAt_comp_jacobiLine
    {y₀ : E} {l : Fin (Module.finrank ℝ E)} {F : E → ℝ}
    (hF : DifferentiableAt ℝ F y₀) :
    HasDerivAt (fun s : ℝ => F (jacobiLine (E := E) y₀ l s))
      (partialDeriv (E := E) l F y₀) 0 := by
  have hy : (jacobiLine (E := E) y₀ l 0) = y₀ := by
    unfold jacobiLine; rw [zero_smul, add_zero]
  have hF' : HasFDerivAt F (fderiv ℝ F y₀) y₀ := hF.hasFDerivAt
  have hF'' : HasFDerivAt F (fderiv ℝ F y₀) (jacobiLine (E := E) y₀ l 0) := by
    rw [hy]; exact hF'
  have hline := hasDerivAt_jacobiLine (E := E) y₀ l 0
  have := hF''.comp_hasDerivAt 0 hline
  exact this

/-- The chart Gram matrix as a function of `s` along the Jacobi line, formed
by composing `chartGramOnE` with the line. -/
private noncomputable def gramJacobiFamily
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E)) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun s => Matrix.of fun i j =>
    chartGramOnE (I := I) g α i j (jacobiLine (E := E) y₀ l s)

private lemma gramJacobiFamily_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E)) :
    gramJacobiFamily (I := I) g α y₀ l 0 =
      Matrix.of fun i j => chartGramOnE (I := I) g α i j y₀ := by
  unfold gramJacobiFamily jacobiLine
  ext i j
  simp [zero_smul, add_zero]

/-- The Gram matrix at `y₀` (viewed as a matrix of `chartGramOnE`-values) equals
the chart Gram matrix at `(symm y₀)`. -/
private lemma gramAtY_eq_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) (y₀ : E) :
    (Matrix.of fun i j => chartGramOnE (I := I) g α i j y₀) =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀) := by
  ext i j
  rfl

/-- Each entry of the Jacobi family is differentiable at `s = 0` with derivative
`partialDeriv l (chartGramOnE g α i j) y₀`. -/
private lemma hasDerivAt_gramJacobiFamily_entry
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => gramJacobiFamily (I := I) g α y₀ l s i j)
      (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀) 0 := by
  have hG : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y₀ :=
    chartGramOnE_differentiableAt_interior (I := I) g α i j hy
  have h := hasDerivAt_comp_jacobiLine (E := E) (l := l) (F := chartGramOnE (I := I) g α i j) hG
  -- `gramJacobiFamily g α y₀ l s i j = chartGramOnE g α i j (jacobiLine y₀ l s)`.
  unfold gramJacobiFamily
  simp only [Matrix.of_apply]
  exact h

/-- The Gram matrix of `gramJacobiFamily ... 0` is the same as the chart Gram
matrix at `symm y₀`, in particular has positive determinant for `y₀` in the chart
target. -/
private lemma gramJacobiFamily_det_pos
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ (extChartAt I α).target) :
    0 < (gramJacobiFamily (I := I) g α y₀ l 0).det := by
  rw [gramJacobiFamily_zero, gramAtY_eq_chartGramMatrix]
  -- The Gram matrix at `symm y₀` has positive determinant on the chart base set.
  have hbase : (extChartAt I α).symm y₀ ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  exact chartGramMatrix_det_pos (I := I) g α hbase

/-- The "spatial" version of `hasDerivAt_det_eq_det_mul_trace_inv_mul`: the
partial derivative of `det (chartGramMatrix g α (symm ·))` in direction `e_l`
equals `det · trace(inv · ∂_l G)`. -/
private lemma partialDeriv_det_chartGramOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) l
        (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det) y₀ =
      (chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀)).det *
        Matrix.trace ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ *
          Matrix.of (fun i j => partialDeriv (E := E) l
            (chartGramOnE (I := I) g α i j) y₀)) := by
  classical
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  -- Use the Jacobi family.
  set Gf := gramJacobiFamily (I := I) g α y₀ l with hGf
  -- Each entry is differentiable.
  have hentries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => Gf s i j)
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀) 0 :=
    fun i j => hasDerivAt_gramJacobiFamily_entry (I := I) g α y₀ l i j hy
  -- Determinant is positive at `s = 0`.
  have hpos : 0 < (Gf 0).det := gramJacobiFamily_det_pos (I := I) g α y₀ l hytgt
  have hunit : IsUnit (Gf 0).det := (ne_of_gt hpos).isUnit
  have hjac :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_det_eq_det_mul_trace_inv_mul
      (n := Fin (Module.finrank ℝ E))
      Gf
      (Matrix.of (fun i j =>
        partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀))
      0 (fun i j => by simpa [Matrix.of_apply] using hentries i j) hunit
  -- `hjac` is: HasDerivAt (fun s => (Gf s).det) ((Gf 0).det * trace ((Gf 0)⁻¹ * G')) 0
  -- where `G' i j = partialDeriv l (chartGramOnE i j) y₀`.
  -- The function `(Gf s).det` equals
  -- `(chartGramMatrix g α (symm (jacobiLine y₀ l s))).det`.
  have hfun_eq : (fun s : ℝ => (Gf s).det) =
      fun s : ℝ => (chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (jacobiLine (E := E) y₀ l s))).det := by
    funext s
    -- gramJacobiFamily g α y₀ l s = Matrix.of fun i j => chartGramOnE g α i j (jacobiLine y₀ l s)
    --                            = chartGramMatrix g α (symm (jacobiLine y₀ l s)).
    have hmat_eq : Gf s = chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (jacobiLine (E := E) y₀ l s)) := by
      rw [hGf]
      ext i j
      rfl
    rw [hmat_eq]
  rw [hfun_eq] at hjac
  -- Now apply chain rule via `hasDerivAt_comp_jacobiLine`.
  -- We have `HasDerivAt (det ∘ chartGramMatrix g α (symm ∘ jacobiLine ...)) (...) 0`.
  -- We want to identify this with `partialDeriv l (det ∘ chartGramMatrix g α (symm ·)) y₀`.
  have hDF : DifferentiableAt ℝ
      (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det) y₀ := by
    -- From smoothness of det of chart Gram on the chart target.
    have hdet_smooth : ContDiffOn ℝ ∞
        (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)
        (extChartAt I α).target := by
      have hexp : (fun y : E =>
            (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det) =
          (fun y : E =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∏ i, chartGramOnE (I := I) g α (σ i) i y) := by
        funext y
        rw [Matrix.det_apply]
        simp only [Units.smul_def, zsmul_eq_mul]
        rfl
      rw [hexp]
      refine ContDiffOn.sum (fun σ _ => ?_)
      refine ContDiffOn.mul contDiffOn_const ?_
      refine contDiffOn_prod (fun i _ => ?_)
      exact chartGramOnE_contDiffOn (I := I) g α (σ i) i
    have hcd_int : ContDiffOn ℝ ∞
        (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)
        (interior (extChartAt I α).target) := hdet_smooth.mono interior_subset
    have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
    have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy
    exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)
  have hcomp := hasDerivAt_comp_jacobiLine (E := E) (l := l)
    (F := fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)
    hDF
  -- Both `hjac` and `hcomp` are HasDerivAt of the SAME function at 0.
  have heq := hjac.unique hcomp
  -- The Gf 0 inverse and value: at `s = 0`, jacobiLine y₀ l 0 = y₀.
  have hGf_zero_eq : Gf 0 =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀) := by
    rw [hGf, gramJacobiFamily_zero, gramAtY_eq_chartGramMatrix]
  rw [hGf_zero_eq] at heq
  -- Symmetrise the equation to match the goal.
  exact heq.symm

/-- The "spatial" version of `hasDerivAt_sqrt_det_eq_half_trace_inv_mul`: the
partial derivative of `chartDensityOnE` in direction `e_l` equals
`(1/2) · trace(inv · ∂_l G) · D`. -/
lemma partialDeriv_chartDensityOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ =
      (1 / 2) *
        Matrix.trace ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ *
          Matrix.of (fun i j => partialDeriv (E := E) l
            (chartGramOnE (I := I) g α i j) y₀)) *
        chartDensityOnE (I := I) g α y₀ := by
  classical
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  set Gf := gramJacobiFamily (I := I) g α y₀ l with hGf
  have hentries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => Gf s i j)
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀) 0 :=
    fun i j => hasDerivAt_gramJacobiFamily_entry (I := I) g α y₀ l i j hy
  have hpos : 0 < (Gf 0).det := gramJacobiFamily_det_pos (I := I) g α y₀ l hytgt
  have hjac :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
      (n := Fin (Module.finrank ℝ E))
      Gf
      (Matrix.of (fun i j =>
        partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀))
      0 (fun i j => by simpa [Matrix.of_apply] using hentries i j) hpos
  -- hjac: HasDerivAt (fun s => sqrt ((Gf s).det)) ((1/2) * trace((Gf 0)⁻¹ * G') * sqrt((Gf 0).det)) 0
  -- The function `sqrt ((Gf s).det)` equals
  -- `chartDensityOnE g α (jacobiLine y₀ l s)` (= sqrt of det of chart Gram).
  have hfun_eq : (fun s : ℝ => Real.sqrt (Gf s).det) =
      fun s : ℝ => chartDensityOnE (I := I) g α (jacobiLine (E := E) y₀ l s) := by
    funext s
    -- sqrt ((gramJacobiFamily g α y₀ l s).det) = sqrt det ... = chartDensity ... (symm ...).
    have hmat_eq : Gf s = chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (jacobiLine (E := E) y₀ l s)) := by
      rw [hGf]
      ext i j
      rfl
    rw [hmat_eq]
    rfl
  rw [hfun_eq] at hjac
  -- Apply chain rule.
  have hDF : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    chartDensityOnE_differentiableAt_interior (I := I) g α hy
  have hcomp := hasDerivAt_comp_jacobiLine (E := E) (l := l)
    (F := chartDensityOnE (I := I) g α) hDF
  -- Both have the same derivative.
  have heq := hjac.unique hcomp
  -- Identify Gf 0 and sqrt ((Gf 0).det) = chartDensityOnE g α y₀.
  have hGf_zero_eq : Gf 0 =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀) := by
    rw [hGf, gramJacobiFamily_zero, gramAtY_eq_chartGramMatrix]
  have hsqrt_eq :
      Real.sqrt (chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀)).det =
        chartDensityOnE (I := I) g α y₀ := rfl
  rw [hGf_zero_eq] at heq
  rw [hsqrt_eq] at heq
  exact heq.symm

/-! ### Matrix-inverse derivative identity

Differentiating `G · G⁻¹ = I` gives `∂_l(G⁻¹) = -G⁻¹ · (∂_l G) · G⁻¹`. We prove
this componentwise in the form most convenient for the trace contraction. -/

/-- The matrix-inverse derivative identity in entry-wise form: for any
direction `l` and any matrix index `(j, p)`,
`∂_l G^{jp}(y₀) = -∑_{a, b} G^{ja}(y₀) · G^{bp}(y₀) · ∂_l G_{ab}(y₀)`. -/
lemma partialDeriv_chartInvGramOnE_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (j p : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j p) y₀ =
      -∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            chartInvGramOnE (I := I) g α b p y₀ *
            partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ := by
  classical
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  -- Strategy: Apply ∂_l to both sides of `∑_b G_{jb}(y) · G^{bp}(y) = δ^p_j`.
  -- (Where the LHS is one entry of the matrix product `G · G⁻¹ = I`.)
  set z₀ : M := (extChartAt I α).symm y₀
  -- Membership in the base set.
  have hz_base : z₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hytgt
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  -- Establish `∑_b G_{jb} · G^{bp} = δ^p_j` at any nearby point.
  -- We use the Jacobi-line composition again.
  -- Define for a point y on the chart line through y₀:
  -- the function `s ↦ ∑_b chartGramOnE g α j b (jacobiLine y₀ l s) *
  --                  chartInvGramOnE g α b p (jacobiLine y₀ l s)`
  -- This equals 1 if j = p, 0 otherwise (constant in s, on a neighborhood of 0).
  -- Hence its derivative at s = 0 is zero. By Leibniz on each summand,
  -- this gives the desired identity.
  --
  -- We prove this directly using `partialDeriv` on the constant function
  -- `y ↦ ∑_b chartGramOnE g α j b y * chartInvGramOnE g α b p y` (= δ^p_j on
  -- the chart target).
  have hidentity : ∀ (e : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ∑ b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α e b y * chartInvGramOnE (I := I) g α b p y =
          if e = p then (1 : ℝ) else 0 := by
    intro e y hy_target
    -- Membership of `symm y` in the base set.
    have hy_base : (extChartAt I α).symm y ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    -- chartGramOnE g α e b y = chartGramMatrix g α (symm y) e b
    -- chartInvGramOnE g α b p y = chartInvGramMatrix g α (symm y) b p
    -- Their sum over b equals the (e, p) entry of `G · G⁻¹` = identity.
    have hprod_eq :
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α e b y * chartInvGramOnE (I := I) g α b p y =
        (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *
          chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)) e p := by
      simp only [Matrix.mul_apply]
      rfl
    rw [hprod_eq]
    rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hy_base]
    -- Now (1 : Matrix) e p = if e = p then 1 else 0.
    by_cases hep : e = p
    · subst hep
      simp
    · rw [if_neg hep]
      exact Matrix.one_apply_ne hep
  -- The function `f y := ∑_b chartGramOnE g α j b y * chartInvGramOnE g α b p y`
  -- equals the constant `if j = p then 1 else 0` on the chart target.
  -- Hence on the open set `interior (chart target)`, its partial derivative is zero.
  have hf_const : ∀ y ∈ interior (extChartAt I α).target,
      (∑ b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α j b y * chartInvGramOnE (I := I) g α b p y) =
        (if j = p then (1 : ℝ) else 0) := by
    intro y hy_int
    exact hidentity j y (interior_subset hy_int)
  -- partialDeriv of a function constant on an open set is zero.
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy
  -- partialDeriv (∑_b G_{jb} · G^{bp}) y₀ = 0.
  -- Use Leibniz on each summand.
  have hf_diff : ∀ b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y : E => chartGramOnE (I := I) g α j b y *
        chartInvGramOnE (I := I) g α b p y) y₀ :=
    fun b => DifferentiableAt.fun_mul
      (chartGramOnE_differentiableAt_interior (I := I) g α j b hy)
      (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)
  -- Apply ∂_l to both sides of `f = const`.
  have hsum_diff : DifferentiableAt ℝ (fun y : E =>
      ∑ b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α j b y *
          chartInvGramOnE (I := I) g α b p y) y₀ := by
    refine DifferentiableAt.fun_sum ?_
    intros b _
    exact hf_diff b
  -- The function `g(y) := ∑ b, chartGramOnE g α j b y * chartInvGramOnE g α b p y`
  -- equals the constant `c := if j = p then 1 else 0` on a neighbourhood of y₀.
  set c : ℝ := (if j = p then (1 : ℝ) else 0) with hc_def
  set fS : E → ℝ := fun y =>
    ∑ b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α j b y *
        chartInvGramOnE (I := I) g α b p y with hfS_def
  have hfS_eventually : ∀ᶠ y in 𝓝 y₀, fS y = c := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨interior (extChartAt I α).target, hy_nhd, ?_⟩
    intro y hy_int
    rw [hfS_def, hc_def]
    exact hf_const y hy_int
  have hfS_partialDeriv_zero : partialDeriv (E := E) l fS y₀ = 0 := by
    -- fS = c on a nbhd of y₀ implies fderiv fS y₀ = 0.
    have hfderiv_eq_zero : fderiv ℝ fS y₀ = 0 := by
      have h1 : fderiv ℝ fS y₀ = fderiv ℝ (fun _ : E => c) y₀ :=
        Filter.EventuallyEq.fderiv_eq hfS_eventually
      rw [h1]
      simp
    unfold partialDeriv
    rw [hfderiv_eq_zero]
    rfl
  -- Now expand `partialDeriv l fS y₀` using Leibniz on each summand of fS.
  -- This gives:
  -- 0 = ∑ b, ∂_l (G_{jb} · G^{bp}) y₀
  --   = ∑ b, ((∂_l G_{jb}) · G^{bp} + G_{jb} · (∂_l G^{bp})) y₀
  have hexpand : partialDeriv (E := E) l fS y₀ =
      ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α j b) y₀ *
            chartInvGramOnE (I := I) g α b p y₀ +
          chartGramOnE (I := I) g α j b y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) := by
    rw [hfS_def]
    -- partialDeriv l (∑ b, ...) y₀
    -- partialDeriv l f y = fderiv ℝ f y (e_l).
    unfold partialDeriv
    rw [fderiv_fun_sum (fun b _ => hf_diff b)]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    -- Each summand: fderiv (G_{jb} · G^{bp}) y₀ (e_l) = ∂_l G_{jb} · G^{bp} + G_{jb} · ∂_l G^{bp}.
    rw [fderiv_fun_mul (𝕜 := ℝ)
      (chartGramOnE_differentiableAt_interior (I := I) g α j b hy)
      (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexpand] at hfS_partialDeriv_zero
  -- Now solve for `∂_l G^{jp}` in terms of `∂_l G_{**}`. Apply on the contraction
  -- `∑_a G^{ja} · (∂_l G^{ap}) = ?` ... actually more directly, multiply both
  -- sides of `0 = ∑_b ((∂_l G_{jb}) · G^{bp} + G_{jb} · (∂_l G^{bp}))` by
  -- `G^{aj}` on the left and sum: this isolates `∂_l G^{ap}`. But we actually
  -- want to express `∂_l G^{jp}` directly, so we use a different angle.
  --
  -- Setting up: from `∑_b ((∂_l G_{jb}) · G^{bp} + G_{jb} · (∂_l G^{bp})) = 0`,
  -- we have `∑_b G_{jb} · (∂_l G^{bp}) = -∑_b (∂_l G_{jb}) · G^{bp}`.
  --
  -- Multiply both sides by G^{??j}... wait, we want ∂_l G^{jp}, which has index
  -- j. So we multiply by G^{ej} on the LEFT (for free index e), sum over j —
  -- but j is fixed in our setup.
  --
  -- Let's switch indices. Apply the identity to indices (a, p) with free direction
  -- `l`. We get: `∑_b ((∂_l G_{ab}) · G^{bp} + G_{ab} · (∂_l G^{bp})) = 0`.
  -- Multiply by G^{ja} and sum over a:
  -- `∑_{a, b} G^{ja} · (∂_l G_{ab}) · G^{bp} + ∑_{a, b} G^{ja} · G_{ab} · (∂_l G^{bp}) = 0`.
  -- The second term: ∑_a G^{ja} · G_{ab} = δ^j_b. So:
  -- `∑_{a, b} G^{ja} · (∂_l G_{ab}) · G^{bp} + ∑_b δ^j_b · (∂_l G^{bp}) = 0`.
  -- I.e., `∑_{a, b} G^{ja} · (∂_l G_{ab}) · G^{bp} + ∂_l G^{jp} = 0`.
  -- Hence `∂_l G^{jp} = -∑_{a, b} G^{ja} · G^{bp} · (∂_l G_{ab})`.
  --
  -- We now formalise this. We need the identity at (a, p) for each `a`.
  have hidentity_ap : ∀ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
            chartInvGramOnE (I := I) g α b p y₀ +
          chartGramOnE (I := I) g α a b y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) = 0 := by
    intro a
    -- Same proof as for j, with a in place of j.
    have hfS_a_eventually : ∀ᶠ y in 𝓝 y₀,
        (∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y * chartInvGramOnE (I := I) g α b p y) =
            (if a = p then (1 : ℝ) else 0) := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨interior (extChartAt I α).target, hy_nhd, ?_⟩
      intro y hy_int
      exact hidentity a y (interior_subset hy_int)
    have hf_diff_a : ∀ b : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun y : E => chartGramOnE (I := I) g α a b y *
          chartInvGramOnE (I := I) g α b p y) y₀ :=
      fun b => DifferentiableAt.fun_mul
        (chartGramOnE_differentiableAt_interior (I := I) g α a b hy)
        (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)
    have hf_a_diff : DifferentiableAt ℝ (fun y : E =>
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y *
            chartInvGramOnE (I := I) g α b p y) y₀ :=
      DifferentiableAt.fun_sum (fun b _ => hf_diff_a b)
    have hpartial_zero : partialDeriv (E := E) l (fun y : E =>
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y *
            chartInvGramOnE (I := I) g α b p y) y₀ = 0 := by
      have hfderiv_eq_zero : fderiv ℝ (fun y : E =>
          ∑ b : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α a b y *
              chartInvGramOnE (I := I) g α b p y) y₀ = 0 := by
        have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hfS_a_eventually
        rw [h1]
        simp
      unfold partialDeriv
      rw [hfderiv_eq_zero]
      rfl
    -- Expand and equate to zero.
    have hexpand_a : partialDeriv (E := E) l (fun y : E =>
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y *
            chartInvGramOnE (I := I) g α b p y) y₀ =
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) := by
      unfold partialDeriv
      rw [fderiv_fun_sum (fun b _ => hf_diff_a b)]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [fderiv_fun_mul (𝕜 := ℝ)
        (chartGramOnE_differentiableAt_interior (I := I) g α a b hy)
        (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hexpand_a] at hpartial_zero
    exact hpartial_zero
  -- Now multiply each `hidentity_ap a` by `G^{ja}` and sum over a.
  have hmul_a : ∀ a : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j a y₀ *
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) = 0 := by
    intro a
    rw [hidentity_ap a, mul_zero]
  have hsum_zero : ∑ a : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j a y₀ *
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) = 0 := by
    refine Finset.sum_eq_zero ?_
    intros a _
    exact hmul_a a
  -- Now expand: split into two sums over (a, b).
  have hsplit : ∑ a : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j a y₀ *
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) =
      (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀)) +
      (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit] at hsum_zero
  -- Now identify the second sum: ∑_{ab} G^{ja} · G_{ab} · ∂_l G^{bp}
  --                            = ∑_b (∑_a G^{ja} · G_{ab}) · ∂_l G^{bp}
  --                            = ∑_b δ^j_b · ∂_l G^{bp} = ∂_l G^{jp}.
  have hsecond : (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀)) =
      partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j p) y₀ := by
    -- Swap order, factor out ∂_l G^{bp}.
    rw [show (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j a y₀ *
                  (chartGramOnE (I := I) g α a b y₀ *
                    partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀)) =
          (∑ b : Fin (Module.finrank ℝ E),
            (∑ a : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j a y₀ *
                chartGramOnE (I := I) g α a b y₀) *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring]
    -- Inner sum: ∑_a G^{ja} · G_{ab} = δ^j_b (since chartInvGram · chartGram = I,
    -- on the chart base set).
    have hinner : ∀ b : Fin (Module.finrank ℝ E),
        (∑ a : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            chartGramOnE (I := I) g α a b y₀) =
        (if j = b then (1 : ℝ) else 0) := by
      intro b
      have hprod_eq :
          (∑ a : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y₀ *
              chartGramOnE (I := I) g α a b y₀) =
          (chartInvGramMatrix (I := I) g α z₀ *
            chartGramMatrix (I := I) g α z₀) j b := by
        simp only [Matrix.mul_apply]
        rfl
      rw [hprod_eq]
      rw [chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hz_base]
      by_cases hjb : j = b
      · subst hjb
        simp
      · rw [if_neg hjb]
        exact Matrix.one_apply_ne hjb
    rw [show (∑ b : Fin (Module.finrank ℝ E),
            (∑ a : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j a y₀ *
                chartGramOnE (I := I) g α a b y₀) *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) =
        ∑ b : Fin (Module.finrank ℝ E),
          (if j = b then (1 : ℝ) else 0) *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀ from by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hinner b]]
    -- Now: ∑_b (if j = b then 1 else 0) · F b = F j.
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; ring
    · intros b _ hbj
      have hjb : ¬ j = b := fun h => hbj h.symm
      rw [if_neg hjb, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  -- Substitute hsecond into hsum_zero and solve for ∂_l G^{jp}.
  rw [hsecond] at hsum_zero
  -- hsum_zero: First sum + ∂_l G^{jp} y₀ = 0.
  -- So ∂_l G^{jp} y₀ = -First sum.
  have hgoal : partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j p) y₀ =
      -(∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀)) := by
    linarith [hsum_zero]
  rw [hgoal]
  -- Final algebraic rearrangement.
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-! ### Smoothness of partial derivatives of `chartGramOnE`

Building on `chartGramOnE_contDiffOn`, the partial derivative of `chartGramOnE`
in any direction is again `C^∞` on the interior of the chart target. -/

/-- `partialDeriv j (chartGramOnE g α a b)` is `C^∞` on the interior of the
chart target. -/
private lemma partialDeriv_chartGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α a b))
      (interior (extChartAt I α).target) := by
  classical
  have hG_target : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α a b)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α a b
  have hG_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α a b)
      (interior (extChartAt I α).target) := hG_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α a b))
      (interior (extChartAt I α).target) :=
    hG_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

/-- `partialDeriv j (chartGramOnE g α a b)` is differentiable at any point
in the interior of the chart target. -/
private lemma partialDeriv_chartGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j a b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α a b)) y := by
  have hcd_int : ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α a b))
      (interior (extChartAt I α).target) :=
    partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α j a b
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

/-- `partialDeriv j (chartInvGramOnE g α k l)` is `C^∞` on the interior of the
chart target. -/
private lemma partialDeriv_chartInvGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) := by
  classical
  have hG_target : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α k l
  have hG_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (interior (extChartAt I α).target) := hG_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) :=
    hG_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

/-- `partialDeriv j (chartInvGramOnE g α k l)` is differentiable at any point
in the interior of the chart target. -/
private lemma partialDeriv_chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j k l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l)) y := by
  have hcd_int : ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) :=
    partialDeriv_chartInvGramOnE_contDiffOn_interior (I := I) g α j k l
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

/-! ### Second-derivative formula for `∂² G^{kl}`

Differentiating the first-derivative formula `∂_j G^{kl} = -∑_{a,b} G^{ka} G^{bl}
∂_j G_{ab}` once more in direction `i`, and substituting the first-derivative
formula for `∂_i G^{ka}` and `∂_i G^{bl}` in the resulting Leibniz expansion,
gives an explicit formula for `∂_i ∂_j G^{kl}` in terms of `∂ G_{pq}` and
`∂² G_{pq}`. -/

/-- The second-derivative formula for the inverse Gram matrix entries:
for any directions `i, j` and any matrix index `(k, l)`,
`∂_i ∂_j G^{kl}(y₀)` equals
`∑_{p,q,r,s} G^{kr} G^{ps} G^{ql} (∂_i G_{rs}) (∂_j G_{pq})`
`+ ∑_{p,q,r,s} G^{kp} G^{qr} G^{ls} (∂_i G_{rs}) (∂_j G_{pq})`
`- ∑_{p,q} G^{kp} G^{ql} (∂_i ∂_j G_{pq})(y₀)`.

This is obtained by differentiating the first-derivative formula
`∂_j G^{kl} = -∑_{a,b} G^{ka} G^{bl} ∂_j G_{ab}` in direction `i`, applying
Leibniz on the resulting product `G^{ka} · G^{bl} · ∂_j G_{ab}`, and substituting
the first-derivative formula again for `∂_i G^{ka}` and `∂_i G^{bl}`. -/
lemma partialDeriv2_chartInvGramOnE_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (i j : Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) i
        (fun y' : E => partialDeriv (E := E) j
          (chartInvGramOnE (I := I) g α k l) y') y₀ =
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
        ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α p s y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) +
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
        ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q r y₀ *
            chartInvGramOnE (I := I) g α l s y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) -
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i
              (fun y' : E => partialDeriv (E := E) j
                (chartGramOnE (I := I) g α p q) y') y₀) := by
  classical
  -- Step 1: rewrite the inner function `partialDeriv j (chartInvGramOnE g α k l)`
  -- via `partialDeriv_chartInvGramOnE_eq` on a neighbourhood of `y₀`.
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy
  -- Define the function `F y' := -∑_{p,q} G^{kp}(y') · G^{ql}(y') · (∂_j G_{pq})(y')`.
  set F : E → ℝ := fun y' =>
    -∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k p y' *
          chartInvGramOnE (I := I) g α q l y' *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y' with hF_def
  -- LHS function = F on interior.
  have hLHS_F : ∀ᶠ y' in 𝓝 y₀,
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y' = F y' := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨interior (extChartAt I α).target, hy_nhd, ?_⟩
    intro y' hy'_int
    rw [hF_def]
    exact partialDeriv_chartInvGramOnE_eq (I := I) g α y' j k l hy'_int
  -- Step 2: their fderiv at y₀ are equal.
  have hfderiv_eq : fderiv ℝ
      (fun y' : E => partialDeriv (E := E) j
        (chartInvGramOnE (I := I) g α k l) y') y₀ =
      fderiv ℝ F y₀ :=
    Filter.EventuallyEq.fderiv_eq hLHS_F
  -- Step 3: convert the goal into one about partialDeriv i F y₀ (via fderiv).
  have hpartial_eq : partialDeriv (E := E) i
      (fun y' : E => partialDeriv (E := E) j
        (chartInvGramOnE (I := I) g α k l) y') y₀ =
      partialDeriv (E := E) i F y₀ := by
    change (fderiv ℝ (fun y' : E => partialDeriv (E := E) j
        (chartInvGramOnE (I := I) g α k l) y') y₀)
        ((chartModelBasis E) i) =
      (fderiv ℝ F y₀) ((chartModelBasis E) i)
    rw [hfderiv_eq]
  rw [hpartial_eq]
  -- Differentiability hypotheses for the per-summand product rule.
  have hG_diff_kp : ∀ p : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k p) y₀ :=
    fun p => chartInvGramOnE_differentiableAt_interior (I := I) g α k p hy
  have hG_diff_ql : ∀ q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α q l) y₀ :=
    fun q => chartInvGramOnE_differentiableAt_interior (I := I) g α q l hy
  have h_dG_diff : ∀ p q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α p q)) y₀ :=
    fun p q => partialDeriv_chartGramOnE_differentiableAt_interior
      (I := I) g α j p q hy
  have h_summand_diff : ∀ p q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartInvGramOnE (I := I) g α k p y' *
          chartInvGramOnE (I := I) g α q l y' *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ :=
    fun p q => DifferentiableAt.fun_mul
      (DifferentiableAt.fun_mul (hG_diff_kp p) (hG_diff_ql q))
      (h_dG_diff p q)
  have h_inner_sum_diff : ∀ p : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y' *
          chartInvGramOnE (I := I) g α q l y' *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ :=
    fun p => DifferentiableAt.fun_sum (fun q _ => h_summand_diff p q)
  -- Step 4: Compute partialDeriv i F y₀ via Leibniz on each (p, q) summand,
  -- exposing the three pieces (∂_i G^{kp})·G^{ql}·∂_j G_{pq} +
  -- G^{kp}·(∂_i G^{ql})·∂_j G_{pq} + G^{kp}·G^{ql}·∂_i ∂_j G_{pq}.
  have hpartial_F : partialDeriv (E := E) i F y₀ =
      -∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
              chartInvGramOnE (I := I) g α q l y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
            chartInvGramOnE (I := I) g α k p y₀ *
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
            chartInvGramOnE (I := I) g α k p y₀ *
              chartInvGramOnE (I := I) g α q l y₀ *
              partialDeriv (E := E) i
                (fun y' : E => partialDeriv (E := E) j
                  (chartGramOnE (I := I) g α p q) y') y₀) := by
    change (fderiv ℝ F y₀) ((chartModelBasis E) i) = _
    rw [hF_def]
    rw [show
      fderiv ℝ (fun y' : E =>
          -∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k p y' *
                chartInvGramOnE (I := I) g α q l y' *
                partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ =
        -fderiv ℝ (fun y' : E =>
          ∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k p y' *
                chartInvGramOnE (I := I) g α q l y' *
                partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ from
      fderiv_neg]
    rw [fderiv_fun_sum (fun p _ => h_inner_sum_diff p)]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, neg_inj]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [fderiv_fun_sum (fun q _ => h_summand_diff p q)]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [fderiv_fun_mul (𝕜 := ℝ)
      (DifferentiableAt.fun_mul (hG_diff_kp p) (hG_diff_ql q))
      (h_dG_diff p q)]
    rw [fderiv_fun_mul (𝕜 := ℝ) (hG_diff_kp p) (hG_diff_ql q)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    -- The fderiv-evaluations equal the corresponding partialDerivs by definition;
    -- use a `change` to unify the form, then ring.
    change chartInvGramOnE (I := I) g α k p y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) i
          (fun y' : E => partialDeriv (E := E) j
            (chartGramOnE (I := I) g α p q) y') y₀ +
      partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ *
        (chartInvGramOnE (I := I) g α k p y₀ *
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ +
        chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀) =
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
      chartInvGramOnE (I := I) g α k p y₀ *
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
      chartInvGramOnE (I := I) g α k p y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) i
          (fun y' : E => partialDeriv (E := E) j
            (chartGramOnE (I := I) g α p q) y') y₀
    ring
  rw [hpartial_F]
  -- Step 5: Substitute the first-derivative formula for ∂_i G^{kp} and ∂_i G^{ql}.
  have hpoint_kp : ∀ p : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ =
        -∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ :=
    fun p => partialDeriv_chartInvGramOnE_eq (I := I) g α y₀ i k p hy
  have hpoint_ql : ∀ q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ =
        -∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ :=
    fun q => partialDeriv_chartInvGramOnE_eq (I := I) g α y₀ i q l hy
  -- Symmetry of the inverse Gram (used for renaming `s ↔ p` and `s ↔ l`).
  have hsymm : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α a b y₀ =
        chartInvGramOnE (I := I) g α b a y₀ := by
    intro a b
    unfold chartInvGramOnE
    set z := (extChartAt I α).symm y₀
    have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α z
    have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
      hG_hermit.inv
    have hentry := hGinv_hermit.apply a b
    unfold chartInvGramMatrix
    have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ b a) =
        (chartGramMatrix (I := I) g α z)⁻¹ a b := hentry
    rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ b a) =
        (chartGramMatrix (I := I) g α z)⁻¹ b a from rfl] at hstar
    exact hstar.symm
  -- Step 6: Substitute on each summand. Each (p, q) summand `(A_pq + B_pq + C_pq)`
  -- becomes a 4-fold sum over (p, q, r, s). Distribute negations and sums to
  -- match canonical form.
  -- We perform the substitution on each (p, q) summand using Finset.sum_congr.
  refine (?_ : _ = _)
  -- Reduce per (p, q): substitute hpoint_kp p and hpoint_ql q.
  have hpq : ∀ p q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
        chartInvGramOnE (I := I) g α k p y₀ *
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i
            (fun y' : E => partialDeriv (E := E) j
              (chartGramOnE (I := I) g α p q) y') y₀ =
      (∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
      (∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q r y₀ *
            chartInvGramOnE (I := I) g α s l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
      chartInvGramOnE (I := I) g α k p y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) i
          (fun y' : E => partialDeriv (E := E) j
            (chartGramOnE (I := I) g α p q) y') y₀ := by
    intro p q
    rw [hpoint_kp p, hpoint_ql q]
    -- Distribute the sum_neg through products.
    have h1 : (-∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
      ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) := by
      rw [neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
      rw [show
        -∑ r : Fin (Module.finrank ℝ E),
          (∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ r : Fin (Module.finrank ℝ E),
          -((∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      rw [show
        -∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      ring
    have h2 : chartInvGramOnE (I := I) g α k p y₀ *
        (-∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
      ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q r y₀ *
            chartInvGramOnE (I := I) g α s l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) := by
      rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
      rw [show
        -∑ r : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            (∑ s : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α q r y₀ *
                chartInvGramOnE (I := I) g α s l y₀ *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ r : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            (∑ s : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α q r y₀ *
                chartInvGramOnE (I := I) g α s l y₀ *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [show
        -∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            (chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            (chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      ring
    rw [h1, h2]
  rw [show
    (-∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
          chartInvGramOnE (I := I) g α k p y₀ *
            partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
          chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i
              (fun y' : E => partialDeriv (E := E) j
                (chartGramOnE (I := I) g α p q) y') y₀)) =
    (-∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
        ((∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            -(chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              chartInvGramOnE (I := I) g α q l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
        (∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            -(chartInvGramOnE (I := I) g α k p y₀ *
              chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i
            (fun y' : E => partialDeriv (E := E) j
              (chartGramOnE (I := I) g α p q) y') y₀)) from by
    refine congrArg Neg.neg ?_
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    exact hpq p q]
  -- Distribute negation across the inner sum, simplify with Finset.sum_neg_distrib.
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_add_rev, neg_neg]
  -- Match symmetry indices on the RHS.
  rw [show
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k r y₀ *
          chartInvGramOnE (I := I) g α p s y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) =
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k r y₀ *
          chartInvGramOnE (I := I) g α s p y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hsymm p s]]
  rw [show
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q r y₀ *
          chartInvGramOnE (I := I) g α l s y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) =
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q r y₀ *
          chartInvGramOnE (I := I) g α s l y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hsymm l s]]
  ring



/-! ### Main theorem: the contracted Christoffel identity holds

We now combine the matrix-inverse derivative identity, Jacobi's formula, and
the symmetry of the Gram matrix to discharge `ChartContractedChristoffelOn`. -/

/-- Symmetry of the chart Gram matrix entries pulled back to `E`, in the
function form. -/
lemma chartGramOnE_symm_fun
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j = chartGramOnE (I := I) g α j i := by
  funext y
  exact chartGramOnE_symm (I := I) g α i j y

/-- Symmetry of the chart inverse Gram matrix entries pulled back to `E`. -/
private lemma chartInvGramOnE_symm_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y = chartInvGramOnE (I := I) g α j i y := by
  unfold chartInvGramOnE
  set z := (extChartAt I α).symm y
  have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α z
  have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
    hG_hermit.inv
  have hentry := hGinv_hermit.apply i j
  unfold chartInvGramMatrix
  -- For ℝ entries, `star = id`, so `(G⁻¹) j i = (G⁻¹) i j`.
  have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
  rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
  exact hstar.symm

/-- **Discharge of the contracted Christoffel identity.**
For any smooth Riemannian metric `g` on `M`, any chart base point `α : M`, any
chart-target point `y` in the interior of the chart target, and any free index
`j`, the predicate `ChartContractedChristoffelOn g α y j` holds.

This identity is the chart-coordinate algebraic content of `div(g · G^{j·}) = 0`
expressing the divergence-free property of the inverse metric "vector field"
against the Riemannian volume density. The proof combines Jacobi's formula for
the determinant, the matrix-inverse derivative identity `∂(G⁻¹) = -G⁻¹·∂G·G⁻¹`,
and the symmetry of the Gram matrix. -/
theorem chartContractedChristoffel_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    (y : E) (j : Fin (Module.finrank ℝ E))
    (hy : y ∈ interior (extChartAt I α).target) :
    ChartContractedChristoffelOn (I := I) g α y j := by
  classical
  unfold ChartContractedChristoffelOn
  set y₀ := y with hy₀_def
  -- Membership in the chart target and base set.
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  have hz_base : (extChartAt I α).symm y₀ ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hytgt
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  -- Density positivity.
  have hD_pos : 0 < chartDensityOnE (I := I) g α y₀ := by
    unfold chartDensityOnE
    exact chartDensity_pos (I := I) g α hz_base
  have hD_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := ne_of_gt hD_pos
  -- Set short notation.
  set D : ℝ := chartDensityOnE (I := I) g α y₀ with hD_def
  set GU : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartInvGramOnE (I := I) g α i k y₀ with hGU_def
  set GD : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartGramOnE (I := I) g α i k y₀ with hGD_def
  set dGD : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun l a b => partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ with hdGD_def
  set dGU : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun l a b => partialDeriv (E := E) l (chartInvGramOnE (I := I) g α a b) y₀ with hdGU_def
  set dD : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ with hdD_def
  -- Step 0: Expand the LHS of the identity using the definition of chartChristoffel.
  -- LHS := ∑_{i k} G^{ik}(y₀) · Γ^j_{ik}(y₀).
  -- Γ^j_{ik}(y₀) = (1/2) ∑_l G^{jl}(y₀) · (∂_i G_{lk}(y₀) + ∂_k G_{li}(y₀) - ∂_l G_{ik}(y₀)).
  have hLHS_expand : ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i k y₀ *
          chartChristoffel (I := I) g α i k j y₀ =
        (1 / 2 : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU i k * GU j l *
                  (dGD i l k + dGD k l i - dGD l i k) := by
    -- First, unfold chartChristoffel inside the double sum.
    have hstep1 : ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i k y₀ *
            chartChristoffel (I := I) g α i k j y₀ =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i k y₀ *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l *
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y₀ +
                   partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y₀ -
                   partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [chartChristoffel_def]
    rw [hstep1]
    -- Goal:
    --  ∑ i, ∑ k, GU i k * ((1/2) * ∑ l, chartInvGramMatrix g α (symm y₀) j l *
    --             (∂_i G_{lk} + ∂_k G_{li} - ∂_l G_{ik}))
    --  = (1/2) * ∑ i, ∑ k, ∑ l, GU i k * GU j l * (∂_i G_{lk} + ∂_k G_{li} - ∂_l G_{ik})
    -- Reorder both sides to a canonical form via Finset.mul_sum and ring on summand.
    -- First convert RHS: pull (1/2) inside the triple sum.
    rw [show (1 / 2 : ℝ) *
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * (dGD i l k + dGD k l i - dGD l i k) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (1 / 2 : ℝ) *
                (GU i k * GU j l * (dGD i l k + dGD k l i - dGD l i k)) from by
      simp only [Finset.mul_sum]]
    -- Now both sides are triple sums. Match them summand-by-summand.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- Goal: GU i k * ((1/2) * ∑ l, ...) = ∑ l, (1/2) * (GU i k * GU j l * (...)).
    -- Pull `GU i k *` and `(1/2)` inside.
    rw [show chartInvGramOnE (I := I) g α i k y₀ *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l *
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y₀ +
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y₀ -
                  partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀)) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i k y₀ *
            ((1 / 2 : ℝ) *
              (chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l *
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y₀ +
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y₀ -
                  partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀))) from by
      simp only [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    -- chartInvGramOnE g α j l y₀ = chartInvGramMatrix g α (symm y₀) j l (definitionally).
    -- Both sides reduce to (1/2) * GU i k * GU j l * (...).
    have hGUjl : GU j l =
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l := rfl
    have hGUik : GU i k = chartInvGramOnE (I := I) g α i k y₀ := rfl
    rw [hGUjl, hGUik]
    ring
  -- Step 1: Use symmetry G^{ik} = G^{ki} and dummy renaming i ↔ k to combine
  -- the first two terms ∂_i G_{lk} + ∂_k G_{li}.
  -- For each fixed l, ∑_{ik} GU(i,k) · GU(j,l) · ∂_i G_{lk}
  --                = ∑_{ki} GU(k,i) · GU(j,l) · ∂_k G_{li}  (rename i↔k)
  --                = ∑_{ik} GU(i,k) · GU(j,l) · ∂_k G_{li}  (use GU(k,i)=GU(i,k)).
  have hsym_swap : ∀ l : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          GU i k * GU j l * dGD i l k) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            GU i k * GU j l * dGD k l i) := by
    intro l
    -- LHS = ∑_i ∑_k GU(i,k) · GU(j,l) · ∂_i G_{lk}.
    -- Swap dummy (i, k) ↔ (k, i): ∑_i ∑_k F(i,k) = ∑_k ∑_i F(i,k) = ∑_i ∑_k F(k, i).
    -- So LHS = ∑_i ∑_k GU(k, i) · GU(j, l) · ∂_k G_{li}.
    -- Use symmetry: GU(k, i) = GU(i, k). Result = ∑_i ∑_k GU(i, k) · GU(j, l) · ∂_k G_{li} = RHS.
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD i l k) =
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              GU i k * GU j l * dGD i l k) from Finset.sum_comm]
    -- Now goal: ∑_k ∑_i GU(i, k) · GU(j, l) · dGD(i, l, k) = ∑_i ∑_k GU(i, k) · GU(j, l) · dGD(k, l, i).
    -- Rename: outer becomes i, inner becomes k.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- Goal: GU(k, i) · GU(j, l) · dGD(k, l, i) = GU(i, k) · GU(j, l) · dGD(k, l, i).
    -- (After the swap, the outer index `k` from sum_comm is renamed to `i`, and inner `i` is renamed to `k`.)
    change GU k i * GU j l * dGD k l i = GU i k * GU j l * dGD k l i
    have hGUki : GU k i = GU i k := by
      change chartInvGramOnE (I := I) g α k i y₀ = chartInvGramOnE (I := I) g α i k y₀
      exact chartInvGramOnE_symm_pointwise (I := I) g α k i y₀
    rw [hGUki]
  -- Now use hsym_swap to rewrite the LHS:
  --   (1/2) ∑_l (∑_{ik} GU(i,k) GU(j,l) (∂_i G_{lk} + ∂_k G_{li}))
  --   - (1/2) ∑_l ∑_{ik} GU(i,k) GU(j,l) ∂_l G_{ik}
  -- = ∑_l (∑_{ik} GU(i,k) GU(j,l) ∂_i G_{lk})
  --   - (1/2) ∑_l ∑_{ik} GU(i,k) GU(j,l) ∂_l G_{ik}.
  have hLHS_simplified : ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i k y₀ *
          chartChristoffel (I := I) g α i k j y₀ =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              GU i k * GU j l * dGD i l k) -
        (1 / 2 : ℝ) *
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD l i k) := by
    rw [hLHS_expand]
    -- Distribute (a + b - c) into 3 sums.
    -- Step 1: distribute multiplication on (a + b - c) into (a' + b' - c') summand-wise.
    rw [show
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              GU i k * GU j l * (dGD i l k + dGD k l i - dGD l i k) =
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (GU i k * GU j l * dGD i l k + GU i k * GU j l * dGD k l i -
                GU i k * GU j l * dGD l i k) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring]
    -- Step 2: split each summand-level sum into three sums via `sum_add_distrib` and `sum_sub_distrib`.
    -- Apply Finset.sum_add_distrib and Finset.sum_sub_distrib at every level.
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- Step 3: Use hsym_swap (rename via a fixed l, so we apply it at each l).
    -- Goal:
    --  T := ∑_l ∑_i ∑_k ... dGD i l k  (after distribution; but indices may permute)
    -- We rewrite the second triple sum (with dGD k l i) using hsym_swap.
    have hsecond_eq : ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            GU i k * GU j l * dGD k l i =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD i l k := by
      -- Pull `∑_l` to the outside (for the swap to make sense): swap the order
      -- so that l is outermost.
      rw [show ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD k l i =
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD k l i from by
        -- Swap inner two (k, l) -> (l, k).
        rw [show (∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD k l i) =
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ k : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD k l i) from by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [Finset.sum_comm]]
        -- Now swap outer two (i, l) -> (l, i).
        rw [Finset.sum_comm]]
      rw [show ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD i l k =
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD i l k from by
        rw [show (∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD i l k) =
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ k : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD i l k) from by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [Finset.sum_comm]]
        rw [Finset.sum_comm]]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact (hsym_swap l).symm
    rw [hsecond_eq]
    ring
  -- Step 2: Apply matrix-inverse derivative identity to simplify the first
  -- triple sum, and Jacobi to simplify the second.
  --
  -- First triple sum: ∑_{ikl} GU(i,k) · GU(j,l) · dGD(i, l, k).
  -- Use matrix-inverse derivative identity to express this.
  -- We have: ∂_i G^{jp}(y₀) = -∑_{a,b} GU(j, a) · GU(b, p) · dGD(i, a, b).  (with `l = i` in the identity)
  --
  -- Hmm, we want ∑_{ikl} GU(i,k) GU(j,l) dGD(i, l, k). Let's denote variables:
  -- partial direction is l_part, gram down indices are α_d, β_d. So we have
  -- dGD(l_part, α_d, β_d) := ∂_{l_part} G_{α_d β_d}.
  --
  -- The matrix-inverse derivative identity:
  --   ∂_l G^{j p}(y₀) = -∑_{a, b} GU(j, a) GU(b, p) · dGD(l, a, b).
  -- I.e.,  dGU(l, j, p) = -∑_{a, b} GU(j, a) GU(b, p) · dGD(l, a, b).
  --
  -- We want to identify ∑_{ikl} GU(i,k) · GU(j,l) · dGD(i, l, k):
  -- partial direction is `i`, lower indices are `(l, k)`. The "partial" index `i` is
  -- summed AND appears as a Gram-up index `GU(i, k)`. Specifically:
  -- ∑_{ikl} GU(i,k) GU(j,l) dGD(i, l, k)
  --   = ∑_l GU(j, l) · (∑_{ik} GU(i,k) · dGD(i, l, k))  -- (factor out GU(j,l))
  -- For each fixed l, we examine the inner sum: ∑_{ik} GU(i,k) · ∂_i G_{lk}(y₀).
  --
  -- Use the matrix-inverse identity at indices (l, ·): ∂_? G^{l q} = -∑_{a,b} GU(l,a) GU(b,q) dGD(?,a,b).
  -- That's not quite right.
  --
  -- Different angle: rename b in the matrix-inverse identity. We have
  -- ∂_l G^{j a}(y₀) = -∑_{p, b} GU(j, p) GU(b, a) dGD(l, p, b).
  -- Let's set `q := j` (free), `r := p` (dummy), `s := q` (dummy), and identify
  -- ∑_a ∂_a G^{r a} for fixed r.
  --
  -- From identity (with j fixed):
  -- ∂_l G^{j a}(y₀) = -∑_{p, b} GU(j, p) · GU(b, a) · dGD(l, p, b).
  -- So ∑_a ∂_a G^{j a}(y₀) (i.e., `dGU(a, j, a)` summed over a)
  --                       = -∑_{a, p, b} GU(j, p) · GU(b, a) · dGD(a, p, b).
  -- (using l = a in the identity)
  --
  -- We want ∑_{ikl} GU(i, k) · GU(j, l) · dGD(i, l, k). Rename i → a, k → b, l → c:
  -- = ∑_{a, b, c} GU(a, b) · GU(j, c) · dGD(a, c, b)
  -- = ∑_c GU(j, c) · (∑_{a, b} GU(a, b) · dGD(a, c, b))
  -- For fixed c (= l in original), compare with `-∑_{a, p, b} GU(j, p) GU(b, a) dGD(a, p, b)`:
  -- We want ∑_{ab} GU(a,b) · ∂_a G_{cb}.
  --
  -- Now to compute `∑_a ∂_a G^{jc}(y₀) = -∑_{a, p, b} GU(j, p) · GU(b, a) · dGD(a, p, b)`:
  -- Rename in this: a→a', p→a, b→b. Then = -∑_{a', a, b} GU(j, a) · GU(b, a') · dGD(a', a, b).
  -- ...
  -- This is getting tangled. Let me proceed step by step in Lean.
  --
  -- Actually here's the cleanest path:
  --
  -- (A) `∑_l ∂_l G^{j l}(y₀) = -∑_{l, a, b} GU(j, a) · GU(b, l) · dGD(l, a, b)`
  --     = -∑_{a, b} GU(j, a) · (∑_l GU(b, l) · dGD(l, a, b)).
  --
  -- Hmm, that still has dGD on partial-derivative direction `l`.
  --
  -- Direct approach: Use the matrix-inverse derivative identity entry-wise.
  -- We have for each (l, a, b):
  -- (dGU l a b at y₀) = -∑_{p, q} GU(a, p)(y₀) · GU(q, b)(y₀) · dGD(l, p, q).
  -- (Here `l` is partial direction; `a, b` are inverse-Gram indices.)
  --
  -- We want to compute the first triple sum:
  --   T := ∑_{ikl} GU(i, k) · GU(j, l) · dGD(i, l, k).
  -- This is partial direction = i, gram-down indices = (l, k).
  --
  -- Key observation: there's no immediate matrix-inverse identity that tells us
  -- about `∂_i G_{l, k}` directly. The matrix-inverse identity gives `∂(G⁻¹)` in
  -- terms of `∂(G)`, not the other way around.
  --
  -- But we can run the identity in reverse: the matrix `∑_b G^{a b} · G_{b c} = δ^a_c`
  -- gives us `∑_a G^{i k} ∂_i G_{l k}` ... no wait.
  --
  -- Let's compute ∑_a ∂_a G^{j a} by direct expansion:
  -- ∑_a ∂_a G^{j a}(y₀) = ∑_a (dGU(a, j, a)) by definition.
  -- Apply matrix-inverse derivative identity to each:
  -- dGU(a, j, a) = -∑_{p, q} GU(j, p) · GU(q, a) · dGD(a, p, q).
  -- Hence ∑_a dGU(a, j, a) = -∑_a ∑_{p,q} GU(j, p) · GU(q, a) · dGD(a, p, q)
  --                       = -∑_{a, p, q} GU(j, p) · GU(q, a) · dGD(a, p, q).
  -- Reorder: rename q ↔ b, p ↔ c, a → a:
  -- = -∑_{a, c, b} GU(j, c) · GU(b, a) · dGD(a, c, b).
  -- Now use symmetry of GU: GU(b, a) = GU(a, b).
  -- = -∑_{a, c, b} GU(j, c) · GU(a, b) · dGD(a, c, b).
  -- Rename a → i, b → k, c → l:
  -- = -∑_{i, k, l} GU(j, l) · GU(i, k) · dGD(i, l, k) = -T.
  --
  -- So **T = -∑_a ∂_a G^{j a}(y₀)**.
  --
  -- This is what we want. Now formalise.
  have hT_eq : ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          GU i k * GU j l * dGD i l k =
        -(∑ a : Fin (Module.finrank ℝ E), dGU a j a) := by
    -- Apply matrix-inverse derivative identity to each `dGU(a, j, a)`.
    have hidentity : ∀ a : Fin (Module.finrank ℝ E),
        dGU a j a =
          -∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              GU j p * GU q a * dGD a p q := by
      intro a
      change partialDeriv (E := E) a (chartInvGramOnE (I := I) g α j a) y₀ =
          -∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j p y₀ *
                chartInvGramOnE (I := I) g α q a y₀ *
                partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) y₀
      rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y₀ a j a hy]
    -- Sum over a.
    have hsum_dGU : ∑ a : Fin (Module.finrank ℝ E), dGU a j a =
        -∑ a : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              GU j p * GU q a * dGD a p q := by
      rw [show (∑ a : Fin (Module.finrank ℝ E), dGU a j a) =
          ∑ a : Fin (Module.finrank ℝ E),
            -∑ p : Fin (Module.finrank ℝ E),
              ∑ q : Fin (Module.finrank ℝ E),
                GU j p * GU q a * dGD a p q from
            Finset.sum_congr rfl (fun a _ => hidentity a)]
      rw [Finset.sum_neg_distrib]
    rw [hsum_dGU]
    -- Now: T = -(- ∑_a ∑_p ∑_q GU(j, p) GU(q, a) dGD(a, p, q)).
    -- Cancel double negation; rename: a → i, p → l, q → k, and use symmetry of GU.
    rw [neg_neg]
    -- Reorder dummy indices: ∑_a ∑_p ∑_q GU(j,p) GU(q,a) dGD(a,p,q)
    --   = ∑_i ∑_l ∑_k GU(j,l) GU(k,i) dGD(i,l,k).
    -- Rename: a → i, p → l, q → k.
    -- Now use symmetry GU(k, i) = GU(i, k).
    rw [show (∑ a : Fin (Module.finrank ℝ E),
              ∑ p : Fin (Module.finrank ℝ E),
                ∑ q : Fin (Module.finrank ℝ E),
                  GU j p * GU q a * dGD a p q) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU j l * GU k i * dGD i l k) from rfl]
    -- Apply symmetry of GU on the q-index.
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU j l * GU k i * dGD i l k) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU j l * GU i k * dGD i l k) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hGUki : GU k i = GU i k := by
        change chartInvGramOnE (I := I) g α k i y₀ = chartInvGramOnE (I := I) g α i k y₀
        exact chartInvGramOnE_symm_pointwise (I := I) g α k i y₀
      rw [hGUki]]
    -- Goal: ∑_i ∑_l ∑_k GU(j,l) · GU(i,k) · dGD(i,l,k) =
    --       ∑_i ∑_k ∑_l GU(i,k) · GU(j,l) · dGD(i,l,k).
    -- Swap inner two sums.
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU j l * GU i k * dGD i l k) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU j l * GU i k * dGD i l k) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  -- Second triple sum: ∑_{ikl} GU(i,k) · GU(j,l) · dGD(l, i, k).
  -- = ∑_l GU(j, l) · (∑_{ik} GU(i,k) · ∂_l G_{ik}).
  -- For each fixed l, ∑_{ik} GU(i,k) · ∂_l G_{ik} = trace(G⁻¹ · ∂_l G)
  -- (using symmetry of G to identify (i,k) with (k,i) summation).
  --
  -- Jacobi gives: ∂_l(D)/D = (1/2) · trace(G⁻¹ · ∂_l G) = (1/2) · ∑_{ik} GU(i,k) · ∂_l G_{ik}.
  -- (Where we use symmetry of G_{ik} = G_{ki} so that
  --  trace(G⁻¹ · ∂_l G) = ∑_{ik} GU(i, k) · dGD(l, k, i) = ∑_{ik} GU(i, k) · dGD(l, i, k).)
  --
  -- Hence (1/2) ∑_{ik} GU(i,k) · dGD(l, i, k) = ∂_l(D)/D, i.e.,
  --       ∑_{ik} GU(i,k) · dGD(l, i, k) = 2 · dD(l) / D.
  have hSecondTriple : (1 / 2 : ℝ) *
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            GU i k * GU j l * dGD l i k) =
        ∑ l : Fin (Module.finrank ℝ E),
          GU j l * (dD l / D) := by
    -- For each l: (1/2) · ∑_{ik} GU(i,k) · dGD(l, i, k) = dD(l) / D.
    -- We'll establish this via partialDeriv_chartDensityOnE.
    have hfor_each_l : ∀ l : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k) = dD l / D := by
      intro l
      -- Recall partialDeriv_chartDensityOnE:
      --   dD(l) = (1/2) · trace(G⁻¹ · ∂_l G) · D.
      -- Where ∂_l G is the matrix `Matrix.of fun i j => dGD(l, i, j)`.
      -- And G⁻¹ here is `chartInvGramMatrix g α (symm y₀)`.
      have hjac := partialDeriv_chartDensityOnE (I := I) g α y₀ l hy
      -- Goal-form: (1/2) · ∑_ik GU(i,k) · dGD(l, i, k) = dD(l) / D.
      -- From hjac: dD(l) = (1/2) · trace(...) · D.
      -- trace(M · N) = ∑_a (M · N)_{aa} = ∑_{ab} M(a, b) · N(b, a).
      -- M = G⁻¹, N = ∂_l G; so trace = ∑_{ab} G⁻¹(a, b) · ∂_l G(b, a) = ∑_{ab} GU(a, b) · dGD(l, b, a).
      -- By symmetry of dGD (G is symmetric, hence dGD is symmetric in (i, k)? Actually
      -- ∂_l G_{ba} = ∂_l G_{ab} by symmetry of G), this equals ∑_{ab} GU(a, b) · dGD(l, a, b).
      -- Renaming: (a, b) → (i, k), this is ∑_{ik} GU(i, k) · dGD(l, i, k).
      have htrace_expand :
          Matrix.trace ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ *
            Matrix.of (fun i j => partialDeriv (E := E) l
              (chartGramOnE (I := I) g α i j) y₀)) =
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU i k * dGD l i k := by
        simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.of_apply]
        -- = ∑_a ∑_b (G⁻¹)(a, b) · (∂_l G)(b, a)
        -- After Matrix.of_apply, simp may have already turned (∂_l G)(b, a) into
        -- partialDeriv l (chartGramOnE g α b a) y₀. We use symmetry to swap (b, a).
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        -- Goal: (chartGramMatrix g α (symm y₀))⁻¹ i k * partialDeriv l (chartGramOnE g α k i) y₀ =
        --        GU i k * dGD l i k.
        -- Note that GU i k = chartInvGramOnE g α i k y₀ = (chartGramMatrix g α (symm y₀))⁻¹ i k by
        -- definition, and dGD l i k = partialDeriv l (chartGramOnE g α i k) y₀.
        -- Use symmetry of chartGramOnE to convert (k, i) to (i, k).
        have hGUik : GU i k = (chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ i k := rfl
        have hdGDlik : dGD l i k = partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀ := rfl
        rw [hGUik, hdGDlik, ← chartGramOnE_symm_fun (I := I) g α k i]
      rw [htrace_expand] at hjac
      -- hjac: dD(l) = (1/2) · ∑_ik GU(i, k) · dGD(l, i, k) · D.
      -- Hence (1/2) · ∑_{ik} GU(i, k) · dGD(l, i, k) = dD(l) / D.
      have hfact : dD l = (1 / 2 : ℝ) *
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              GU i k * dGD l i k) * D := by
        rw [hdD_def, hD_def]
        exact hjac
      rw [hfact]
      field_simp
    -- Pull the GU(j, l) factor out and apply hfor_each_l.
    rw [show (1 / 2 : ℝ) *
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD l i k) =
        (1 / 2 : ℝ) *
            ∑ l : Fin (Module.finrank ℝ E),
              GU j l * (∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k) from by
      -- Reorder sums: pull `∑ l` outside and factor `GU j l`.
      congr 1
      -- Goal: ∑_i ∑_k ∑_l GU(i,k) · GU(j,l) · dGD(l, i, k) = ∑_l GU(j, l) · (∑_i ∑_k GU(i, k) · dGD(l, i, k)).
      -- Step 1: swap (k, l): (∑_i ∑_k ∑_l) → (∑_i ∑_l ∑_k).
      rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD l i k) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD l i k) from by
        refine Finset.sum_congr rfl (fun _ _ => ?_)
        rw [Finset.sum_comm]]
      -- Step 2: swap (i, l): (∑_i ∑_l) → (∑_l ∑_i).
      rw [Finset.sum_comm]
      -- Now factor GU(j, l) out of the inner sums.
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
    -- Goal: (1/2) · ∑_l GU(j,l) · (∑_ik GU(i,k) · dGD(l,i,k)) = ∑_l GU(j,l) · (dD(l) / D).
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (1 / 2 : ℝ) *
            (GU j l * (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k)) =
        GU j l * ((1 / 2 : ℝ) *
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k)) from by ring]
    rw [hfor_each_l l]
  -- Step 3: Conclude. From hT_eq and hSecondTriple:
  --   LHS_simplified = T - (1/2)·SecondTriple = -∑_a dGU(a, j, a) - ∑_l GU(j,l) · (dD l / D).
  -- We want: this = -(1/D) · ∑_l ∂_l(D · G^{j l})(y₀)
  --                = -∑_l ∂_l(D·G^{jl})(y₀) / D
  --                = -∑_l ((dD l) · GU(j,l) + D · dGU(l, j, l)) / D
  --                = -∑_l (GU(j,l) · dD(l) / D + dGU(l, j, l)).
  -- Comparing: -∑_a dGU(a, j, a) - ∑_l GU(j, l) · (dD l / D)
  --          = -∑_l dGU(l, j, l) - ∑_l GU(j, l) · (dD l / D)
  --          = -∑_l (dGU(l, j, l) + GU(j, l) · (dD l / D)). ✓
  rw [hLHS_simplified]
  rw [hT_eq, hSecondTriple]
  -- Now goal:
  -- -∑_a dGU(a, j, a) - ∑_l GU(j, l) · (dD(l) / D) = -(1/D) · ∑_l ∂_l(D · G^{j l})(y₀).
  -- Expand the RHS using Leibniz.
  have hRHS_expand : -(1 / D) *
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) l
          (fun y' : E =>
            chartDensityOnE (I := I) g α y' *
              chartInvGramOnE (I := I) g α j l y') y₀ =
      -∑ l : Fin (Module.finrank ℝ E),
        (GU j l * (dD l / D) + dGU l j l) := by
    rw [show -(1 / D) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α j l y') y₀ =
        -((1 / D) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α j l y') y₀) from by ring]
    congr 1
    -- (1/D) · ∑_l ∂_l(D · G^{j l}) = ∑_l (1/D) · (∂_l D · G^{j l} + D · ∂_l G^{j l})
    --                              = ∑_l ((dD l) · GU(j, l) / D + dGU(l, j, l))
    --                              = ∑_l (GU(j, l) · dD(l) / D + dGU(l, j, l)).
    rw [show (1 / D) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α j l y') y₀ =
        ∑ l : Fin (Module.finrank ℝ E),
          (1 / D) * partialDeriv (E := E) l
            (fun y' : E =>
              chartDensityOnE (I := I) g α y' *
                chartInvGramOnE (I := I) g α j l y') y₀ from by
      rw [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    -- Apply Leibniz to ∂_l (D · G^{jl}): ∂_l D · G^{jl} + D · ∂_l G^{jl}.
    have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
      chartDensityOnE_differentiableAt_interior (I := I) g α hy
    have hG_diff : DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y₀ :=
      chartInvGramOnE_differentiableAt_interior (I := I) g α j l hy
    have hLeibniz : partialDeriv (E := E) l
        (fun y' : E => chartDensityOnE (I := I) g α y' *
          chartInvGramOnE (I := I) g α j l y') y₀ =
        partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α j l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j l) y₀ := by
      unfold partialDeriv
      rw [fderiv_fun_mul (𝕜 := ℝ) hdens_diff hG_diff]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hLeibniz]
    -- Now: (1/D) · (dD l · GU(j,l) + D · dGU(l, j, l))
    --    = (dD l · GU(j, l)) / D + dGU(l, j, l)  (using D ≠ 0)
    --    = GU(j, l) · (dD l / D) + dGU(l, j, l).
    -- Note: in the goal, dD l = partialDeriv l (chartDensityOnE g α) y₀,
    --       GU(j,l) = chartInvGramOnE g α j l y₀, dGU(l, j, l) = partialDeriv l (chartInvGramOnE g α j l) y₀.
    change (1 / chartDensityOnE (I := I) g α y₀) *
        (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α j l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j l) y₀) =
      GU j l * (dD l / D) + dGU l j l
    rw [hdD_def, hGU_def, hdGU_def, hD_def]
    have hDne : chartDensityOnE (I := I) g α y₀ ≠ 0 := hD_ne
    field_simp
  rw [hRHS_expand]
  -- Goal:
  -- (∑_i ∑_k ∑_l GU(i,k) GU(j,l) dGD(i, l, k)) - (1/2) ∑_i ∑_k ∑_l GU(i,k) GU(j,l) dGD(l, i, k)
  -- =? -∑_a dGU(a, j, a) - ∑_l GU(j,l) · (dD(l) / D)
  --
  -- Wait. We rewrote LHS by hT_eq and hSecondTriple. The current goal is:
  -- -∑_a dGU(a, j, a) - ∑_l GU(j, l) * (dD l / D) = -∑_l (GU(j, l) * (dD l / D) + dGU(l, j, l)).
  rw [show -∑ l : Fin (Module.finrank ℝ E),
            (GU j l * (dD l / D) + dGU l j l) =
        -(∑ l : Fin (Module.finrank ℝ E),
          GU j l * (dD l / D)) -
        (∑ l : Fin (Module.finrank ℝ E), dGU l j l) from by
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            (GU j l * (dD l / D) + dGU l j l) =
          (∑ l : Fin (Module.finrank ℝ E), GU j l * (dD l / D)) +
            ∑ l : Fin (Module.finrank ℝ E), dGU l j l from
        Finset.sum_add_distrib]
    ring]
  -- Goal: -∑_a dGU(a, j, a) - ∑_l GU(j,l) · (dD l / D) =
  --        -∑_l GU(j,l) · (dD l / D) - ∑_l dGU(l, j, l).
  -- This is just dummy renaming a ↔ l.
  ring

/-- **Discharge of the contracted Christoffel identity (boundaryless variant).**
Under `[I.Boundaryless]`, the chart target is open in `E`, so any point in the
chart target is automatically in its interior, and the discharge theorem applies
to any chart-target point. -/
theorem chartContractedChristoffel_holds_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target)
    (j : Fin (Module.finrank ℝ E)) :
    ChartContractedChristoffelOn (I := I) g α y j := by
  have hy_int : y ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hy
  exact chartContractedChristoffel_holds (I := I) g α y j hy_int

/-! ### Closed-form variants of the headline theorems

We can now drop the `hcc` hypothesis from the headline trace identities by
discharging it via `chartContractedChristoffel_holds_of_boundaryless`. -/

/-- On a closed (boundaryless, compact, T2, σ-compact) manifold, for smooth `f`
the chart trace `chartHessTrace g f x` of the chart Hessian against the inverse
Gram matrix equals the Laplace–Beltrami operator `Δ_g f x`. This is the closed
form of `chartHessTrace_eq_laplacian`: the contracted-Christoffel hypothesis is
discharged automatically via `chartContractedChristoffel_holds_of_boundaryless`. -/
theorem chartHessTrace_eq_laplacian_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  -- Discharge `hcc` for every j using the boundaryless discharge.
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact chartHessTrace_eq_laplacian (I := I) g hf x hcc

/-- On a closed (boundaryless, compact, T2, σ-compact) manifold, for smooth `f`
the explicit chart-coordinate trace
`∑_{ij} (G⁻¹)_{ij}(x) · (Hess f)_{ij}(x)`, written out in terms of
`chartInvGramMatrix` and `chartHessianTensor`, equals the Laplace–Beltrami
operator `Δ_g f x`. This is the closed form of `trace_hessFun_eq_laplacian`:
the contracted-Christoffel hypothesis is discharged automatically via
`chartContractedChristoffel_holds_of_boundaryless`. -/
theorem chartInvGram_trace_hessianTensor_eq_laplacian_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i j *
          chartHessianTensor (I := I) g x f i j x =
      Δ_g (I := I) g hf x := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact trace_hessFun_eq_laplacian (I := I) g hf x hcc

/-- Dimension–Laplacian inequality `(Δ_g f x)² ≤ n · ∑_{ij} (Hess f)_{ij}(x)²`
for smooth `f` on a closed (boundaryless, compact, T2, σ-compact) manifold,
*assuming the chart is g-orthonormal at* `x` (the inverse Gram matrix at `x` is
the identity). This is the pure Frobenius–trace Cauchy–Schwarz bound applied to
the Hessian; it is not the Bochner formula and carries no Ricci term. The
orthonormality hypothesis `h_orth` is what makes the naive (non-metric) chart
Frobenius sum on the right the correct quantity. This is the closed form of
`laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted`: the
contracted-Christoffel hypothesis is discharged automatically via
`chartContractedChristoffel_holds_of_boundaryless`. -/
theorem laplacian_sq_le_dim_mul_frobenius_sq_of_orthonormal
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted
    (I := I) g hf x hcc h_orth

/-! ## Compactness-free pointwise variant of the chart trace identity

The proof of `chartHessTrace_eq_laplacian` uses `[CompactSpace M]` only
indirectly, via `voss_weyl_laplacian_formula_of_closed`. Substituting the pointwise
chart Voss-Weyl identity `voss_weyl_laplacian_formula_pointwise` gives the
same conclusion without compactness. The remaining algebraic manipulation
(Leibniz expansion of the chart Voss-Weyl Laplacian, contracted-Christoffel
substitution, symmetrisation of the inverse Gram matrix) is purely chart-
local and unconditionally valid under `[I.Boundaryless] [SigmaCompactSpace M]
[T2Space M]`.

The pointwise variant is the standard input for downstream callers (notably,
the heart-of-Bochner closure on the smooth orthonormal local frame) that
work pointwise and cannot afford a compactness hypothesis. -/

/-- **Compactness-free pointwise variant** of `chartHessTrace_eq_laplacian`.
The chart-coordinate trace `∑_{ij} G^{ij} (Hess f)_{ij}(x)` equals `Δ_g f x`
under the contracted Christoffel hypothesis, *without* requiring
`[CompactSpace M]`. The proof is identical to `chartHessTrace_eq_laplacian`
except it uses `voss_weyl_laplacian_formula_pointwise` for the Voss-Weyl
expansion of `Δ_g f x`. -/
theorem chartHessTrace_eq_laplacian_pointwise
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  -- Set notation.
  set y₀ : E := extChartAt I x x with hy₀_def
  set α : M := x with hα_def
  -- Step 1: Voss–Weyl expansion of `Δ_g f` (compactness-free pointwise variant).
  have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H x
  have hVW : Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x :=
    voss_weyl_laplacian_formula_pointwise (I := I) g α hf hxsrc
  rw [hVW]
  -- Step 2: Hessian expansion of `chartHessTrace`.
  rw [chartHessTrace_expand (I := I) g f x]
  -- Step 3: Identify `chartInvGramMatrix g x x i j = chartInvGramOnE g x i j y₀`.
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hsymm_y₀ : (extChartAt I α).symm y₀ = x :=
    (extChartAt I α).left_inv hxsrc_ext
  have hG_eq : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j =
        chartInvGramOnE (I := I) g α i j y₀ := by
    intros i j
    rw [chartInvGramOnE_def]
    rw [hsymm_y₀]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x i j *
                chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartIteratedPartialDeriv (I := I) α f i j y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_eq i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x i j *
                  chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                    partialDeriv (E := E) k
                      (scalarOnE (I := I) x f) (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartChristoffel (I := I) g α i j k y₀ *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) α f) y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hG_eq i j]]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxsrc
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hy₀_int : y₀ ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hy₀_target
  have hy₀_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ :=
    isOpen_interior.mem_nhds hy₀_int
  have hgrad_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (gradChartCoeffOnE (I := I) g α f i) y₀ := by
    intro i
    have h := gradChartCoeffOnE_contDiffOn_interior (I := I) g α hf i
    exact (h.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ := by
    have hcd_target : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (extChartAt I α).target := chartDensityOnE_contDiffOn (I := I) g α
    have hcd_int : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (interior (extChartAt I α).target) := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hD_pos : 0 < chartDensity (I := I) g α x :=
    chartDensity_pos (I := I) g α hxbase
  have hD_eq : chartDensityOnE (I := I) g α y₀ = chartDensity (I := I) g α x := by
    unfold chartDensityOnE
    rw [hsymm_y₀]
  rw [chartVossWeylLaplacian_expand_hypBearing (I := I) g α f x
      hgrad_diff hdens_diff]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
              (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
                partialDeriv (E := E) i
                  (chartDensityOnE (I := I) g α) (extChartAt I α x) +
                chartDensityOnE (I := I) g α (extChartAt I α x) *
                  partialDeriv (E := E) i
                    (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x))) =
        (∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
            chartDensityOnE (I := I) g α y₀ *
              ∑ j : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialDeriv_gradChartCoeffOnE_expand (I := I) g α hf i hy₀_int]]
  -- Step 7: Massage T2 (the contracted-Christoffel sum) using the `hcc` hypothesis.
  have hT2_swap : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀ *
                partialDeriv (E := E) k
                  (scalarOnE (I := I) α f) y₀) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀ *
                      partialDeriv (E := E) k
                        (scalarOnE (I := I) α f) y₀) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                    (chartInvGramOnE (I := I) g α i j y₀ *
                      chartChristoffel (I := I) g α i j k y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hT2_swap]
  -- Apply `hcc k` to each inner double sum.
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcc k]]
  have hDens_diffAt : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    hdens_diff
  have hG_diffAt : ∀ k l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    have hcd_target := chartInvGramOnE_contDiffOn (I := I) g α k l
    have hcd_int := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hLeibniz : ∀ k l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) l
          (fun y' : E => chartDensityOnE (I := I) g α y' *
            chartInvGramOnE (I := I) g α k l y') y₀ =
        partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α k l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    unfold partialDeriv
    rw [fderiv_fun_mul (𝕜 := ℝ) hDens_diffAt (hG_diffAt k l)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀))) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 2
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hLeibniz k l]]
  -- Step 9: Expand `gradChartCoeffOnE g α f i y₀`.
  have hgrad_eval : ∀ i : Fin (Module.finrank ℝ E),
      gradChartCoeffOnE (I := I) g α f i y₀ =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y₀ *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ := fun i => rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            (gradChartCoeffOnE (I := I) g α f i y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) =
        (∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hgrad_eval i]]
  -- Step 10: Symmetrise via the Hermitian inverse Gram matrix.
  have hG_sym : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i j y₀ =
        chartInvGramOnE (I := I) g α j i y₀ := by
    intro i j
    unfold chartInvGramOnE chartInvGramMatrix
    set z : M := (extChartAt I α).symm y₀
    have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α z
    have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
      hG_hermit.inv
    have hentry := hGinv_hermit.apply i j
    have hpoint : (chartGramMatrix (I := I) g α z)⁻¹ i j =
        (chartGramMatrix (I := I) g α z)⁻¹ j i := by
      have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
      rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
      exact hstar.symm
    exact hpoint
  have hDOnE_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := by
    rw [hD_eq]; exact ne_of_gt hD_pos
  have hDx_ne : chartDensity (I := I) g α x ≠ 0 := ne_of_gt hD_pos
  -- Begin: re-express RHS so the `(1/D)` is distributed.
  rw [show
      (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) =
        (1 / chartDensity (I := I) g α x) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) from by
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]]
  rw [show (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((1 / chartDensity (I := I) g α x) *
            (chartInvGramOnE (I := I) g α i j y₀ *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀) +
            (1 / chartDensity (I := I) g α x) *
              (chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k
                (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀) *
                ∑ l : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                      chartInvGramOnE (I := I) g α k l y₀ +
                    chartDensityOnE (I := I) g α y₀ *
                      partialDeriv (E := E) l
                        (chartInvGramOnE (I := I) g α k l) y₀))) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α k l y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) l
                  (chartInvGramOnE (I := I) g α k l) y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α j i y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α j i) y₀)) from by
    rw [Finset.sum_comm]]
  have h_partial_swap : ∀ i j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j i) y₀ =
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ := by
    intros i j
    have hfun_eq : chartInvGramOnE (I := I) g α j i =
        chartInvGramOnE (I := I) g α i j := by
      funext y'
      unfold chartInvGramOnE
      set z' : M := (extChartAt I α).symm y'
      have hz_hermit : (chartGramMatrix (I := I) g α z').IsHermitian :=
        chartGramMatrix_isHermitian (I := I) g α z'
      have hzinv_hermit : (chartGramMatrix (I := I) g α z')⁻¹.IsHermitian :=
        hz_hermit.inv
      have hentry := hzinv_hermit.apply i j
      have hstar_eq : (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j := by
        have hstar : star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ i j := hentry
        rw [show star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ j i from rfl] at hstar
        exact hstar
      change (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j
      exact hstar_eq
    rw [hfun_eq]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α j i y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α j i) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α i j y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α i j) y₀)) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_sym j i]
    rw [h_partial_swap i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartIteratedPartialDeriv (I := I) α f i j y₀) -
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀ -
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀))) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hD_eq]
  field_simp
  ring

/-- **Closed-form pointwise variant** of `chartHessTrace_eq_laplacian_of_boundaryless`,
under `[I.Boundaryless]` only (no `[CompactSpace M]`). The contracted Christoffel
hypothesis is discharged automatically via
`chartContractedChristoffel_holds_of_boundaryless`. -/
theorem chartHessTrace_eq_laplacian_pointwise_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact chartHessTrace_eq_laplacian_pointwise (I := I) g hf x hcc

end DivergenceTheorem
end Integral
end DifferentialGeometry
