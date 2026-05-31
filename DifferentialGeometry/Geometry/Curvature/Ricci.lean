import DifferentialGeometry.Geometry.Curvature.Riemann
import DifferentialGeometry.Geometry.HessianTrace

/-!
# Symmetry of the chart Ricci tensor for the Levi-Civita connection

For a smooth Riemannian metric `g` on a smooth manifold `M`, the Ricci tensor in
chart coordinates is the trace `Rc_{ik}(α, y) = ∑_j R^j{}_{ijk}(α, y)` of the
Riemann curvature tensor. The standard symmetry `Rc_{ik} = Rc_{ki}` is a
consequence of the Levi-Civita connection's torsion-free and metric-compatible
properties; at the chart-coordinate level these enter through the symmetry of
the Christoffel symbols in the lower indices, the matrix-inverse derivative
identity `∂(G⁻¹) = -G⁻¹·∂G·G⁻¹`, and Schwarz's theorem on the smooth Gram
matrix.

This file derives `Rc_{ik} = Rc_{ki}` directly from these ingredients, then
discharges `ricciFun_symm_of_chartRicciTensor_symm` to obtain unconditional
pointwise symmetry of the Ricci bilinear form `ricciFun`.

## Strategy

Expanding `R^l{}_{ijk}` and contracting `l = j` gives, after distributing the
summation across the four parts of the chart-Riemann formula:
$$\operatorname{Rc}_{ik}(α, y) = \sum_j \partial_j \Gamma^j{}_{ik}(α, y)
  - \sum_j \partial_k \Gamma^j{}_{ij}(α, y)
  + \sum_{j,m} \Gamma^j{}_{jm}(α, y)\,\Gamma^m{}_{ik}(α, y)
  - \sum_{j,m} \Gamma^j{}_{km}(α, y)\,\Gamma^m{}_{ij}(α, y).$$

The first and third terms are visibly symmetric in `(i, k)` because
`Γ^l{}_{ab}` is symmetric in `(a, b)`. The fourth term is symmetric in
`(i, k)` by relabeling the summation indices and applying lower-index symmetry
of `Γ`. The only nontrivial step is the second term: we must show
$$\sum_j \partial_k \Gamma^j{}_{ij}(α, y) = \sum_j \partial_i \Gamma^j{}_{kj}(α, y).$$

Using a sum-derivative interchange, this reduces to
$$\partial_k\Bigl(\sum_j \Gamma^j{}_{ij}\Bigr)(y) =
    \partial_i\Bigl(\sum_j \Gamma^j{}_{kj}\Bigr)(y).$$

Substituting the chart-Christoffel formula and simplifying via dummy-index swaps
gives `∑_j Γ^j{}_{ij}(α, y) = (1/2)∑_{j, l} G^{jl}(α, y) (∂_i G_{lj})(α, y)`.
Differentiating in `y_k` and using
* the matrix-inverse derivative identity
  `∂_k G^{jl} = -∑_{a, b} G^{ja} G^{bl} ∂_k G_{ab}` (provided here as
  `partialDeriv_chartInvGramOnE_eq` from `HessianTrace.lean`),
* Schwarz's theorem on the smooth Gram matrix
  (`partialDeriv_partialDeriv_chartGramOnE_swap` proved here),
* trace cyclicity for finite matrices (`Matrix.trace_mul_comm` from Mathlib),

leaves a single matrix-trace expression `tr(G⁻¹ · ∂_k G · G⁻¹ · ∂_i G)` which is
manifestly symmetric in `(i, k)` by trace cyclicity.

## Main results

* `partialDeriv_partialDeriv_chartGramOnE_swap`: Schwarz on `chartGramOnE`.
* `chartContractedChristoffel_eq_half_invGram_partialDeriv`:
  `∑_j Γ^j{}_{ij}(α, y) = (1/2) ∑_{j,l} G^{jl}(y) (∂_i G_{lj})(y)`.
* `partialDeriv_contractedChristoffel_swap`: the central identity
  `∂_k(∑_j Γ^j{}_{ij})(y) = ∂_i(∑_j Γ^j{}_{kj})(y)`.
* `chartRicciTensor_symm`: `Rc_{ik}(α, y) = Rc_{ki}(α, y)` on the interior.
* `chartRicciTensor_symm_of_boundaryless`: the same on the chart source under
  `[I.Boundaryless]`.
* `ricciFun_isPointwiseSymm_of_boundaryless`: pointwise symmetry of `ricciFun g` under `[I.Boundaryless]`.
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

/-! ## Symmetry of the chart inverse Gram matrix entries -/

lemma chartInvGramOnE_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y = chartInvGramOnE (I := I) g α j i y := by
  unfold chartInvGramOnE
  set z := (extChartAt I α).symm y
  have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α z
  have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian := hG_hermit.inv
  have hentry := hGinv_hermit.apply i j
  unfold chartInvGramMatrix
  have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
  rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
  exact hstar.symm

/-! ## Schwarz's theorem on the chart Gram matrix -/

/-- **Schwarz's theorem on `chartGramOnE`.** -/
lemma partialDeriv_partialDeriv_chartGramOnE_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (l j a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) a
        (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j)) y =
      partialDeriv (E := E) b
        (partialDeriv (E := E) a (chartGramOnE (I := I) g α l j)) y := by
  classical
  unfold partialDeriv
  have hsmooth_target :
      ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j) (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α l j
  have hsmooth_int :
      ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
        (interior (extChartAt I α).target) :=
    hsmooth_target.mono interior_subset
  have hopen_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hcontDiffAt :
      ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α l j) y :=
    hsmooth_int.contDiffAt (hopen_int.mem_nhds hy)
  have hsymm_2 :
      IsSymmSndFDerivAt ℝ (chartGramOnE (I := I) g α l j) y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff :
      DifferentiableAt ℝ (fderiv ℝ (chartGramOnE (I := I) g α l j)) y := by
    have hfderiv_smooth : ContDiffOn ℝ ∞
        (fderiv ℝ (chartGramOnE (I := I) g α l j))
        (interior (extChartAt I α).target) :=
      hsmooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    have hcontDiff_at_fderiv :
        ContDiffAt ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α l j)) y :=
      hfderiv_smooth.contDiffAt (hopen_int.mem_nhds hy)
    exact hcontDiff_at_fderiv.differentiableAt (by simp)
  have hkey : ∀ p q : Fin (Module.finrank ℝ E),
      fderiv ℝ
          (fun z =>
            fderiv ℝ (chartGramOnE (I := I) g α l j) z ((chartModelBasis E) q))
          y ((chartModelBasis E) p) =
        (fderiv ℝ (fderiv ℝ (chartGramOnE (I := I) g α l j)) y
          ((chartModelBasis E) p)) ((chartModelBasis E) q) := by
    intro p q
    set L : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) q)
    have hcomp_eq : (fun z : E =>
          fderiv ℝ (chartGramOnE (I := I) g α l j) z ((chartModelBasis E) q)) =
        L ∘ (fderiv ℝ (chartGramOnE (I := I) g α l j)) := by
      funext z; rfl
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hg_diff]
    rw [L.fderiv]
    rfl
  rw [hkey a b, hkey b a]
  exact hsymm_2 _ _

/-! ## Algebraic simplification of `∑_j Γ^j{}_{ij}` -/

private lemma sum_invGram_partialDeriv_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y) =
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartInvGramOnE_symm (I := I) g α l j y]
  congr 1
  exact congrArg (fun f => partialDeriv (E := E) l f y)
    (funext (fun y' => chartGramOnE_symm (I := I) g α j i y'))

/-- **Identity for the contracted Christoffel.** -/
lemma chartContractedChristoffel_eq_half_invGram_partialDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j j y) =
      (1 / 2 : ℝ) *
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y := by
  classical
  -- Each Γ^j_{ij} expands by definition.
  have hexp : (∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j j y) =
      (∑ j : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y *
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
               partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
               partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) := rfl
  rw [hexp]
  rw [← Finset.mul_sum]
  congr 1
  -- Distribute: G^{jl} (A + B - C) = G^{jl}·A + G^{jl}·B - G^{jl}·C, sum over j, l.
  -- Step 1: Rewrite each summand as a difference of three terms.
  have hexpand : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
         partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
         partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) =
      chartInvGramOnE (I := I) g α j l y *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y := fun j l => by ring
  -- Step 2: The double sum splits into three.
  have hdouble :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y) -
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
    -- For each (j, l), apply hexpand. Then split sum.
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y) -
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
      intro j
      rw [show (∑ l : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j l y *
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
                   partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
                   partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) =
              (∑ l : Fin (Module.finrank ℝ E),
                (chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) from
        Finset.sum_congr rfl (fun l _ => hexpand j l)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hdouble]
  -- Now use the swap lemma to cancel the second and third terms.
  rw [sum_invGram_partialDeriv_swap (I := I) g α i y]
  ring

/-! ## Differentiability infrastructure on the interior -/

private lemma partialDeriv_chartGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (l j b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j))
      (interior (extChartAt I α).target) := by
  classical
  have hf_target : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α l j
  have hf_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
      (interior (extChartAt I α).target) := hf_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α l j))
      (interior (extChartAt I α).target) :=
    hf_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

private lemma chartInvGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y := by
  have hcd : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α j l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α j l
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α j l)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α j l) y :=
    hcd_int.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

private lemma partialDeriv_chartGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (l j b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j)) y := by
  have hcd : ContDiffOn ℝ ∞
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j))
      (interior (extChartAt I α).target) :=
    partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α l j b
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j)) y :=
    hcd.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

private lemma chartChristoffel_diag_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E => chartChristoffel (I := I) g α i j j y)
      (interior (extChartAt I α).target) := by
  classical
  -- The function is `(1/2) * ∑_l G^{jl}(y) (∂_i G_{lj}(y) + ∂_j G_{li}(y) - ∂_l G_{ij}(y))`.
  have heq : (fun y : E => chartChristoffel (I := I) g α i j j y) =
      (fun y : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) := rfl
  rw [heq]
  refine ContDiffOn.mul contDiffOn_const ?_
  refine ContDiffOn.sum (fun l _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α j l).mono interior_subset
  · refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α l j i
    · exact partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α l i j
    · exact partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α i j l

private lemma chartChristoffel_diag_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' : E => chartChristoffel (I := I) g α i j j y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' : E => chartChristoffel (I := I) g α i j j y')
      (interior (extChartAt I α).target) :=
    chartChristoffel_diag_contDiffOn_interior (I := I) g α i j
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞
      (fun y' : E => chartChristoffel (I := I) g α i j j y') y :=
    hcd.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

/-! ## Trace identity

The "trace cyclicity" we need is the identity
`∑_{j, l, a, b} G^{ja} G^{bl} (∂_k G_{ab}) (∂_i G_{lj}) =
   ∑_{j, l, a, b} G^{ja} G^{bl} (∂_i G_{ab}) (∂_k G_{lj})`.
We give a *direct* proof: the bijection on the index set
`(j, l, a, b) ↦ (b, a, l, j)` transforms the LHS summand into the RHS summand
(after using commutativity of multiplication on `ℝ`). This bypasses the explicit
matrix-trace formulation. -/

/-- **Index-bijection identity** equivalent to trace cyclicity for our
specific four-fold sum. -/
private lemma traceCyclic_invGram_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j a y *
          chartInvGramOnE (I := I) g α b l y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) =
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j a y *
          chartInvGramOnE (I := I) g α b l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) := by
  classical
  -- The bijection `(j, l, a, b) → (b, a, l, j)` maps the LHS summand to the RHS
  -- summand. Concretely:
  -- LHS@(j, l, a, b) = G^{ja} · G^{bl} · ∂_k G_{ab} · ∂_i G_{lj}
  -- RHS@(b, a, l, j) = G^{ba} · G^{jl} · ∂_i G_{al} · ∂_k G_{jb}
  -- These are NOT immediately equal, so we need to apply the bijection
  -- AND swap factors. Specifically, after the bijection LHS@(j, l, a, b) ↔
  -- "what LHS evaluates at (b, a, l, j)" = G^{bl} · G^{ja} · ∂_k G_{la} · ∂_i G_{ab}.
  -- Compare with RHS@(j, l, a, b) = G^{ja} · G^{bl} · ∂_i G_{ab} · ∂_k G_{lj}.
  -- Hmm — let's reverse the direction.
  -- We perform sum-comm rearrangements directly to build LHS = RHS.
  --
  -- Strategy: Apply `Finset.sum_comm` four times to permute the order of
  -- summation from `j l a b` to `b a l j`, then relabel.
  --
  -- LHS = ∑_j ∑_l ∑_a ∑_b f(j, l, a, b) where
  -- f(j, l, a, b) = G^{ja} · G^{bl} · ∂_k G_{ab} · ∂_i G_{lj}.
  --
  -- Reorder to ∑_b ∑_a ∑_l ∑_j f(j, l, a, b).
  -- Rename (j, l, a, b) ↔ (j', l', a', b') with j' := b, l' := a, a' := l, b' := j:
  -- That is, j ← b', l ← a', a ← l', b ← j' (going back: substitute j = b', l = a', a = l', b = j').
  -- Then ∑_{b}_{a}_{l}_{j} f(j, l, a, b) = ∑_{j'}_{a'}_{l'}_{b'} f(b', a', l', j').
  -- So LHS = ∑_j ∑_l ∑_a ∑_b f(j, l, a, b) = ∑_{j'} ∑_{l'} ∑_{a'} ∑_{b'} f(b', a', l', j')
  -- = ∑_{j} ∑_{l} ∑_{a} ∑_{b} f(b, a, l, j) (after renaming primes).
  --
  -- f(b, a, l, j) = G^{bl} · G^{ja} · ∂_k G_{la} · ∂_i G_{ab}
  -- = G^{ja} · G^{bl} · ∂_i G_{ab} · ∂_k G_{la}    (commutativity)
  -- We want: G^{ja} · G^{bl} · ∂_i G_{ab} · ∂_k G_{lj}   (RHS@(j,l,a,b))
  -- Hmm — `∂_k G_{la}` ≠ `∂_k G_{lj}` because the indices differ.
  --
  -- Let me re-derive: we want a bijection σ : (j, l, a, b) ↦ (j', l', a', b') such
  -- that f(σ⁻¹(j', l', a', b')) = g(j', l', a', b') where g is the RHS summand.
  -- i.e., we need
  -- f(j, l, a, b) = g(σ(j, l, a, b))
  -- f(j, l, a, b) = G^{ja} · G^{bl} · ∂_k G_{ab} · ∂_i G_{lj}
  -- g(j', l', a', b') = G^{j'a'} · G^{b'l'} · ∂_i G_{a'b'} · ∂_k G_{l'j'}
  -- Match:
  -- G^{ja} = G^{j'a'} ⟹ (j, a) = (j', a') OR (j, a) = (a', j')
  -- G^{bl} = G^{b'l'} ⟹ (b, l) = (b', l') OR (b, l) = (l', b')
  -- ∂_k G_{ab} = ∂_k G_{l'j'} ⟹ (a, b) = (l', j')
  -- ∂_i G_{lj} = ∂_i G_{a'b'} ⟹ (l, j) = (a', b')
  -- These give: a = l', b = j', l = a', j = b'.
  -- So σ(j, l, a, b) = (b, a, l, j).
  --
  -- Now check G^{ja} = G^{j'a'} = G^{b a}. So we need G^{ja} = G^{ba}? No, we need
  -- G^{ja} = G^{σ(j)σ(a)} where σ acts on indices via the chosen bijection.
  -- Actually the substitution gives: σ(j, l, a, b) = (j' = b, l' = a, a' = l, b' = j).
  -- So G^{j'a'} = G^{bl} (using j' = b, a' = l). And we needed G^{ja} = G^{j'a'} = G^{bl}.
  -- That's NOT equal to G^{ja} unless j = b and a = l... which is only at specific points.
  --
  -- So a single bijection doesn't work. We need bijection AND symmetries of G.
  -- LHS@(j, l, a, b) ↦ at the bijection-image (b, a, l, j):
  -- the *original LHS summand evaluated at this image* is f(b, a, l, j) = G^{ba} · G^{jl} · ∂_k G_{al} · ∂_i G_{ab}.
  -- We want this to equal g(j, l, a, b) = G^{ja} · G^{bl} · ∂_i G_{ab} · ∂_k G_{lj}.
  -- Hmm, ∂_k G_{al} ≠ ∂_k G_{lj} in general.
  --
  -- I had a math error above. Let me redo carefully.
  --
  -- Actually, by repeated `sum_comm`:
  -- LHS = ∑_j ∑_l ∑_a ∑_b f(j, l, a, b)
  --     = ∑_b ∑_a ∑_l ∑_j f(j, l, a, b)  [4 sum_comms]
  -- Now relabel the bound variables b → j', a → l', l → a', j → b':
  --     = ∑_{j'} ∑_{l'} ∑_{a'} ∑_{b'} f(b', a', l', j')
  -- Then drop primes:
  --     = ∑_j ∑_l ∑_a ∑_b f(b, a, l, j)
  -- where f(b, a, l, j) = G^{bl} · G^{ja} · ∂_k G_{la} · ∂_i G_{ab}.
  -- (Substitute j ← b, l ← a, a ← l, b ← j into f(j, l, a, b) = G^{ja} G^{bl} ∂_k G_{ab} ∂_i G_{lj}.)
  -- f(b, a, l, j) = G^{bl} · G^{ja} · ∂_k G_{la} · ∂_i G_{ab}.
  -- Compare with RHS = ∑_j ∑_l ∑_a ∑_b g(j, l, a, b) where
  -- g(j, l, a, b) = G^{ja} · G^{bl} · ∂_i G_{ab} · ∂_k G_{lj}.
  -- These are NOT equal unless we have specific symmetries.
  --
  -- Use G symmetry on chartInvGramOnE: G^{bl} = G^{lb}. Hmm that doesn't directly help.
  -- And chartGramOnE_symm: G_{la} = G_{al}.
  -- ∂_k G_{la} = ∂_k G_{al}.
  -- Still doesn't directly give ∂_k G_{lj}.
  --
  -- So the direct bijection approach does NOT work. We genuinely need the matrix
  -- trace cyclicity which uses the inverse-Gram structure.
  -- Use the matrix-trace approach.
  --
  -- We define the matrices and use trace cyclicity.
  set H : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun a b => chartInvGramOnE (I := I) g α a b y with hH_def
  set Ak : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun a b =>
      partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y with hAk_def
  set Ai : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun a b =>
      partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y with hAi_def
  -- Both sides equal a matrix trace. We rewrite both sides explicitly.
  have hLHS_eq_trace :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) =
      (H * Ak * H * Ai).trace := by
    -- Compute the matrix trace as an iterated sum.
    -- (H * Ak * H * Ai) j j = ∑_l (H * Ak * H) j l * Ai l j
    -- = ∑_l ∑_b (H * Ak) j b * H b l * Ai l j
    -- = ∑_l ∑_b ∑_a H j a * Ak a b * H b l * Ai l j
    -- Sum over j gives the trace.
    have hexpand_diag : ∀ j : Fin (Module.finrank ℝ E),
        (H * Ak * H * Ai) j j =
          ∑ l : Fin (Module.finrank ℝ E),
          ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y := by
      intro j
      simp only [Matrix.mul_apply, hH_def, hAk_def, hAi_def, Matrix.of_apply,
        Finset.sum_mul]
      -- Now both sides are 4-fold sums. We need to match them.
      -- Reorder summations to match (l, a, b) ordering.
      refine Finset.sum_congr rfl ?_
      intro l _
      -- Inner sum: ∑_b (∑_a chartInvGramOnE(j,a) * partialDeriv k chartGramOnE(a,b)) *
      --              chartInvGramOnE(b,l) * partialDeriv i chartGramOnE(l,j)
      -- We need to swap `∑_b ∑_a` to `∑_a ∑_b`.
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro b _
      ring
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Matrix.diag_apply]
    rw [hexpand_diag j]
  have hRHS_eq_trace :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) =
      (H * Ai * H * Ak).trace := by
    have hexpand_diag : ∀ j : Fin (Module.finrank ℝ E),
        (H * Ai * H * Ak) j j =
          ∑ l : Fin (Module.finrank ℝ E),
          ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y := by
      intro j
      simp only [Matrix.mul_apply, hH_def, hAi_def, hAk_def, Matrix.of_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro b _
      ring
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Matrix.diag_apply]
    rw [hexpand_diag j]
  rw [hLHS_eq_trace, hRHS_eq_trace]
  -- Trace cyclicity: tr(H Ak H Ai) = tr((H Ak)(H Ai)) = tr((H Ai)(H Ak)) = tr(H Ai H Ak).
  have heq1 : (H * Ak * H * Ai).trace = ((H * Ak) * (H * Ai)).trace := by
    rw [Matrix.mul_assoc]
  have heq2 : ((H * Ai) * (H * Ak)).trace = (H * Ai * H * Ak).trace := by
    rw [← Matrix.mul_assoc]
  rw [heq1, Matrix.trace_mul_comm (H * Ak) (H * Ai), heq2]

/-! ## Leibniz expansion of `∂_k(∑_{j,l} G^{jl} ∂_i G_{lj})` -/

private lemma partialDeriv_doubleSum_invGram_partialGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y =
      ∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) := by
  classical
  -- Differentiability data.
  have hdiff_innermost : ∀ j l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    intro j l
    refine DifferentiableAt.mul ?_ ?_
    · exact chartInvGramOnE_diffAt_int (I := I) g α j l hy
    · exact partialDeriv_chartGramOnE_diffAt_int (I := I) g α l j i hy
  have hdiff_inner : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    intro j
    exact DifferentiableAt.fun_sum (fun l _ => hdiff_innermost j l)
  -- partialDeriv k of a sum = sum of partialDeriv k.
  have hsum_outer : partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y =
      ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
          (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    change fderiv ℝ
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
        ((chartModelBasis E) k) =
      ∑ j : Fin (Module.finrank ℝ E),
        fderiv ℝ
          (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
          ((chartModelBasis E) k)
    rw [fderiv_fun_sum (fun j _ => hdiff_inner j)]
    rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [hsum_outer]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hsum_inner : partialDeriv (E := E) k
        (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y =
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
          (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    change fderiv ℝ
        (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
        ((chartModelBasis E) k) =
      ∑ l : Fin (Module.finrank ℝ E),
        fderiv ℝ
          (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
          ((chartModelBasis E) k)
    rw [fderiv_fun_sum (fun l _ => hdiff_innermost j l)]
    rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [hsum_inner]
  refine Finset.sum_congr rfl ?_
  intro l _
  -- Leibniz on the (j, l) summand.
  have hu : DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y :=
    chartInvGramOnE_diffAt_int (I := I) g α j l hy
  have hv : DifferentiableAt ℝ
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y :=
    partialDeriv_chartGramOnE_diffAt_int (I := I) g α l j i hy
  change fderiv ℝ
      (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
      ((chartModelBasis E) k) =
    partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
      chartInvGramOnE (I := I) g α j l y *
        partialDeriv (E := E) k
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y
  rw [fderiv_fun_mul (𝕜 := ℝ) hu hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  -- The fderiv expressions are definitionally `partialDeriv k`.
  -- Use `change` to unify them, then `ring`.
  change chartInvGramOnE (I := I) g α j l y *
      (partialDeriv (E := E) k
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) +
      partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y *
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y) =
    partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
      chartInvGramOnE (I := I) g α j l y *
        partialDeriv (E := E) k
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y
  ring

/-! ## The contracted Christoffel cross-derivative identity -/

/-- **Contracted Christoffel symmetry identity.** -/
theorem partialDeriv_contractedChristoffel_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j j y') y =
      partialDeriv (E := E) i
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k j j y') y := by
  classical
  have hC_i : (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j j y') =
      (fun y' : E =>
        (1 / 2 : ℝ) *
          ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') := by
    funext y'
    exact chartContractedChristoffel_eq_half_invGram_partialDeriv (I := I) g α i y'
  have hC_k : (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k j j y') =
      (fun y' : E =>
        (1 / 2 : ℝ) *
          ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y') := by
    funext y'
    exact chartContractedChristoffel_eq_half_invGram_partialDeriv (I := I) g α k y'
  rw [hC_i, hC_k]
  -- Pull out 1/2.
  have hsmul : ∀ (μ ν : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) μ
        (fun y' : E =>
          (1 / 2 : ℝ) *
            ∑ j : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y' *
                partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y =
        (1 / 2 : ℝ) *
          partialDeriv (E := E) μ
            (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j l y' *
                  partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y := by
    intro μ ν
    have hdiff : DifferentiableAt ℝ
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y := by
      refine DifferentiableAt.fun_sum (fun j _ => ?_)
      refine DifferentiableAt.fun_sum (fun l _ => ?_)
      refine DifferentiableAt.mul ?_ ?_
      · exact chartInvGramOnE_diffAt_int (I := I) g α j l hy
      · exact partialDeriv_chartGramOnE_diffAt_int (I := I) g α l j ν hy
    -- partialDeriv μ (c * f) y = c * partialDeriv μ f y.
    change fderiv ℝ
        (fun y' : E =>
          (1 / 2 : ℝ) *
            ∑ j : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y' *
                partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y
        ((chartModelBasis E) μ) =
      (1 / 2 : ℝ) *
        fderiv ℝ
          (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y' *
                partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y
          ((chartModelBasis E) μ)
    -- Rewrite (1/2) * X as (1/2) • X to use fderiv_const_smul.
    set F : E → ℝ := fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y' with hF_def
    have hfn_eq : (fun y' : E => (1 / 2 : ℝ) * F y') = (1 / 2 : ℝ) • F := by
      funext y'; rw [Pi.smul_apply, smul_eq_mul]
    change fderiv ℝ (fun y' : E => (1 / 2 : ℝ) * F y') y
        ((chartModelBasis E) μ) =
      (1 / 2 : ℝ) * fderiv ℝ F y ((chartModelBasis E) μ)
    rw [hfn_eq]
    rw [fderiv_const_smul hdiff]
    simp [smul_eq_mul]
  rw [hsmul k i, hsmul i k]
  congr 1
  -- Apply Leibniz on each side.
  rw [partialDeriv_doubleSum_invGram_partialGram (I := I) g α i k hy,
      partialDeriv_doubleSum_invGram_partialGram (I := I) g α k i hy]
  -- Now substitute the matrix-inverse derivative formula.
  -- Both sides are `S_inv + S_2nd`.
  -- We split each side and handle the two parts.
  -- LHS = ∑_{j,l} (∂_k G^{jl}) (∂_i G_{lj}) + ∑_{j,l} G^{jl} (∂_k ∂_i G_{lj})
  -- RHS = ∑_{j,l} (∂_i G^{jl}) (∂_k G_{lj}) + ∑_{j,l} G^{jl} (∂_i ∂_k G_{lj})
  -- The "Schwarz part" (G^{jl} ∂_k ∂_i G_{lj}) is symmetric in (i,k) by Schwarz on G.
  -- The "inverse-Gram-derivative cross" part is symmetric by trace cyclicity.
  -- We split each side into the two parts.
  have hsplit_LHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) k
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) := by
    -- First: each inner ∑_l (X + Y) = ∑_l X + ∑_l Y.
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) k
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) := by
      intro j
      exact Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    exact Finset.sum_add_distrib
  have hsplit_RHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) i
                (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y) := by
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) i
                (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y) := by
      intro j
      exact Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    exact Finset.sum_add_distrib
  rw [hsplit_LHS, hsplit_RHS]
  -- The Schwarz parts are equal by Schwarz on chartGramOnE.
  have hSchwarz : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_chartGramOnE_swap (I := I) g α l j k i hy]
  -- The cross parts: substitute the matrix-inverse derivative formula.
  have hsubst_LHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) =
      -(∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) := by
    have hentry : ∀ j l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y =
        -(∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) := by
      intro j l
      rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y k j l hy]
      rw [neg_mul]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => hentry j l))]
    -- Move the negation outside.
    rw [show (∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                -(∑ a : Fin (Module.finrank ℝ E),
                  ∑ b : Fin (Module.finrank ℝ E),
                    chartInvGramOnE (I := I) g α j a y *
                      chartInvGramOnE (I := I) g α b l y *
                        partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                          partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y)) =
            -(∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j a y *
                  chartInvGramOnE (I := I) g α b l y *
                    partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                      partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]]
  have hsubst_RHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) =
      -(∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) := by
    have hentry : ∀ j l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y =
        -(∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) := by
      intro j l
      rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y i j l hy]
      rw [neg_mul]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => hentry j l))]
    rw [show (∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                -(∑ a : Fin (Module.finrank ℝ E),
                  ∑ b : Fin (Module.finrank ℝ E),
                    chartInvGramOnE (I := I) g α j a y *
                      chartInvGramOnE (I := I) g α b l y *
                        partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                          partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y)) =
            -(∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j a y *
                  chartInvGramOnE (I := I) g α b l y *
                    partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                      partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]]
  rw [hsubst_LHS, hsubst_RHS, hSchwarz]
  -- Now apply trace cyclicity.
  rw [traceCyclic_invGram_partial (I := I) g α i k y]

/-! ## Sum-derivative interchange and Ricci symmetry -/

lemma sum_partialDeriv_eq_partialDeriv_sum_christ
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) =
      partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j j y') y := by
  classical
  unfold partialDeriv
  have hdiff_each : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartChristoffel (I := I) g α i j j y') y :=
    fun j => chartChristoffel_diag_diffAt_int (I := I) g α i j hy
  rw [fderiv_fun_sum (fun j _ => hdiff_each j)]
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]

/-- **Chart-coordinate Ricci symmetry on the interior.** -/
theorem chartRicciTensor_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciTensor (I := I) g α i k y =
      chartRicciTensor (I := I) g α k i y := by
  classical
  -- Expand the definitions.
  rw [chartRicciTensor_def, chartRicciTensor_def]
  -- Replace each `chartRiemannTensor` by its explicit formula.
  have hLHS_replace :
      (∑ j : Fin (Module.finrank ℝ E), chartRiemannTensor (I := I) g α i j k j y) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m j y *
                chartChristoffel (I := I) g α i j m y))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rfl
  have hRHS_replace :
      (∑ j : Fin (Module.finrank ℝ E), chartRiemannTensor (I := I) g α k j i j y) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α k i m y -
              chartChristoffel (I := I) g α i m j y *
                chartChristoffel (I := I) g α k j m y))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rfl
  rw [hLHS_replace, hRHS_replace]
  -- Distribute the m-sum into a difference of two products on each summand.
  have hmsplit_L : ∀ j : Fin (Module.finrank ℝ E),
      (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α i k m y -
          chartChristoffel (I := I) g α k m j y *
            chartChristoffel (I := I) g α i j m y)) =
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α j m j y *
          chartChristoffel (I := I) g α i k m y) -
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k m j y *
          chartChristoffel (I := I) g α i j m y) := by
    intro j
    simp only [Finset.sum_sub_distrib]
  have hmsplit_R : ∀ j : Fin (Module.finrank ℝ E),
      (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α k i m y -
          chartChristoffel (I := I) g α i m j y *
            chartChristoffel (I := I) g α k j m y)) =
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α j m j y *
          chartChristoffel (I := I) g α k i m y) -
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i m j y *
          chartChristoffel (I := I) g α k j m y) := by
    intro j
    simp only [Finset.sum_sub_distrib]
  -- Rewrite each j-th summand of LHS using hmsplit_L; similarly for RHS.
  have hLHS_step : (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m j y *
                chartChristoffel (I := I) g α i j m y))) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmsplit_L j]
  have hRHS_step : (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α k i m y -
              chartChristoffel (I := I) g α i m j y *
                chartChristoffel (I := I) g α k j m y))) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmsplit_R j]
  rw [hLHS_step, hRHS_step]
  -- Now distribute the j-sum.
  -- LHS = ∑_j (T1_L - T2_L + (T3_L - T4_L)) and similarly for RHS.
  -- We rewrite each as a sum of four sums.
  have hLHS_redistribute :
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y)))) =
      ((∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y) -
       (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) +
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y)) := by
    -- Each summand is ((A - B) + (C - D)) = (A - B + C) - D = A - B + C - D.
    -- Distribute over the j-sum.
    have hpoint : ∀ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y))) =
        ((partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) +
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y) := fun _ => by ring
    rw [Finset.sum_congr rfl (fun j _ => hpoint j)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
  have hRHS_redistribute :
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y)))) =
      ((∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y) -
       (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) +
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y)) := by
    have hpoint : ∀ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y))) =
        ((partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
            partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) +
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y) := fun _ => by ring
    rw [Finset.sum_congr rfl (fun j _ => hpoint j)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
  rw [hLHS_redistribute, hRHS_redistribute]
  -- Now we have four pieces on each side. Match them.
  -- T1: ∑_j ∂_j Γ^j_{ik} = ∑_j ∂_j Γ^j_{ki}, since Γ^j_{ik} = Γ^j_{ki}.
  have hT1 : (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsym : chartChristoffel (I := I) g α i k j =
        chartChristoffel (I := I) g α k i j :=
      funext (fun y' => chartChristoffel_symm (I := I) g α i k j y')
    rw [hsym]
  -- T2: contracted Christoffel symmetry.
  have hT2 : (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) := by
    rw [sum_partialDeriv_eq_partialDeriv_sum_christ (I := I) g α i k hy,
        sum_partialDeriv_eq_partialDeriv_sum_christ (I := I) g α k i hy]
    exact partialDeriv_contractedChristoffel_swap (I := I) g α i k hy
  -- T3: ∑_{j,m} Γ^j_{jm} Γ^m_{ik} = ∑_{j,m} Γ^j_{jm} Γ^m_{ki}, since Γ^m_{ik} = Γ^m_{ki}.
  have hT3 : (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α i k m y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α k i m y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [chartChristoffel_symm (I := I) g α i k m]
  -- T4: ∑_{j,m} Γ^j_{km} Γ^m_{ij} = ∑_{j,m} Γ^j_{im} Γ^m_{kj} via swap j ↔ m.
  have hT4 : (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k m j y *
            chartChristoffel (I := I) g α i j m y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i m j y *
            chartChristoffel (I := I) g α k j m y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hT1, hT2, hT3, hT4]

/-- **Chart-coordinate Ricci symmetry on the chart source under
`[I.Boundaryless]`.** -/
theorem chartRicciTensor_symm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartRicciTensor (I := I) g α i k (extChartAt I α x) =
      chartRicciTensor (I := I) g α k i (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartRicciTensor_symm (I := I) g α i k hx_int

/-- The pointwise Ricci bilinear form `ricciFun g` of a smooth Riemannian metric
`g` is symmetric on a boundaryless manifold: `ricciFun g x v w = ricciFun g x w v`
for every `x`, `v`, `w`. The boundaryless hypothesis is used so that every point
lies in the interior of its chart target, where `chartRicciTensor_symm` applies;
the chart-level symmetry is then transported through
`ricciFun_symm_of_chartRicciTensor_symm`. -/
theorem ricciFun_isPointwiseSymm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    IsPointwiseSymm (ricciFun (I := I) (M := M) g) := by
  refine ricciFun_symm_of_chartRicciTensor_symm (I := I) (M := M) g ?_
  intro x i k
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  exact chartRicciTensor_symm_of_boundaryless (I := I) g x i k hxsrc

end DivergenceTheorem
end Integral
end DifferentialGeometry
