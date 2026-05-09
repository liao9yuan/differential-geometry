import DifferentialGeometry.Geometry.Hessian

/-!
# Pointwise Ricci curvature of a Riemannian metric

For a smooth Riemannian metric `g` on a smooth manifold `M`, the Riemann
curvature tensor is the `(1, 3)`-tensor expressed in chart coordinates by the
Christoffel-symbol formula
$$R^l{}_{ijk}(\alpha, x) =
    \partial_j \Gamma^l{}_{ik}(\alpha, x)
  - \partial_k \Gamma^l{}_{ij}(\alpha, x)
  + \sum_m \bigl(\Gamma^l{}_{jm}(\alpha, x)\,\Gamma^m{}_{ik}(\alpha, x)
                 - \Gamma^l{}_{km}(\alpha, x)\,\Gamma^m{}_{ij}(\alpha, x)\bigr).$$
Contracting `j = l` produces the Ricci tensor
$$\operatorname{Rc}_{ik}(\alpha, x) = \sum_j R^j{}_{ijk}(\alpha, x).$$

This file packages those chart-coordinate formulas and a `pointwiseBilin`
glueing the chart-Ricci entries to a real-valued bilinear form on each
tangent space, computed using the chart at the point itself.

## Main definitions

* `chartRiemannTensor g α i j k l y`: chart-coordinate component
  `R^l{}_{ijk}(α, y)` of the Riemann curvature tensor, written in terms of
  `chartChristoffel` and `partialDeriv`.
* `chartRicciTensor g α i k y`: chart-coordinate component
  `Rc_{ik}(α, y) = ∑ j, R^j{}_{ijk}(α, y)` of the Ricci tensor.
* `ricciFun g`: the pointwise Ricci tensor on the tangent bundle, packaged
  as a `pointwiseBilin`. At each point `x`, the bilinear form sends
  `(v, w)` to `∑ i k, v^i · w^k · Rc_{ik}(x, ϕ_x x)` where the components
  `v^i, w^k` are read off in the canonical model basis.

## Main results

* `ricciFun_apply`: pointwise expansion of `ricciFun g x v w` in terms of
  the chart Ricci entries and the basis components of `v, w`.
* `ricciFun_basis_apply`: evaluating `ricciFun g x` on canonical basis
  vectors `b i, b k` returns the chart Ricci entry `Rc_{ik}(x, ϕ_x x)`.
* `ricciFun_symm_of_chartRicciTensor_symm`: hypothesis-bearing symmetry of
  the pointwise Ricci form. The standard symmetry of the Ricci tensor as a
  `(0, 2)`-tensor follows from the algebraic identities of the Levi-Civita
  Riemann tensor (the first Bianchi identity together with metric
  compatibility), expressed at the chart-coordinate level by the symmetry
  `Rc_{ik}(x, ϕ_x x) = Rc_{ki}(x, ϕ_x x)`. Once a downstream client supplies
  this chart-level symmetry, the bilinear form is pointwise symmetric.
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

/-! ## Chart-coordinate Riemann curvature tensor

The Riemann curvature tensor in chart coordinates is the standard expression
in terms of Christoffel symbols and their first partial derivatives. The
component `R^l{}_{ijk}(α, y)` carries one upper index `l` and three lower
indices `i, j, k`. The convention used here is the geometer's convention
$$R^l{}_{ijk} =
    \partial_j \Gamma^l{}_{ik} - \partial_k \Gamma^l{}_{ij}
  + \sum_m \bigl(\Gamma^l{}_{jm} \Gamma^m{}_{ik}
                 - \Gamma^l{}_{km} \Gamma^m{}_{ij}\bigr),$$
which makes `R^l{}_{ijk}` antisymmetric in `(j, k)` (interchanging `j` and
`k` flips the sign of every term).
-/

/-- The chart-coordinate Riemann curvature tensor `R^l{}_{ijk}(α, y)`.

This is the pointwise scalar combining the Christoffel symbols of the chart
at `α` and their `partialDeriv`-style first partials in `E`:
$$R^l{}_{ijk}(\alpha, y) =
    \partial_j \Gamma^l{}_{ik}(\alpha, y)
  - \partial_k \Gamma^l{}_{ij}(\alpha, y)
  + \sum_m \bigl(\Gamma^l{}_{jm}(\alpha, y) \Gamma^m{}_{ik}(\alpha, y)
                 - \Gamma^l{}_{km}(\alpha, y) \Gamma^m{}_{ij}(\alpha, y)\bigr).$$

The lower-index ordering follows `(i, j, k)`: `i` is the "vector" index,
`j` is the differentiation direction, `k` is the second lower index of the
Christoffel symbol contracted by the alternating second-partial term. -/
def chartRiemannTensor (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
    partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
    (∑ m : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g α j m l y *
          chartChristoffel (I := I) g α i k m y -
        chartChristoffel (I := I) g α k m l y *
          chartChristoffel (I := I) g α i j m y))

@[simp] lemma chartRiemannTensor_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannTensor (I := I) g α i j k l y =
      partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
        (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) := rfl

/-- **Antisymmetry of the chart Riemann tensor in the differentiation
indices.** Interchanging `j ↔ k` flips the sign of every term in the
chart formula. -/
theorem chartRiemannTensor_antisymm_jk
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannTensor (I := I) g α i j k l y =
      - chartRiemannTensor (I := I) g α i k j l y := by
  classical
  rw [chartRiemannTensor_def, chartRiemannTensor_def]
  -- Both sides are linear combinations of partial derivatives and Christoffel
  -- products. The first two terms are visibly antisymmetric in (j, k); the
  -- summed term flips sign under m-summation by exchanging the two products.
  have hsum :
      (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) =
      -(∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y -
            chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring
  rw [hsum]
  ring

/-! ## Chart-coordinate Ricci tensor

The Ricci tensor is the contraction `Rc_{ik} := ∑ j, R^j{}_{ijk}` of the
Riemann tensor on its first upper index `l` against the second lower index
`j`. With the sign convention chosen above, this gives
$$\operatorname{Rc}_{ik}(\alpha, y) = \sum_j R^j{}_{ijk}(\alpha, y)
  = \sum_j \Bigl(\partial_j \Gamma^j{}_{ik}(\alpha, y)
                  - \partial_k \Gamma^j{}_{ij}(\alpha, y)\Bigr)
    + \sum_{j, m} \Bigl(\Gamma^j{}_{jm}(\alpha, y) \Gamma^m{}_{ik}(\alpha, y)
                       - \Gamma^j{}_{km}(\alpha, y) \Gamma^m{}_{ij}(\alpha, y)\Bigr).$$
-/

/-- The chart-coordinate Ricci tensor `Rc_{ik}(α, y) = ∑ j, R^j{}_{ijk}(α, y)`,
obtained by contracting the upper index of `chartRiemannTensor` against the
second lower index. -/
def chartRicciTensor (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartRiemannTensor (I := I) g α i j k j y

@[simp] lemma chartRicciTensor_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g α i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α i j k j y := rfl

/-! ## Pointwise Ricci tensor as a `pointwiseBilin`

We package the chart Ricci tensor at the chart `α := x` itself as a
real-valued bilinear form on `TangentSpace I x = E`. Components of tangent
vectors are read off in the canonical model basis `Module.finBasis ℝ E`.
This is the same convention used by `hessFun` in the file
`Hessian.lean`; in particular `pointwiseBilin` and `IsPointwiseSymm` are the
project's standard carrier and symmetry predicate. -/

/-- The pointwise Ricci tensor of a smooth Riemannian metric `g`, packaged
as a `pointwiseBilin`. At each point `x`, the bilinear form is computed in
the chart at `x`, summing the chart Ricci tensor entries against the
model-basis representations of the input tangent vectors:
$$\operatorname{Rc}(g)(x)(v, w) =
    \sum_{i, k} v^i\,w^k \cdot \operatorname{Rc}_{ik}(x, \varphi_x(x)).$$
The basis used to read off coordinates is the canonical model basis
`Module.finBasis ℝ E`. -/
def ricciFun (g : SmoothRiemannianMetric I M) :
    pointwiseBilin (M := M) I :=
  fun x => LinearMap.mk₂ ℝ
    (fun v w =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr v) i *
            ((Module.finBasis ℝ E).repr w) k *
            chartRicciTensor (I := I) g x i k (extChartAt I x x))
    (fun v₁ v₂ w => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (v₁ + v₂) =
          (Module.finBasis ℝ E).repr v₁ + (Module.finBasis ℝ E).repr v₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (c • v) =
          c • (Module.finBasis ℝ E).repr v := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring)
    (fun v w₁ w₂ => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (w₁ + w₂) =
          (Module.finBasis ℝ E).repr w₁ + (Module.finBasis ℝ E).repr w₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (Module.finBasis ℝ E).repr (c • w) =
          c • (Module.finBasis ℝ E).repr w := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring)

/-- Pointwise expansion of `ricciFun`: applied to two tangent vectors, it
sums the chart Ricci tensor entries weighted by the model-basis
coordinates. -/
lemma ricciFun_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciFun (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr v) i *
            ((Module.finBasis ℝ E).repr w) k *
            chartRicciTensor (I := I) g x i k (extChartAt I x x) := by
  rfl

/-- The bilinear form `ricciFun g x` evaluated on the canonical basis
vectors `b i, b k` returns the chart Ricci tensor entry
`Rc_{ik}(x, ϕ_x x)`. -/
lemma ricciFun_basis_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciFun (I := I) g x
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) k) =
      chartRicciTensor (I := I) g x i k (extChartAt I x x) := by
  classical
  rw [ricciFun_apply]
  -- Replace the basis-rep entries by Kronecker deltas.
  conv_lhs => rw [show
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ k' : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr ((Module.finBasis ℝ E) i)) i' *
            ((Module.finBasis ℝ E).repr ((Module.finBasis ℝ E) k)) k' *
            chartRicciTensor (I := I) g x i' k' (extChartAt I x x)) =
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ k' : Fin (Module.finrank ℝ E),
          (if i = i' then (1 : ℝ) else 0) *
            (if k = k' then (1 : ℝ) else 0) *
            chartRicciTensor (I := I) g x i' k' (extChartAt I x x)) from
      Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun k' _ => by
        rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]))]
  -- After replacing reprs by Kronecker deltas, the only surviving term is `(i, k)`.
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'_ne
      have hkk' : ¬ k = k' := fun h => hk'_ne h.symm
      simp [hkk']
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro i' _ hi'_ne
    apply Finset.sum_eq_zero
    intro k' _
    have hii' : ¬ i = i' := fun h => hi'_ne h.symm
    simp [hii']
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## Symmetry of the pointwise Ricci tensor

The Ricci tensor is symmetric as a `(0, 2)`-tensor: `Rc(X, Y) = Rc(Y, X)`.
At the chart-coordinate level this is the identity
`Rc_{ik}(x, ϕ_x x) = Rc_{ki}(x, ϕ_x x)`.

The standard derivation uses the algebraic identities of the
Levi-Civita Riemann tensor: combining `chartChristoffel_symm` (torsion-free
property) with the first Bianchi identity and metric compatibility yields
the chart-level Ricci symmetry. We expose the result here as a
*hypothesis-bearing* form: a downstream client supplies the chart-level
symmetry of `chartRicciTensor` and obtains pointwise symmetry of `ricciFun`.

This is parallel to the hypothesis-bearing forms exposed by `Hessian.lean`
(e.g. `laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq`), where a bridging
identity to the geometric trace is supplied externally.
-/

/-- **Hypothesis-bearing pointwise symmetry of `ricciFun`.** Given chart-level
symmetry of `chartRicciTensor` at every point `x` evaluated in the chart at
`x` itself, the pointwise Ricci form is symmetric. -/
theorem ricciFun_symm_of_chartRicciTensor_symm
    (g : SmoothRiemannianMetric I M)
    (h_chart_symm : ∀ x : M, ∀ i k : Fin (Module.finrank ℝ E),
        chartRicciTensor (I := I) g x i k (extChartAt I x x) =
          chartRicciTensor (I := I) g x k i (extChartAt I x x)) :
    IsPointwiseSymm (ricciFun (I := I) (M := M) g) := by
  intro x v w
  classical
  rw [ricciFun_apply, ricciFun_apply]
  -- Swap the order of summation on RHS: ∑ i k, ... = ∑ k i, ...
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [h_chart_symm x k i]
  ring

end DivergenceTheorem
end Integral
end DifferentialGeometry
