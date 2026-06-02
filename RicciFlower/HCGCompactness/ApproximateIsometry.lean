import RicciFlower.HCGCompactness.AllTimesBounds
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceAction
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Approximate Isometries On A Fixed Domain

This file records the supplied-metric version of the MSM135 approximate
isometry hypotheses used by the HCG compactness construction.  The construction
provides the pullback metric as data, so the predicate compares two metrics on
the same domain rather than constructing a pullback metric.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- Supplied-metric `(eps,p)` comparison data on a set `K`.

The `C^0` part is the uniform metric equivalence with constant `1 + eps`.
Higher-order smallness is stated using the fixed-background covariant derivative
norms from `AllTimesBounds`; order `0` is intentionally represented by the
metric-equivalence field.

This is the same-domain supplied-pullback side used by the HCG construction, not
the full MSM135 approximate-isometry definition.  Higher-order F3 estimates use
`IsTwoSidedApproxIsometryOn`, which also records the inverse-side derivative
smallness. -/
structure IsApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  uniform_equiv : MetricUniformEquivalentOn (I := I) K g h (1 + eps)
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        metricCovDerivNorm (I := I) a h g x <= eps

/-- Same-domain version of the two-sided approximate-isometry hypotheses in
MSM135 Chapter 4.

`IsApproxIsometryOn` is the forward, supplied-pullback side.  The extra field
records the inverse-side derivative smallness, equivalently the bounds on
`nabla_h^a g` needed in the higher connection-difference estimate. -/
structure IsTwoSidedApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  forward : IsApproxIsometryOn (I := I) K eps p g h
  reverse_cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        metricCovDerivNorm (I := I) a g h x <= eps

theorem IsTwoSidedApproxIsometryOn.toApprox
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h) :
    IsApproxIsometryOn (I := I) K eps p g h :=
  Happrox.forward

/-- Pointwise norm `|nabla_cov^a h|_norm`, separating the connection metric
from the metric used to measure the resulting tensor. -/
noncomputable def metricCovDerivNormWith
    (a : Nat) (h cov norm : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) norm x (a + 2)
      (metricCovDeriv (I := I) h cov a x))

/-- Compatibility with the older fixed-background notation:
`metricCovDerivNorm a h gRef = |nabla_gRef^a h|_gRef`. -/
theorem metricCovDerivNorm_eq_with
    (a : Nat) (h gRef : SmoothRiemannianMetric I M) (x : M) :
    metricCovDerivNorm (I := I) a h gRef x =
      metricCovDerivNormWith (I := I) a h gRef gRef x := rfl

/-- Under metric equivalence, the norm metric in `|nabla_cov^a h|` may be
changed at the expected tensor-norm cost. -/
theorem metricCovDerivNormWith_le_of_equiv
    {K : Set M} {C : Real}
    {h cov norm norm' : SmoothRiemannianMetric I M}
    (hEq : MetricUniformEquivalentOn (I := I) K norm norm' C)
    {x : M} (hx : x ∈ K) (a : Nat) :
    metricCovDerivNormWith (I := I) a h cov norm' x <=
      Real.sqrt (C ^ (a + 2)) *
        metricCovDerivNormWith (I := I) a h cov norm x := by
  let A := metricCovDeriv (I := I) h cov a x
  have hA_sq :
      Tensor0SBundle.normSq0S (I := I) norm' x (a + 2) A <=
        C ^ (a + 2) *
          Tensor0SBundle.normSq0S (I := I) norm x (a + 2) A :=
    Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I) norm norm' x (a + 2) hEq.1 (hEq.2 x hx) A
  have hC_nonneg : 0 <= C := le_trans (by norm_num : (0 : Real) <= 1) hEq.1
  calc
    metricCovDerivNormWith (I := I) a h cov norm' x
        = Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) norm' x (a + 2) A) := rfl
    _ <= Real.sqrt
          (C ^ (a + 2) *
            Tensor0SBundle.normSq0S (I := I) norm x (a + 2) A) :=
          Real.sqrt_le_sqrt hA_sq
    _ = Real.sqrt (C ^ (a + 2)) *
          metricCovDerivNormWith (I := I) a h cov norm x := by
          rw [Real.sqrt_mul (pow_nonneg hC_nonneg (a + 2))]
          rfl

/-- Book-facing norm conversion for the inverse-side metric derivatives:
`|nabla_h^a g|_g` is controlled by `|nabla_h^a g|_h` under the `C^0` part of a
two-sided approximate isometry. -/
theorem IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
    {K : Set M} {eps : Real} {p a : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) :
    metricCovDerivNormWith (I := I) a g h g x <=
      Real.sqrt ((1 + eps) ^ (a + 2)) *
        metricCovDerivNorm (I := I) a g h x := by
  simpa [metricCovDerivNorm_eq_with]
    using metricCovDerivNormWith_le_of_equiv
      (I := I) (hEq := metricUniformEquivalentOn_symm
        (I := I) Happrox.forward.uniform_equiv) hx a

/-- An approximate isometry compares all covariant tensor squared norms by the
expected powers of the `C^0` equivalence constant. -/
theorem IsApproxIsometryOn.normSq0S_compare
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (s : Nat)
    (T : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    (1 + eps) ^ (-(s : Int)) *
        Tensor0SBundle.normSq0S (I := I) g x s T <=
      Tensor0SBundle.normSq0S (I := I) h x s T /\
    Tensor0SBundle.normSq0S (I := I) h x s T <=
      (1 + eps) ^ (s : Int) *
        Tensor0SBundle.normSq0S (I := I) g x s T := by
  exact Tensor0SBundle.normSq0S_le_of_metric_equiv
    (I := I) g h x s Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx) T

/-- Non-method form of `IsApproxIsometryOn.normSq0S_compare`. -/
theorem normSq0S_compare_of_approxIsometry
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (s : Nat)
    (T : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    (1 + eps) ^ (-(s : Int)) *
        Tensor0SBundle.normSq0S (I := I) g x s T <=
      Tensor0SBundle.normSq0S (I := I) h x s T /\
    Tensor0SBundle.normSq0S (I := I) h x s T <=
      (1 + eps) ^ (s : Int) *
        Tensor0SBundle.normSq0S (I := I) g x s T :=
  Happrox.normSq0S_compare (I := I) hx s T

/-- An approximate isometry compares all mixed-tensor squared norms by the
expected power of the `C^0` equivalence constant. -/
theorem IsApproxIsometryOn.normSqRS_compare
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    ((1 + eps) ^ (r + s))⁻¹ *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T <=
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T /\
    Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T <=
      (1 + eps) ^ (r + s) *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T := by
  exact Tensor0SBundle.normSqRS_le_of_metric_equiv
    (I := I) g h x r s Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx) T

/-- Non-method form of `IsApproxIsometryOn.normSqRS_compare`. -/
theorem normSqRS_compare_of_approxIsometry
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    ((1 + eps) ^ (r + s))⁻¹ *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T <=
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T /\
    Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T <=
      (1 + eps) ^ (r + s) *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T :=
  Happrox.normSqRS_compare (I := I) hx r s T

/-- Square-root upper mixed-tensor norm comparison from the `C^0` part of an
approximate isometry. -/
theorem IsApproxIsometryOn.sqrt_normRS_upper
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T) <=
      Real.sqrt ((1 + eps) ^ (r + s)) *
        Real.sqrt
          (Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T) := by
  exact Tensor0SBundle.sqrt_normRS_upper_le_of_equiv
    (I := I) g h x r s Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx) T

/-- F3 first producer, corresponding to the estimate preceding MSM135 Chapter 4
equation `lbl369`.

At a point with an `h`-orthonormal basis, an `(eps,p)` approximate isometry with
`1 <= p` bounds the norm of the Levi-Civita connection-difference tensor by the
first metric covariant-derivative smallness.  The book later combines this with
elementary numerical estimates when `eps < 1`; this theorem keeps the sharper
constant produced by the checked connection-difference API. -/
theorem connDiff_le_approx
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)) <=
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
  have hdiff :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K) h g hx (1 + eps) Happrox.uniform_equiv basis hinv
  have hsmall :
      metricCovDerivNorm (I := I) 1 h g x <= eps :=
    Happrox.cov_deriv_small 1 le_rfl hp x hx
  have hcoef_nonneg :
      0 <= (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3) := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x))
        <= (3 / 2 : Real) *
            (Real.sqrt ((1 + eps) ^ 3) *
              metricCovDerivNorm (I := I) 1 h g x) := hdiff
    _ = ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) *
          metricCovDerivNorm (I := I) 1 h g x := by ring
    _ <= ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) * eps :=
      mul_le_mul_of_nonneg_left hsmall hcoef_nonneg
    _ = (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by ring

/-- Book-orientation version of `connDiff_le_approx`.

This bounds `Gamma_g - Gamma_h` in the `g` norm using the inverse-side
derivative smallness `|nabla_h g|`. -/
theorem connDiff_book_le_approx
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)) <=
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
  have hdiff :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K) g h hx (1 + eps)
      (metricUniformEquivalentOn_symm (I := I) Happrox.forward.uniform_equiv)
      basis hinv
  have hsmall :
      metricCovDerivNorm (I := I) 1 g h x <= eps :=
    Happrox.reverse_cov_deriv_small 1 le_rfl hp x hx
  have hcoef_nonneg :
      0 <= (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3) := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x))
        <= (3 / 2 : Real) *
            (Real.sqrt ((1 + eps) ^ 3) *
              metricCovDerivNorm (I := I) 1 g h x) := hdiff
    _ = ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) *
          metricCovDerivNorm (I := I) 1 g h x := by ring
    _ <= ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) * eps :=
      mul_le_mul_of_nonneg_left hsmall hcoef_nonneg
    _ = (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by ring

/-- Legacy-orientation base case for the connection-difference estimate in the
`g` norm.

This keeps the same `Gamma_h - Gamma_g` orientation as `connDiff_le_approx`.
The book-orientation version is `connDiff_book_le_eps_g`. -/
theorem connDiff_le_eps_g
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)) <=
      12 * eps := by
  let A : Tensor0SBundle.TensorRSSpace 1 2 I x :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hC_nonneg : 0 <= (1 + eps) := by linarith
  have hpow_nonneg : 0 <= (1 + eps) ^ 3 := pow_nonneg hC_nonneg 3
  have hpow_le : (1 + eps) ^ 3 <= (8 : Real) := by
    have hbase_le : 1 + eps <= (2 : Real) := by linarith
    have hpow : (1 + eps) ^ 3 <= (2 : Real) ^ 3 :=
      pow_le_pow_left₀ hC_nonneg hbase_le 3
    norm_num at hpow
    exact hpow
  have hcompare :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) 1 2 A) <=
        Real.sqrt ((1 + eps) ^ (1 + 2)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2 A) :=
    Tensor0SBundle.sqrt_normRS_lower_le_of_equiv
      (I := I) g h x 1 2 Happrox.uniform_equiv.1
      (Happrox.uniform_equiv.2 x hx) A
  have hconn :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) 1 2 A) <=
        (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
    simpa [A] using
      connDiff_le_approx
        (I := I) Happrox hx hp basis hinv
  have hfirst :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) 1 2 A) <=
        Real.sqrt ((1 + eps) ^ 3) *
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)) := by
    simpa using
      le_trans hcompare
        (mul_le_mul_of_nonneg_left hconn (Real.sqrt_nonneg _))
  have hsqrt_sq :
      Real.sqrt ((1 + eps) ^ 3) * Real.sqrt ((1 + eps) ^ 3) =
        (1 + eps) ^ 3 := by
    rw [← pow_two, Real.sq_sqrt hpow_nonneg]
  have hcoef :
      Real.sqrt ((1 + eps) ^ 3) *
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)) =
        (3 / 2 : Real) * ((1 + eps) ^ 3 * eps) := by
    calc
      Real.sqrt ((1 + eps) ^ 3) *
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
          =
        (3 / 2 : Real) *
          ((Real.sqrt ((1 + eps) ^ 3) *
            Real.sqrt ((1 + eps) ^ 3)) * eps) := by ring
      _ = (3 / 2 : Real) * ((1 + eps) ^ 3 * eps) := by
            rw [hsqrt_sq]
  have hbound :
      (3 / 2 : Real) * ((1 + eps) ^ 3 * eps) <= 12 * eps := by
    have hmul :
        (1 + eps) ^ 3 * eps <= 8 * eps :=
      mul_le_mul_of_nonneg_right hpow_le heps_nonneg
    calc
      (3 / 2 : Real) * ((1 + eps) ^ 3 * eps)
          <= (3 / 2 : Real) * (8 * eps) := by
            exact mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 12 * eps := by ring
  exact hfirst.trans ((le_of_eq hcoef).trans hbound)

/-- Book-orientation `k = 0` connection-difference estimate in the `g` norm. -/
theorem connDiff_book_le_eps_g
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)) <=
      12 * eps := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.forward.uniform_equiv.1
    linarith
  have hC_nonneg : 0 <= (1 + eps) := by linarith
  have hpow_le : (1 + eps) ^ 3 <= (8 : Real) := by
    have hbase_le : 1 + eps <= (2 : Real) := by linarith
    have hpow : (1 + eps) ^ 3 <= (2 : Real) ^ 3 :=
      pow_le_pow_left₀ hC_nonneg hbase_le 3
    norm_num at hpow
    exact hpow
  have hsqrt_le : Real.sqrt ((1 + eps) ^ 3) <= (8 : Real) := by
    have hsqrt : Real.sqrt ((1 + eps) ^ 3) <= Real.sqrt (8 : Real) :=
      Real.sqrt_le_sqrt hpow_le
    have hsqrt8 : Real.sqrt (8 : Real) <= (8 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt8
  have hbase :=
    connDiff_book_le_approx
      (I := I) Happrox hx hp basis hinv
  have hcoef :
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) <=
        12 * eps := by
    have hs :
        (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3) <= 12 := by
      calc
        (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)
            <= (3 / 2 : Real) * 8 := by
              exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
        _ <= 12 := by norm_num
    calc
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)
          = ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) * eps := by ring
      _ <= 12 * eps := mul_le_mul_of_nonneg_right hs heps_nonneg
  exact hbase.trans hcoef

/-- A supplied smooth mixed `(1,2)` tensor field realizes the concrete
Levi-Civita connection-difference tensor.  This is the field-level bridge
needed before taking higher covariant derivatives; it is not an existence
assertion. -/
def ConnDiffFieldRealizes
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M)
    (D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2) : Prop :=
  forall x : M,
    D x =
      Tensor0SBundle.connectionDifferenceTensorAt
        (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x

/-- Pointwise `g`-norm of a supplied `k`-th `h`-covariant derivative of the
connection-difference tensor. -/
noncomputable def connDiffDerivNorm
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2))
    (x : M) : Real :=
  Tensor0SBundle.fieldNormRS (I := I) g 1 (k + 2) Dk x

/-- A supplied mixed tensor field realizes the `k`-th `h`-covariant derivative
of `Gamma_g - Gamma_h`, the orientation used in MSM135 Chapter 4. -/
def ConnDiffDerivRealizes
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2)) : Prop :=
  exists D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2,
    ConnDiffFieldRealizes (I := I) g h D ∧
      Tensor0SBundle.HigherCovDerivRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D k Dk

/-- The first positive-order connection-difference realization is an actual
total `h`-covariant derivative of the connection-difference field. -/
theorem ConnDiffDerivRealizes.one
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1) :
    exists D : Tensor0SBundle.TensorRSField
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1 2,
      ConnDiffFieldRealizes (I := I) g h D ∧
        Tensor0SBundle.TotalNablaRSRealizes
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D D1 := by
  rcases hD1 with ⟨D, hD, hderiv⟩
  exact ⟨D, hD, Tensor0SBundle.HigherCovDerivRSRealizes.one_12 hderiv⟩

/-- Pointwise application form of the first realized connection-difference
derivative. -/
theorem ConnDiffDerivRealizes.one_apply
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) (β : Tensor0SBundle.Tensor0SSpace 1 I x)
    (slots : Fin 2 -> TangentSpace I x) :
    exists D : Tensor0SBundle.TensorRSField
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1 2,
      ConnDiffFieldRealizes (I := I) g h D ∧
        D1 x β (Fin.cons (X x) slots) =
          Tensor0SBundle.nablaRSFun
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            1 2 (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            X D x β slots := by
  rcases hD1 with ⟨D, hD, hderiv⟩
  exact ⟨D, hD,
    Tensor0SBundle.HigherCovDerivRSRealizes.one_apply_12
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      hderiv X x β slots⟩

/-- Uniform bound predicate for realized higher connection-difference
derivatives on a set.  The realization field prevents this from becoming an
arbitrary placeholder predicate. -/
def ConnDiffDerivBoundOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) :
    Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C

/-- The finite metric-derivative sum appearing in the book estimate
`|nabla_h^k (Gamma_g-Gamma_h)| <= C_k sum_{j=1}^{k+1} |nabla_h^j g|`. -/
noncomputable def connDiffMetricSum
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (k : Nat) (x : M) : Real :=
  (Finset.Icc 1 (k + 1)).sum
    (fun j : Nat => metricCovDerivNorm (I := I) j g h x)

/-- A finite product of inverse-side metric-derivative norms.

Repeated orders are allowed; a product such as
`|nabla_h g| * |nabla_h^2 g|` is represented by `[1, 2]`.  This is the
book-faithful shape of the terms produced when differentiating the
Christoffel-difference formula: differentiating the inverse metric creates
products of lower metric derivatives. -/
noncomputable def connDiffMetricProduct
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (orders : List Nat) (x : M) : Real :=
  (orders.map (fun j : Nat => metricCovDerivNorm (I := I) j g h x)).prod

/-- A finite sum of metric-derivative products. -/
noncomputable def connDiffMetricProducts
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (terms : List (List Nat)) (x : M) :
    Real :=
  (terms.map (fun orders : List Nat =>
    connDiffMetricProduct (I := I) g h orders x)).sum

@[simp]
theorem connDiffMetricProduct_nil
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffMetricProduct (I := I) g h [] x = 1 := by
  simp [connDiffMetricProduct]

@[simp]
theorem connDiffMetricProduct_singleton
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (j : Nat) (x : M) :
    connDiffMetricProduct (I := I) g h [j] x =
      metricCovDerivNorm (I := I) j g h x := by
  simp [connDiffMetricProduct]

@[simp]
theorem connDiffMetricProducts_nil
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffMetricProducts (I := I) g h [] x = 0 := by
  simp [connDiffMetricProducts]

@[simp]
theorem connDiffMetricProducts_singleton
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (orders : List Nat) (x : M) :
    connDiffMetricProducts (I := I) g h [orders] x =
      connDiffMetricProduct (I := I) g h orders x := by
  simp [connDiffMetricProducts]

@[simp]
theorem connDiffMetricProducts_singleton_singleton
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (j : Nat) (x : M) :
    connDiffMetricProducts (I := I) g h [[j]] x =
      metricCovDerivNorm (I := I) j g h x := by
  simp

theorem connDiffMetricProducts_append
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (terms terms' : List (List Nat))
    (x : M) :
    connDiffMetricProducts (I := I) g h (terms ++ terms') x =
      connDiffMetricProducts (I := I) g h terms x +
        connDiffMetricProducts (I := I) g h terms' x := by
  simp [connDiffMetricProducts, List.map_append]

/-- Singleton product terms encoding the book's linear sum
`sum_{j=1}^{k+1} |nabla_h^j g|`. -/
def connDiffLinTerms (k : Nat) : List (List Nat) :=
  (Finset.Icc 1 (k + 1)).toList.map fun j : Nat => [j]

/-- Singleton product terms are exactly the linear metric-derivative sum. -/
@[simp]
theorem linTerms_products
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (k : Nat) (x : M) :
    connDiffMetricProducts (I := I) g h (connDiffLinTerms k) x =
      connDiffMetricSum (I := I) g h k x := by
  simp [connDiffLinTerms, connDiffMetricProducts, connDiffMetricProduct,
    connDiffMetricSum]

/-- Every singleton product term is nonempty. -/
theorem linTerms_nonempty {k : Nat} {orders : List Nat}
    (horders : orders ∈ connDiffLinTerms k) :
    orders ≠ [] := by
  rcases List.mem_map.mp horders with ⟨j, _hj, rfl⟩
  simp

/-- Every derivative order in the singleton linear terms is positive. -/
theorem linTerms_pos {k : Nat} {orders : List Nat}
    (horders : orders ∈ connDiffLinTerms k) {j : Nat} (hj : j ∈ orders) :
    1 <= j := by
  rcases List.mem_map.mp horders with ⟨a, ha, rfl⟩
  have haIcc : a ∈ Finset.Icc 1 (k + 1) := Finset.mem_toList.mp ha
  have hbounds := Finset.mem_Icc.mp haIcc
  have hja : j = a := by simpa using hj
  rw [hja]
  exact hbounds.1

/-- Every derivative order in the singleton linear terms is at most `k + 1`. -/
theorem linTerms_le_succ {k : Nat} {orders : List Nat}
    (horders : orders ∈ connDiffLinTerms k) {j : Nat} (hj : j ∈ orders) :
    j <= k + 1 := by
  rcases List.mem_map.mp horders with ⟨a, ha, rfl⟩
  have haIcc : a ∈ Finset.Icc 1 (k + 1) := Finset.mem_toList.mp ha
  have hbounds := Finset.mem_Icc.mp haIcc
  have hja : j = a := by simpa using hj
  rw [hja]
  exact hbounds.2

/-- The total derivative weight of a schematic Christoffel product term.

The list `[2, 1]` represents a product such as
`|nabla_h^2 g| * |nabla_h g|`, and has weight `3`. -/
def connDiffProdWeight (orders : List Nat) : Nat :=
  orders.sum

/-- A schematic Christoffel product term of weight `w`: a nonempty product of
positive metric-derivative factors whose orders sum to `w`. -/
def ConnDiffProdTerm (w : Nat) (orders : List Nat) : Prop :=
  orders ≠ [] ∧
    (forall j : Nat, j ∈ orders -> 1 <= j) ∧
    connDiffProdWeight orders = w

/-- A finite family of schematic Christoffel product terms, all of the same
weight. -/
def ConnDiffProdTerms (w : Nat) (terms : List (List Nat)) : Prop :=
  forall orders : List Nat, orders ∈ terms -> ConnDiffProdTerm w orders

theorem prodTerm_nonempty {w : Nat} {orders : List Nat}
    (h : ConnDiffProdTerm w orders) :
    orders ≠ [] :=
  h.1

theorem prodTerm_pos {w : Nat} {orders : List Nat}
    (h : ConnDiffProdTerm w orders) {j : Nat} (hj : j ∈ orders) :
    1 <= j :=
  h.2.1 j hj

theorem prodTerm_le_weight {w : Nat} {orders : List Nat}
    (h : ConnDiffProdTerm w orders) {j : Nat} (hj : j ∈ orders) :
    j <= w := by
  have hle : j <= orders.sum := by
    exact List.le_sum_of_mem hj
  rw [← h.2.2]
  exact hle

theorem prodTerms_nonempty {w : Nat} {terms : List (List Nat)}
    (h : ConnDiffProdTerms w terms) {orders : List Nat}
    (horders : orders ∈ terms) :
    orders ≠ [] :=
  prodTerm_nonempty (h orders horders)

theorem prodTerms_pos {w : Nat} {terms : List (List Nat)}
    (h : ConnDiffProdTerms w terms) {orders : List Nat}
    (horders : orders ∈ terms) {j : Nat} (hj : j ∈ orders) :
    1 <= j :=
  prodTerm_pos (h orders horders) hj

theorem prodTerms_le_weight {w : Nat} {terms : List (List Nat)}
    (h : ConnDiffProdTerms w terms) {orders : List Nat}
    (horders : orders ∈ terms) {j : Nat} (hj : j ∈ orders) :
    j <= w :=
  prodTerm_le_weight (h orders horders) hj

/-- Product terms for the static Christoffel-difference formula DC1:
`Gamma_g - Gamma_h` is linear in `nabla_h g`. -/
def connDiffBaseTerms : List (List Nat) :=
  [[1]]

/-- Product terms expected after one `nabla_h` derivative of the DC1 formula:
one term from `nabla_h^2 g`, and one quadratic term from differentiating
`g^{-1}`. -/
def connDiffOneTerms : List (List Nat) :=
  [[2], [1, 1]]

/-- Slot permutation sending `(c,a,b)` to `(a,b,c)` in the DC1
Christoffel-difference symmetrization. -/
def lcDiffPermABC : Equiv.Perm (Fin 3) where
  toFun q :=
    if q = 0 then 1 else if q = 1 then 2 else 0
  invFun q :=
    if q = 0 then 2 else if q = 1 then 0 else 1
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

/-- Slot permutation sending `(c,a,b)` to `(b,a,c)` in the DC1
Christoffel-difference symmetrization. -/
def lcDiffPermBAC : Equiv.Perm (Fin 3) where
  toFun q :=
    if q = 0 then 2 else if q = 1 then 1 else 0
  invFun q :=
    if q = 0 then 2 else if q = 1 then 1 else 0
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

@[simp]
theorem lcDiffPermABC_zero : lcDiffPermABC 0 = 1 := by
  simp [lcDiffPermABC]

@[simp]
theorem lcDiffPermABC_one : lcDiffPermABC 1 = 2 := by
  simp [lcDiffPermABC]

@[simp]
theorem lcDiffPermABC_two : lcDiffPermABC 2 = 0 := by
  simp [lcDiffPermABC]

@[simp]
theorem lcDiffPermBAC_zero : lcDiffPermBAC 0 = 2 := by
  simp [lcDiffPermBAC]

@[simp]
theorem lcDiffPermBAC_one : lcDiffPermBAC 1 = 1 := by
  simp [lcDiffPermBAC]

@[simp]
theorem lcDiffPermBAC_two : lcDiffPermBAC 2 = 0 := by
  simp [lcDiffPermBAC]

theorem lcDiffPermABC_slots {Idx : Type*} (c a b : Idx) :
    ((Fin.cons c (fun q : Fin 2 => if q = 0 then a else b) :
        Fin 3 -> Idx) ∘ lcDiffPermABC) =
      (fun q : Fin 3 => if q = 0 then a else if q = 1 then b else c) := by
  funext q
  fin_cases q <;> rfl

theorem lcDiffPermBAC_slots {Idx : Type*} (c a b : Idx) :
    ((Fin.cons c (fun q : Fin 2 => if q = 0 then a else b) :
        Fin 3 -> Idx) ∘ lcDiffPermBAC) =
      (fun q : Fin 3 => if q = 0 then b else if q = 1 then a else c) := by
  funext q
  fin_cases q <;> rfl

/-- The three finite-sum terms in the DC1 Christoffel-difference expansion. -/
noncomputable def connDiffBaseExpansionTerm
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    Fin 3 -> Tensor0SBundle.TensorRSSpace 1 2 I x :=
  let A := metricCovDeriv (I := I) g h 1 x
  fun i : Fin 3 =>
    if i = 0 then
      Tensor0SBundle.smulRS (I := I) (1 / 2 : Real)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x 2
          (Tensor0SBundle.permute0S (I := I) lcDiffPermABC A))
    else if i = 1 then
      Tensor0SBundle.smulRS (I := I) (1 / 2 : Real)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x 2
          (Tensor0SBundle.permute0S (I := I) lcDiffPermBAC A))
    else
      Tensor0SBundle.smulRS (I := I) (-1 / 2 : Real)
        (Tensor0SBundle.raiseFirst0S (I := I) g x 2 A)

@[simp]
theorem connDiffBaseExpansionTerm_zero
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffBaseExpansionTerm (I := I) g h x 0 =
      Tensor0SBundle.smulRS (I := I) (1 / 2 : Real)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x 2
          (Tensor0SBundle.permute0S
            (I := I) lcDiffPermABC (metricCovDeriv (I := I) g h 1 x))) := by
  simp [connDiffBaseExpansionTerm]

@[simp]
theorem connDiffBaseExpansionTerm_one
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffBaseExpansionTerm (I := I) g h x 1 =
      Tensor0SBundle.smulRS (I := I) (1 / 2 : Real)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x 2
          (Tensor0SBundle.permute0S
            (I := I) lcDiffPermBAC (metricCovDeriv (I := I) g h 1 x))) := by
  simp [connDiffBaseExpansionTerm]

@[simp]
theorem connDiffBaseExpansionTerm_two
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffBaseExpansionTerm (I := I) g h x 2 =
      Tensor0SBundle.smulRS (I := I) (-1 / 2 : Real)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x 2 (metricCovDeriv (I := I) g h 1 x)) := by
  simp [connDiffBaseExpansionTerm]

set_option linter.unusedDecidableInType false in
/-- DC3b base finite expansion: in a pointwise `g`-orthonormal local frame,
the realized connection-difference tensor is the finite sum of the three
raised/permuted `nabla_h g` terms from the DC1 Christoffel formula. -/
theorem connDiffBase_expansion
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2}
    (hD : ConnDiffFieldRealizes (I := I) g h D)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinvGlobal :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv frame)
    (hinv_id : forall i j : Idx, gInv x i j = if i = j then 1 else 0) :
    D x =
      Tensor0SBundle.metricSumRS
        (I := I) (g := g) (x := x) 1 2
        (Finset.univ : Finset (Fin 3))
        (connDiffBaseExpansionTerm (I := I) g h x) := by
  let basis := hframe.toBasisAt hx
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    localFrameOneOfInf (I := I) frame hframe
  have hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
    intro i j
    constructor
    · simpa [basis, Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, IsLocalFrameOn.toBasisAt_coe,
        Coordinates.metricCompForMetricInFrame, hinv_id] using
        (hinvGlobal x i j).1
    · simpa [basis, Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, IsLocalFrameOn.toBasisAt_coe,
        Coordinates.metricCompForMetricInFrame, hinv_id] using
        (hinvGlobal x i j).2
  rw [hD x]
  apply Tensor0SBundle.eq_metricSumRS_of_components
    (I := I) 1 2 basis (Finset.univ : Finset (Fin 3))
  intro upper lower
  have hupper : upper = fun _ : Fin 1 => upper 0 := by
    funext q
    fin_cases q
    rfl
  rw [hupper]
  let e := upper 0
  let a := lower 0
  let b := lower 1
  have hlower :
      lower = (fun q : Fin 2 => if q = 0 then a else b) := by
    funext q
    fin_cases q <;> rfl
  rw [hlower]
  have hdc1 :=
    Coordinates.lcDiffComp_eq
      (I := I) (M := M) (u := u) (Idx := Idx)
      (g := g) (h := h) (gInv := gInv) (frame := frame)
      (hframe := hframe1) hu hx hinvGlobal a b e
  have hsum_id :
      (∑ c : Idx,
        gInv x e c *
          (Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x a b c +
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x b a c -
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x c a b)) =
        Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x a b e +
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x b a e -
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x e a b := by
    rw [Finset.sum_eq_single e]
    · simp [hinv_id]
    · intro c _hc hce
      have hec : e ≠ c := hce.symm
      simp [hinv_id, hec]
    · intro he
      exact False.elim (he (Finset.mem_univ e))
  have hdc1' :
      2 *
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
        Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x a b e +
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x b a e -
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x e a b := by
    simpa [basis, hsum_id] using hdc1
  have hAab :
      Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x a b e =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.raiseFirst0S
            (I := I) g x 2
            (Tensor0SBundle.permute0S
              (I := I) lcDiffPermABC
              (metricCovDeriv (I := I) g h 1 x)))
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) := by
    rw [Tensor0SBundle.compRS_raiseFirst_permute0S
      (I := I) g x 2 basis hinvBasis lcDiffPermABC
      (metricCovDeriv (I := I) g h 1 x) e
      (fun q : Fin 2 => if q = 0 then a else b)]
    rw [lcDiffPermABC_slots e a b]
    rw [← metricCov1_coord (I := I) g h frame hframe hu hx a b e]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hAba :
      Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x b a e =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.raiseFirst0S
            (I := I) g x 2
            (Tensor0SBundle.permute0S
              (I := I) lcDiffPermBAC
              (metricCovDeriv (I := I) g h 1 x)))
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) := by
    rw [Tensor0SBundle.compRS_raiseFirst_permute0S
      (I := I) g x 2 basis hinvBasis lcDiffPermBAC
      (metricCovDeriv (I := I) g h 1 x) e
      (fun q : Fin 2 => if q = 0 then a else b)]
    rw [lcDiffPermBAC_slots e a b]
    rw [← metricCov1_coord (I := I) g h frame hframe hu hx b a e]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hAea :
      Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 x e a b =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.raiseFirst0S
            (I := I) g x 2 (metricCovDeriv (I := I) g h 1 x))
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) := by
    rw [Tensor0SBundle.compRS_raiseFirst
      (I := I) g x 2 basis hinvBasis
      (metricCovDeriv (I := I) g h 1 x) e
      (fun q : Fin 2 => if q = 0 then a else b)]
    rw [← metricCov1_coord (I := I) g h frame hframe hu hx e a b]
  let C0 : Real :=
    Tensor0SBundle.componentRS (I := I) basis
      (Tensor0SBundle.raiseFirst0S
        (I := I) g x 2
        (Tensor0SBundle.permute0S
          (I := I) lcDiffPermABC
          (metricCovDeriv (I := I) g h 1 x)))
      (fun _ : Fin 1 => e)
      (fun q : Fin 2 => if q = 0 then a else b)
  let C1 : Real :=
    Tensor0SBundle.componentRS (I := I) basis
      (Tensor0SBundle.raiseFirst0S
        (I := I) g x 2
        (Tensor0SBundle.permute0S
          (I := I) lcDiffPermBAC
          (metricCovDeriv (I := I) g h 1 x)))
      (fun _ : Fin 1 => e)
      (fun q : Fin 2 => if q = 0 then a else b)
  let C2 : Real :=
    Tensor0SBundle.componentRS (I := I) basis
      (Tensor0SBundle.raiseFirst0S
        (I := I) g x 2 (metricCovDeriv (I := I) g h 1 x))
      (fun _ : Fin 1 => e)
      (fun q : Fin 2 => if q = 0 then a else b)
  have htarget :
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
        (1 / 2 : Real) * C0 + (1 / 2 : Real) * C1 +
          (-1 / 2 : Real) * C2 := by
    have h := hdc1'
    rw [hAab, hAba, hAea] at h
    unfold C0 C1 C2
    linarith
  have hT0 :
      Tensor0SBundle.componentRS (I := I) basis
          (connDiffBaseExpansionTerm (I := I) g h x 0)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
        (1 / 2 : Real) * C0 := by
    rw [connDiffBaseExpansionTerm_zero]
    rw [Tensor0SBundle.componentRS_smulRS]
  have hT1 :
      Tensor0SBundle.componentRS (I := I) basis
          (connDiffBaseExpansionTerm (I := I) g h x 1)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
        (1 / 2 : Real) * C1 := by
    rw [connDiffBaseExpansionTerm_one]
    rw [Tensor0SBundle.componentRS_smulRS]
  have hT2 :
      Tensor0SBundle.componentRS (I := I) basis
          (connDiffBaseExpansionTerm (I := I) g h x 2)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
        (-1 / 2 : Real) * C2 := by
    rw [connDiffBaseExpansionTerm_two]
    rw [Tensor0SBundle.componentRS_smulRS]
  rw [Fin.sum_univ_three, hT0, hT1, hT2]
  exact htarget

theorem baseTerms_prod :
    ConnDiffProdTerms 1 connDiffBaseTerms := by
  intro orders horders
  simp [connDiffBaseTerms] at horders
  subst orders
  simp [ConnDiffProdTerm, connDiffProdWeight]

theorem oneTerms_prod :
    ConnDiffProdTerms 2 connDiffOneTerms := by
  intro orders horders
  have hmem : orders = [2] ∨ orders = [1, 1] := by
    simpa [connDiffOneTerms] using horders
  rcases hmem with rfl | rfl
  · refine ⟨by simp, ?_, by simp [connDiffProdWeight]⟩
    intro j hj
    have hj2 : j = 2 := by simpa using hj
    rw [hj2]
    norm_num
  · refine ⟨by simp, ?_, by simp [connDiffProdWeight]⟩
    intro j hj
    have hj1 : j = 1 := by simpa using hj
    rw [hj1]

@[simp]
theorem baseTerms_products
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffMetricProducts (I := I) g h connDiffBaseTerms x =
      metricCovDerivNorm (I := I) 1 g h x := by
  simp [connDiffBaseTerms]

@[simp]
theorem oneTerms_products
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (x : M) :
    connDiffMetricProducts (I := I) g h connDiffOneTerms x =
      metricCovDerivNorm (I := I) 2 g h x +
        metricCovDerivNorm (I := I) 1 g h x *
          metricCovDerivNorm (I := I) 1 g h x := by
  simp [connDiffOneTerms, connDiffMetricProducts, connDiffMetricProduct]

/-- Metric-derivative products are nonnegative. -/
theorem connDiffMetricProduct_nonneg
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (orders : List Nat) (x : M) :
    0 <= connDiffMetricProduct (I := I) g h orders x := by
  induction orders with
  | nil =>
      simp [connDiffMetricProduct]
  | cons j js ih =>
      simpa [connDiffMetricProduct] using
        mul_nonneg (Real.sqrt_nonneg _) ih

/-- Under two-sided `(eps,p)` smallness with `eps < 1`, every nonempty product
of allowed inverse-side metric derivatives is bounded by `eps`. -/
theorem connDiffMetricProduct_le_eps
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1) {orders : List Nat}
    (hne : orders ≠ [])
    (hpos : forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall j : Nat, j ∈ orders -> j <= p)
    {x : M} (hx : x ∈ K) :
    connDiffMetricProduct (I := I) g h orders x <= eps := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.forward.uniform_equiv.1
    linarith
  have heps_sq : eps * eps <= eps := by
    nlinarith
  revert hne hpos hle
  induction orders with
  | nil =>
      intro hne _hpos _hle
      exact False.elim (hne rfl)
  | cons j js ih =>
      intro _hne hpos hle
      have hjmem : j ∈ j :: js := by simp
      have hjbound :
          metricCovDerivNorm (I := I) j g h x <= eps :=
        Happrox.reverse_cov_deriv_small j (hpos j hjmem) (hle j hjmem) x hx
      cases js with
      | nil =>
          simpa [connDiffMetricProduct] using hjbound
      | cons j' js' =>
          have htail_ne : j' :: js' ≠ [] := by simp
          have htail_pos :
              forall a : Nat, a ∈ j' :: js' -> 1 <= a := by
            intro a ha
            exact hpos a (by simp [ha])
          have htail_le :
              forall a : Nat, a ∈ j' :: js' -> a <= p := by
            intro a ha
            exact hle a (by simp [ha])
          have htail_bound :
              connDiffMetricProduct (I := I) g h (j' :: js') x <= eps :=
            ih htail_ne htail_pos htail_le
          have htail_nonneg :
              0 <= connDiffMetricProduct (I := I) g h (j' :: js') x :=
            connDiffMetricProduct_nonneg (I := I) g h (j' :: js') x
          have hprod :
              metricCovDerivNorm (I := I) j g h x *
                  connDiffMetricProduct (I := I) g h (j' :: js') x <=
                eps * eps :=
            mul_le_mul hjbound htail_bound htail_nonneg heps_nonneg
          calc
            connDiffMetricProduct (I := I) g h (j :: j' :: js') x
                =
              metricCovDerivNorm (I := I) j g h x *
                connDiffMetricProduct (I := I) g h (j' :: js') x := by
                simp [connDiffMetricProduct]
            _ <= eps * eps := hprod
            _ <= eps := heps_sq

/-- Under two-sided `(eps,p)` smallness, a finite sum of nonempty products of
allowed inverse-side metric derivatives is bounded by the number of summands
times `eps`. -/
theorem connDiffMetricProducts_le_eps
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1) {terms : List (List Nat)}
    (hne : forall orders : List Nat, orders ∈ terms -> orders ≠ [])
    (hpos : forall orders : List Nat, orders ∈ terms ->
      forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall orders : List Nat, orders ∈ terms ->
      forall j : Nat, j ∈ orders -> j <= p)
    {x : M} (hx : x ∈ K) :
    connDiffMetricProducts (I := I) g h terms x <=
      (terms.length : Real) * eps := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.forward.uniform_equiv.1
    linarith
  induction terms with
  | nil =>
      simp [connDiffMetricProducts]
  | cons orders rest ih =>
      have hhead_mem : orders ∈ orders :: rest := by simp
      have hhead :
          connDiffMetricProduct (I := I) g h orders x <= eps :=
        connDiffMetricProduct_le_eps
          (I := I) Happrox heps_lt
          (hne orders hhead_mem)
          (hpos orders hhead_mem)
          (hle orders hhead_mem) hx
      have hrest :
          connDiffMetricProducts (I := I) g h rest x <=
            (rest.length : Real) * eps := by
        exact ih
          (fun o ho => hne o (by simp [ho]))
          (fun o ho => hpos o (by simp [ho]))
          (fun o ho => hle o (by simp [ho]))
      calc
        connDiffMetricProducts (I := I) g h (orders :: rest) x
            =
          connDiffMetricProduct (I := I) g h orders x +
            connDiffMetricProducts (I := I) g h rest x := by
            simp [connDiffMetricProducts]
        _ <= eps + (rest.length : Real) * eps := add_le_add hhead hrest
        _ = ((orders :: rest).length : Real) * eps := by
            simp
            ring

/-- Coarse `epsilon` constant obtained from `connDiffMetricSum` under a
two-sided `(eps,p)` approximate-isometry hypothesis. -/
def connDiffEpsConstant (C : Real) (k : Nat) (eps : Real) : Real :=
  C * ((Finset.Icc 1 (k + 1)).card : Real) * eps

/-- Raw Lemma-3.11-style control of higher connection-difference derivatives by
inverse-side metric derivatives.

This is an internal producer shape.  The book-facing F3 consumer is the
epsilon-bound form `ConnDiffEpsBoundOn` below, under a full two-sided
approximate-isometry hypothesis.  For positive order this raw linear statement
should only be used after the required norm-comparison constants have been
accounted for. -/
def ConnDiffMetricControlOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) :
    Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <=
          C * connDiffMetricSum (I := I) g h k x

/-- Internal product-form metric control for higher connection-difference
derivatives.

This is the mathematically honest shape for `k >= 1`: differentiating the
Christoffel-difference formula produces finite sums of products of
`nabla_h^j g`, not just a linear sum before the approximate-isometry smallness
is used.  It is proof infrastructure, not the public F3-hi endpoint. -/
def ConnDiffProductControlOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat)
    (C : Real) (terms : List (List Nat)) : Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <=
          C * connDiffMetricProducts (I := I) g h terms x

/-- Pointwise norm of a raised, slot-permuted actual metric covariant
derivative.  This is the linear DC3b termwise norm identity for the
Christoffel symmetrization terms. -/
theorem raiseMetricPerm_norm
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {g h : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a : Nat) (sigma : Fin (a + 2) ≃ Fin (a + 2)) :
    Tensor0SBundle.normRS
        (I := I) (g := h) (x := x) 1 (a + 1)
        (Tensor0SBundle.raiseFirst0S
          (I := I) h x (a + 1)
          (Tensor0SBundle.permute0S
            (I := I) sigma (metricCovDeriv (I := I) g h a x))) =
      metricCovDerivNorm (I := I) a g h x := by
  rw [Tensor0SBundle.normRS_raiseFirst_permute0S
    (I := I) h x (a + 1) basis hinv sigma
    (metricCovDeriv (I := I) g h a x)]
  rfl

/-- A raised, slot-permuted metric covariant derivative using the actual `g`
inverse metric is controlled by the corresponding `h`-measured derivative norm
under the `C^0` part of an approximate isometry. -/
theorem raiseMetricPerm_le
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a : Nat) (sigma : Fin (a + 2) ≃ Fin (a + 2)) :
    Tensor0SBundle.normRS
        (I := I) (g := g) (x := x) 1 (a + 1)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x (a + 1)
          (Tensor0SBundle.permute0S
            (I := I) sigma (metricCovDeriv (I := I) g h a x))) <=
      Real.sqrt ((1 + eps) ^ (a + 2)) *
        metricCovDerivNorm (I := I) a g h x := by
  let A := metricCovDeriv (I := I) g h a x
  have hsymm := Tensor0SBundle.metric_equiv_symm
    (I := I) g h x Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx)
  have hA_sq :
      Tensor0SBundle.normSq0S (I := I) g x (a + 2) A <=
        (1 + eps) ^ (a + 2) *
          Tensor0SBundle.normSq0S (I := I) h x (a + 2) A :=
    Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I) h g x (a + 2) Happrox.uniform_equiv.1 hsymm A
  have hC_nonneg : 0 <= 1 + eps := by
    exact le_trans (by norm_num : (0 : Real) <= 1) Happrox.uniform_equiv.1
  calc
    Tensor0SBundle.normRS
        (I := I) (g := g) (x := x) 1 (a + 1)
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x (a + 1)
          (Tensor0SBundle.permute0S
            (I := I) sigma (metricCovDeriv (I := I) g h a x)))
        = Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a + 2) A) := by
          rw [Tensor0SBundle.normRS_raiseFirst_permute0S
            (I := I) g x (a + 1) basis hinv sigma A]
    _ <= Real.sqrt
          ((1 + eps) ^ (a + 2) *
            Tensor0SBundle.normSq0S (I := I) h x (a + 2) A) :=
          Real.sqrt_le_sqrt hA_sq
    _ = Real.sqrt ((1 + eps) ^ (a + 2)) *
        metricCovDerivNorm (I := I) a g h x := by
          rw [Real.sqrt_mul (pow_nonneg hC_nonneg (a + 2))]
          rfl

/-- Pointwise norm of a raised product of two actual metric covariant
derivatives.  This is a concrete DC3b termwise norm identity; later
differentiated-Christoffel expansions can use it for product terms without
reproving the tensor product algebra. -/
theorem raiseMetricProd_norm
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {g h : SmoothRiemannianMetric I M} {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a b : Nat) :
    Tensor0SBundle.normRS
        (I := I) (g := h) (x := x) 1 (a + 2 + (b + 1))
        (Tensor0SBundle.raiseFirst0S
          (I := I) h x (a + 2 + (b + 1))
          (Bundle.continuousMultilinearMap.product_fun
            (s := a + 2) (q := b + 2)
            (metricCovDeriv (I := I) g h a x)
            (metricCovDeriv (I := I) g h b x))) =
      metricCovDerivNorm (I := I) a g h x *
        metricCovDerivNorm (I := I) b g h x := by
  rw [Tensor0SBundle.normRS_raiseProdR
    (I := I) h x (a + 2) (b + 1) basis hinv
    (metricCovDeriv (I := I) g h a x)
    (metricCovDeriv (I := I) g h b x)]
  rfl

/-- A raised product using the actual `g` inverse metric is controlled by the
`h`-measured metric-derivative product under the `C^0` part of an approximate
isometry.  This is the termwise estimate needed when the Christoffel formula
uses `g^{-1}` but the approximate-isometry smallness controls
`|nabla_h^j g|_h`. -/
theorem raiseMetricProd_le
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a b : Nat) :
    Tensor0SBundle.normRS
        (I := I) (g := g) (x := x) 1 (a + 2 + (b + 1))
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x (a + 2 + (b + 1))
          (Bundle.continuousMultilinearMap.product_fun
            (s := a + 2) (q := b + 2)
            (metricCovDeriv (I := I) g h a x)
            (metricCovDeriv (I := I) g h b x))) <=
      (Real.sqrt ((1 + eps) ^ (a + 2)) *
          Real.sqrt ((1 + eps) ^ (b + 2))) *
        (metricCovDerivNorm (I := I) a g h x *
          metricCovDerivNorm (I := I) b g h x) := by
  let A := metricCovDeriv (I := I) g h a x
  let B := metricCovDeriv (I := I) g h b x
  have hsymm := Tensor0SBundle.metric_equiv_symm
    (I := I) g h x Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx)
  have hA_sq :
      Tensor0SBundle.normSq0S (I := I) g x (a + 2) A <=
        (1 + eps) ^ (a + 2) *
          Tensor0SBundle.normSq0S (I := I) h x (a + 2) A :=
    Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I) h g x (a + 2) Happrox.uniform_equiv.1 hsymm A
  have hB_sq :
      Tensor0SBundle.normSq0S (I := I) g x (b + 2) B <=
        (1 + eps) ^ (b + 2) *
          Tensor0SBundle.normSq0S (I := I) h x (b + 2) B :=
    Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I) h g x (b + 2) Happrox.uniform_equiv.1 hsymm B
  have hC_nonneg : 0 <= 1 + eps := by
    exact le_trans (by norm_num : (0 : Real) <= 1) Happrox.uniform_equiv.1
  have hA :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a + 2) A) <=
        Real.sqrt ((1 + eps) ^ (a + 2)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (a + 2) A) := by
    calc
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a + 2) A)
          <= Real.sqrt
              ((1 + eps) ^ (a + 2) *
                Tensor0SBundle.normSq0S (I := I) h x (a + 2) A) :=
            Real.sqrt_le_sqrt hA_sq
      _ = Real.sqrt ((1 + eps) ^ (a + 2)) *
            Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (a + 2) A) := by
            rw [Real.sqrt_mul (pow_nonneg hC_nonneg (a + 2))]
  have hB :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (b + 2) B) <=
        Real.sqrt ((1 + eps) ^ (b + 2)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (b + 2) B) := by
    calc
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (b + 2) B)
          <= Real.sqrt
              ((1 + eps) ^ (b + 2) *
                Tensor0SBundle.normSq0S (I := I) h x (b + 2) B) :=
            Real.sqrt_le_sqrt hB_sq
      _ = Real.sqrt ((1 + eps) ^ (b + 2)) *
            Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (b + 2) B) := by
            rw [Real.sqrt_mul (pow_nonneg hC_nonneg (b + 2))]
  have hA_nonneg :
      0 <= Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a + 2) A) :=
    Real.sqrt_nonneg _
  have hB_g_nonneg :
      0 <= Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (b + 2) B) :=
    Real.sqrt_nonneg _
  have hA_rhs_nonneg :
      0 <= Real.sqrt ((1 + eps) ^ (a + 2)) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (a + 2) A) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hB_nonneg :
      0 <= Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (b + 2) B) :=
    Real.sqrt_nonneg _
  calc
    Tensor0SBundle.normRS
        (I := I) (g := g) (x := x) 1 (a + 2 + (b + 1))
        (Tensor0SBundle.raiseFirst0S
          (I := I) g x (a + 2 + (b + 1))
          (Bundle.continuousMultilinearMap.product_fun
            (s := a + 2) (q := b + 2)
            (metricCovDeriv (I := I) g h a x)
            (metricCovDeriv (I := I) g h b x)))
        = Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a + 2) A) *
            Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (b + 2) B) := by
          rw [Tensor0SBundle.normRS_raiseProdR
            (I := I) g x (a + 2) (b + 1) basis hinv A B]
    _ <= (Real.sqrt ((1 + eps) ^ (a + 2)) *
            Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (a + 2) A)) *
          (Real.sqrt ((1 + eps) ^ (b + 2)) *
            Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (b + 2) B)) := by
          exact mul_le_mul hA hB hB_g_nonneg hA_rhs_nonneg
    _ = (Real.sqrt ((1 + eps) ^ (a + 2)) *
          Real.sqrt ((1 + eps) ^ (b + 2))) *
        (metricCovDerivNorm (I := I) a g h x *
          metricCovDerivNorm (I := I) b g h x) := by
          simp [metricCovDerivNorm, A, B]
          ring

/-- A finite expansion gives a product-form connection-difference control once
each expansion term is bounded by its schematic product.  Scalar coefficients
can be absorbed into the supplied expansion terms; the constant `C` records the
resulting termwise norm loss.  This is the norm-packaging consumer for the DC3b
concrete product layer. -/
theorem prodControl_of_expansion
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {k : Nat}
    {ι : Type*} [Fintype ι]
    {C : Real} (hC : 0 <= C) (orders : ι -> List Nat)
    {terms : List (List Nat)}
    (hproducts : forall x : M,
      ((Finset.univ : Finset ι).sum fun i =>
        connDiffMetricProduct (I := I) g h (orders i) x) <=
          connDiffMetricProducts (I := I) g h terms x)
    (hexpansion :
      forall Dk : Tensor0SBundle.TensorRSField
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
        ConnDiffDerivRealizes (I := I) g h k Dk ->
          forall x : M, x ∈ K ->
            exists T : ι -> Tensor0SBundle.TensorRSSpace 1 (k + 2) I x,
              Dk x =
                Tensor0SBundle.metricSumRS
                  (I := I) (g := g) (x := x) 1 (k + 2)
                  (Finset.univ : Finset ι) T ∧
              forall i : ι,
                Tensor0SBundle.normRS
                    (I := I) (g := g) (x := x) 1 (k + 2) (T i) <=
                  C * connDiffMetricProduct (I := I) g h (orders i) x) :
    ConnDiffProductControlOn (I := I) K g h k C terms := by
  intro Dk hDk x hx
  rcases hexpansion Dk hDk x hx with ⟨T, hsum, hterm⟩
  let prodSum : Real := (Finset.univ : Finset ι).sum fun i =>
    connDiffMetricProduct (I := I) g h (orders i) x
  have htri :
      connDiffDerivNorm (I := I) g k Dk x <=
        ((Finset.univ : Finset ι).sum fun i =>
          Tensor0SBundle.normRS
            (I := I) (g := g) (x := x) 1 (k + 2) (T i)) := by
    have hraw :=
      Tensor0SBundle.sqrt_normRS_metricSum_le
        (I := I) (g := g) (x := x) 1 (k + 2)
        (Finset.univ : Finset ι) T
    change
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) 1 (k + 2) (Dk x)) <=
        ((Finset.univ : Finset ι).sum fun i =>
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) 1 (k + 2) (T i)))
    rw [hsum]
    exact hraw
  have hterm_sum :
      ((Finset.univ : Finset ι).sum fun i =>
          Tensor0SBundle.normRS
            (I := I) (g := g) (x := x) 1 (k + 2) (T i)) <=
        ((Finset.univ : Finset ι).sum fun i =>
          C * connDiffMetricProduct (I := I) g h (orders i) x) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact hterm i
  have hsumC :
      ((Finset.univ : Finset ι).sum fun i =>
          C * connDiffMetricProduct (I := I) g h (orders i) x) =
        C * prodSum := by
    simp [prodSum, Finset.mul_sum]
  have hproducts_x : prodSum <= connDiffMetricProducts (I := I) g h terms x := by
    simpa [prodSum] using hproducts x
  have hfinal :
      C * prodSum <= C * connDiffMetricProducts (I := I) g h terms x :=
    mul_le_mul_of_nonneg_left hproducts_x hC
  calc
    connDiffDerivNorm (I := I) g k Dk x
        <= (Finset.univ : Finset ι).sum fun i =>
          Tensor0SBundle.normRS
            (I := I) (g := g) (x := x) 1 (k + 2) (T i) := htri
    _ <= (Finset.univ : Finset ι).sum fun i =>
          C * connDiffMetricProduct (I := I) g h (orders i) x :=
        hterm_sum
    _ = C * prodSum := hsumC
    _ <= C * connDiffMetricProducts (I := I) g h terms x := hfinal

/-- Uniform product-form connection-difference controls for all orders below
`m`.  The list of product terms may depend on the derivative order. -/
def ConnDiffProductControlsBelow
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) (terms : Nat -> List (List Nat)) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffProductControlOn (I := I) K g h k (C k) (terms k)

/-- Positive-order product-form connection-difference controls below `m`.

The `k = 0` estimate is produced separately by the checked base connection
difference bound, so this is the exact remaining F3e1b producer shape. -/
def ConnDiffProdTail
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) (terms : Nat -> List (List Nat)) : Prop :=
  forall k : Nat, 0 < k -> k < m ->
    ConnDiffProductControlOn (I := I) K g h k (C k) (terms k)

/-- Uniform connection-difference metric controls for all orders below `m`. -/
def ConnDiffMetricControlsBelow
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffMetricControlOn (I := I) K g h k (C k)

/-- A book-shaped linear connection-difference control is a product-control
estimate using singleton product terms. -/
theorem prodControl_of_sum
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {k : Nat} {C : Real}
    (hcontrol : ConnDiffMetricControlOn (I := I) K g h k C) :
    ConnDiffProductControlOn (I := I) K g h k C (connDiffLinTerms k) := by
  intro Dk hDk x hx
  simpa using hcontrol Dk hDk x hx

/-- Finite-order linear controls can feed the product-control layer through
singleton product terms. -/
theorem prodControls_of_sums
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {m : Nat} {C : Nat -> Real}
    (hcontrols : ConnDiffMetricControlsBelow (I := I) K g h m C) :
    ConnDiffProductControlsBelow (I := I) K g h m C connDiffLinTerms := by
  intro k hk
  exact prodControl_of_sum (I := I) (hcontrols k hk)

/-- Positive-order linear controls can feed the remaining product-tail target
through singleton product terms. -/
theorem prodTail_of_sumTail
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {m : Nat} {C : Nat -> Real}
    (hcontrols : forall k : Nat, 0 < k -> k < m ->
      ConnDiffMetricControlOn (I := I) K g h k (C k)) :
    ConnDiffProdTail (I := I) K g h m C connDiffLinTerms := by
  intro k hkpos hk
  exact prodControl_of_sum (I := I) (hcontrols k hkpos hk)

/-- Uniform connection-difference derivative bounds for all orders below `m`. -/
def ConnDiffDerivBoundsBelow
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffDerivBoundOn (I := I) K g h k (C k)

/-- Book-facing F3-hi epsilon control for a realized `k`-th `h`-covariant
derivative of `Gamma_g - Gamma_h`.  The constant is independent of `eps`; this
is the shape consumed in MSM135 Chapter 4 Lemma `lbl368`. -/
def ConnDiffEpsBoundOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) : Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C * eps

/-- Uniform book-facing F3-hi epsilon controls for all orders below `m`. -/
def ConnDiffEpsBoundsBelow
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffEpsBoundOn (I := I) K eps g h k (C k)

/-- Numeric F3e packaging: once the Lemma-3.11-style metric control has been
proved, the inverse-side derivative smallness in a two-sided approximate
isometry turns it into an `epsilon` connection-difference derivative bound. -/
theorem connDiffBound_of_metricControl
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p k : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hk : k + 1 <= p) {C : Real} (hC : 0 <= C)
    (hcontrol : ConnDiffMetricControlOn (I := I) K g h k C) :
    ConnDiffDerivBoundOn (I := I) K g h k
      (connDiffEpsConstant C k eps) := by
  intro Dk hDk x hx
  have hbase :
      connDiffDerivNorm (I := I) g k Dk x <=
        C * connDiffMetricSum (I := I) g h k x :=
    hcontrol Dk hDk x hx
  have hsum :
      connDiffMetricSum (I := I) g h k x <=
        ((Finset.Icc 1 (k + 1)).card : Real) * eps := by
    unfold connDiffMetricSum
    calc
      (Finset.Icc 1 (k + 1)).sum
          (fun j : Nat => metricCovDerivNorm (I := I) j g h x)
          <= (Finset.Icc 1 (k + 1)).sum (fun _j : Nat => eps) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hjbounds := Finset.mem_Icc.mp hj
            exact Happrox.reverse_cov_deriv_small
              j hjbounds.1 (le_trans hjbounds.2 hk) x hx
      _ = ((Finset.Icc 1 (k + 1)).card : Real) * eps := by
            simp
  have hmul :
      C * connDiffMetricSum (I := I) g h k x <=
        C * (((Finset.Icc 1 (k + 1)).card : Real) * eps) :=
    mul_le_mul_of_nonneg_left hsum hC
  exact le_trans hbase (by
    simpa [connDiffEpsConstant, mul_assoc] using hmul)

/-- A raw linear metric-control estimate feeds the book-facing epsilon-bound
predicate.  The metric-control constant is enlarged by the length of the
linear sum `j = 1, ..., k + 1`. -/
theorem epsBound_of_metric
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p k : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hk : k + 1 <= p) {C : Real} (hC : 0 <= C)
    (hcontrol : ConnDiffMetricControlOn (I := I) K g h k C) :
    ConnDiffEpsBoundOn (I := I) K eps g h k
      (C * ((Finset.Icc 1 (k + 1)).card : Real)) := by
  have hbound :=
    connDiffBound_of_metricControl
      (I := I) Happrox hk hC hcontrol
  intro Dk hDk x hx
  simpa [ConnDiffEpsBoundOn, ConnDiffDerivBoundOn,
    connDiffEpsConstant, mul_assoc] using hbound Dk hDk x hx

/-- Product-form F3e packaging: a finite product-control estimate and the
two-sided approximate-isometry smallness imply an epsilon bound for the
realized connection-difference derivative. -/
theorem connDiffBound_of_productControl
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p k : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1)
    {C : Real} (hC : 0 <= C) {terms : List (List Nat)}
    (hne : forall orders : List Nat, orders ∈ terms -> orders ≠ [])
    (hpos : forall orders : List Nat, orders ∈ terms ->
      forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall orders : List Nat, orders ∈ terms ->
      forall j : Nat, j ∈ orders -> j <= p)
    (hcontrol : ConnDiffProductControlOn (I := I) K g h k C terms) :
    ConnDiffDerivBoundOn (I := I) K g h k
      (C * (terms.length : Real) * eps) := by
  intro Dk hDk x hx
  have hbase :
      connDiffDerivNorm (I := I) g k Dk x <=
        C * connDiffMetricProducts (I := I) g h terms x :=
    hcontrol Dk hDk x hx
  have hprod :
      connDiffMetricProducts (I := I) g h terms x <=
        (terms.length : Real) * eps :=
    connDiffMetricProducts_le_eps
      (I := I) Happrox heps_lt hne hpos hle hx
  have hmul :
      C * connDiffMetricProducts (I := I) g h terms x <=
        C * ((terms.length : Real) * eps) :=
    mul_le_mul_of_nonneg_left hprod hC
  exact le_trans hbase (by
    simpa [mul_assoc] using hmul)

/-- A product-control estimate feeds the book-facing epsilon-bound predicate.
The product-control constant is enlarged by the number of schematic terms. -/
theorem epsBound_of_prod
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p k : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1)
    {C : Real} (hC : 0 <= C) {terms : List (List Nat)}
    (hne : forall orders : List Nat, orders ∈ terms -> orders ≠ [])
    (hpos : forall orders : List Nat, orders ∈ terms ->
      forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall orders : List Nat, orders ∈ terms ->
      forall j : Nat, j ∈ orders -> j <= p)
    (hcontrol : ConnDiffProductControlOn (I := I) K g h k C terms) :
    ConnDiffEpsBoundOn (I := I) K eps g h k
      (C * (terms.length : Real)) := by
  have hbound :=
    connDiffBound_of_productControl
      (I := I) Happrox heps_lt hC hne hpos hle hcontrol
  intro Dk hDk x hx
  simpa [ConnDiffEpsBoundOn, ConnDiffDerivBoundOn, mul_assoc]
    using hbound Dk hDk x hx

/-- Product-form F3e packaging where the product terms are supplied as
schematic Christoffel terms of a fixed weight. -/
theorem connDiffBound_of_terms
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p k w : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1)
    {C : Real} (hC : 0 <= C) {terms : List (List Nat)}
    (hterms : ConnDiffProdTerms w terms) (hw : w <= p)
    (hcontrol : ConnDiffProductControlOn (I := I) K g h k C terms) :
    ConnDiffDerivBoundOn (I := I) K g h k
      (C * (terms.length : Real) * eps) := by
  refine connDiffBound_of_productControl
    (I := I) Happrox heps_lt hC ?_ ?_ ?_ hcontrol
  · intro orders horders
    exact prodTerms_nonempty hterms horders
  · intro orders horders j hj
    exact prodTerms_pos hterms horders hj
  · intro orders horders j hj
    exact le_trans (prodTerms_le_weight hterms horders hj) hw

/-- Aggregated product-form F3e packaging below a finite order.  Product
controls for each order below `m`, together with allowed nonempty product-term
indices, give epsilon connection-difference derivative bounds for all those
orders. -/
theorem connDiffBoundsBelow_of_productControls
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1)
    {C : Nat -> Real} {terms : Nat -> List (List Nat)}
    (hC : forall k : Nat, k < m -> 0 <= C k)
    (hne : forall k : Nat, k < m ->
      forall orders : List Nat, orders ∈ terms k -> orders ≠ [])
    (hpos : forall k : Nat, k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall k : Nat, k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> j <= p)
    (hcontrols :
      ConnDiffProductControlsBelow (I := I) K g h m C terms) :
    ConnDiffDerivBoundsBelow (I := I) K g h m
      (fun k : Nat => C k * ((terms k).length : Real) * eps) := by
  intro k hk
  exact connDiffBound_of_productControl
    (I := I) Happrox heps_lt (hC k hk)
    (hne k hk) (hpos k hk) (hle k hk) (hcontrols k hk)

/-- Aggregated product controls feed the book-facing epsilon-bound package. -/
theorem epsBounds_of_prods
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (heps_lt : eps < 1)
    {C : Nat -> Real} {terms : Nat -> List (List Nat)}
    (hC : forall k : Nat, k < m -> 0 <= C k)
    (hne : forall k : Nat, k < m ->
      forall orders : List Nat, orders ∈ terms k -> orders ≠ [])
    (hpos : forall k : Nat, k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall k : Nat, k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> j <= p)
    (hcontrols :
      ConnDiffProductControlsBelow (I := I) K g h m C terms) :
    ConnDiffEpsBoundsBelow (I := I) K eps g h m
      (fun k : Nat => C k * ((terms k).length : Real)) := by
  intro k hk
  exact epsBound_of_prod
    (I := I) Happrox heps_lt (hC k hk)
    (hne k hk) (hpos k hk) (hle k hk) (hcontrols k hk)

/-- Aggregated F3e packaging below a finite order: metric controls for each
order below `m` give epsilon connection-difference derivative bounds for the
same orders. -/
theorem connDiffBoundsBelow_of_metricControls
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hm : m <= p) {C : Nat -> Real}
    (hC : forall k : Nat, k < m -> 0 <= C k)
    (hcontrols : ConnDiffMetricControlsBelow (I := I) K g h m C) :
    ConnDiffDerivBoundsBelow (I := I) K g h m
      (fun k : Nat => connDiffEpsConstant (C k) k eps) := by
  intro k hk
  exact connDiffBound_of_metricControl
    (I := I) Happrox
    (le_trans (Nat.succ_le_of_lt hk) hm)
    (hC k hk) (hcontrols k hk)

/-- The `k = 0` connection-difference derivative bound, packaged in the
higher-derivative realization vocabulary used by F3e. -/
theorem connDiffDerivBound_zero
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffDerivBoundOn (I := I) K g h 0 (12 * eps) := by
  intro D0 hD0 x hx
  rcases hD0 with ⟨D, hD, hderiv⟩
  cases hderiv
  simpa [connDiffDerivNorm, ConnDiffFieldRealizes, hD x] using
    connDiff_book_le_eps_g
      (I := I) Happrox hx hp heps_lt (basis x hx) (hinv x hx)

/-- The checked `k = 0` instance of the book-facing F3-hi epsilon control. -/
theorem connDiffEpsBound_zero
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffEpsBoundOn (I := I) K eps g h 0 12 := by
  intro D0 hD0 x hx
  simpa using
    connDiffDerivBound_zero
      (I := I) Happrox hp heps_lt basis hinv D0 hD0 x hx

/-- If the first positive-order differentiated-Christoffel product estimate is
available with the expected terms `[[2], [1, 1]]`, then it gives the
book-facing `k = 1` epsilon-bound.  This is the corrected public F3-hi-k1
assembly target; the remaining proof obligation is the internal product-control
producer. -/
theorem epsBound_one_of_prod
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 2 <= p) (heps_lt : eps < 1)
    {C : Real} (hC : 0 <= C)
    (hcontrol :
      ConnDiffProductControlOn (I := I) K g h 1 C connDiffOneTerms) :
    ConnDiffEpsBoundOn (I := I) K eps g h 1
      (C * (connDiffOneTerms.length : Real)) := by
  refine epsBound_of_prod
    (I := I) Happrox heps_lt hC ?_ ?_ ?_ hcontrol
  · intro orders horders
    exact prodTerms_nonempty oneTerms_prod horders
  · intro orders horders j hj
    exact prodTerms_pos oneTerms_prod horders hj
  · intro orders horders j hj
    exact le_trans (prodTerms_le_weight oneTerms_prod horders hj) hp

/-- Controls below order `2` from the checked `k = 0` bound and a supplied
first positive-order product-control producer. -/
theorem epsBounds_two_of_oneProd
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 2 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {C : Real} (hC : 0 <= C)
    (hcontrol :
      ConnDiffProductControlOn (I := I) K g h 1 C connDiffOneTerms) :
    ConnDiffEpsBoundsBelow (I := I) K eps g h 2
      (fun k : Nat =>
        if k = 0 then 12 else C * (connDiffOneTerms.length : Real)) := by
  intro k hk
  cases k with
  | zero =>
      simpa using
        connDiffEpsBound_zero
          (I := I) Happrox
          (le_trans (by norm_num : (1 : Nat) <= 2) hp)
          heps_lt basis hinv
  | succ k =>
      have hk0 : k = 0 := by
        have hklt : k < 1 := Nat.succ_lt_succ_iff.mp hk
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hklt)
      subst k
      simpa using
        epsBound_one_of_prod
          (I := I) Happrox hp heps_lt hC hcontrol

/-- The `k = 0` instance of the book's metric-control producer for
`Gamma_g - Gamma_h`. -/
theorem connDiffMetricControl_zero
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K h g C)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffMetricControlOn
      (I := I) K g h 0 ((3 / 2 : Real) * Real.sqrt (C ^ 3)) := by
  intro D0 hD0 x hx
  rcases hD0 with ⟨D, hD, hderiv⟩
  cases hderiv
  have hdiff :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K) g h hx C hEq (basis x hx) (hinv x hx)
  calc
    connDiffDerivNorm (I := I) g 0 D x
        <= (3 / 2 : Real) *
            (Real.sqrt (C ^ 3) * metricCovDerivNorm (I := I) 1 g h x) := by
          simpa [connDiffDerivNorm, ConnDiffFieldRealizes, hD x] using hdiff
    _ = ((3 / 2 : Real) * Real.sqrt (C ^ 3)) *
          connDiffMetricSum (I := I) g h 0 x := by
          simp [connDiffMetricSum]
          ring

/-- The `k = 0` metric-control producer specialized to the `C^0` part of a
two-sided approximate isometry. -/
theorem connDiffMetricControl_zero_of_twoSided
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffMetricControlOn
      (I := I) K g h 0
      ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) :=
  connDiffMetricControl_zero
    (I := I)
    (metricUniformEquivalentOn_symm (I := I) Happrox.forward.uniform_equiv)
    basis hinv

/-- The `k = 0` product-form producer.  This is the singleton-product version
of `connDiffMetricControl_zero`, included so the product-control layer can
handle the base connection difference uniformly. -/
theorem connDiffProductControl_zero
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K h g C)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffProductControlOn
      (I := I) K g h 0 ((3 / 2 : Real) * Real.sqrt (C ^ 3)) [[1]] := by
  intro D0 hD0 x hx
  have hcontrol :=
    connDiffMetricControl_zero
      (I := I) (K := K) (g := g) (h := h) hEq basis hinv D0 hD0 x hx
  simpa [connDiffMetricSum] using hcontrol

/-- The `k = 0` product-form producer specialized to a two-sided
approximate-isometry hypothesis. -/
theorem connDiffProductControl_zero_of_twoSided
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffProductControlOn
      (I := I) K g h 0
      ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) [[1]] :=
  connDiffProductControl_zero
    (I := I)
    (metricUniformEquivalentOn_symm (I := I) Happrox.forward.uniform_equiv)
    basis hinv

/-- Product-form controls below order `1`, supplied by the `k = 0` singleton
producer. -/
theorem connDiffProductControlsBelow_one_of_twoSided
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffProductControlsBelow (I := I) K g h 1
      (fun _ : Nat => (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3))
      (fun _ : Nat => [[1]]) := by
  intro k hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  subst k
  exact connDiffProductControl_zero_of_twoSided
    (I := I) Happrox basis hinv

/-- Full product-form controls below `m` from the checked singleton `k = 0`
producer and a positive-order tail producer.

This is only assembly: the hard geometric input remains `ConnDiffProdTail`,
the differentiated-Christoffel product estimate for `k > 0`. -/
theorem connDiffProductControlsBelow_of_tail_zero
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {C : Nat -> Real} {terms : Nat -> List (List Nat)}
    (hC0 : C 0 = (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3))
    (hterms0 : terms 0 = [[1]])
    (htail : ConnDiffProdTail (I := I) K g h m C terms) :
    ConnDiffProductControlsBelow (I := I) K g h m C terms := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simpa [hC0, hterms0] using
      connDiffProductControl_zero_of_twoSided
        (I := I) Happrox basis hinv
  · exact htail k (Nat.pos_of_ne_zero hk0) hk

/-- Assemble the checked `k = 0` connection-difference estimate with a
positive-order product-control producer.  This keeps the remaining geometric
frontier exactly at the differentiated Christoffel formula for `k > 0`. -/
theorem connDiffTailBound
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {C : Nat -> Real} {terms : Nat -> List (List Nat)}
    (hC : forall k : Nat, 0 < k -> k < m -> 0 <= C k)
    (hne : forall k : Nat, 0 < k -> k < m ->
      forall orders : List Nat, orders ∈ terms k -> orders ≠ [])
    (hpos : forall k : Nat, 0 < k -> k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> 1 <= j)
    (hle : forall k : Nat, 0 < k -> k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> j <= p)
    (hcontrols : ConnDiffProdTail (I := I) K g h m C terms) :
    ConnDiffDerivBoundsBelow (I := I) K g h m
      (fun k : Nat =>
        if k = 0 then 12 * eps
        else C k * ((terms k).length : Real) * eps) := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simpa using
      connDiffDerivBound_zero
        (I := I) Happrox hp heps_lt basis hinv
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hbound :
        ConnDiffDerivBoundOn (I := I) K g h k
          (C k * ((terms k).length : Real) * eps) :=
      connDiffBound_of_productControl
        (I := I) Happrox heps_lt (hC k hkpos hk)
        (hne k hkpos hk) (hpos k hkpos hk) (hle k hkpos hk)
        (hcontrols k hkpos hk)
    simpa [hk0] using hbound

/-- Variant of `connDiffTailBound` for the expected differentiated-Christoffel
producer shape: every product factor at order `k` has derivative order at most
`k + 1`.  If `m <= p`, this supplies the approximate-isometry admissibility
condition `j <= p`. -/
theorem connDiffTailBound_of_ordered
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (hm : m <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {C : Nat -> Real} {terms : Nat -> List (List Nat)}
    (hC : forall k : Nat, 0 < k -> k < m -> 0 <= C k)
    (hne : forall k : Nat, 0 < k -> k < m ->
      forall orders : List Nat, orders ∈ terms k -> orders ≠ [])
    (hpos : forall k : Nat, 0 < k -> k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> 1 <= j)
    (hord : forall k : Nat, 0 < k -> k < m ->
      forall orders : List Nat, orders ∈ terms k ->
        forall j : Nat, j ∈ orders -> j <= k + 1)
    (hcontrols : ConnDiffProdTail (I := I) K g h m C terms) :
    ConnDiffDerivBoundsBelow (I := I) K g h m
      (fun k : Nat =>
        if k = 0 then 12 * eps
        else C k * ((terms k).length : Real) * eps) := by
  refine connDiffTailBound
    (I := I) Happrox hp heps_lt basis hinv hC hne hpos ?_ hcontrols
  intro k hkpos hk orders horders j hj
  exact le_trans (hord k hkpos hk orders horders j hj)
    (le_trans (Nat.succ_le_of_lt hk) hm)

/-- Variant of `connDiffTailBound` where the positive-order product terms are
registered as schematic Christoffel product terms of weight `k + 1`. -/
theorem tailBound_of_terms
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (hm : m <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {C : Nat -> Real} {terms : Nat -> List (List Nat)}
    (hC : forall k : Nat, 0 < k -> k < m -> 0 <= C k)
    (hterms : forall k : Nat, 0 < k -> k < m ->
      ConnDiffProdTerms (k + 1) (terms k))
    (hcontrols : ConnDiffProdTail (I := I) K g h m C terms) :
    ConnDiffDerivBoundsBelow (I := I) K g h m
      (fun k : Nat =>
        if k = 0 then 12 * eps
        else C k * ((terms k).length : Real) * eps) := by
  refine connDiffTailBound_of_ordered
    (I := I) Happrox hp hm heps_lt basis hinv hC ?_ ?_ ?_ hcontrols
  · intro k hkpos hk orders horders
    exact prodTerms_nonempty (hterms k hkpos hk) horders
  · intro k hkpos hk orders horders j hj
    exact prodTerms_pos (hterms k hkpos hk) horders hj
  · intro k hkpos hk orders horders j hj
    exact prodTerms_le_weight (hterms k hkpos hk) horders hj

/-- Book-shaped positive linear controls give the checked F3e derivative bounds.

The remaining geometric producer can now focus on the linear estimate
`|nabla_h^k (Gamma_g - Gamma_h)| <= C_k sum_{j=1}^{k+1} |nabla_h^j g|`; this
lemma feeds that estimate through singleton product terms and the existing
epsilon absorption. -/
theorem tailBound_of_sumTail
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p m : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (hm : m <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x ∈ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x ∈ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {C : Nat -> Real}
    (hC : forall k : Nat, 0 < k -> k < m -> 0 <= C k)
    (hcontrols : forall k : Nat, 0 < k -> k < m ->
      ConnDiffMetricControlOn (I := I) K g h k (C k)) :
    ConnDiffDerivBoundsBelow (I := I) K g h m
      (fun k : Nat =>
        if k = 0 then 12 * eps
        else C k * ((connDiffLinTerms k).length : Real) * eps) := by
  refine connDiffTailBound_of_ordered
    (I := I) Happrox hp hm heps_lt basis hinv hC ?_ ?_ ?_ ?_
  · intro _k _hkpos _hk orders horders
    exact linTerms_nonempty horders
  · intro _k _hkpos _hk orders horders j hj
    exact linTerms_pos horders hj
  · intro _k _hkpos _hk orders horders j hj
    exact linTerms_le_succ horders hj
  · exact prodTail_of_sumTail (I := I) hcontrols

/-- F3 component-action estimate at order one.

This is the component-level consequence of `connDiff_le_approx`: the
connection-difference action on one component of a mixed tensor is bounded by
the connection-difference norm times the tensor norm, with a coarse finite
constant depending only on valence and dimension.  The orientation is
`leviCivita(h) - leviCivita(g)`, matching `connDiff_le_approx`; the later
`nabla` comparison chooses the corresponding sign. -/
theorem connAct_le_approx
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat} (T : Tensor0SBundle.TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |Tensor0SBundle.connActComp
      (fun l i j =>
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)
          (fun _ : Fin 1 => l)
          (fun q : Fin 2 => if q = 0 then i else j))
      (fun upper' lower' => Tensor0SBundle.componentRS (I := I) basis T upper' lower')
      upper lower| <=
      Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
  let A : Tensor0SBundle.TensorRSSpace 1 2 I x :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x
  have hbase :=
    Tensor0SBundle.abs_connActTensor_le
      (I := I) h x basis hinv A T upper lower
  have hdiff :=
    connDiff_le_approx
      (I := I) Happrox hx hp basis hinv
  have hT_nonneg :
      0 <= Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r s T) :=
    Real.sqrt_nonneg _
  have hvalence_nonneg :
      0 <= ((r + s : Nat) : Real) := by
    positivity
  have hdim_nonneg :
      0 <= (Fintype.card Idx : Real) := by
    positivity
  have hconst :
      Tensor0SBundle.connActConst (Idx := Idx) r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) 1 2 A))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) <=
      Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
    unfold Tensor0SBundle.connActConst
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdiff hT_nonneg)
        hdim_nonneg)
      hvalence_nonneg
  exact hbase.trans hconst

set_option backward.isDefEq.respectTransparency false in
/-- F3 order-one component estimate for covariant derivatives of a mixed tensor.

This combines the manifold component identity
`Tensor0SBundle.componentRS_nablaRSFun_sub` with the approximate-isometry
connection-difference estimate `connAct_le_approx`.  It is still a local-frame
component statement: the later F3 induction/norm packaging consumes this
component estimate and the existing finite-dimensional tensor norm comparison. -/
theorem nablaRS_component_le_approx
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (y : M) -> Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r y)
    (V : Idx -> (y : M) -> TangentSpace I y)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx)
    (hX_at : X x = basis (lower 0))
    (hβ_at : β x = Tensor0SBundle.basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x = basis i)
    (hpairT : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => (T y (β y)) (fun a : Fin s => V (lower a.succ) y)) x)
    (hpairβ : forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => β y (fun a : Fin r => V (slots a) y)) x)
    (hβmodel : DifferentiableWithinAt Real
      (TensorLieDeriv.tensor0SModelInChart
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x β)
      (Set.range I) (extChartAt I x x))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x (V i))
        (Set.range I) (extChartAt I x x))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (Module.finBasis Real E).coord j
            (TensorLieDeriv.tangentFieldModelInChart
              (𝕜 := Real) (I := I) x (V i) (extChartAt I x y))) x) :
    |Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.nablaRSFun
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) X T x -
          Tensor0SBundle.nablaRSFun
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) X T x)
        upper (fun b : Fin s => lower b.succ)| <=
      Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s (T x))) := by
  let covh := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let covg := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  have hcomp := Tensor0SBundle.componentRS_nablaRSFun_sub
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) covh covg X T β x basis V upper lower
    hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord
  have hconn :
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.nablaRSFun
              (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s covh X T x -
            Tensor0SBundle.nablaRSFun
              (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s covg X T x)
          upper (fun b : Fin s => lower b.succ) =
        Tensor0SBundle.connActComp
          (fun l i j =>
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covh covg x)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            Tensor0SBundle.componentRS (I := I) basis (T x) upper' lower')
          upper lower := by
    calc
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.nablaRSFun
              (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s covh X T x -
            Tensor0SBundle.nablaRSFun
              (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s covg X T x)
          upper (fun b : Fin s => lower b.succ)
          =
        (∑ a : Fin r, ∑ k : Idx,
          basis.coord (upper a)
            (((CovariantDerivative.difference covh covg x) (basis k)) (basis (lower 0))) *
            Tensor0SBundle.componentRS (I := I) basis (T x) (Function.update upper a k)
              (fun b : Fin s => lower b.succ)) -
        (∑ b : Fin s, ∑ k : Idx,
          basis.coord k
            (((CovariantDerivative.difference covh covg x) (basis (lower b.succ)))
              (basis (lower 0))) *
            Tensor0SBundle.componentRS (I := I) basis (T x) upper
              (Function.update (fun c : Fin s => lower c.succ) b k)) := hcomp
      _ =
        Tensor0SBundle.connActComp
          (fun l i j =>
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covh covg x)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            Tensor0SBundle.componentRS (I := I) basis (T x) upper' lower')
          upper lower := by
          simp [Tensor0SBundle.connActComp, Tensor0SBundle.basisTensor0S_apply]
          rfl
  rw [hconn]
  exact connAct_le_approx
    (I := I) Happrox hx hp basis hinv (T x) upper lower

/-- F3c norm packaging at order one.

If every component of the covariant-derivative difference satisfies the
component estimate supplied by `nablaRS_component_le_approx`, then the full
pointwise mixed-tensor norm is bounded by the corresponding finite-dimensional
component-count factor.  This is the final finite-sum step in the `p = 1`
part of MSM135 Chapter 4, Lemma "Norms of covariant derivatives of tensors,
I"; producing the component bounds is handled by `nablaRS_component_le_approx`.
-/
theorem nablaRS_norm_le_approx_comps
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (A : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      |Tensor0SBundle.componentRS (I := I) basis A upper lower| <=
        Tensor0SBundle.connActConst (Idx := Idx) r s
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
          (Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) r s T))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r (s + 1) A) <=
      Real.sqrt
        ((Fintype.card (Fin r -> Idx) : Real) *
          ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
            (Tensor0SBundle.connActConst (Idx := Idx) r s
              ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
              (Real.sqrt
                (Tensor0SBundle.normSqRS
                  (I := I) (g := h) (x := x) r s T))) ^ 2)) := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hcoef_nonneg :
      0 <= (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) heps_nonneg)
  have hT_nonneg :
      0 <= Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r s T) :=
    Real.sqrt_nonneg _
  have hvalence_nonneg : 0 <= ((r + s : Nat) : Real) := by
    positivity
  have hcard_nonneg : 0 <= (Fintype.card Idx : Real) := by
    positivity
  have hB :
      0 <= Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
    unfold Tensor0SBundle.connActConst
    exact mul_nonneg hvalence_nonneg
      (mul_nonneg hcard_nonneg (mul_nonneg hcoef_nonneg hT_nonneg))
  exact Tensor0SBundle.sqrt_normRS_le_comps
    (I := I) h x r (s + 1) basis hinv A hB hcomp

/-- Coefficient from the checked connection-difference estimate used in the
order-one F3 bounds. -/
def connDiffCoeff (eps : Real) : Real :=
  (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)

/-- Component-action bound with the connection-difference coefficient inserted. -/
def connActApproxBound
    (Idx : Type*) [Fintype Idx] (eps : Real) (r s : Nat) (Tnorm : Real) : Real :=
  Tensor0SBundle.connActConst (Idx := Idx) r s (connDiffCoeff eps) Tnorm

/-- The explicit `p = 1` error term in the `g` norm for the F3d assembly. -/
def nablaRSOneError
    (eps : Real)
    {g : SmoothRiemannianMetric I M}
    {Idx : Type*} [Fintype Idx]
    {x : M} (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) : Real :=
  Real.sqrt ((1 + eps) ^ (r + (s + 1))) *
    Real.sqrt
      ((Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (connActApproxBound (Idx := Idx) eps r s
            (Real.sqrt ((1 + eps) ^ (r + s)) *
              Real.sqrt
                (Tensor0SBundle.normSqRS
                  (I := I) (g := g) (x := x) r s T))) ^ 2))

/-- Component hypothesis consumed by the order-one F3 norm assembly. -/
def NablaDiffCompBound
    (eps : Real)
    {h : SmoothRiemannianMetric I M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (A : Tensor0SBundle.TensorRSSpace r (s + 1) I x) : Prop :=
  forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
    |Tensor0SBundle.componentRS (I := I) basis A upper lower| <=
      connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T))

set_option maxHeartbeats 600000 in
/-- The `|T|_h` component-error bound is dominated by the explicit F3d
`|T|_g` error factor. -/
theorem nablaRSOneError_hpart
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K)
    {Idx : Type*} [Fintype Idx]
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    Real.sqrt
      ((Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (connActApproxBound (Idx := Idx) eps r s
            (Real.sqrt
              (Tensor0SBundle.normSqRS
                (I := I) (g := h) (x := x) r s T))) ^ 2)) <=
    Real.sqrt
      ((Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (connActApproxBound (Idx := Idx) eps r s
            (Real.sqrt ((1 + eps) ^ (r + s)) *
              Real.sqrt
                (Tensor0SBundle.normSqRS
                  (I := I) (g := g) (x := x) r s T))) ^ 2)) := by
  have hT_h_g :=
    Happrox.sqrt_normRS_upper (I := I) hx r s T
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hcoef_nonneg :
      0 <= connDiffCoeff eps := by
    unfold connDiffCoeff
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) heps_nonneg)
  have hT_h_nonneg :
      0 <= Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r s T) :=
    Real.sqrt_nonneg _
  have hT_g_nonneg :
      0 <= Real.sqrt ((1 + eps) ^ (r + s)) *
        Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) r s T) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hvalence_nonneg : 0 <= ((r + s : Nat) : Real) := by
    positivity
  have hcardIdx_nonneg : 0 <= (Fintype.card Idx : Real) := by
    positivity
  have hB_h_nonneg :
      0 <= connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
    unfold connActApproxBound Tensor0SBundle.connActConst
    exact mul_nonneg hvalence_nonneg
      (mul_nonneg hcardIdx_nonneg (mul_nonneg hcoef_nonneg hT_h_nonneg))
  have hB_g_nonneg :
      0 <= connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt ((1 + eps) ^ (r + s)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s T)) := by
    unfold connActApproxBound Tensor0SBundle.connActConst
    exact mul_nonneg hvalence_nonneg
      (mul_nonneg hcardIdx_nonneg (mul_nonneg hcoef_nonneg hT_g_nonneg))
  have hB_le :
      connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) <=
      connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt ((1 + eps) ^ (r + s)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s T)) := by
    unfold connActApproxBound Tensor0SBundle.connActConst
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hT_h_g hcoef_nonneg)
        hcardIdx_nonneg)
      hvalence_nonneg
  have hBsq_le :
      (connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T))) ^ 2 <=
      (connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt ((1 + eps) ^ (r + s)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s T))) ^ 2 :=
    (sq_le_sq₀ hB_h_nonneg hB_g_nonneg).2 hB_le
  have hcardUpper_nonneg :
      0 <= (Fintype.card (Fin r -> Idx) : Real) := by
    positivity
  have hcardLower_nonneg :
      0 <= (Fintype.card (Fin (s + 1) -> Idx) : Real) := by
    positivity
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hBsq_le hcardLower_nonneg)
      hcardUpper_nonneg)

/-- Component-packaged derivative difference is bounded by the explicit F3d
error term in the `g` norm. -/
theorem nablaRSOneError_of_comps
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (A : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    (hcomp : NablaDiffCompBound (I := I) (h := h) (Idx := Idx) eps basis T A) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) A) <=
      nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T := by
  have hdiff_h :=
    nablaRS_norm_le_approx_comps
      (I := I) Happrox basis hinv T A
      (by
        intro upper lower
        simpa [NablaDiffCompBound, connActApproxBound, connDiffCoeff] using
          hcomp upper lower)
  have hdiff_g_h :=
    Tensor0SBundle.sqrt_normRS_lower_le_of_equiv
      (I := I) g h x r (s + 1) Happrox.uniform_equiv.1
      (Happrox.uniform_equiv.2 x hx) A
  have hdiff_h_g :=
    nablaRSOneError_hpart (I := I) (Idx := Idx) Happrox hx T
  calc
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) A)
        <= Real.sqrt ((1 + eps) ^ (r + (s + 1))) *
            Real.sqrt
              (Tensor0SBundle.normSqRS
                (I := I) (g := h) (x := x) r (s + 1) A) :=
          hdiff_g_h
    _ <= Real.sqrt ((1 + eps) ^ (r + (s + 1))) *
            Real.sqrt
              ((Fintype.card (Fin r -> Idx) : Real) *
                ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
                  (connActApproxBound (Idx := Idx) eps r s
                    (Real.sqrt
                      (Tensor0SBundle.normSqRS
                        (I := I) (g := h) (x := x) r s T))) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hdiff_h (Real.sqrt_nonneg _)
    _ <= nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T := by
          exact mul_le_mul_of_nonneg_left hdiff_h_g (Real.sqrt_nonneg _)

set_option maxHeartbeats 2000000 in
/-- F3d, order-one book-form norm inequality.

This is the algebraic assembly of the `p = 1` case of MSM135 Chapter 4,
Lemma "Norms of covariant derivatives of tensors, I": triangle inequality in
the `g` norm, the component estimate packaged by
`nablaRS_norm_le_approx_comps`, and the mixed-tensor norm comparison under the
`C^0` part of the approximate-isometry hypothesis.  The component hypothesis is
kept explicit so callers can supply it from `nablaRS_component_le_approx` with
their chosen local frame data. -/
theorem nablaRS_one_le_approx_comps
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (nablaH nablaG : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    (hcomp : NablaDiffCompBound
      (I := I) (h := h) (Idx := Idx) eps basis T
      (Tensor0SBundle.metricSubRS
        (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG)) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) nablaG) <=
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) nablaH) +
        nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T := by
  have htri :=
    Tensor0SBundle.sqrt_normRS_le_add_metricSub
      (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG
  have hdiff_g_bound :
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (Tensor0SBundle.metricSubRS
            (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG)) <=
        nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T :=
    nablaRSOneError_of_comps
      (I := I) Happrox hx basis hinv T
      (Tensor0SBundle.metricSubRS
        (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG) hcomp
  exact htri.trans (add_le_add_right hdiff_g_bound _)

end FixedDomain

end HCGCompactness
end RicciFlower
