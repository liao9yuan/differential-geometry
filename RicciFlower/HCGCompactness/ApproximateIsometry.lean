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

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- Supplied-metric `(eps,p)` approximate isometry data on a set `K`.

The `C^0` part is the uniform metric equivalence with constant `1 + eps`.
Higher-order smallness is stated using the fixed-background covariant derivative
norms from `AllTimesBounds`; order `0` is intentionally represented by the
metric-equivalence field. -/
structure IsApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  uniform_equiv : MetricUniformEquivalentOn (I := I) K g h (1 + eps)
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        metricCovDerivNorm (I := I) a h g x <= eps

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
