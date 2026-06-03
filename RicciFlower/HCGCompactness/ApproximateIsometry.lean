import RicciFlower.HCGCompactness.AllTimesBounds
import RicciFlower.Metric.Pullback
import RicciFlower.Tensor.RSTensor.QuadraticBounds.Unit
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceAction
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceActionIdentity
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

It also records a book-facing map-level interface for MSM135 Definition 4.1.
That interface is deliberately separate from the same-domain comparison
predicate below: for a general smooth map `Phi`, the pullback of a metric is a
smooth `(0,2)` tensor field, not a Riemannian metric a priori.
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

section MapLevel

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]

/-- Concrete pullback metric tensor data for a smooth map.

For a general smooth map this is not packaged as a Riemannian metric: it is the
actual covariant `(0,2)` tensor whose value is
`h_{Phi x}(d Phi_x -, d Phi_x -)`.  The smooth tensor field is supplied as data,
and the formula field pins it to the map. -/
structure PullbackMetricTensorData
    (Phi : M -> N) (h : SmoothRiemannianMetric I N) where
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))

/-- The pointwise norm of the metric-error tensor `A - g`, measured by `g`. -/
noncomputable def metricTensorErrorNorm
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) g x 2
      (A x - Tensor0SBundle.metricTensorField (I := I) g x))

/-- Generic iterated covariant derivatives of a smooth `(0,2)` tensor field,
using the Levi-Civita connection of the reference metric.  This is the
tensor-field version of `metricCovDeriv`; it is needed because `Phi^* h` is not
necessarily a Riemannian metric for a general smooth map. -/
noncomputable def tensor02CovDeriv
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    A
    (fun a Aprev =>
      metricCovDerivStep (I := I) gRef a Aprev)

/-- Pointwise norm `|nabla_cov^a A|_norm` for a smooth `(0,2)` tensor field. -/
noncomputable def tensor02CovDerivNormWith
    (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (cov norm : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) norm x (a + 2)
      (tensor02CovDeriv (I := I) A cov a x))

/-- MSM135 Definition 4.1, localized to a set `K`: data for an `(eps,p)`
pre-approximate isometry is a smooth map whose actual pullback metric tensor is
`C^p`-close to the source metric. -/
structure PreApproxIsometryData
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smooth : ContMDiff I I (∞ : WithTop ℕ∞) Phi
  pullbackData : PullbackMetricTensorData (I := I) Phi h
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullbackData.pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullbackData.pullback g g x <= eps

/-- MSM135 Definition 4.1, localized two-sided data for diffeomorphisms.

The forward field is the pre-approximate isometry on the source set.  The
reverse field is the same condition for the inverse map on the target set. -/
structure BookApproxIsometryData
    (K : Set M) (L : Set N) (eps : Real) (p : Nat)
    (Phi : M ≃ₘ⟮I, I⟯ N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  forward : PreApproxIsometryData (I := I) K eps p (Phi : M -> N) g h
  reverse : PreApproxIsometryData (I := I) L eps p (Phi.symm : N -> M) h g

/-- The metric tensor evaluates to the Riemannian quadratic form. -/
private theorem quad02_metricTensorField
    (g : SmoothRiemannianMetric I M) {x : M} (v : TangentSpace I x) :
    quad02 (I := I) (M := M)
      (Tensor0SBundle.metricTensorField (I := I) g x) v =
      g.inner x v v := by
  simp [quad02, Tensor0SBundle.metricTensorField_apply]

/-- A small `(0,2)` metric-error tensor gives a small quadratic error. -/
theorem preApprox_quad_error_abs_le
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : PreApproxIsometryData (I := I) K eps p Phi g h)
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    |quad02 (I := I) (M := M)
        (H.pullbackData.pullback x -
          Tensor0SBundle.metricTensorField (I := I) g x) v| <=
      eps * g.inner x v v := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by simp)
  have hcs :=
    abs_quad02_le_norm (I := I) (M := M) g
      (H.pullbackData.pullback x -
        Tensor0SBundle.metricTensorField (I := I) g x) v
  have hsmall :
      metricTensorErrorNorm (I := I) H.pullbackData.pullback g x <= eps :=
    H.c0_small x hx
  have hquad_nonneg : 0 <= g.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt (g.pos x v hv)
  calc
    |quad02 (I := I) (M := M)
        (H.pullbackData.pullback x -
          Tensor0SBundle.metricTensorField (I := I) g x) v|
        <= Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) g x 2
              (H.pullbackData.pullback x -
                Tensor0SBundle.metricTensorField (I := I) g x)) *
            g.inner x v v := hcs
    _ <= eps * g.inner x v v :=
        mul_le_mul_of_nonneg_right
          (by simpa [metricTensorErrorNorm] using hsmall) hquad_nonneg

/-- MSM135 Proposition 4.2, pre-approximate direction: the `C^0` tensor error
bound implies the upper quadratic-form bound for the actual pullback tensor. -/
theorem preApprox_quad_upper
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : PreApproxIsometryData (I := I) K eps p Phi g h)
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) (H.pullbackData.pullback x) v <=
      (1 + eps) * g.inner x v v := by
  let A := H.pullbackData.pullback x
  let G := Tensor0SBundle.metricTensorField (I := I) g x
  have herr :
      |quad02 (I := I) (M := M) (A - G) v| <=
        eps * g.inner x v v :=
    preApprox_quad_error_abs_le (I := I) H hx v
  have herr_upper :
      quad02 (I := I) (M := M) (A - G) v <=
        eps * g.inner x v v :=
    le_trans (le_abs_self _) herr
  have hmetric :
      quad02 (I := I) (M := M) G v = g.inner x v v :=
    quad02_metricTensorField (I := I) g v
  have hdiff :
      quad02 (I := I) (M := M) (A - G) v =
        quad02 (I := I) (M := M) A v - g.inner x v v := by
    simp [quad02, G, ContinuousMultilinearMap.sub_apply]
  have hsum :
      quad02 (I := I) (M := M) A v =
        quad02 (I := I) (M := M) (A - G) v + g.inner x v v := by
    linarith
  calc
    quad02 (I := I) (M := M) A v
        = quad02 (I := I) (M := M) (A - G) v + g.inner x v v := hsum
    _ <= eps * g.inner x v v + g.inner x v v :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right herr_upper (g.inner x v v)
    _ = (1 + eps) * g.inner x v v := by ring

private theorem mfderiv_symm_apply_mfderiv
    (Phi : M ≃ₘ⟮I, I⟯ N) (x : M) (v : TangentSpace I x) :
    mfderiv I I (Phi.symm : N -> M) (Phi x)
        (mfderiv I I (Phi : M -> N) x v) = v := by
  have hsymm_diff : MDifferentiableAt I I (Phi.symm : N -> M) (Phi x) :=
    Phi.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hPhi_diff : MDifferentiableAt I I (Phi : M -> N) x :=
    Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (g := (Phi.symm : N -> M)) (f := (Phi : M -> N))
      (x := x) hsymm_diff hPhi_diff v
  have hid :
      (fun y : M => Phi.symm (Phi y)) = fun y : M => y := by
    funext y
    exact Diffeomorph.symm_apply_apply Phi y
  have hleft :
      mfderiv I I (fun y : M => Phi.symm (Phi y)) x v = v := by
    rw [hid]
    change (mfderiv I I (@id M) x) v = v
    rw [mfderiv_id]
    rfl
  have hcomp' :
      mfderiv I I (fun y : M => Phi.symm (Phi y)) x v =
        mfderiv I I (Phi.symm : N -> M) (Phi x)
          (mfderiv I I (Phi : M -> N) x v) := by
    simpa [Function.comp_def] using hcomp
  exact hcomp'.symm.trans hleft

/-- MSM135 Proposition 4.2, two-sided approximate-isometry form.  The first
inequality comes from the forward pre-approximate condition, and the second
from the inverse pre-approximate condition evaluated at `Phi x`. -/
theorem bookApprox_quad_twoSided
    {K : Set M} {L : Set N} {eps : Real} {p : Nat}
    {Phi : M ≃ₘ⟮I, I⟯ N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : BookApproxIsometryData (I := I) K L eps p Phi g h)
    (hMapsTo : Set.MapsTo (Phi : M -> N) K L)
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    (1 + eps)⁻¹ *
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v <=
      g.inner x v v ∧
    g.inner x v v <=
      (1 + eps) *
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v := by
  have hCpos : 0 < 1 + eps := by linarith [H.forward.eps_pos]
  have hforward :=
    preApprox_quad_upper (I := I) H.forward hx v
  have hleft :
      (1 + eps)⁻¹ *
          quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v <=
        g.inner x v v := by
    rwa [inv_mul_le_iff₀ hCpos]
  let w : TangentSpace I (Phi x) :=
    mfderiv I I (Phi : M -> N) x v
  have hrev :=
    preApprox_quad_upper (I := I) H.reverse (hMapsTo hx) w
  have hrev_eval :
      quad02 (I := I) (M := N) (H.reverse.pullbackData.pullback (Phi x)) w =
        g.inner x v v := by
    have happly :=
      H.reverse.pullbackData.pullback_apply (Phi x)
        (fun _ : Fin 2 => w)
    have hmw :
        mfderiv I I (Phi.symm : N -> M) (Phi x) w = v := by
      simpa [w] using mfderiv_symm_apply_mfderiv (I := I) Phi x v
    have hpoint : Phi.symm (Phi x) = x :=
      Diffeomorph.symm_apply_apply Phi x
    rw [hpoint] at hmw happly
    rw [hmw] at happly
    simpa [quad02] using happly
  have hforward_eval :
      h.inner (Phi x) w w =
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v := by
    have happly :=
      H.forward.pullbackData.pullback_apply x (fun _ : Fin 2 => v)
    simpa [quad02, w] using happly.symm
  have hright :
      g.inner x v v <=
        (1 + eps) *
          quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v := by
    simpa [hrev_eval, hforward_eval] using hrev
  exact ⟨hleft, hright⟩

/-- Same-domain packaging of MSM135 Proposition 4.2 when the pullback tensor is
already supplied as a Riemannian metric `gh` on the source.  This adapter does
not construct a pullback metric; it only transfers the checked quadratic-form
estimate to the existing `MetricUniformEquivalentOn` API. -/
theorem bookApprox_uniformEquiv_of_pullback
    {K : Set M} {L : Set N} {eps : Real} {p : Nat}
    {Phi : M ≃ₘ⟮I, I⟯ N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : BookApproxIsometryData (I := I) K L eps p Phi g h)
    (hMapsTo : Set.MapsTo (Phi : M -> N) K L)
    (gh : SmoothRiemannianMetric I M)
    (hgh : forall x : M, x ∈ K -> forall v : TangentSpace I x,
      gh.inner x v v =
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v) :
    MetricUniformEquivalentOn (I := I) K g gh (1 + eps) := by
  have hCpos : 0 < 1 + eps := by linarith [H.forward.eps_pos]
  refine ⟨?_, ?_⟩
  · linarith [H.forward.eps_pos]
  · intro x hx v
    have htwo :=
      bookApprox_quad_twoSided (I := I) H hMapsTo hx v
    have hupper_raw :=
      preApprox_quad_upper (I := I) H.forward hx v
    constructor
    · rw [inv_mul_le_iff₀ hCpos]
      simpa [hgh x hx v] using htwo.2
    · simpa [hgh x hx v] using hupper_raw

end MapLevel

/-- Supplied-metric `(eps,p)` comparison data on a set `K`.

The `C^0` part is the uniform metric equivalence with constant `1 + eps`.
Higher-order smallness is stated using the fixed-background covariant derivative
norms from `AllTimesBounds`; order `0` is intentionally represented by the
metric-equivalence field.

This is a same-domain comparison predicate for a supplied pullback metric.  It
is not MSM135 Definition 4.1; it is the consumer-side form obtained after the
map-level pullback metric has already been constructed and its `C^0` tensor
error has been converted into vector metric equivalence.  Higher-order F3
estimates use `IsTwoSidedApproxIsometryOn`, which also records the inverse-side
derivative smallness. -/
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

section BookTensorNorms

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]

/-- MSM135 Corollary "Norms of tensors", in the supplied-pullback-metric
form.  If a Riemannian metric `gh` on the source has the same quadratic form
as the pullback tensor `Phi^* h` on `K`, then an `(eps,0)` approximate isometry
compares mixed-tensor norms with the expected factor. -/
theorem bookNormRS_compare
    {K : Set M} {L : Set N} {eps : Real}
    {Phi : M ≃ₘ⟮I, I⟯ N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : BookApproxIsometryData (I := I) K L eps 0 Phi g h)
    (hMapsTo : Set.MapsTo (Phi : M -> N) K L)
    (gh : SmoothRiemannianMetric I M)
    (hgh : forall x : M, x ∈ K -> forall v : TangentSpace I x,
      gh.inner x v v =
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v)
    {x : M} (hx : x ∈ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    Tensor0SBundle.normRS (I := I) (g := gh) (x := x) r s T <=
        Real.sqrt ((1 + eps) ^ (r + s)) *
          Tensor0SBundle.normRS (I := I) (g := g) (x := x) r s T /\
      Tensor0SBundle.normRS (I := I) (g := g) (x := x) r s T <=
        Real.sqrt ((1 + eps) ^ (r + s)) *
          Tensor0SBundle.normRS (I := I) (g := gh) (x := x) r s T := by
  have hEq :
      MetricUniformEquivalentOn (I := I) K g gh (1 + eps) :=
    bookApprox_uniformEquiv_of_pullback (I := I) H hMapsTo gh hgh
  constructor
  · simpa [Tensor0SBundle.normRS_eq_sqrt_normSqRS]
      using Tensor0SBundle.sqrt_normRS_upper_le_of_equiv
        (I := I) g gh x r s hEq.1 (hEq.2 x hx) T
  · simpa [Tensor0SBundle.normRS_eq_sqrt_normSqRS]
      using Tensor0SBundle.sqrt_normRS_lower_le_of_equiv
        (I := I) g gh x r s hEq.1 (hEq.2 x hx) T

end BookTensorNorms

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

/-- Book-facing F3-hi epsilon control for a realized `k`-th `h`-covariant
derivative of `Gamma_g - Gamma_h`.  The constant is independent of `eps`; this
is the shape consumed in MSM135 Chapter 4, Lemma "Norms of covariant derivatives
of tensors, I". -/
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

/-- Total-derivative `p = 1` form of MSM135 Lemma "Norms of covariant
derivatives of tensors, I".

This is the checked base case in the natural total-covariant-derivative
language: supplied realizations of `nabla_h T` and `nabla_g T` satisfy the
book estimate with the zero-order connection-difference epsilon bound.  The
remaining higher-order Lemma 4.5 work is the iterated product-rule realization
for repeated `h`-derivatives of the connection-difference action. -/
theorem nablaRS_one_le_approx_total
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x ∈ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisG basisH : Module.Basis Idx Real (TangentSpace I x))
    (hinvG :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basisG (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hinvH :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basisH (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaH nablaG : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hrealH : Tensor0SBundle.TotalNablaRSRealizes
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) T nablaH)
    (hrealG : Tensor0SBundle.TotalNablaRSRealizes
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) T nablaG)
    (β : (y : M) -> Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r y)
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (y : M) -> TangentSpace I y)
    (hX_at : forall i : Idx, Xfield i x = basisG i)
    (hβ_at : forall upper : Fin r -> Idx,
      β x = Tensor0SBundle.basisTensor0S (I := I) basisG upper)
    (hV_at : forall i : Idx, V i x = basisG i)
    (hpairT : forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
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
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (nablaG x)) <=
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (nablaH x)) +
        eps * Tensor0SBundle.connActNormConst (Idx := Idx) r s 12
          (Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s (T x))) := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hA :
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)) <=
        eps * 12 := by
    have hraw :=
      connDiff_le_eps_g
        (I := I) Happrox hx hp heps_lt basisH hinvH
    simpa [mul_comm] using hraw
  exact Tensor0SBundle.totalNablaNorm_bound
    (I := I) (M := M) (Idx := Idx) g
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
    T nablaH nablaG hrealH hrealG β x basisG hinvG Xfield V
    hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord
    heps_nonneg hA le_rfl

end FixedDomain

end HCGCompactness
end RicciFlower
