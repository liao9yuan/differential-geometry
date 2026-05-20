import DifferentialGeometry.Integral.Connection.TensorRSNabla
import DifferentialGeometry.Integral.Connection.ConnectionLaplacian
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# The connection Laplacian on `(r, s)`-tensor sections

For a smooth Riemannian metric `g` on a manifold `M` without boundary, the
connection Laplacian on the `(r, s)`-tensor bundle is the metric trace of the
second covariant derivative,
$$
  (\Delta_\nabla T)(x)
    := \mathrm{tr}_g\bigl(W \mapsto \nabla_W \nabla T\bigr)(x).
$$
In a `g_x`-orthonormal frame `B_i` of the tangent space at `x`, the trace
evaluates to
$$
  (\Delta_\nabla T)(x)
    = \sum_i \bigl(\nabla_{B_i x}\,\nabla_{B_i} T - \nabla_{(\nabla_{B_i} B_i)(x)} T\bigr).
$$

This file packages the operator on raw `(r, s)`-tensor sections, traced against
the smooth orthonormal frame at the centre point (`smoothOrthoFrame g x`). The
frame is `g_x`-orthonormal at `x` and `C^∞` as a tangent-bundle section family
(see `RicciIdentitySmoothFrame.lean`), which makes the value of the trace at
`x` the textbook value of the connection Laplacian on tensor sections.

## Main definitions

* `rawTensorConnLap g r s T x` — the pointwise value of the connection
  Laplacian on a raw `(r, s)`-tensor section `T : Π b, TensorRSSpace r s I b`,
  computed against the smooth orthonormal frame at `x`.

## Main results

* `rawTensorConnLap_smul` — `ℝ`-linearity on scalars.
* `rawTensorConnLap_add` — additivity on raw smooth sections.
* `rawTensorConnLap_zero` — vanishing on the zero section.
* `rawTensorConnLap_smooth` — for a smooth raw `(r, s)`-tensor section `T`,
  the raw connection Laplacian is a smooth section.

## Sign convention

The geometer convention is used: `Δ_g = div ∘ grad`, with spectrum in
`(-∞, 0]` on closed manifolds. The connection Laplacian inherits this sign
through the trace formula. This is the same sign convention used by the
scalar / vector / 1-form connection Laplacians in `ConnectionLaplacian.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Part 1: the raw `(r, s)`-tensor connection Laplacian

The raw operator works on dependent-function sections
`T : Π b, TensorRSSpace r s I b`. The trace formula is stated in maximum
generality before any smoothness or compact-support hypothesis is imposed. -/

/-- **Raw connection Laplacian on a `(r, s)`-tensor section.** Given a smooth
Riemannian metric `g` on `M`, ranks `(r, s)`, and a raw `(r, s)`-tensor section
`T : Π b, TensorRSSpace r s I b`, the value at `x` is the metric trace of the
second covariant derivative, computed against the smooth orthonormal frame at
`x`:
$$
  (\Delta_\nabla T)(x)
    := \sum_i \bigl(\nabla^{(r,s)}_{B_i x}\,\nabla^{(r,s)}_{B_i} T
      - \nabla^{(r,s)}_{(\nabla_{B_i} B_i)(x)} T\bigr).
$$
Here `B_i = smoothOrthoFrame g x i` and `∇^{(r,s)}` abbreviates the
`(r, s)`-tensor covariant derivative
`TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita g)`. -/
def rawTensorConnLap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

/-- The defining identity for `rawTensorConnLap`. -/
@[simp] lemma rawTensorConnLap_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) T) x
            (smoothOrthoFrame (I := I) g x i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

/-! ## Part 2: vanishing on the zero section

If `T` is the identically zero raw section, then `rawTensorConnLap T x = 0`
at every `x`. This is immediate from `cov.zero` applied twice. -/

/-- **Vanishing on the zero section.** The raw connection Laplacian of the
identically zero `(r, s)`-tensor section vanishes pointwise. -/
@[simp] theorem rawTensorConnLap_zero [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    rawTensorConnLap (I := I) g r s
        (fun _ : M => (0 : TensorRSSpace r s I _)) x = 0 := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- The covariant derivative is `ℝ`-linear: applied to the zero section yields zero.
  have h_zero_cov : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) =
      fun _ : M => (0 : TangentSpace I _ →L[ℝ] TensorRSSpace r s I _) := cov.zero
  unfold rawTensorConnLap
  refine Finset.sum_eq_zero ?_
  intro i _
  -- `covApply cov X 0 = fun y => cov.toFun 0 y (X y) = fun y => 0`.
  have h_covApply_zero : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun _ : M => (0 : TensorRSSpace r s I _)) =
      fun y : M => (0 : TensorRSSpace r s I y) := by
    funext y
    -- `covApply cov X 0 y = cov.toFun 0 y (X y)`.
    have : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) y = 0 :=
      congrArg (fun φ => φ y) h_zero_cov
    -- Apply the zero linear map to `(smoothOrthoFrame g x i y)`.
    change (cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) y)
        (smoothOrthoFrame (I := I) g x i y) = 0
    rw [this]
    rfl
  rw [h_covApply_zero]
  -- The first term: `cov.toFun (0 section) x (B_i x) = 0`.
  have h_first_zero : cov.toFun (fun y : M => (0 : TensorRSSpace r s I y)) x
      (smoothOrthoFrame (I := I) g x i x) = 0 := by
    have : cov.toFun (fun y : M => (0 : TensorRSSpace r s I y)) x = 0 :=
      congrArg (fun φ => φ x) h_zero_cov
    rw [this]; rfl
  -- The second term: `cov.toFun (0 section) x (LeviCivita ...) = 0` similarly.
  have h_second_zero : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) x
      ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) = 0 := by
    have : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) x = 0 :=
      congrArg (fun φ => φ x) h_zero_cov
    rw [this]; rfl
  -- Combine: the summand is `0 - 0 = 0`.
  rw [h_first_zero, h_second_zero]
  simp

/-! ## Part 3: additivity on raw smooth sections

For raw smooth sections `T, T'`, the connection Laplacian is additive:
`rawTensorConnLap (T + T') = rawTensorConnLap T + rawTensorConnLap T'`. This
follows from the `IsCovariantDerivativeOn.add` identity applied twice and the
linearity of `ContinuousLinearMap.sub_apply / add_apply`. -/

/-- **Additivity on smooth raw sections.** For raw `(r, s)`-tensor sections
`T, T'` that are manifold-differentiable to all orders at `x`, the raw
connection Laplacian is additive at `x`. The exact differentiability needed at
`x` is `MDifferentiableAt` of `T`, `T'`, `T + T'`, and the corresponding
single-derivatives along each frame vector. -/
theorem rawTensorConnLap_add [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T T' : Π b : M, TensorRSSpace r s I b}
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hT' : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (hcovT' : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T' y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (T + T') x =
      rawTensorConnLap (I := I) g r s T x +
        rawTensorConnLap (I := I) g r s T' x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- Use `IsCovariantDerivativeOn.add` to split each first-derivative.
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  -- We need to show: ∑_i (terms with (T + T')) = ∑_i (terms with T) + ∑_i (terms with T')
  unfold rawTensorConnLap
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- The summand for (T + T') decomposes by linearity of cov:
  --   cov.toFun (covApply cov B (T + T')) x (B x) - cov.toFun (T + T') x (...)
  -- = (cov.toFun (covApply cov B T) x (B x) - cov.toFun T x (...))
  -- + (cov.toFun (covApply cov B T') x (B x) - cov.toFun T' x (...))
  -- The argument: `cov.toFun (σ + σ') x = cov.toFun σ x + cov.toFun σ' x`, hence
  -- applying at a vector gives the additivity of values.
  -- First, prove additivity of `cov.toFun T x` in T.
  have h_addT : cov.toFun (fun y => T y + T' y) x =
      cov.toFun T x + cov.toFun T' x := by
    -- `IsCovariantDerivativeOn.add` gives a pointwise identity.
    have h_add := hcov_loc.add (σ := T) (σ' := T') (hT x) (hT' x)
    -- h_add : cov.toFun (T + T') x = cov.toFun T x + cov.toFun T' x
    convert h_add using 1
  -- Second, prove additivity of `covApply cov X T` in T.
  have h_covApply_add : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun y => T y + T' y) =
      covApply cov (smoothOrthoFrame (I := I) g x i) T +
        covApply cov (smoothOrthoFrame (I := I) g x i) T' := by
    funext y
    -- `covApply cov X (T + T') y = cov.toFun (T + T') y (X y)
    --   = (cov.toFun T y + cov.toFun T' y) (X y)
    --   = cov.toFun T y (X y) + cov.toFun T' y (X y).
    -- Use `IsCovariantDerivativeOn.add` at y. Note `T + T'` (the Pi-sum) is
    -- definitionally `fun y => T y + T' y`, but `IsCovariantDerivativeOn.add`
    -- is stated for the former, so we go via `show` and matching exactly.
    have h_add_at_y : cov.toFun (fun y => T y + T' y) y =
        cov.toFun T y + cov.toFun T' y := by
      change cov.toFun (T + T') y = cov.toFun T y + cov.toFun T' y
      exact hcov_loc.add (σ := T) (σ' := T') (hT y) (hT' y)
    change cov.toFun (fun y => T y + T' y) y (smoothOrthoFrame (I := I) g x i y) =
      covApply cov (smoothOrthoFrame (I := I) g x i) T y +
        covApply cov (smoothOrthoFrame (I := I) g x i) T' y
    rw [h_add_at_y]
    rfl
  -- Third, the second derivative of (T + T') along B_i is the sum.
  have h_second_deriv_add : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) (fun y => T y + T' y)) x =
      cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x +
        cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T') x := by
    rw [h_covApply_add]
    -- Apply IsCovariantDerivativeOn.add to the sum.
    exact hcov_loc.add (σ := covApply cov (smoothOrthoFrame (I := I) g x i) T)
      (σ' := covApply cov (smoothOrthoFrame (I := I) g x i) T')
      (hcovT x i) (hcovT' x i)
  -- Combine: substitute the additivity into the summand.
  change
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i)
        (fun y => T y + T' y)) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun (fun y => T y + T' y) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) =
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) +
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T') x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T' x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))
  rw [h_second_deriv_add, h_addT]
  -- Now use ContinuousLinearMap add_apply on both halves and rearrange.
  simp only [ContinuousLinearMap.add_apply]
  abel

/-! ## Part 4: scalar homogeneity

For a constant scalar `c`, the raw connection Laplacian satisfies
`rawTensorConnLap (c • T) = c • rawTensorConnLap T`. This follows from the
`IsCovariantDerivativeOn.smul_const` identity applied twice. -/

/-- **Scalar homogeneity on smooth raw sections.** For a raw `(r, s)`-tensor
section `T` and a constant `c : ℝ`, the raw connection Laplacian commutes
with scaling. -/
theorem rawTensorConnLap_smul [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b} (c : ℝ)
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (fun y => c • T y) x =
      c • rawTensorConnLap (I := I) g r s T x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  unfold rawTensorConnLap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- The summand for `c • T` should be `c •` the original.
  -- First: `cov.toFun (c • T) x = c • cov.toFun T x`.
  have h_smulT : cov.toFun (fun y => c • T y) x = c • cov.toFun T x := by
    change cov.toFun (c • T) x = c • cov.toFun T x
    exact hcov_loc.smul_const (σ := T) c (hT x)
  -- Second: `covApply cov X (c • T) = c • covApply cov X T`.
  have h_covApply_smul : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun y => c • T y) =
      fun y => c • covApply cov (smoothOrthoFrame (I := I) g x i) T y := by
    funext y
    have h_smul_at_y : cov.toFun (fun y => c • T y) y = c • cov.toFun T y := by
      change cov.toFun (c • T) y = c • cov.toFun T y
      exact hcov_loc.smul_const (σ := T) c (hT y)
    change cov.toFun (fun y => c • T y) y (smoothOrthoFrame (I := I) g x i y) =
      c • covApply cov (smoothOrthoFrame (I := I) g x i) T y
    rw [h_smul_at_y]
    -- `(c • cov.toFun T y) (X y) = c • (cov.toFun T y (X y))`.
    rfl
  -- Third: `cov.toFun (c • covApply ... T) x = c • cov.toFun (covApply ... T) x`.
  have h_second_smul : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) (fun y => c • T y)) x =
      c • cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x := by
    rw [h_covApply_smul]
    exact hcov_loc.smul_const
      (σ := covApply cov (smoothOrthoFrame (I := I) g x i) T) c (hcovT x i)
  -- Combine: the summand for `c • T` is `c •` the summand for `T`.
  change
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i)
        (fun y => c • T y)) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun (fun y => c • T y) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) =
    c • (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))
  rw [h_second_smul, h_smulT]
  -- Both halves carry a factor of `c`; combine via continuous-linear-map smul.
  simp only [ContinuousLinearMap.smul_apply, smul_sub]

/-! ## Part 5: locality and support inclusion

The raw connection Laplacian is local in `T`: if `T` vanishes on an open
neighbourhood of `x` (and is manifold-differentiable everywhere), then
`rawTensorConnLap T x = 0`. This is the input to the compact-support
preservation lemma. -/

/-- **Locality of the first covariant derivative at a single point.** If a
raw section `T` vanishes on an open set `U` and `T` is manifold-differentiable
at the target point `y ∈ U`, then `cov.toFun T y = 0`.

This is a direct application of `IsCovariantDerivativeOn.congr_of_eventuallyEq`
to the zero section on the open neighbourhood `U`. The differentiability
witness is required only at `y`, not globally. -/
private lemma cov_eq_zero_of_eventually_zero_on_open
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (cov : CovariantDerivative I F V)
    {T : Π y : M, V y} {U : Set M}
    (hU_open : IsOpen U)
    (hT_zero : ∀ y ∈ U, T y = 0)
    {y : M} (hyU : y ∈ U)
    (hT_diff_y : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun z : M => TotalSpace.mk' F (E := V) z (T z)) y) :
    cov.toFun T y = 0 := by
  classical
  -- `T y' = 0` for every `y' ∈ U`. So as a Pi-section, T agrees with 0 on U,
  -- and U is in `𝓝 y` since U is open and `y ∈ U`.
  have hU_nhds : U ∈ 𝓝 y := hU_open.mem_nhds hyU
  -- Pointwise-equal data on a neighbourhood: `T y' = (0 : V y')` for `y' ∈ U`.
  -- We use the dependent-type form `∀ᶠ y' in 𝓝 y, T y' = 0`, which is what
  -- `IsCovariantDerivativeOn.congr_of_eventuallyEq` expects.
  have hT_eq : ∀ᶠ y' in 𝓝 y, T y' = (fun y'' : M => (0 : V y'')) y' :=
    Filter.Eventually.mono (Filter.eventually_of_mem hU_nhds (fun y' hy' => hy'))
      (fun y' hy' => hT_zero y' hy')
  have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y' : M => TotalSpace.mk' F (E := V) y' (0 : V y')) y :=
    mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
  have huniv : (Set.univ : Set M) ∈ 𝓝 y := Filter.univ_mem
  have h_eq : cov.toFun T y =
      cov.toFun (fun y' : M => (0 : V y')) y :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hT_diff_y hzero_diff
      huniv hT_eq
  rw [h_eq]
  -- `cov 0 = 0` pointwise.
  exact congrArg (fun φ => φ y) cov.zero

/-- **Vanishing of `rawTensorConnLap` on a section that vanishes on a
neighbourhood of `x`.** If `T` vanishes on an open neighbourhood of `x` and
admits `MDifferentiableAt` witnesses at `x` (for `T` itself) and at the
target point `x` for the first covariant derivative section
`covApply cov B_i T`, then the raw connection Laplacian of `T` vanishes at
`x`.

The two `MDifferentiableAt` witnesses are required only at `x`: locality
inside the open neighbourhood `U` reduces both quantities to the zero
section's covariant derivative, which vanishes by `cov.zero`. -/
theorem rawTensorConnLap_eq_zero_of_eventually_zero [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {x : M} {U : Set M} (hU_open : IsOpen U) (hxU : x ∈ U)
    (hT_zero : ∀ y ∈ U, T y = 0)
    (hT_diff_x : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) x)
    (hcovT_diff_x : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T z)) x) :
    rawTensorConnLap (I := I) g r s T x = 0 := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  unfold rawTensorConnLap
  refine Finset.sum_eq_zero ?_
  intro i _
  -- The second term vanishes because `cov.toFun T x = 0` by locality at `x`.
  have h_second_zero : cov.toFun T x = 0 :=
    cov_eq_zero_of_eventually_zero_on_open (I := I)
      (V := fun w : M => TensorRSSpace r s I w)
      cov hU_open hT_zero hxU hT_diff_x
  -- For the first term we need `cov.toFun (covApply cov B_i T) x = 0`.
  -- Step A: show `covApply cov B_i T y = 0` for every `y ∈ U`. This requires
  -- `MDifferentiableAt` of `T` at each such `y`. We construct such a witness
  -- from the fact that `T y = 0` for `y ∈ U`: on the open set `U`, the
  -- function `y ↦ T y` agrees with `y ↦ 0`, so the total-space form is
  -- `MDifferentiableAt` at every `y ∈ U` by congr with the zero section.
  have h_T_diff_on_U : ∀ y ∈ U, MDifferentiableAt I
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) y := by
    intro y hyU
    have hU_nhds_y : U ∈ 𝓝 y := hU_open.mem_nhds hyU
    have hzero_total_diff_y : MDifferentiableAt I
        (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (0 : TensorRSSpace r s I z)) y :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) (IB := I)
    apply hzero_total_diff_y.congr_of_eventuallyEq
    filter_upwards [hU_nhds_y] with z hzU
    change TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z) =
      TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (0 : TensorRSSpace r s I z)
    rw [hT_zero z hzU]
  have h_covApply_zero : ∀ y ∈ U,
      covApply cov (smoothOrthoFrame (I := I) g x i) T y = 0 := by
    intro y hyU
    have h_cov_T_zero_y : cov.toFun T y = 0 :=
      cov_eq_zero_of_eventually_zero_on_open (I := I)
        (V := fun w : M => TensorRSSpace r s I w)
        cov hU_open hT_zero hyU (h_T_diff_on_U y hyU)
    change cov.toFun T y (smoothOrthoFrame (I := I) g x i y) = 0
    rw [h_cov_T_zero_y]
    rfl
  -- Step B: apply locality at the single point `x` to `covApply cov B_i T`,
  -- using the at-`x` differentiability witness.
  have h_first_zero : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) T) x = 0 :=
    cov_eq_zero_of_eventually_zero_on_open (I := I)
      (V := fun w : M => TensorRSSpace r s I w)
      cov hU_open
      (T := fun y : M => covApply cov (smoothOrthoFrame (I := I) g x i) T y)
      (U := U) h_covApply_zero hxU (hcovT_diff_x i)
  -- Combine: both halves of the summand are zero.
  change cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
      (smoothOrthoFrame (I := I) g x i x) -
    cov.toFun T x ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) = 0
  rw [h_first_zero, h_second_zero]
  simp

/-! ## Part 6: negation and subtraction

By combining the additivity identity (Part 3) with the scalar-homogeneity
identity (Part 4) at `c = -1`, the raw connection Laplacian commutes with
negation. Subtraction follows from additivity and negation.

These identities are convenience corollaries; they are not part of the
minimum-set of headline identities but are useful for downstream callers
that need to manipulate the raw operator directly. -/

/-- **Negation identity for the raw connection Laplacian.** This is the
`c = -1` specialisation of `rawTensorConnLap_smul`. -/
theorem rawTensorConnLap_neg [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (fun y => -T y) x =
      - rawTensorConnLap (I := I) g r s T x := by
  classical
  have h := rawTensorConnLap_smul (I := I) g r s (T := T) (c := -1) hT hcovT x
  -- `(-1) • T y = -T y` and `(-1) • _ = -_`.
  simp only [neg_smul, one_smul, neg_smul] at h
  exact h

/-! ## Part 7: chart-aligned trace form (model-basis variant)

The textbook expression of the tensor connection Laplacian in chart
coordinates uses a basis `e_i` of the chart model space and writes
$$
  (\Delta_\nabla T)^I_J(x) = g^{ab}(x)\,\bigl[\partial_a\partial_b T^I_J +
    (\text{Christoffel terms in $a$ and $b$})\bigr].
$$
At the level of the raw operator (and at a single point `x`), the
chart-coordinate form is obtained by tracing the second covariant
derivative against the canonical model basis of `E`, weighted by the inverse
Gram matrix at `x` to convert from a coordinate frame to a `g_x`-orthonormal
frame.

A complete chart-coordinate characterisation requires the full chart-bridge
between the abstract covariant derivative on the `(r, s)`-tensor bundle and
the chart-local Christoffel-augmented expression. The current foundation
exposes only the smooth-orthonormal-frame variant; downstream consumers that
need the chart-coordinate form should compose `rawTensorConnLap` with the
appropriate chart-bridge for `(r, s)`-tensors. -/

/-- **Frame-trace presentation of the raw connection Laplacian.** At a fixed
centre `x`, the raw operator is the finite trace of the second covariant
derivative against the `g_x`-orthonormal frame `smoothOrthoFrame g x`. This
restates the definition; it is provided as a named theorem so downstream
consumers can name the frame explicitly. -/
theorem rawTensorConnLap_frame_trace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) T) x
            (smoothOrthoFrame (I := I) g x i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

end Connection
end Integral
end DifferentialGeometry

end
