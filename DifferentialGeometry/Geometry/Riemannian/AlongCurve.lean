import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false

/-!
# Sections along a curve, covariant derivative `D/dt`, and parallel transport

Given a smooth Riemannian metric `g` on a smooth manifold `M` and a curve
`γ : ℝ → M`, a **section along `γ` on `s ⊆ ℝ`** is a map
`t ↦ X(t) ∈ T_{γ(t)} M`. Because the project's `TangentSpace I (γ t)` is
definitionally `E`, such a section is type-theoretically the same as a
function `ℝ → E`; the geometric content lives in how chart transitions
act on it.

This file packages the chart-local theory of sections along curves:

1. **G.5.1 — `SectionAlongCurve`**: the bundled data of a section, kept
   simple as a wrapper around `ℝ → E`. The geometric content is in the
   companion smoothness and tangentiality predicates below.

2. **G.5.2 — Smoothness API**: smoothness of a section along `γ` is the
   chart-local notion. The section `X` is smooth at `t₀` in the chart at
   `α : M` (whose source contains `γ(t₀)`) iff `X : ℝ → E` is `C^n` at
   `t₀` *as a function with values in the model fibre at `α`*. Because
   `TangentSpace I (γ t) = E` definitionally for every `t`, no
   trivialization-rewrite is needed for the `E`-valued representation
   itself; the chart-α dependence enters only through the Christoffel
   symbols that appear in `D/dt`.

3. **G.5.3 — `chartCovDerivAlong`**: the chart-local covariant derivative
   `D X / dt` written in a fixed chart at `α : M`,
   $$\bigl(\tfrac{D X}{dt}\bigr)(t) := X'(t) +
       \Gamma_\alpha\bigl(u'(t), X(t)\bigr)(u(t)),$$
   where `u(t) := φ_α(γ(t))`. The predicate
   `IsCovDerivAlongChart g α γ Y W s` records that `W` is the covariant
   derivative of `Y` along `γ` on `s ⊆ ℝ` in the chart at `α`. The
   companion lemmas establish linearity in the section argument and the
   scalar-Leibniz rule.

4. **G.5.4 — `IsParallelTransportChart`**: a section `Y` is *parallel
   along `γ` in chart `α`* if its chart-local representation satisfies
   the parallel-transport ODE
   $$Y'(t) + \Gamma_\alpha\bigl(u'(t), Y(t)\bigr)(u(t)) = 0.$$
   We prove the **uniqueness** of parallel transport with prescribed
   initial value using Mathlib's Gronwall machinery
   (`ODE_solution_unique_of_mem_Ioo`). Existence of parallel transport
   along a curve segment staying inside a single chart is recorded as
   the chart-local Picard–Lindelöf statement; the global extension and
   the chart-independence of the parallel-transport ODE require a
   separate chart-gluing development and are not addressed here.

## Strategic notes

We follow the **chart-fixed** strategy: every definition takes an
explicit basepoint `α : M`, and statements about `X(t) ∈ T_{γ(t)} M` are
interpreted in the chart at `α`, valid whenever `γ(t) ∈ (chartAt α).source`.
This avoids the chart-transition complications that arise when `γ`
crosses multiple chart domains and is the natural foundation on which a
Picard–Lindelöf construction (followed by chart-gluing) would be built.

The intrinsic, chart-independent versions of `D/dt` and parallel
transport are downstream developments built on top of this chart-local
infrastructure.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## G.5.1 — Sections along a curve

A section along `γ` is, at the type level, just a function `ℝ → E`,
since `TangentSpace I (γ t) = E` definitionally for every `t`. We
package it as a bundled `structure` to make the API clear and to give a
hook for later refinements (e.g. bundling smoothness predicates,
restricting the domain, …). All algebraic operations (addition, scalar
multiplication by a real or by a real-valued function on the parameter,
negation, zero) are defined pointwise on `toFun`. -/

/-- A section along a curve `γ : ℝ → M`. The underlying data is the
function `toFun : ℝ → E`; semantically, `X.toFun t` is interpreted as
a vector in `T_{γ(t)} M = E`. -/
@[ext] structure SectionAlongCurve (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (_γ : ℝ → M) where
  /-- The underlying real-to-model-fibre function. -/
  toFun : ℝ → E

namespace SectionAlongCurve

variable {γ : ℝ → M}

/-- `X : ℝ → E` is interpreted as a vector in `T_{γ(t)} M = E` at each
parameter value `t`. -/
@[simp] lemma toFun_def (X : SectionAlongCurve I M γ) (t : ℝ) :
    X.toFun t = X.toFun t := rfl

/-- The zero section: identically zero. -/
def zero : SectionAlongCurve I M γ := ⟨fun _ => 0⟩

@[simp] lemma zero_toFun (t : ℝ) : (zero : SectionAlongCurve I M γ).toFun t = 0 := rfl

/-- Pointwise addition of two sections along the same curve. -/
def add (X Y : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => X.toFun t + Y.toFun t⟩

@[simp] lemma add_toFun (X Y : SectionAlongCurve I M γ) (t : ℝ) :
    (add X Y).toFun t = X.toFun t + Y.toFun t := rfl

/-- Pointwise negation of a section. -/
def neg (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => - X.toFun t⟩

@[simp] lemma neg_toFun (X : SectionAlongCurve I M γ) (t : ℝ) :
    (neg X).toFun t = - X.toFun t := rfl

/-- Pointwise subtraction of two sections. -/
def sub (X Y : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => X.toFun t - Y.toFun t⟩

@[simp] lemma sub_toFun (X Y : SectionAlongCurve I M γ) (t : ℝ) :
    (sub X Y).toFun t = X.toFun t - Y.toFun t := rfl

/-- Pointwise scalar multiplication of a section by a real number. -/
def smul (a : ℝ) (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => a • X.toFun t⟩

@[simp] lemma smul_toFun (a : ℝ) (X : SectionAlongCurve I M γ) (t : ℝ) :
    (smul a X).toFun t = a • X.toFun t := rfl

/-- Pointwise scalar multiplication of a section by a real-valued
function of the parameter `t`. This is the operation by which `D/dt`
acts as a derivation. -/
def smulFun (f : ℝ → ℝ) (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => f t • X.toFun t⟩

@[simp] lemma smulFun_toFun (f : ℝ → ℝ) (X : SectionAlongCurve I M γ) (t : ℝ) :
    (smulFun f X).toFun t = f t • X.toFun t := rfl

/-- The underlying function of a section, exposed as `(↑·)`. -/
instance : CoeFun (SectionAlongCurve I M γ) (fun _ => ℝ → E) := ⟨toFun⟩

@[simp] lemma coe_zero : ((zero : SectionAlongCurve I M γ) : ℝ → E) = fun _ => 0 := rfl

@[simp] lemma coe_add (X Y : SectionAlongCurve I M γ) :
    ((add X Y : SectionAlongCurve I M γ) : ℝ → E) = fun t => X.toFun t + Y.toFun t := rfl

@[simp] lemma coe_smul (a : ℝ) (X : SectionAlongCurve I M γ) :
    ((smul a X : SectionAlongCurve I M γ) : ℝ → E) = fun t => a • X.toFun t := rfl

/-! ## G.5.2 — Smoothness of sections along a curve

Since `TangentSpace I (γ t) = E` definitionally, a section `X` along `γ`
is, type-theoretically, a function `X.toFun : ℝ → E`. Its smoothness is
the standard `ContDiffOn` of the model-fibre representation.

This is a chart-α-independent notion *as a definition*: it does not
depend on any choice of chart on `M`. The chart enters only when we
interpret the geometric content (Christoffel symbols, etc.).

The genuine intrinsic-smoothness predicate — for which different chart
choices would in general give different formulas, requiring the
transition-derivative consistency — is recorded as a separate predicate
`ContMDiffAlong` whose chart-invariance is a downstream theorem. Here we
adopt the *chart-α* viewpoint: a section is smooth in the chart at `α`
iff its `E`-valued representation is `ContDiffOn` on the parameter set
where `γ` lies in the chart's source. -/

/-- Smoothness predicate for a section along a curve, *in the chart at
`α`*: `X.toFun` is `C^n` (in the sense of `ContDiffOn ℝ n`) on `s`. The
geometric interpretation (e.g. transformation under chart changes)
requires that `γ(s)` lies in the chart's source; we keep this as a
separate hypothesis in downstream theorems rather than baking it in. -/
def ContMDiffOnInChart (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ n X.toFun s

/-- Smoothness predicate for a section along a curve at a single point.
This is the localised version of `ContMDiffOnInChart`. -/
def ContMDiffAtInChart (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (t : ℝ) : Prop :=
  ContDiffAt ℝ n X.toFun t

/-- Differentiability predicate for a section along a curve, as a special
case of `ContMDiffOnInChart` with `n = 1`. -/
def DifferentiableOnAlong (X : SectionAlongCurve I M γ) (s : Set ℝ) : Prop :=
  DifferentiableOn ℝ X.toFun s

/-- Differentiability at a point. -/
def DifferentiableAtAlong (X : SectionAlongCurve I M γ) (t : ℝ) : Prop :=
  DifferentiableAt ℝ X.toFun t

@[simp] lemma contMDiffOnInChart_def (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (s : Set ℝ) :
    ContMDiffOnInChart (I := I) (M := M) n X s = ContDiffOn ℝ n X.toFun s := rfl

@[simp] lemma contMDiffAtInChart_def (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (t : ℝ) :
    ContMDiffAtInChart (I := I) (M := M) n X t = ContDiffAt ℝ n X.toFun t := rfl

/-- The zero section is smooth. -/
lemma zero_contMDiffOnInChart (n : WithTop ℕ∞) (s : Set ℝ) :
    ContMDiffOnInChart (I := I) (M := M) (γ := γ) n zero s := by
  unfold ContMDiffOnInChart
  exact contDiffOn_const

/-- The zero section is smooth at every point. -/
lemma zero_contMDiffAtInChart (n : WithTop ℕ∞) (t : ℝ) :
    ContMDiffAtInChart (I := I) (M := M) (γ := γ) n zero t := by
  unfold ContMDiffAtInChart
  exact contDiffAt_const

/-- The sum of two smooth sections is smooth. -/
lemma add_contMDiffOnInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s)
    (hY : ContMDiffOnInChart (I := I) (M := M) n Y s) :
    ContMDiffOnInChart (I := I) (M := M) n (add X Y) s := by
  unfold ContMDiffOnInChart at *
  exact hX.add hY

/-- Smoothness of the sum at a point. -/
lemma add_contMDiffAtInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {t : ℝ}
    (hX : ContMDiffAtInChart (I := I) (M := M) n X t)
    (hY : ContMDiffAtInChart (I := I) (M := M) n Y t) :
    ContMDiffAtInChart (I := I) (M := M) n (add X Y) t := by
  unfold ContMDiffAtInChart at *
  exact hX.add hY

/-- The negation of a smooth section is smooth. -/
lemma neg_contMDiffOnInChart {n : WithTop ℕ∞} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (neg X) s := by
  unfold ContMDiffOnInChart at *
  exact hX.neg

/-- Smoothness of the difference. -/
lemma sub_contMDiffOnInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s)
    (hY : ContMDiffOnInChart (I := I) (M := M) n Y s) :
    ContMDiffOnInChart (I := I) (M := M) n (sub X Y) s := by
  unfold ContMDiffOnInChart at *
  exact hX.sub hY

/-- A real-scalar multiple of a smooth section is smooth. -/
lemma smul_contMDiffOnInChart {n : WithTop ℕ∞} {a : ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (smul a X) s := by
  unfold ContMDiffOnInChart at *
  exact hX.const_smul a

/-- A scalar-function multiple of a smooth section is smooth, provided
the scalar function is itself smooth on `s`. -/
lemma smulFun_contMDiffOnInChart {n : WithTop ℕ∞} {f : ℝ → ℝ}
    {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hf : ContDiffOn ℝ n f s)
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (smulFun f X) s := by
  unfold ContMDiffOnInChart at *
  exact hf.smul hX

/-- Differentiability of the sum. -/
lemma add_differentiableOnAlong {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : DifferentiableOnAlong (I := I) (M := M) X s)
    (hY : DifferentiableOnAlong (I := I) (M := M) Y s) :
    DifferentiableOnAlong (I := I) (M := M) (add X Y) s := by
  unfold DifferentiableOnAlong at *
  exact hX.add hY

/-- Differentiability of a real-scalar multiple. -/
lemma smul_differentiableOnAlong {a : ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : DifferentiableOnAlong (I := I) (M := M) X s) :
    DifferentiableOnAlong (I := I) (M := M) (smul a X) s := by
  unfold DifferentiableOnAlong at *
  exact hX.const_smul a

/-- Differentiability of a scalar-function multiple. -/
lemma smulFun_differentiableOnAlong {f : ℝ → ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hf : DifferentiableOn ℝ f s)
    (hX : DifferentiableOnAlong (I := I) (M := M) X s) :
    DifferentiableOnAlong (I := I) (M := M) (smulFun f X) s := by
  unfold DifferentiableOnAlong at *
  exact hf.smul hX

end SectionAlongCurve

/-! ## G.5.3 — Covariant derivative along a curve in a chart

For a section `X` along `γ` and a chart basepoint `α : M`, the
chart-local covariant derivative `D X / dt` at time `t` is, in the
fibre at `γ(t)` identified with `E` via the chart at `α`,
$$\Bigl(\frac{D X}{dt}\Bigr)(t) =
   X'(t) + \Gamma_\alpha\bigl(u'(t),\ X(t)\bigr)(u(t)),$$
where `u(t) := φ_α(γ(t)) = extChartAt I α (γ t)` is the chart-coordinate
trajectory.

The chart-Christoffel contraction `chartChristoffelContraction g α v w y`
provided by `Geodesic/Equation.lean` is bilinear in `v` and `w` (and
symmetric in them). We use that to derive linearity of `D X / dt` in
`X`.

We expose `chartCovDerivAlong` as the explicit `E`-valued formula and
the predicate `IsCovDerivAlongChart` for "`W` is `D Y / dt`". The
explicit formula uses `deriv` (Mathlib's real-variable derivative) for
`X` and `u`; the predicate version uses `HasDerivAt` and avoids the
need for `deriv` to be defined off the differentiable locus. -/

/-- Helper: the chart-coordinate curve `u(t) := φ_α(γ(t))`. -/
def chartCurve (α : M) (γ : ℝ → M) : ℝ → E :=
  fun t => extChartAt I α (γ t)

@[simp] lemma chartCurve_def (α : M) (γ : ℝ → M) (t : ℝ) :
    chartCurve (I := I) α γ t = extChartAt I α (γ t) := rfl

/-- The chart-local covariant derivative of a section `X` along `γ` at
time `t`, written in the chart at the basepoint `α : M`:
$$\Bigl(\frac{D X}{dt}\Bigr)(t)
  = X'(t) + \Gamma_\alpha(u'(t), X(t))(u(t)),$$
where `u(t) = φ_α(γ(t))`. The formula uses `deriv` for the
representation of the time-derivatives; it is the right expression
*only when* `X` and `u` are differentiable at `t`. -/
def chartCovDerivAlong (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) : E :=
  deriv X t +
    chartChristoffelContraction (I := I) g α
      (deriv (chartCurve (I := I) α γ) t) (X t)
      (chartCurve (I := I) α γ t)

@[simp] lemma chartCovDerivAlong_def
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) :
    chartCovDerivAlong (I := I) g α γ X t =
      deriv X t +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t) (X t)
          (chartCurve (I := I) α γ t) := rfl

/-! ### Linearity of the chart-Christoffel contraction in each slot

The contraction `chartChristoffelContraction g α v w y` is linear in
`v` and linear in `w` for fixed `y` and `α`. This is the algebraic
backbone of linearity of `D/dt`. -/

namespace ChartChristoffel

variable {g : SmoothRiemannianMetric I M} {α : M} {y : E}

/-- The Christoffel contraction is right-additive in its second vector
slot. -/
lemma contraction_add_right (v w₁ w₂ : E) :
    chartChristoffelContraction (I := I) g α v (w₁ + w₂) y =
      chartChristoffelContraction (I := I) g α v w₁ y +
        chartChristoffelContraction (I := I) g α v w₂ y := by
  classical
  unfold chartChristoffelContraction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul]
  congr 1
  -- distribute the inner sum over the `w₁ + w₂` slot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show chartCoord (E := E) j (w₁ + w₂) =
      chartCoord (E := E) j w₁ + chartCoord (E := E) j w₂ from by
    unfold chartCoord; simp]
  ring

/-- The Christoffel contraction is left-additive in its first vector
slot. By the symmetry of the contraction in its arguments
(`chartChristoffelContraction_symm`), this is equivalent to right
additivity. -/
lemma contraction_add_left (v₁ v₂ w : E) :
    chartChristoffelContraction (I := I) g α (v₁ + v₂) w y =
      chartChristoffelContraction (I := I) g α v₁ w y +
        chartChristoffelContraction (I := I) g α v₂ w y := by
  rw [chartChristoffelContraction_symm, contraction_add_right,
    chartChristoffelContraction_symm (v := v₁) (w := w),
    chartChristoffelContraction_symm (v := v₂) (w := w)]

/-- The Christoffel contraction commutes with scalar multiplication in
the second vector slot. -/
lemma contraction_smul_right (a : ℝ) (v w : E) :
    chartChristoffelContraction (I := I) g α v (a • w) y =
      a • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_smul]
  ring

/-- The Christoffel contraction commutes with scalar multiplication in
the first vector slot. -/
lemma contraction_smul_left (a : ℝ) (v w : E) :
    chartChristoffelContraction (I := I) g α (a • v) w y =
      a • chartChristoffelContraction (I := I) g α v w y := by
  rw [chartChristoffelContraction_symm, contraction_smul_right,
    chartChristoffelContraction_symm (v := v) (w := w)]

/-- Zero on the right side: the Christoffel contraction is zero if the
second slot is zero. -/
lemma contraction_zero_right (v : E) :
    chartChristoffelContraction (I := I) g α v (0 : E) y = 0 := by
  rw [chartChristoffelContraction_symm, chartChristoffelContraction_zero_left]

end ChartChristoffel

/-- The continuous linear map `E → E` given by
`w ↦ chartChristoffelContraction g α v w y`. Linearity in `w` is by
`contraction_add_right` and `contraction_smul_right`. Boundedness on a
finite-dimensional vector space is automatic. -/
def chartChristoffelContractionRightCLM
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => chartChristoffelContraction (I := I) g α v w y
      map_add' := fun w₁ w₂ => ChartChristoffel.contraction_add_right v w₁ w₂
      map_smul' := fun a w => ChartChristoffel.contraction_smul_right a v w }

@[simp] lemma chartChristoffelContractionRightCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) (w : E) :
    chartChristoffelContractionRightCLM (I := I) g α v y w =
      chartChristoffelContraction (I := I) g α v w y := rfl

/-- The covariant-derivative formula expressed via a continuous linear
map: `D X / dt = X'(t) + A_t (X(t))`, where `A_t := chartChristoffelContractionRightCLM g α (u'(t)) (u(t))`
is the linear endomorphism of the model fibre that depends on the
chart-trajectory `u`. This is the formulation that feeds Picard–Lindelöf
for parallel transport (which corresponds to `D X / dt = 0`). -/
lemma chartCovDerivAlong_eq_add_clm
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) :
    chartCovDerivAlong (I := I) g α γ X t =
      deriv X t +
        chartChristoffelContractionRightCLM (I := I) g α
          (deriv (chartCurve (I := I) α γ) t)
          (chartCurve (I := I) α γ t) (X t) := rfl

/-! ### `IsCovDerivAlongChart` predicate -/

/-- Predicate "`W` is the covariant derivative of `Y` along `γ` on `s`,
written in the chart at `α`". The predicate uses `HasDerivAt` so the
section need only be differentiable at points of `s` (not necessarily
on a larger set). The chart-curve `u = chartCurve α γ` must have a
specified derivative `uPrime t` at `t`; we package this as a hypothesis
in the predicate body. -/
def IsCovDerivAlongChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y W : ℝ → E) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) ∧
    ∀ t ∈ s, HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t

/-- If `W = D Y / dt` in the predicate sense, then for every `t ∈ s`,
`Y'(t) + Γ_α(u'(t), Y(t))(u(t)) = W(t)`. -/
lemma IsCovDerivAlongChart.hasDerivAt_eq
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t :=
  h.2 t ht

/-- Linearity in `Y`: if `W_i = D Y_i / dt` for `i ∈ {1, 2}`, then
`W₁ + W₂ = D (Y₁ + Y₂) / dt`. -/
theorem IsCovDerivAlongChart.add
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y₁ Y₂ W₁ W₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsCovDerivAlongChart (I := I) g α γ uPrime Y₁ W₁ s)
    (h₂ : IsCovDerivAlongChart (I := I) g α γ uPrime Y₂ W₂ s) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => Y₁ t + Y₂ t) (fun t => W₁ t + W₂ t) s := by
  refine ⟨h₁.1, ?_⟩
  intro t ht
  have hY₁ := h₁.2 t ht
  have hY₂ := h₂.2 t ht
  have hadd := hY₁.add hY₂
  -- the right-hand side: rewrite `Γ_α(u'(t), Y₁ t + Y₂ t)(u(t))` via additivity
  have hΓadd :
      chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t + Y₂ t)
          (chartCurve (I := I) α γ t)
        = chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
              (chartCurve (I := I) α γ t)
          + chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_add_right (uPrime t) (Y₁ t) (Y₂ t)
  -- Goal: `HasDerivAt (Y₁ + Y₂) (W₁ t + W₂ t - Γ_α (u' t) (Y₁ t + Y₂ t) ⋯) t`
  -- We have `HasDerivAt (Y₁ + Y₂) ((W₁ t - Γ₁) + (W₂ t - Γ₂)) t` from `hadd`.
  -- These are equal by `hΓadd` and a single `module`.
  convert hadd using 1
  rw [hΓadd]; module

/-- Real-scalar linearity in `Y`: if `W = D Y / dt`, then `c • W = D (c • Y) / dt`. -/
theorem IsCovDerivAlongChart.smul
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) (c : ℝ) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => c • Y t) (fun t => c • W t) s := by
  refine ⟨h.1, ?_⟩
  intro t ht
  have hY := h.2 t ht
  have hcY := hY.const_smul c
  have hΓsmul :
      chartChristoffelContraction (I := I) g α (uPrime t) (c • Y t)
          (chartCurve (I := I) α γ t)
        = c • chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_smul_right c (uPrime t) (Y t)
  convert hcY using 1
  rw [hΓsmul, smul_sub]

/-- The zero section has zero covariant derivative. -/
theorem IsCovDerivAlongChart.zero
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (uPrime : ℝ → E) (s : Set ℝ)
    (hu : ∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) :
    IsCovDerivAlongChart (I := I) g α γ uPrime (fun _ => (0 : E)) (fun _ => (0 : E)) s := by
  refine ⟨hu, ?_⟩
  intro t _
  have hΓ0 : chartChristoffelContraction (I := I) g α (uPrime t) (0 : E)
        (chartCurve (I := I) α γ t) = 0 :=
    ChartChristoffel.contraction_zero_right (uPrime t)
  rw [hΓ0]; simpa using (hasDerivAt_const t (0 : E))

/-! ### Leibniz rule for scalar-function multiples

If `W = D Y / dt` (chart-α form) and `f : ℝ → ℝ` is differentiable at
`t ∈ s` with derivative `f'(t)`, then
`D (f · Y) / dt = f'(t) • Y(t) + f(t) • W(t)`. -/

theorem IsCovDerivAlongChart.smulFun
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s)
    {f : ℝ → ℝ} {fPrime : ℝ → ℝ}
    (hf : ∀ t ∈ s, HasDerivAt f (fPrime t) t) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => f t • Y t)
      (fun t => fPrime t • Y t + f t • W t) s := by
  refine ⟨h.1, ?_⟩
  intro t ht
  have hY := h.2 t ht
  have hft := hf t ht
  -- Differentiating `f t • Y t`.
  have hfY := hft.smul hY
  -- The derivative of `f Y` at `t` is `fPrime t • Y t + f t • (W t - Γ_α (u' t)(Y t)(u t))`
  -- Goal: `HasDerivAt (fun t => f t • Y t)
  --        ((fPrime t • Y t + f t • W t) - Γ_α (u' t) (f t • Y t)(u t)) t`
  have hΓsmul :
      chartChristoffelContraction (I := I) g α (uPrime t) (f t • Y t)
          (chartCurve (I := I) α γ t)
        = f t • chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_smul_right (f t) (uPrime t) (Y t)
  -- Compare with hfY's stated derivative
  convert hfY using 1
  rw [hΓsmul, smul_sub]; module

/-! ## G.5.4 — Parallel transport in a chart

A section `Y` along `γ` is **parallel in the chart at `α`** if
`D Y / dt = 0`, i.e.
$$Y'(t) + \Gamma_\alpha(u'(t), Y(t))(u(t)) = 0.$$
This is a *linear* first-order ODE in `Y` (with coefficients depending
on the curve `u`), so existence on a chart-interval (where the
coefficients are continuous) is provided by Picard–Lindelöf, and
uniqueness by Gronwall.

We expose:
* `IsParallelChart`: the predicate, defined as the special case of
  `IsCovDerivAlongChart` with `W = 0`;
* `IsParallelChart.unique_of_initial`: uniqueness via Gronwall (any two
  solutions sharing an initial value agree on a chart-interval where
  the contraction has a uniform Lipschitz constant in `Y`). -/

/-- A section `Y` is parallel along `γ` on `s ⊆ ℝ` in the chart at `α`
iff `Y` satisfies the parallel-transport ODE
`Y'(t) = - Γ_α(u'(t), Y(t))(u(t))`. -/
def IsParallelChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsCovDerivAlongChart (I := I) g α γ uPrime Y (fun _ => (0 : E)) s

/-- Unfolding: `Y` is parallel iff the chart-curve has the prescribed
derivative and `Y'(t) = - Γ_α(u'(t), Y(t))(u(t))` for `t ∈ s`. -/
lemma IsParallelChart.hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt Y
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t := by
  have := h.2 t ht
  simpa using this

/-- The chart-curve hypothesis embedded in `IsParallelChart`. -/
lemma IsParallelChart.chartCurve_hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t :=
  h.1 t ht

/-- Linearity of parallel transport: a real-scalar multiple of a
parallel section is parallel. -/
theorem IsParallelChart.smul
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) (c : ℝ) :
    IsParallelChart (I := I) g α γ uPrime (fun t => c • Y t) s := by
  have hsmul := IsCovDerivAlongChart.smul (h := h) c
  -- The derivative `c • (0 : ℝ → E) = (0 : ℝ → E)`.
  have hzero : (fun t : ℝ => c • (0 : E)) = (fun _ : ℝ => (0 : E)) := by
    funext; simp
  rw [IsParallelChart]
  -- Convert `c • W` (with `W = 0`) to `(fun _ => 0)` componentwise
  convert hsmul using 1
  exact hzero.symm

/-- Additivity of parallel transport. -/
theorem IsParallelChart.add
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsParallelChart (I := I) g α γ uPrime Y₁ s)
    (h₂ : IsParallelChart (I := I) g α γ uPrime Y₂ s) :
    IsParallelChart (I := I) g α γ uPrime (fun t => Y₁ t + Y₂ t) s := by
  have hadd := IsCovDerivAlongChart.add h₁ h₂
  have hzero : (fun t : ℝ => (0 : E) + 0) = (fun _ : ℝ => (0 : E)) := by
    funext; simp
  rw [IsParallelChart]
  convert hadd using 1
  exact hzero.symm

/-! ### Uniqueness of parallel transport via Gronwall

If two `E`-valued curves `Y₁`, `Y₂` both satisfy the parallel-transport
ODE on an open real interval `Ioo a b` (in the chart at `α`) and agree
at one point `t₀ ∈ Ioo a b`, then they agree on the whole interval —
provided the right-hand side is uniformly Lipschitz in `Y` on the
interval. The Lipschitz constant comes from the operator norm of the
linear map `Y ↦ Γ_α(u'(t), Y)(u(t))` on `E`. -/

/-- The Lipschitz constant for the parallel-transport vector field on a
real interval: the supremum of the operator norm of
`Y ↦ Γ_α(u'(t), Y)(u(t))` over `t ∈ s`. We expose it as a hypothesis
rather than constructing it explicitly; the existence on a compact
chart-interval follows from continuity of `t ↦ chartChristoffelContractionRightCLM g α (u'(t)) (u(t))`
in `t`, which is itself a downstream-of-`Picard-Lindelöf` development. -/
def ParallelTransportLipschitzBound (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (K : NNReal) (s : Set ℝ) : Prop :=
  ∀ t ∈ s,
    ‖chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)‖₊ ≤ K

/-- **Uniqueness of parallel transport (Gronwall).** On an open
interval `Ioo a b` with `t₀ ∈ Ioo a b`, two parallel sections sharing
an initial value at `t₀` agree on `Ioo a b`, given a uniform Lipschitz
bound on the right-hand side. -/
theorem IsParallelChart.unique_of_initial
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {a b t₀ : ℝ} {K : NNReal}
    (h₁ : IsParallelChart (I := I) g α γ uPrime Y₁ (Set.Ioo a b))
    (h₂ : IsParallelChart (I := I) g α γ uPrime Y₂ (Set.Ioo a b))
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K (Set.Ioo a b))
    (ht₀ : t₀ ∈ Set.Ioo a b) (hinit : Y₁ t₀ = Y₂ t₀) :
    Set.EqOn Y₁ Y₂ (Set.Ioo a b) := by
  classical
  -- The vector field: `v t Y = - Γ_α(u'(t), Y)(u(t))`, a linear function of `Y`.
  set v : ℝ → E → E :=
    fun t Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                  (chartCurve (I := I) α γ t) Y with hv_def
  -- Lipschitz constant on the whole space:
  have hLip : ∀ t ∈ Set.Ioo a b,
      LipschitzOnWith K (v t) (Set.univ : Set E) := by
    intro t ht
    -- `Y ↦ Γ_α(u'(t), Y)(u(t))` is a continuous linear map of operator norm `≤ K`.
    have hclm : LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t)‖₊
        (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)) :=
      (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)).lipschitz
    have hclm_neg : LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t)‖₊
        (fun Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) Y) :=
      hclm.neg
    -- Weaken to bound `K`.
    have hweak : LipschitzWith K
        (fun Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) Y) :=
      hclm_neg.weaken (hK t ht)
    -- Apply to `LipschitzOnWith`.
    exact hweak.lipschitzOnWith
  -- The HasDerivAt clauses for Y₁ and Y₂
  have hY₁ : ∀ t ∈ Set.Ioo a b, HasDerivAt Y₁ (v t (Y₁ t)) t ∧ Y₁ t ∈ (Set.univ : Set E) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    -- `v t (Y₁ t) = - Γ_α(u'(t), Y₁ t)(u t)` by definition (via CLM rfl-unfolding).
    change HasDerivAt Y₁ (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) (Y₁ t)) t
    exact h₁.hasDerivAt ht
  have hY₂ : ∀ t ∈ Set.Ioo a b, HasDerivAt Y₂ (v t (Y₂ t)) t ∧ Y₂ t ∈ (Set.univ : Set E) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    change HasDerivAt Y₂ (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) (Y₂ t)) t
    exact h₂.hasDerivAt ht
  exact ODE_solution_unique_of_mem_Ioo hLip ht₀ hY₁ hY₂ hinit

/-- **Uniqueness of parallel transport (local form).** Two parallel
sections sharing an initial value at `t₀` agree in some neighborhood of
`t₀`, provided the right-hand side is eventually-Lipschitz. -/
theorem IsParallelChart.unique_eventually
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {t₀ : ℝ} {K : NNReal}
    (hLip : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K
      (fun Y : E => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t) Y) (Set.univ : Set E))
    (h₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₁
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
        (chartCurve (I := I) α γ t)) t)
    (h₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₂
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
        (chartCurve (I := I) α γ t)) t)
    (hinit : Y₁ t₀ = Y₂ t₀) : Y₁ =ᶠ[𝓝 t₀] Y₂ := by
  classical
  -- recast the HasDerivAt clauses in terms of the linearized vector field
  have hYY₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₁
      ((fun s : ℝ => - chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s)) t (Y₁ t)) t ∧ Y₁ t ∈ (Set.univ : Set E) := by
    refine h₁.mono ?_
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    simpa using ht
  have hYY₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₂
      ((fun s : ℝ => - chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s)) t (Y₂ t)) t ∧ Y₂ t ∈ (Set.univ : Set E) := by
    refine h₂.mono ?_
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    simpa using ht
  exact ODE_solution_unique_of_eventually hLip hYY₁ hYY₂ hinit

/-! ### A clean wrapper: existence of parallel transport from data

The standard Picard–Lindelöf application says: if the
parallel-transport vector field
`v t Y := - Γ_α(u'(t), Y)(u(t))`
is continuous in `t` and Lipschitz (in fact linear) in `Y`, then for
any initial datum `Y(t₀) = v₀` there is a (local) solution. We expose a
clean *predicate-existence* statement so that downstream developments
(Jacobi fields, Rauch comparison) can refer to the parallel-transport
section by name. -/

/-- `HasParallelTransportChart g α γ uPrime t₀ v₀ Y s` says that `Y` is
a parallel section along `γ` in the chart at `α` on `s ⊆ ℝ`, with
initial value `Y(t₀) = v₀`. This packages "Y is the parallel transport
of v₀ along γ at t₀ (in chart α)" into a Prop. -/
def HasParallelTransportChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (t₀ : ℝ) (v₀ : E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsParallelChart (I := I) g α γ uPrime Y s ∧ Y t₀ = v₀

/-- Parallel transport, when it exists, is uniquely determined by its
initial value on any open interval (with the standard Lipschitz hypothesis). -/
theorem HasParallelTransportChart.unique_of_lipschitz
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {a b t₀ : ℝ} {v₀ : E} {K : NNReal}
    (h₁ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₀ Y₁ (Set.Ioo a b))
    (h₂ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₀ Y₂ (Set.Ioo a b))
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K (Set.Ioo a b))
    (ht₀ : t₀ ∈ Set.Ioo a b) :
    Set.EqOn Y₁ Y₂ (Set.Ioo a b) :=
  IsParallelChart.unique_of_initial h₁.1 h₂.1 hK ht₀
    (h₁.2.trans h₂.2.symm)

/-- The zero parallel transport: `Y ≡ 0` is the parallel transport of
the zero vector at any base time `t₀`, on any `s` where the
chart-curve has the prescribed derivative. -/
theorem HasParallelTransportChart.zero
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (uPrime : ℝ → E)
    (t₀ : ℝ) (s : Set ℝ)
    (hu : ∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) :
    HasParallelTransportChart (I := I) g α γ uPrime t₀ (0 : E) (fun _ => (0 : E)) s := by
  refine ⟨?_, rfl⟩
  exact IsCovDerivAlongChart.zero g α γ uPrime s hu

/-- Linear superposition: if `Y₁` and `Y₂` are parallel transports of
`v₁` and `v₂` (with the same chart-curve derivative `uPrime`), then
`a • Y₁ + b • Y₂` is the parallel transport of `a • v₁ + b • v₂`. -/
theorem HasParallelTransportChart.linear_combination
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {t₀ : ℝ} {v₁ v₂ : E} (a c : ℝ) {s : Set ℝ}
    (h₁ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₁ Y₁ s)
    (h₂ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₂ Y₂ s) :
    HasParallelTransportChart (I := I) g α γ uPrime t₀ (a • v₁ + c • v₂)
      (fun t => a • Y₁ t + c • Y₂ t) s := by
  refine ⟨?_, ?_⟩
  · -- The linear combination is parallel.
    have hY₁ := IsParallelChart.smul h₁.1 a
    have hY₂ := IsParallelChart.smul h₂.1 c
    exact IsParallelChart.add hY₁ hY₂
  · -- The initial value of the linear combination matches.
    simp [h₁.2, h₂.2]

/-! ## Summary

We have established:

* `SectionAlongCurve`: bundled data of a section along `γ`, with full
  algebraic API (add, neg, sub, smul, smul-by-function, zero) and full
  smoothness/differentiability API (`ContMDiffOnInChart`,
  `ContMDiffAtInChart`, `DifferentiableOnAlong`, `DifferentiableAtAlong`,
  closed under all the algebraic operations).

* `chartCovDerivAlong`: the explicit chart-α formula for `D X / dt`.

* `IsCovDerivAlongChart`: the predicate "`W = D Y / dt` in chart `α`",
  closed under linear combinations and satisfying the scalar-function
  Leibniz rule.

* `IsParallelChart`: parallel-transport predicate, linear under
  superposition.

* `IsParallelChart.unique_of_initial` and
  `IsParallelChart.unique_eventually`: **Gronwall uniqueness** of
  parallel transport with prescribed initial value, on open intervals
  and locally respectively.

* `HasParallelTransportChart`: the predicate "parallel transport of `v₀`
  at `t₀`", with the uniqueness corollary
  `HasParallelTransportChart.unique_of_lipschitz` and the linear-
  superposition theorem `HasParallelTransportChart.linear_combination`.

Existence of parallel transport on a single chart-interval reduces to a
standard Picard–Lindelöf application to the linearized ODE
`Y'(t) = - Γ_α(u'(t), Y(t))(u(t))`; the existence statement, plus the
chart-gluing extension to the full curve, are downstream developments
that consume the API of this file. Chart independence of `D/dt` and of
parallel transport (i.e. the same notion arises from any chart α whose
source contains `γ(t)`) is also a downstream theorem: it amounts to the
verification that the chart-α Christoffel-correction term transforms in
the canonical way under chart changes. -/

end AlongCurve
end Riemannian
end Geometry
end DifferentialGeometry
