import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueFields
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Divergence-form organization of the two-metric Laplacian difference (Route-K brick K2.3)

Kotschwar's forward-uniqueness argument (`ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §4)
needs the difference of the two rough Laplacians applied to the *same* tensor field to
be written in **divergence form**: the naive expansion of `Δ_{g₁} − Δ_{g₂}` produces a
second derivative of the metric difference `h₀₂`, which the Kotschwar energy cannot
control, whereas

```
Δ_{g₁} T − Δ_{g₂} T = div_{g₁} U + R,          U = ∇¹T − ∇²T
```

keeps the dangerous term inside a divergence whose flux `U` is only *first* order in `T`
and *zeroth* order in the differences, and leaves a remainder `R` that carries no
derivative of the curvature difference `S₀₄` and no second derivative of `h₀₂`.

## The flux

Kotschwar writes the flux as `Uᵃ = (g₁ᵃᵇ − g₂ᵃᵇ)∇²_b Rm₂ + g₁ᵃᵇ(∇¹_b − ∇²_b)Rm₂`, which
telescopes to `g₁ᵃᵇ∇¹_bRm₂ − g₂ᵃᵇ∇²_bRm₂`.  Lowering the free index with `g₁` turns this
into `∇¹Rm₂ − (g₁ ∘ g₂⁻¹)∇²Rm₂`.  This file uses the *equivalent* flux

```
U₀₅ = ∇¹T − ∇²T
```

which differs from the lowered Kotschwar flux by `(id − g₁∘g₂⁻¹)∇²T = O(|h₀₂|)·|∇²T|`,
hence satisfies the same estimate `|U| ≤ C(|h₀₂| + |A₀₃|)` — in fact the sharper
`|U| ≤ C|A₀₃|`, since `∇¹T − ∇²T` is the algebraic action of the connection-difference
tensor on `T` (`Tensor0SBundle.nabla0SFun_sub_cov`).  Choosing this representative avoids
the composite endomorphism `g₁♭ ∘ g₂♯` on the divergence slot entirely, so the whole brick
stays inside the `Tensor0S` stack: no mixed-variance `(1,s)` object and no cross-variance
connection-difference module are needed.

The divergence index sits in **slot 0**, matching the repository's
`contract_covariant`/`covDivergence` convention
(`Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/TensorCovDivergence.lean`):
`totalNabla0SFun` places the new derivative slot first, and `metricTraceFirstTwoField`
contracts slots `0, 1`, i.e. the derivative index against the flux's own slot `0`.

## The remainder

```
R = tr_{g₁}(∇¹∇²T − ∇²∇²T) + (tr_{g₁} − tr_{g₂})(∇²∇²T).
```

Both summands are manifestly *differences*: the first is the connection difference `A₀₃`
acting algebraically on the background field `∇²T`, the second is the inverse-metric
difference (an `O(|h₀₂|)` quantity) contracted against the background field `∇²∇²T`.
Neither contains a derivative of `S₀₄` nor a second derivative of `h₀₂`.  The norm
estimate `|R| ≤ C(|h₀₂| + |A₀₃| + |S₀₄|)` is deliberately **not** proved here; it is the
separate estimate brick.

## Scope

Two fixed smooth metrics, no time parameter.  The identity `lapDiff_eq_div_flux` is stated
generically at `(0,s)` and specialized to the `(0,4)` curvature setting through
`rmDiffFlux` and `rm2Low_eq_sub`, which identifies the input field of the curvature
instance as `metricRm04At g₁ − rmDiffLowAt g₁ g₂` (the carriers of
`Evolution/ForwardUniqueFields.lean`).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- An additive, `ℝ`-homogeneous map between `ℝ`-modules subtracts.  Local helper used to
turn the existing `_add`/`_smul` pairs of `totalNabla0SFun` and `metricTraceFirstTwoField`
into the `_sub` form the divergence-form regrouping needs. -/
private theorem sub_of_add_smul {A B : Type*}
    [AddCommGroup A] [Module Real A] [AddCommGroup B] [Module Real B]
    (f : A -> B) (hadd : ∀ a b : A, f (a + b) = f a + f b)
    (hsmul : ∀ (c : Real) (a : A), f (c • a) = c • f a) (a b : A) :
    f (a - b) = f a - f b := by
  have hab : a - b = a + (-1 : Real) • b := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hab, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]

section Operators

variable {s : ℕ}

/-- **One Levi-Civita covariant-derivative step on a `(0,s)` tensor field.**

The canonical total covariant derivative `totalNabla0S` of the Levi-Civita connection of
`g`, with its regularity discharged by `totalNabla0S_reg` from `metricCov_smooth`.  The
new derivative slot is slot `0`. -/
def metricNabla0S (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
    (metricCov (I := I) g) T
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M) s
      (metricCov (I := I) g) (metricCov_smooth (I := I) g) T)

@[simp] theorem metricNabla0S_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    metricNabla0S (I := I) g T x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
        (metricCov (I := I) g) T x := rfl

theorem metricNabla0S_add (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (T + U) =
      metricNabla0S (I := I) g T + metricNabla0S (I := I) g U := by
  refine DFunLike.ext _ _ fun x => ?_
  have hsplit :
      (metricNabla0S (I := I) g T + metricNabla0S (I := I) g U) x
        = metricNabla0S (I := I) g T x + metricNabla0S (I := I) g U x := rfl
  rw [hsplit]
  exact totalNabla0SFun_add (I := I) (M := M) (metricCov (I := I) g) T U x

theorem metricNabla0S_smul (g : SmoothRiemannianMetric I M) (c : Real)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (c • T) = c • metricNabla0S (I := I) g T := by
  refine DFunLike.ext _ _ fun x => ?_
  have hsplit :
      (c • metricNabla0S (I := I) g T) x = c • (metricNabla0S (I := I) g T x) := rfl
  rw [hsplit]
  exact totalNabla0SFun_smul (I := I) (M := M) (metricCov (I := I) g) c T x

theorem metricNabla0S_sub (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (T - U) =
      metricNabla0S (I := I) g T - metricNabla0S (I := I) g U :=
  sub_of_add_smul (metricNabla0S (I := I) g) (metricNabla0S_add (I := I) g)
    (fun c a => metricNabla0S_smul (I := I) g c a) T U

theorem traceFirstTwo_sub (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (A - B) =
      metricTraceFirstTwoField (I := I) (M := M) g A -
        metricTraceFirstTwoField (I := I) (M := M) g B :=
  sub_of_add_smul (metricTraceFirstTwoField (I := I) (M := M) (s := s) g)
    (metricTraceFirstTwoField_add (I := I) (M := M) g)
    (fun c a => metricTraceFirstTwoField_smul (I := I) (M := M) g c a) A B

theorem traceFirstTwo_zero (g : SmoothRiemannianMetric I M) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2)) = 0 := by
  simpa using traceFirstTwo_sub (I := I) (M := M) (s := s) g 0 0

/-- **Covariant divergence of a `(0,s+1)` tensor field**, contracting the derivative index
against slot `0` with `g`.

This is the field-level, everywhere-defined counterpart of the compactly-supported bundled
`covDivergence`
(`Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/TensorCovDivergence.lean`) and
uses the same slot-`0` convention; identifying the two is the job of the integration-by-parts
bridge, not of this file. -/
def covDiv0SField (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  metricTraceFirstTwoField (I := I) (M := M) g (metricNabla0S (I := I) g V)

/-- **Rough (connection) Laplacian of a `(0,s)` tensor field**: `Δ_g = div_g ∘ ∇^g`.

Fiberwise this is the canonical `roughLap0STensor` of the second covariant derivative
(`roughLap0SField_apply`). -/
def roughLap0SField (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  covDiv0SField (I := I) g (metricNabla0S (I := I) g T)

theorem roughLap0SField_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    roughLap0SField (I := I) g T x =
      roughLap0STensor (I := I) g
        (metricNabla0S (I := I) g (metricNabla0S (I := I) g T) x) := rfl

theorem covDiv0SField_sub (g : SmoothRiemannianMetric I M)
    (V W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    covDiv0SField (I := I) g (V - W) =
      covDiv0SField (I := I) g V - covDiv0SField (I := I) g W := by
  rw [covDiv0SField, covDiv0SField, covDiv0SField, metricNabla0S_sub,
    traceFirstTwo_sub]

end Operators

section DivergenceForm

variable {s : ℕ}

/-- **The Kotschwar curvature flux `U`** of two metrics on a covariant tensor field:
`U = ∇¹T − ∇²T`, a `(0,s+1)` field whose slot `0` is the divergence index.

See the module docstring: this is Kotschwar's `U` up to the `O(|h₀₂|)` term
`(id − g₁∘g₂⁻¹)∇²T`, and it is the algebraic action of the connection-difference tensor on
`T`, hence `O(|A₀₃|)`. -/
def lapDiffFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricNabla0S (I := I) g₁ T - metricNabla0S (I := I) g₂ T

theorem lapDiffFlux_apply (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    lapDiffFlux (I := I) g₁ g₂ T x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (metricCov (I := I) g₁) T x -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (metricCov (I := I) g₂) T x := rfl

/-- Equal metrics give a vanishing flux. -/
@[simp] theorem lapDiffFlux_self (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    lapDiffFlux (I := I) g g T = 0 :=
  sub_self _

/-- **The remainder `R`** of the divergence-form organization:

```
R = tr_{g₁}(∇¹∇²T − ∇²∇²T) + (tr_{g₁} − tr_{g₂})(∇²∇²T).
```

Both summands are explicit differences carrying no derivative of the curvature difference
`S₀₄` and no second derivative of `h₀₂`: the first is the connection difference acting
algebraically on the background field `∇²T`, the second is the inverse-metric difference
contracted against the background field `∇²∇²T`. -/
def lapDiffRem (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  metricTraceFirstTwoField (I := I) (M := M) g₁
      (lapDiffFlux (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T)) +
    (metricTraceFirstTwoField (I := I) (M := M) g₁
        (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)) -
      metricTraceFirstTwoField (I := I) (M := M) g₂
        (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)))

/-- Equal metrics give a vanishing remainder. -/
@[simp] theorem lapDiffRem_self (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    lapDiffRem (I := I) g g T = 0 := by
  rw [lapDiffRem, lapDiffFlux_self, traceFirstTwo_zero, sub_self, add_zero]

/-- **Divergence-form organization of the two-metric Laplacian difference** (Route-K brick
K2.3).  For any covariant tensor field `T` and any two smooth metrics,

```
Δ_{g₁}T − Δ_{g₂}T = div_{g₁}(∇¹T − ∇²T) + R,
```

with `R = lapDiffRem` explicit.  The point is what does *not* appear on the right: the
flux is first order in `T` and the remainder contains no derivative of the curvature
difference and no second derivative of the metric difference, which is exactly what makes
the Kotschwar energy estimate close after one integration by parts against `S₀₄`. -/
theorem lapDiff_eq_div_flux (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g₁ T - roughLap0SField (I := I) g₂ T =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) +
        lapDiffRem (I := I) g₁ g₂ T := by
  have hdiv :
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) =
        roughLap0SField (I := I) g₁ T -
          covDiv0SField (I := I) g₁ (metricNabla0S (I := I) g₂ T) := by
    rw [lapDiffFlux, covDiv0SField_sub, roughLap0SField]
  have hrem :
      lapDiffRem (I := I) g₁ g₂ T =
        (covDiv0SField (I := I) g₁ (metricNabla0S (I := I) g₂ T) -
            metricTraceFirstTwoField (I := I) (M := M) g₁
              (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T))) +
          (metricTraceFirstTwoField (I := I) (M := M) g₁
              (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)) -
            roughLap0SField (I := I) g₂ T) := by
    rw [lapDiffRem, lapDiffFlux, traceFirstTwo_sub, roughLap0SField, covDiv0SField,
      covDiv0SField]
  rw [hdiv, hrem]
  abel

end DivergenceForm

section Curvature

/-- **`U₀₅`: the pointwise curvature flux** of the forward-uniqueness system, the `(0,5)`
fiber value of `lapDiffFlux` on the `(0,4)` field of the `g₁`-lowered Riemann tensor of
`g₂`.  Its slot `0` is the divergence index. -/
def rmDiffFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x :=
  lapDiffFlux (I := I) g₁ g₂ Rm2 x

theorem rmDiffFlux_apply (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    rmDiffFlux (I := I) g₁ g₂ Rm2 x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (metricCov (I := I) g₁) Rm2 x -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (metricCov (I := I) g₂) Rm2 x := rfl

/-- **The input field of the curvature instance, read through the `S₀₄` carrier.**  The
`g₁`-lowered Riemann tensor of `g₂` — the field `T` that `rmDiffFlux` differentiates — is
the canonical `metricRm04At g₁` minus the Kotschwar curvature-difference carrier
`rmDiffLowAt g₁ g₂` of `Evolution/ForwardUniqueFields.lean`. -/
theorem rm2Low_eq_sub (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x =
      metricRm04At (I := I) g₁ x - rmDiffLowAt (I := I) g₁ g₂ x :=
  (sub_sub_cancel _ _).symm

/-- **The curvature instance of `lapDiff_eq_div_flux`**: the difference of the two rough
Laplacians of the `g₁`-lowered Riemann tensor of `g₂` is a `g₁`-divergence of `U₀₅` plus
the explicit remainder.  Pointwise form at each `x`. -/
theorem rmLapDiff_div_flux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    roughLap0SField (I := I) g₁ Rm2 x - roughLap0SField (I := I) g₂ Rm2 x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) x +
        lapDiffRem (I := I) g₁ g₂ Rm2 x := by
  have h := lapDiff_eq_div_flux (I := I) g₁ g₂ Rm2
  have hsub :
      (roughLap0SField (I := I) g₁ Rm2 - roughLap0SField (I := I) g₂ Rm2) x =
        roughLap0SField (I := I) g₁ Rm2 x - roughLap0SField (I := I) g₂ Rm2 x := rfl
  have hadd :
      (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) +
          lapDiffRem (I := I) g₁ g₂ Rm2) x =
        covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) x +
          lapDiffRem (I := I) g₁ g₂ Rm2 x := rfl
  rw [← hsub, ← hadd, h]

end Curvature

end DifferentialGeometry.PDE.RicciFlow

end
