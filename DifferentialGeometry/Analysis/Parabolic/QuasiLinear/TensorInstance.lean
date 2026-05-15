import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Existence
import DifferentialGeometry.Analysis.Parabolic.TensorLinearParabolic

/-!
# Quasi-linear tensor heat equation on `L²`: short-time existence and uniqueness

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a uniform
tensor Sobolev bound `h_uniform`, the tensor heat semigroup `e^{t Δ_∇}`
on `TensorL2 r s g` is a bounded strongly continuous one-parameter
contraction semigroup. This file packages it as a `BoundedC0Semigroup`
and feeds it into the abstract semilinear existence/uniqueness machinery
to obtain a short-time mild solution of the **quasi-linear** tensor heat
equation

  `∂_t T = Δ_∇ T + N(T)`,  `T(0) = T_0`,

for a globally Lipschitz lower-order nonlinearity `N : TensorL2 → TensorL2`.

## Main definitions

* `tensorBoundedC0Semigroup g r s h_uniform` — the tensor heat semigroup
  `e^{t Δ_∇}` packaged as a `BoundedC0Semigroup (TensorL2 r s g)`.

## Main results

* `tensor_quasilinear_parabolic_existence` — short-time existence of a
  continuous mild solution of the quasi-linear tensor heat equation.
* `tensor_quasilinear_parabolic_unique` — uniqueness of the mild
  solution on a short time interval.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The tensor heat semigroup as a `BoundedC0Semigroup`

The four structural fields of `BoundedC0Semigroup` are discharged from
the established analytic properties of the tensor heat semigroup:

* `apply_zero` from `tensorHeatSemigroup_zero` (stated as the
  continuous-linear-map identity `e^{0 Δ_∇} = id`);
* `apply_add` from `tensorHeatSemigroup_add` (the semigroup law, valid
  for non-negative times — exactly the hypotheses the field requires);
* `opNorm_le_one` from `tensorHeatSemigroup_opNorm_le_one` (the
  operator-norm contraction bound, available for every real time, in
  particular for `t ≥ 0`);
* `continuousOn_apply` from `tensorHeatSemigroup_continuous_on_nonneg`
  (strong continuity on `[0, ∞)`).
-/

/-- The tensor heat semigroup `e^{t Δ_∇}` on `TensorL2 r s g` packaged as
a bounded strongly continuous one-parameter contraction semigroup. -/
noncomputable def tensorBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s) :
    BoundedC0Semigroup (TensorL2 r s g) where
  toFun := fun t => tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t
  apply_zero :=
    tensorHeatSemigroup_zero (I := I) (M := M) h_uniform
  apply_add := fun _ _ ht hs =>
    tensorHeatSemigroup_add (I := I) (M := M) h_uniform ht hs
  opNorm_le_one := fun t _ =>
    tensorHeatSemigroup_opNorm_le_one
      (I := I) (M := M) (h_uniform := h_uniform) t
  continuousOn_apply := fun T =>
    tensorHeatSemigroup_continuous_on_nonneg
      (I := I) (M := M) h_uniform T

/-- The underlying one-parameter family of `tensorBoundedC0Semigroup` is
the tensor heat semigroup. -/
@[simp]
theorem tensorBoundedC0Semigroup_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s) (t : ℝ) :
    tensorBoundedC0Semigroup (I := I) (M := M) g r s h_uniform t =
      tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t :=
  rfl

/-! ## Short-time existence for the quasi-linear tensor heat equation

Instantiating the abstract semilinear existence theorem
`semilinear_parabolic_existence` with the tensor heat semigroup and a
globally Lipschitz nonlinearity yields a continuous short-time mild
solution of the quasi-linear tensor heat equation. The abstract Duhamel
terms `S t u₀` and `S (t - τ) (N (u τ))` unfold definitionally — the
`toFun` field of `tensorBoundedC0Semigroup` *is* the tensor heat
semigroup — to the concrete heat-semigroup applications. -/

/-- **Short-time existence of a mild solution of the quasi-linear tensor
heat equation.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a uniform
tensor Sobolev bound `h_uniform`, an initial datum `T_0 : TensorL2 r s g`,
and a globally Lipschitz lower-order nonlinearity `N`, there is a
positive existence time `T` and a continuous path
`u : [0, T] → TensorL2 r s g` solving the Duhamel integral equation

  `u(t) = e^{t Δ_∇} T_0 + ∫₀ᵗ e^{(t-τ) Δ_∇} (N (u τ)) dτ`

with `u(0) = T_0`. -/
theorem tensor_quasilinear_parabolic_existence
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (T_0 : TensorL2 r s g)
    {N : TensorL2 r s g → TensorL2 r s g} {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → TensorL2 r s g,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = T_0 ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = tensorHeatSemigroup g r s h_uniform t T_0 +
          ∫ τ in (0:ℝ)..t,
            tensorHeatSemigroup g r s h_uniform (t - τ) (N (u τ)) := by
  -- Apply the abstract semilinear existence theorem to the tensor heat
  -- semigroup.
  obtain ⟨T, hT_pos, u, hu_cont, hu_zero, hu_eq⟩ :=
    semilinear_parabolic_existence
      (tensorBoundedC0Semigroup (I := I) (M := M) g r s h_uniform) T_0 hN
  refine ⟨T, hT_pos, u, hu_cont, hu_zero, ?_⟩
  -- The abstract Duhamel terms coincide with the concrete heat-semigroup
  -- applications by definition of `tensorBoundedC0Semigroup`.
  intro t ht
  have h := hu_eq t ht
  simpa only [tensorBoundedC0Semigroup_apply] using h

/-! ## Uniqueness for the quasi-linear tensor heat equation

Instantiating the abstract semilinear uniqueness theorem
`semilinear_parabolic_unique` with the tensor heat semigroup: two
continuous mild solutions on the same interval `[0, T]` with
`(L : ℝ) * T < 1` coincide. -/

/-- **Uniqueness of the mild solution of the quasi-linear tensor heat
equation.**

Any two continuous paths `u, v : [0, T] → TensorL2 r s g` solving the
quasi-linear tensor heat Duhamel integral equation with the same initial
datum `T_0` coincide on `[0, T]`, provided `(L : ℝ) * T < 1`. -/
theorem tensor_quasilinear_parabolic_unique
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (T_0 : TensorL2 r s g)
    {N : TensorL2 r s g → TensorL2 r s g} {L : ℝ≥0} (hN : LipschitzWith L N)
    {T : ℝ} (hT : 0 < T) (hTL : (L : ℝ) * T < 1)
    {u v : ℝ → TensorL2 r s g}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = tensorHeatSemigroup g r s h_uniform t T_0 +
        ∫ τ in (0:ℝ)..t,
          tensorHeatSemigroup g r s h_uniform (t - τ) (N (u τ)))
    (hv_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = tensorHeatSemigroup g r s h_uniform t T_0 +
        ∫ τ in (0:ℝ)..t,
          tensorHeatSemigroup g r s h_uniform (t - τ) (N (v τ))) :
    Set.EqOn u v (Set.Icc 0 T) := by
  -- Translate the concrete Duhamel equations into the abstract form
  -- expected by `semilinear_parabolic_unique`, then apply it.
  refine semilinear_parabolic_unique
    (tensorBoundedC0Semigroup (I := I) (M := M) g r s h_uniform) T_0 hN
    hT hTL hu hv ?_ ?_
  · intro t ht
    simpa only [tensorBoundedC0Semigroup_apply] using hu_eq t ht
  · intro t ht
    simpa only [tensorBoundedC0Semigroup_apply] using hv_eq t ht

/-! ## Connection to the linear Duhamel mild solution

The abstract Duhamel map `duhamel` applied to the tensor heat semigroup
recovers the concrete `tensorMildSolution` of `TensorLinearParabolic.lean`:
the two are definitionally equal, since the abstract Duhamel formula
`S t u₀ + ∫₀ᵗ S (t - τ) (F τ) dτ` reduces — with `S` the tensor heat
semigroup — to the tensor mild-solution formula. -/

/-- The abstract Duhamel mild solution for the tensor heat semigroup is
the concrete tensor mild solution. -/
theorem duhamel_tensorBoundedC0Semigroup_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (T_0 : TensorL2 r s g) (F : ℝ → TensorL2 r s g) (t : ℝ) :
    duhamel (tensorBoundedC0Semigroup (I := I) (M := M) g r s h_uniform)
        T_0 F t =
      tensorMildSolution (I := I) (M := M) g r s h_uniform T_0 F t :=
  rfl

end Parabolic
end Analysis
end DifferentialGeometry

end
