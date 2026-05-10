import RicciFlower.Realized.Operators
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Scalar Weak Maximum Principle

This file starts the realized formalization of Hamilton's scalar weak maximum
principle for supersolutions. The proved part is the algebra that reduces the
supersolution and ODE hypotheses to a negative-region inequality. The compact
strict-barrier argument is stated as a precise theorem with a controlled
`sorry`, because the endpoint time-derivative/minimum infrastructure is not yet
fully packaged for the realized manifold layer.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The compact spacetime slab `[0,T] × M`. -/
def spacetimeSlab (T : Real) : Set (Real × M) :=
  Set.Icc 0 T ×ˢ Set.univ

/-- The scalar parabolic operator `∂ₜ - Δ_g - <X,∇·>` on a realized metric family. -/
def parabolicOperatorWithDrift
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M) : Real :=
  derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
    heatOperatorWithDrift (I := I) G t (X t) (u t) x

@[simp] theorem parabolicOperatorWithDrift_eq
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X u t x =
      derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
        heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
  rfl

/-! ## Algebraic core of the negative-region estimate -/

/-- Lipschitz control converts the reaction difference into a lower bound on
the negative region `u - c < 0`. -/
theorem reaction_difference_lower_bound_on_negative_region
    {uval cval Fu Fc L : Real}
    (hlip : |Fu - Fc| <= L * |uval - cval|)
    (hneg : uval - cval < 0) :
    L * (uval - cval) <= Fu - Fc := by
  have hlow_abs : -(L * |uval - cval|) <= Fu - Fc := by
    exact le_trans (neg_le_neg hlip) (neg_abs_le (Fu - Fc))
  have hvabs : |uval - cval| = -(uval - cval) := abs_of_neg hneg
  calc
    L * (uval - cval) = -(L * |uval - cval|) := by
      rw [hvabs]
      ring
    _ <= Fu - Fc := hlow_abs

/-- Supersolution, ODE, and Lipschitz hypotheses imply `L v <= P v` on the
negative region, where `v = u - c`. -/
theorem negative_region_parabolic_lower_bound
    {uval cval Pu Pv cderiv Fu Fc L : Real}
    (hsuper : Fu <= Pu)
    (hode : cderiv = Fc)
    (hsub : Pv = Pu - cderiv)
    (hlip : |Fu - Fc| <= L * |uval - cval|)
    (hneg : uval - cval < 0) :
    L * (uval - cval) <= Pv := by
  have hlow : L * (uval - cval) <= Fu - Fc :=
    reaction_difference_lower_bound_on_negative_region hlip hneg
  have hupper : Fu - Fc <= Pv := by
    calc
      Fu - Fc <= Pu - cderiv := by
        rw [hode]
        exact sub_le_sub_right hsuper Fc
      _ = Pv := hsub.symm
  exact le_trans hlow hupper

/-! ## Calculus interfaces used by the maximum-principle assembly -/

/-- Spatial constants and the ordinary one-variable time derivative give
`P(u-c)=Pu-c'`.

Expected proof: use `derivWithin_sub` for the time derivative, then prove the
spatial identity from linearity of `gradientFun`, `divergence`, and the already
proved `gradientFun_const` / `laplacian_const` facts. The current realized
operator layer has the constant lemmas but not yet the full linearity API for
divergence and Laplacian. -/
theorem parabolic_sub_time_curve_identity
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (t : Real) (_ht : t ∈ Set.Icc 0 T) (x : M)
    (_hu : DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (_hc : DifferentiableWithinAt Real c (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => u s y - c s) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x -
        derivWithin c (Set.Icc 0 T) t := by
  sorry

/-- Exponential rescaling identity for `w = exp(-Lt) v`.

Expected proof: use `derivWithin_mul`, the derivative of `exp (-L*t)`, and the
spatial fact that the exponential factor is constant in the `M` variable, so the
heat operator scales by that factor. -/
theorem parabolic_exp_rescale_identity
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T L : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (v : Real -> M -> Real)
    (t : Real) (_ht : t ∈ Set.Icc 0 T) (x : M)
    (_hv : DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t)
    (_hscale : DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
      (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => Real.exp (-L * s) * v s y) t x =
      Real.exp (-L * t) *
        (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
  sorry

/-! ## Strict barrier maximum principle -/

/-- Strict-barrier form of the scalar weak maximum principle.

Expected proof: for each `ε > 0`, minimize `wε = w + εt` on the compact slab.
At a negative minimum, use the endpoint derivative test to get
`∂ₜ wε <= 0`, use `heatOperatorWithDrift_at_spatial_min_nonneg` to get the
spatial operator nonnegative, and contradict `P wε = P w + ε > 0`. -/
theorem strict_barrier_nonnegative
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (_hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (_hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (_hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  sorry

/-! ## Hamilton Theorem 7.1, first realized core -/

/-- Hamilton Theorem 7.1, realized core form with an already chosen Lipschitz
constant on the values of `u` and `c`.

The theorem is fully synthetic after the two explicit calculus identities and
the strict-barrier theorem: no global Ricci-flow black box is used. -/
theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hexpCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-L * s) * (u s y - c s)) t x =
        Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - L * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => Real.exp (-L * t) * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    simpa [w, v] using hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    have hexppos : 0 < Real.exp (-L * t) := Real.exp_pos _
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= Real.exp (-L * t) * v t x :=
        mul_nonneg (le_of_lt hexppos) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        L * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      exact negative_region_parabolic_lower_bound
        (hsuper t ht x)
        (hode t ht)
        (by simpa [v] using hsubCalc t ht x)
        (hlip t ht x)
        (by simpa [v] using hvneg)
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
        exact mul_nonneg (le_of_lt hexppos) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hexpCalc t ht x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T hT X w
      (by simpa [w, v] using hw_cont) hw0
      (by simpa [w, v] using hw_mdiff) (by simpa [w, v] using hw_grad)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)

/-- Textbook locally-Lipschitz wrapper for Hamilton Theorem 7.1.

Expected proof: use compactness of the slab and continuity of `u` and `c` to
put their values in a compact real interval, extract a uniform Lipschitz
constant from `LocallyLipschitz`, then apply
`scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values`. -/
theorem scalar_weak_maximum_principle_supersolutions_locallyLipschitz
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real)
    (_hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2) (spacetimeSlab (M := M) T))
    (_hc_cont : ContinuousOn c (Set.Icc 0 T))
    (_hF_local : forall t : Real, t ∈ Set.Icc 0 T ->
      LocallyLipschitz (fun a : Real => F a t))
    (_hF_mono : forall t : Real, t ∈ Set.Icc 0 T ->
      Monotone (fun a : Real => F a t))
    (_hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (_hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (_hinit : forall x : M, c 0 <= u 0 x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  sorry

end

end Realized
end RicciFlower
