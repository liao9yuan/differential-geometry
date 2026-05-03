import DifferentialGeometry.Synthetic.Realization.Coordinates.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Christoffel Symbols in a Local Frame

Mathlib's bundled covariant derivative has argument order
`cov sigma x v = (nabla_v sigma)(x)`. Given a local frame `frame i`, the
Christoffel coefficient is the `k`-th frame coefficient of
`nabla_{frame i} frame j`:

`Gamma^k_{ij}(x) = coeff_k ((cov (frame j) x) (frame i x))`.

The definitions below are frame-based. Coordinate charts can supply their
coordinate frame later, while arbitrary local frames already support the
normal-coordinate and connection-variation APIs needed for local calculations.

For a fixed frame, the Christoffel symbol as a scalar function is simply
`fun x => christoffelSymbolInFrame cov frame hframe x i j k`; this file avoids
separate currying wrappers.
-/

noncomputable section

open Bundle Module
open scoped BigOperators Manifold ContDiff

section FrameChristoffel

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {ι : Type*}
  {u : Set M}

/-- Christoffel coefficients in a local frame:
`Gamma^k_{ij}(x) = coeff_k(nabla_{frame_i} frame_j)`. -/
noncomputable def christoffelSymbolInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : ι) : Real :=
  hframe.coeff k x ((cov (frame j) x) (frame i x))

theorem christoffelSymbolInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : ι) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      hframe.coeff k x ((cov (frame j) x) (frame i x)) := by
  rfl

/-- Expansion of `nabla_{frame i} frame j` in the local frame. -/
theorem covariantDerivative_eq_sum_christoffel
    [Fintype ι]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : ι) :
    (cov (frame j) x) (frame i x) =
      ∑ k, christoffelSymbolInFrame cov frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq (fun y => (cov (frame j) y) (frame i y)) hx

/-- A local frame has vanishing Christoffel symbols at a point. This is the
normal-coordinate condition on the connection part of the frame. -/
def ChristoffelSymbolsVanishAtFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) : Prop :=
  forall i j k : ι, christoffelSymbolInFrame cov frame hframe x i j k = 0

section Difference

variable [FiniteDimensional Real E]
  [VectorBundle Real E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

/-- Components of the tensorial connection difference `cov - cov'` in a local frame.

This is deliberately not defined as the pointwise subtraction of Christoffel
symbols. `CovariantDerivative.difference cov cov'` is tensorial in the section
slot and can be evaluated pointwise. The theorem
`christoffelSymbolDifferenceInFrame_eq_sub` identifies it with
`Gamma(cov) - Gamma(cov')` when the acted-on frame section is differentiable at
the point. -/
noncomputable def christoffelSymbolDifferenceInFrame
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : ι) : Real :=
  hframe.coeff k x (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))

/-- Expansion of the connection-difference tensor in the local frame. -/
theorem christoffelSymbolDifference_expansion
    [Fintype ι]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : ι) :
    ((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x) =
      ∑ k, christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq
    (fun y => ((CovariantDerivative.difference cov cov' y) (frame j y)) (frame i y)) hx

/-- If the frame vector `frame j` is differentiable at `x`, the tensorial
connection-difference coefficient agrees with the pointwise subtraction
`Gamma(cov) - Gamma(cov')`. -/
theorem christoffelSymbolDifferenceInFrame_eq_sub
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : ι)
    (hframe_j : MDiffAt (T% (frame j)) x) :
    christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov' frame hframe x i j k := by
  unfold christoffelSymbolDifferenceInFrame christoffelSymbolInFrame
  change hframe.coeff k x
      (((cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv x)
        (frame j x)) (frame i x)) =
    hframe.coeff k x ((cov (frame j) x) (frame i x)) -
      hframe.coeff k x ((cov' (frame j) x) (frame i x))
  rw [IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := frame j) (x := x) (hx := by trivial) hframe_j]
  simp

end Difference

end FrameChristoffel

end
