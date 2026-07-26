import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04Reduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Producers for the `Rm04Reduction` input packages

`Evolution/Rm04Reduction.lean` proves the static reduction
`rm04VarRHS = Δ Rm − 2(B − B + B − B) − drift` from ten named inputs.  This module
discharges those inputs from a Ricci-flow solution `S` (and `hS`) alone.

Current content: the canonical coordinate-frame lowered-curvature component array
`rmComp`, and the discharge of the algebraic-symmetry package `Rm04Symm` for it.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- The canonical lowered-curvature component array of a Ricci-flow solution in the
coordinate frame centred at `x₀`, in the `FourComp` currency of `Evolution/Uhlenbeck.lean`.

This is `realizedRmBase` written with `vec4` instead of a `Fin 4` slot map, so that the
tensor-level curvature-symmetry producers of `Evolution/Ricci/Trace.lean` apply to it
directly. -/
def rmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  fun t x i j k l =>
    S.base.rm04 t x
      (DifferentialGeometry.Integral.Connection.vec4 (I := I)
        (coordinateFrameAt (I := I) x₀ i x) (coordinateFrameAt (I := I) x₀ j x)
        (coordinateFrameAt (I := I) x₀ k x) (coordinateFrameAt (I := I) x₀ l x))

/-- **`Rm04Symm` discharged from the solution.**  The algebraic curvature symmetries
— antisymmetry in each slot pair, pair symmetry, and the first Bianchi identity — hold
for `rmComp` at every regular time and every point, with `S` and `hS` as the only inputs.

This discharges the `hsym` package of `rm04Var_eq_uhl` (`Evolution/Rm04Reduction.lean`)
and the `Rm04Symm` argument of `rmQuad_eq_b`. -/
theorem rm04SymmOfSol
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    Rm04Symm (rmComp (I := I) S x₀ (t : Real) x) := by
  have hRm13 :
      ∀ τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
          (S.family.connection (τ : Real)) (S.base.rm13 (τ : Real)) :=
    fun τ => rm13OfSol (I := I) S (τ : Real) (D.regular_subset τ.2)
  have hLower :
      ∀ (τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
        (y : M),
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I)
          (S.family.metric (τ : Real)) y
          (S.base.rm13 (τ : Real) y) (S.base.rm04 (τ : Real) y) :=
    fun τ y => solution_rm04LowersRm13At (I := I) S (τ : Real) y
  have hskew :=
    rm04InputSkew_regular (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hpair :=
    rm04PairSymm_regular (I := I) S hS S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hbi :=
    rm04FirstBianchi_regular (I := I) S hS S.base.rm13 S.base.rm04 hRm13 hLower t x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    exact hskew (coordinateFrameAt (I := I) x₀ b x) (coordinateFrameAt (I := I) x₀ a x)
      (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)
  · intro a b c d
    calc rmComp (I := I) S x₀ (t : Real) x a b c d
        = rmComp (I := I) S x₀ (t : Real) x c d a b :=
          hpair (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
            (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)
      _ = -rmComp (I := I) S x₀ (t : Real) x d c a b :=
          hskew (coordinateFrameAt (I := I) x₀ d x) (coordinateFrameAt (I := I) x₀ c x)
            (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
      _ = -rmComp (I := I) S x₀ (t : Real) x a b d c :=
          neg_inj.mpr
            (hpair (coordinateFrameAt (I := I) x₀ d x)
              (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ a x)
              (coordinateFrameAt (I := I) x₀ b x))
  · intro a b c d
    exact hpair (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
      (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)
  · intro a b c d
    exact hbi (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
      (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)

end DifferentialGeometry.PDE.RicciFlow
