import RicciFlower.Realized.RicciFlow
import RicciFlower.Realized.Bochner
import RicciFlower.Realized.CurvatureTensor

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# RicciFlower Ricci-Flow Folder Entry Point

This file is the forward-facing Ricci-flow API.  The older
`RicciFlower.Realized.RicciFlow` module remains as a compatibility layer; this
folder-level module packages a solution as a realized metric family together
with bundled Ricci tensor sections.

The Section 6.2 evolution identities are introduced as explicit equation
predicates.  The current file records the interfaces and the algebraic
composition for Lemma 6.7; the geometric producers for Ricci/scalar evolution
are separate proof frontiers.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Ricci-flow solutions as metric families -/

/-- A time-dependent bundled Ricci tensor section. -/
abbrev RicciSectionFamily : Type _ :=
  Real -> Realized.Tensor02Section (I := I) (M := M)

namespace RicciSectionFamily

/-- View a bundled Ricci section family as the pointwise tensor field expected
by the compatibility `Realized.RicciFlow` API. -/
def toTensorField (Ric : RicciSectionFamily (I := I) (M := M)) :
    Realized.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (Realized.vec2 X Y)

@[simp] theorem toTensorField_apply
    (Ric : RicciSectionFamily (I := I) (M := M))
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    toTensorField (I := I) Ric t x X Y =
      Ric t x (Realized.vec2 X Y) := by
  rfl

end RicciSectionFamily

variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- A data-only Ricci-flow solution candidate on a real interval.

The solution is primarily a `RealizedMetricFamilyOn`; the bundled Ricci section
family is the right-hand side of the metric evolution equation. -/
structure SolutionOn (D : Realized.RealTimeInterval) where
  family : Realized.RealizedMetricFamilyOn (I := I) (M := M) D
  ricci : RicciSectionFamily (I := I) (M := M)

namespace SolutionOn

/-- Compatibility view as the older realized Ricci-flow candidate. -/
def toRealizedCandidate {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Realized.RealizedRicciFlowCandidateOn (I := I) (M := M) D where
  family := S.family
  ricci := RicciSectionFamily.toTensorField (I := I) S.ricci

@[simp] theorem toRealizedCandidate_family {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.toRealizedCandidate.family = S.family := by
  rfl

end SolutionOn

/-- The Ricci-flow metric equation for a folder-level solution:
`∂_t g = -2 Ric`, on the interval carrier and at regular times. -/
def MetricVariationEquationOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  Realized.MetricVariationEquationOn (I := I) S.family
    (RicciSectionFamily.toTensorField (I := I) S.ricci)

/-- Predicate package saying the folder-level candidate is a Ricci-flow
solution. -/
structure IsSolutionOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  smoothMetric : Realized.MetricFamilySmoothOn (I := I) (M := M) D S.family
  smoothConnection : RicciFlower.Connection.ConnectionFamilySmoothOn (I := I) (M := M) S.family
  leviCivita : RicciFlower.LeviCivita.IsLeviCivitaFamilyOn (I := I) S.family
  equation : MetricVariationEquationOn (I := I) S

/-- Convert the folder-level solution predicate to the older realized
compatibility predicate. -/
theorem isRealizedRicciFlowSolutionOn_of_isSolutionOn
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) :
    Realized.IsRealizedRicciFlowSolutionOn (I := I) S.toRealizedCandidate := by
  exact
    { smoothMetric := hS.smoothMetric
      smoothConnection := hS.smoothConnection
      leviCivita := hS.leviCivita
      equation := hS.equation }

/-- Extract the interval metric evolution equation from a folder-level solution. -/
theorem metric_derivWithin_eq_neg_two_ricci
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricci (t : Real) x (Realized.vec2 X Y))
      D.carrier
      (t : Real) := by
  simpa [MetricVariationEquationOn, RicciSectionFamily.toTensorField] using
    hS.equation t x X Y

/-! ## Section 6.2: Ricci and scalar evolution interfaces -/

section Components

variable {Idx : Type*} [Fintype Idx]

/-- Interpret the bundled Ricci section family as the pointwise two-tensor
field used by the coordinate Bochner layer. -/
def ricciTwoTensorField
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> Realized.TwoTensorField (I := I) (M := M) :=
  fun t x X Y => S.ricci t x (Realized.vec2 X Y)

@[simp] theorem ricciTwoTensorField_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    ricciTwoTensorField (I := I) S t x X Y =
      S.ricci t x (Realized.vec2 X Y) := by
  rfl

/-- Ricci component in a time-dependent frame. -/
def ricciCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  S.ricci t x (Realized.vec2 (frame i x) (frame j x))

@[simp] theorem ricciCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      S.ricci t x (Realized.vec2 (frame i x) (frame j x)) := by
  rfl

/-- Ricci with both indices raised:
`Ric^{ij} = g^{ia} g^{jb} Ric_ab`. -/
def raisedRicciCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv t x i a * gInv t x j b *
      ricciCompInFrame (I := I) S frame t x a b

@[simp] theorem raisedRicciCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b *
          ricciCompInFrame (I := I) S frame t x a b := by
  rfl

/-- Ricci with the second index raised:
`Ric_i^k = g^{ka} Ric_ia`. -/
def ricciOneUpCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a

@[simp] theorem ricciOneUpCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) :
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k =
      ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a := by
  rfl

/-- The quadratic term `Ric_i^k Ric_kj` from Lemma 6.3. -/
def ricciQuadraticCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      ricciCompInFrame (I := I) S frame t x k j

@[simp] theorem ricciQuadraticCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciQuadraticCompInFrame (I := I) S gInv frame t x i j =
      ∑ k : Idx,
        ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
          ricciCompInFrame (I := I) S frame t x k j := by
  rfl

/-- The curvature-Ricci contraction `R_ikjl Ric^{kl}` from Lemma 6.3. -/
def rmRicciContractionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
      raisedRicciCompInFrame (I := I) S gInv frame t x k l

@[simp] theorem rmRicciContractionCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl

/-- Component RHS for Lemma 6.3:
`Δ Ric_ij + 2 R_ikjl Ric^{kl} - 2 Ric_i^k Ric_kj`. -/
def ricciEvolutionRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapRic t x i j +
    2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
      2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem ricciEvolutionRHSInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j =
      roughLapRic t x i j +
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
          2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate Ricci norm square for a folder-level Ricci-flow solution. -/
def ricciNormSqInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      ricciCompInFrame (I := I) S frame t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem ricciNormSqInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate inner product `<roughDelta Ric, Ric>` for a folder-level
Ricci-flow solution. -/
def roughLapRicciInnerInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      roughLapRic t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem roughLapRicciInnerInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate squared norm of `nabla Ric`. -/
def nablaRicciNormSqInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv t x a b * gInv t x i k * gInv t x j l *
        nablaRic t x a i j * nablaRic t x b k l

@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (t : Real) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl

/-- The curvature-Ricci-Ricci term `R_ikjl Ric^ij Ric^kl`. -/
def curvRicciRicciInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l

@[simp] theorem curvRicciRicciInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j *
            raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl

/-- The inverse-metric part of the Ricci-flow metric evolution:
`partial_t g^{ij} = 2 Ric^{ij}`.  The future geometric proof differentiates
`g^{ik} g_kj = delta^i_j` and uses `partial_t g_ij = -2 Ric_ij`. -/
def inverseMetricEvolutionRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j

/-- Component equation `partial_t g^{ij} = 2 Ric^{ij}`. -/
def InverseMetricEvolutionEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Product-rule RHS for differentiating `Ric^{ij}`. -/
def raisedRicciDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i a *
        gInv t x j b * ricciCompInFrame (I := I) S frame t x a b +
      gInv t x i a *
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x j b *
          ricciCompInFrame (I := I) S frame t x a b +
        gInv t x i a * gInv t x j b *
          ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x a b)

/-- Product-rule RHS for differentiating `|Ric|^2 = Ric_ij Ric^ij`. -/
def ricciNormDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j +
      ricciCompInFrame (I := I) S frame t x i j *
        raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)

/-- The remaining finite-sum simplification in Lemma 6.7.

This is the explicit cancellation/reindexing frontier: after the product rule,
the inverse-metric variation terms cancel the `-2 Ric_i^k Ric_kj` part of
Lemma 6.3, leaving `2 <roughDelta Ric, Ric> + 4 R_ikjl Ric^ij Ric^kl`. -/
def RicciNormDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x

/-- Lemma 6.3 in component/equation form.  This is the geometric frontier
needed before the norm evolution proof can be made constructive. -/
def RicciEvolutionEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Project the inverse-metric evolution equation at fixed components. -/
theorem inverseMetricEvolutionEquationInFrame_apply
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {gInv : Real -> Realized.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    (h : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x i j

/-- Constructor for the inverse-metric evolution equation from component
derivative equalities. -/
theorem inverseMetricEvolutionEquationInFrame_of_components
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => gInv s x i j)
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame :=
  h

/-- Project Lemma 6.3's component equation at fixed components. -/
theorem ricciEvolutionEquationInFrame_apply
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)}
    {gInv : Real -> Realized.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    {roughLapRic : Real -> M -> Idx -> Idx -> Real}
    (h : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x i j

/-- Constructor for Lemma 6.3's component equation from component derivative
equalities. -/
theorem ricciEvolutionEquationInFrame_of_components
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h : ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic :=
  h

/-- Product-rule derivative of the raised Ricci components. -/
theorem raisedRicciCompInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [raisedRicciCompInFrame, raisedRicciDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun a s =>
        ∑ b : Idx,
          gInv s x i a * gInv s x j b *
            ricciCompInFrame (I := I) S frame s x a b)
      (A' := fun a =>
        ∑ b : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i a *
              gInv (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
            gInv (t : Real) x i a *
              inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
              gInv (t : Real) x i a * gInv (t : Real) x j b *
                ricciEvolutionRHSInFrame
                  (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
      (s := D.carrier) (x := (t : Real))
      (fun a _ha =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s =>
                gInv s x i a * gInv s x j b *
                  ricciCompInFrame (I := I) S frame s x a b)
              (A' := fun b =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i a *
                    gInv (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                  gInv (t : Real) x i a *
                    inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                    gInv (t : Real) x i a * gInv (t : Real) x j b *
                      ricciEvolutionRHSInFrame
                        (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                by
                  have hia := h_inv t x i a
                  have hjb := h_inv t x j b
                  have hrab := h_ricci t x a b
                  have hprod := (hia.mul hjb).mul hrab
                  simpa [Pi.mul_apply, mul_assoc, add_mul] using hprod))))

/-- Product-rule derivative of the coordinate Ricci norm square. -/
theorem ricciNormSqInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) :
    HasDerivWithinAt
      (fun s : Real => ricciNormSqInFrame (I := I) S gInv frame s x)
      (ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [ricciNormSqInFrame, ricciNormDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          ricciCompInFrame (I := I) S frame s x i j *
            raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
              raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
            ricciCompInFrame (I := I) S frame (t : Real) x i j *
              raisedRicciDerivRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                ricciCompInFrame (I := I) S frame s x i j *
                  raisedRicciCompInFrame (I := I) S gInv frame s x i j)
              (A' := fun j =>
                (ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
                    raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
                  ricciCompInFrame (I := I) S frame (t : Real) x i j *
                    raisedRicciDerivRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hRic := h_ricci t x i j
                  have hRaised :=
                    raisedRicciCompInFrame_hasDerivWithinAt
                      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x i j
                  have hprod := hRic.mul hRaised
                  simpa [Pi.mul_apply] using hprod))))

end Components

/-- Scalar curvature evolution in Section 6.2:
`∂_t R = Δ R + 2 |Ric|²`. -/
def ScalarEvolutionEquationOn
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (scalarLap (t : Real) x + 2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-! ## Lemma 6.7: Ricci norm heat equation, component assembly -/

/-- Time derivative component identity for `|Ric|²`.

This is the point where differentiating inverse metrics and using Lemma 6.3 has
already cancelled the cubic `Ric_i^k Ric_kj` terms. -/
def RicciNormTimeDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (ricciNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x)
      D.carrier
      (t : Real)

section RicciNormDerivative

variable {Idx : Type*} [Fintype Idx]

/-- The time-derivative identity for `|Ric|^2` once the component evolution
equations and the remaining finite-sum simplification are supplied. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_simplify : RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic roughLapInner reaction) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      roughLapInner reaction := by
  intro t x
  have hnorm :=
    ricciNormSqInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x
  simpa [h_simplify t x] using hnorm

end RicciNormDerivative

/-- Laplacian component identity for `|Ric|²`:
`Δ |Ric|² = 2 <Δ Ric, Ric> + 2 |∇Ric|²`. -/
def RicciNormLaplacianComponentsOn
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x

/-- Bridge from the realized Bochner coordinate predicate to the interval
Ricci-flow predicate. -/
theorem ricciNormLaplacianComponentsOn_of_bochner
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real)
    (h_lap : Realized.RicciNormLaplacianComponentsInFrame
      (M := M) (Time := Real) ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormLaplacianComponentsOn ricciNormLap roughLapInner nablaRicNormSq :=
  h_lap

/-- Heat-equation form of Lemma 6.7:
`∂_t |Ric|² = Δ |Ric|² - 2 |∇Ric|² + 4 R_ikjl Ric^{ij} Ric^{kl}`. -/
def RicciNormHeatEquationOn
    {D : Realized.RealTimeInterval}
    (ricciNormSq ricciNormLap nablaRicNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (ricciNormLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x))
      D.carrier
      (t : Real)

/-- Algebraic assembly of Lemma 6.7 from the time-derivative and Laplacian
component identities. -/
theorem ricciNormHeatEquationOn_of_components
    {D : Realized.RealTimeInterval}
    (ricciNormSq ricciNormLap roughLapInner nablaRicNormSq reaction : Real -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsOn
      (D := D) ricciNormSq roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction := by
  intro t x
  have hvalue :
      ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x

section RicciNormAssembly

variable {Idx : Type*} [Fintype Idx]

/-- Section 6.2 Ricci-norm heat identity for a folder-level solution, reduced
to the named inverse-metric, Ricci-evolution, finite-sum simplification, and
Bochner Laplacian component frontiers. -/
theorem ricciNormHeatEquationOn_of_solution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap roughLapInner nablaRicNormSq reaction : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_simplify : RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap nablaRicNormSq reaction := by
  exact
    ricciNormHeatEquationOn_of_components
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap roughLapInner nablaRicNormSq reaction
      (ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
        (I := I) S Rm04 gInv frame roughLapRic roughLapInner reaction
        h_inv h_ricci h_simplify)
      h_lap

end RicciNormAssembly

end RicciFlow
end RicciFlower
