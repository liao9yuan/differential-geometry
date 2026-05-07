import RicciFlower.Realized.Curvature
import RicciFlower.Realized.Operators

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Coordinate Bochner Formulae

This file contains the coordinate-facing Bochner consumers needed for the
Ricci-norm evolution calculation.

The geometric producer statements are kept explicit: this file does not prove
that a scalar Laplacian or a rough tensor Laplacian has a particular coordinate
expression.  Once those expressions are supplied, the Bochner identities below
are finite-sum algebra.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

/-! ## General coordinate Bochner data -/

section GeneralTensorNorm

variable {Comp Dir : Type*} [Fintype Comp] [Fintype Dir]

/-- A weighted coordinate squared norm for a tensor component list.

The finite component type `Comp` is deliberately abstract. For a concrete
covariant tensor, `weight` packages the appropriate inverse-metric contractions
for the chosen frame and slot convention. -/
def tensorNormSqInFrame
    (weight component : Time -> M -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x => ∑ I : Comp, weight t x I * component t x I * component t x I

@[simp] theorem tensorNormSqInFrame_apply
    (weight component : Time -> M -> Comp -> Real)
    (t : Time) (x : M) :
    tensorNormSqInFrame (M := M) weight component t x =
      ∑ I : Comp, weight t x I * component t x I * component t x I := by
  rfl

/-- Coordinate inner product of a rough Laplacian component with the tensor. -/
def roughLapTensorInnerInFrame
    (weight roughLap component : Time -> M -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x => ∑ I : Comp, weight t x I * roughLap t x I * component t x I

@[simp] theorem roughLapTensorInnerInFrame_apply
    (weight roughLap component : Time -> M -> Comp -> Real)
    (t : Time) (x : M) :
    roughLapTensorInnerInFrame (M := M) weight roughLap component t x =
      ∑ I : Comp, weight t x I * roughLap t x I * component t x I := by
  rfl

/-- Coordinate squared norm of the covariant derivative of a tensor.

The finite direction type `Dir` represents the traced derivative direction.
Any inverse-metric factors for that trace are included in `weight`. -/
def nablaTensorNormSqInFrame
    (weight : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x =>
    ∑ a : Dir, ∑ I : Comp,
      weight t x I * nablaComponent t x a I * nablaComponent t x a I

@[simp] theorem nablaTensorNormSqInFrame_apply
    (weight : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real)
    (t : Time) (x : M) :
    nablaTensorNormSqInFrame (M := M) weight nablaComponent t x =
      ∑ a : Dir, ∑ I : Comp,
        weight t x I * nablaComponent t x a I * nablaComponent t x a I := by
  rfl

/-- The supplied scalar Laplacian of `|T|^2` realizes the coordinate Bochner
product expansion. This is the geometric bridge left explicit in this pass. -/
def ScalarLaplacianRealizesTensorNormBochnerInFrame
    (lapNormSq : Time -> M -> Real)
    (weight roughLap component : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real) : Prop :=
  forall (t : Time) (x : M),
    lapNormSq t x =
      (∑ I : Comp, 2 * (weight t x I * roughLap t x I * component t x I)) +
        (∑ a : Dir, ∑ I : Comp,
          2 * (weight t x I * nablaComponent t x a I * nablaComponent t x a I))

/-- Named Bochner product-rule conclusion for tensor norms. -/
def TensorNormBochnerComponentsInFrame
    (lapNormSq roughLapInner nablaNormSq : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    lapNormSq t x = 2 * roughLapInner t x + 2 * nablaNormSq t x

/-- Finite-sum proof of the coordinate Bochner product rule. -/
theorem tensorNormBochnerComponentsInFrame_of_coordinate_expansion
    (lapNormSq : Time -> M -> Real)
    (weight roughLap component : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real)
    (h_lap : ScalarLaplacianRealizesTensorNormBochnerInFrame
      (M := M) lapNormSq weight roughLap component nablaComponent) :
    TensorNormBochnerComponentsInFrame
      lapNormSq
      (roughLapTensorInnerInFrame (M := M) weight roughLap component)
      (nablaTensorNormSqInFrame (M := M) weight nablaComponent) := by
  intro t x
  rw [h_lap t x]
  unfold roughLapTensorInnerInFrame nablaTensorNormSqInFrame
  let roughTerm : Comp -> Real :=
    fun I => weight t x I * roughLap t x I * component t x I
  let nablaTerm : Dir -> Comp -> Real :=
    fun a I => weight t x I * nablaComponent t x a I * nablaComponent t x a I
  change
      (∑ I : Comp, 2 * roughTerm I) +
          (∑ a : Dir, ∑ I : Comp, 2 * nablaTerm a I) =
        2 * (∑ I : Comp, roughTerm I) +
          2 * (∑ a : Dir, ∑ I : Comp, nablaTerm a I)
  have hrough :
      (∑ I : Comp, 2 * roughTerm I) = 2 * (∑ I : Comp, roughTerm I) := by
    rw [Finset.mul_sum]
  have hnabla :
      (∑ a : Dir, ∑ I : Comp, 2 * nablaTerm a I) =
        2 * (∑ a : Dir, ∑ I : Comp, nablaTerm a I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [hrough, hnabla]

/-- Consume the named Bochner product-rule conclusion. -/
theorem tensor_norm_laplacian_eq_of_bochner_components
    (lapNormSq roughLapInner nablaNormSq : Time -> M -> Real)
    (h : TensorNormBochnerComponentsInFrame lapNormSq roughLapInner nablaNormSq)
    (t : Time) (x : M) :
    lapNormSq t x = 2 * roughLapInner t x + 2 * nablaNormSq t x :=
  h t x

end GeneralTensorNorm

/-! ## Ricci-specific coordinate quantities -/

section RicciNorm

variable {Idx : Type*} [Fintype Idx]

/-- Components of Ricci with both indices raised:
`Ric^{ij} = g^{ia} g^{jb} Ric_ab`. -/
def raisedRicciComponentsInFrame
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Idx -> Idx -> Real :=
  fun t x i j =>
    ∑ a : Idx, ∑ b : Idx,
      gInv t x i a * gInv t x j b * Ric t x (frame a x) (frame b x)

@[simp] theorem raisedRicciComponentsInFrame_apply
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) :
    raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b * Ric t x (frame a x) (frame b x) := by
  rfl

/-- Coordinate squared norm of Ricci:
`|Ric|^2 = Ric_ij Ric^{ij}`. -/
def ricciNormSqInFrame
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      Ric t x (frame i x) (frame j x) *
        raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j

@[simp] theorem ricciNormSqInFrame_apply
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    ricciNormSqInFrame (I := I) Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        Ric t x (frame i x) (frame j x) *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
  rfl

/-- Coordinate inner product `<roughDelta Ric, Ric>`. -/
def roughLapRicciInnerInFrame
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      roughLapRic t x i j *
        raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j

@[simp] theorem roughLapRicciInnerInFrame_apply
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    roughLapRicciInnerInFrame (I := I) roughLapRic Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
  rfl

/-- Coordinate squared norm of `nabla Ric`:
`g^{ab} g^{ik} g^{jl} (nabla_a Ric_ij) (nabla_b Ric_kl)`. -/
def nablaRicciNormSqInFrame
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx) :
    Time -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv t x a b * gInv t x i k * gInv t x j l *
        nablaRic t x a i j * nablaRic t x b k l

@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (t : Time) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl

/-- The cubic curvature-Ricci-Ricci reaction
`R_ikjl Ric^{ij} Ric^{kl}` in the frame convention fixed in
`Curvature.lean`. -/
def curvRicciRicciReactionInFrame
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (RicRaised : Time -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      Riemann04 t x (frame i x) (frame k x) (frame j x) (frame l x) *
        RicRaised t x i j * RicRaised t x k l

@[simp] theorem curvRicciRicciReactionInFrame_apply
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (RicRaised : Time -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    curvRicciRicciReactionInFrame (I := I) Riemann04 RicRaised frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Riemann04 t x (frame i x) (frame k x) (frame j x) (frame l x) *
          RicRaised t x i j * RicRaised t x k l := by
  rfl

/-- Time-derivative component identity for the Ricci norm.

This is the point at which the inverse-metric variation terms and the
`-2 Ric_i^k Ric_kj` part of Ricci evolution are assumed to have cancelled. -/
def RicciNormTimeDerivativeComponentsInFrame
    (ricciNormDt roughLapInner reaction : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormDt t x = 2 * roughLapInner t x + 4 * reaction t x

/-- Laplacian component identity for the Ricci norm, i.e. the Bochner product
rule specialized to Ricci. -/
def RicciNormLaplacianComponentsInFrame
    (ricciNormLap roughLapInner nablaRicNormSq : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x

/-- Lemma 6.7 in coordinate-component form:
`(partial_t - Delta)|Ric|^2 = -2 |nabla Ric|^2 + 4 R_ikjl Ric^ij Ric^kl`. -/
theorem ricci_norm_heat_eq_of_bochner_components
    (ricciNormDt ricciNormLap roughLapInner nablaRicNormSq reaction : Time -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsInFrame
      ricciNormDt roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsInFrame
      ricciNormLap roughLapInner nablaRicNormSq) :
    forall (t : Time) (x : M),
      ricciNormDt t x - ricciNormLap t x =
        -2 * nablaRicNormSq t x + 4 * reaction t x := by
  intro t x
  rw [h_dt t x, h_lap t x]
  ring

end RicciNorm

end

end Realized
end RicciFlower
