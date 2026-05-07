import RicciFlower.Realized.Curvature
import RicciFlower.Realized.Operators
import RicciFlower.Coordinates.Tensor
import RicciFlower.Tensor.RSTensor.TensorRSRiemannian
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

/-! ## Pointwise metric tensor norms -/

section TensorInner

variable [FiniteDimensional Real E]

private noncomputable instance tangentSpace_addCommMonoid (x : M) :
    AddCommMonoid (TangentSpace I x) :=
  inferInstanceAs (AddCommMonoid E)

private noncomputable instance tangentSpace_module (x : M) :
    Module Real (TangentSpace I x) :=
  inferInstanceAs (Module Real E)

/-- A pointwise covariant two-tensor on `T_x M`. -/
abbrev Tensor02At (x : M) :=
  ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real

/-- A time-dependent covariant two-tensor field. -/
abbrev Tensor02Field :=
  Time -> (x : M) -> Tensor02At (I := I) x

/-- The metric inner product on cotangent vectors:
`<alpha,beta>_{g^{-1}} = g(alpha^#, beta^#)`. -/
def cotInner
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha beta : Module.Dual Real (TangentSpace I x)) : Real :=
  g.inner x (metricSharp (I := I) g x alpha) (metricSharp (I := I) g x beta)

@[simp] theorem cotInner_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha beta : Module.Dual Real (TangentSpace I x)) :
    cotInner (I := I) g x alpha beta =
      g.inner x (metricSharp (I := I) g x alpha) (metricSharp (I := I) g x beta) := by
  rfl

/-- Linear version of the metric-induced inner product on cotangent vectors. -/
def cotInnerLinear
    (g : SmoothRiemannianMetric I M) (x : M) :
    Module.Dual Real (TangentSpace I x) →ₗ[Real]
      Module.Dual Real (TangentSpace I x) →ₗ[Real] Real where
  toFun alpha :=
    { toFun := fun beta => beta (metricSharp (I := I) g x alpha)
      map_add' beta gamma := by
        simp
      map_smul' c beta := by
        simp }
  map_add' alpha beta := by
    ext gamma
    simp [metricSharp, map_add]
  map_smul' c alpha := by
    ext beta
    simp [metricSharp]

@[simp] theorem cotInnerLinear_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha beta : Module.Dual Real (TangentSpace I x)) :
    cotInnerLinear (I := I) g x alpha beta =
      beta (metricSharp (I := I) g x alpha) := by
  rfl

/-- For a `(0,2)` tensor `T`, fix the first argument and view the second slot
as a covector. -/
def covRight02
    {x : M} (T : Tensor02At (I := I) x) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  (ContinuousLinearMap.coeLM Real).comp
    (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).toLinearEquiv).toLinearMap.comp
      T.curryLeft.toLinearMap)

/-- For a `(0,2)` tensor `T`, fix the second argument and view the first slot
as a covector. -/
def covLeft02
    {x : M} (T : Tensor02At (I := I) x) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  (ContinuousLinearMap.coeLM Real).comp
    ((ContinuousLinearMap.flip
      ((continuousMultilinearCurryFin1 Real (TangentSpace I x)
          (TangentSpace I x →L[Real] Real)) T.curryRight)).toLinearMap)

/-- Raise the second covariant index of a `(0,2)` tensor. -/
def raiseRight02
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor02At (I := I) x) :
    TangentSpace I x →ₗ[Real] TangentSpace I x :=
  (metricFlatEquiv (I := I) g x).symm.toLinearMap.comp (covRight02 (I := I) T)

/-- Raise the first covariant index of a `(0,2)` tensor. -/
def raiseLeft02
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor02At (I := I) x) :
    TangentSpace I x →ₗ[Real] TangentSpace I x :=
  (metricFlatEquiv (I := I) g x).symm.toLinearMap.comp (covLeft02 (I := I) T)

/-- First-principles metric inner product on covariant two-tensors.

This follows the definition from the metric-induced inner product on `V*` and
bilinear extension. Equivalently, for two `(0,2)` tensors it is the trace of
the composition obtained by raising the first index of one tensor and the
second index of the other. -/
def inner02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor02At (I := I) x) : Real :=
  Tensor0SBundle.inner0S (I := I) (M := M) g x 2 A B

/-- Squared norm of a covariant two-tensor from the metric inner product. -/
def normSq02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor02At (I := I) x) : Real :=
  inner02 (I := I) g x A A

@[simp] theorem normSq02_eq_inner02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor02At (I := I) x) :
    normSq02 (I := I) g x A = inner02 (I := I) g x A A := by
  rfl

/-- Pointwise norm square of a time-dependent `(0,2)` tensor field. -/
def tensorNormSq02
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A : Tensor02Field (I := I) (M := M) (Time := Time)) :
    Time -> M -> Real :=
  fun t x => normSq02 (I := I) (G.metric t) x (A t x)

/-- Components of a `(0,2)` tensor in a frame. -/
def tensor02Comp
    {Idx : Type*}
    (A : Tensor02Field (I := I) (M := M) (Time := Time))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) : Real :=
  A t x (fun a => if a = 0 then frame i x else frame j x)

/-- Coordinate contraction formula for the first-principles `(0,2)` tensor
inner product. This is the bridge that should be proved from the local-frame
basis expansion and the inverse metric identities. -/
theorem inner02_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A B : Tensor02Field (I := I) (M := M) (Time := Time))
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrame (I := I) G gInv frame)
    (t : Time) {x : M} (_hx : x ∈ u) :
    inner02 (I := I) (G.metric t) x (A t x) (B t x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x i k * gInv t x j l *
          tensor02Comp (I := I) A frame t x i j *
            tensor02Comp (I := I) B frame t x k l := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInFrame (I := I) (M := M) (G.metric t) x
        (fun i : Idx => frame i x) (fun i j : Idx => gInv t x i j) := by
    intro i j
    exact hinv t x i j
  exact Tensor0SBundle.inner0S_two_eq_coord (I := I) (M := M) (G.metric t) x
    (fun i : Idx => frame i x) (fun i j : Idx => gInv t x i j) hinvAt
    (A t x) (B t x)

/-- Coordinate formula for the first-principles squared norm. -/
theorem normSq02_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A : Tensor02Field (I := I) (M := M) (Time := Time))
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrame (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    tensorNormSq02 (I := I) G A t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x i k * gInv t x j l *
          tensor02Comp (I := I) A frame t x i j *
            tensor02Comp (I := I) A frame t x k l := by
  unfold tensorNormSq02 normSq02
  exact inner02_eq_coord (I := I) G A A gInv frame hframe hinv t hx

end TensorInner

/-! ## General coordinate Bochner data -/

section GeneralTensorNorm

variable {Comp Dir : Type*} [Fintype Comp] [Fintype Dir]

/-- A weighted coordinate squared norm for a tensor component list.

The finite component type `Comp` is deliberately abstract. For a concrete
covariant tensor, `weight` packages the appropriate inverse-metric contractions
for the chosen frame and slot convention.

This is only a finite-sum algebra helper for coordinate calculations. The
first-principles `(0,2)` metric norm is `normSq02`, with coordinate evaluation
given by `normSq02_eq_coord`. -/
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

