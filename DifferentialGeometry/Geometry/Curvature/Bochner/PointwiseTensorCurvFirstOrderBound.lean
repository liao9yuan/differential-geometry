import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FixedFieldThirdOrderCommutator
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceIntertwining
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldFiberEnergy
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Geometry.Curvature.Order2Defect.FrozenFrameTrace
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval

/-!
# The first-order curvature fibre bound of the order-`2` commutator defect

For a closed smooth Riemannian manifold `(M, g)` this file proves the **first-order** pointwise
fibre bound of the order-`2` commutator defect
```
Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)
```
(`∇S := covGrad g 0 s S`, a `(0, s + 1)`-tensor field): there are uniform constants `K_R, K_dR ≥ 0`
such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, and point `x`,
```
√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x)).
```
The defect is **first-order**: it carries the value `∇S` and the tensor `S` only, *not* `∇²S`. The
`∇²S`-order terms that appear in any per-direction expansion of the defect cancel under the metric
trace (see below), so the genuine commutator is a curvature contraction of `(∇S, S)` alone.

## Why the bound is first-order (the `∇²S`-elimination)

The rough Laplacian is the metric trace of the second covariant derivative,
`Δ_∇ T (x) = ∑ₐ ∇²_{Vₐ, Vₐ} T (x)`
(`rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`), so by the metric-compatibility
intertwining `metricTrace2_covDeriv_comm_map` the outer covariant gradient passes through the trace
with the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` *frozen* at `x`:
```
Curv S (x) = ∑ᵢ [ ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇(∇²_{Bᵢ, Bᵢ} S)(x) ].
```
The per-frame third-order difference is the seven-term curvature carrier
`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`: two genuinely differentiated curvature
terms `R(Bᵢ, ·)(∇_{Bᵢ} S)`, `∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `R(∇S)` and `(∇R) S` contractions, genuinely
`rfns(∇S)` / `rfns(S)`-order), three curvature-operator terms
`R(∇_{Bᵢ} ·, Bᵢ) S`, `R(·, ∇_{Bᵢ} Bᵢ) S`, `−∇_{R(Bᵢ, ·) Bᵢ} S` (`rfns(S)` / `rfns(∇S)`-order), and the
symmetric `∇²S`-order pair `−∇²_{∇_· Bᵢ, Bᵢ} S − ∇²_{Bᵢ, ∇_· Bᵢ} S`. The `∇²S`-order pair *cancels in
the frame sum* `∑ᵢ`: expanding `∇_· Bᵢ = ∑ⱼ aᵢⱼ Bⱼ` with `aᵢⱼ := g(∇_· Bᵢ, Bⱼ)` antisymmetric
(`smoothOrthoFrame_cov_skew` / `cometric_skew_core`, `∇g = 0` on the orthonormal frame), the pair
becomes `∑ᵢⱼ aᵢⱼ (∇²_{Bⱼ, Bᵢ} S + ∇²_{Bᵢ, Bⱼ} S)`, an antisymmetric coefficient against a
swap-symmetric Hessian, hence `0`. So no `∇²S` survives; the genuine defect is the curvature
contraction of `(∇S, S)`.

## The carried debt

The frame-summed `∇²S`-cancellation above is the genuine moving-frame third-order
Bochner–Weitzenböck content (the project's known frame-free curvature debt). It is the *pointwise*
form of the (now-discarded) integrated nullity — the per-`x` `∇²S`-free fibre bound. It is carried
here as the single honest leaf `pointwiseTensorCurv_fiberNormSq_le_first_order`: the per-point
first-order fibre bound parameterised by the **existing** uniform curvature sups (the pure-`R` sup
`exists_uniform_genuineCurvTracePureR_fiberNormSq_bound` and the differentiated-curvature /
Ricci-trace operator-field sups), so the uniformisation over the compact manifold is free. The
genuine mathematical content of the leaf is exactly the seven-term frame-sum assembly with the
antisymmetric `∇²S`-pair cancelled; everything above it — the `∃`-uniformisation and the integrated
cross-bound — is proved here.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s`
raises the tensor rank from `(0, s)` to `(0, s + 1)`. All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Entry reduction.** The intrinsic fibre norm of any `(0, s + 1)`-tensor `T` at `x` is the
frame sum, over the smooth `g_x`-orthonormal frame `Bₐ := smoothOrthoFrame g x a x` read in the
gradient (slot-`0`) direction, of the `(0, s)`-fibre norms of the wrapped slot-`0` curry slices
`Trₐ := tensor0SAsRS x (tensor0S_curry s x (T (unit)) (Bₐ))`:
```
rfns(T)(x) = ∑ₐ rfns( tensor0SAsRS x (tensor0S_curry s x (T (unit)) (Bₐ)) ).
```
This is `riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame` at the smooth-frame values
`Bₐ` (orthonormal at `x`, with both Parseval representations supplied by
`rfns_eq_sum_fiberNormSqSummand_of_orthoFrame`), rewritten through the slot-`0`-curry bridge
`slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec`. -/
private lemma rfns_succ_eq_sum_curry_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
      ∑ a : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (slot0Curry (I := I) (M := M) g x s
            (fun a => smoothOrthoFrame (I := I) g x a x) (fun k : Fin 0 => k.elim0) T a) := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he
  have hn : (Module.finrank ℝ E) = Module.finrank ℝ (TangentSpace I x) := rfl
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin s → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x 0 s S (Module.finrank ℝ E) e K J := fun S =>
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x S e hn horth
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S (Module.finrank ℝ E) e K J := fun S =>
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (s + 1) x S e hn horth
  exact riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g s x e
    (fun k : Fin 0 => k.elim0) hreprS hreprSucc T

/-- **Wrapper extensionality on model tuples.** Two `(0, t)`-tensors agreeing on every model
tuple are equal. -/
private lemma tensor0S_eq_of_toModel_eq' {t : ℕ} {x : M} {T T' : Tensor0SSpace t I x}
    (h : ∀ v : Fin t → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' :=
  Tensor0SSpace.toModel_injective (ContinuousMultilinearMap.ext h)

/-- The scalar-extraction functional evaluates to `1` on the unit `(0, 0)`-tensor. -/
private lemma tensor00Scalar_unitZeroSec' (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

/-- Every `(0, 0)`-tensor is its unit-scalar multiple of the unit `(0, 0)`-tensor. -/
private lemma tensor0S_zero_span' (x : M) (τ : Tensor0SSpace 0 I x) :
    τ = tensor00Scalar (I := I) (M := M) x τ • unitZeroSec (I := I) (M := M) x := by
  apply tensor0S_eq_of_toModel_eq' (I := I) (M := M)
  intro v
  rw [show v = (fun k : Fin 0 => k.elim0) from funext (fun k => k.elim0)]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
      (fun k : Fin 0 => k.elim0) = 1 from by
    rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.constOfIsEmpty_apply]]
  rw [show Tensor0SSpace.toModel τ (fun k : Fin 0 => k.elim0) =
      tensor00Scalar (I := I) (M := M) x τ from
    (tensor00Scalar_apply (I := I) (M := M) x τ (fun k : Fin 0 => k.elim0)).symm]
  rw [smul_eq_mul, mul_one]

/-- **Wrapping the unit evaluation of a `(0, t)`-Hom-tensor reconstructs the tensor.**
`tensor0SAsRS x ((W : Tensor0SSpace 0 →L Tensor0SSpace t) (unit)) = W`. -/
private lemma tensor0SAsRS_unit_recover (t : ℕ) (x : M) (W : TensorRSSpace 0 t I x) :
    tensor0SAsRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) = W := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
            (unitZeroSec (I := I) (M := M) x))) τ =
      tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  conv_rhs => rw [tensor0S_zero_span' (I := I) (M := M) x τ]
  rw [ContinuousLinearMap.map_smul]

/-- **The `(0, t)`-tensor wrapper distributes over subtraction.** -/
private lemma tensor0SAsRS_sub' (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C - D) =
      tensor0SAsRS (I := I) (M := M) x C - tensor0SAsRS (I := I) (M := M) x D := by
  have h : (tensor0SAsRS (I := I) (M := M) x (C - D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) -
        (tensor0SAsRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C - D) =
      tensor00Scalar (I := I) (M := M) x τ • C - tensor00Scalar (I := I) (M := M) x τ • D
    apply tensor0S_eq_of_toModel_eq' (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
      smul_eq_mul]
    ring
  exact h

/-- **The `(0, t)`-tensor wrapper distributes over addition.** -/
private lemma tensor0SAsRS_add' (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C + D) =
      tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D := by
  have h : (tensor0SAsRS (I := I) (M := M) x (C + D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) +
        (tensor0SAsRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C + D) =
      tensor00Scalar (I := I) (M := M) x τ • C + tensor00Scalar (I := I) (M := M) x τ • D
    rw [smul_add]
  exact h

/-- **The `(0, t)`-tensor wrapper distributes over finite sums.** -/
private lemma tensor0SAsRS_sum' {ι : Type*} (s_dummy : Finset ι) (t : ℕ) (x : M)
    (C : ι → Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (∑ i ∈ s_dummy, C i) =
      ∑ i ∈ s_dummy, tensor0SAsRS (I := I) (M := M) x (C i) := by
  classical
  induction s_dummy using Finset.induction with
  | empty => simp [tensor0SAsRS]
  | insert a t' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      have h : (tensor0SAsRS (I := I) (M := M) x (C a + ∑ i ∈ t', C i) :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
          (tensor0SAsRS (I := I) (M := M) x (C a) :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) +
            (tensor0SAsRS (I := I) (M := M) x (∑ i ∈ t', C i) :
              Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
        apply ContinuousLinearMap.ext
        intro τ
        change tensor00Scalar (I := I) (M := M) x τ • (C a + ∑ i ∈ t', C i) =
          tensor00Scalar (I := I) (M := M) x τ • (C a) +
            tensor00Scalar (I := I) (M := M) x τ • (∑ i ∈ t', C i)
        rw [smul_add]
      exact h

/-- **The frame-summed `∇²S`-pair reduces to first-order curvature (the genuine
moving-frame `∇²S`-elimination).** For the smooth `g_x`-orthonormal frame
`Bᵢ := smoothOrthoFrame g x i` and a smooth direction field `X`, writing
`wᵢ := ∇_X Bᵢ = fun y => (LeviCivita g) Bᵢ y (X y)` and `aᵢⱼ := g_x(wᵢ x, Bⱼ x)`, the
frame sum of the symmetric `∇²S`-order pair `∇²_{wᵢ, Bᵢ}S + ∇²_{Bᵢ, wᵢ}S` equals a pure
first-order curvature contraction of `S`:
```
∑ᵢ (∇²_{wᵢ, Bᵢ}S + ∇²_{Bᵢ, wᵢ}S)(x)
  = ∑ᵢⱼ aᵢⱼ • R(Bⱼ, Bᵢ)S(x) + ∑ᵢ R(Bᵢ, wᵢ)S(x).
```
The proof: the second-slot term `∇²_{Bᵢ, wᵢ}S` is `∇²_{wᵢ, Bᵢ}S + R(Bᵢ, wᵢ)S` by the Ricci
identity `tensorSecondCovDeriv_antisymm_eq_riemannSec`, so the pair is
`2 ∇²_{wᵢ, Bᵢ}S + R(Bᵢ, wᵢ)S`. The first-slot Hessian map
`tensorSecondCovDeriv_eq_firstSlotHessMap` is continuous-linear in its first argument; expanding
`wᵢ x = ∑ⱼ aᵢⱼ Bⱼ x` (`orthonormal_frame_vector_expansion`) gives
`∇²_{wᵢ, Bᵢ}S = ∑ⱼ aᵢⱼ ∇²_{Bⱼ, Bᵢ}S`. Antisymmetrising with `aᵢⱼ = -aⱼᵢ`
(`smoothOrthoFrame_cov_skew`) over `Finset.sum_comm` gives
`2 ∑ᵢ ∇²_{wᵢ, Bᵢ}S = ∑ᵢⱼ aᵢⱼ (∇²_{Bⱼ, Bᵢ}S − ∇²_{Bᵢ, Bⱼ}S) = ∑ᵢⱼ aᵢⱼ R(Bⱼ, Bᵢ)S`,
again by the Ricci identity. No `∇²S` survives. -/
private lemma frameSum_secondCovDeriv_pair_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) x +
          tensorSecondCovDeriv (I := I) g 0 s (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (fun y : M => S.toSection y) x) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (g.inner x
              ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x))
              (smoothOrthoFrame (I := I) g x j x)) •
            riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x j)
              (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) x +
        ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (fun y : M => S.toSection y) x := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set B : Fin n → Π b : M, TangentSpace I b := fun i => smoothOrthoFrame (I := I) g x i with hB
  set w : Fin n → Π b : M, TangentSpace I b :=
    fun i y => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y) with hw
  set Sf : Π b : M, TensorRSSpace 0 s I b := fun y => S.toSection y with hSf
  set a : Fin n → Fin n → ℝ :=
    fun i j => g.inner x (w i x) (smoothOrthoFrame (I := I) g x j x) with ha
  -- Smoothness of the frame fields and the direction-derivative fields.
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hwsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, w i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) hX (hBsm i)
  have hBon : ∀ i j : Fin n,
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  -- The Ricci identity at the second-slot field for the `(0, s)`-tensor `Sf`.
  have hric : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (B i) (w i) Sf x -
          tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
        riemannSec (tensorCov (I := I) g 0 s) (B i) (w i) Sf x := by
    intro i
    exact tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g 0 s Sf
      ((hBsm i x).mdifferentiableAt (by simp)) ((hwsm i x).mdifferentiableAt (by simp))
  -- Hence the pair equals `2·∇²_{wᵢ,Bᵢ}S + R(Bᵢ,wᵢ)S`.
  have hpair : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x +
          tensorSecondCovDeriv (I := I) g 0 s (B i) (w i) Sf x =
        (2 : ℝ) • tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x +
          riemannSec (tensorCov (I := I) g 0 s) (B i) (w i) Sf x := by
    intro i
    have hr := hric i
    rw [two_smul]
    linear_combination (norm := module) hr
  rw [Finset.sum_congr rfl (fun i _ => hpair i)]
  rw [Finset.sum_add_distrib]
  congr 1
  -- The `2·∑ᵢ ∇²_{wᵢ,Bᵢ}S` term: expand via firstSlotHessMap + Parseval + skew.
  -- First-slot reading: `∇²_{wᵢ,Bᵢ}S x = firstSlotHessMap g 0 s Bᵢ S x (wᵢ x)`.
  have hfsh : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
        firstSlotHessMap (I := I) g 0 s (B i) Sf x (w i x) :=
    fun i => tensorSecondCovDeriv_eq_firstSlotHessMap (I := I) g 0 s (w i) (B i) Sf x
  -- Expand `wᵢ x = ∑ⱼ aᵢⱼ Bⱼ x`.
  have hexp : ∀ i : Fin n,
      w i x = ∑ j : Fin n, a i j • smoothOrthoFrame (I := I) g x j x := by
    intro i
    have := orthonormal_frame_vector_expansion (I := I) g x (w i x)
      (fun j => smoothOrthoFrame (I := I) g x j x) hBon
    simpa [ha] using this
  -- Hence `∇²_{wᵢ,Bᵢ}S x = ∑ⱼ aᵢⱼ • firstSlotHessMap g 0 s Bᵢ S x (Bⱼ x)`.
  have hfsh2 : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
        ∑ j : Fin n, a i j • firstSlotHessMap (I := I) g 0 s (B i) Sf x
          (smoothOrthoFrame (I := I) g x j x) := by
    intro i
    rw [hfsh i, hexp i, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  -- Read `firstSlotHessMap g 0 s Bᵢ S x (Bⱼ x) = ∇²_{Bⱼ,Bᵢ}S x`.
  have hfshread : ∀ i j : Fin n,
      firstSlotHessMap (I := I) g 0 s (B i) Sf x (smoothOrthoFrame (I := I) g x j x) =
        tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x := by
    intro i j
    rw [tensorSecondCovDeriv_eq_firstSlotHessMap (I := I) g 0 s (B j) (B i) Sf x]
  -- So `∑ᵢ ∇²_{wᵢ,Bᵢ}S = ∑ᵢⱼ aᵢⱼ • ∇²_{Bⱼ,Bᵢ}S`.
  have hsumT6 : ∑ i : Fin n, tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hfsh2 i]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hfshread i j]
  -- Antisymmetry of `a`: `aᵢⱼ = -aⱼᵢ`.
  have hskew : ∀ i j : Fin n, a i j = - a j i := by
    intro i j
    simp only [ha, hw]
    rw [smoothOrthoFrame_cov_skew (I := I) g x i j (X x),
      g.symm x (smoothOrthoFrame (I := I) g x i x) _]
  -- Ricci identity at the frame pair: `∇²_{Bⱼ,Bᵢ}S − ∇²_{Bᵢ,Bⱼ}S = R(Bⱼ,Bᵢ)S`.
  have hricBB : ∀ i j : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x -
          tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x =
        riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x := by
    intro i j
    exact tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g 0 s Sf
      ((hBsm j x).mdifferentiableAt (by simp)) ((hBsm i x).mdifferentiableAt (by simp))
  -- Antisymmetrise: `2 ∑ᵢⱼ aᵢⱼ • ∇²_{Bⱼ,Bᵢ}S = ∑ᵢⱼ aᵢⱼ • R(Bⱼ,Bᵢ)S`.
  have hkey : (2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n,
        a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x) =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x := by
    -- `Y := ∑∑ aᵢⱼ • ∇²_{Bᵢ,Bⱼ}S = -X`, the swap-image of `X := ∑∑ aᵢⱼ • ∇²_{Bⱼ,Bᵢ}S`.
    have hswap : (∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x) =
        - ∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x := by
      have hstep : (∑ i : Fin n, ∑ j : Fin n,
            a i j • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x) =
          ∑ i : Fin n, ∑ j : Fin n,
            (- a j i) • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hskew i j]
      rw [hstep]
      simp only [neg_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
    -- `X - Y = ∑∑ aᵢⱼ • R(Bⱼ,Bᵢ)S` by the Ricci identity.
    have hdiff : (∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x) -
        (∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x) =
        ∑ i : Fin n, ∑ j : Fin n,
          a i j • riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← smul_sub, hricBB i j]
    rw [← hdiff, hswap, two_smul]
    abel
  -- Assemble the `2·∑ᵢ ∇²_{wᵢ,Bᵢ}S` arm.
  rw [show (∑ i : Fin n, (2 : ℝ) • tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x) =
      (2 : ℝ) • ∑ i : Fin n, tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x from
    (Finset.smul_sum).symm]
  rw [hsumT6, hkey]

/-- **Matching of the gradient piece of the frame-summand `Dᵢ`.** For the frame field
`V := smoothOrthoFrame g x i` (smoothness `hV`), the `covGradBundleEquiv`-image of the
`(0, s)`-tensor covariant derivative of the diagonal second covariant derivative
`∇²_{V,V}S` equals the section value of the packaged covariant gradient of `secondCovDerivCc`:
```
covGradBundleEquiv 0 s x (∇(∇²_{V,V}S)(x)) = (covGrad g 0 s (secondCovDerivCc g s hV S)).toSection x.
```
This identifies the second per-summand of `pointwiseTensorCurv_toSection_eq_frame_sum` with the
gradient piece consumed by the carrier `secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`. -/
private lemma covGradBundleEquiv_secondCovDeriv_eq_covGrad_secondCovDerivCc
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    covGradBundleEquiv (I := I) (M := M) 0 s x
        ((tensorCov (I := I) g 0 s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g 0 s V V
            (fun z : M => S.toSection z) y) x) =
      (covGrad (I := I) (M := M) g 0 s (secondCovDerivCc (I := I) (M := M) g s hV S)).toSection x := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (secondCovDerivCc (I := I) (M := M) g s hV S) x]
  rfl

/-- The seven-term curvature carrier value, as a single `(0, s)`-model-tensor at `x` (the
unit-evaluation of the carrier RHS of
`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`, with fields `V, X`). -/
private noncomputable def carrierSevenInner
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V X : Π b : M, TangentSpace I b) (x : M) : Tensor0SSpace s I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannSec (tensorCov (I := I) g 0 s) V X
        (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) x)
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      covApply (tensorCov (I := I) g 0 s) V
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
          (fun z : M => S.toSection z) y) x)
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannOp (tensorCov (I := I) g 0 s) x
        ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x))
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannOp (tensorCov (I := I) g 0 s) x (X x)
        ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x))
      (unitZeroSec (I := I) (M := M) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
        (riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x)))
      (unitZeroSec (I := I) (M := M) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorSecondCovDeriv (I := I) g 0 s
        (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
        (fun y : M => S.toSection y) x)
      (unitZeroSec (I := I) (M := M) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorSecondCovDeriv (I := I) g 0 s V
        (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
        (fun y : M => S.toSection y) x)
      (unitZeroSec (I := I) (M := M) x)

/-- **Per-frame, per-direction carrier lift (unwrapped).** The slot-`0` `X`-read of the difference
`piece1 − piece2` (the frame-summand `Dᵢ` of `pointwiseTensorCurv_toSection_eq_frame_sum`, with the
gradient piece written through `secondCovDerivCc`) equals the seven-term curvature carrier value
`carrierSevenInner`, as a `(0, s)`-model-tensor at `x`. This lifts the scalar-model carrier
`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq` to the `(0, s)`-fibre value. -/
private lemma slot0_read_Di_eq_carrierSevenInner
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {V X : Π b : M, TangentSpace I b}
    (hVs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            tensorSecondCovDeriv (I := I) g 0 (s + 1) V V
                (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
            (unitZeroSec (I := I) (M := M) x)) (X x) -
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g 0 s
              (secondCovDerivCc (I := I) (M := M) g s hVs S)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (X x) =
      carrierSevenInner (I := I) (M := M) g s S V X x := by
  classical
  apply tensor0S_eq_of_toModel_eq' (I := I) (M := M)
  intro m
  rw [Tensor0SSpace.toModel_sub]
  rw [carrierSevenInner]
  exact secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq (I := I) g s S hVs hXs x m

/-- **Wrapper recovery of the carrier value.** The `tensor0SAsRS`-wrap of the seven-term carrier
value `carrierSevenInner` is the difference of genuine `(0, s)`-tensor curvature values: the wrapper
collapses against each unit-evaluation, recovering the seven `TensorRSSpace 0 s` curvature terms
(`tensor0SAsRS_unit_recover`). -/
private lemma wrap_carrierSevenInner_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V X : Π b : M, TangentSpace I b) (x : M) :
    tensor0SAsRS (I := I) (M := M) x (carrierSevenInner (I := I) (M := M) g s S V X x) =
      riemannSec (tensorCov (I := I) g 0 s) V X
          (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) x +
        covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
            (fun z : M => S.toSection z) y) x +
        riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x) +
        riemannOp (tensorCov (I := I) g 0 s) x (X x)
          ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x) -
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x)) -
        tensorSecondCovDeriv (I := I) g 0 s
          (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
          (fun y : M => S.toSection y) x -
        tensorSecondCovDeriv (I := I) g 0 s V
          (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
          (fun y : M => S.toSection y) x := by
  rw [carrierSevenInner]
  rw [tensor0SAsRS_sub', tensor0SAsRS_sub', tensor0SAsRS_sub',
    tensor0SAsRS_add', tensor0SAsRS_add', tensor0SAsRS_add']
  rw [tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover,
    tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover,
    tensor0SAsRS_unit_recover]

/-- **Per-direction slice value identity.** The wrapped slot-`0` `X`-read of the order-`2`
commutator defect `Curv S (x) = ∑ᵢ Dᵢ` equals the frame sum, over `i`, of the wrapped seven-term
curvature carrier values with frame field `Bᵢ := smoothOrthoFrame g x i`:
```
tensor0SAsRS x (tensor0S_curry s x (Curv S (x) (unit)) (X x))
  = ∑ᵢ tensor0SAsRS x (carrierSevenInner with V = Bᵢ).
```
This combines `pointwiseTensorCurv_toSection_eq_frame_sum` (the frame split), the matching
`covGradBundleEquiv_secondCovDeriv_eq_covGrad_secondCovDerivCc` of the gradient piece, the slot-`0`
curry / wrapper linearity, and the per-`i` carrier lift `slot0_read_Di_eq_carrierSevenInner`. -/
private lemma slot0_read_curv_eq_sum_carrier
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (X x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensor0SAsRS (I := I) (M := M) x
          (carrierSevenInner (I := I) (M := M) g s S
            (smoothOrthoFrame (I := I) g x i) X x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  -- The frame summand `Dᵢ`, with the gradient piece written through `secondCovDerivCc`.
  set D : Fin n → Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x := fun i =>
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      tensorSecondCovDeriv (I := I) g 0 (s + 1) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s
        (secondCovDerivCc (I := I) (M := M) g s
          (smoothOrthoFrame_smooth (I := I) g x i) S)).toSection x) with hD
  -- `Curv S (x) = ∑ᵢ Dᵢ` (frame split + gradient-piece matching).
  have hcurv : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) = ∑ i : Fin n, D i := by
    rw [pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hD]
    rw [covGradBundleEquiv_secondCovDeriv_eq_covGrad_secondCovDerivCc (I := I) (M := M) g s S
      (smoothOrthoFrame_smooth (I := I) g x i) x]
  rw [hcurv]
  -- Push the slot-`0` curry / read / wrapper through the frame sum.
  rw [ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.sum_apply,
    tensor0SAsRS_sum']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Per-`i`: wrap the carrier lift.
  rw [hD]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (secondCovDerivCc (I := I) (M := M) g s
              (smoothOrthoFrame_smooth (I := I) g x i) S)).toSection x))
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s
          (secondCovDerivCc (I := I) (M := M) g s
            (smoothOrthoFrame_smooth (I := I) g x i) S)).toSection x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [ContinuousLinearMap.sub_apply]]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  congr 1
  exact slot0_read_Di_eq_carrierSevenInner (I := I) (M := M) g s S
    (smoothOrthoFrame_smooth (I := I) g x i) hXs x

/-- **The frame-summed `∇²S`-pair vanishes (the antisymmetric Hessian cancellation).** Continuing
`frameSum_secondCovDeriv_pair_eq_riemannSec`, its right-hand side is itself `0`: with
`wᵢ := ∇_X Bᵢ`, `aᵢⱼ := g_x(wᵢ x, Bⱼ x)`,
```
∑ᵢⱼ aᵢⱼ • R(Bⱼ, Bᵢ)S(x) + ∑ᵢ R(Bᵢ, wᵢ)S(x) = 0.
```
Expanding `wᵢ x = ∑ⱼ aᵢⱼ Bⱼ x` (`orthonormal_frame_vector_expansion`) and using the
`Y`-tensoriality + `C^∞`-linearity of `riemannSec` (`riemannSec_eq_of_Y_eq_at`, `riemannSec_add_right`,
`riemannSec_smul_right`) gives `R(Bᵢ, wᵢ)S = ∑ⱼ aᵢⱼ R(Bᵢ, Bⱼ)S`; antisymmetrising with
`riemannSec_swap` makes the second sum `−∑ᵢⱼ aᵢⱼ R(Bⱼ, Bᵢ)S`, cancelling the first. Hence the frame
sum `∑ᵢ (∇²_{wᵢ, Bᵢ}S + ∇²_{Bᵢ, wᵢ}S)(x) = 0`. -/
private lemma frameSum_secondCovDeriv_pair_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) x +
          tensorSecondCovDeriv (I := I) g 0 s (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (fun y : M => S.toSection y) x) = 0 := by
  classical
  rw [frameSum_secondCovDeriv_pair_eq_riemannSec (I := I) (M := M) g s S hX x]
  set n : ℕ := Module.finrank ℝ E with hn
  set B : Fin n → Π b : M, TangentSpace I b := fun i => smoothOrthoFrame (I := I) g x i with hB
  set w : Fin n → Π b : M, TangentSpace I b :=
    fun i y => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y) with hw
  set Sf : Π b : M, TensorRSSpace 0 s I b := fun y => S.toSection y with hSf
  set a : Fin n → Fin n → ℝ :=
    fun i j => g.inner x (w i x) (smoothOrthoFrame (I := I) g x j x) with ha
  -- Smoothness of the frame fields and the direction-derivative fields.
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hwsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, w i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) hX (hBsm i)
  have hBon : ∀ i j : Fin n,
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  -- Expand `wᵢ x = ∑ⱼ aᵢⱼ Bⱼ x`.
  have hexp : ∀ i : Fin n, w i x = ∑ j : Fin n, a i j • B j x := by
    intro i
    have := orthonormal_frame_vector_expansion (I := I) g x (w i x)
      (fun j => smoothOrthoFrame (I := I) g x j x) hBon
    simpa [ha, hB] using this
  -- Pass each `riemannSec` to the pointwise bundled operator `riemannOp` (genuinely
  -- multilinear at `x`, so no field smoothness is needed for the middle-slot expansion).
  have hsec_to_op : ∀ Y : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => (⟨b, Y b⟩ : TotalSpace E (TangentSpace I))) →
      ∀ i : Fin n, riemannSec (tensorCov (I := I) g 0 s) (B i) Y Sf x =
        riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Y x) (Sf x) := by
    intro Y hY i
    exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s)
      (hBsm i) hY S.toSection.contMDiff
  -- The first double sum, in bundled-operator form.
  have hfirst : (∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x) =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannOp (tensorCov (I := I) g 0 s) x (B j x) (B i x) (Sf x) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [hsec_to_op (B i) (hBsm i) j]))
  -- The second sum: `R(Bᵢ, wᵢ)S x = riemannOp x (Bᵢ x) (wᵢ x) (Sf x)`, then expand the
  -- middle slot by `wᵢ x = ∑ⱼ aᵢⱼ Bⱼ x` (CLM `map_sum` + `map_smul`).
  have hsecond : (∑ i : Fin n,
        riemannSec (tensorCov (I := I) g 0 s) (B i) (w i) Sf x) =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (B j x) (Sf x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsec_to_op (w i) (hwsm i) i, hexp i]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
  -- Pair the two double sums index-by-index; `riemannOp_swap` makes them cancel.
  rw [hfirst, hsecond]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x (B i x) (B j x)]
  rw [smul_neg]
  abel

/-- **The frame-free value of the wrapped slot-`0` read of the curvature defect.** Combining the
per-direction slice identity `slot0_read_curv_eq_sum_carrier` with the C2-expansion
(`nablaTensorCurvSec_def`), the curvature-operator antisymmetries (`riemannOp_swap`,
`riemannSec_eq_riemannOp_tensorCov`) which cancel the frame-jet sub-terms `C3, C4` against the two
middle pieces of the expanded `C2`, and the antisymmetric `∇²S`-pair cancellation
(`frameSum_secondCovDeriv_pair_eq_zero`, the `C6, C7` sum), the wrapped slot-`0` `X`-read of the
order-`2` defect `Curv S (x)` is the **frame-free** first-order curvature combination
```
∑ᵢ nablaTensorCurvSec g (tensorCov g 0 s) Bᵢ Bᵢ X S (x)        [the ∇R·S arm]
  + 2 ∑ᵢ R(Bᵢ, X)(∇_{Bᵢ} S)(x)                                 [the R·∇S arm, the two C1 copies]
  − ∑ᵢ ∇_{R(Bᵢ, X) Bᵢ} S (x),                                   [the R·∇S arm, the C5 term]
```
with `Bᵢ := smoothOrthoFrame g x i`. No `∇²S`, no frame-jet coefficient, and no Lie bracket survives. -/
private lemma slot0_read_curv_eq_frameFree
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (X x)) =
      ∑ i : Fin (Module.finrank ℝ E),
          nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) X
            (fun y : M => S.toSection y) x +
        (2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) X
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x) (X x)
              (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set B : Fin n → Π b : M, TangentSpace I b := fun i => smoothOrthoFrame (I := I) g x i with hB
  set Sf : Π b : M, TensorRSSpace 0 s I b := fun y => S.toSection y with hSf
  -- Smoothness of the frame fields, the direction `X`, and the once-derived frame fields.
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hBBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, covApply (LeviCivita (I := I) g) (B i) (B i) b⟩
        : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hBsm i) (hBsm i)
  have hBXsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, covApply (LeviCivita (I := I) g) (B i) X b⟩
        : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hBsm i) hXs
  -- Per-`i`: the wrapped carrier equals `nabla i + 2•C1 i − C5 i − (C6 i + C7 i)`.
  -- (The two middle pieces of the expanded `C2` cancel the frame-jet carriers `C3, C4`.)
  have hper : ∀ i : Fin n,
      tensor0SAsRS (I := I) (M := M) x (carrierSevenInner (I := I) (M := M) g s S (B i) X x) =
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s) (B i) (B i) X Sf x +
          (2 : ℝ) • riemannSec (tensorCov (I := I) g 0 s) (B i) X
            (covApply (tensorCov (I := I) g 0 s) (B i) Sf) x -
          (tensorCov (I := I) g 0 s).toFun Sf x
            (riemannOp (LeviCivita (I := I) g) x (B i x) (X x) (B i x)) -
          (tensorSecondCovDeriv (I := I) g 0 s
              (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) (B i) Sf x +
            tensorSecondCovDeriv (I := I) g 0 s (B i)
              (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) Sf x) := by
    intro i
    rw [wrap_carrierSevenInner_eq (I := I) (M := M) g s S (B i) X x]
    -- Expand `C2 = nabla + RS_BB + RS_BX + C1`.
    have hC2eq : covApply (tensorCov (I := I) g 0 s) (B i)
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) (B i) X Sf y) x =
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s) (B i) (B i) X Sf x +
          riemannSec (tensorCov (I := I) g 0 s)
            (covApply (LeviCivita (I := I) g) (B i) (B i)) X Sf x +
          riemannSec (tensorCov (I := I) g 0 s) (B i)
            (covApply (LeviCivita (I := I) g) (B i) X) Sf x +
          riemannSec (tensorCov (I := I) g 0 s) (B i) X
            (covApply (tensorCov (I := I) g 0 s) (B i) Sf) x := by
      have hdef := nablaTensorCurvSec_def (I := I) g (tensorCov (I := I) g 0 s) (B i) (B i) X Sf x
      have hC2_unfold : covApply (tensorCov (I := I) g 0 s) (B i)
          (fun y : M => riemannSec (tensorCov (I := I) g 0 s) (B i) X Sf y) x =
          (tensorCov (I := I) g 0 s).toFun
            (fun b => riemannSec (tensorCov (I := I) g 0 s) (B i) X Sf b) x (B i x) := rfl
      rw [hC2_unfold]
      rw [hdef]
      abel
    rw [hC2eq]
    -- C3 in bundled-operator form: `C3 = -riemannSec(Bᵢ, ∇_{Bᵢ}X)`.
    have hC3op : riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun X x (B i x)) (B i x) (Sf x) =
        -riemannSec (tensorCov (I := I) g 0 s) (B i)
          (covApply (LeviCivita (I := I) g) (B i) X) Sf x := by
      rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (hBsm i) (hBXsm i) S.toSection.contMDiff]
      rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x (B i x)
        ((covApply (LeviCivita (I := I) g) (B i) X) x), neg_neg]
      rfl
    -- C4 in bundled-operator form: `C4 = -riemannSec(∇_{Bᵢ}Bᵢ, X)`.
    have hC4op : riemannOp (tensorCov (I := I) g 0 s) x (X x)
          ((LeviCivita (I := I) g).toFun (B i) x (B i x)) (Sf x) =
        -riemannSec (tensorCov (I := I) g 0 s)
          (covApply (LeviCivita (I := I) g) (B i) (B i)) X Sf x := by
      rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (hBBsm i) hXs S.toSection.contMDiff]
      rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x
        ((covApply (LeviCivita (I := I) g) (B i) (B i)) x) (X x), neg_neg]
      rfl
    rw [hC3op, hC4op, two_smul]
    abel
  -- Sum the per-`i` identity, then drop the vanishing `C6 + C7` frame sum.
  rw [slot0_read_curv_eq_sum_carrier (I := I) (M := M) g s S hXs x]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hper i)]
  have hC6C7 := frameSum_secondCovDeriv_pair_eq_zero (I := I) (M := M) g s S hXs x
  -- Split the four-term frame sum and discharge the pair sum.
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ i : Fin n,
        (tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) (B i) Sf x +
          tensorSecondCovDeriv (I := I) g 0 s (B i)
            (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) Sf x)) = 0 from hC6C7]
  rw [Finset.smul_sum]
  abel

/-- **The `∇R · S` arm uniform fibre bound (`appCc`-contracted differentiated curvature).** For a
closed smooth Riemannian manifold `(M, g)` there is a valence-dependent nonnegative constant
`Cd : ℕ → ℝ` such that, at every rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`,
and frame index `a`, the frame-summed differentiated-curvature contraction
`∑ᵢ nablaTensorCurvSec g (tensorCov g 0 s) Bᵢ Bᵢ Bₐ S (x)` (the genuine `(∇R) · S` term, where
`Bⱼ := smoothOrthoFrame g x j`) is fibre-bounded `rfns(S)`-order, uniformly in `x, a`:
```
rfns( ∑ᵢ nablaTensorCurvSec g (tensorCov g 0 s) Bᵢ Bᵢ Bₐ S (x) ) ≤ Cd s · rfns(S)(x).
```
This is `S`-linear: each `nablaTensorCurvSec` is the once-differentiated curvature operator field
`∇R` contracted against `S` (the `appCc`-image `genuineDiffCurvSection` of `covGrad (curvOpField g s)`
applied to `S`, via `nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum` and the
`appCc_curvOpField_eq_pureRGenuineDiffOp` / `genuineDiffCurvSection_toSection` chain), so the uniform
section-proportional envelope `exists_uniform_riemannianFiberNormSq_appCc_le` of the **fixed** smooth
`∇R` operator field controls it by `rfns(S)`, uniformly over the compact `M`. -/
private theorem exists_frameSummed_nablaTensorCurvSec_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) :
    ∃ Cd : ℕ → ℝ, (∀ s, 0 ≤ Cd s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) ≤
          Cd s * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
  sorry

/-- **The `∇_{R·B} S` arm uniform fibre bound (the curvature-direction covariant-derivative slice).**
For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent nonnegative constant
`Cc : ℕ → ℝ` such that, at every rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`,
and frame index `a`, the frame-summed covariant-derivative slice in the curvature directions
`R(Bᵢ, Bₐ) Bᵢ` (`Bⱼ := smoothOrthoFrame g x j`),
```
∑ᵢ (tensorCov g 0 s).toFun (S.toSection) x (R(Bᵢ, Bₐ) Bᵢ),
```
is fibre-bounded `rfns(∇S)`-order, uniformly in `x, a`:
```
rfns( ∑ᵢ ∇_{R(Bᵢ, Bₐ) Bᵢ} S (x) ) ≤ Cc s · rfns(∇S)(x),    ∇S := covGrad g 0 s S.
```
This is a directional covariant-derivative slice of `∇S`: the direction `R(Bᵢ, Bₐ) Bᵢ` is the
Levi-Civita curvature operator (uniformly fibre-bounded `‖R‖_∞` over the compact `M` by
`exists_uniform_riemannOp_LeviCivita_gNorm_bound`, with `g(Bᵢ, Bᵢ) = g(Bₐ, Bₐ) = 1`), and the slot-`0`
slice `∇_w S = (tensorCov g 0 s).toFun S x w` is dominated by the full gradient fibre norm `rfns(∇S)`
(the slot-`0` Parseval domination). -/
private theorem exists_frameSummed_curvDirCovDeriv_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) :
    ∃ Cc : ℕ → ℝ, (∀ s, 0 ≤ Cc s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x))) ≤
          Cc s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
  sorry

/-- **Per-direction-slice arm bound for the C1 (`R·∇S`) term.** The pure-Riemann curvature trace
`∑ᵢ R(Bᵢ, Bₐ)(∇_{Bᵢ} S)(x)` of the frame-free slice (at the gradient-frame direction
`Bₐ := smoothOrthoFrame g x a`) coincides with the packaged pure-Riemann genuine trace
`genuineCurvTraceFixedFramePureR` at the smooth extension of `Bₐ x`, so it is fibre-bounded
`rfns(∇S)`-order by `exists_uniform_genuineCurvTracePureR_fiberNormSq_bound`. -/
private lemma frameSummed_C1_eq_genuineCurvTracePureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y)) x) =
      genuineCurvTraceFixedFramePureR (I := I) g s
        (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x a x))
        (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
  classical
  rw [genuineCurvTraceFixedFramePureR_def (I := I) g s
    (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x a x))
    (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Both `riemannSec`s have the same value at `x` (the middle slot agrees at `x`).
  have hcov_sm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
      (smoothOrthoFrame_smooth (I := I) g x i)
  rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (smoothOrthoFrame_smooth (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x a) hcov_sm]
  rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (smoothOrthoFrame_smooth (I := I) g x i)
    (smoothExtensionTangent_contMDiff (I := I) x (smoothOrthoFrame (I := I) g x a x)) hcov_sm]
  rw [smoothExtensionTangent_eq (I := I) x (smoothOrthoFrame (I := I) g x a x)]

/-- **The per-point squared fibre bound of the order-`2` curvature defect.** Summing the per-direction
frame-free slice value (`slot0_read_curv_eq_frameFree`) over the gradient frame and bounding each of
the three arms — the `∇R · S` arm (`hCd`), the `R · ∇S` arm (the two pure-`R` curvature-trace copies,
`hKpure`), and the curvature-direction `∇S`-slice arm (`hCc`) — by `n`-sub-additivity of the squared
fibre norm gives
```
rfns(Curv S)(x) ≤ n · (32 Kpure s + 2 Cc s) · rfns(∇S)(x) + n · (4 Cd s) · rfns(S)(x).
```
-/
private lemma pointwiseTensorCurv_fiberNormSq_squared_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (Kpure Cd Cc : ℕ → ℝ)
    (hKpure : ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x),
        g.inner x v v = 1 →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (genuineCurvTraceFixedFramePureR (I := I) g s
              (smoothExtensionTangent (I := I) x v) (smoothOrthoFrame (I := I) g x)
              (fun y : M => S.toSection y) x) ≤
          Kpure s *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x))
    (hCd : ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) ≤
          Cd s * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))
    (hCc : ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x))) ≤
          Cc s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
      (Module.finrank ℝ E : ℝ) * (16 * Kpure s + 2 * Cc s) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        (Module.finrank ℝ E : ℝ) * (4 * Cd s) *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set grad : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hgrad
  set base : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hbase
  have hgrad_nn : 0 ≤ grad := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hbase_nn : 0 ≤ base := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- Entry reduction: `rfns(Curv)(x) = ∑ₐ rfns(slice_a)`, `slice_a := tensor0SAsRS(curry Curv at Bₐ)`.
  have hentry := rfns_succ_eq_sum_curry_smoothOrthoFrame (I := I) (M := M) g s x
    ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
  rw [hentry]
  -- Per-`a`: identify the slice with the frame-free value and bound its fibre norm.
  set sliceVal : Fin n → TensorRSSpace 0 s I x := fun a =>
    ∑ i : Fin n,
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x +
      (2 : ℝ) • ∑ i : Fin n,
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin n,
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) with hsliceVal
  have hslice_eq : ∀ a : Fin n,
      slot0Curry (I := I) (M := M) g x s (fun a => smoothOrthoFrame (I := I) g x a x)
          (fun k : Fin 0 => k.elim0)
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) a =
        sliceVal a := by
    intro a
    rw [slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec (I := I) (M := M) g x s
      (fun a => smoothOrthoFrame (I := I) g x a x) (fun k : Fin 0 => k.elim0) _ a]
    rw [hsliceVal]
    exact slot0_read_curv_eq_frameFree (I := I) (M := M) g s S
      (smoothOrthoFrame_smooth (I := I) g x a) x
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => by rw [hslice_eq a])]
  -- Per-`a` squared bound.
  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (sliceVal a) ≤
        (16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base := by
    intro a
    set A_a : TensorRSSpace 0 s I x := ∑ i : Fin n,
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x with hA_a
    set R_a : TensorRSSpace 0 s I x := ∑ i : Fin n,
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y)) x with hR_a
    set C5_a : TensorRSSpace 0 s I x := ∑ i : Fin n,
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) with hC5_a
    have hsliceVal_a : sliceVal a = A_a + (2 : ℝ) • R_a - C5_a := by
      rw [hsliceVal, hA_a, hR_a, hC5_a]
    -- Arm bounds.
    have hbd_A : riemannianFiberNormSq (I := I) (M := M) g 0 s x A_a ≤ Cd s * base := by
      rw [hA_a, hbase]; exact hCd s S x a
    have hbd_C5 : riemannianFiberNormSq (I := I) (M := M) g 0 s x C5_a ≤ Cc s * grad := by
      rw [hC5_a, hgrad]; exact hCc s S x a
    have hbd_R : riemannianFiberNormSq (I := I) (M := M) g 0 s x R_a ≤ Kpure s * grad := by
      rw [hR_a, frameSummed_C1_eq_genuineCurvTracePureR (I := I) (M := M) g s S x a, hgrad]
      exact hKpure s S x (smoothOrthoFrame (I := I) g x a x)
        (by
          have := smoothOrthoFrame_orthonormal_at_center (I := I) g x a a
          simpa using this)
    have hbd_2R : riemannianFiberNormSq (I := I) (M := M) g 0 s x ((2 : ℝ) • R_a) ≤
        4 * (Kpure s * grad) := by
      rw [two_smul]
      calc riemannianFiberNormSq (I := I) (M := M) g 0 s x (R_a + R_a)
          ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x R_a +
              2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x R_a :=
            riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x R_a R_a
        _ ≤ 2 * (Kpure s * grad) + 2 * (Kpure s * grad) := by
            have := hbd_R; linarith
        _ = 4 * (Kpure s * grad) := by ring
    -- Combine via `2`-subadditivity twice.
    rw [hsliceVal_a]
    calc riemannianFiberNormSq (I := I) (M := M) g 0 s x (A_a + (2 : ℝ) • R_a - C5_a)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (A_a + (2 : ℝ) • R_a) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x C5_a :=
          riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 s x (A_a + (2 : ℝ) • R_a) C5_a
      _ ≤ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x A_a +
              2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x ((2 : ℝ) • R_a)) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x C5_a := by
          have := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x A_a ((2 : ℝ) • R_a)
          linarith
      _ ≤ 2 * (2 * (Cd s * base) + 2 * (4 * (Kpure s * grad))) + 2 * (Cc s * grad) := by
          have h1 := hbd_A; have h2 := hbd_2R; have h3 := hbd_C5; linarith
      _ = (16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base := by ring
  -- Sum the per-`a` bound (n terms).
  calc (∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (sliceVal a))
      ≤ ∑ _a : Fin n, ((16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (n : ℝ) * ((16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * (16 * Kpure s + 2 * Cc s) * grad +
          (Module.finrank ℝ E : ℝ) * (4 * Cd s) * base := by rw [hn]; ring

/-- **The first-order curvature fibre bound of the order-`2` commutator defect (the genuine
moving-frame third-order Bochner–Weitzenböck `∇²S`-elimination leaf).** For a closed smooth
Riemannian manifold `(M, g)` there are uniform nonnegative valence-dependent constants
`K_R, K_dR : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor
`S`, and point `x`, the intrinsic Riemannian fibre norm of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` is controlled by the gradient field `∇S := covGrad g 0 s S` and
the tensor `S` alone:
```
√(rfns(Curv S)(x)) ≤ K_R s · √(rfns(∇S)(x)) + K_dR s · √(rfns(S)(x)).
```

This is **first-order**: the bound carries `∇S` and `S` only, never `∇²S`. The genuine `∇²S`-order pair
in any per-direction expansion of the defect cancels in the frame sum (the antisymmetric Hessian
cancellation `frameSum_secondCovDeriv_pair_eq_zero`), leaving the frame-free curvature combination
`∑ᵢ (∇R)(Bᵢ, Bᵢ, ·) S + 2 ∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S) − ∑ᵢ ∇_{R(Bᵢ, ·) Bᵢ} S`
(`slot0_read_curv_eq_frameFree`), which is uniformly fibre-bounded `‖∇R‖_∞ · √(rfns(S))` and
`‖R‖_∞ · √(rfns(∇S))` over the compact manifold.

**Non-vacuity.** With `K_R s = K_dR s = 0` the bound forces `Curv S (x) = 0` for all `S, x`, i.e. the
rough Laplacian and the covariant gradient commute pointwise; this is *false* on a non-flat manifold,
so the bound genuinely envelopes the per-point curvature operator norm. -/
theorem pointwiseTensorCurv_fiberNormSq_le_first_order
    (g : SmoothRiemannianMetric I M) :
    ∃ K_R K_dR : ℕ → ℝ, (∀ s, 0 ≤ K_R s) ∧ (∀ s, 0 ≤ K_dR s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
          K_R s * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
            K_dR s * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (S.toSection x)) := by
  classical
  -- Subadditivity of the square root on non-negative reals.
  have hsqrt_add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h_sum_nn : 0 ≤ a + b := add_nonneg ha hb
    have h_sum_sq_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_lhs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt h_sum_nn
    have h_rhs_sq : (Real.sqrt a + Real.sqrt b) ^ 2 =
        a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
      rw [add_pow_two, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
    have h_cross_nn : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
    have h_sq_le : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
      rw [h_lhs_sq, h_rhs_sq]; linarith
    exact (abs_le_of_sq_le_sq' h_sq_le h_sum_sq_nn).2
  -- The three uniform arm constants.
  obtain ⟨Kpure, hKpure_nn, hKpure_bd⟩ :=
    exists_uniform_genuineCurvTracePureR_fiberNormSq_bound (I := I) (M := M) g
  obtain ⟨Cd, hCd_nn, hCd_bd⟩ :=
    exists_frameSummed_nablaTensorCurvSec_fiberNormSq_le (I := I) (M := M) g
  obtain ⟨Cc, hCc_nn, hCc_bd⟩ :=
    exists_frameSummed_curvDirCovDeriv_fiberNormSq_le (I := I) (M := M) g
  -- The assembled per-rank coefficients of the squared bound `rfns(Curv) ≤ P·rfns(∇S) + Q·rfns(S)`.
  set nR : ℝ := (Module.finrank ℝ E : ℝ) with hnR
  have hnR_nn : 0 ≤ nR := Nat.cast_nonneg _
  refine ⟨fun s => Real.sqrt (nR * (16 * Kpure s + 2 * Cc s)),
    fun s => Real.sqrt (nR * (4 * Cd s)),
    fun s => Real.sqrt_nonneg _, fun s => Real.sqrt_nonneg _, ?_⟩
  intro s S x
  -- The squared per-direction (slice) bound, summed over the gradient frame, controls `rfns(Curv)`.
  set Curv : TensorRSSpace 0 (s + 1) I x :=
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x with hCurv
  set grad : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hgrad
  set base : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hbase
  have hgrad_nn : 0 ≤ grad := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hbase_nn : 0 ≤ base := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The squared bound: `rfns(Curv)(x) ≤ nR·(32 Kpure + 2 Cc)·grad + nR·(4 Cd)·base`.
  have hsq : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Curv ≤
      nR * (16 * Kpure s + 2 * Cc s) * grad + nR * (4 * Cd s) * base := by
    exact pointwiseTensorCurv_fiberNormSq_squared_bound (I := I) (M := M) g s S x
      Kpure Cd Cc hKpure_bd hCd_bd hCc_bd
  -- Non-negativity of the assembled coefficients.
  have hPcoef_nn : 0 ≤ nR * (16 * Kpure s + 2 * Cc s) := by
    have := hKpure_nn s; have := hCc_nn s
    have : 0 ≤ 16 * Kpure s + 2 * Cc s := by nlinarith [hKpure_nn s, hCc_nn s]
    exact mul_nonneg hnR_nn this
  have hQcoef_nn : 0 ≤ nR * (4 * Cd s) := mul_nonneg hnR_nn (by nlinarith [hCd_nn s])
  -- Take square roots and split the sum.
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Curv)
      ≤ Real.sqrt (nR * (16 * Kpure s + 2 * Cc s) * grad + nR * (4 * Cd s) * base) :=
        Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (nR * (16 * Kpure s + 2 * Cc s) * grad) +
          Real.sqrt (nR * (4 * Cd s) * base) :=
        hsqrt_add _ _ (mul_nonneg hPcoef_nn hgrad_nn) (mul_nonneg hQcoef_nn hbase_nn)
    _ = Real.sqrt (nR * (16 * Kpure s + 2 * Cc s)) * Real.sqrt grad +
          Real.sqrt (nR * (4 * Cd s)) * Real.sqrt base := by
        rw [Real.sqrt_mul hPcoef_nn grad, Real.sqrt_mul hQcoef_nn base]

/-- **STEP 1 — the uniform first-order curvature fibre bound (rank-fixed `∃`-form).** For a closed
smooth Riemannian manifold `(M, g)` and covariant rank `s`, there are uniform constants
`K_R, K_dR ≥ 0` such that, for every smooth compactly-supported `(0, s)`-tensor `S` and point `x`,
```
√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x)),
```
with `Curv S := pointwiseTensorCurv g s S` and `∇S := covGrad g 0 s S`. This is the rank-fixed
specialisation of the valence-dependent first-order curvature fibre bound
`pointwiseTensorCurv_fiberNormSq_le_first_order`, read at the fixed rank `s`. -/
theorem exists_pointwiseTensorCurv_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K_R K_dR : ℝ, 0 ≤ K_R ∧ 0 ≤ K_dR ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
        K_R * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
          K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (S.toSection x)) := by
  obtain ⟨K_R, K_dR, hK_R_nn, hK_dR_nn, hbound⟩ :=
    pointwiseTensorCurv_fiberNormSq_le_first_order (I := I) (M := M) g
  exact ⟨K_R s, K_dR s, hK_R_nn s, hK_dR_nn s, fun S x => hbound s S x⟩

end Connection
end Integral
end DifferentialGeometry

end
