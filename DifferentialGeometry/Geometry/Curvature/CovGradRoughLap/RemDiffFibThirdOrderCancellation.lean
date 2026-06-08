import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.SecondOrderCommutationResidueFiberBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Connection.LeviCivita.TwoJetVanishingExtension

/-!
# The per-direction third-order cancellation of the moving-frame frame summand

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the two
genuinely-irreducible per-direction fibre atoms that the moving-frame frame summand
`remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)`
(`MovingFrameRemainderFrameSumBridge`) splits into once its third-order top-order term has cancelled:

* `remDiffGenuineFib g s S x i` — the pure-Riemann curvature fibre `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, the
  `rfns(∇S)`-order curvature contraction; and
* the genuine `∇³S`-cancellation residue carried by `remDiffFib` itself: the *commutator*
  `Aᵢ − Dᵢ := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)` of the rough-Laplacian frame trace and the
  covariant gradient, which is order-`≤ 2` in `S` because the third-order `∇³S` term cancels through
  the iterated Ricci identity.

## Why the per-direction commutator `remDiffFib` is order-`≤ 2`

The frame summand `remDiffFib g s S x i` is *exactly* the difference `Aᵢ − Dᵢ` of the two frame
summands whose curried unit-evaluation difference is pinned by the rank-generic second-order
leading-slot commutation `covGrad_covDeriv_leadingSlot_secondOrder_commutation`
(`MetricCompatibility/CovGradCovDerivSecondOrderCommutation`, sorry-free): for every smooth tangent
field `w`, the slot-`0` curry at `w` of `(remDiffFib g s S x i)(unit)` equals the abstract third-order
Ricci residue
```
curry (remDiffFib …)(unit)(w)
  = (∇_{Bᵢ} R)(Bᵢ, w) V                                                    -- the (∇R) S class
  + ( R(∇_{Bᵢ} Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ} w) V + 2 R(Bᵢ, w)(∇_{Bᵢ} V) )       -- the R(diff) class
  + ρ,                                                                      -- the Christoffel residual
```
`V := unitEvalSection g s S`, `R = riemannSec (tensor0SCovariantDerivative s (LeviCivita g))`,
`(∇R) = nablaTensorCurvSec`, `ρ = secondOrderChristoffelResidual`. Every right-hand-side summand is
order-`≤ 2` in `S`: the `(∇R) S` and `R(diff) V` classes are curvature contractions of `V` resp.
`∇_{Bᵢ} V` (orders `0` and `1`), and the Christoffel residual `ρ` is a sum of iterated `cov`-covariant
derivatives of `V` along the tangent Christoffel directions of `Bᵢ, w` (each at most a second covariant
derivative of `V`, order `≤ 2`). The intrinsic `(0, s + 1)` fibre norm of `remDiffFib` reconstructs as
the slot-`0` frame-sum of the slot-`s` fibre norms of these curries
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry`), so a uniform-over-`(i, a, x)` per-direction fibre
bound on the curvature residue — with the slot-`0` direction realised as the smooth extension
`smoothExtensionTangent x (e a)` of the orthonormal slot-`0` frame vector — gives the per-direction
order-`≤ 2` fibre bound on `remDiffFib`. The `∇³S`-cancellation is *false term-by-term* through the
non-tensorial `smoothExtensionTangent` reading of the individual third covariant derivatives
(chart-selection-unbounded on `S²`); only the intrinsic frame-summand *difference* `Aᵢ − Dᵢ` is
order-`≤ 2`, which is exactly what the commutation identity provides.

## Main results (the two posited per-direction frontiers)

* `exists_remDiffFib_fiberOrder_bound` — the **per-direction commutator fibre order**: the genuine
  `∇³S`-cancellation content, the order-`≤ 2` fibre bound on `remDiffFib g s S x i = Aᵢ − Dᵢ`.
* `exists_remDiffGenuineFib_fiberOrder_bound` — the **per-direction pure-Riemann curvature fibre
  order**: the `rfns(∇S)`-order fibre bound on the pure-Riemann curvature contraction
  `remDiffGenuineFib g s S x i`.

These two are the strictly-smaller, precise, intrinsic frontiers the per-direction bracket-summand
fibre order `exists_remDiffBracketFib_fiberOrder_bound` (`RemDiffBracketFiberOrder`) is assembled from,
via the named split `remDiffBracketFib = remDiffFib − remDiffGenuineFib` and fibre subadditivity. Both
are posited; their next recursion is the curvature-residue uniform-sup route documented above (toward
the pointwise iterated-Ricci identity `covGrad_covDeriv_leadingSlot_secondOrder_commutation`, already
sorry-free), not a re-statement.

## Convention

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` (`rfns`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
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

/-- **Uniform-over-`M` rank-`s` proportional curvature-operator fibre bound.** The supremum over the
compact `M` of the continuous per-point proportional curvature envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`: a single nonnegative
constant `Csup` with, for every point `x`, tangent vectors `v, w`, and `(0, s)`-tensor `T`,
`rfns(R_x(v, w) T)(x) ≤ Csup · g(v, v) · g(w, w) · rfns(T)(x)`. It is the rank-`s` curvature
operator's base-point-uniform proportional fibre constant. -/
private lemma exists_uniform_riemannOp_tensorCov_proportional_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Csup : ℝ, 0 ≤ Csup ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x v w T) ≤
          Csup * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional (I := I) (M := M) g s
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hvv_nn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le
  have hww_nn : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]; simp
    · exact (g.pos x w hw0).le
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
    mul_nonneg (mul_nonneg hvv_nn hww_nn)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (riemannOp (tensorCov (I := I) g 0 s) x v w T)
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
          hCcurv_bound x v w T
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T) := by ring
    _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by ring

/-- **The bridge from the per-direction covariant derivative to the slot-`0` reading of the gradient.**
The directional covariant derivative `(tensorCov g 0 s).toFun (S.toSection) x v = ∇_v S(x)` is the
slot-`0` reading of the gradient `∇S = covGrad g 0 s S` along `v`:
```
(tensorCov g 0 s).toFun (S.toSection) x v =
  ((covGradBundleEquiv 0 s x).symm ((covGrad g 0 s S).toSection x)) v.
```
Both sides are `tensorRSCovariantDerivative I M 0 s (LeviCivita g) (S.toSection) x v`: the left by
definition of `tensorCov`, the right by the pointwise gradient formula `covGrad_toSection_apply` after
applying `(covGradBundleEquiv 0 s x).symm`. -/
private lemma tensorCov_toFun_eq_covGradBundleEquiv_symm_reading
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v =
      ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x)) v := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **The slot-`0` curry of the unit-evaluated frame commutator is the second-order curvature residue
(sorry-free, the curry identity through the named difference).** For a smooth slot-`0` direction field
`w`, the slot-`0` curry at `w x` of the unit-evaluation of the frame commutator `remDiffFib g s S x i`
is the curvature residue `secondOrderResidue g s S x i w`. This is `secondOrderResidue_eq_curry_remDiffFib_unit`
(itself the rank-generic second-order leading-slot commutation, sorry-free) routed through the named
difference `remDiffFib = Aᵢ − Dᵢ`: the continuous-linear coercion of the subtraction distributes over the
unit evaluation (`ContinuousLinearMap.sub_apply`) and the slot-`0` curry (`map_sub`), recovering the
difference of the two curried unit-evaluated frame summands. -/
private lemma curry_remDiffFib_unit_eq_secondOrderResidue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          remDiffFib (I := I) (M := M) g s S x i)
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      secondOrderResidue (I := I) (M := M) g s S x i w := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        remDiffFib (I := I) (M := M) g s S x i) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 s x
          ((tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => S.toSection z) y) x)) from rfl]
  rw [ContinuousLinearMap.sub_apply, map_sub]
  exact secondOrderResidue_eq_curry_remDiffFib_unit (I := I) (M := M) g s S x i hw

/-- **Additivity of the `tensor0SAsRS` wrapper in the wrapped tensor.** `tensor0SAsRS x (a + b) =
tensor0SAsRS x a + tensor0SAsRS x b`: the wrapper is the continuous-linear map `τ ↦ (unit scalar) • C`,
linear in `C` through the `smul`. -/
private lemma tensor0SAsRS_add {s : ℕ} (x : M) (a b : Tensor0SSpace s I x) :
    tensor0SAsRS (I := I) (M := M) x (a + b) =
      tensor0SAsRS (I := I) (M := M) x a + tensor0SAsRS (I := I) (M := M) x b := by
  apply ContinuousLinearMap.ext
  intro τ
  rw [ContinuousLinearMap.add_apply, tensor0SAsRS_apply, tensor0SAsRS_apply, tensor0SAsRS_apply,
    smul_add]

/-- **Sub-additivity envelope for a `tensor0SAsRS`-wrapped two-term sum.** Combining
`tensor0SAsRS_add` with the `2`-sub-additivity of the squared fibre norm. -/
private lemma riemannianFiberNormSq_tensor0SAsRS_add_le
    (g : SmoothRiemannianMetric I M) {s : ℕ} (x : M) (a b : Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x (a + b)) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (tensor0SAsRS (I := I) (M := M) x a) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (tensor0SAsRS (I := I) (M := M) x b) := by
  rw [tensor0SAsRS_add (I := I) (M := M) x a b]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x _ _

/-- **The `tensor0SAsRS` wrapper of a `(0, s)`-tensor is its `unitScalarRSLift`.** Both lifts of a
model `(0, s)`-tensor `C` to a `(0, s)`-rank tensor are the continuous-linear map `τ ↦ (unit-scalar of
`τ`) • C`; the unit scalar is extracted identically (`tensor00Scalar x τ = tensor0Iso x τ`, both factor
through `continuousMultilinearCurryFin0`). -/
private lemma tensor0SAsRS_eq_unitScalarRSLift {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    tensor0SAsRS (I := I) (M := M) x C = unitScalarRSLift (I := I) (M := M) x C := by
  apply tensorRSSpace_ext 0 s x
  intro τ
  show (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      (unitScalarRSLift (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ]
  rw [show (unitScalarRSLift (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      (Tensor0SNabla.tensor0Iso (I := I) M x τ) • C from
    unitScalarRSLift_apply (I := I) (M := M) x C τ]
  congr 1

/-- **The intrinsic `(0, s)` fibre norm reads only the unit `(0, 0)`-evaluation.** If two `(0, s)`-rank
tensors `T, T'` agree at the unit `(0, 0)`-tensor, they have the same intrinsic fibre norm: the
Parseval summands of the rank-`0` covariant slot range over the empty-index coframe covector, which is
the unit (`coframeS_zero_eq_unitZeroSec`), so every summand reads only `T(unit)`. -/
private lemma riemannianFiberNormSq_eq_of_unit_eq {s : ℕ} (g : SmoothRiemannianMetric I M) (x : M)
    (T T' : TensorRSSpace 0 s I x)
    (h : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (unitZeroSec (I := I) (M := M) x) =
         (T' : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (unitZeroSec (I := I) (M := M) x)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x T =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x T' := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he
  have hn : (Module.finrank ℝ E) = Module.finrank ℝ (TangentSpace I x) := rfl
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := fun a b =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  rw [rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x T e hn horth,
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x T' e hn horth]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  unfold fiberNormSqSummand
  have hKunit : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K k))) : Tensor0SSpace 0 I x) =
      unitZeroSec (I := I) (M := M) x := by
    rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k))) : Tensor0SSpace 0 I x) =
        coframeS (I := I) (M := M) g x 0 e K from rfl]
    exact coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K
  rw [hKunit, h]

/-- **The intrinsic fibre norm of the `tensor0SAsRS`-wrapped abstract curvature operator equals the
fibre norm of the bundled `(0, s)` curvature operator on the unit-scalar lift.** For the abstract
`(0, s)`-tensor connection `nab := tensor0SCovariantDerivative I M s (LeviCivita g)`,
```
rfns(tensor0SAsRS x (riemannOp nab x v w T₀))
  = rfns(riemannOp (tensorCov g 0 s) x v w (unitScalarRSLift x T₀)).
```
The wrapper is the unit-scalar lift (`tensor0SAsRS_eq_unitScalarRSLift`); the abstract curvature value
is the unit-evaluation of the bundled curvature on the lift
(`riemannOp_tensorCov_unitScalarRSLift_unitEval`); and the `(0, s)` fibre norm reads only that
unit-evaluation (`riemannianFiberNormSq_eq_of_unit_eq`). -/
private lemma riemannianFiberNormSq_tensor0SAsRS_riemannOp_abstract_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (v w : TangentSpace I x)
    (T₀ : Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            x v w T₀)) =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (riemannOp (tensorCov (I := I) g 0 s) x v w
          (unitScalarRSLift (I := I) (M := M) x T₀)) := by
  rw [tensor0SAsRS_eq_unitScalarRSLift (I := I) (M := M) x
    (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x v w T₀)]
  refine riemannianFiberNormSq_eq_of_unit_eq (I := I) (M := M) g x _ _ ?_
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x _]
  exact (riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g s x v w T₀).symm

/-- **The `0`-jet transport.** The intrinsic fibre norm of the `tensor0SAsRS`-wrapped unit-evaluated
section `V := unitEvalSection g s S` at `x` equals the intrinsic fibre norm of `S` at `x`: the wrapper
is the unit-scalar lift, and `V x = (S.toSection x)(unit)`, so the `(0, s)` fibre norm reads only that
value (`riemannianFiberNormSq_eq_of_unit_eq`). -/
private lemma riemannianFiberNormSq_tensor0SAsRS_unitEval_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x (unitEvalSection (I := I) (M := M) g s S x)) =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  rw [tensor0SAsRS_eq_unitScalarRSLift (I := I) (M := M) x
    (unitEvalSection (I := I) (M := M) g s S x)]
  refine riemannianFiberNormSq_eq_of_unit_eq (I := I) (M := M) g x _ _ ?_
  rw [show (unitScalarRSLift (I := I) (M := M) x (unitEvalSection (I := I) (M := M) g s S x) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (unitZeroSec (I := I) (M := M) x) =
      unitEvalSection (I := I) (M := M) g s S x from
    unitScalarRSLift_apply_unit (I := I) (M := M) x _]
  rw [unitEvalSection_apply (I := I) (M := M) g s S x]

/-- **The `1`-jet transport along the centre frame.** The intrinsic fibre norm of the
`tensor0SAsRS`-wrapped abstract directional covariant derivative `∇^{abs}_{Bᵢ} V` of `V :=
unitEvalSection g s S` along the orthonormal centre-frame direction `Bᵢ := smoothOrthoFrame g x i` is
bounded by the intrinsic `(0, s + 1)` fibre norm of the gradient `∇S = covGrad g 0 s S`. The abstract
directional derivative of `V` is the slot-`0` reading of the gradient field
(`curriedSection_unitGradFieldGen_apply`); read at the unit it is the slot-`0` curry of `(∇S).toSection
x` along `Bᵢ x` (`tensor0S_curry_covGradBundleEquiv_unit_genVal`), whose squared fibre norm is dominated
by the full `(0, s + 1)` fibre norm of `∇S` over the orthonormal frame
(`riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le`). -/
private lemma riemannianFiberNormSq_tensor0SAsRS_covApply_unitEval_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i)
            (unitEvalSection (I := I) (M := M) g s S) x)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  have hval : covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i)
        (unitEvalSection (I := I) (M := M) g s S) x =
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) := by
    rw [covApply_apply]
    rw [← curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S x
      (smoothOrthoFrame (I := I) g x i x)]
    rw [Tensor0SNabla.curriedSection_apply (I := I) M (unitGradFieldGen (I := I) (M := M) g s S) x]
    rw [unitGradFieldGen_apply (I := I) (M := M) g s S x]
  rw [hval]
  set T : TensorRSSpace 0 (s + 1) I x := (covGrad (I := I) (M := M) g 0 s S).toSection x with hT
  have hcurry : tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
          (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x i x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [show T = covGradBundleEquiv (I := I) (M := M) 0 s x
        ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm T) from
      (ContinuousLinearEquiv.apply_symm_apply _ _).symm]
    rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
      ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm T) (smoothOrthoFrame (I := I) g x i x)]
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hcurry]
  have hrw2 : riemannianFiberNormSq (I := I) (M := M) g 0 s x
      (tensor0SAsRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x))) =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (smoothOrthoFrame (I := I) g x i x)) := by
    rw [tensor0SAsRS_eq_unitScalarRSLift (I := I) (M := M) x _]
    refine riemannianFiberNormSq_eq_of_unit_eq (I := I) (M := M) g x _ _ ?_
    rw [show (unitScalarRSLift (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T
              (smoothOrthoFrame (I := I) g x i x))
            (unitZeroSec (I := I) (M := M) x)) :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) from
      unitScalarRSLift_apply_unit (I := I) (M := M) x _]
  rw [hrw2]
  refine riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le (I := I) (M := M) g s x T
    (fun a => smoothOrthoFrame (I := I) g x a) ?_ i
  intro a b
  exact smoothOrthoFrame_orthonormal_at_center (I := I) g x a b

/-- **Quadratic homogeneity of the `tensor0SAsRS`-wrapped fibre norm.** `rfns(tensor0SAsRS x (c • C)) =
c² · rfns(tensor0SAsRS x C)`: the wrapper is `ℝ`-linear, and the squared fibre norm is `2`-homogeneous
(each Parseval component scales by `c`). -/
private lemma riemannianFiberNormSq_tensor0SAsRS_smul {s : ℕ} (g : SmoothRiemannianMetric I M)
    (x : M) (c : ℝ) (C : Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (tensor0SAsRS (I := I) (M := M) x (c • C)) =
      c ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (tensor0SAsRS (I := I) (M := M) x C) := by
  classical
  have hsmul : tensor0SAsRS (I := I) (M := M) x (c • C) =
      c • tensor0SAsRS (I := I) (M := M) x C := by
    apply tensorRSSpace_ext 0 s x
    intro τ
    show (tensor0SAsRS (I := I) (M := M) x (c • C) :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
        (c • tensor0SAsRS (I := I) (M := M) x C :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ
    rw [tensor0SAsRS_apply (I := I) (M := M) x (c • C) τ, ContinuousLinearMap.smul_apply,
      tensor0SAsRS_apply (I := I) (M := M) x C τ, smul_comm]
  rw [hsmul]
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he
  have hn : (Module.finrank ℝ E) = Module.finrank ℝ (TangentSpace I x) := rfl
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := fun a b =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  rw [rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x _ e hn horth,
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x
      (tensor0SAsRS (I := I) (M := M) x C) e hn horth, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [fiberNormSqSummand_eq_component_sq, fiberNormSqSummand_eq_component_sq,
    fiberNormSqComponent_smul]
  ring

/-- **The per-direction curvature-operator fibre bound on the `tensor0SAsRS`-wrapped abstract curvature.**
Combining the fibre-norm reduction `riemannianFiberNormSq_tensor0SAsRS_riemannOp_abstract_eq` with the
base-point-uniform proportional curvature sup `exists_uniform_riemannOp_tensorCov_proportional_local`:
for the abstract `(0, s)`-tensor connection `nab`,
```
rfns(tensor0SAsRS x (riemannOp nab x v w T₀))
  ≤ Csup s · g(v, v) · g(w, w) · rfns(tensor0SAsRS x T₀),
```
with `Csup` the uniform curvature constant. -/
private lemma riemannianFiberNormSq_tensor0SAsRS_riemannOp_abstract_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Csup : ℝ)
    (hCsup : ∀ (y : M) (v w : TangentSpace I y) (Tt : TensorRSSpace 0 s I y),
        riemannianFiberNormSq (I := I) (M := M) g 0 s y
            (riemannOp (tensorCov (I := I) g 0 s) y v w Tt) ≤
          Csup * g.inner y v v * g.inner y w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s y Tt)
    (x : M) (v w : TangentSpace I x) (T₀ : Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            x v w T₀)) ≤
      Csup * g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x T₀) := by
  rw [riemannianFiberNormSq_tensor0SAsRS_riemannOp_abstract_eq (I := I) (M := M) g s x v w T₀,
    tensor0SAsRS_eq_unitScalarRSLift (I := I) (M := M) x T₀]
  exact hCsup x v w (unitScalarRSLift (I := I) (M := M) x T₀)

/-- **The recentered orthonormal-frame Christoffel-direction uniform sup (posited genuine missing
compactness infrastructure).** For a closed smooth Riemannian manifold `(M, g)` there is a single
nonnegative constant `Kchr`, independent of the base point `x` and the frame index `i`, bounding the
squared `g`-norm of the Christoffel direction `(∇_{Bᵢ} Bᵢ)(x)` of the *recentered* orthonormal frame
`Bᵢ := smoothOrthoFrame g x i` (the frame centred at `x` itself), `(∇_{Bᵢ} Bᵢ)(x) = (LeviCivita
g).toFun Bᵢ x (Bᵢ x)`:
```
∀ x i, g((∇_{Bᵢ} Bᵢ)(x), (∇_{Bᵢ} Bᵢ)(x)) ≤ Kchr.
```

This is the genuine `‖∇B‖_∞`-style envelope of the recentered orthonormal frame's covariant derivative
at its own centre. It is the one genuinely-missing piece of the `R(diff) V` curvature-class fibre
envelope (`exists_riemannSecClass_tensor0SAsRS_fiberOrder_bound`): the entire reduction of that class to
the bundled curvature operator + the curvature sup + the `≤ 1`-jet `unitEvalSection` transports is
established sorry-free above, and the curvature term `R(∇_{Bᵢ} Bᵢ, w) V` is bounded by `Csup ·
g((∇_{Bᵢ} Bᵢ)(x), (∇_{Bᵢ} Bᵢ)(x)) · g(w x, w x) · rfns(S)` — so only this uniform Christoffel-direction
bound remains. No bound on the recentered Christoffel direction exists on disk (the existing uniform
curvature sups are computed frame-freely through the dual-frame route precisely because the recentered
orthonormal frame is not jointly continuous in `(centre, point)` by elementary means); the body is
`sorry` and `exists_riemannSecClass_tensor0SAsRS_fiberOrder_bound` transitively depends on its
`sorryAx`. -/
theorem exists_uniform_recentered_christoffel_direction_gNorm_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kchr : ℝ, 0 ≤ Kchr ∧
      ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
        g.inner x ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x)) ≤ Kchr := by
  sorry

/-- **Child A — the differentiated-curvature `(∇R) S` class fibre envelope (posited genuine `∇R`
content).** For a closed smooth Riemannian manifold `(M, g)` there is a nonnegative valence-dependent
`Ca : ℕ → ℝ` such that, at every rank `s`, smooth `(0, s)`-tensor `S`, point `x`, frame index `i`, and
smooth slot-`0` direction field `w` with `g(w x, w x) ≤ 1`, the `tensor0SAsRS`-wrapped
differentiated-curvature contraction `nablaTensorCurvSec nab Bᵢ Bᵢ w V x` (the `(∇_{Bᵢ} R)(Bᵢ, w) V`
class, `V := unitEvalSection g s S`, `nab` the abstract `(0, s)`-tensor connection) has intrinsic fibre
norm bounded by `Ca s` times the sum of the `∇²S, ∇S, S` fibre norms:
```
rfns(tensor0SAsRS x (nablaTensorCurvSec nab Bᵢ Bᵢ w V x))(x) ≤ Ca s · (rfns(∇²S) + rfns(∇S) + rfns(S)).
```

This is the genuine `‖∇R‖_∞` envelope: `nablaTensorCurvSec` is the covariant derivative of the bundled
curvature operator contracted against the value `w x` (a unit direction) and the `≤ 1`-jet of `V`
(transported to `rfns(∇S), rfns(S)`), uniformly bounded over the compact `M` and the frame indices
through the differentiated-curvature operator tower `diffCurvOp` / `genuineDiffCurvSection`
(`exists_continuous_proportional_diffCurvOp`, `genuineDiffCurvSection_gradedCurvJet`). It is genuine new
content — no uniform fibre bound on `nablaTensorCurvSec` exists on disk; the body is `sorry` and consumers
transitively depend on its `sorryAx`. -/
theorem exists_nablaTensorCurvSec_tensor0SAsRS_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Ca : ℕ → ℝ, (∀ s, 0 ≤ Ca s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E))
        (w : Π b : M, TangentSpace I b),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w) →
        g.inner x (w x) (w x) ≤ 1 →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (nablaTensorCurvSec (I := I) g
                (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) w
                (unitEvalSection (I := I) (M := M) g s S) x)) ≤
          Ca s *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

/-- **Child B — the curvature-`R(diff) V` class fibre envelope (posited genuine `R(∇V)`/`R(∇B,w)`
content).** For a closed smooth Riemannian manifold `(M, g)` there is a nonnegative valence-dependent
`Cb : ℕ → ℝ` such that, at every rank `s`, smooth `(0, s)`-tensor `S`, point `x`, frame index `i`, and
smooth slot-`0` direction field `w` with `g(w x, w x) ≤ 1` whose covariant `1`-jet vanishes at `x`
(`∇_u w(x) = 0` for every `u`), the `tensor0SAsRS`-wrapped curvature `R(diff) V` group
```
R(∇_{Bᵢ} Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ} w) V + 2 R(Bᵢ, w)(∇_{Bᵢ} V)
```
(the three `riemannSec` summands of `secondOrderResidue`) has intrinsic fibre norm bounded by `Cb s`
times the sum of the `∇²S, ∇S, S` fibre norms.

This is the `‖R‖_∞` curvature-operator envelope: each summand is the bundled curvature `riemannOp`
(value-only via `riemannOp_apply_smooth`) contracted against the tangent Christoffel direction
`∇_{Bᵢ} Bᵢ`, the value `w x`, and the `≤ 1`-jet of `V` (`∇_{Bᵢ} V`), uniformly bounded over `M` and the
frame indices by the curvature sup `exists_uniform_riemannOp_tensorCov_proportional_local`; the
`R(Bᵢ, ∇_{Bᵢ} w) V` term vanishes through `∇w(x) = 0`. It is genuine new content (the curvature `R(∇V)`
fibre envelope over the orthonormal centre frame, with the `unitEvalSection` `≤ 1`-jet transports); the
body is `sorry` and consumers transitively depend on its `sorryAx`. -/
theorem exists_riemannSecClass_tensor0SAsRS_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Cb : ℕ → ℝ, (∀ s, 0 ≤ Cb s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E))
        (w : Π b : M, TangentSpace I b),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w) →
        g.inner x (w x) (w x) ≤ 1 →
        (∀ u : TangentSpace I x, (LeviCivita (I := I) g).toFun w x u = 0) →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                  (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame (I := I) g x i)) w
                  (unitEvalSection (I := I) (M := M) g s S) x
                + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g x i)
                  (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w)
                  (unitEvalSection (I := I) (M := M) g s S) x
                + (2 : ℝ) • riemannSec
                  (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g x i) w
                  (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                    (smoothOrthoFrame (I := I) g x i)
                    (unitEvalSection (I := I) (M := M) g s S)) x)) ≤
          Cb s *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  choose Csup hCsup_nn hCsup using fun s =>
    exists_uniform_riemannOp_tensorCov_proportional_local (I := I) (M := M) g s
  obtain ⟨Kchr, hKchr_nn, hKchr⟩ :=
    exists_uniform_recentered_christoffel_direction_gNorm_bound (I := I) (M := M) g
  refine ⟨fun s => 8 * (Csup s * Kchr + Csup s + Csup s), ?_, fun s S x i w hw hww hgrad => ?_⟩
  · intro s; have := hCsup_nn s; positivity
  have hBi : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hChr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame (I := I) g x i))) :=
    covApply_contMDiff (LeviCivita (I := I) g) (hcov := LeviCivita_isContMDiff g) hBi hBi
  have hV : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) b (unitEvalSection (I := I) (M := M) g s S b)) :=
    contMDiff_unitEvalSection (I := I) (M := M) g s S
  have hDw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w)) :=
    covApply_contMDiff (LeviCivita (I := I) g) (hcov := LeviCivita_isContMDiff g) hBi hw
  have hDV : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) b
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S) b)) :=
    covApply_contMDiff (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      hBi hV
  have hT1 : riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)) w (unitEvalSection (I := I) (M := M) g s S) x =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
        ((covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)) x) (w x)
        (unitEvalSection (I := I) (M := M) g s S x) :=
    riemannSec_eq_riemannOp_smooth _ hChr hw hV
  have hT2 : riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i)
        (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w)
        (unitEvalSection (I := I) (M := M) g s S) x =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
        (smoothOrthoFrame (I := I) g x i x)
        ((covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w) x)
        (unitEvalSection (I := I) (M := M) g s S x) :=
    riemannSec_eq_riemannOp_smooth _ hBi hDw hV
  have hT3 : riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) w
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
        (smoothOrthoFrame (I := I) g x i x) (w x)
        ((covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x) :=
    riemannSec_eq_riemannOp_smooth _ hBi hw hDV
  rw [hT1, hT2, hT3]
  have hDw0 : (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w) x = 0 := by
    rw [covApply_apply]; exact hgrad (smoothOrthoFrame (I := I) g x i x)
  rw [hDw0, map_zero]
  set B := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hBdef
  set D := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hDdef
  set A := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)).toSection x)
    with hAdef
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have hCsnn := hCsup_nn s
  have hb1 : riemannianFiberNormSq (I := I) (M := M) g 0 s x
      (tensor0SAsRS (I := I) (M := M) x
        (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
          ((covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x i)) x) (w x)
          (unitEvalSection (I := I) (M := M) g s S x))) ≤ Csup s * Kchr * D := by
    refine le_trans (riemannianFiberNormSq_tensor0SAsRS_riemannOp_abstract_le (I := I) (M := M) g s
      (Csup s) (hCsup s) x _ (w x) (unitEvalSection (I := I) (M := M) g s S x)) ?_
    rw [riemannianFiberNormSq_tensor0SAsRS_unitEval_eq (I := I) (M := M) g s S x]
    rw [covApply_apply]
    have hgv := hKchr x i
    have hgvnn : 0 ≤ g.inner x ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x))
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) := by
      rcases eq_or_ne ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) 0 with h0 | h0
      · rw [h0]; simp
      · exact (g.pos x _ h0).le
    have hwwnn : 0 ≤ g.inner x (w x) (w x) := by
      rcases eq_or_ne (w x) 0 with h0 | h0
      · rw [h0]; simp
      · exact (g.pos x _ h0).le
    have hprod : g.inner x ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)) * g.inner x (w x) (w x) ≤ Kchr := by
      calc g.inner x _ _ * g.inner x (w x) (w x)
          ≤ Kchr * g.inner x (w x) (w x) := mul_le_mul_of_nonneg_right hgv hwwnn
        _ ≤ Kchr * 1 := mul_le_mul_of_nonneg_left hww hKchr_nn
        _ = Kchr := mul_one _
    calc Csup s * g.inner x _ _ * g.inner x (w x) (w x) * D
        = Csup s * (g.inner x _ _ * g.inner x (w x) (w x)) * D := by ring
      _ ≤ Csup s * Kchr * D := by
          apply mul_le_mul_of_nonneg_right _ hD_nn
          exact mul_le_mul_of_nonneg_left hprod hCsnn
  have hb3 : riemannianFiberNormSq (I := I) (M := M) g 0 s x
      (tensor0SAsRS (I := I) (M := M) x
        ((2 : ℝ) • riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          x (smoothOrthoFrame (I := I) g x i x) (w x)
          ((covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x))) ≤
      4 * (Csup s * B) := by
    rw [riemannianFiberNormSq_tensor0SAsRS_smul (I := I) (M := M) g x (2 : ℝ) _]
    have hstep := riemannianFiberNormSq_tensor0SAsRS_riemannOp_abstract_le (I := I) (M := M) g s
      (Csup s) (hCsup s) x (smoothOrthoFrame (I := I) g x i x) (w x)
      ((covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x)
    have hgB : g.inner x (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x i x) = 1 := by
      have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i; rwa [if_pos rfl] at this
    rw [hgB] at hstep
    have hjet1 := riemannianFiberNormSq_tensor0SAsRS_covApply_unitEval_le (I := I) (M := M) g s S x i
    rw [← hBdef] at hjet1
    have hX_le : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            x (smoothOrthoFrame (I := I) g x i x) (w x)
            ((covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x))) ≤
        Csup s * B := by
      refine le_trans hstep ?_
      set X := riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x
          ((covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x)) with hX
      have hX_nn : 0 ≤ X := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
      have hwwnn : 0 ≤ g.inner x (w x) (w x) := by
        rcases eq_or_ne (w x) 0 with h0 | h0
        · rw [h0]; simp
        · exact (g.pos x _ h0).le
      calc Csup s * 1 * g.inner x (w x) (w x) * X
          = Csup s * (g.inner x (w x) (w x) * X) := by ring
        _ ≤ Csup s * (1 * B) := by
            refine mul_le_mul_of_nonneg_left ?_ hCsnn
            calc g.inner x (w x) (w x) * X
                ≤ 1 * X := mul_le_mul_of_nonneg_right hww hX_nn
              _ ≤ 1 * B := by rw [one_mul, one_mul]; exact hjet1
        _ = Csup s * B := by rw [one_mul]
    nlinarith [hX_le, hCsnn, hB_nn]
  have hsub1 := riemannianFiberNormSq_tensor0SAsRS_add_le (I := I) (M := M) g x
    (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
        ((covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)) x) (w x)
        (unitEvalSection (I := I) (M := M) g s S x) + 0)
    ((2 : ℝ) • riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        x (smoothOrthoFrame (I := I) g x i x) (w x)
        ((covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitEvalSection (I := I) (M := M) g s S)) x))
  have hsub2 := riemannianFiberNormSq_tensor0SAsRS_add_le (I := I) (M := M) g x
    (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
        ((covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)) x) (w x)
        (unitEvalSection (I := I) (M := M) g s S x))
    (0 : Tensor0SSpace s I x)
  have h0rfns : riemannianFiberNormSq (I := I) (M := M) g 0 s x
      (tensor0SAsRS (I := I) (M := M) x (0 : Tensor0SSpace s I x)) = 0 := by
    rw [show tensor0SAsRS (I := I) (M := M) x (0 : Tensor0SSpace s I x) =
        (0 : TensorRSSpace 0 s I x) from by
      apply tensorRSSpace_ext 0 s x
      intro τ
      rw [tensor0SAsRS_apply (I := I) (M := M) x (0 : Tensor0SSpace s I x) τ, smul_zero]
      rfl]
    exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 s x
  have hfin : (4 : ℝ) * (Csup s * Kchr) * D + 8 * (Csup s * B) ≤
      8 * (Csup s * Kchr + Csup s + Csup s) * (A + B + D) := by
    have h1 : Csup s * Kchr * D ≤ Csup s * Kchr * (A + B + D) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : Csup s * B ≤ Csup s * (A + B + D) :=
      mul_le_mul_of_nonneg_left (by linarith) hCsnn
    nlinarith [h1, h2, hA_nn, hB_nn, hD_nn, hCsnn, hKchr_nn,
      mul_nonneg (mul_nonneg hCsnn hKchr_nn) hD_nn, mul_nonneg hCsnn hB_nn]
  refine le_trans hsub1 (le_trans ?_ hfin)
  rw [h0rfns] at hsub2
  linarith [hsub1, hsub2, hb1, hb3]

/-- **Child C — the Christoffel-derivative residual fibre envelope (posited genuine internal-cancellation
content).** For a closed smooth Riemannian manifold `(M, g)` there is a nonnegative valence-dependent
`Cc : ℕ → ℝ` such that, at every rank `s`, smooth `(0, s)`-tensor `S`, point `x`, frame index `i`, and
smooth slot-`0` direction field `w` with `g(w x, w x) ≤ 1` whose covariant `1`- and `2`-jets vanish at
`x` (`∇_u w(x) = 0` for every `u`, and `∇_Y(∇_Y w)(x) = 0` for every smooth `Y`), the
`tensor0SAsRS`-wrapped Christoffel-derivative residual `secondOrderChristoffelResidual nab Bᵢ w V x`
(`MetricCompatibility/CovGradCovDerivSecondOrderCommutation`) has intrinsic fibre norm bounded by `Cc s`
times the sum of the `∇²S, ∇S, S` fibre norms.

**This is the genuine internal-cancellation content of the residual `ρ`.** The residual carries seven
iterated-`covApply` summands reading the tangent Christoffel directions `∇_{Bᵢ} Bᵢ`, the bracket
`[Bᵢ, w]`, the `1`-jet `∇_{Bᵢ} w` and the `2`-jet `∇_{Bᵢ}(∇_{Bᵢ} w)` contracted against the `≤ 2`-jet of
`V := unitEvalSection g s S`. Through `∇w(x) = 0`, `∇²w(x) = 0` the explicit single-direction `2`-jet
term `∇_{∇_{Bᵢ}(∇_{Bᵢ} w)} V` and the `∇_{∇_{Bᵢ} w}(·)` terms vanish; the surviving terms — the
`∇_{[Bᵢ, w]}(·)` and `∇_w(·)` order-`≤ 2` derivatives of `V` along the (value-only) bracket direction
`[Bᵢ, w] x = −∇_{w x} Bᵢ` and the Christoffel direction `∇_{∇_{Bᵢ} Bᵢ} w` — contract the `≤ 2`-jet of
`V` (transported to `rfns(∇²S), rfns(∇S), rfns(S)`) against metric/Christoffel direction factors,
uniformly bounded over `M` and the frame indices `(i, a)` by compactness. (The `∇³S`-cancellation that
makes the *full* commutator order-`≤ 2` is internal to this residual together with the curvature classes;
the bound here is the order-`≤ 2` envelope of the residual itself, which is sound.) It is genuine new
content — no fibre envelope of `secondOrderChristoffelResidual` exists on disk; the body is `sorry` and
consumers transitively depend on its `sorryAx`. -/
theorem exists_secondOrderChristoffelResidual_tensor0SAsRS_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Cc : ℕ → ℝ, (∀ s, 0 ≤ Cc s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E))
        (w : Π b : M, TangentSpace I b),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w) →
        g.inner x (w x) (w x) ≤ 1 →
        (∀ u : TangentSpace I x, (LeviCivita (I := I) g).toFun w x u = 0) →
        (∀ Y : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
          (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y w) x (Y x) = 0) →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (secondOrderChristoffelResidual (I := I) g
                (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) w
                (unitEvalSection (I := I) (M := M) g s S) x)) ≤
          Cc s *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

/-- **Posited uniform fibre order of the second-order commutation curvature residue (the genuine
`∇R`-and-curvature content of the `∇³S`-cancellation).** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, frame index `i`, and **smooth
slot-`0` direction field `w` with vanishing covariant `1`- and `2`-jets at `x`** (a unit direction
`g(w x, w x) ≤ 1`, `∇_u w(x) = 0` for every `u`, and `∇_Y(∇_Y w)(x) = 0` for every smooth `Y`), the
intrinsic fibre norm of the `tensor0SAsRS`-wrapped second-order commutation curvature residue
`secondOrderResidue g s S x i w` (`SecondOrderCommutationResidueFiberBound`) is bounded by `C s` times
the **sum** of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(tensor0SAsRS x (secondOrderResidue g s S x i w))(x)
  ≤ C s · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof (glue, TRANSIT over Children A/B/C).** The residue `secondOrderResidue g s S x i w` is, by
definition, the sum of the differentiated-curvature class `nablaTensorCurvSec nab Bᵢ Bᵢ w V x`, the
three-term curvature `R(diff) V` class, and the Christoffel-derivative residual
`secondOrderChristoffelResidual nab Bᵢ w V x`. The `tensor0SAsRS` wrapper is `ℝ`-linear, so the wrapped
residue is the sum of the three wrapped class-groups; the `2`-sub-additivity of the squared fibre norm
(`riemannianFiberNormSq_add_le`) bounds it by `4 ·` the differentiated-curvature envelope (Child A) `+
4 ·` the curvature `R(diff) V` envelope (Child B) `+ 2 ·` the Christoffel-residual envelope (Child C),
each over the `2`-jet-vanishing reading direction `w`. Collecting the three constants into
`C s := 8 · (Ca s + Cb s + Cc s)` gives the bound. Transits the three children's `sorryAx`.

**This is the genuine order-`≤ 2` curvature content of the iterated-Ricci `∇³S`-cancellation.** With the
covariant-`2`-jet-vanishing reading direction `w`, the four covariant-derivative-of-`w` summands of the
residue `secondOrderResidue` — the `R(B, ∇_B w) V` curvature term, and the three Christoffel-residual
summands reading `∇_B(∇_B w)`, `∇_{[B, w]}(·)` and `∇_{∇_B w}(·)` — vanish at `x` through `∇w(x) = 0`,
`∇²w(x) = 0`; the surviving summands are the differentiated-curvature `(∇_B R)(B, w) V` class
(`nablaTensorCurvSec`, tensorial in the reading direction, contracting the `0`-jet of `V` against `∇R`)
and the curvature classes `R(∇_B B, w) V`, `R(B, w)(∇_B V)` (contracting the `≤ 1`-jet of `V` against
`R`). Each reads only the value `w x` (a unit direction) of the reading field, the tangent Christoffel
directions `∇_B B`, and the bracket value `[B, w] x`, contracted against the `≤ 2`-jet of the
unit-evaluated section `V := unitEvalSection g s S` (orders `0, 1, 2`, transported to `rfns(∇²S), rfns(∇S),
rfns(S)`); bounding the differentiated-curvature `‖∇R‖_∞` and the curvature `‖R‖_∞` uniformly over the
compact `M` and the frame indices `(i, a)` gives the single nonnegative valence-dependent `C`.

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian fibre
norm `rfns` of the single tensor `tensor0SAsRS x (secondOrderResidue g s S x i w)` throughout — it never
extracts a per-direction `M → E` quantity. The reading direction `w` enters only through its value `w x`
and its (vanishing) covariant `1`- and `2`-jets at `x`, never through a chart-selection-unbounded
`smoothExtensionTangent` jet — the `2`-jet-vanishing hypotheses are exactly the intrinsic, chart-free
covariant-jet conditions, and the residue is genuinely a `(0, s)`-tensor of `w x`
(`secondOrderResidue_eq_curry_remDiffFib_unit`).

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces
`rfns(tensor0SAsRS x (secondOrderResidue g s S x i w)) = 0`, hence the residue
`secondOrderResidue g s S x i w = 0`, for every such direction `w` and every `S`. By the curry identity
`secondOrderResidue_eq_curry_remDiffFib_unit` this forces the slot-`0` curry of the unit-evaluated frame
commutator `remDiffFib g s S x i` to vanish, hence (Parseval) the frame summand `remDiffFib g s S x i`
itself, hence `∑ᵢ remDiffFib g s S x i = (Curv S).toSection x` would vanish for every `S` — false on a
non-flat manifold already at `s = 0` (`weitzenbock_integrated_covGrad_l2_normSq`). So `C` is genuinely
positive. The body is `sorry` (the uniform `‖∇R‖_∞` and `‖R‖_∞` envelope of the surviving curvature
classes over the `2`-jet-vanishing reading direction, with the unit-evaluation `≤ 2`-jet transports);
consumers transitively depend on its `sorryAx`. -/
theorem exists_secondOrderResidue_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E))
        (w : Π b : M, TangentSpace I b),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w) →
        g.inner x (w x) (w x) ≤ 1 →
        (∀ u : TangentSpace I x, (LeviCivita (I := I) g).toFun w x u = 0) →
        (∀ Y : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
          (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y w) x (Y x) = 0) →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (secondOrderResidue (I := I) (M := M) g s S x i w)) ≤
          C s *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_nablaTensorCurvSec_tensor0SAsRS_fiberOrder_bound (I := I) (M := M) g
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_riemannSecClass_tensor0SAsRS_fiberOrder_bound (I := I) (M := M) g
  obtain ⟨Cc, hCc_nn, hCc⟩ :=
    exists_secondOrderChristoffelResidual_tensor0SAsRS_fiberOrder_bound (I := I) (M := M) g
  refine ⟨fun s => 8 * (Ca s + Cb s + Cc s),
    fun s => by have := hCa_nn s; have := hCb_nn s; have := hCc_nn s; positivity,
    fun s S x i w hw hww hgrad hhess => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- abbreviations for the three class-groups of `secondOrderResidue`
  set GA : Tensor0SSpace s I x :=
    nablaTensorCurvSec (I := I) g
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) w
      (unitEvalSection (I := I) (M := M) g s S) x with hGA
  set GB : Tensor0SSpace s I x :=
    riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)) w
        (unitEvalSection (I := I) (M := M) g s S) x
      + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i)
        (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w)
        (unitEvalSection (I := I) (M := M) g s S) x
      + (2 : ℝ) • riemannSec
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) w
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i)
          (unitEvalSection (I := I) (M := M) g s S)) x with hGB
  set GC : Tensor0SSpace s I x :=
    secondOrderChristoffelResidual (I := I) g
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      (smoothOrthoFrame (I := I) g x i) w
      (unitEvalSection (I := I) (M := M) g s S) x with hGC
  -- `secondOrderResidue = (GA + GB) + GC` definitionally
  have hres : secondOrderResidue (I := I) (M := M) g s S x i w = GA + GB + GC := rfl
  rw [hres]
  -- the three child bounds, specialised at this `(s, S, x, i, w)`
  have hCa' := hCa s S x i w hw hww
  have hCb' := hCb s S x i w hw hww hgrad
  have hCc' := hCc s S x i w hw hww hgrad hhess
  rw [← hGA, ← hA, ← hB, ← hD] at hCa'
  rw [← hGB, ← hA, ← hB, ← hD] at hCb'
  rw [← hGC, ← hA, ← hB, ← hD] at hCc'
  have hstep1 := riemannianFiberNormSq_tensor0SAsRS_add_le (I := I) (M := M) g x (GA + GB) GC
  have hstep2 := riemannianFiberNormSq_tensor0SAsRS_add_le (I := I) (M := M) g x GA GB
  -- chain the two subadditivity steps and the three child bounds
  calc riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x (GA + GB + GC))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x (GA + GB)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x GC) := hstep1
    _ ≤ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensor0SAsRS (I := I) (M := M) x GA) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensor0SAsRS (I := I) (M := M) x GB)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x GC) := by
          nlinarith [hstep2]
    _ ≤ 2 * (2 * (Ca s * (A + B + D)) + 2 * (Cb s * (A + B + D))) +
          2 * (Cc s * (A + B + D)) := by
          nlinarith [hCa', hCb', hCc']
    _ ≤ 8 * (Ca s + Cb s + Cc s) * (A + B + D) := by
          have hCa0 := hCa_nn s; have hCb0 := hCb_nn s; have hCc0 := hCc_nn s
          have hsum_nn : (0 : ℝ) ≤ A + B + D := by positivity
          nlinarith [mul_nonneg hCa0 hsum_nn, mul_nonneg hCb0 hsum_nn, mul_nonneg hCc0 hsum_nn]

/-- **Posited per-direction moving-frame commutator fibre order (the genuine `∇³S`-cancellation
content).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `C : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor
`S`, point `x`, and frame index `i`, the intrinsic fibre norm of the per-direction frame summand
`remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)`
(`MovingFrameRemainderFrameSumBridge`) — the *commutator* `Aᵢ − Dᵢ` of the rough-Laplacian frame trace
and the covariant gradient, both at the single frame direction `Bᵢ := smoothOrthoFrame g x i` — is
bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(remDiffFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuine, irreducible `∇³S`-cancellation content.** The summand carries the top-order
`∇³S` term `∇²_{Bᵢ, Bᵢ}(∇S)`, so it is **not** order-`≤ 2` term-by-term; the bound holds precisely
because the third-order `∇³S` cancels in the commutator `Aᵢ − Dᵢ` through the iterated Ricci identity.
The curried unit-evaluation difference is pinned, for every smooth slot-`0` direction field `w`, by the
rank-generic second-order leading-slot commutation
`covGrad_covDeriv_leadingSlot_secondOrder_commutation`
(`MetricCompatibility/CovGradCovDerivSecondOrderCommutation`, sorry-free):
```
curry (remDiffFib …)(unit)(w)
  = (∇_{Bᵢ} R)(Bᵢ, w) V + ( R(∇_{Bᵢ} Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ} w) V + 2 R(Bᵢ, w)(∇_{Bᵢ} V) ) + ρ,
```
with `V := unitEvalSection g s S`; every right-hand-side summand is order-`≤ 2` in `S` (the `(∇R) S`
and `R(diff) V` classes contract the `≤ 1`-jet of `V` against curvature; the Christoffel residual `ρ`
is a sum of `≤ 2`-fold covariant derivatives of `V`). Reconstructing the intrinsic `(0, s + 1)` fibre
norm from its slot-`0` frame-sum of curried slot-`s` fibre norms
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry`), with the slot-`0` direction realised as
`smoothExtensionTangent x (e a)`, and bounding the curvature residue uniformly over the frame indices
`(i, a)` and the point `x` by compactness gives the single nonnegative valence-dependent `C`.

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian
fibre norm `rfns` of the single tensor `remDiffFib g s S x i` throughout — it never extracts a
per-direction `M → E` quantity, never reads a chart-selection-unbounded `smoothExtensionTangent` jet of
an individual third covariant derivative. The `∇³S`-cancellation is *false term-by-term* through the
non-tensorial reading of the individual third covariant derivatives (chart-selection-unbounded on
`S²`); only the intrinsic frame-summand *difference* `Aᵢ − Dᵢ` is order-`≤ 2`, which is exactly the
content of the commutation identity.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces `rfns(remDiffFib g s S x i) = 0`
for every direction `i`, hence `remDiffFib g s S x i = 0`, hence the frame sum
`∑ᵢ remDiffFib g s S x i = (Curv S).toSection x` (`pointwiseTensorCurv_toSection_eq_frame_sum`) would
vanish for every `S` — false on a non-flat manifold. Already at `s = 0` the scalar commutator defect
`Curv f = Ric(∇f, ·)` integrated is nonzero for a non-harmonic `f` on a curved manifold
(`weitzenbock_integrated_covGrad_l2_normSq`), and `remDiffFib` genuinely uses `S` through its
`∇²_{Bᵢ, Bᵢ}(∇S)` top-order term. So `C` is genuinely positive.

**Proof (the intrinsic `∇³S`-cancellation, over the covariant-`2`-jet-vanishing extension).** The bound
is the single tensorial fibre-order statement of the iterated-Ricci `∇³S`-cancellation: the per-direction
frame summand `remDiffFib g s S x i` is intrinsically a *tensor* (its slot-`0` curry depends only on the
value of the reading direction, not its jet — `secondOrderResidue_eq_curry_remDiffFib_unit` exhibits it as
the order-`≤ 2` curvature residue `secondOrderResidue`). The `(0, s + 1)` fibre norm reconstructs as the
slot-`0` frame-sum of the slot-`s` fibre norms of the `tensor0SAsRS`-wrapped bare curries
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame`, in the `g_x`-orthonormal centre frame
`Bᵢ x`); each curry, read at the unit through the curry identity with the *covariant-`2`-jet-vanishing*
smooth extension `wₐ := exists_twoJetVanishing_tangentExtension g x (Bₐ x)` of the orthonormal direction
(`curry_remDiffFib_unit_eq_secondOrderResidue`, the curry is `w`-jet-independent so `wₐ x = Bₐ x` suffices),
is `secondOrderResidue g s S x i wₐ`. The four covariant-derivative-of-`wₐ` summands of the residue vanish
through `∇wₐ(x) = 0` and `∇²wₐ(x) = 0`, leaving the order-`≤ 2` curvature contractions bounded uniformly
over `(i, a, x)` by `exists_secondOrderResidue_fiberOrder_bound`; summing over the `finrank` slot-`0`
directions gives the single nonnegative valence-dependent `C s := √(finrank · C₀ s)`. A prior attempt to
prove this by a slot-`0` Parseval reconstruction over a *per-direction `secondOrderResidue` per-class* split
was found UNSOUND — the per-class split exposes a chart-selection-unbounded `smoothExtensionTangent` 1-jet
(read by an inner `covApply`) that cancels only in the full residue sum, never class-by-class — so the bound
is established here over the residue's *full* curvature fibre order, which is sound. -/
theorem exists_remDiffFib_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (remDiffFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨Csup, hCsup_nn, hCsup⟩ :=
    exists_secondOrderResidue_fiberOrder_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s),
    fun s => Real.sqrt_nonneg _, fun s S x i => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The `g_x`-orthonormal centre frame `Bₐ x` represents both fibre norms.
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with heC
  have hnC : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := rfl
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  -- Slot-`0` Parseval reconstruction of the `(0, s + 1)` fibre norm of `remDiffFib`.
  rw [riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame (I := I) (M := M) g s x
    (remDiffFib (I := I) (M := M) g s S x i) eC hnC horthC]
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * Csup s := by
    rw [Real.sq_sqrt]; exact mul_nonneg (by positivity) (hCsup_nn s)
  rw [hCsq]
  -- Per-direction: realise each slot-`0` curry through the `2`-jet-vanishing extension of `Bₐ x`.
  have hper : ∀ a : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                remDiffFib (I := I) (M := M) g s S x i)
                (unitZeroSec (I := I) (M := M) x)) (eC a))) ≤ Csup s * (A + B + D) := by
    intro a
    obtain ⟨w, hw_sm, hw_x, hw_grad, hw_hess⟩ :=
      exists_twoJetVanishing_tangentExtension (I := I) (M := M) g x (eC a)
    have hrw : tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            remDiffFib (I := I) (M := M) g s S x i)
            (unitZeroSec (I := I) (M := M) x)) (eC a) =
        secondOrderResidue (I := I) (M := M) g s S x i w := by
      rw [← hw_x]
      exact curry_remDiffFib_unit_eq_secondOrderResidue (I := I) (M := M) g s S x i hw_sm
    rw [hrw]
    have hww : g.inner x (w x) (w x) ≤ 1 := by
      rw [hw_x]; have := horthC a a; rw [if_pos rfl] at this; rw [this]
    exact hCsup s S x i w hw_sm hww hw_grad hw_hess
  refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq; ring

/-- **Posited per-direction pure-Riemann curvature fibre order.** For a closed smooth Riemannian
manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every
covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, and frame index `i`, the
intrinsic fibre norm of the per-direction pure-Riemann curvature fibre `remDiffGenuineFib g s S x i`
(`MovingFrameRemainderFrameSumBridge`) — the slot-`0` uncurry of the curvature-direction CLM
`v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, `Bᵢ := smoothOrthoFrame g x i` — is bounded by `(C s)²` times the **sum** of
the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(remDiffGenuineFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuinely-tensorial pure-Riemann `R(∇S)` contraction**, order-`1` in `S` (it contracts
the `1`-jet `∇_{Bᵢ} S` against the curvature `R(Bᵢ, ·)`, read off the bundled trilinear Riemann
operator `riemannOp`). Its frame sum is the concrete pure-Riemann genuine section `GcurvSection g s S`
(`remDiffGenuineFib_sum_eq_GcurvSection_toSection`, frame-free, tensorial), whose fibre norm is bounded
sorry-free by `‖R‖_∞ · rfns(∇S)` through the curvature-operator `g`-norm sup
(`riemannOp_covGrad_fiberNormSq_le_gen`, `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`,
`IntegratedOrder2WeitzenbockCurvature`); the per-direction fibre norm is the slot-`0` uncurry of the
same curvature-direction CLM (`remDiffGenuineDirCLM`), uniformly bounded over the frame index `i` and
the point `x` by the same compactness sup. The `∇²S` and `S` terms appear only to give the per-direction
bound the common order-`≤ 2` shape shared with the commutator leg (the bound is, in fact, of pure
`rfns(∇S)` order, which is `≤` the full sum since every fibre norm is nonnegative).

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian
fibre norm `rfns` of the single tensor `remDiffGenuineFib g s S x i` throughout — it never extracts a
per-direction `M → E` quantity; the curvature direction is read off the bundled `riemannOp`, genuinely
linear in `v`.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces
`rfns(remDiffGenuineFib g s S x i) = 0` for every direction `i`, hence the frame sum
`∑ᵢ remDiffGenuineFib g s S x i = (GcurvSection g s S).toSection x` would vanish for every `S`. For
`s ≥ 1` this is false on a non-flat manifold (the pure-Riemann trace `GcurvSection` is genuinely
nonzero, `pureRGenuineDiffOp0_eq_GcurvSection`). The `R(∇S)` contraction genuinely uses `S` through its
`∇_{Bᵢ} S` factor. So `C` is genuinely positive. The body is `sorry` (the per-direction curvature-CLM
fibre sup, the slot-`0` uncurry of the uniform `‖R‖_∞` bound); consumers transitively depend on
`sorryAx`. -/
theorem exists_remDiffGenuineFib_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (remDiffGenuineFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  -- The uniform rank-`s` curvature sup family.
  choose Csup hCsup_nn hCsup using fun s =>
    exists_uniform_riemannOp_tensorCov_proportional_local (I := I) (M := M) g s
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s),
    fun s => Real.sqrt_nonneg _, fun s S x i => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The per-direction genuine fibre is the slot-`0` uncurry of the curvature-direction CLM.
  have hfib : remDiffGenuineFib (I := I) (M := M) g s S x i =
      covGradBundleEquiv (I := I) (M := M) 0 s x
        (remDiffGenuineDirCLM (I := I) (M := M) g s S x i) := rfl
  rw [hfib]
  -- The squared constant.
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * Csup s := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (hCsup_nn s)
  rw [hCsq]
  -- Per-direction unit-direction fibre bound on the curvature contraction.
  have hbound : ∀ v : TangentSpace I x, g.inner x v v = 1 →
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (remDiffGenuineDirCLM (I := I) (M := M) g s S x i v) ≤ Csup s * B := by
    intro v hv
    -- Unfold the CLM to its curvature-contraction value.
    have hval : remDiffGenuineDirCLM (I := I) (M := M) g s S x i v =
        riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)
            (smoothOrthoFrame (I := I) g x i x)) := by
      rw [remDiffGenuineDirCLM, LinearMap.coe_toContinuousLinearMap', remDiffGenuineDirLM,
        LinearMap.coe_mk, AddHom.coe_mk]
      rw [show covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x =
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (smoothOrthoFrame (I := I) g x i x) from rfl,
        tensorCov_toFun_eq_covGradBundleEquiv_symm_reading (I := I) (M := M) g s S x
          (smoothOrthoFrame (I := I) g x i x)]
    rw [hval]
    -- The orthonormality scalars at the centre frame are `1`.
    have hgB : g.inner x (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x i x) = 1 := by
      have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i; rwa [if_pos rfl] at this
    -- The curvature sup bound on the contraction.
    have hcurv := hCsup s x (smoothOrthoFrame (I := I) g x i x) v
      ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x)
        (smoothOrthoFrame (I := I) g x i x))
    rw [hgB, hv, mul_one, mul_one] at hcurv
    refine le_trans hcurv ?_
    -- The slot-`0` reading of the gradient along the centre frame is dominated by `rfns(∇S) = B`.
    have hread : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)
          (smoothOrthoFrame (I := I) g x i x)) ≤ B := by
      rw [hB]
      exact riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le (I := I) (M := M) g s x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) (smoothOrthoFrame (I := I) g x)
        (fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b) i
    exact mul_le_mul_of_nonneg_left hread (hCsup_nn s)
  -- Lift the per-direction bound to the full fibre norm via the frame-sum engine.
  refine le_trans
    (riemannianFiberNormSq_covGradBundleEquiv_le_card_mul (I := I) (M := M) g s x
      (remDiffGenuineDirCLM (I := I) (M := M) g s S x i) (Csup s * B) hbound) ?_
  -- `finrank · (Csup · B) = (finrank · Csup) · B ≤ (finrank · Csup) · (A + B + D)`.
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
  calc (Module.finrank ℝ E : ℝ) * (Csup s * B)
      = (Module.finrank ℝ E : ℝ) * Csup s * B := by ring
    _ ≤ (Module.finrank ℝ E : ℝ) * Csup s * (A + B + D) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hfr_nn (hCsup_nn s))
        nlinarith [hA_nn, hD_nn]

end Connection
end Integral
end DifferentialGeometry

end
