import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

/-!
# The differentiated slot-wise curvature transfer

For the Levi-Civita connection `LeviCivita g` of a smooth Riemannian metric `g` on a closed manifold,
this file connects the **tangent-level** differentiated curvature `nablaCurvSec` (the Leibniz-contracted
`∇R` of `SecondBianchi`) to the **tensor-level** differentiated curvature action on `(0, s)`-tensors,
*slot by slot*. It is the differentiated analogue of the (undifferentiated) slot-wise curvature formula
`riemannSec_tensor0SCov_apply_eval` (`TensorSlotwiseCurvature`): where the undifferentiated tensor
curvature `R^{(s)}(X, W)` acts slot-wise through the base-tangent curvature `R^{TM}(X, W)`, the
differentiated tensor curvature `(∇_X R^{(s)})(Y, ·)` acts slot-wise through the tangent-level
`(∇_X R^{TM})(Y, ·) = nablaCurvSec (LeviCivita g) X Y · ·`.

## The differentiated curvature of a bundle covariant derivative

`nablaRiemannSec covT covV X Y Z A x` is the Leibniz-contracted covariant derivative of the
section-level Riemann curvature `riemannSec covV Y Z A` along the derivative direction `X`, for a
*bundle* covariant derivative `covV` on a vector bundle `V` whose two antisymmetric curvature slots
`Y, Z` are tangent fields differentiated by the *tangent* covariant derivative `covT`:
$$
  (\nabla_X R)(Y, Z) A := \nabla_X\bigl(R(Y, Z) A\bigr)
    - R(\nabla_X Y, Z) A - R(Y, \nabla_X Z) A - R(Y, Z)(\nabla_X A),
$$
with the outer derivative and the `∇_X A` correction taken in `covV`, and the slot derivatives
`∇_X Y, ∇_X Z` taken in `covT`. When `V` is the tangent bundle and `covV = covT`, this is exactly
`nablaCurvSec` (`nablaCurvSec_eq_nablaRiemannSec`); the genuine content here is the case `covV =
tensor0SCovariantDerivative s (LeviCivita g)`, the induced `(0, s)`-tensor connection.

## Main results

* `nablaRiemannSec` — the generic differentiated curvature of a bundle covariant derivative, the
  rank-`s` lift of `nablaCurvSec`.
* `nablaCurvSec_eq_nablaRiemannSec` — the tangent-bundle case is `nablaCurvSec` (the `s = 1` litmus
  collapses to this through the slot-wise transfer).
* `nablaTensor0SCurv_succ_consEval` — the differentiated leading-slot peel (the single inductive
  slot-algebra coherence brick), the differentiated analogue of
  `riemannSec_tensor0SCov_succ_consEval`.
* `nablaTensor0SCurv_apply_eval` — **the transfer**: the differentiated `(0, s)`-tensor curvature
  acts as the negated base-tangent slot sum through the tangent-level `nablaCurvSec`,
  $$
    \mathrm{toModel}\bigl((\nabla_X R^{(s)})(Y, \cdot) A\bigr)(u)
      = -\sum_k \mathrm{toModel}(A_x)\bigl(\mathrm{update}\,u\,k\,(\nabla_X R^{TM})(Y)(u_k)\bigr).
  $$
* `nablaTensorCov_baseSlot_eval` — the `(0, s)`-tensor restatement at the level the moving-frame
  remainder bracket-sum consumes, the differentiated analogue of `riemannSec_tensorCov_baseSlot_eval`.
* `nablaTensorCurv_frame_trace_eq_nablaRicci` — **the frame-traced trace bridge**: the orthonormal-frame
  trace of the differentiated base-slot curvature in its first antisymmetric slot, metric-paired against
  the frame, folds into the covariant derivative of the Ricci tensor (`nablaRicci`), through
  `nablaRicci_eq_frame_trace_nablaCurvSec`.
* `frame_sum_nablaTensor0SCurv_baseSlot_eval` — **the frame-traced corollary** consumed by the
  curvature-line assembly: the orthonormal-frame sum (over the leading antisymmetric curvature slot) of
  the differentiated `(0, s)`-tensor curvature is the negated slot sum of the frame-summed differentiated
  base-tangent curvature `∑ᵢ (∇_X R)(Bᵢ, Z)(·)` — the tensor-level Ricci/Bianchi fold, which collapses
  through `nablaTensorCurv_frame_trace_eq_nablaRicci` and the contracted second Bianchi identity
  `contracted_second_bianchi` (`div Ric = ½ d scal`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **The differentiated curvature of a bundle covariant derivative.** For a tangent covariant
derivative `covT` (differentiating the antisymmetric curvature slots `Y, Z`) and a bundle covariant
derivative `covV` on `V` (acting on the section `A` and the outer derivative), this is the standard
Leibniz formula
$$
  (\nabla_X R)(Y, Z) A := \nabla_X\bigl(R(Y, Z) A\bigr)
    - R(\nabla_X Y, Z) A - R(Y, \nabla_X Z) A - R(Y, Z)(\nabla_X A),
$$
with `R(Y, Z) A = riemannSec covV Y Z A` the section-level curvature operator of `covV`, the slot
derivatives `∇_X Y = covApply covT X Y` taken in the tangent connection, and `∇_X A = covApply covV X A`
in the bundle connection. This is the rank-generic lift of `nablaCurvSec` (`SecondBianchi`); the latter
is the special case `V = tangent bundle`, `covV = covT`. -/
def nablaRiemannSec (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (covV : CovariantDerivative I F V)
    (X Y Z : Π b : M, TangentSpace I b) (A : Π b : M, V b) (x : M) : V x :=
  covV.toFun (fun b => riemannSec covV Y Z A b) x (X x)
    - riemannSec covV (covApply covT X Y) Z A x
    - riemannSec covV Y (covApply covT X Z) A x
    - riemannSec covV Y Z (covApply covV X A) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [VectorBundle ℝ F V] in
/-- Definitional unfolding of `nablaRiemannSec`. -/
lemma nablaRiemannSec_def (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (covV : CovariantDerivative I F V)
    (X Y Z : Π b : M, TangentSpace I b) (A : Π b : M, V b) (x : M) :
    nablaRiemannSec covT covV X Y Z A x =
      covV.toFun (fun b => riemannSec covV Y Z A b) x (X x)
        - riemannSec covV (covApply covT X Y) Z A x
        - riemannSec covV Y (covApply covT X Z) A x
        - riemannSec covV Y Z (covApply covV X A) x := rfl

end Generic

section TangentCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **The tangent-bundle case of `nablaRiemannSec` is `nablaCurvSec`.** For a tangent covariant
derivative `cov`, the differentiated curvature `nablaRiemannSec cov cov X Y Z W` of the bundle
`covV := cov` on the tangent bundle is definitionally `nablaCurvSec cov X Y Z W` (`SecondBianchi`).
This is the `s = 1` litmus reference: the single-slot differentiated tensor curvature reduces to the
tangent-level differentiated curvature directly through the slot-wise transfer. -/
lemma nablaCurvSec_eq_nablaRiemannSec
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π b : M, TangentSpace I b) (x : M) :
    nablaCurvSec cov X Y Z W x = nablaRiemannSec cov cov X Y Z W x := rfl

end TangentCase

section TensorTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- Smoothness predicate for a raw `(0, s)`-tensor section: the total-space map is `C^∞`. -/
private abbrev TensorSmooth (s : ℕ) (A : Π b : M, Tensor0SSpace s I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
    (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) b (A b))

/-- **The differentiated base-tangent curvature acting on a fixed slot vector.** The tangent-level
differentiated curvature `(∇_X R^{TM})(Y, Z) u = nablaCurvSec (LeviCivita g) X Y Z (ext u) x`
(`SecondBianchi`), packaged on a fixed slot vector `u` through a smooth extension `ext u =
smoothExtensionTangent x u`. This is the differentiated analogue of `baseSlotCurv`; because
`nablaCurvSec` is the Leibniz-contracted curvature, this value is independent of the smooth extension
chosen (the `∇_X(ext u)`-correction in `nablaCurvSec` cancels the extension-dependence of the leading
derivative), so it is the genuine differentiated curvature `(∇_X R)(Y, Z) u` as a tensor in `u`. -/
def nablaBaseSlotCurv
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    TangentSpace I x :=
  nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
    (fun b => smoothExtensionTangent (I := I) x u b) x

/-- **The differentiated `(0, s)`-tensor curvature, the section-level differentiated curvature of the
induced `(0, s)`-tensor connection.** This specialises the generic `nablaRiemannSec` to the bundle
covariant derivative `covV := tensor0SCovariantDerivative s (LeviCivita g)` with antisymmetric slots
differentiated by the tangent connection `covT := LeviCivita g`. Its value at `x` is the
`(0, s)`-tensor `(∇_X R^{(s)})(Y, Z) A`, the Leibniz-contracted covariant derivative of the tensor
Riemann curvature `R^{(s)}(Y, Z) A = riemannSec (tensor0SCovariantDerivative s …) Y Z A`. -/
def nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) : Tensor0SSpace s I x :=
  nablaRiemannSec (LeviCivita (I := I) g)
    (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (fun b => X b) (fun b => Y b) (fun b => Z b) A x

/-- Definitional unfolding of `nablaTensor0SCurv` into the four Leibniz terms. -/
lemma nablaTensor0SCurv_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    nablaTensor0SCurv (I := I) g s X Y Z A x =
      (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun b => riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b) x (X x)
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b)) (fun b => Z b) A x
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b)) A x
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b)
            (covApply (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (fun b => X b) A) x :=
  rfl

/-- The scalar `(0, 0)`-tensor curvature vanishes for *any* smooth raw direction fields `P, Q` and
smooth scalar section `A` (the rank-`0` flatness of the scalar connection, raw-field form). This
specialises `riemannSec_tensor0SCov_zero_eq_zero` after packaging the raw smooth fields as smooth
sections. -/
private lemma riemannSec_tensor0SCov_zero_raw_eq_zero
    (g : SmoothRiemannianMetric I M)
    {P Q : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Q))
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) P Q A x = 0 := by
  have hz := riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g
    (ContMDiffSection.mk P hP) (ContMDiffSection.mk Q hQ) A hA x
  simpa using hz

/-- **Base case `s = 0` of the differentiated slot-wise transfer.** The differentiated scalar
`(0, 0)`-tensor curvature vanishes: the scalar connection is flat, so its curvature is the zero
section and the differentiated curvature (the Leibniz contraction of a zero section) is zero. -/
theorem nablaTensor0SCurv_zero_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    nablaTensor0SCurv (I := I) g 0 X Y Z A x = 0 := by
  classical
  rw [nablaTensor0SCurv_def]
  have hzero_sec : (fun b => riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (fun b => Y b) (fun b => Z b) A b) = (0 : Π b : M, Tensor0SSpace 0 I b) := by
    funext b
    exact riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g Y Z A hA b
  rw [hzero_sec]
  have hlead : (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).toFun
      (0 : Π b : M, Tensor0SSpace 0 I b) x (X x) = 0 := by
    rw [(tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).isCovariantDerivativeOnUniv.zero
      (Set.mem_univ x)]
    simp
  rw [hlead]
  have hXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Y b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff
  have hXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Z b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff
  rw [riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g hXY Z.contMDiff A hA x,
    riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g Y.contMDiff hXZ A hA x]
  have hcXA : TensorSmooth (I := I) 0 (covApply
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) (fun b => X b) A) :=
    covApply_contMDiff (cov := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      X.contMDiff hA
  rw [riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g Y.contMDiff Z.contMDiff _ hcXA x]
  abel

/-- **The differentiated leading-slot peel of the tensor curvature (the single inductive slot-algebra
coherence brick).** For smooth fields `X, Y, Z`, a smooth `(0, s + 1)`-tensor section `A`, a leading
slot vector `u₀ : T_x M` and a residual tuple `u' : Fin s → T_x M`, the differentiated
`(0, s + 1)`-tensor curvature evaluated on the cons-tuple peels its leading argument: it equals the
differentiated `(0, s)`-tensor curvature of the leading-slot paired section (the contraction of `A`
against a smooth extension of `u₀` in the leading argument), read on `u'`, minus the value of `A` with
the *differentiated* base-tangent curvature `nablaBaseSlotCurv g X Y Z x u₀ = (∇_X R^{TM})(Y, Z) u₀`
inserted into the leading slot:

```
toModel(nablaTensor0SCurv g (s + 1) X Y Z A x)(Fin.cons u₀ u')
  = toModel(nablaTensor0SCurv g s X Y Z (b ↦ A b ⌟ ext u₀ b) x)(u')
    − toModel(A x)(Fin.cons (nablaBaseSlotCurv g X Y Z x u₀) u').
```

**Why this is TRUE.** This is the covariant derivative (along the derivative direction `X`) of the
*undifferentiated* leading-slot peel `riemannSec_tensor0SCov_succ_consEval`, taken term by term through
the curried first-order product rule `tensor0SCovariantDerivative_succ_consEval_peel`
(`TensorMetricCompatible`). Differentiating the undifferentiated peel — whose proof is the generic
Hom-bundle curvature–Leibniz rule `riemannSec_homBundleGen_apply_eq` transported through the fibrewise
currying `tensor0S_curry` — once more in the `X` direction produces, in addition to the rank-`s`
differentiated curvature of the paired section and the leading-slot *differentiated* base curvature,
the same four mixed `(∇A)(∇ext)` cross terms that already cancel between the two derivative orderings
`∇_X ∇_Y` and `∇_X ∇_Z` together with the bracket term in the undifferentiated identity. The Leibniz
`∇_X A`-correction of `nablaTensor0SCurv` is precisely what absorbs the derivative of the leading-slot
contraction `A ⌟ ext u₀` against the leading-slot peel, so the residual base term is the
*extension-independent* differentiated curvature `nablaBaseSlotCurv g X Y Z x u₀` (the symmetric,
torsion-free correction `∇_X(ext u₀)` cancels exactly as in the undifferentiated peel's
`baseSlotCurv`). It is the differentiated analogue of the single inductive ingredient
`riemannSec_tensor0SCov_succ_consEval` of the undifferentiated slot-wise curvature formula.

**Litmus.** At `s = 0` the residual tuple is empty and the paired-section term is the differentiated
*scalar* curvature `nablaTensor0SCurv g 0 …`, which vanishes (`nablaTensor0SCurv_zero_eq_zero`); the
identity reduces to the single-slot peel `toModel(nablaTensor0SCurv g 1 X Y Z A x)(![u₀]) =
−toModel(A x)(![nablaBaseSlotCurv g X Y Z x u₀])`, the `s = 1` collapse to the tangent-level
differentiated curvature (`nablaCurvSec_eq_nablaRiemannSec`).

**Non-vacuity.** The peel is *not* trivially satisfied by the zero family: its leading-slot residue
`nablaBaseSlotCurv g X Y Z x u₀` is the genuine differentiated tangent curvature `nablaCurvSec`, which
is nonzero on a non-flat manifold with a non-parallel curvature (the second Bianchi identity
`second_bianchi_levi_civita` shows its cyclic sum vanishes but the individual term does not), so the
right-hand side genuinely depends on the curvature derivative — replacing `nablaBaseSlotCurv` by `0`
breaks the identity precisely when `∇R ≠ 0`. The body is `sorry`; consumers transitively depend on
`sorryAx`. -/
theorem nablaTensor0SCurv_succ_consEval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A)
    (x : M) (u₀ : TangentSpace I x) (u' : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) (Fin.cons u₀ u') =
      Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s X Y Z
            (fun b => curriedSection I M A b
              (smoothExtensionTangent (I := I) x u₀ b)) x) u' -
        Tensor0SSpace.toModel (A x)
          (Fin.cons (nablaBaseSlotCurv (I := I) g X Y Z x u₀) u') := by
  sorry

/-- **The differentiated slot-wise curvature transfer (tuple form).** For smooth tangent fields
`X, Y, Z`, a smooth `(0, t)`-tensor section `A`, a point `x`, and a tangent tuple
`u : Fin t → T_x M`, the differentiated Riemann curvature of the `(0, t)`-tensor connection acts as the
negated sum of the *differentiated* base-tangent curvature inserted into each argument slot:

```
toModel(nablaTensor0SCurv g t X Y Z A x)(u)
  = − ∑ₖ toModel(A x)(Function.update u k (nablaBaseSlotCurv g X Y Z x (u k))),
```

where `nablaBaseSlotCurv g X Y Z x u = (∇_X R^{TM})(Y, Z) u = nablaCurvSec (LeviCivita g) X Y Z (ext u) x`
is the tangent-level differentiated curvature acting on the `k`-th slot. This is the differentiated
analogue of the slot-wise curvature formula `riemannSec_tensor0SCov_apply_eval` (`TensorSlotwiseCurvature`):
where the undifferentiated tensor curvature `R^{(t)}(X, W)` acts slot-wise through the base-tangent
curvature `R^{TM}(X, W) = baseSlotCurv`, the differentiated tensor curvature `(∇_X R^{(t)})(Y, ·)` acts
slot-wise through the tangent-level differentiated curvature `nablaCurvSec`. It is proved by induction
on `t` using the differentiated leading-slot peel `nablaTensor0SCurv_succ_consEval` (inductive step)
over the differentiated scalar flatness `nablaTensor0SCurv_zero_eq_zero` (base case), mirroring the
undifferentiated induction verbatim. -/
theorem nablaTensor0SCurv_apply_eval
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ (A : Π b : M, Tensor0SSpace t I b), TensorSmooth (I := I) t A →
      ∀ (x : M) (u : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g t X Y Z A x) u =
        - ∑ k : Fin t,
            Tensor0SSpace.toModel (A x)
              (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))) := by
  induction t with
  | zero =>
      intro A hA x u
      rw [nablaTensor0SCurv_zero_eq_zero (I := I) g X Y Z A hA x]
      simp
  | succ s ih =>
      intro A hA x u
      classical
      have hpaired_smooth : TensorSmooth (I := I) s
          (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b)) :=
        ContMDiff.clm_bundle_apply (b := id)
          ((contMDiff_curriedSection_iff_section I M A).mp hA)
          (smoothExtensionTangent_contMDiff (I := I) x (u 0))
      rw [show u = Fin.cons (u 0) (Fin.tail u) from (Fin.cons_self_tail u).symm,
        nablaTensor0SCurv_succ_consEval (I := I) g s X Y Z A hA x (u 0) (Fin.tail u)]
      have hih := ih (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b))
        hpaired_smooth x (Fin.tail u)
      rw [hih]
      have hpx : ∀ v : Fin s → TangentSpace I x,
          Tensor0SSpace.toModel
              (curriedSection I M A x (smoothExtensionTangent (I := I) x (u 0) x)) v =
            Tensor0SSpace.toModel (A x) (Fin.cons (u 0) v) := by
        intro v
        rw [curriedSection_apply, smoothExtensionTangent_eq (I := I) x (u 0),
          TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := A x) (v0 := u 0) (vs := v)]
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [hpx (Function.update (Fin.tail u) k (nablaBaseSlotCurv (I := I) g X Y Z x (Fin.tail u k)))])]
      have hcons_lead :
          Fin.cons (nablaBaseSlotCurv (I := I) g X Y Z x (u 0)) (Fin.tail u) =
            Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0)) := by
        rw [← Fin.update_cons_zero (x := u 0) (p := Fin.tail u)
          (z := nablaBaseSlotCurv (I := I) g X Y Z x (u 0)), Fin.cons_self_tail]
      have hcons_succ : ∀ (k : Fin s),
          Fin.cons (u 0) (Function.update (Fin.tail u) k
              (nablaBaseSlotCurv (I := I) g X Y Z x (Fin.tail u k))) =
            Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)) := by
        intro k
        have htk : Fin.tail u k = u k.succ := rfl
        rw [htk, Fin.cons_update (x := u 0) (p := Fin.tail u) (i := k)
          (y := nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)), Fin.cons_self_tail]
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcons_succ k]), hcons_lead]
      rw [show (- ∑ k : Fin s,
            Tensor0SSpace.toModel (A x)
              (Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)))) -
          Tensor0SSpace.toModel (A x)
            (Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0))) =
          - (Tensor0SSpace.toModel (A x)
              (Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0))) +
              ∑ k : Fin s,
                Tensor0SSpace.toModel (A x)
                  (Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)))) from by
        ring]
      rw [Fin.cons_self_tail]
      congr 1
      rw [Fin.sum_univ_succ
        (f := fun k : Fin (s + 1) =>
          Tensor0SSpace.toModel (A x)
            (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))))]

/-- **The `(0, s)`-tensor restatement of the differentiated slot-wise transfer (base-slot sum form).**
For smooth tangent fields `X, Y, Z`, a smooth `(0, s)`-tensor section `A`, a point `x`, and a covariant
tuple `u : Fin s → T_x M`, the differentiated Riemann curvature of the `(0, s)`-tensor connection acts
as the negated *differentiated* base-tangent slot sum across the covariant slots:

```
toModel(nablaTensor0SCurv g s X Y Z A x)(u)
  = − ∑ₖ toModel(A x)(Function.update u k (nablaBaseSlotCurv g X Y Z x (u k))).
```

This is the differentiated analogue of `riemannSec_tensorCov_baseSlot_eval`
(`TensorWeitzenbockIdentity`), packaged at the level the moving-frame remainder bracket-sum consumes;
it is `nablaTensor0SCurv_apply_eval` read directly on the tuple. -/
theorem nablaTensorCov_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g s X Y Z A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))) :=
  nablaTensor0SCurv_apply_eval (I := I) g s X Y Z A hA x u

/-- **The differentiated base-slot curvature is the tangent-level `nablaCurvSec`, raw-field form.**
For smooth raw tangent fields `X, Y, Z` (packaged as smooth sections) and a fixed slot vector `u`, the
differentiated base-slot curvature `nablaBaseSlotCurv` equals the tangent-level differentiated Riemann
curvature `nablaCurvSec (LeviCivita g) X Y Z (ext u) x` (`SecondBianchi`) — by definition. This is the
bridge identifying the slot quantity of the differentiated tensor transfer with the differentiated
tangent curvature consumed by the contracted-Bianchi frame folds. -/
lemma nablaBaseSlotCurv_eq_nablaCurvSec
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => smoothExtensionTangent (I := I) x u b) x := rfl

/-- **The frame-traced corollary — the Ricci fold at the tensor level.** The orthonormal-frame trace of
the differentiated base-slot curvature in its first antisymmetric slot, metric-paired against the same
frame, folds into the covariant derivative of the Ricci tensor: for smooth tangent fields `X, V`, the
orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, and a fixed slot vector `w`,
$$
  \sum_i g_x\bigl((\nabla_X R)(B_i, V)\,w,\; B_i\bigr)
    = (\nabla_X \mathrm{Ric})(V, \tilde w),
$$
with `(∇_X R)(B_i, V) w = nablaCurvSec (LeviCivita g) X Bᵢ V (ext w) x` the differentiated tangent
curvature on the slot vector `w`, and `ž = ext w = smoothExtensionTangent x w` a smooth extension of
`w`. This is the trace bridge `nablaRicci_eq_frame_trace_nablaCurvSec` read on the slot vector through a
smooth extension: it is the slot-wise Ricci contraction of the differentiated tensor curvature, the
per-slot fold the curvature-line assembly composes with the contracted second Bianchi identity
`contracted_second_bianchi` (`div Ric = ½ d scal`) to collapse the divergence of the differentiated
tensor curvature. -/
theorem nablaTensorCurv_frame_trace_eq_nablaRicci
    (g : SmoothRiemannianMetric I M)
    {X V : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g) X
          (smoothOrthoFrame (I := I) g x i) V
          (fun b => smoothExtensionTangent (I := I) x w b) x)
          (smoothOrthoFrame (I := I) g x i x) =
      nablaRicci (I := I) g X V (fun b => smoothExtensionTangent (I := I) x w b) x := by
  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x w b)) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  exact (nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hX hV hext).symm

/-- **The frame-summed differentiated tensor curvature, slot-wise (the divergence-of-curvature tensor
transfer).** For a fixed derivative direction `X`, a smooth `(0, s)`-tensor section `A`, a covariant
tuple `u`, the orthonormal-frame sum (over the *first antisymmetric* curvature slot `Bᵢ :=
smoothOrthoFrame g x i`) of the differentiated `(0, s)`-tensor curvature acts as the negated slot sum of
the frame-summed differentiated base-tangent curvature:

```
∑ᵢ toModel(nablaTensor0SCurv g s X Bᵢ Z A x)(u)
  = − ∑ₖ ∑ᵢ toModel(A x)(Function.update u k (nablaBaseSlotCurv g X Bᵢ Z x (u k))).
```

This is `nablaTensorCov_baseSlot_eval` (the per-frame transfer) summed over the frame and the finite
slot/frame sums interchanged. It is the divergence-of-curvature shape: tracing the leading antisymmetric
curvature slot against the frame puts each slot of the differentiated tensor curvature into the
frame-summed differentiated tangent curvature `∑ᵢ (∇_X R)(Bᵢ, Z)(·)`, which folds — through the trace
bridge `nablaTensorCurv_frame_trace_eq_nablaRicci` (metric-paired against the frame, per slot) and the
contracted second Bianchi identity `contracted_second_bianchi` (`div Ric = ½ d scal`) — into the
covariant derivative of the Ricci tensor. It is the tensor-level Ricci/Bianchi fold the curvature-line
assembly consumes. -/
theorem frame_sum_nablaTensor0SCurv_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s X
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Z A x) u =
      - ∑ k : Fin s, ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (A x)
            (Function.update u k
              (nablaBaseSlotCurv (I := I) g X
                (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                  (smoothOrthoFrame_smooth (I := I) g x i)) Z x (u k))) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => nablaTensorCov_baseSlot_eval (I := I) g s X
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) Z A hA x u)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]

end TensorTransfer

end Connection
end Integral
end DifferentialGeometry

end
