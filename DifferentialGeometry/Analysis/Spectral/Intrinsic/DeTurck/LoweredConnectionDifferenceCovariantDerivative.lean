import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise

/-! # The covariant derivative of the metrically-lowered connection difference

For two smooth Riemannian metrics `g₁`, `g₀` on a closed manifold, the `g₀`-lowered
connection-difference section `loweredConnDiffSection g₁ g₀` is the covariant `(0, 3)`-tensor
`L(a, b, c) = g₀(D(b, a), c)` with `D = connDiff g₁ g₀` (`a` the direction slot, `b` the
differentiated-vector slot, `c` the lowered output slot).  Because the lowering uses the
*background* metric `g₀`, whose Levi-Civita derivative is metric-compatible (`∇₀ g₀ = 0`), the
`∇₀`-covariant derivative of the lowered section is the `g₀`-lowering of the `∇₀`-covariant
derivative of the connection-difference `(1, 2)`-tensor:
```
(∇₀_u L)(a, b, c) = g₀((∇₀_u D)(a, b), c) = g₀(covDerivDiff ∇₀ ∇₁ U A B x, c),
```
the central bridge `tensorCovDerivAt_loweredConnDiffSection_unitModel_eq`.

Supporting byproducts, each first-class:

* `tensorCovDeriv03_eval` — the first-order `(0, 3)`-tensor covariant-derivative product rule
  `(∇⁰_v S)(a, b, c) = ∂_v(S(A, B, C)) − S(∇⁰_v A, b, c) − S(a, ∇⁰_v B, c) − S(a, b, ∇⁰_v C)`
  on smooth extensions, the rank-`3` sibling of `tensorCovDeriv02_eval`.
* `covDerivDiffDirCLM` — the covariant derivative of the connection difference as a continuous
  linear map in the differentiation direction (`covDerivDiff` reads its direction field only
  through its value at the base point).
* `trace_eq_sum_basis_repr` — the coordinate trace of a tangent endomorphism on any
  `Fin (finrank ℝ E)`-indexed model basis.
* `sum_inner_dualPair_apply_eq_sum_chartBasis_repr` — the `g₀`-dual-pair diagonal pairing
  `∑ₖ g₀(F(♯bᵏ), bₖ)` of a tangent endomorphism `F` against any family `♯bᵏ` characterised by
  `g₀(♯bᵏ, u) = repr(u)ₖ` (the cometric raise of the dual basis) equals the basis-free coordinate
  trace of `F`, read on the `chartModelBasis` coordinates.  This converts the intrinsic cometric
  raised-coframe trace into the model-basis coordinate trace carried by the linearized-Ricci
  order-zero normal form.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [BoundarylessManifold I M] in
/-- **The coordinate trace of a tangent endomorphism on a model basis.**  For any basis `cc` of the
model space indexed by `Fin (finrank ℝ E)` and any continuous endomorphism `F` of the tangent
fibre, the linear-map trace is the diagonal coordinate sum `∑ᵢ repr(F(ccᵢ))ᵢ`.  This is
`LinearMap.trace_eq_matrix_trace` read entrywise through `LinearMap.toMatrix_apply`; the statement
is basis-independent (any two such sums agree through the trace). -/
theorem trace_eq_sum_basis_repr (x : M)
    (cc : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F : TangentSpace I x →L[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x)
        (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x) =
      ∑ i : Fin (Module.finrank ℝ E), cc.repr (F (cc i)) i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (show Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) from cc)
    (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x)]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **The `g₀`-dual-pair diagonal pairing of a tangent endomorphism is its coordinate trace.**
Let `P k` be the `g₀`-raise of the `k`-th dual-basis covector of the model basis `b := finBasis`,
characterised by the inverse property `g₀(P k, u) = repr(u)ₖ` (the form in which the cometric
sharp enters all raised-coframe traces).  Then for any continuous tangent endomorphism `F`, the
diagonal pairing of `F` against the dual pair `(P k, b k)` is the basis-free coordinate trace of
`F`, read on the `chartModelBasis` coordinates:
```
∑ₖ g₀(F(P k), bₖ) = ∑ᵢ chartRepr(F(eᵢ))ᵢ  (= tr F).
```
Proved by expanding `P k = ∑ⱼ repr(P k)ⱼ bⱼ` (whose coefficient matrix is *symmetric*, being the
Gram matrix `repr(P k)ⱼ = g₀(P j, P k)` of the raised family), converting the trace side through
the inverse property `tr F = ∑ⱼ repr(F bⱼ)ⱼ = ∑ⱼ g₀(P j, F bⱼ)`, and matching the two double sums
by that symmetry; the two coordinate-trace readings agree through `trace_eq_sum_basis_repr`. -/
theorem sum_inner_dualPair_apply_eq_sum_chartBasis_repr
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (P : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hP : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g₀.inner x (P k) u = (Module.finBasis ℝ E).repr (u : E) k)
    (F : TangentSpace I x →L[ℝ] TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x (F (P k)) ((Module.finBasis ℝ E) k) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (F ((chartModelBasis E) i)) i := by
  classical
  set bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hbb
  have hQsymm : ∀ k j : Fin (Module.finrank ℝ E),
      bb.repr (P k : E) j = bb.repr (P j : E) k := by
    intro k j
    rw [← hP j (P k), ← hP k (P j)]
    exact g₀.symm x (P j) (P k)
  have hPexp : ∀ k : Fin (Module.finrank ℝ E),
      (P k : TangentSpace I x) =
        ∑ j : Fin (Module.finrank ℝ E), bb.repr (P k : E) j • (bb j : TangentSpace I x) :=
    fun k => (bb.sum_repr (P k : E)).symm
  have hLHS : ∑ k : Fin (Module.finrank ℝ E), g₀.inner x (F (P k)) (bb k) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        bb.repr (P k : E) j * g₀.inner x (F (bb j)) (bb k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [hPexp k]
    rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hTr : ∑ j : Fin (Module.finrank ℝ E), bb.repr (F (bb j)) j =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        bb.repr (P k : E) j * g₀.inner x (F (bb j)) (bb k) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hP j (F (bb j)), g₀.symm x (P j) (F (bb j))]
    conv_lhs => rw [hPexp j]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, hQsymm j k]
  calc ∑ k : Fin (Module.finrank ℝ E), g₀.inner x (F (P k)) (bb k)
      = ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          bb.repr (P k : E) j * g₀.inner x (F (bb j)) (bb k) := hLHS
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          bb.repr (P k : E) j * g₀.inner x (F (bb j)) (bb k) := Finset.sum_comm
    _ = ∑ j : Fin (Module.finrank ℝ E), bb.repr (F (bb j)) j := hTr.symm
    _ = LinearMap.trace ℝ (TangentSpace I x)
          (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :=
        (trace_eq_sum_basis_repr (I := I) (M := M) x bb F).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr (F ((chartModelBasis E) i)) i :=
        trace_eq_sum_basis_repr (I := I) (M := M) x (chartModelBasis E) F

section DirectionLinear

set_option linter.unusedSectionVars false in
/-- **The covariant derivative of the connection difference as a continuous linear map in the
differentiation direction.**  `covDerivDiff cov₀ cov₁ X Y Z x` reads its direction field `X` only
through the value `X x`; this is that dependence packaged as a continuous endomorphism of the
tangent fibre: the `∇₀`-derivative term of the difference section, minus the two Leibniz
corrections, each a composition of fibrewise continuous linear maps. -/
def covDerivDiffDirCLM (cov₀ cov₁ : CovariantDerivative I E (TangentSpace I : M → Type _))
    (Y Z : Π b : M, TangentSpace I b) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  cov₀.toFun (diffSec cov₀ cov₁ Y Z) x
    - (CovariantDerivative.difference cov₁ cov₀ x (Z x)).comp (cov₀.toFun Y x)
    - ((CovariantDerivative.difference cov₁ cov₀ x).flip (Y x)).comp (cov₀.toFun Z x)

set_option linter.unusedSectionVars false in
/-- Evaluation of the direction-linear packaging: at the value `X x` of any direction field `X`,
`covDerivDiffDirCLM` recovers `covDerivDiff cov₀ cov₁ X Y Z x`. -/
@[simp] lemma covDerivDiffDirCLM_apply
    (cov₀ cov₁ : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    covDerivDiffDirCLM (I := I) cov₀ cov₁ Y Z x (X x) =
      covDerivDiff cov₀ cov₁ X Y Z x := by
  simp only [covDerivDiffDirCLM, covDerivDiff, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, covApply_apply]

end DirectionLinear

omit [CompactSpace M] [I.Boundaryless] in
/-- **The first-order `(0,3)`-tensor covariant-derivative product rule.**  For a `(0,3)`-tensor
section `S` differentiable at `x` and tangent vectors `a`, `b`, `c` with their chosen smooth
global extensions `A`, `B`, `C`, the model coercion of the `(0,3)`-tensor covariant derivative
`∇⁰_v S`, read on the triple `![a, b, c]`, obeys the Leibniz product rule
$$
  (\nabla^{0}_v S)(a, b, c) = \partial_v\bigl(S(A, B, C)\bigr)
    - S(\nabla^{0}_v A, b, c) - S(a, \nabla^{0}_v B, c) - S(a, b, \nabla^{0}_v C).
$$
This is the rank-`3` sibling of `tensorCovDeriv02_eval`: three applications of the leading-slot
Koszul peel `tensor0SCovariantDerivative_succ_consEval_peel` over the scalar base case
`tensor0SCovariantDerivative_zero_toModel_apply`. -/
theorem tensorCovDeriv03_eval
    (g : SmoothRiemannianMetric I M)
    (S : Π b : M, Tensor0SSpace 3 I b)
    {x : M} (hS_at : TensorSectionMDiffAt (I := I) 3 S x)
    (a b c : TangentSpace I x) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g) S x v) ![a, b, c] =
      directionalDeriv (I := I) (fun y : M => Tensor0SSpace.toModel (S y)
          ![smoothExtensionTangent (I := I) x a y, smoothExtensionTangent (I := I) x b y,
            smoothExtensionTangent (I := I) x c y]) x v
      - Tensor0SSpace.toModel (S x)
          ![(LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v, b, c]
      - Tensor0SSpace.toModel (S x)
          ![a, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x b) x v, c]
      - Tensor0SSpace.toModel (S x)
          ![a, b, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x c) x v] := by
  classical
  set A : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x a)
      (smoothExtensionTangent_contMDiff (I := I) x a) with hAdef
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x b)
      (smoothExtensionTangent_contMDiff (I := I) x b) with hBdef
  set C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x c)
      (smoothExtensionTangent_contMDiff (I := I) x c) with hCdef
  have hAx : (A : Π y, TangentSpace I y) x = a := smoothExtensionTangent_eq (I := I) x a
  have hBx : (B : Π y, TangentSpace I y) x = b := smoothExtensionTangent_eq (I := I) x b
  have hCx : (C : Π y, TangentSpace I y) x = c := smoothExtensionTangent_eq (I := I) x c
  set W2 : Π y : M, Tensor0SSpace 2 I y :=
    fun y => curriedSection I M S y (A y) with hW2def
  have hW2_at : TensorSectionMDiffAt (I := I) 2 W2 x := by
    classical
    unfold TensorSectionMDiffAt
    have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 2 S hS_at
    have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (A y)) x :=
      A.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    exact MDifferentiableAt.clm_bundle_apply
      (b := id) (ϕ := fun y : M => curriedSection I M S y)
      (v := fun y : M => A y) hCurried hY
  set W1 : Π y : M, Tensor0SSpace 1 I y :=
    fun y => curriedSection I M W2 y (B y) with hW1def
  have hW1_at : TensorSectionMDiffAt (I := I) 1 W1 x := by
    classical
    unfold TensorSectionMDiffAt
    have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 1 W2 hW2_at
    have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (B y)) x :=
      B.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    exact MDifferentiableAt.clm_bundle_apply
      (b := id) (ϕ := fun y : M => curriedSection I M W2 y)
      (v := fun y : M => B y) hCurried hY
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 2 S hS_at A v ![b, c]
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 1 W2 hW2_at B v ![c]
  have hpeel3 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 0 W1 hW1_at C v ![]
  set W0 : Π y : M, Tensor0SSpace 0 I y :=
    fun y => curriedSection I M W1 y (C y) with hW0def
  have hcons_abc : (![a, b, c] : Fin 3 → TangentSpace I x) = Fin.cons (A x) ![b, c] := by
    rw [hAx]; rfl
  have hcons_bc : (![b, c] : Fin 2 → TangentSpace I x) = Fin.cons (B x) ![c] := by
    rw [hBx]; rfl
  have hcons_c : (![c] : Fin 1 → TangentSpace I x) = Fin.cons (C x) ![] := by
    rw [hCx]; rfl
  have hbase : Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W0 x v) ![] =
      directionalDeriv (I := I) (scalarFn I M W0) x v := by
    rw [show (![] : Fin 0 → TangentSpace I x) = (fun i => Fin.elim0 i) from rfl,
      tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g W0 x v]
  have hscalar : scalarFn I M W0 = fun y : M =>
      Tensor0SSpace.toModel (S y) ![A y, B y, C y] := by
    funext y
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M) W0 y]
    change Tensor0SSpace.toModel (curriedSection I M W1 y (C y)) (fun i => Fin.elim0 i) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W1 y) (v0 := C y) (vs := fun i => Fin.elim0 i)]
    change Tensor0SSpace.toModel (curriedSection I M W2 y (B y))
        (Fin.cons (C y) (fun i => Fin.elim0 i)) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W2 y) (v0 := B y) (vs := Fin.cons (C y) (fun i => Fin.elim0 i))]
    change Tensor0SSpace.toModel (curriedSection I M S y (A y))
        (Fin.cons (B y) (Fin.cons (C y) (fun i => Fin.elim0 i))) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := S y) (v0 := A y) (vs := Fin.cons (B y) (Fin.cons (C y) (fun i => Fin.elim0 i)))]
    rfl
  have hcorrB : Tensor0SSpace.toModel (W2 x)
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => B y) x v)
          (Fin.cons (C x) ![])) =
      Tensor0SSpace.toModel (S x)
        ![a, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x b) x v, c] := by
    change Tensor0SSpace.toModel (curriedSection I M S x (A x))
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => B y) x v)
          (Fin.cons (C x) ![])) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := S x) (v0 := A x)
        (vs := Fin.cons ((LeviCivita (I := I) g).toFun (fun y => B y) x v)
          (Fin.cons (C x) ![]))]
    rw [hAx, hCx]; rfl
  have hcorrC : Tensor0SSpace.toModel (W1 x)
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => C y) x v) ![]) =
      Tensor0SSpace.toModel (S x)
        ![a, b, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x c) x v] := by
    change Tensor0SSpace.toModel (curriedSection I M W2 x (B x))
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => C y) x v) ![]) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W2 x) (v0 := B x)
        (vs := Fin.cons ((LeviCivita (I := I) g).toFun (fun y => C y) x v) ![])]
    change Tensor0SSpace.toModel (curriedSection I M S x (A x))
        (Fin.cons (B x)
          (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => C y) x v) ![])) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := S x) (v0 := A x)
        (vs := Fin.cons (B x)
          (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => C y) x v) ![]))]
    rw [hAx, hBx]; rfl
  rw [hcons_abc, hpeel1, hcons_bc, hpeel2, hcons_c, hpeel3, hbase, hscalar, hcorrB, hcorrC]
  have hdd : (fun y : M => Tensor0SSpace.toModel (S y) ![A y, B y, C y]) =
      (fun y : M => Tensor0SSpace.toModel (S y)
        ![smoothExtensionTangent (I := I) x a y, smoothExtensionTangent (I := I) x b y,
          smoothExtensionTangent (I := I) x c y]) := rfl
  rw [hdd]
  have hcorrA : Tensor0SSpace.toModel (S x)
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => (A : Π y, TangentSpace I y) y) x v)
          (Fin.cons (B x) (Fin.cons (C x) ![]))) =
      Tensor0SSpace.toModel (S x)
        ![(LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v, b, c] := by
    rw [hBx, hCx]; rfl
  have hcorrA' : Tensor0SSpace.toModel (S x)
        (Matrix.vecCons ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v)
          (Fin.cons (B x) (Fin.cons (C x) ![]))) =
      Tensor0SSpace.toModel (S x)
        ![(LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v, b, c] := by
    rw [hBx, hCx]; rfl
  have hcorrB' : Tensor0SSpace.toModel (S x)
        (Matrix.vecCons a
          (Matrix.vecCons
            ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x b) x v)
            (Fin.cons (C x) ![]))) =
      Tensor0SSpace.toModel (S x)
        ![a, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x b) x v, c] := by
    rw [hCx]; rfl
  rw [hcorrA, hcorrA', hcorrB']
  abel

end Connection
end Integral

namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-- **The order-one lowered-connection-difference covariant-derivative bridge: `∇₀` commutes with
the `g₀`-lowering of the connection difference.**  The unit-evaluated model `(0, 3)`-form of the
directional covariant derivative `tensorCovDerivAt g₀ 0 3 (loweredConnDiffSection g₁ g₀) x u`
equals the `g₀`-pairing of the covariantly differentiated connection-difference `(1, 2)`-tensor:
```
(∇₀_u L)(a, b, c) = g₀(covDerivDiff ∇₀ ∇₁ U A B x, c),
```
with `L(a, b, c) = g₀(connDiff g₁ g₀ x b a) c` and `U, A, B` the smooth extensions of `u, a, b`
(`A` carries the direction slot of the difference, `B` its differentiated-vector slot, matching
`loweredConnDiffSection_toModel_apply`).  Because the lowering uses the *background* metric, whose
Levi-Civita connection is metric-compatible, no derivative falls on the metric: the proof expands
the `(0, 3)` product rule `tensorCovDeriv03_eval` on smooth extensions, converts the leading
directional-derivative term by the inner-product Leibniz identity `leibniz_inner`, and matches the
remaining terms with the definition of `covDerivDiff` (the `∇₀` of the difference section minus
the two Leibniz corrections); the metric-compatibility correction `g₀(D(b,a), ∇₀_u C)` cancels the
third product-rule term. -/
theorem tensorCovDerivAt_loweredConnDiffSection_unitModel_eq
    (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) (u a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            tensorCovDerivAt (I := I) (M := M) g₀ 0 3
              (loweredConnDiffSection (I := I) g₁ g₀) x u)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      g₀.inner x
        (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (smoothExtensionTangent (I := I) x u)
          (smoothExtensionTangent (I := I) x a)
          (smoothExtensionTangent (I := I) x b) x) c := by
  classical
  have hunit0 : (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) = unitZeroSec (I := I) (M := M) x := rfl
  rw [hunit0, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 3
      (loweredConnDiffSection (I := I) g₁ g₀) x u,
    tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g₀ 3
      (loweredConnDiffSection (I := I) g₁ g₀).toSection x u]
  set V3 : Π y : M, Tensor0SSpace 3 I y := fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
      (loweredConnDiffSection (I := I) g₁ g₀).toSection y)
      (unitZeroSec (I := I) (M := M) y) with hV3def
  have hV3_at : TensorSectionMDiffAt (I := I) 3 V3 x := by
    unfold TensorSectionMDiffAt
    have h := contMDiff_unitEvalSection (I := I) (M := M) g₀ 3
      (loweredConnDiffSection (I := I) g₁ g₀)
    exact (h x).mdifferentiableAt (by simp)
  rw [tensorCovDeriv03_eval g₀ V3 hV3_at a b c u]
  have hval : ∀ (y : M) (p q r : TangentSpace I y),
      Tensor0SSpace.toModel (V3 y) ![p, q, r] =
        g₀.inner y (connDiff (I := I) g₁ g₀ y q p) r := fun y p q r =>
    loweredConnDiffSection_toModel_apply (I := I) g₁ g₀ y p q r
  have hfun : (fun y : M => Tensor0SSpace.toModel (V3 y)
        ![smoothExtensionTangent (I := I) x a y, smoothExtensionTangent (I := I) x b y,
          smoothExtensionTangent (I := I) x c y]) =
      (fun y : M => g₀.inner y
        (connDiff (I := I) g₁ g₀ y (smoothExtensionTangent (I := I) x b y)
          (smoothExtensionTangent (I := I) x a y))
        (smoothExtensionTangent (I := I) x c y)) := by
    funext y; exact hval y _ _ _
  rw [hfun]
  have hVsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => connDiff (I := I) g₁ g₀ y (smoothExtensionTangent (I := I) x b y)
        (smoothExtensionTangent (I := I) x a y))) :=
    connDiff_contMDiff (I := I) g₁ g₀
      (smoothExtensionTangent_contMDiff (I := I) x b)
      (smoothExtensionTangent_contMDiff (I := I) x a)
  have hCsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothExtensionTangent (I := I) x c)) :=
    smoothExtensionTangent_contMDiff (I := I) x c
  have hleib : (mfderiv I 𝓘(ℝ)
        (fun y : M => g₀.inner y
          (connDiff (I := I) g₁ g₀ y (smoothExtensionTangent (I := I) x b y)
            (smoothExtensionTangent (I := I) x a y))
          (smoothExtensionTangent (I := I) x c y)) x) u =
      g₀.inner x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => connDiff (I := I) g₁ g₀ y (smoothExtensionTangent (I := I) x b y)
              (smoothExtensionTangent (I := I) x a y)) x u)
          (smoothExtensionTangent (I := I) x c x)
        + g₀.inner x
          (connDiff (I := I) g₁ g₀ x (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x))
          ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x c) x u) :=
    leibniz_inner (I := I) g₀ hVsm hCsm (x := x) u
  rw [directionalDeriv_eq, hleib]
  rw [hval x ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x a) x u) b c,
    hval x a ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x b) x u) c,
    hval x a b ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x c) x u)]
  rw [smoothExtensionTangent_eq (I := I) x a, smoothExtensionTangent_eq (I := I) x b,
    smoothExtensionTangent_eq (I := I) x c]
  have hRHS : covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (smoothExtensionTangent (I := I) x u)
        (smoothExtensionTangent (I := I) x a)
        (smoothExtensionTangent (I := I) x b) x =
      (LeviCivita (I := I) g₀).toFun
          (fun y : M => connDiff (I := I) g₁ g₀ y (smoothExtensionTangent (I := I) x b y)
            (smoothExtensionTangent (I := I) x a y)) x u
        - connDiff (I := I) g₁ g₀ x b
            ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x a) x u)
        - connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x b) x u) a := by
    unfold covDerivDiff
    simp only [covApply_apply]
    rw [smoothExtensionTangent_eq (I := I) x u, smoothExtensionTangent_eq (I := I) x a,
      smoothExtensionTangent_eq (I := I) x b]
    rfl
  rw [hRHS]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

end DeTurck
end PDE
end DifferentialGeometry
