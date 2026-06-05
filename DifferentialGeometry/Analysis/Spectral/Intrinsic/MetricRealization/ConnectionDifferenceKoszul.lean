import DifferentialGeometry.Geometry.Flow.ConnectionDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIdentity

/-!
# The section-level Koszul difference formula for two Riemannian metrics

For two smooth Riemannian metrics `g₁`, `g₀` on a closed manifold `M`, whose difference is
realized as the symmetric extracted bilinear form `h = ccTensorBilinSymm g₀ T` of a smooth
compactly-supported `(0,2)`-tensor section `T` (the *realize idiom*
`g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm g₀ T x v w`), the connection-difference
tensor `connDiff g₁ g₀ = ∇^{g₁} - ∇^{g₀}` is characterised through the `g₀`-covariant
derivative of `h` by the classical **Koszul difference formula**:
$$
  2\,g_1\bigl(D(Y,X), Z\bigr)
    = (\nabla^{0}_X h)(Y,Z) + (\nabla^{0}_Y h)(X,Z) - (\nabla^{0}_Z h)(X,Y),
$$
where `D = connDiff g₁ g₀`, `D x (Y x) (X x) = ∇^{g₁}_X Y - ∇^{g₀}_X Y`, and `∇^{0} h` is the
Levi-Civita-`g₀` covariant derivative of `h` as a `(0,2)`-tensor.  The inner product on the
left is `g₁` (the perturbed metric); this is forced — only with the `g₁`-inner do both
covariant derivatives enter through their own Koszul characterisations.

## Convention

`connDiff g₁ g₀ x w v` (Mathlib `difference` convention) carries `w` = the *differentiated*
vector value and `v` = the *direction*: `connDiff g₁ g₀ x (σ x) v = ∇^{g₁}_v σ - ∇^{g₀}_v σ`.
With `a` = direction, `b` = differentiated vector, `c` = test vector,
`2 g₁.inner x (connDiff g₁ g₀ x b a) c = (∇⁰_a h)(b,c) + (∇⁰_b h)(a,c) − (∇⁰_c h)(a,b)`.

## Main results

* `tensorCovDeriv02_eval` — the first-order `(0,2)`-tensor product rule
  `(∇⁰_v S)(a,b) = ∂_v(S(a,b)) − S(∇⁰_v a, b) − S(a, ∇⁰_v b)` for a smooth `(0,2)`-tensor
  section, the bridge tying the `(0,2)` covariant derivative to directional derivatives.
* `connDiff_cocycle` — `connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` (the cocycle).
* `covDerivRealizeEval` / `covDerivRealizeEval_eq` — the realized `g₀`-covariant derivative
  `(∇⁰ h)` of `h = ccTensorBilinSymm g₀ T`, packaged as a `(0,3)`-evaluation, and its Leibniz
  product-rule expansion; `liftedRealizeSymm_eval` is the supporting metric-lift bridge.
* `connDiff_koszul_realize` — the section-level Koszul difference formula above (`g₁`-inner).
* `connDiff_koszul_realize_g0` — the `g₀`-lowered form (background-uniform LHS, carrying the
  `(g₁ − g₀)·D` correction).
* `connDiff_diff_koszul_realize` — the difference-of-differences corollary, characterising
  `connDiff g₁ g₂` through the `g₀`-covariant derivatives of `ccTensorBilinSymm g₀ T₁` and
  `ccTensorBilinSymm g₀ T₂`, in the `g₀`-lowered form (carrying the `g₁`-vs-`g₂` inner
  corrections); the identity the higher-order telescoping consumes.
* `connDiff_g0_fibre_abs_bound` — the scalar fibre bound: the `g₀`-pairing of the connection
  difference is dominated by the realized `≤ 1`-jet `covDerivRealizeEval g₀ T` plus the
  perturbation·connection-difference correction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck
open Tensor0SNabla Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M]

omit [CompactSpace M] [I.Boundaryless] in
/-- **The first-order `(0,2)`-tensor covariant-derivative product rule.**  For a smooth
`(0,2)`-tensor section `S` (as a section of `Tensor0SSpace 2`), differentiable at `x`, and
two tangent vectors `a`, `b` at `x` with their chosen smooth global extensions
`A = smoothExtensionTangent x a`, `B = smoothExtensionTangent x b`, the model coercion of the
`(0,2)`-tensor covariant derivative `∇⁰_v S`, read on the pair `![a, b]`, obeys the Leibniz
product rule
$$
  (\nabla^{0}_v S)(a, b) = \partial_v\bigl(S(A, B)\bigr) - S(\nabla^{0}_v A, b) - S(a, \nabla^{0}_v B).
$$
This is two applications of the leading-slot Koszul peel
`tensor0SCovariantDerivative_succ_consEval_peel` over the scalar base case
`tensor0SCovariantDerivative_zero_toModel_apply`. -/
theorem tensorCovDeriv02_eval
    (g : SmoothRiemannianMetric I M)
    (S : Π b : M, Tensor0SSpace 2 I b)
    {x : M} (hS_at : TensorSectionMDiffAt (I := I) 2 S x)
    (a b : TangentSpace I x) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g) S x v) ![a, b] =
      directionalDeriv (I := I) (fun y : M => Tensor0SSpace.toModel (S y)
          ![smoothExtensionTangent (I := I) x a y, smoothExtensionTangent (I := I) x b y]) x v
      - Tensor0SSpace.toModel (S x)
          ![(LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v, b]
      - Tensor0SSpace.toModel (S x)
          ![a, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x b) x v] := by
  classical
  set A : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x a)
      (smoothExtensionTangent_contMDiff (I := I) x a) with hAdef
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x b)
      (smoothExtensionTangent_contMDiff (I := I) x b) with hBdef
  have hAx : (A : Π y, TangentSpace I y) x = a := smoothExtensionTangent_eq (I := I) x a
  have hBx : (B : Π y, TangentSpace I y) x = b := smoothExtensionTangent_eq (I := I) x b
  set W1 : Π y : M, Tensor0SSpace 1 I y :=
    fun y => curriedSection I M S y (A y) with hW1def
  have hW1_at : TensorSectionMDiffAt (I := I) 1 W1 x := by
    classical
    unfold TensorSectionMDiffAt
    have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 1 S hS_at
    have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (A y)) x :=
      A.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    exact MDifferentiableAt.clm_bundle_apply
      (b := id) (ϕ := fun y : M => curriedSection I M S y)
      (v := fun y : M => A y) hCurried hY
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 1 S hS_at A v ![b]
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 0 W1 hW1_at B v ![]
  set W0 : Π y : M, Tensor0SSpace 0 I y :=
    fun y => curriedSection I M W1 y (B y) with hW0def
  have hcons_ab : (![a, b] : Fin 2 → TangentSpace I x) = Fin.cons (A x) ![b] := by
    rw [hAx]; rfl
  have hcons_b : (![b] : Fin 1 → TangentSpace I x) = Fin.cons (B x) ![] := by
    rw [hBx]; rfl
  have hbase : Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W0 x v) ![] =
      directionalDeriv (I := I) (scalarFn I M W0) x v := by
    rw [show (![] : Fin 0 → TangentSpace I x) = (fun i => Fin.elim0 i) from rfl,
      tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g W0 x v]
  have hscalar : scalarFn I M W0 = fun y : M =>
      Tensor0SSpace.toModel (S y) ![A y, B y] := by
    funext y
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M) W0 y]
    change Tensor0SSpace.toModel (curriedSection I M W1 y (B y)) (fun i => Fin.elim0 i) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W1 y) (v0 := B y) (vs := fun i => Fin.elim0 i)]
    change Tensor0SSpace.toModel (curriedSection I M S y (A y))
        (Fin.cons (B y) (fun i => Fin.elim0 i)) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := S y) (v0 := A y) (vs := Fin.cons (B y) (fun i => Fin.elim0 i))]
    rfl
  have hcorr2 : Tensor0SSpace.toModel (W1 x)
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => B y) x v) ![]) =
      Tensor0SSpace.toModel (S x)
        ![a, (LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x b) x v] := by
    change Tensor0SSpace.toModel (curriedSection I M S x (A x))
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => B y) x v) ![]) = _
    rw [curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := S x) (v0 := A x)
        (vs := Fin.cons ((LeviCivita (I := I) g).toFun (fun y => B y) x v) ![])]
    rw [hAx]; rfl
  rw [hcons_ab, hpeel1, hcons_b, hpeel2, hbase, hscalar, hcorr2]
  have hdd : (fun y : M => Tensor0SSpace.toModel (S y) ![A y, B y]) =
      (fun y : M => Tensor0SSpace.toModel (S y)
        ![smoothExtensionTangent (I := I) x a y, smoothExtensionTangent (I := I) x b y]) := rfl
  rw [hdd]
  have hcorr1 : Tensor0SSpace.toModel (S x)
        (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => (A : Π y, TangentSpace I y) y) x v)
          (Fin.cons (B x) ![])) =
      Tensor0SSpace.toModel (S x)
        ![(LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v, b] := by
    rw [hBx]; rfl
  have hcorr2' : Tensor0SSpace.toModel (S x)
        (Matrix.vecCons ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v)
          (Fin.cons (B x) ![])) =
      Tensor0SSpace.toModel (S x)
        ![(LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x a) x v, b] := by
    rw [hBx]; rfl
  rw [hcorr1, hcorr2']
  abel

omit [CompactSpace M] [I.Boundaryless] in
/-- **The connection-difference cocycle.**  For three smooth Riemannian metrics, the
connection-difference tensor satisfies the additive cocycle identity
`connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀`, pointwise on all fibre values.  This is
immediate from the evaluation formula `connDiff_apply`, since both sides equal
`∇^{g₁}_v σ − ∇^{g₂}_v σ` on a smooth extension `σ` of the differentiated vector. -/
theorem connDiff_cocycle (g₁ g₂ g₀ : SmoothRiemannianMetric I M)
    (x : M) (w v : TangentSpace I x) :
    connDiff (I := I) g₁ g₂ x w v =
      connDiff (I := I) g₁ g₀ x w v - connDiff (I := I) g₂ g₀ x w v := by
  classical
  set A : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hAdef
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (A y)) x :=
    A.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hσx : (A : Π y, TangentSpace I y) x = w := smoothExtensionTangent_eq (I := I) x w
  have h12 := connDiff_apply (I := I) g₁ g₂ hσ v
  have h10 := connDiff_apply (I := I) g₁ g₀ hσ v
  have h20 := connDiff_apply (I := I) g₂ g₀ hσ v
  rw [hσx] at h12 h10 h20
  rw [h12, h10, h20]; abel

/-- **The `g₀`-covariant derivative of the realized perturbation, evaluated as a
`(0,3)`-tensor.**  For the realized symmetric perturbation `h = ccTensorBilinSymm g₀ T`,
packaged as the `(0,2)`-tensor `realizeSymmCcTensor g₀ T`, this is the model coercion of its
metric-lifted `(0,2)`-tensor `g₀`-covariant derivative `∇⁰ h`, read on the triple
`![u, p, q]` (the leftmost slot `u` is the differentiation direction).  It equals
`(∇⁰_u h)(p, q)`. -/
def covDerivRealizeEval (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (u p q : TangentSpace I x) : ℝ :=
  Tensor0SSpace.toModel
    (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
      (liftedTensorSection (I := I) (M := M) g₀ 0 2
        (realizeSymmCcTensor (I := I) g₀ T).toSection) x u) ![p, q]

/-- **The realized perturbation, evaluated as a `(0,2)`-tensor through the metric lift.**
`toModel (lifted realizeSymm)(![a,b]) = ccTensorBilinSymm g₀ T x a b`: at rank `(0,2)` the
metric lift is a pure reindexing, and the realized `(0,2)`-tensor's extracted bilinear form is
exactly the symmetric perturbation `ccTensorBilinSymm`. -/
theorem liftedRealizeSymm_eval (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (a b : TangentSpace I x) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ T).toSection x) ![a, b] =
      ccTensorBilinSymm (I := I) g₀ T x a b := by
  rw [toModel_liftedTensorSection_zero_eq_apply_unit_reindex (I := I) (M := M) g₀ 2
    (realizeSymmCcTensor (I := I) g₀ T).toSection x ![a, b]]
  have hbil := realizeSymmCcTensor_ccTensorBilin_apply (I := I) g₀ T x a b
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply] at hbil
  rw [← hbil]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The realized covariant-derivative `(0,3)`-evaluation as the Leibniz product rule.**
`covDerivRealizeEval g₀ T x u p q = (∇⁰_u h)(p,q)` expands by the `(0,2)`-tensor product rule
`tensorCovDeriv02_eval` and the metric-lift bridge `liftedRealizeSymm_eval` into the explicit
Leibniz form on `h = ccTensorBilinSymm g₀ T`:
$$
  (\nabla^{0}_u h)(p,q) = \partial_u\bigl(h(P,Q)\bigr) - h(\nabla^{0}_u P, q) - h(p, \nabla^{0}_u Q),
$$
where `P = smoothExtensionTangent x p`, `Q = smoothExtensionTangent x q` are smooth extensions. -/
theorem covDerivRealizeEval_eq (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (u p q : TangentSpace I x) :
    covDerivRealizeEval (I := I) g₀ T x u p q =
      directionalDeriv (I := I) (fun y : M => ccTensorBilinSymm (I := I) g₀ T y
          (smoothExtensionTangent (I := I) x p y) (smoothExtensionTangent (I := I) x q y)) x u
      - ccTensorBilinSymm (I := I) g₀ T x
          ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x p) x u) q
      - ccTensorBilinSymm (I := I) g₀ T x p
          ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x q) x u) := by
  classical
  unfold covDerivRealizeEval
  rw [tensorCovDeriv02_eval (I := I) g₀
    (liftedTensorSection (I := I) (M := M) g₀ 0 2 (realizeSymmCcTensor (I := I) g₀ T).toSection)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g₀ 0 2
      (realizeSymmCcTensor (I := I) g₀ T).toSection x) p q u]
  have hfun : (fun y : M => Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ T).toSection y)
        ![smoothExtensionTangent (I := I) x p y, smoothExtensionTangent (I := I) x q y]) =
      (fun y : M => ccTensorBilinSymm (I := I) g₀ T y
        (smoothExtensionTangent (I := I) x p y) (smoothExtensionTangent (I := I) x q y)) := by
    funext y; rw [liftedRealizeSymm_eval]
  rw [hfun, liftedRealizeSymm_eval, liftedRealizeSymm_eval]

omit [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **The directional derivative of the realized perturbation as a difference of the two
metrics' inner-product directional derivatives.**  Under the realize idiom
`g₁ = g₀ + ccTensorBilinSymm g₀ T`, for smooth tangent fields `P`, `Q` the directional
derivative of `y ↦ h(P,Q)` equals the difference of the directional derivatives of the two
metric pairings.  This is metric-pairing smoothness (`contMDiff_g_inner_of_smooth_sections`)
plus `mfderiv` linearity. -/
theorem dirDeriv_ccTensorBilinSymm_eq
    (g₁ g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (P Q : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    directionalDeriv (I := I) (fun y : M => ccTensorBilinSymm (I := I) g₀ T y (P y) (Q y)) x u =
      directionalDeriv (I := I) (fun y : M => g₁.inner y (P y) (Q y)) x u
        - directionalDeriv (I := I) (fun y : M => g₀.inner y (P y) (Q y)) x u := by
  have hg1 : MDiffAt (fun y : M => g₁.inner y (P y) (Q y)) x :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g₁ P Q).contMDiffAt.mdifferentiableAt
      (by simp)
  have hg0 : MDiffAt (fun y : M => g₀.inner y (P y) (Q y)) x :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g₀ P Q).contMDiffAt.mdifferentiableAt
      (by simp)
  have hfun : (fun y : M => ccTensorBilinSymm (I := I) g₀ T y (P y) (Q y)) =
      (fun y : M => g₁.inner y (P y) (Q y)) - (fun y : M => g₀.inner y (P y) (Q y)) := by
    funext y; rw [Pi.sub_apply, hr y (P y) (Q y)]; ring
  unfold directionalDeriv
  rw [hfun, mfderiv_sub hg1 hg0]
  rfl

/-- **The section-level Koszul difference formula** (realize idiom).  For two smooth Riemannian
metrics with `g₁ = g₀ + ccTensorBilinSymm g₀ T`, the connection-difference tensor
`connDiff g₁ g₀` is characterised through the `g₀`-covariant derivative of the realized
perturbation `h = ccTensorBilinSymm g₀ T`:
$$
  2\,g_1\bigl((\nabla^{g_1}-\nabla^{g_0})_a\,b, c\bigr)
    = (\nabla^{0}_a h)(b,c) + (\nabla^{0}_b h)(a,c) - (\nabla^{0}_c h)(a,b),
$$
with `a` the direction, `b` the differentiated vector, `c` the test vector; the inner product
is `g₁` (forced).  The proof subtracts the two Levi-Civita Koszul identities (`koszul_identity`
for `g₁` and `g₀`), splits the difference of inner-product pairings by the realize identity
(`dirDeriv_ccTensorBilinSymm_eq` and bilinearity), expands the `(0,2)`-covariant derivative of
`h` by the product rule (`covDerivRealizeEval_eq`), and reconciles the Lie-bracket terms with the
covariant-derivative corrections using torsion-freeness (`torsion_eq_zero_iff`) and the symmetry
of `ccTensorBilinSymm`. -/
theorem connDiff_koszul_realize
    (g₁ g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (a b c : TangentSpace I x) :
    2 * g₁.inner x
        (connDiff (I := I) g₁ g₀ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c =
      covDerivRealizeEval (I := I) g₀ T x a b c
      + covDerivRealizeEval (I := I) g₀ T x b a c
      - covDerivRealizeEval (I := I) g₀ T x c a b := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x a)
      (smoothExtensionTangent_contMDiff (I := I) x a) with hXdef
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x b)
      (smoothExtensionTangent_contMDiff (I := I) x b) with hYdef
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x c)
      (smoothExtensionTangent_contMDiff (I := I) x c) with hZdef
  have hXx : (X : Π y, TangentSpace I y) x = a := smoothExtensionTangent_eq (I := I) x a
  have hYx : (Y : Π y, TangentSpace I y) x = b := smoothExtensionTangent_eq (I := I) x b
  have hZx : (Z : Π y, TangentSpace I y) x = c := smoothExtensionTangent_eq (I := I) x c
  have hXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Z y)) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- abbreviations for the connection values at x
  set DXY : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y => Y y) x (X x) with hDXY
  set DYX : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y => X y) x (Y x) with hDYX
  set DXZ : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y => Z y) x (X x) with hDXZ
  set DZX : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y => X y) x (Z x) with hDZX
  set DYZ : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y => Z y) x (Y x) with hDYZ
  set DZY : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y => Y y) x (Z x) with hDZY
  -- RHS: expand each covDerivRealizeEval via covDerivRealizeEval_eq
  rw [covDerivRealizeEval_eq, covDerivRealizeEval_eq, covDerivRealizeEval_eq]
  -- Koszul identities for g₁ and g₀ on the smooth-extension fields X, Y, Z
  have hkos1 := koszul_identity (I := I) (LeviCivita (I := I) g₁)
    (LeviCivita_torsion_eq_zero (I := I) g₁) (LeviCivita_isMetricCompatible (I := I) g₁)
    (X := fun y => X y) (Y := fun y => Y y) (Z := fun y => Z y) hXd hYd hZd
  have hkos0 := koszul_identity (I := I) (LeviCivita (I := I) g₀)
    (LeviCivita_torsion_eq_zero (I := I) g₀) (LeviCivita_isMetricCompatible (I := I) g₀)
    (X := fun y => X y) (Y := fun y => Y y) (Z := fun y => Z y) hXd hYd hZd
  -- connDiff value on Y (differentiated) and X (direction)
  have hcd := connDiff_apply (I := I) g₁ g₀ (σ := fun y => Y y) hYd (X x)
  -- rewrite LHS connDiff to the smooth-extension fields
  rw [show smoothExtensionTangent (I := I) x b x = (Y : Π y, TangentSpace I y) x from rfl,
      show smoothExtensionTangent (I := I) x a x = (X : Π y, TangentSpace I y) x from rfl]
  rw [hcd]
  -- distribute g₁.inner over the subtraction
  have hsub : g₁.inner x
        ((LeviCivita (I := I) g₁).toFun (fun y => Y y) x (X x) - DXY) c =
      g₁.inner x ((LeviCivita (I := I) g₁).toFun (fun y => Y y) x (X x)) c
        - g₁.inner x DXY c := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [hsub]
  -- realize on the g₀-connection term: g₁.inner DXY c = g₀.inner DXY c + h DXY c
  rw [hr x DXY c]
  -- LHS now: 2 * (g₁.inner ((LeviCivita g₁) Y x (X x)) c - (g₀.inner DXY c + h DXY c))
  -- Establish the two Koszul LHS forms as 2 * ... and substitute.
  have hk1 : 2 * g₁.inner x ((LeviCivita (I := I) g₁).toFun (fun y => Y y) x (X x)) (Z x) =
      directionalDeriv (I := I) (fun b => g₁.inner b (Y b) (Z b)) x (X x)
      + directionalDeriv (I := I) (fun b => g₁.inner b (X b) (Z b)) x (Y x)
      - directionalDeriv (I := I) (fun b => g₁.inner b (X b) (Y b)) x (Z x)
      + g₁.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Y y) x) (Z x)
      - g₁.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Z y) x) (Y x)
      - g₁.inner x (VectorField.mlieBracket I (fun y => Y y) (fun y => Z y) x) (X x) := hkos1
  have hk0 : 2 * g₀.inner x DXY (Z x) =
      directionalDeriv (I := I) (fun b => g₀.inner b (Y b) (Z b)) x (X x)
      + directionalDeriv (I := I) (fun b => g₀.inner b (X b) (Z b)) x (Y x)
      - directionalDeriv (I := I) (fun b => g₀.inner b (X b) (Y b)) x (Z x)
      + g₀.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Y y) x) (Z x)
      - g₀.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Z y) x) (Y x)
      - g₀.inner x (VectorField.mlieBracket I (fun y => Y y) (fun y => Z y) x) (X x) := hkos0
  -- torsion-free bracket relations
  have hbXY : VectorField.mlieBracket I (fun y => X y) (fun y => Y y) x = DXY - DYX :=
    (((CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g₀)).mp
      (LeviCivita_torsion_eq_zero (I := I) g₀)) hXd hYd).symm
  have hbXZ : VectorField.mlieBracket I (fun y => X y) (fun y => Z y) x = DXZ - DZX :=
    (((CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g₀)).mp
      (LeviCivita_torsion_eq_zero (I := I) g₀)) hXd hZd).symm
  have hbYZ : VectorField.mlieBracket I (fun y => Y y) (fun y => Z y) x = DYZ - DZY :=
    (((CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g₀)).mp
      (LeviCivita_torsion_eq_zero (I := I) g₀)) hYd hZd).symm
  -- realize on the bracket inner products (g₁ - g₀ = h on brackets)
  have hbr1 : g₁.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Y y) x) (Z x)
      = g₀.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Y y) x) (Z x)
        + ccTensorBilinSymm (I := I) g₀ T x (DXY - DYX) (Z x) := by
    rw [hr x _ (Z x), hbXY]
  have hbr2 : g₁.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Z y) x) (Y x)
      = g₀.inner x (VectorField.mlieBracket I (fun y => X y) (fun y => Z y) x) (Y x)
        + ccTensorBilinSymm (I := I) g₀ T x (DXZ - DZX) (Y x) := by
    rw [hr x _ (Y x), hbXZ]
  have hbr3 : g₁.inner x (VectorField.mlieBracket I (fun y => Y y) (fun y => Z y) x) (X x)
      = g₀.inner x (VectorField.mlieBracket I (fun y => Y y) (fun y => Z y) x) (X x)
        + ccTensorBilinSymm (I := I) g₀ T x (DYZ - DZY) (X x) := by
    rw [hr x _ (X x), hbYZ]
  -- directional-deriv realize splits (for the 3 pairings)
  have hdd1 := dirDeriv_ccTensorBilinSymm_eq (I := I) g₁ g₀ T hr Y Z x (X x)
  have hdd2 := dirDeriv_ccTensorBilinSymm_eq (I := I) g₁ g₀ T hr X Z x (Y x)
  have hdd3 := dirDeriv_ccTensorBilinSymm_eq (I := I) g₁ g₀ T hr X Y x (Z x)
  -- ccTensorBilinSymm linearity (CLM) on the bracket arguments
  have hlin1 : ccTensorBilinSymm (I := I) g₀ T x (DXY - DYX) (Z x)
      = ccTensorBilinSymm (I := I) g₀ T x DXY (Z x)
        - ccTensorBilinSymm (I := I) g₀ T x DYX (Z x) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  have hlin2 : ccTensorBilinSymm (I := I) g₀ T x (DXZ - DZX) (Y x)
      = ccTensorBilinSymm (I := I) g₀ T x DXZ (Y x)
        - ccTensorBilinSymm (I := I) g₀ T x DZX (Y x) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  have hlin3 : ccTensorBilinSymm (I := I) g₀ T x (DYZ - DZY) (X x)
      = ccTensorBilinSymm (I := I) g₀ T x DYZ (X x)
        - ccTensorBilinSymm (I := I) g₀ T x DZY (X x) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  -- symmetry of ccTensorBilinSymm to match slot orders
  have hsym1 : ccTensorBilinSymm (I := I) g₀ T x DXZ (Y x)
      = ccTensorBilinSymm (I := I) g₀ T x (Y x) DXZ := ccTensorBilinSymm_symm (I := I) g₀ T x _ _
  have hsym2 : ccTensorBilinSymm (I := I) g₀ T x DYZ (X x)
      = ccTensorBilinSymm (I := I) g₀ T x (X x) DYZ := ccTensorBilinSymm_symm (I := I) g₀ T x _ _
  have hsym3 : ccTensorBilinSymm (I := I) g₀ T x DZY (X x)
      = ccTensorBilinSymm (I := I) g₀ T x (X x) DZY := ccTensorBilinSymm_symm (I := I) g₀ T x _ _
  -- normalize the goal's covDerivRealizeEval-produced terms to the bundled fields X,Y,Z
  rw [show smoothExtensionTangent (I := I) x a = ((X : Π y, TangentSpace I y)) from rfl,
      show smoothExtensionTangent (I := I) x b = ((Y : Π y, TangentSpace I y)) from rfl,
      show smoothExtensionTangent (I := I) x c = ((Z : Π y, TangentSpace I y)) from rfl] at *
  -- normalize goal directions a,b,c to X x, Y x, Z x to match the abbreviations
  rw [← hXx, ← hYx, ← hZx]
  linarith [hk0, hk1, hbr1, hbr2, hbr3, hlin1, hlin2, hlin3,
    hdd1, hdd2, hdd3, hsym1, hsym2, hsym3]


/-- **The Koszul difference formula, `g₀`-lowered form.**  Pairing the connection-difference
tensor against the *background* metric `g₀` (rather than the perturbed `g₁`) carries an extra
correction `−2·h(D, c)` where `h = ccTensorBilinSymm g₀ T` and `D = connDiff g₁ g₀ x b a`.  This
is the form whose left-hand side is metric-uniform in `g₀`, used to telescope two perturbations
against a common background.  It follows from `connDiff_koszul_realize` and the realize
identity. -/
theorem connDiff_koszul_realize_g0
    (g₁ g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (a b c : TangentSpace I x) :
    2 * g₀.inner x
        (connDiff (I := I) g₁ g₀ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c =
      (covDerivRealizeEval (I := I) g₀ T x a b c
        + covDerivRealizeEval (I := I) g₀ T x b a c
        - covDerivRealizeEval (I := I) g₀ T x c a b)
      - 2 * ccTensorBilinSymm (I := I) g₀ T x
          (connDiff (I := I) g₁ g₀ x
            (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x)) c := by
  have h1 := connDiff_koszul_realize (I := I) g₁ g₀ T hr x a b c
  set D := connDiff (I := I) g₁ g₀ x
    (smoothExtensionTangent (I := I) x b x) (smoothExtensionTangent (I := I) x a x) with hD
  rw [hr x D c] at h1
  linarith [h1]

/-- **The difference-of-differences Koszul formula** (`g₀`-lowered).  For two perturbations
`T₁`, `T₂` realized over the common background `g₀` (`g₁ = g₀ + h₁`, `g₂ = g₀ + h₂`), the
`g₀`-paired connection-difference `connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` (the
cocycle) is the difference of the two `g₀`-lowered Koszul characterisations.  The leading term
is the difference of the realized `(0,3)`-covariant-derivative evaluations
`covDerivRealizeEval g₀ T₁ − covDerivRealizeEval g₀ T₂`; the trailing correction terms carry the
`(g_i − g₀)`-factor times the respective connection difference, handled honestly (they do not
cancel pointwise).  This is the identity the higher-order Faà-di-Bruno telescoping consumes.
Proved from `connDiff_cocycle` and `connDiff_koszul_realize_g0`. -/
theorem connDiff_diff_koszul_realize
    (g₁ g₂ g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (hr2 : ∀ (y : M) (v w : TangentSpace I y),
      g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w)
    (x : M) (a b c : TangentSpace I x) :
    2 * g₀.inner x
        (connDiff (I := I) g₁ g₂ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c =
      ((covDerivRealizeEval (I := I) g₀ T₁ x a b c
          + covDerivRealizeEval (I := I) g₀ T₁ x b a c
          - covDerivRealizeEval (I := I) g₀ T₁ x c a b)
        - 2 * ccTensorBilinSymm (I := I) g₀ T₁ x
            (connDiff (I := I) g₁ g₀ x
              (smoothExtensionTangent (I := I) x b x)
              (smoothExtensionTangent (I := I) x a x)) c)
      - ((covDerivRealizeEval (I := I) g₀ T₂ x a b c
          + covDerivRealizeEval (I := I) g₀ T₂ x b a c
          - covDerivRealizeEval (I := I) g₀ T₂ x c a b)
        - 2 * ccTensorBilinSymm (I := I) g₀ T₂ x
            (connDiff (I := I) g₂ g₀ x
              (smoothExtensionTangent (I := I) x b x)
              (smoothExtensionTangent (I := I) x a x)) c) := by
  have hk1 := connDiff_koszul_realize_g0 (I := I) g₁ g₀ T₁ hr1 x a b c
  have hk2 := connDiff_koszul_realize_g0 (I := I) g₂ g₀ T₂ hr2 x a b c
  have hcoc := connDiff_cocycle (I := I) g₁ g₂ g₀ x
    (smoothExtensionTangent (I := I) x b x) (smoothExtensionTangent (I := I) x a x)
  rw [hcoc, map_sub, ContinuousLinearMap.sub_apply]
  ring_nf
  linarith [hk1, hk2]

/-- **Scalar fibre bound for the `g₀`-paired connection difference.**  The absolute value of the
`g₀`-pairing `2·g₀(connDiff g₁ g₀ · b a, c)` is controlled by the three realized
`(0,3)`-covariant-derivative evaluations `covDerivRealizeEval g₀ T` (the `≤ 1`-jet of
`h = ccTensorBilinSymm g₀ T`) plus the perturbation·connection-difference correction.  This is
the triangle inequality applied to the `g₀`-lowered Koszul difference formula
`connDiff_koszul_realize_g0`; together with the realize-jet domination of `covDerivRealizeEval`
by the jet-sum of `T`, it controls the connection difference by the `≤ 1`-jet of `T` at `x`. -/
theorem connDiff_g0_fibre_abs_bound
    (g₁ g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (a b c : TangentSpace I x) :
    |2 * g₀.inner x
        (connDiff (I := I) g₁ g₀ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c|
      ≤ |covDerivRealizeEval (I := I) g₀ T x a b c|
        + |covDerivRealizeEval (I := I) g₀ T x b a c|
        + |covDerivRealizeEval (I := I) g₀ T x c a b|
        + 2 * |ccTensorBilinSymm (I := I) g₀ T x
            (connDiff (I := I) g₁ g₀ x
              (smoothExtensionTangent (I := I) x b x)
              (smoothExtensionTangent (I := I) x a x)) c| := by
  rw [connDiff_koszul_realize_g0 (I := I) g₁ g₀ T hr x a b c]
  set A := covDerivRealizeEval (I := I) g₀ T x a b c with hA
  set B := covDerivRealizeEval (I := I) g₀ T x b a c with hB
  set C := covDerivRealizeEval (I := I) g₀ T x c a b with hC
  set D := ccTensorBilinSymm (I := I) g₀ T x
    (connDiff (I := I) g₁ g₀ x
      (smoothExtensionTangent (I := I) x b x)
      (smoothExtensionTangent (I := I) x a x)) c with hDdef
  have hAB : |A + B| ≤ |A| + |B| := abs_add_le A B
  have hABC : |A + B - C| ≤ |A + B| + |C| := abs_sub _ _
  have hfull : |A + B - C - 2 * D| ≤ |A + B - C| + |2 * D| := abs_sub _ _
  have h2D : |2 * D| = 2 * |D| := by rw [abs_mul]; norm_num
  linarith [hAB, hABC, hfull, h2D]

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
