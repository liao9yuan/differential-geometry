import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.TensorExtension

/-!
# The abstract Ricci tensor of the Levi-Civita covariant derivative

For a smooth Riemannian metric `g` on a smooth manifold `M`, the Levi-Civita covariant
derivative `LeviCivita g` produces a Riemann curvature operator
`riemannOp (LeviCivita g) x : T_x M →L T_x M →L T_x M →L T_x M` at each point. The
**Ricci tensor** at `x` is the trace of the operator `Z ↦ R(Z, v) w` on the fibre
`T_x M`:
$$
  \mathrm{Ric}^{\nabla}(v, w) := \mathrm{tr}_{\mathbb{R}}\bigl(Z \mapsto R^{\nabla}(Z, v) w\bigr).
$$

## Main definitions

* `ricciEndo g x v w : T_x M →ₗ T_x M` — the endomorphism `Z ↦ R(Z, v) w`.
* `ricciTensor g x : T_x M →L T_x M →L ℝ` — the abstract pointwise Ricci tensor.

## Main theorems

* `ricciTensor_apply` — the defining trace identity at each point.
* `ricciTensor_apply_basisSum` — the basis expansion of `ricciTensor` as a sum over the
  canonical model basis `chartModelBasis E`:
  `ricciTensor g x v w = ∑ i, (chartModelBasis E).repr (R(b i, v) w) i`.
* `ricciTensor_apply_smooth` — the application formula on smooth tangent vector fields:
  `ricciTensor g x (Y x) (Z x) = tr (W ↦ riemannOp (LeviCivita g) x W (Y x) (Z x))`.
* `ricciTensor_apply_smooth_basisSum` — combined with `riemannOp_apply_smooth`, the
  basis-sum entries rewrite to scalar pairings of the section-level Riemann formula
  `riemannSec (LeviCivita g) B_i Y Z`.

## Sign convention

With Mathlib's covariant-derivative convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, the
section-level Riemann formula `riemannSec cov X Y Z` realises the standard `R(X, Y) Z`
operator: `R(X, Y) Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_{[X, Y]} Z`. The Ricci contraction
adopts the geometer's convention `Ric(v, w) = tr_Z R(Z, v) w`, matching the
chart-coordinate Ricci tensor `chartRicciTensor g α i k = ∑ j R^j_{ijk}` defined in
`Integral/DivergenceTheorem/RicciCurvature.lean`.

## Symmetry and smoothness

* `riemannSec_metric_skew` — section-level metric skewness for the Levi-Civita Riemann
  curvature on smooth tangent vector fields:
  `g(R(X, Y) Z, W) + g(Z, R(X, Y) W) = 0`.
  The proof iterates metric compatibility (`LeviCivita_isMetricCompatible`) for the
  scalar `b ↦ g(Z, W)` and uses the foundation identity
  `extDerivFun f x [X, Y]_x = X(Y f)(x) - Y(X f)(x)` for the curvature commutator on
  scalars.

* `riemannOp_metric_skew` — fibre-level form of the same identity for the bundled
  curvature operator `riemannOp (LeviCivita g) x`.

* `trace_eq_zero_of_skew_dual` — algebraic skew-trace lemma: an endomorphism that is
  skew-adjoint with respect to a non-degenerate symmetric bilinear pairing on a
  finite-dimensional real vector space has zero trace. The proof uses
  `Module.Dual.transpose` plus `LinearMap.trace_comp_comm'` and
  `LinearMap.trace_transpose'`.

* `ricciTensor_symm` — symmetry of the Ricci tensor: `Ric(v, w) = Ric(w, v)`. The
  argument combines `riemannOp_metric_skew` (giving zero trace of the curvature
  endomorphism `Z ↦ R(v, w) Z`) with the first Bianchi identity rearranged at the
  fibre level: `R(Z, v) w - R(Z, w) v = -R(v, w) Z`.

* `ricciTensor_contMDiff` — smoothness of `b ↦ ⟨b, ricciTensor g b⟩` as a section of
  the (0, 2)-tensor bundle. The proof uses the operator-to-bundle bridge
  `cotangentCov_clmSection_smooth_aux` twice to reduce to: for every pair of smooth
  tangent vector fields `Y, W`, the scalar `b ↦ ricciTensor g b (Y b) (W b)` is smooth.
  That scalar smoothness is established locally via the chart-frame trace expansion
  combined with smoothness of the section-level Riemann formula
  (`riemannSec_section_smooth`).
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure

/-! ## The pointwise endomorphism `Z ↦ R(Z, v) w` -/

/-- The pointwise Riemann endomorphism of `T_x M` for fixed `(v, w)`:
`Z ↦ riemannOp (LeviCivita g) x Z v w`. As a `LinearMap`, this packages the trilinear
`riemannOp` into a single-argument endomorphism; the trace of this endomorphism is the
Ricci tensor at `(v, w)`. -/
def ricciEndo (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun Z := riemannOp (LeviCivita (I := I) g) x Z v w
  map_add' Z Z' := by
    -- riemannOp x is additive in its first slot.
    have h := (riemannOp (LeviCivita (I := I) g) x).map_add Z Z'
    have happ := congrArg
      (fun (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) =>
        φ v w) h
    set_option linter.unnecessarySimpa false in
    simpa [ContinuousLinearMap.add_apply] using happ
  map_smul' c Z := by
    -- riemannOp x is ℝ-linear in its first slot.
    have h := (riemannOp (LeviCivita (I := I) g) x).map_smul c Z
    have happ := congrArg
      (fun (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) =>
        φ v w) h
    set_option linter.unnecessarySimpa false in
    simpa [ContinuousLinearMap.smul_apply] using happ

@[simp] lemma ricciEndo_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w Z : TangentSpace I x) :
    ricciEndo (I := I) g x v w Z = riemannOp (LeviCivita (I := I) g) x Z v w := rfl

/-! ## The Ricci tensor as a continuous bilinear form

We package `Ric(v, w) := tr_Z R(Z, v) w` as a `LinearMap.mk₂` bilinear form on
`T_x M × T_x M → ℝ`, then upgrade to a continuous bilinear form via
`LinearMap.toContinuousLinearMap₂` (using `T2Space E` and `FiniteDimensional ℝ E`,
both transferred to `T_x M` via the definitional equality `TangentSpace I x = E`). -/

/-- The pointwise Ricci tensor as a bilinear form `T_x M →ₗ T_x M →ₗ ℝ`. Linearity in
each slot follows from the linearity of `riemannOp` in its corresponding slot together
with `LinearMap.trace`'s linearity in its endomorphism input. -/
def ricciTensorBilin (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun v w => LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w))
    (fun v v' w => by
      classical
      have hadd : ricciEndo (I := I) g x (v + v') w =
          ricciEndo (I := I) g x v w + ricciEndo (I := I) g x v' w := by
        apply LinearMap.ext
        intro Z
        change riemannOp (LeviCivita (I := I) g) x Z (v + v') w =
          riemannOp (LeviCivita (I := I) g) x Z v w +
            riemannOp (LeviCivita (I := I) g) x Z v' w
        rw [(riemannOp (LeviCivita (I := I) g) x Z).map_add v v']
        rfl
      change LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x (v + v') w) =
        LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w) +
          LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v' w)
      rw [hadd, map_add])
    (fun c v w => by
      classical
      have hsmul : ricciEndo (I := I) g x (c • v) w = c • ricciEndo (I := I) g x v w := by
        apply LinearMap.ext
        intro Z
        change riemannOp (LeviCivita (I := I) g) x Z (c • v) w =
          c • riemannOp (LeviCivita (I := I) g) x Z v w
        rw [(riemannOp (LeviCivita (I := I) g) x Z).map_smul c v]
        rfl
      change LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x (c • v) w) =
        c • LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w)
      rw [hsmul, map_smul, smul_eq_mul])
    (fun v w w' => by
      classical
      have hadd : ricciEndo (I := I) g x v (w + w') =
          ricciEndo (I := I) g x v w + ricciEndo (I := I) g x v w' := by
        apply LinearMap.ext
        intro Z
        change riemannOp (LeviCivita (I := I) g) x Z v (w + w') =
          riemannOp (LeviCivita (I := I) g) x Z v w +
            riemannOp (LeviCivita (I := I) g) x Z v w'
        exact ((riemannOp (LeviCivita (I := I) g) x Z v).map_add w w')
      change LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v (w + w')) =
        LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w) +
          LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w')
      rw [hadd, map_add])
    (fun c v w => by
      classical
      have hsmul : ricciEndo (I := I) g x v (c • w) = c • ricciEndo (I := I) g x v w := by
        apply LinearMap.ext
        intro Z
        change riemannOp (LeviCivita (I := I) g) x Z v (c • w) =
          c • riemannOp (LeviCivita (I := I) g) x Z v w
        exact ((riemannOp (LeviCivita (I := I) g) x Z v).map_smul c w)
      change LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v (c • w)) =
        c • LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w)
      rw [hsmul, map_smul, smul_eq_mul])

@[simp] lemma ricciTensorBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensorBilin (I := I) g x v w =
      LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w) :=
  rfl

/-! ## The bundled Ricci tensor

Using `LinearMap.toContinuousLinearMap` twice (the finite-dimensional automatic-continuity
construction), we obtain the continuous bilinear form `ricciTensor g x` from
`ricciTensorBilin g x`: first promote each `ricciTensorBilin g x v : T_x M →ₗ ℝ` to a
continuous functional, then promote the linear map `v ↦ (above)` to a continuous map. -/

/-- Auxiliary linear map: `v ↦ (ricciTensorBilin g x v).toContinuousLinearMap`, viewed
as a `LinearMap` from `T_x M` to the continuous-functional space `T_x M →L ℝ`. -/
private def ricciTensorAuxClm (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  { toFun := fun v => LinearMap.toContinuousLinearMap (ricciTensorBilin (I := I) g x v)
    map_add' := fun v v' => by
      ext w
      have := (ricciTensorBilin (I := I) g x).map_add v v'
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      set_option linter.unnecessarySimpa false in
      simpa [LinearMap.add_apply, ContinuousLinearMap.add_apply,
             LinearMap.coe_toContinuousLinearMap'] using happ
    map_smul' := fun c v => by
      ext w
      have := (ricciTensorBilin (I := I) g x).map_smul c v
      have happ := congrArg
        (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      set_option linter.unnecessarySimpa false in
      simpa [LinearMap.smul_apply, ContinuousLinearMap.smul_apply,
             LinearMap.coe_toContinuousLinearMap', smul_eq_mul] using happ }

@[simp] private lemma ricciTensorAuxClm_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensorAuxClm (I := I) g x v w = ricciTensorBilin (I := I) g x v w := rfl

/-- The **abstract Ricci tensor** of the Levi-Civita covariant derivative on a smooth
Riemannian manifold, as a continuous bilinear form `T_x M →L T_x M →L ℝ` at each
point `x`. By definition, `ricciTensor g x v w` is the trace of the linear map
`Z ↦ riemannOp (LeviCivita g) x Z v w` on `T_x M`. -/
noncomputable def ricciTensor (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (ricciTensorAuxClm (I := I) g x)

/-- The defining identity: `ricciTensor g x v w = tr_Z (Z ↦ riemannOp (LeviCivita g) x Z v w)`.
-/
theorem ricciTensor_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w) := by
  change ricciTensorAuxClm (I := I) g x v w = _
  rw [ricciTensorAuxClm_apply, ricciTensorBilin_apply]

/-! ## Basis expansion of the trace

By `LinearMap.trace_eq_matrix_trace` applied to the canonical model basis
`chartModelBasis E` (which is also a basis of `T_x M = E`), the trace of
`ricciEndo g x v w` is the diagonal sum of its matrix coordinates. -/

/-- **Basis expansion of `ricciTensor`.** For the canonical model basis
`b := chartModelBasis E`, the Ricci tensor at `x` admits the coordinate sum
`ricciTensor g x v w = ∑ i, b.repr (riemannOp (LeviCivita g) x (b i) v w) i`. -/
theorem ricciTensor_apply_basisSum (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (riemannOp (LeviCivita (I := I) g) x ((chartModelBasis E) i) v w) i := by
  classical
  rw [ricciTensor_apply]
  -- Use `LinearMap.trace_eq_matrix_trace` with the chart-model basis (which is
  -- also a basis of `T_x M = E`).
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [LinearMap.trace_eq_matrix_trace ℝ
        (chartModelBasis (TangentSpace I x)) (ricciEndo (I := I) g x v w)]
  unfold Matrix.trace
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  rfl

/-! ## Application formula on smooth sections

`ricciTensor g x (Y x) (Z x)`, evaluated on the values of smooth tangent vector fields
`Y, Z` at `x`, equals the trace of the endomorphism `W ↦ riemannOp (LeviCivita g) x W (Y x) (Z x)`,
which by `riemannOp_apply_smooth` rewrites to the section-level Riemann formula on smooth
tangent vector-field extensions of the basis vectors. -/

/-- **Application formula on smooth sections (definitional form).** For smooth tangent
vector fields `Y, Z` and a point `x`, the Ricci tensor evaluated at `(Y x, Z x)` equals
the trace of the endomorphism `W ↦ riemannOp (LeviCivita g) x W (Y x) (Z x)`. -/
theorem ricciTensor_apply_smooth (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b}
    (_hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (_hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (x : M) :
    ricciTensor (I := I) g x (Y x) (Z x) =
      LinearMap.trace ℝ (TangentSpace I x)
        (ricciEndo (I := I) g x (Y x) (Z x)) :=
  ricciTensor_apply (I := I) g x (Y x) (Z x)

/-- **Section-level basis-sum application formula.** Combining
`ricciTensor_apply_basisSum` with `riemannOp_apply_smooth`, the Ricci tensor evaluated on
the values `(Y x, Z x)` of smooth tangent vector fields admits the expansion
`ricciTensor g x (Y x) (Z x) = ∑ i, b.repr (riemannSec (LeviCivita g) B_i Y Z x) i` for
any choice of smooth tangent vector fields `B_i` with `B_i x = (chartModelBasis E) i`.

This is the form used downstream by the L3.3 Ricci identity and the L4.4 Ricci bridge:
plugging the canonical model basis `b_i = (chartModelBasis E) i` together with smooth
local-frame extensions `B_i` agreeing with the canonical basis at `x`, the abstract Ricci
contraction reduces to a finite sum of section-level Riemann curvature scalars, each
expressible from `LeviCivita g` data alone. -/
theorem ricciTensor_apply_smooth_basisSum (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M) (hBx : ∀ i, B i x = (chartModelBasis E) i) :
    ricciTensor (I := I) g x (Y x) (Z x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (riemannSec (LeviCivita (I := I) g) (B i) Y Z x) i := by
  classical
  rw [ricciTensor_apply_basisSum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show ((chartModelBasis E) i : TangentSpace I x) = B i x from (hBx i).symm,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hB i) hY hZ]

/-! ## Algebraic skew-trace lemma

For a finite-dimensional real vector space `V` equipped with a non-degenerate symmetric
bilinear form `B : V → V → ℝ` (encoded as a linear injection `♭ : V → V*` whose
underlying pairing `(♭ a) b` is symmetric), an endomorphism `F : V → V` is
`B`-skew-adjoint if `B(F v, w) = -B(v, F w)` for all `v, w`. The trace of any
`B`-skew-adjoint endomorphism on a real finite-dimensional vector space is zero.

The argument is purely algebraic: skew-adjointness rewrites as
`♭ ∘ F = - F^t ∘ ♭` where `F^t = LinearMap.dualMap F`. Composing with the inverse `♯`
of `♭` yields `F = -♯ ∘ F^t ∘ ♭`. Cyclic invariance of the trace
(`LinearMap.trace_comp_comm'`) plus `LinearMap.trace_transpose'` then gives
`tr F = -tr F`, hence `tr F = 0`. -/

/-- **Skew-adjoint trace lemma.** Let `V` be a finite-dimensional real vector space,
let `flat : V →ₗ[ℝ] (V →ₗ[ℝ] ℝ)` be a linear injection (equivalently, a non-degenerate
bilinear pairing), with the underlying pairing symmetric in the sense
`(flat a) b = (flat b) a`. If `F : V →ₗ[ℝ] V` satisfies the skew identity
`(flat (F v)) w = -(flat v) (F w)` for all `v, w`, then `LinearMap.trace ℝ V F = 0`. -/
lemma trace_eq_zero_of_skew_dual
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (flat : V →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
    (hflat_inj : Function.Injective flat)
    {F : V →ₗ[ℝ] V}
    (hskew : ∀ v w : V, (flat (F v)) w = - (flat v) (F w)) :
    LinearMap.trace ℝ V F = 0 := by
  classical
  -- `flat` is bijective in finite dimensions: injective ⇒ surjective.
  have hdimEq : Module.finrank ℝ V = Module.finrank ℝ (V →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm
  have hflat_surj : Function.Surjective flat :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimEq).mp hflat_inj
  have hflat_bij : Function.Bijective flat := ⟨hflat_inj, hflat_surj⟩
  set flatE : V ≃ₗ[ℝ] (V →ₗ[ℝ] ℝ) := LinearEquiv.ofBijective flat hflat_bij with hflatE_def
  set sharp : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] V := flatE.symm.toLinearMap with hsharp_def
  have hsharp_flat : sharp ∘ₗ flat = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change flatE.symm (flatE v) = v
    exact flatE.left_inv v
  have hflat_sharp : flat ∘ₗ sharp = LinearMap.id := by
    apply LinearMap.ext
    intro θ
    change flatE (flatE.symm θ) = θ
    exact flatE.right_inv θ
  -- Skew-adjointness encoded as `flat ∘ₗ F = - F.dualMap ∘ₗ flat`.
  have hskew_op : flat ∘ₗ F = -(F.dualMap ∘ₗ flat) := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change (flat (F v)) w = -(F.dualMap (flat v)) w
    rw [hskew v w, LinearMap.dualMap_apply]
  -- Hence `F = -sharp ∘ₗ F.dualMap ∘ₗ flat`.
  have hF_decomp : F = -(sharp ∘ₗ F.dualMap ∘ₗ flat) := by
    apply LinearMap.ext
    intro v
    -- LHS: F v.
    -- Note: sharp ∘ₗ flat = id, so F v = sharp (flat (F v)).
    have hvalue : F v = sharp (flat (F v)) := by
      have h := congrArg (fun (φ : V →ₗ[ℝ] V) => φ (F v)) hsharp_flat
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at h
      exact h.symm
    -- Use the skew operator identity to rewrite flat (F v) = -(F.dualMap (flat v)).
    have hskew_val : flat (F v) = -F.dualMap (flat v) := by
      have h := congrArg (fun (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) => φ v) hskew_op
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply] at h
      exact h
    rw [hvalue, hskew_val, map_neg]
    rfl
  -- Compute trace using linearity (`map_neg`).
  have htr_eq : LinearMap.trace ℝ V F =
      -LinearMap.trace ℝ V (sharp ∘ₗ F.dualMap ∘ₗ flat) := by
    have := congrArg (LinearMap.trace ℝ V) hF_decomp
    rw [map_neg] at this
    exact this
  -- `tr (sharp ∘ F.dualMap ∘ flat) = tr ((F.dualMap ∘ flat) ∘ sharp) = tr (F.dualMap)`.
  have htr_cyc : LinearMap.trace ℝ V (sharp ∘ₗ F.dualMap ∘ₗ flat) =
      LinearMap.trace ℝ (Module.Dual ℝ V) F.dualMap := by
    -- Use `trace_comp_comm'` to cycle `sharp` to the right.
    have h1 : LinearMap.trace ℝ V (sharp ∘ₗ (F.dualMap ∘ₗ flat)) =
        LinearMap.trace ℝ (Module.Dual ℝ V) ((F.dualMap ∘ₗ flat) ∘ₗ sharp) :=
      LinearMap.trace_comp_comm' (M := V) (N := Module.Dual ℝ V)
        (f := F.dualMap ∘ₗ flat) (g := sharp)
    have h2 : (F.dualMap ∘ₗ flat) ∘ₗ sharp = F.dualMap := by
      rw [LinearMap.comp_assoc, hflat_sharp, LinearMap.comp_id]
    rw [show (sharp ∘ₗ F.dualMap ∘ₗ flat) = sharp ∘ₗ (F.dualMap ∘ₗ flat) from rfl, h1, h2]
  have htr_dualMap : LinearMap.trace ℝ (Module.Dual ℝ V) F.dualMap =
      LinearMap.trace ℝ V F := by
    rw [LinearMap.dualMap_def]
    exact LinearMap.trace_transpose' F
  -- Combine: tr F = -tr F.
  have hself_neg : LinearMap.trace ℝ V F = -LinearMap.trace ℝ V F := by
    calc LinearMap.trace ℝ V F
        = -LinearMap.trace ℝ V (sharp ∘ₗ F.dualMap ∘ₗ flat) := htr_eq
      _ = -LinearMap.trace ℝ (Module.Dual ℝ V) F.dualMap := by rw [htr_cyc]
      _ = -LinearMap.trace ℝ V F := by rw [htr_dualMap]
  linarith

/-! ## Section-level metric skewness of Riemann curvature

For a smooth Riemannian metric `g` on `M` and the Levi-Civita covariant derivative
`cov := LeviCivita g`, the section-level Riemann curvature operator is metric-skew:
$$
  g(R(X, Y) Z, W) + g(Z, R(X, Y) W) = 0,
$$
for smooth tangent vector fields `X, Y, Z, W` and at every `x ∈ M`. The argument
combines metric compatibility (applied iteratively to the iterated covariant
derivatives that appear in the Riemann formula) with the foundation identity
`extDerivFun f x [X, Y]_x = X(Y f)(x) - Y(X f)(x)` for the manifold Lie bracket
acting on a smooth scalar function. -/

section MetricSkewSection

variable [CompleteSpace E]

/-- Compose `covApply` of `cov` with `Z`: the smooth tangent section `b ↦ cov_Y Z (b)`,
which is `MDiff` at every point given that the prerequisite smoothness holds. We use
this to organise the iterated derivatives in the metric-skew calculation. -/
private lemma covApply_smooth_section
    {Y : Π b : M, TangentSpace I b} {Z : Π b : M, TangentSpace I b}
    (g : SmoothRiemannianMetric I M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g) Y Z)) := by
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  intro x
  exact (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hZ_le).contMDiffAt
    (Filter.univ_mem)

/-- The scalar `b ↦ g.inner b (Y b) (Z b)` is smooth for smooth `Y, Z` tangent sections. -/
private lemma inner_smooth_scalar
    (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => g.inner b (Y b) (Z b)) := by
  -- Use the (0,2)-tensor pairing smoothness: g is smooth as a (0,2)-tensor section,
  -- and the bilinear pairing of a smooth (0,2)-tensor on smooth tangent sections is smooth.
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (g.inner b)) := g.contMDiff
  -- `cotangentCov_pairing_contMDiff` chains: g (Y) is a smooth cotangent section,
  -- then (g (Y))(Z) is a smooth scalar.
  -- First apply `cotangentCov_pairing_contMDiff` with target = T*M. We need θ = g(·,·).
  -- Use the standalone fact `tensor02Cov_pairing_contMDiff` — but it is private. We
  -- replicate using `clm_bundle_apply` directly.
  have hgY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (g.inner b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => g.inner b) (v := fun b => Y b) hg hY
  exact cotangentCov_pairing_contMDiff hgY hZ

/-- A version of `inner_smooth_scalar` packaged for `MDiffAt` at a single point. -/
private lemma inner_mdiffAt_scalar
    (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b => g.inner b (Y b) (Z b)) x :=
  ((inner_smooth_scalar g hY hZ) x).mdifferentiableAt (by simp)

/-- Helper: at a point `x`, the directional derivative `extDerivFun (b ↦ g(Z, W)) x (Y x)`
equals `g(cov_Y Z, W) + g(Z, cov_Y W)` at `x` (metric compatibility, with `cov_Y σ x =
cov.toFun σ x (Y x) = covApply cov Y σ x`). -/
private lemma metric_compat_one
    (g : SmoothRiemannianMetric I M)
    {Y Z W : Π b : M, TangentSpace I b} {x : M}
    (_hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x) :
    extDerivFun (I := I) (fun b => g.inner b (Z b) (W b)) x (Y x) =
      g.inner x (covApply (LeviCivita (I := I) g) Y Z x) (W x) +
        g.inner x (Z x) (covApply (LeviCivita (I := I) g) Y W x) := by
  classical
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hZ hW (Y x)
  -- `hmc : (mfderiv I 𝓘(ℝ) f) x (Y x) = g.inner x (cov Z x (Y x)) (W x) + g.inner x (Z x) (cov W x (Y x))`.
  -- And `extDerivFun = mfderiv` for ℝ-valued functions (the cast is the identity).
  have hext_eq : extDerivFun (I := I) (fun b => g.inner b (Z b) (W b)) x (Y x) =
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Z b) (W b)) x) (Y x) := rfl
  rw [hext_eq, hmc]
  rfl

/-- The directional-derivative scalar `b ↦ extDerivFun (g(Z,W)) b (Y b)` is, **as a
function of `b`**, eventually equal (in fact globally equal) to
`b ↦ g(cov_Y Z, W) b + g(Z, cov_Y W) b`. This is the section-level form of
`metric_compat_one`, used to differentiate again. -/
private lemma extDerivFun_inner_eq_globally
    (g : SmoothRiemannianMetric I M)
    {Y Z W : Π b : M, TangentSpace I b}
    (hY_glob : MDiff (T% Y))
    (hZ_glob : MDiff (T% Z)) (hW_glob : MDiff (T% W)) :
    (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (Y b)) =
      (fun b : M =>
        g.inner b (covApply (LeviCivita (I := I) g) Y Z b) (W b) +
          g.inner b (Z b) (covApply (LeviCivita (I := I) g) Y W b)) := by
  funext b
  exact metric_compat_one g (hY_glob b) (hZ_glob b) (hW_glob b)

/-- Iteratively applying metric compatibility, the second derivative
`extDerivFun (extDerivFun (g(Z,W)) · (Y ·)) x (X x)` decomposes into four terms. -/
private lemma metric_compat_two
    (g : SmoothRiemannianMetric I M)
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (Y b))
        x (X x) =
      g.inner x (covApply (LeviCivita (I := I) g) X
                   (covApply (LeviCivita (I := I) g) Y Z) x) (W x) +
        g.inner x (covApply (LeviCivita (I := I) g) Y Z x)
          (covApply (LeviCivita (I := I) g) X W x) +
        g.inner x (covApply (LeviCivita (I := I) g) X Z x)
          (covApply (LeviCivita (I := I) g) Y W x) +
        g.inner x (Z x)
          (covApply (LeviCivita (I := I) g) X
            (covApply (LeviCivita (I := I) g) Y W) x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  -- Globalize the section-level identity for the inner derivative.
  have hY_glob : MDiff (T% Y) := hY.mdifferentiable (by simp)
  have hZ_glob : MDiff (T% Z) := hZ.mdifferentiable (by simp)
  have hW_glob : MDiff (T% W) := hW.mdifferentiable (by simp)
  have hsec_eq := extDerivFun_inner_eq_globally g hY_glob hZ_glob hW_glob
  -- Substitute on the LHS via `extDerivFun_congr` (i.e., `mfderiv` of equal functions).
  have hLHS_rw : extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (Y b))
        x (X x) =
      extDerivFun (I := I)
        (fun b : M =>
          g.inner b (covApply cov Y Z b) (W b) +
            g.inner b (Z b) (covApply cov Y W b)) x (X x) := by
    rw [hsec_eq]
  rw [hLHS_rw]
  -- Apply `extDerivFun` linearity (it's additive in the function via `mfderiv_add`).
  have hsmooth_first : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (covApply cov Y Z b) (W b)) := by
    have hcovYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y Z)) :=
      covApply_smooth_section g hY hZ
    exact inner_smooth_scalar g hcovYZ hW
  have hsmooth_second : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (Z b) (covApply cov Y W b)) := by
    have hcovYW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y W)) :=
      covApply_smooth_section g hY hW
    exact inner_smooth_scalar g hZ hcovYW
  have hfirst_mdiff : MDiff (fun b : M => g.inner b (covApply cov Y Z b) (W b)) :=
    hsmooth_first.mdifferentiable (by simp)
  have hsecond_mdiff : MDiff (fun b : M => g.inner b (Z b) (covApply cov Y W b)) :=
    hsmooth_second.mdifferentiable (by simp)
  -- Decompose via `extDerivFun_add` (additivity of the exterior-derivative section).
  have hext_add : extDerivFun (I := I)
        (fun b : M =>
          g.inner b (covApply cov Y Z b) (W b) +
            g.inner b (Z b) (covApply cov Y W b)) x (X x) =
      extDerivFun (I := I) (fun b => g.inner b (covApply cov Y Z b) (W b)) x (X x) +
        extDerivFun (I := I) (fun b => g.inner b (Z b) (covApply cov Y W b)) x (X x) := by
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun b => g.inner b (covApply cov Y Z b) (W b)) x := hfirst_mdiff x
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun b => g.inner b (Z b) (covApply cov Y W b)) x := hsecond_mdiff x
    have hsum : extDerivFun (I := I)
        ((fun b => g.inner b (covApply cov Y Z b) (W b)) +
          (fun b => g.inner b (Z b) (covApply cov Y W b))) x =
        extDerivFun (I := I) (fun b => g.inner b (covApply cov Y Z b) (W b)) x +
          extDerivFun (I := I) (fun b => g.inner b (Z b) (covApply cov Y W b)) x :=
      extDerivFun_add h1 h2
    -- Apply both sides at `(X x)` and unfold `(f + g) b = f b + g b`.
    have happ := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ (X x)) hsum
    simp only [ContinuousLinearMap.add_apply] at happ
    convert happ using 2
  rw [hext_add]
  -- Apply metric compatibility to each piece (with `(covApply cov Y Z, W)` and `(Z, covApply cov Y W)`).
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_at : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hcovYZ_at : MDiffAt (T% (covApply cov Y Z)) x :=
    (covApply_smooth_section g hY hZ x).mdifferentiableAt (by simp)
  have hcovYW_at : MDiffAt (T% (covApply cov Y W)) x :=
    (covApply_smooth_section g hY hW x).mdifferentiableAt (by simp)
  -- First inner derivative.
  have hmc1 := metric_compat_one g hX_at hcovYZ_at hW_at
  -- Second inner derivative.
  have hmc2 := metric_compat_one g hX_at hZ_at hcovYW_at
  rw [hmc1, hmc2]
  ring

/-- The section-level metric skewness of the Levi-Civita Riemann curvature on smooth
tangent vector fields:
$$
  g\bigl(R(X, Y) Z, W\bigr)(x) + g\bigl(Z, R(X, Y) W\bigr)(x) = 0.
$$
-/
theorem riemannSec_metric_skew
    (g : SmoothRiemannianMetric I M)
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) X Y Z x) (W x) +
      g.inner x (Z x) (riemannSec (LeviCivita (I := I) g) X Y W x) = 0 := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  -- Apply `metric_compat_two` (X, Y, Z, W) and (Y, X, Z, W), and subtract.
  have hxy := metric_compat_two (x := x) g hX hY hZ hW
  have hyx := metric_compat_two (x := x) g hY hX hZ hW
  -- Foundation: extDerivFun (extDerivFun f · Y ·) x (X x) - extDerivFun (extDerivFun f · X ·) x (Y x)
  --           = extDerivFun f x [X, Y]_x.
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_at : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b => g.inner b (Z b) (W b)) := inner_smooth_scalar g hZ hW
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun b => g.inner b (Z b) (W b)) x := by
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1
    exact (hf_smooth x).of_le hle
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    (I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint
  have hfound : extDerivFun (I := I) (fun b => g.inner b (Z b) (W b)) x
      (VectorField.mlieBracket I X Y x) =
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (Y b))
        x (X x) -
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (X b))
        x (Y x) :=
    extDerivFun_apply_mlieBracket hX_at hY_at hf_2 hx_int
  -- Apply metric compatibility to `extDerivFun f x [X,Y]_x`.
  have hbr_mdiff : MDiffAt (T% (VectorField.mlieBracket I X Y)) x := by
    haveI : IsManifold I 2 M := by
      have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
      exact IsManifold.of_le h_le
    haveI : CompleteSpace E := inferInstance
    -- The internal `mlieBracket_vectorField` proof requires `IsManifold I (minSmoothness ℝ 2) M`.
    haveI : IsManifold I (minSmoothness ℝ 2 : WithTop ℕ∞) M := by
      have h_eq : (minSmoothness ℝ 2 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by
        rw [minSmoothness_of_isRCLikeNormedField]
      rw [h_eq]; infer_instance
    -- Use `ContMDiffAt.mlieBracket_vectorField` with `n := 1`, `m := 0`.
    have h_le_inf : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    have hX1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% X) x := (hX x).of_le h_le_inf
    have hY1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% Y) x := (hY x).of_le h_le_inf
    have hmin : minSmoothness ℝ ((0 : ℕ∞) + 1) ≤ (1 : ℕ∞) := by
      simp [minSmoothness_of_isRCLikeNormedField]
    haveI : IsManifold I ((1 : ℕ∞) + 1) M := by
      have h_eq : ((1 : ℕ∞) + 1 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by rfl
      rw [h_eq]; infer_instance
    -- Use n=2, m=1 so that the resulting smoothness ≥ 1 ⇒ MDifferentiableAt.
    have h_le_inf2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    have hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% X) x := (hX x).of_le h_le_inf2
    have hY2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% Y) x := (hY x).of_le h_le_inf2
    have hmin' : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ (2 : ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      decide
    haveI : IsManifold I ((2 : ℕ∞) + 1) M := by
      have h_eq : ((2 : ℕ∞) + 1 : WithTop ℕ∞) = (3 : WithTop ℕ∞) := by rfl
      rw [h_eq]
      have h_le3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
      exact IsManifold.of_le h_le3
    exact (hX2.mlieBracket_vectorField (m := 1) (n := 2) hY2 hmin').mdifferentiableAt
      (by decide)
  have hmc_br := metric_compat_one g hbr_mdiff hZ_at hW_at
  -- Compose: hxy - hyx using hfound and hmc_br.
  -- This is an equation in extDerivFun. Goal is the metric-skew identity at x.
  -- Compute LHS - RHS of the foundation in two ways (via metric_compat_two each side):
  -- LHS_two_xy - LHS_two_yx = (sums via hxy minus sums via hyx)
  --                         = g((cov_X cov_Y - cov_Y cov_X) Z, W) + g(Z, (cov_X cov_Y - cov_Y cov_X) W)
  -- And this equals extDerivFun f x [X,Y]_x = g(cov_{[X,Y]} Z, W) + g(Z, cov_{[X,Y]} W).
  -- Hence g((cov_X cov_Y - cov_Y cov_X - cov_{[X,Y]}) Z, W) + g(Z, (...) W) = 0.
  -- And the `(cov_X cov_Y - cov_Y cov_X - cov_{[X,Y]})` is `riemannSec` (with sign).
  have hsub : extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (Y b))
        x (X x) -
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (Z b') (W b')) b (X b))
        x (Y x) =
      g.inner x (covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x) (W x) +
        g.inner x (Z x) (covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x) := by
    rw [hxy, hyx]
    -- Algebraic rearrangement: the four-term sums minus four-term sums collapse.
    -- (a + b + c + d) - (a' + b + c + d') with appropriate identifications.
    -- Use `map_sub` on the linear `g.inner x (·) (W x)` and `g.inner x (Z x) (·)`.
    have h1 : g.inner x (covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x) (W x) =
        g.inner x (covApply cov X (covApply cov Y Z) x) (W x) -
          g.inner x (covApply cov Y (covApply cov X Z) x) (W x) := by
      rw [map_sub]; rfl
    have h2 : g.inner x (Z x) (covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x) =
        g.inner x (Z x) (covApply cov X (covApply cov Y W) x) -
          g.inner x (Z x) (covApply cov Y (covApply cov X W) x) := by
      rw [map_sub]
    rw [h1, h2]
    ring
  -- The Lie-bracket scalar derivative.
  have hbr_eq : extDerivFun (I := I) (fun b => g.inner b (Z b) (W b)) x
      (VectorField.mlieBracket I X Y x) =
      g.inner x (covApply cov (VectorField.mlieBracket I X Y) Z x) (W x) +
        g.inner x (Z x) (covApply cov (VectorField.mlieBracket I X Y) W x) := hmc_br
  -- Combine: hsub says LHS_diff = (RHS); hfound says extDerivFun f x [X,Y] = LHS_diff;
  -- hbr_eq says extDerivFun f x [X,Y] = (mlieBracket version of metric-compat RHS).
  -- Hence (RHS) = (mlieBracket version of metric-compat RHS).
  have hkey : g.inner x (covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x) (W x) +
      g.inner x (Z x) (covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x) =
      g.inner x (covApply cov (VectorField.mlieBracket I X Y) Z x) (W x) +
        g.inner x (Z x) (covApply cov (VectorField.mlieBracket I X Y) W x) := by
    have h := hsub.symm.trans (hfound.symm.trans hbr_eq)
    exact h
  -- Now `riemannSec cov X Y Z x = covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x
  --                                - cov.toFun Z x ([X,Y]_x)`.
  -- And `cov.toFun Z x ([X,Y]_x) = covApply cov (mlieBracket I X Y) Z x` definitionally.
  have hRZ : riemannSec cov X Y Z x =
      covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x -
        covApply cov (VectorField.mlieBracket I X Y) Z x := by
    rfl
  have hRW : riemannSec cov X Y W x =
      covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x -
        covApply cov (VectorField.mlieBracket I X Y) W x := by
    rfl
  rw [hRZ, hRW]
  -- Now goal: g(A - B - C, W) + g(Z, D - E - F) = 0 where (A, B) etc encode the iterated covs.
  -- By `map_sub` (on the linear `g.inner x · (W x)` and `g.inner x (Z x) ·`) and `hkey`, this collapses.
  have h1 : g.inner x (covApply cov X (covApply cov Y Z) x -
            covApply cov Y (covApply cov X Z) x -
            covApply cov (VectorField.mlieBracket I X Y) Z x) (W x) =
      g.inner x (covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x) (W x) -
        g.inner x (covApply cov (VectorField.mlieBracket I X Y) Z x) (W x) := by
    rw [show (covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x -
        covApply cov (VectorField.mlieBracket I X Y) Z x) =
      (covApply cov X (covApply cov Y Z) x - covApply cov Y (covApply cov X Z) x) -
        covApply cov (VectorField.mlieBracket I X Y) Z x from rfl,
      map_sub]
    rfl
  have h2 : g.inner x (Z x) (covApply cov X (covApply cov Y W) x -
            covApply cov Y (covApply cov X W) x -
            covApply cov (VectorField.mlieBracket I X Y) W x) =
      g.inner x (Z x) (covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x) -
        g.inner x (Z x) (covApply cov (VectorField.mlieBracket I X Y) W x) := by
    rw [show (covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x -
        covApply cov (VectorField.mlieBracket I X Y) W x) =
      (covApply cov X (covApply cov Y W) x - covApply cov Y (covApply cov X W) x) -
        covApply cov (VectorField.mlieBracket I X Y) W x from rfl,
      map_sub]
  rw [h1, h2]
  linarith

end MetricSkewSection

/-! ## Fiber-level (bundled) metric skewness

The section-level metric skewness lifts to the bundled `riemannOp` via
`riemannOp_apply_smooth` together with smooth global extensions of fibre vectors. -/

section MetricSkewFiber

variable [CompleteSpace E]

/-- **Metric skewness of `riemannOp`.** At each point `x ∈ M` and for any fibre vectors
`v, w, Z, W ∈ T_x M`,
$$
  g_x\bigl(R(v, w) Z, W\bigr) + g_x\bigl(Z, R(v, w) W\bigr) = 0.
$$
-/
theorem riemannOp_metric_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w Z W : TangentSpace I x) :
    g.inner x (riemannOp (LeviCivita (I := I) g) x v w Z) W +
      g.inner x Z (riemannOp (LeviCivita (I := I) g) x v w W) = 0 := by
  classical
  -- Use smooth global extensions.
  set Xext := smoothExtensionTangent (I := I) x v with hXext
  set Yext := smoothExtensionTangent (I := I) x w with hYext
  set Zext := smoothExtensionTangent (I := I) x Z with hZext
  set Wext := smoothExtensionTangent (I := I) x W with hWext
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xext) :=
    smoothExtensionTangent_contMDiff x v
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Yext) :=
    smoothExtensionTangent_contMDiff x w
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Zext) :=
    smoothExtensionTangent_contMDiff x Z
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Wext) :=
    smoothExtensionTangent_contMDiff x W
  have hXx : Xext x = v := smoothExtensionTangent_eq x v
  have hYx : Yext x = w := smoothExtensionTangent_eq x w
  have hZx : Zext x = Z := smoothExtensionTangent_eq x Z
  have hWx : Wext x = W := smoothExtensionTangent_eq x W
  -- Apply `riemannOp_apply_smooth` to identify both Riemann terms with section formulas.
  have hRZ : riemannOp (LeviCivita (I := I) g) x v w Z =
      riemannSec (LeviCivita (I := I) g) Xext Yext Zext x := by
    rw [show v = Xext x from hXx.symm, show w = Yext x from hYx.symm,
        show Z = Zext x from hZx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hX hY hZ]
  have hRW : riemannOp (LeviCivita (I := I) g) x v w W =
      riemannSec (LeviCivita (I := I) g) Xext Yext Wext x := by
    rw [show v = Xext x from hXx.symm, show w = Yext x from hYx.symm,
        show W = Wext x from hWx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hX hY hW]
  rw [hRZ, hRW]
  -- Now apply section-level metric skewness.
  rw [show Z = Zext x from hZx.symm, show W = Wext x from hWx.symm]
  exact riemannSec_metric_skew g hX hY hZ hW

end MetricSkewFiber

/-! ## Symmetry of the Ricci tensor

We now combine the first Bianchi identity, the metric-skew property of the Riemann
curvature operator, and the algebraic skew-trace lemma to deduce the symmetry of the
Ricci tensor:
$$
  \mathrm{Ric}(v, w) = \mathrm{Ric}(w, v).
$$

The argument:
1. The endomorphism `R(v, w) : T_x M → T_x M` defined by `Z ↦ riemannOp (LeviCivita g) x v w Z`
   is `g`-skew-adjoint (by `riemannOp_metric_skew`); hence its trace is zero
   (`trace_eq_zero_of_skew_dual`).
2. By first Bianchi (`riemannSec_first_bianchi_levi_civita`) applied to smooth global
   extensions and rearranged at the fibre level via `riemannOp`:
   `R(Z, v) w - R(Z, w) v = -R(v, w) Z`.
3. Tracing in `Z`: `Ric(v, w) - Ric(w, v) = -tr(R(v, w)) = 0`.
-/

section RicciSymmetry

variable [CompleteSpace E]

/-- The endomorphism `Z ↦ riemannOp (LeviCivita g) x v w Z` on `T_x M`, packaged as a
`LinearMap`. This is the curvature operator `R(v, w)` at the point `x`. -/
private def riemannOpEndo
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun Z := riemannOp (LeviCivita (I := I) g) x v w Z
  map_add' Z Z' := by
    have h := (riemannOp (LeviCivita (I := I) g) x v w).map_add Z Z'
    set_option linter.unnecessarySimpa false in
    simpa using h
  map_smul' c Z := by
    have h := (riemannOp (LeviCivita (I := I) g) x v w).map_smul c Z
    set_option linter.unnecessarySimpa false in
    simpa using h

@[simp] private lemma riemannOpEndo_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w Z : TangentSpace I x) :
    riemannOpEndo (I := I) g x v w Z = riemannOp (LeviCivita (I := I) g) x v w Z := rfl

/-- The metric `g.inner x : T_x M →L T_x M →L ℝ`, viewed as a plain linear map
`T_x M →ₗ T_x M →ₗ ℝ` (forgetting the inner-CLM continuity to match the algebraic
skew-trace lemma signature). -/
private def gFlat (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ where
  toFun v := (g.inner x v).toLinearMap
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    change g.inner x (v + v') w = g.inner x v w + g.inner x v' w
    rw [(g.inner x).map_add v v']
    rfl
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change g.inner x (c • v) w = c • g.inner x v w
    rw [(g.inner x).map_smul c v]
    rfl

@[simp] private lemma gFlat_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    (gFlat (I := I) g x v) w = g.inner x v w := rfl

/-- The metric `gFlat g x` is injective (positive-definiteness of `g`). -/
private lemma gFlat_injective (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (gFlat (I := I) g x) := by
  intro v v' hvv'
  have h := congrArg (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ (v - v')) hvv'
  -- h : g.inner x v (v - v') = g.inner x v' (v - v').
  -- Then g.inner x (v - v') (v - v') = g.inner x v (v - v') - g.inner x v' (v - v') = 0.
  have hlhs : g.inner x v (v - v') = g.inner x v' (v - v') := by
    change (gFlat (I := I) g x v) (v - v') = (gFlat (I := I) g x v') (v - v')
    exact h
  have hself_zero : g.inner x (v - v') (v - v') = 0 := by
    have h1 : g.inner x (v - v') (v - v') = g.inner x v (v - v') - g.inner x v' (v - v') := by
      rw [(g.inner x).map_sub v v']
      rfl
    rw [h1, hlhs]
    ring
  -- By positive-definiteness, this forces v - v' = 0.
  by_contra hne
  have hne' : v - v' ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.pos x (v - v') hne'
  exact (lt_irrefl _) (hself_zero ▸ hpos)

/-- The trace of `riemannOpEndo g x v w` is zero, by metric skewness and the
algebraic skew-trace lemma. -/
private lemma riemannOpEndo_trace_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) (riemannOpEndo (I := I) g x v w) = 0 := by
  classical
  -- Apply the algebraic skew-trace lemma with `flat := gFlat g x`.
  apply trace_eq_zero_of_skew_dual (gFlat (I := I) g x) (gFlat_injective g x)
  intro Z W
  -- `(gFlat g x (riemannOpEndo g x v w Z)) W = g.inner x (riemannOp x v w Z) W`.
  -- And `-(gFlat g x Z) (riemannOpEndo g x v w W) = -g.inner x Z (riemannOp x v w W)`.
  -- These sum to zero by `riemannOp_metric_skew`.
  change g.inner x (riemannOp (LeviCivita (I := I) g) x v w Z) W =
    -g.inner x Z (riemannOp (LeviCivita (I := I) g) x v w W)
  have hskew := riemannOp_metric_skew (I := I) g x v w Z W
  linarith

/-- **Bianchi-type rearrangement at the fibre level.** From the section-level first
Bianchi identity (`riemannSec_first_bianchi_levi_civita`) applied to smooth global
extensions of fibre vectors, the bundled curvature operator `riemannOp` satisfies
$$
  R(Z, v) w - R(Z, w) v = -R(v, w) Z.
$$
Equivalent (and used downstream): `riemannOp x Z v w - riemannOp x Z w v = -riemannOp x v w Z`. -/
private lemma riemannOp_first_bianchi_rearranged
    (g : SmoothRiemannianMetric I M) (x : M) (v w Z : TangentSpace I x) :
    riemannOp (LeviCivita (I := I) g) x Z v w -
      riemannOp (LeviCivita (I := I) g) x Z w v =
      -riemannOp (LeviCivita (I := I) g) x v w Z := by
  classical
  -- Smooth global extensions for v, w, Z.
  set V := smoothExtensionTangent (I := I) x v with hV_def
  set W := smoothExtensionTangent (I := I) x w with hW_def
  set Zext := smoothExtensionTangent (I := I) x Z with hZ_def
  have hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) :=
    smoothExtensionTangent_contMDiff x v
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) :=
    smoothExtensionTangent_contMDiff x w
  have hZext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Zext) :=
    smoothExtensionTangent_contMDiff x Z
  have hVx : V x = v := smoothExtensionTangent_eq x v
  have hWx : W x = w := smoothExtensionTangent_eq x w
  have hZx : Zext x = Z := smoothExtensionTangent_eq x Z
  -- Apply riemannOp_apply_smooth to each of the three Riemann terms.
  have hZ_at : MDiffAt (T% Zext) x := (hZext x).mdifferentiableAt (by simp)
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  -- Smoothness of intermediate covApply sections (needed for the Bianchi hypotheses).
  have hcZV : MDiffAt (T% (covApply (LeviCivita (I := I) g) Zext V)) x :=
    ((covApply_smooth_section g hZext hV) x).mdifferentiableAt (by simp)
  have hcVZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) V Zext)) x :=
    ((covApply_smooth_section g hV hZext) x).mdifferentiableAt (by simp)
  have hcZW : MDiffAt (T% (covApply (LeviCivita (I := I) g) Zext W)) x :=
    ((covApply_smooth_section g hZext hW) x).mdifferentiableAt (by simp)
  have hcWZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) W Zext)) x :=
    ((covApply_smooth_section g hW hZext) x).mdifferentiableAt (by simp)
  have hcVW : MDiffAt (T% (covApply (LeviCivita (I := I) g) V W)) x :=
    ((covApply_smooth_section g hV hW) x).mdifferentiableAt (by simp)
  have hcWV : MDiffAt (T% (covApply (LeviCivita (I := I) g) W V)) x :=
    ((covApply_smooth_section g hW hV) x).mdifferentiableAt (by simp)
  -- mlieBracket smoothness. We need it for the three pairs (Z,V), (V,W), (W,Z).
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : IsManifold I (minSmoothness ℝ 2 : WithTop ℕ∞) M := by
    have h_eq : (minSmoothness ℝ 2 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
    rw [h_eq]; infer_instance
  have h_le_inf : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
  haveI : IsManifold I ((1 : ℕ∞) + 1) M := by
    have h_eq : ((1 : ℕ∞) + 1 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := rfl
    rw [h_eq]; infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M := by
    have h_eq : ((2 : ℕ∞) + 1 : WithTop ℕ∞) = (3 : WithTop ℕ∞) := by rfl
    rw [h_eq]
    have h_le3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le3
  have h_le_inf2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
  have hmlieBr : ∀ {U V' : Π b : M, TangentSpace I b},
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V') →
      MDiffAt (T% (VectorField.mlieBracket I U V')) x := by
    intro U V' hU hV'
    have hU2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% U) x := (hU x).of_le h_le_inf2
    have hV2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% V') x := (hV' x).of_le h_le_inf2
    have hmin : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ (2 : ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact (hU2.mlieBracket_vectorField (m := 1) (n := 2) hV2 hmin).mdifferentiableAt
      (by decide)
  have hbrZV : MDiffAt (T% (VectorField.mlieBracket I Zext V)) x := hmlieBr hZext hV
  have hbrVW : MDiffAt (T% (VectorField.mlieBracket I V W)) x := hmlieBr hV hW
  have hbrWZ : MDiffAt (T% (VectorField.mlieBracket I W Zext)) x := hmlieBr hW hZext
  -- Smoothness of `Z, V, W` in nbhds of x (for first Bianchi hypotheses).
  have hZ_nhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Zext) b :=
    Filter.Eventually.of_forall (hZext.mdifferentiable (by simp))
  have hV_nhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% V) b :=
    Filter.Eventually.of_forall (hV.mdifferentiable (by simp))
  have hW_nhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% W) b :=
    Filter.Eventually.of_forall (hW.mdifferentiable (by simp))
  -- Higher smoothness for Jacobi.
  have h_min2_le : (minSmoothness ℝ 2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hZ_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Zext) x :=
    (hZext x).of_le h_min2_le
  have hV_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% V) x :=
    (hV x).of_le h_min2_le
  have hW_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% W) x :=
    (hW x).of_le h_min2_le
  -- Apply first Bianchi to (Z, V, W).
  have hbianchi := riemannSec_first_bianchi_levi_civita (I := I) g
    (X := Zext) (Y := V) (Z := W) (x := x)
    hZ_at hV_at hW_at hZ_nhd hV_nhd hW_nhd
    hcZV hcVZ hcZW hcWZ hcVW hcWV hbrZV hbrVW hbrWZ hZ_2 hV_2 hW_2
  -- Convert riemannSec to riemannOp at the basepoint.
  have hRZV : riemannSec (LeviCivita (I := I) g) Zext V W x =
      riemannOp (LeviCivita (I := I) g) x Z v w := by
    rw [show Z = Zext x from hZx.symm, show v = V x from hVx.symm, show w = W x from hWx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hZext hV hW]
  have hRVW : riemannSec (LeviCivita (I := I) g) V W Zext x =
      riemannOp (LeviCivita (I := I) g) x v w Z := by
    rw [show v = V x from hVx.symm, show w = W x from hWx.symm, show Z = Zext x from hZx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hV hW hZext]
  have hRWZ : riemannSec (LeviCivita (I := I) g) W Zext V x =
      riemannOp (LeviCivita (I := I) g) x w Z v := by
    rw [show w = W x from hWx.symm, show Z = Zext x from hZx.symm, show v = V x from hVx.symm,
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hW hZext hV]
  rw [hRZV, hRVW, hRWZ] at hbianchi
  -- hbianchi: R(Z, v, w) + R(v, w, Z) + R(w, Z, v) = 0.
  -- Apply riemannOp_swap to move R(w, Z, v) = -R(Z, w, v).
  have hswap := riemannOp_swap (LeviCivita (I := I) g) x w Z v
  -- hswap: riemannOp x w Z v = -riemannOp x Z w v.
  rw [hswap] at hbianchi
  -- hbianchi: R(Z,v,w) + R(v,w,Z) + -R(Z,w,v) = 0.
  -- Goal: R(Z,v,w) - R(Z,w,v) = -R(v,w,Z) (in the additive group T_x M).
  -- Use `abel` (additive abelian group cancellation).
  set A := riemannOp (LeviCivita (I := I) g) x Z v w with hA
  set B := riemannOp (LeviCivita (I := I) g) x v w Z with hB
  set C := riemannOp (LeviCivita (I := I) g) x Z w v with hC
  -- hbianchi: A + B + (-C) = 0, i.e., A - C = -B.
  change A - C = -B
  -- Direct algebraic manipulation in the additive group.
  have hreorg : A + B + -C = (A - C) + B := by abel
  rw [hreorg] at hbianchi
  -- hbianchi: (A - C) + B = 0. Solve for A - C.
  have hfinal : A - C = -B := by
    have h := add_eq_zero_iff_eq_neg.mp hbianchi
    exact h
  exact hfinal

/-- **Symmetry of the Ricci tensor.** For a smooth Riemannian metric `g` on `M`, the
Ricci tensor is symmetric:
$$
  \mathrm{Ric}(v, w) = \mathrm{Ric}(w, v).
$$ -/
theorem ricciTensor_symm
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w = ricciTensor (I := I) g x w v := by
  classical
  -- Express both via `ricciTensor_apply` (trace formula).
  rw [ricciTensor_apply, ricciTensor_apply]
  -- ricciEndo g x v w = (Z ↦ riemannOp x Z v w).
  -- Difference: ricciEndo g x v w - ricciEndo g x w v = (Z ↦ R(Z, v) w - R(Z, w) v) = (Z ↦ -R(v,w) Z)
  --                                                  = -riemannOpEndo g x v w.
  -- Hence tr(ricciEndo g x v w) - tr(ricciEndo g x w v) = -tr(riemannOpEndo g x v w) = 0.
  have hdiff_eq : ricciEndo (I := I) g x v w - ricciEndo (I := I) g x w v =
      -riemannOpEndo (I := I) g x v w := by
    apply LinearMap.ext
    intro Z
    show (ricciEndo (I := I) g x v w - ricciEndo (I := I) g x w v) Z =
      (-riemannOpEndo (I := I) g x v w) Z
    simp only [LinearMap.sub_apply, ricciEndo_apply, LinearMap.neg_apply, riemannOpEndo_apply]
    -- (Z↦R(Z, v) w) Z - (Z↦R(Z, w) v) Z = R(Z,v)w - R(Z,w)v = -R(v,w)Z
    -- by `riemannOp_first_bianchi_rearranged`.
    exact riemannOp_first_bianchi_rearranged g x v w Z
  have htr_diff : LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w) -
      LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x w v) =
      LinearMap.trace ℝ (TangentSpace I x) (-riemannOpEndo (I := I) g x v w) := by
    rw [← map_sub, hdiff_eq]
  rw [show LinearMap.trace ℝ (TangentSpace I x) (-riemannOpEndo (I := I) g x v w) =
      -LinearMap.trace ℝ (TangentSpace I x) (riemannOpEndo (I := I) g x v w) from map_neg _ _,
      riemannOpEndo_trace_eq_zero g x v w] at htr_diff
  linarith

end RicciSymmetry

/-! ## Smoothness of `ricciTensor` as a `(0, 2)`-tensor section

We prove that `b ↦ ricciTensor g b` is a smooth section of the (0, 2)-tensor bundle. The
strategy mirrors the smoothness chain used for `tensor02Cov_isContMDiff`:

1. Smoothness of `b ↦ riemannSec (LeviCivita g) X Y Z b` as a smooth tangent section, given
   smooth global tangent sections `X, Y, Z`. This combines the smoothness of `covApply`
   (which is the smoothness of a `Hom(TM, TM)`-section applied to a smooth tangent section)
   and the smoothness of the manifold Lie bracket.

2. **Local trace formula.** At each point `x ∈ M`, with the trivialisation
   `e := trivializationAt E (TangentSpace I) x`, choose smooth global tangent sections `S_i`
   that agree with the local frame `e.localFrame (chartModelBasis E)` on a neighbourhood
   of `x`. The trace of `Z ↦ riemannOp (LeviCivita g) b Z (Y b) (W b)` decomposes (via
   `LinearMap.trace_eq_matrix_trace` applied to the basis `chartBasisFamily x hb`) as a
   finite sum of pairings of `riemannSec (LeviCivita g) S_i Y W b` against the dual basis,
   itself given by the trivialisation's `continuousLinearMapAt`.

3. The scalar `b ↦ ricciTensor g b (Y b) (W b)` is smooth on a neighbourhood of any point,
   hence smooth globally.

4. By the operator-to-bundle bridge (`cotangentCov_clmSection_smooth_aux`) applied twice,
   smoothness of the scalar pairings on smooth tangent sections lifts to smoothness of
   `b ↦ ⟨b, ricciTensor g b⟩` as a section of the (0, 2)-tensor bundle. -/

section RicciSmoothness

variable [CompleteSpace E]

/-- For smooth global tangent sections `X, Y, Z`, the section
`b ↦ ⟨b, riemannSec (LeviCivita g) X Y Z b⟩` of the tangent bundle is smooth. -/
private theorem riemannSec_section_smooth
    (g : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g) X Y Z b)) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  -- riemannSec cov X Y Z b = covApply cov X (covApply cov Y Z) b -
  --                          covApply cov Y (covApply cov X Z) b -
  --                          covApply cov (mlieBracket I X Y) Z b
  -- Each summand is smooth as a tangent section.
  -- (1) covApply cov Y Z is smooth.
  have hcYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y Z)) :=
    covApply_smooth_section g hY hZ
  -- (2) covApply cov X Z is smooth.
  have hcXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Z)) :=
    covApply_smooth_section g hX hZ
  -- (3) covApply cov X (covApply cov Y Z) is smooth.
  have hcXcYZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply cov X (covApply cov Y Z))) :=
    covApply_smooth_section g hX hcYZ
  -- (4) covApply cov Y (covApply cov X Z) is smooth.
  have hcYcXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply cov Y (covApply cov X Z))) :=
    covApply_smooth_section g hY hcXZ
  -- (5) mlieBracket I X Y is smooth (using `ContMDiff.mlieBracket_vectorField`).
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    have h_eq : (minSmoothness ℝ 2 : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
    rw [h_eq]; infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M := by
    have h_eq : ((2 : ℕ∞) + 1 : WithTop ℕ∞) = (3 : WithTop ℕ∞) := rfl
    rw [h_eq]
    have h_le3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le3
  have hbrXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I X Y)) := by
    -- ContMDiff.mlieBracket_vectorField requires `n + 1 ≤` smoothness on inputs.
    intro b
    -- Use n=2 → result is C^1 — this is insufficient. We need C^∞.
    -- We apply `mlieBracket_vectorField` with `m, n : ℕ∞`, using `n := ⊤` and `m := ⊤`
    -- (since `(⊤ : ℕ∞) + 1 = ⊤`, so `minSmoothness ℝ (m + 1) = ⊤ ≤ n = ⊤`).
    have hn_le : minSmoothness ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      have h_eq : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) = (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
        rw [ENat.coe_top_add_one]
      rw [h_eq]
    have hX_inf : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (T% X) b := by
      exact hX b
    have hY_inf : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (T% Y) b := by
      exact hY b
    haveI : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
      have h_eq : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) = (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
        rw [ENat.coe_top_add_one]
      rw [h_eq]; infer_instance
    exact hX_inf.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY_inf hn_le
  -- (6) covApply cov (mlieBracket I X Y) Z is smooth.
  have hcbrZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply cov (VectorField.mlieBracket I X Y) Z)) :=
    covApply_smooth_section g hbrXY hZ
  -- Combine: riemannSec is the sum of three smooth tangent sections (with signs).
  have hresult : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply cov X (covApply cov Y Z) -
        covApply cov Y (covApply cov X Z) -
        covApply cov (VectorField.mlieBracket I X Y) Z)) := by
    have h12 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (covApply cov X (covApply cov Y Z) - covApply cov Y (covApply cov X Z))) :=
      hcXcYZ.sub_section hcYcXZ
    exact h12.sub_section hcbrZ
  -- riemannSec equals this difference via definitional unfolding.
  refine hresult.congr ?_
  intro b
  -- Goal: (T% (sub-section)) b = (T% (riemannSec...)) b. Reduces by `rfl`.
  rfl

/-- The local trace formula: for `b` in a trivialization base set, the trace of an
endomorphism `F : T_b M →L[ℝ] T_b M` decomposes as a sum of dual-frame pairings using
the chart-local frame `chartBasisVecFiber x i b`. -/
private lemma trace_eq_chart_sum
    (x : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet)
    (F : TangentSpace I b →L[ℝ] TangentSpace I b) :
    LinearMap.trace ℝ (TangentSpace I b) (F : TangentSpace I b →ₗ[ℝ] TangentSpace I b) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt ℝ b
            (F (chartBasisVecFiber (I := I) x i b)))) i := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he
  set basisB := chartBasisFamily (I := I) x hb with hbasisB_def
  -- Use `LinearMap.trace_eq_matrix_trace` with `basisB`.
  rw [LinearMap.trace_eq_matrix_trace ℝ basisB
      (F : TangentSpace I b →ₗ[ℝ] TangentSpace I b)]
  unfold Matrix.trace
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  -- LHS: basisB.repr (F (basisB i)) i.
  -- basisB i = chartBasisVecFiber x i b (by `chartBasisFamily_apply`).
  -- basisB.repr v = (chartModelBasis E).repr ((e.continuousLinearEquivAt ℝ b hb) v)
  --              = (chartModelBasis E).repr (e.continuousLinearMapAt ℝ b v) (on baseSet).
  rw [show basisB i = chartBasisVecFiber (I := I) x i b from
    chartBasisFamily_apply (I := I) x hb i]
  -- basisB.repr v i = (chartModelBasis E).repr ((e.continuousLinearEquivAt ℝ b hb) v) i.
  change (basisB.repr (F (chartBasisVecFiber (I := I) x i b))) i =
      ((chartModelBasis E).repr
        (e.continuousLinearMapAt ℝ b (F (chartBasisVecFiber (I := I) x i b)))) i
  -- Unfold basisB.repr.
  rw [hbasisB_def]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply]
  -- Match `e.continuousLinearMapAt ℝ b` with `e.continuousLinearEquivAt ℝ b hb` on baseSet.
  congr 2
  change (e.continuousLinearEquivAt ℝ b hb : TangentSpace I b → E)
      (F (chartBasisVecFiber (I := I) x i b)) =
      (e.continuousLinearMapAt ℝ b : TangentSpace I b → E)
        (F (chartBasisVecFiber (I := I) x i b))
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e hb]

/-! ### Smoothness of `b ↦ ricciTensor g b (Y b) (W b)` for smooth `Y, W`.

The decomposition uses a smooth local frame: at each point `x`, we have a smooth global
tangent section `S_i` agreeing with the trivialisation-induced frame on a neighbourhood
of `x`. Then for `b` in that neighbourhood,
$$
  \mathrm{Ric}\,g\,b\,(Y b)\,(W b)
    = \sum_i \bigl((\mathtt{finBasis}\,\mathbb R\,E).\mathrm{repr}\,
        (e.\mathtt{continuousLinearMapAt}\,\mathbb R\,b\,
          (\mathrm{riemannSec}\,(\mathrm{LeviCivita}\,g)\,(S_i)\,Y\,W\,b))\bigr)_i.
$$
The right-hand side is smooth in `b` (chain of smooth operations on smooth tangent
sections). -/

/-- A smooth global tangent section that agrees with the trivialisation-induced frame on a
neighbourhood of `x`. -/
private noncomputable def localFrameSmoothExtension
    (x : M) :
    Fin (Module.finrank ℝ E) → Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he_def
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) (chartModelBasis E)
  exact (hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he).choose

private lemma localFrameSmoothExtension_eqOn_nhd (x : M) :
    let e := trivializationAt E (TangentSpace I : M → Type _) x
    ∀ᶠ b in 𝓝 x, ∀ i, (localFrameSmoothExtension (I := I) x i) b =
      e.localFrame (chartModelBasis E) i b := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he_def
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) (chartModelBasis E)
  exact (hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he).choose_spec

private lemma localFrameSmoothExtension_contMDiff (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => localFrameSmoothExtension (I := I) x i b)) :=
  (localFrameSmoothExtension (I := I) x i).contMDiff

/-- The linear functional `v ↦ ((chartModelBasis E).repr v) i` packaged as a continuous
linear map `E →L[ℝ] ℝ`. -/
private noncomputable def finBasisReprAt (i : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  haveI : T2Space E := inferInstance
  haveI : FiniteDimensional ℝ E := inferInstance
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj i).comp ((chartModelBasis E).equivFun.toLinearMap)) : E →ₗ[ℝ] ℝ)

@[simp] private lemma finBasisReprAt_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    finBasisReprAt (E := E) i v = ((chartModelBasis E).repr v) i := by
  classical
  unfold finBasisReprAt
  change ((LinearMap.proj i).comp ((chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

/-- For smooth global tangent sections `Y, W`, the scalar
`b ↦ ricciTensor g b (Y b) (W b)` is smooth on `M`. -/
private theorem ricciTensor_pairing_contMDiff
    (g : SmoothRiemannianMetric I M)
    {Y W : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => ricciTensor (I := I) g b (Y b) (W b)) := by
  classical
  -- Local-to-global smoothness: smoothness is `∀ x, ContMDiffAt`.
  intro x
  -- Local trivialization at `x`.
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he_def
  have hex : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  -- Smooth global frame `S_i` matching `e.localFrame (chartModelBasis E) i` on a nbhd of x.
  set S : Fin (Module.finrank ℝ E) → Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    localFrameSmoothExtension (I := I) x with hS_def
  have hS_smooth : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => S i b)) := fun i =>
    localFrameSmoothExtension_contMDiff (I := I) x i
  have hS_eqOn_nhd : ∀ᶠ b in 𝓝 x, ∀ i,
      S i b = e.localFrame (chartModelBasis E) i b :=
    localFrameSmoothExtension_eqOn_nhd (I := I) x
  -- Smoothness of each summand.
  have hsec_smooth : ∀ i,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => riemannSec (LeviCivita (I := I) g) (S i) Y W b)) := fun i =>
    riemannSec_section_smooth g (hS_smooth i) hY hW
  -- The summand: `b ↦ ((chartModelBasis E).repr (e.continuousLinearMapAt ℝ b (Z_i b))) i`.
  have hsummand_smooth : ∀ i,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun b : M => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ b (riemannSec (LeviCivita (I := I) g) (S i) Y W b))) i) x := by
    intro i
    -- The trivialized fibre is smooth at x.
    have h_triv : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun b : M => (e ⟨b, riemannSec (LeviCivita (I := I) g) (S i) Y W b⟩).2) x := by
      have := (contMDiffAt_section (F := E) (E := TangentSpace I) x).mp ((hsec_smooth i) x)
      simpa [e, trivializationAt] using this
    -- On `e.baseSet`, `(e ⟨b, ·⟩).2 = e.continuousLinearMapAt ℝ b (·)`.
    have h_eq_nbhd : ∀ᶠ b in 𝓝 x, (e ⟨b, riemannSec (LeviCivita (I := I) g) (S i) Y W b⟩).2 =
        e.continuousLinearMapAt ℝ b (riemannSec (LeviCivita (I := I) g) (S i) Y W b) := by
      filter_upwards [e.open_baseSet.mem_nhds hex] with b hb
      change (Trivialization.continuousLinearEquivAt ℝ e b hb) _ = _
      rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e hb]
    have h_continuousLinearMapAt_smooth : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun b : M => e.continuousLinearMapAt ℝ b
          (riemannSec (LeviCivita (I := I) g) (S i) Y W b)) x := by
      apply h_triv.congr_of_eventuallyEq
      filter_upwards [h_eq_nbhd] with b hb
      exact hb.symm
    -- Compose with the linear functional `finBasisReprAt i : E →L[ℝ] ℝ`.
    have h_clm_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (finBasisReprAt (E := E) i : E → ℝ) :=
      (finBasisReprAt (E := E) i).contMDiff
    have h_comp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun b : M => finBasisReprAt (E := E) i
          (e.continuousLinearMapAt ℝ b (riemannSec (LeviCivita (I := I) g) (S i) Y W b))) x :=
      (h_clm_smooth.contMDiffAt).comp x h_continuousLinearMapAt_smooth
    refine h_comp.congr_of_eventuallyEq ?_
    filter_upwards with b
    exact finBasisReprAt_apply i _
  -- Trace formula: `ricciTensor g b (Y b) (W b) = ∑ᵢ (summand i) b` on a nbhd of x.
  -- Using `ricciTensor_apply_basisSum` and the chart-local trace expansion.
  have h_decomp_nhd : ∀ᶠ b in 𝓝 x,
      ricciTensor (I := I) g b (Y b) (W b) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr
            (e.continuousLinearMapAt ℝ b (riemannSec (LeviCivita (I := I) g) (S i) Y W b))) i := by
    -- Use the trace identity: `ricciTensor g b (Y b) (W b) = tr_b (Z ↦ riemannOp _ b Z (Y b) (W b))`.
    -- Then apply `trace_eq_chart_sum` with `b ∈ e.baseSet` and `F = riemannOp _ b · (Y b) (W b)`.
    -- The sum then equals `∑ᵢ ((chartModelBasis E).repr (e.continuousLinearMapAt ℝ b
    --                       (riemannOp _ b (chartBasisVecFiber x i b) (Y b) (W b)))) i`.
    -- And `riemannOp _ b (S i b) (Y b) (W b) = riemannSec _ (S i) Y W b` for `b` in the nbhd,
    -- which uses `S i b = chartBasisVecFiber x i b`.
    filter_upwards [e.open_baseSet.mem_nhds hex, hS_eqOn_nhd] with b hb hSb
    -- Step 1: trace identity.
    have h1 : ricciTensor (I := I) g b (Y b) (W b) =
        LinearMap.trace ℝ (TangentSpace I b)
          (ricciEndo (I := I) g b (Y b) (W b)) := ricciTensor_apply g b (Y b) (W b)
    -- Step 2: the underlying linear map is exactly `Z ↦ riemannOp _ b Z (Y b) (W b)`,
    -- which equals `(riemannOpEndo g b (Y b) (W b))`'s nuance (different but compatible).
    -- Actually `ricciEndo g b v w Z = riemannOp _ b Z v w` (note slot order).
    -- So `ricciEndo g b v w = (Z ↦ riemannOp _ b Z v w)` as a linear map T_b M → T_b M.
    -- Apply `trace_eq_chart_sum` with `F` the CLM version.
    -- The CLM `riemannOpZ : T_b M →L[ℝ] T_b M` defined by `Z ↦ riemannOp _ b Z (Y b) (W b)`.
    -- It coincides with `riemannOp (LeviCivita g) b` partially applied.
    let F : TangentSpace I b →L[ℝ] TangentSpace I b :=
      (riemannOp (LeviCivita (I := I) g) b).flip (Y b) |>.flip (W b)
    -- Verify F coincides with ricciEndo:
    -- `F Z = ((riemannOp _ b).flip (Y b)).flip (W b) Z = ((riemannOp _ b).flip (Y b)) Z (W b)
    --      = riemannOp _ b Z (Y b) (W b)`.
    have hF_eq : (F : TangentSpace I b →ₗ[ℝ] TangentSpace I b) =
        ricciEndo (I := I) g b (Y b) (W b) := by
      apply LinearMap.ext
      intro Z
      change F Z = riemannOp (LeviCivita (I := I) g) b Z (Y b) (W b)
      rfl
    -- Apply `trace_eq_chart_sum`.
    rw [h1, ← hF_eq]
    rw [trace_eq_chart_sum (I := I) (x := x) (b := b) hb F]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Each summand: `(chartModelBasis E).repr (e.continuousLinearMapAt ℝ b
    --                  (F (chartBasisVecFiber x i b))) i`.
    -- Want to rewrite `chartBasisVecFiber x i b` as `S i b`.
    -- Note: `e.localFrame basis i b = chartBasisVecFiber x i b` on `e.baseSet`.
    have hframe_eq : e.localFrame (chartModelBasis E) i b =
        chartBasisVecFiber (I := I) x i b := by
      rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hb)]
      simp only [Trivialization.basisAt, Module.Basis.map_apply,
        Trivialization.linearEquivAt_symm_apply]
      rfl
    have hSb_i : S i b = chartBasisVecFiber (I := I) x i b := (hSb i).trans hframe_eq
    rw [show chartBasisVecFiber (I := I) x i b = S i b from hSb_i.symm]
    -- The argument equality: `F (S i b) = riemannSec ... b`.
    have h_F_eq : F (S i b) = riemannOp (LeviCivita (I := I) g) b (S i b) (Y b) (W b) := by
      change ((riemannOp (LeviCivita (I := I) g) b).flip (Y b)).flip (W b) (S i b) =
        riemannOp (LeviCivita (I := I) g) b (S i b) (Y b) (W b)
      rfl
    have h_F_eq_riemannSec : F (S i b) = riemannSec (LeviCivita (I := I) g) (S i) Y W b := by
      rw [h_F_eq]
      exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g)
        (hS_smooth i) hY hW
    rw [h_F_eq_riemannSec]
  -- Conclude by smoothness of the sum and congruence.
  have hsum_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ b (riemannSec (LeviCivita (I := I) g) (S i) Y W b))) i) x := by
    apply ContMDiffAt.sum
    intro i _
    exact hsummand_smooth i
  refine hsum_smooth.congr_of_eventuallyEq ?_
  filter_upwards [h_decomp_nhd] with b hb
  exact hb

/-! ### Smoothness of `ricciTensor` as a (0,2)-tensor section -/

/-- The (0,2)-tensor bundle is locally instantiated for the `T%` macro. -/
local instance ricciTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance ricciTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance ricciTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  inferInstance

/-- **Smoothness of the Ricci tensor as a (0,2)-tensor section.** For a smooth Riemannian
metric `g` on `M`, the section `b ↦ ⟨b, ricciTensor g b⟩` of the (0,2)-tensor bundle
`fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` is `C^∞`. -/
theorem ricciTensor_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (ricciTensor (I := I) g b)) := by
  classical
  -- Two-stage descent via `cotangentCov_clmSection_smooth_aux`.
  -- Stage 1: For each smooth tangent section `Y`, `b ↦ ⟨b, ricciTensor g b (Y b)⟩` is a
  -- smooth section of `T*M = Hom(TM, ℝ)`.
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ricciTensor (I := I) g x)
  intro Y
  -- Stage 2: For each smooth tangent section `W`, the scalar `b ↦ ricciTensor g b (Y b) (W b)`
  -- is smooth.
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ricciTensor (I := I) g x (Y x))
  intro W
  -- Reduce to scalar smoothness via `contMDiffAt_section` for the trivial bundle.
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b (Y b) (W b)) :=
    ricciTensor_pairing_contMDiff g Y.contMDiff W.contMDiff
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ricciTensor (I := I) g y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ricciTensor (I := I) g y (Y y) (W y)⟩).2
  rfl

end RicciSmoothness

end Connection
end Integral
end DifferentialGeometry
