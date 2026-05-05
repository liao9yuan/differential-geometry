import DifferentialGeometry.Analysis.Laplacian.H1Compl
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# L² inclusion of smooth scalars and the H¹ completion

For a closed Riemannian manifold `(M, g)`, smooth scalars `SmoothScalar g`
inject continuously into `Lp ℝ 2 μ_g` via the canonical "smooth function ↦
its L² class" map, with the operator-norm bound `‖f‖_{L²} ≤ ‖f‖_{pre H¹}`.
This map then extends uniquely along the dense embedding
`smoothToH1Compl : SmoothScalar g →L[ℝ] H1Compl g` to a continuous linear
map `H1Compl g →L[ℝ] Lp ℝ 2 μ_g`.

This furnishes the link between the abstract H¹ Hilbert completion and
classical L² function spaces, and is used to define the resolvent of
the variational Laplacian via Lax-Milgram.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Smooth scalar belongs to Lp on a closed manifold -/

/-- A smooth scalar on a closed manifold is in `MemLp 2`: it is continuous
and has compact support (because `M` is compact). -/
lemma SmoothScalar.memLp_two {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-! ## The L² inclusion as a linear map -/

/-- The linear map from smooth scalars to `Lp ℝ 2 μ_g` sending each smooth
function to its `Lp` class. -/
noncomputable def smoothToLpLin (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →ₗ[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun f := f.memLp_two.toLp f.toFun
  map_add' f h := by
    -- `(f + h).toFun = f.toFun + h.toFun` definitionally (rfl).
    -- `(MemLp.add hf hh).toLp (f + h) = hf.toLp f + hh.toLp h` via `MemLp.toLp_add`.
    have h_lhs_rfl : (f + h).memLp_two.toLp (f + h).toFun =
        (f.memLp_two.add h.memLp_two).toLp (f.toFun + h.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_add]
  map_smul' c f := by
    -- `(c • f).toFun = c • f.toFun` definitionally (rfl).
    have h_lhs_rfl : (c • f).memLp_two.toLp (c • f).toFun =
        (f.memLp_two.const_smul c).toLp (c • f.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_const_smul]
    rfl

@[simp] lemma smoothToLpLin_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToLpLin (I := I) (M := M) g f = f.memLp_two.toLp f.toFun := rfl

/-! ## Squared L² norm equals `∫ f²` -/

/-- The squared norm of `MemLp.toLp f.toFun` equals `∫ f.toFun² dμ_g` for a
smooth real scalar on a closed manifold. -/
lemma SmoothScalar.norm_smoothToLp_sq {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  -- Use `real_inner_self_eq_norm_sq` on Lp ℝ 2: `⟨f, f⟩ = ‖f‖²` for ℝ.
  have h := real_inner_self_eq_norm_sq (smoothToLpLin (I := I) (M := M) g f)
  -- `h : ⟨smoothToLpLin g f, smoothToLpLin g f⟩_ℝ = ‖smoothToLpLin g f‖^2`.
  -- Unfold L² inner product: ⟨smoothToLpLin g f, smoothToLpLin g f⟩
  -- = ∫ ⟨smoothToLpLin g f a, smoothToLpLin g f a⟩_ℝ ∂μ.
  rw [L2.inner_def (𝕜 := ℝ)] at h
  -- a.e.-rewrite the integrand using `f.memLp_two.toLp f.toFun =ᵐ f.toFun`.
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((smoothToLpLin (I := I) (M := M) g f : Lp ℝ 2 _) a)
          ((smoothToLpLin (I := I) (M := M) g f : Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLin (I := I) (M := M) g f : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    -- `⟨a, b⟩_ℝ = a * b` for reals.
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

/-! ## Norm bound: smooth-to-Lp is non-expansive in pre-H¹ norm -/

/-- The squared seminorm of a smooth scalar in pre-H¹ equals the H¹
self-pairing. -/
lemma SmoothScalar.norm_sq_eq_inner_self {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖f‖ ^ 2 = smoothScalarH1Inner (I := I) (M := M) f f := by
  -- Use real_inner_self_eq_norm_sq: ⟨f, f⟩_ℝ = ‖f‖^2.
  have h := real_inner_self_eq_norm_sq f
  -- ⟨f, f⟩ = smoothScalarH1Inner f f for our PreInnerProductSpace.Core.
  rw [SmoothScalar.inner_def] at h
  exact h.symm

/-- Squared L² norm is bounded by the squared pre-H¹ norm. -/
lemma SmoothScalar.norm_smoothToLp_sq_le {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold smoothScalarH1Inner
  -- ‖smoothToLp f‖² = ∫ f² ≤ ∫ f² + ∫ g(grad f, grad f) = ‖f‖²_pre.
  -- Both terms are non-negative.
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x ((grad_g (I := I) g f.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g f.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

/-- L²-norm of the smooth-inclusion is bounded by the pre-H¹ norm. -/
lemma SmoothScalar.norm_smoothToLp_le {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ≤ ‖f‖ := by
  -- both norms are non-negative; reduce to the squared inequality.
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLin (I := I) (M := M) g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

/-- The bound: `‖smoothToLpLin g f‖ ≤ 1 * ‖f‖`. -/
lemma SmoothScalar.norm_smoothToLp_le_one_mul {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

/-! ## The L² inclusion as a continuous linear map -/

/-- The continuous linear map from smooth scalars to `Lp ℝ 2 μ_g`. -/
noncomputable def smoothToLp (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothToLpLin (I := I) (M := M) g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

@[simp] lemma smoothToLp_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToLp (I := I) (M := M) g f =
      f.memLp_two.toLp f.toFun := rfl

/-! ## The L² inclusion extended to the H¹ completion -/

/-- `toComplL` has dense range. -/
private lemma denseRange_toComplL_smoothScalar (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- `toComplL` is uniform-inducing. -/
private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

/-- The continuous linear extension of `smoothToLp` along the dense
embedding `smoothToH1Compl`. Since `Lp ℝ 2 μ_g` is complete (a Banach
space), the extension exists. -/
noncomputable def H1ComplToLp (g : SmoothRiemannianMetric I M) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLp (I := I) (M := M) g)
    (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g)

@[simp] lemma H1ComplToLp_smoothToH1Compl (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g f) =
      smoothToLp (I := I) (M := M) g f := by
  unfold H1ComplToLp
  exact ContinuousLinearMap.extend_eq (smoothToLp (I := I) (M := M) g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) f

end Laplacian
end Analysis
end DifferentialGeometry

end
