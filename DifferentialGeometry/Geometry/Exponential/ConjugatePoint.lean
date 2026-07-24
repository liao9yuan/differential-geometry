import DifferentialGeometry.Geometry.Exponential.JacobiVariation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Conjugate vectors of the intrinsic exponential

The conjugate-point interface of the option-1 route (brick N of
`Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`), in the form ruled on
2026-07-19: the **definition** is differential-singularity of the intrinsic
exponential in its vector slot, and the **Jacobi characterization** is a
bridge theorem through `intrinsic_jacobi_one`.

* `IsConjVec g hEnorm p x` — the vector-slot differential of
  `expMapIntrinsic g hEnorm p` at `x` is not injective (singular, since the
  fibers are finite-dimensional of equal dimension).
* `isConjVec_iff` — singularity ⟺ a nonzero kernel vector.
* `isConjVec_iff_jacobi` — singularity ⟺ some variation Jacobi field
  `∂ₛ|₀ intrinsicGeodesic p (x + s•w) t` with `w ≠ 0` vanishes at `t = 1`.
  This is the hinge to the variational theory: by `intrinsic_jacobi` the
  variation field is Jacobi along the whole geodesic, and by `jacobi_unique`
  (`Variation/JacobiCoord.lean`) it is the *only* Jacobi field with its
  initial data.

No smallness or injectivity-radius hypothesis appears anywhere: the intrinsic
exponential is globally smooth (`intrinsicExp_smooth`), so the interface is
meaningful at every scale.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace E]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Conjugate vector.**  `x` is conjugate for the exponential at `p` when
the vector-slot differential of the intrinsic exponential at `x` is not
injective. -/
def IsConjVec
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x : E) : Prop :=
  ¬ Function.Injective fun w : E =>
      mfderiv 𝓘(ℝ, E) I
        (fun b : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from b)) x w

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Singularity ⟺ nonzero kernel vector.** -/
theorem isConjVec_iff
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x : E) :
    IsConjVec (I := I) g hEnorm p x ↔
      ∃ w : E, w ≠ 0 ∧
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from b)) x w = 0 := by
  classical
  set f := mfderiv 𝓘(ℝ, E) I
    (fun b : E => expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from b)) x with hf
  have hker : Function.Injective (fun w : E => f w) ↔
      ∀ w : E, f w = 0 → w = 0 := by
    constructor
    · intro hinj w hw
      have h0 : f w = f 0 := by rw [hw, map_zero]
      exact hinj h0
    · intro hker a b hab
      have hab' : f a = f b := hab
      have hsub : f (a - b) = 0 := by
        calc f (a - b) = f a - f b := map_sub f a b
          _ = 0 := by rw [hab', sub_self]
      exact sub_eq_zero.mp (hker _ hsub)
  unfold IsConjVec
  rw [← hf, hker]
  push Not
  constructor
  · rintro ⟨w, hw0, hwne⟩
    exact ⟨w, hwne, hw0⟩
  · rintro ⟨w, hwne, hw0⟩
    exact ⟨w, hw0, hwne⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Jacobi characterization of conjugate vectors.**  `x` is conjugate iff
some variation Jacobi field with nonzero direction `w` vanishes at time one:
`∂ₛ|₀ intrinsicGeodesic p (x + s•w) 1 = 0`.  Bridge through
`intrinsic_jacobi_one`. -/
theorem isConjVec_iff_jacobi
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x : E) :
    IsConjVec (I := I) g hEnorm p x ↔
      ∃ w : E, w ≠ 0 ∧
        mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + s • w) 1) 0 (1 : ℝ) = 0 := by
  rw [isConjVec_iff (I := I) g hEnorm p x]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [intrinsic_jacobi_one (I := I) g hEnorm p x w]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The variation Jacobi field vanishes at time zero.**  Every geodesic of
the variation starts at `p`, so the `s`-derivative at `t = 0` is zero.  With
`isConjVec_iff_jacobi` this gives the classical phrasing: a conjugate vector
carries a nontrivial Jacobi field vanishing at both ends of the segment. -/
theorem jacobiVar_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (x w : E) :
    mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x + s • w) 0) 0 (1 : ℝ) = 0 := by
  have hconst : (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w) 0) = fun _ : ℝ => p := by
    funext s
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  rw [hconst, mfderiv_const]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Rescaling the launch vector and evaluating at time one agrees, after
differentiation, with evaluating the rescaled variation at the original
time. -/
theorem jacobiVar_smul
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u w : E) {c : ℝ} (hc : c ≠ 0) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1) 0 (1 : ℝ) := by
  have hfun :
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + s • (c⁻¹ • w)) c) =
        fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1 := by
    funext s
    have hscale : c • (u + s • (c⁻¹ • w)) = c • u + s • w := by
      rw [smul_add, smul_smul, smul_smul]
      congr 1
      field_simp
    calc
      intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c =
        intrinsicGeodesic (I := I) g hEnorm p
          (c • (show TangentSpace I p from u + s • (c⁻¹ • w))) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm p
          (show TangentSpace I p from u + s • (c⁻¹ • w)) c).symm
      _ = intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from c • u + s • w) 1 := by
        exact congrArg
          (fun z : E => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from z) 1)
          hscale
  rw [hfun]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A conjugate vector at `c • u` produces a nontrivial intrinsic Jacobi
variation along the geodesic launched by `u` that vanishes at time `c`. -/
theorem conjVec_jacobi_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E) {c : ℝ} (hc : c ≠ 0)
    (hconj : IsConjVec (I := I) g hEnorm p (c • u)) :
    ∃ z : E, z ≠ 0 ∧
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + s • z) c) 0 (1 : ℝ) = 0 := by
  rw [isConjVec_iff_jacobi (I := I) g hEnorm p (c • u)] at hconj
  obtain ⟨w, hw, hwend⟩ := hconj
  refine ⟨c⁻¹ • w, smul_ne_zero (inv_ne_zero hc) hw, ?_⟩
  rw [jacobiVar_smul (I := I) g hEnorm p u w hc]
  exact hwend

end Riemannian
end Geometry
end DifferentialGeometry
