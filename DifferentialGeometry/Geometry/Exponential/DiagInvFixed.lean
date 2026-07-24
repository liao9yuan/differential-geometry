import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity

set_option autoImplicit false

/-!
# Fixed-base partial diffeomorphisms from diagonal exponential branches

This file restricts a selected diagonal-exponential inverse branch to one
fixed tangent fibre.  The resulting `C∞` partial diffeomorphism exposes the
intrinsic exponential and its selected inverse in the model space.
-/

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential
namespace DiagInvBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Restrict a selected diagonal-exponential branch to the tangent fibre over
`p`, expressed in the model space `E`. -/
def fixedPD
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ where
  toFun := fun u : E =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  invFun := fun q : M => ((B.inv (p, q)).snd : E)
  source :=
    (fun u : E => (⟨p, u⟩ : TangentBundle I M)) ⁻¹' B.hom.source
  target := (fun q : M => (p, q)) ⁻¹' B.dom
  map_source' := by
    intro u hu
    change (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source at hu
    have hmap := B.hom.map_source hu
    have heq := B.hom_eq hu
    change
      B.hom (⟨p, u⟩ : TangentBundle I M) =
        (p, expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u)) at heq
    rw [heq] at hmap
    exact hmap
  map_target' := by
    intro q hq
    change (p, q) ∈ B.dom at hq
    have hinv : B.inv (p, q) ∈ B.hom.source :=
      B.hom.map_target hq
    have htotal :
        B.inv (p, q) =
          (⟨p, (show TangentSpace I p from (B.inv (p, q)).snd)⟩ :
            TangentBundle I M) := by
      apply TotalSpace.ext (B.proj_eq hq)
      exact heq_of_eq rfl
    change
      (⟨p, (show TangentSpace I p from (B.inv (p, q)).snd)⟩ :
        TangentBundle I M) ∈ B.hom.source
    rw [← htotal]
    exact hinv
  left_inv' := by
    intro u hu
    have hleft := B.left_inv hu
    have hsnd :=
      congrArg (fun a : TangentBundle I M => (a.snd : E)) hleft
    simpa only [diagExp_apply] using hsnd
  right_inv' := by
    intro q hq
    simpa only using B.exp_eq hq
  open_source :=
    B.hom.open_source.preimage
      (FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p)
  open_target :=
    B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  contMDiffOn_toFun :=
    (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffOn
  contMDiffOn_invFun :=
    B.inv_fst_coord_inf (S := (fun q : M => (p, q)) ⁻¹' B.dom)
      (fun q hq => hq)

/-- The fixed-base partial diffeomorphism agrees with the intrinsic
exponential map. -/
@[simp]
theorem fixedPD_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) (u : E) :
    B.fixedPD u =
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from u) :=
  rfl

/-- The source of the fixed-base partial diffeomorphism is the corresponding
slice of the diagonal branch source. -/
@[simp]
theorem fixedPD_source
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.fixedPD.source =
      (fun u : E => (⟨p, u⟩ : TangentBundle I M)) ⁻¹' B.hom.source :=
  rfl

/-- The target of the fixed-base partial diffeomorphism is the corresponding
slice of the diagonal branch target. -/
@[simp]
theorem fixedPD_target
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.fixedPD.target =
      (fun q : M => (p, q)) ⁻¹' B.dom :=
  rfl

/-- The inverse of the fixed-base partial diffeomorphism is the selected
fixed-first coordinate readout. -/
@[simp]
theorem fixedPD_inv_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) (q : M) :
    B.fixedPD.symm q = ((B.inv (p, q)).snd : E) :=
  rfl

/-- The model-space origin belongs to the fixed-base source. -/
theorem fixedPD_zero_mem
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    (0 : E) ∈ B.fixedPD.source := by
  exact B.zero_mem

/-- The branch center belongs to the fixed-base target. -/
theorem fixedPD_center_mem
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    p ∈ B.fixedPD.target := by
  have hmap :=
    B.fixedPD.map_source B.fixedPD_zero_mem
  have hzero :
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E)) = p :=
    expMapIntrinsic_zero (I := I) g hEnorm p
  simpa only [fixedPD_apply, hzero] using hmap

/-- The inverse fixed-base chart sends its center to the model-space
origin. -/
@[simp]
theorem fixedPD_symm_center
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.fixedPD.symm p = (0 : E) := by
  have hleft :=
    B.fixedPD.left_inv B.fixedPD_zero_mem
  have hzero :
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E)) = p :=
    expMapIntrinsic_zero (I := I) g hEnorm p
  simpa only [fixedPD_apply, hzero] using hleft

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
