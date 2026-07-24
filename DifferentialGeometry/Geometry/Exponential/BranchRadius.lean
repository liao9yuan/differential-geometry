import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicGauss
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity
import DifferentialGeometry.Geometry.Operator.Operators

set_option autoImplicit false

/-!
# Radius functions from a selected inverse branch

This file develops the fixed-first calculus of a selected inverse branch of the
intrinsic exponential.  The centre used to select the branch is independent of
the fixed source point used by the radius function.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Half the squared length of the inverse vector selected by `B`, with the
first point fixed at `p`. -/
noncomputable def branchEnergy
    (g : SmoothRiemannianMetric I M)
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c)
    (p z : M) : Real :=
  (1 / 2 : Real) *
    g.inner (B.inv (p, z)).proj
      (B.inv (p, z)).snd
      (B.inv (p, z)).snd

/-- Length of the inverse vector selected by `B`, with the first point fixed
at `p`. -/
noncomputable def branchRadius
    (g : SmoothRiemannianMetric I M)
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c)
    (p z : M) : Real :=
  Real.sqrt
    (g.inner (B.inv (p, z)).proj
      (B.inv (p, z)).snd
      (B.inv (p, z)).snd)

/-- The branch radius is the square root of twice the branch energy. -/
theorem branchRadius_eq
    (g : SmoothRiemannianMetric I M)
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) (p : M) :
    branchRadius (I := I) g B p =
      fun z => Real.sqrt (2 * branchEnergy (I := I) g B p z) := by
  funext z
  simp only [branchRadius, branchEnergy]
  congr 1
  ring

/-- On the selected source, branch energy reads off the launch-vector energy. -/
theorem branchEnergy_exp
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source) :
    branchEnergy (I := I) g B p
      (expMapIntrinsic (I := I) g hEnorm p u) =
        (1 / 2 : Real) * g.inner p u u := by
  have hinv :
      B.inv (p, expMapIntrinsic (I := I) g hEnorm p u) =
        (⟨p, u⟩ : TangentBundle I M) := by
    simpa only [diagExp_apply] using B.left_inv hu
  unfold branchEnergy
  exact congrArg
    (fun a : TangentBundle I M =>
      (1 / 2 : Real) * g.inner a.proj a.snd a.snd) hinv

/-- On the selected source, branch radius reads off the launch-vector norm. -/
theorem branchRadius_exp
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source) :
    branchRadius (I := I) g B p
      (expMapIntrinsic (I := I) g hEnorm p u) =
        Real.sqrt (g.inner p u u) := by
  have hinv :
      B.inv (p, expMapIntrinsic (I := I) g hEnorm p u) =
        (⟨p, u⟩ : TangentBundle I M) := by
    simpa only [diagExp_apply] using B.left_inv hu
  unfold branchRadius
  exact congrArg
    (fun a : TangentBundle I M =>
      Real.sqrt (g.inner a.proj a.snd a.snd)) hinv

/-- Along a positive radial ray that stays in the selected source, the branch
radius is locally the affine function `s ↦ s |x|`. -/
theorem branchRadius_ray
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {x : TangentSpace I p} {t : Real}
    (ht : 0 < t)
    (hsrc :
      (⟨p, t • x⟩ : TangentBundle I M) ∈ B.hom.source) :
    (fun s : Real =>
      branchRadius (I := I) g B p
        (intrinsicGeodesic (I := I) g hEnorm p x s))
      =ᶠ[𝓝 t]
    (fun s : Real => s * Real.sqrt (g.inner p x x)) := by
  have hlaunch : Continuous
      (fun s : Real => (⟨p, s • x⟩ : TangentBundle I M)) := by
    exact
      (FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p).comp
        (continuous_id.smul continuous_const)
  have hsrc_ev :
      ∀ᶠ s in 𝓝 t,
        (⟨p, s • x⟩ : TangentBundle I M) ∈ B.hom.source :=
    hlaunch.continuousAt (B.hom.open_source.mem_nhds hsrc)
  have hpos_ev : ∀ᶠ s in 𝓝 t, 0 < s :=
    isOpen_Ioi.mem_nhds ht
  filter_upwards [hsrc_ev, hpos_ev] with s hs hsp
  rw [← intrinsicGeodesic_smul (I := I) g hEnorm p x s,
    ← expMapIntrinsic_def,
    branchRadius_exp (I := I) B hs,
    sqrt_gInner_smul_self (I := I) g p hsp.le x]

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem half_inner_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) :
    HasFDerivAt
      (fun v : E => (1 / 2 : Real) * g.inner p v v)
      (g.inner p u) u := by
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have h :=
    (gp.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)).const_mul
      (1 / 2 : Real)
  convert h using 1
  ext w
  change g.inner p u w =
    (1 / 2 : Real) * (g.inner p u w + g.inner p w u)
  rw [g.symm p w u]
  ring

/-- The derivative of the selected branch energy is the base metric pairing
with the derivative of the fixed-first inverse vector. -/
theorem branchEnergy_deriv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p q : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    (hq : (p, q) ∈ B.dom) :
    let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
    HasMFDerivAt I 𝓘(Real, Real)
      (branchEnergy (I := I) g B p) q
      ((g.inner p (invf q)).comp
        (mfderiv I 𝓘(Real, E) invf q)) := by
  dsimp only
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let U : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  have hUopen : IsOpen U := by
    change IsOpen ((fun z : M => (p, z)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqU : q ∈ U := hq
  have hinv : MDifferentiableAt I 𝓘(Real, E) invf q := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using
        B.inv_fst_coord_inf (S := U) (fun z hz => hz)
    exact (hinf.contMDiffAt (hUopen.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hquad :=
    (half_inner_hasFDerivAt (I := I) g p (invf q)).hasMFDerivAt.comp q
      hinv.hasMFDerivAt
  have heq :
      branchEnergy (I := I) g B p =ᶠ[𝓝 q]
        (fun z : M => (1 / 2 : Real) * g.inner p (invf z) (invf z)) := by
    filter_upwards [hUopen.mem_nhds hqU] with z hz
    simp only [branchEnergy, invf]
    rw [B.proj_eq hz]
  simpa only using hquad.congr_of_eventuallyEq heq

/-- The differential of the selected fixed-first inverse is a right inverse of
the differential of the intrinsic exponential. -/
theorem exp_inv_mfderiv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p q : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    (hq : (p, q) ∈ B.dom)
    (Y : TangentSpace I q) :
    let uB : E := (B.inv (p, q)).snd
    let dInv : E :=
      mfderiv I 𝓘(Real, E)
        (fun z : M => ((B.inv (p, z)).snd : E)) q Y
    ((mfderiv 𝓘(Real, E) I
        (fun u : E =>
          expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from u))
        uB dInv : TangentSpace I _) : E) =
      (Y : E) := by
  dsimp only
  let expf : E → M := fun u =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from u)
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let U : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  have hUopen : IsOpen U := by
    change IsOpen ((fun z : M => (p, z)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqU : q ∈ U := hq
  have hinv : MDifferentiableAt I 𝓘(Real, E) invf q := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using
        B.inv_fst_coord_inf (S := U) (fun z hz => hz)
    exact (hinf.contMDiffAt (hUopen.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(Real, E) I expf (invf q) := by
    exact ((intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt).mdifferentiableAt
      (by simp)
  have hright : (expf ∘ invf) =ᶠ[𝓝 q] id := by
    filter_upwards [hUopen.mem_nhds hqU] with z hz
    simpa only [Function.comp_apply, id_eq, expf, invf, U] using B.exp_eq hz
  have hchain :=
    mfderiv_comp_apply (I := I) (I' := 𝓘(Real, E)) (I'' := I)
      (x := q) (g := expf) hexp hinv Y
  have hchainE :
      ((mfderiv 𝓘(Real, E) I expf (invf q)
          (mfderiv I 𝓘(Real, E) invf q Y) : TangentSpace I _) : E) =
        ((mfderiv I I (expf ∘ invf) q Y : TangentSpace I _) : E) :=
    congrArg (fun V => (V : E)) hchain.symm
  have hidE :
      ((mfderiv I I (expf ∘ invf) q Y : TangentSpace I _) : E) =
        (Y : E) := by
    rw [hright.mfderiv_eq, mfderiv_id]
    rfl
  exact hchainE.trans hidE

/-- The differential of the selected fixed-first inverse is a left inverse of
the differential of the intrinsic exponential on the selected source. -/
theorem inv_exp_mfderiv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source)
    (w : TangentSpace I p) :
    mfderiv I 𝓘(Real, E)
      (fun z : M => ((B.inv (p, z)).snd : E))
      (expMapIntrinsic (I := I) g hEnorm p u)
      (mfderiv 𝓘(Real, E) I
        (fun v : E =>
          expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from v))
        (u : E) (w : E))
      = (w : E) := by
  let expf : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from v)
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let uE : E := (u : E)
  let wE : E := (w : E)
  let V : Set E :=
    (fun v : E => (⟨p, v⟩ : TangentBundle I M)) ⁻¹' B.hom.source
  have hVopen : IsOpen V := by
    exact B.hom.open_source.preimage
      (FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p)
  have huV : uE ∈ V := hu
  have htarget :
      (p, expf uE) ∈ B.dom := by
    change
      diagExp (I := I) g hEnorm
        (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.target
    rw [← B.hom_eq hu]
    exact B.hom.map_source hu
  let U : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  have hUopen : IsOpen U := by
    change IsOpen ((fun z : M => (p, z)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqU : expf uE ∈ U := htarget
  have hinv : MDifferentiableAt I 𝓘(Real, E) invf (expf uE) := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using
        B.inv_fst_coord_inf (S := U) (fun z hz => hz)
    exact (hinf.contMDiffAt (hUopen.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(Real, E) I expf uE := by
    exact ((intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt).mdifferentiableAt
      (by simp)
  have hleft : (invf ∘ expf) =ᶠ[𝓝 uE] id := by
    filter_upwards [hVopen.mem_nhds huV] with v hv
    have h := B.left_inv hv
    have hsnd := congrArg (fun a : TangentBundle I M => (a.snd : E)) h
    simpa only [Function.comp_apply, id_eq, expf, invf, diagExp_apply] using hsnd
  have hchain :=
    mfderiv_comp_apply (I := 𝓘(Real, E)) (I' := I)
      (I'' := 𝓘(Real, E)) (x := uE) (g := invf)
      hinv hexp wE
  have hid :
      mfderiv 𝓘(Real, E) 𝓘(Real, E)
          (invf ∘ expf) uE wE = wE := by
    have hmf :
        mfderiv 𝓘(Real, E) 𝓘(Real, E) (invf ∘ expf) uE =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) id uE :=
      hleft.mfderiv_eq
    rw [hmf, mfderiv_id]
    rfl
  simpa only [expf, invf, uE, wE] using hchain.symm.trans hid

/-- The selected branch radius is smooth at every nonzero vector in the
selected source. -/
theorem branchRadius_infAt
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (branchRadius (I := I) g B p)
      (expMapIntrinsic (I := I) g hEnorm p u) := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let U : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  have hUopen : IsOpen U := by
    change IsOpen ((fun z : M => (p, z)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqU : q ∈ U := by
    change (p, q) ∈ B.hom.target
    change
      diagExp (I := I) g hEnorm
        (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.target
    rw [← B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv : ContMDiffAt I 𝓘(Real, E) ∞ invf q := by
    have hinf : ContMDiffOn I 𝓘(Real, E) ∞ invf U := by
      simpa only [invf, U] using
        B.inv_fst_coord_inf (S := U) (fun z hz => hz)
    exact hinf.contMDiffAt (hUopen.mem_nhds hqU)
  have hinv_eq :
      B.inv (p, q) = (⟨p, u⟩ : TangentBundle I M) := by
    simpa only [q, diagExp_apply] using B.left_inv hu
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hinner : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun z : M => g.inner p (invf z) (invf z)) q := by
    have hg : ContMDiffAt I
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun _ : M => gp) q :=
      contMDiffAt_const
    simpa only [gp] using (hg.clm_apply hinv).clm_apply hinv
  have hinner_ne :
      g.inner p (invf q) (invf q) ≠ 0 := by
    have heq : invf q = (u : E) := by
      exact congrArg (fun a : TangentBundle I M => (a.snd : E)) hinv_eq
    rw [heq]
    exact hu_pos.ne'
  have hsqrt : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun z : M => Real.sqrt (g.inner p (invf z) (invf z))) q := by
    exact ((Real.contDiffAt_sqrt hinner_ne).contMDiffAt).comp q hinner
  have heq :
      branchRadius (I := I) g B p =ᶠ[𝓝 q]
        (fun z : M => Real.sqrt (g.inner p (invf z) (invf z))) := by
    filter_upwards [hUopen.mem_nhds hqU] with z hz
    simp only [branchRadius, invf]
    rw [B.proj_eq hz]
  simpa only [q] using hsqrt.congr_of_eventuallyEq heq

/-- A nonzero selected launch vector has an open endpoint neighborhood on
which the fixed-first branch radius is smooth. -/
theorem branchRadius_open
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    ∃ U : Set M,
      IsOpen U ∧
      expMapIntrinsic (I := I) g hEnorm p u ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞
        (branchRadius (I := I) g B p) U := by
  let D : Set M := (fun z : M => (p, z)) ⁻¹' B.dom
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let sq : M → Real := fun z => g.inner p (invf z) (invf z)
  let U : Set M := D ∩ sq ⁻¹' Set.Ioi 0
  have hDopen : IsOpen D := by
    change IsOpen ((fun z : M => (p, z)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
  have hinv : ContMDiffOn I 𝓘(Real, E) ∞ invf D := by
    simpa only [invf, D] using
      B.inv_fst_coord_inf (S := D) (fun z hz => hz)
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hsq : ContMDiffOn I 𝓘(Real, Real) ∞ sq D := by
    have hgp : ContMDiffOn I
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun _ : M => gp) D :=
      contMDiffOn_const
    simpa only [sq, gp] using (hgp.clm_apply hinv).clm_apply hinv
  have hUopen : IsOpen U := by
    exact hsq.continuousOn.isOpen_inter_preimage hDopen isOpen_Ioi
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  have hqD : q ∈ D := by
    change (p, q) ∈ B.hom.target
    change
      diagExp (I := I) g hEnorm
        (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.target
    rw [← B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv_q :
      B.inv (p, q) = (⟨p, u⟩ : TangentBundle I M) := by
    simpa only [q, diagExp_apply] using B.left_inv hu
  have hsq_q : sq q = g.inner p u u := by
    change
      g.inner p ((B.inv (p, q)).snd : E) ((B.inv (p, q)).snd : E) =
        g.inner p u u
    rw [hinv_q]
  have hqU : q ∈ U := by
    refine ⟨hqD, ?_⟩
    change 0 < sq q
    rw [hsq_q]
    exact hu_pos
  have hsqU : ContMDiffOn I 𝓘(Real, Real) ∞ sq U :=
    hsq.mono Set.inter_subset_left
  have hsqrt : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z => Real.sqrt (sq z)) U := by
    intro z hz
    exact
      (Real.contDiffAt_sqrt hz.2.ne').contMDiffAt.comp_contMDiffWithinAt z
        (hsqU z hz)
  refine ⟨U, hUopen, hqU, ContMDiffOn.congr hsqrt ?_⟩
  intro z hz
  simp only [branchRadius, sq, invf]
  rw [B.proj_eq hz.1]

/-- The gradient of the fixed-first branch energy is the terminal velocity of
the intrinsic geodesic selected by the launch vector. -/
theorem grad_branchEnergy
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source) :
    gradientFun (I := I) g
        (branchEnergy (I := I) g B p)
        (expMapIntrinsic (I := I) g hEnorm p u) =
      (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let invf : M → E := fun z => ((B.inv (p, z)).snd : E)
  let uB : E := invf q
  let dInv : TangentSpace I q → E := fun Y =>
    mfderiv I 𝓘(Real, E) invf q Y
  have hq : (p, q) ∈ B.dom := by
    change
      diagExp (I := I) g hEnorm
        (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.target
    rw [← B.hom_eq hu]
    exact B.hom.map_source hu
  have hinv :
      B.inv (p, q) = (⟨p, u⟩ : TangentBundle I M) := by
    simpa only [q, diagExp_apply] using B.left_inv hu
  have huB : uB = (u : E) := by
    exact congrArg (fun a : TangentBundle I M => (a.snd : E)) hinv
  have hderiv := branchEnergy_deriv (I := I) B hq
  apply gradientFun_eq_of_flat (I := I) g
  apply LinearMap.ext
  intro Y
  change
    mfderiv I 𝓘(Real, Real)
        (branchEnergy (I := I) g B p) q Y =
      g.inner q
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd Y
  rw [hderiv.mfderiv]
  change g.inner p uB (dInv Y) =
    g.inner q
      (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd Y
  rw [huB]
  have hgauss :=
    intrinsic_gauss (I := I) g hEnorm p uB (dInv Y)
  have hright :
      ((mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from v))
          uB (dInv Y) :
        TangentSpace I
          (expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from uB))) : E) =
        (Y : E) := by
    simpa only [uB, dInv, invf] using
      exp_inv_mfderiv (I := I) B hq Y
  rw [huB] at hgauss hright
  have hpair :
      g.inner q
          (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
          (show TangentSpace I q from
            ((mfderiv 𝓘(Real, E) I
              (fun v : E =>
                expMapIntrinsic (I := I) g hEnorm p
                  (show TangentSpace I p from v))
              (u : E) (dInv Y) :
              TangentSpace I q) : E)) =
        g.inner q
          (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd Y := by
    exact congrArg
      (fun Z : E =>
        g.inner q
          (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
          (show TangentSpace I q from Z)) hright
  have hgauss' :
      g.inner q
          (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
          (show TangentSpace I q from
            ((mfderiv 𝓘(Real, E) I
              (fun v : E =>
                expMapIntrinsic (I := I) g hEnorm p
                  (show TangentSpace I p from v))
              (u : E) (dInv Y) :
              TangentSpace I q) : E)) =
        g.inner p u (dInv Y) := by
    simpa only [q] using hgauss
  exact hgauss'.symm.trans hpair

/-- The gradient of the nonzero fixed-first branch radius is the terminal unit
velocity of its intrinsic radial geodesic. -/
theorem grad_branchRadius
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M}
    (B : DiagInvBranch (I := I) g hEnorm c)
    {u : TangentSpace I p}
    (hu : (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.source)
    (hu_pos : 0 < g.inner p u u) :
    gradientFun (I := I) g
        (branchRadius (I := I) g B p)
        (expMapIntrinsic (I := I) g hEnorm p u) =
      (Real.sqrt (g.inner p u u))⁻¹ •
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p u
  let e : M → Real := branchEnergy (I := I) g B p
  let e2 : M → Real := (2 : Real) • e
  have hq : (p, q) ∈ B.dom := by
    change
      diagExp (I := I) g hEnorm
        (⟨p, u⟩ : TangentBundle I M) ∈ B.hom.target
    rw [← B.hom_eq hu]
    exact B.hom.map_source hu
  have he_diff : MDifferentiableAt I 𝓘(Real, Real) e q := by
    exact (branchEnergy_deriv (I := I) B hq).mdifferentiableAt
  have he2_diff : MDifferentiableAt I 𝓘(Real, Real) e2 q := by
    exact he_diff.const_smul 2
  have he2_val : e2 q = g.inner p u u := by
    simp only [e2, e, Pi.smul_apply, smul_eq_mul, q,
      branchEnergy_exp (I := I) B hu]
    ring
  have hsqrt_diff : DifferentiableAt Real Real.sqrt (e2 q) := by
    rw [he2_val]
    exact (Real.hasDerivAt_sqrt hu_pos.ne').differentiableAt
  rw [branchRadius_eq (I := I) g B p]
  change gradientFun (I := I) g
      (fun z : M => Real.sqrt (e2 z)) q =
    (Real.sqrt (g.inner p u u))⁻¹ •
      (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd
  rw [gradientFun_comp (I := I) g hsqrt_diff he2_diff,
    gradientFun_const_smul (I := I) g 2 he_diff,
    show gradientFun (I := I) g e q =
        (intrinsicVelocityLift (I := I) g hEnorm p u 1).snd by
      simpa only [e, q] using grad_branchEnergy (I := I) B hu,
    he2_val,
    (Real.hasDerivAt_sqrt hu_pos.ne').deriv,
    smul_smul]
  have hsqrt_ne : Real.sqrt (g.inner p u u) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hu_pos
  congr 1
  field_simp

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
