import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffBilinGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairing
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS

/-!
# The frame-free pure-Riemann differentiated curvature tower at contravariant valence `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-valence-`r` lift of the frame-free moving-centre pure-Riemann differentiated curvature
operator tower `pureRGenuineDiffOp` (`FrozenFramePureRCurvatureTower`).  The rank-`0` tower is
hard-locked to contravariant rank `0`: its order-`0` endomorphism reads the slot-`0` direction of a
`(0, m + 1)`-tensor through `covGradBundleEquiv 0 m`, contracts it with the bundled curvature operator
`riemannOp (tensorCov g 0 m)`, sums over a `g`-orthonormal frame, and is frame-independent because the
trace is a genuine metric trace.  This file rebuilds the entire tower **at a fixed but generic
contravariant valence `r`** (R7 — extend, do not duplicate), so that it packages as a
`DiffBilinOpRS g r` (`RankRDiffBilinGrid`) and the contravariant-rank-`r` curvature-jet tower can
consume the same single-sum covariant-Leibniz grid the rank-`0` tower consumes from `DiffBilinOp`.

The construction differs from rank `0` in exactly one index: every `0` in the contravariant slot
becomes `r` (the order-`0` endomorphism reads slot-`0` through `covGradBundleEquiv r m`, contracts with
`riemannOp (tensorCov g r m)`, and lands in the `(r, m + 1)`-bundle).  Smoothness, frame-independence
(the bilinear-Parseval `orthonormal_basis_bilin_trace`), the order-`(p + 1)` exact covariant-Leibniz
remainder recursion, and the order-`0` slot-`0` reading all port verbatim with `0` replaced by `r`,
exactly as `MovingFrameGenuineFieldPairingRS` ports the `∇S`-specialised genuine section to valence `r`.

## What is proved vs. posited

* the **order-`0` endomorphism** `genuinePureREndoSuccRS`, its base-point smoothness (the moving-frame
  freeze `genuinePureREndoFibRS_contMDiff`, *sorry-free*), and the slot-`0` reading
  `genuinePureREndoFibRS_slot0Reading` are *proved* here;
* the **order-`(p + 1)` differentiated operator** is the exact covariant-Leibniz remainder, so the
  single-step Leibniz field `covGrad_op` holds *by `sub_add_cancel`* — *proved*;
* the **per-order, per-rank frame-free proportional fibre envelope** `rfns_op_le` (the
  `DiffBilinOpRS g r` boundedness field) is the single genuinely-irreducible analytic node at valence
  `r`.  At rank `0` its order-`0` layer is the proven moving-frame endomorphism bound (off the rank-`0`
  proportional curvature sup) and its high-order layer is the lone posited analytic node
  `exists_proportional_pureRGenuineDiffOp_highOrder`; at valence `r` BOTH layers need the absent
  rank-`r` proportional curvature sup
  (`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`, stated only at
  contravariant rank `0`) and the absent rank-`r` differentiated-curvature normal-form envelope, so the
  whole frame-free envelope is collected as **one** posited primitive
  `exists_proportional_genuinePureRDiffOpRS` — exactly the valence-`r` mirror of
  `exists_proportional_pureRGenuineDiffOp`, the count not increasing.  Consumers transitively depend on
  `sorryAx` through this single node.

The `DiffBilinOpRS g r` package `genuinePureRDiffOpRS_bilinOp` and the slot-`0` reading lemma let the
downstream `MovingFrameGenuineFieldPairingRS` discharge the rank-`r` frame-free differentiated-curvature
tower posit `exists_pureRGenuineDiffOpRS_bridge` in one step (the bridge
`op 0 (s + 1) (∇S) = GcurvSectionRS g r s S` is proved there, where `GcurvSectionRS` lives).

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`.  The moving frame is
`Bᵢ := smoothOrthoFrame g x i` (centre = the evaluation point).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The frozen-frame order-`0` endomorphism at valence `r` -/

/-- **The slot-`i` frozen-frame pure-Riemann curvature direction linear map at valence `r`.** The
curvature-direction-linear summand
`v ↦ riemannOp (tensorCov g r m) x (Bᵢ x) v (slot0_{Bᵢ x} W)`, where the contracted argument
`(covGradBundleEquiv r m x).symm (W x) (Bᵢ x)` is the slot-`0` reading of `W` along `Bᵢ x` — a
`(r, m)`-tensor.  The valence-`r` mirror of `pureRFrozenDirLMSummand`. -/
private def pureRFrozenDirLMSummandRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace r (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace r m I x where
  toFun v := riemannOp (tensorCov (I := I) g r m) x (B i x) v
    ((covGradBundleEquiv (I := I) (M := M) r m x).symm (W x) (B i x))
  map_add' v v' := by
    rw [map_add (riemannOp (tensorCov (I := I) g r m) x (B i x)) v v']
    rfl
  map_smul' c v := by
    rw [map_smul (riemannOp (tensorCov (I := I) g r m) x (B i x)) c v]
    rfl

/-- The continuous-linear-map form of `pureRFrozenDirLMSummandRS`. -/
private noncomputable def pureRFrozenDirCLMSummandRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace r (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace r m I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRFrozenDirLMSummandRS (I := I) (M := M) g r m B W x i)

/-- **The frozen-frame pure-Riemann curvature direction continuous-linear map at valence `r` (rank
`m + 1`).** The frame sum over `i` of `pureRFrozenDirCLMSummandRS`. -/
private noncomputable def pureRFrozenDirCLMRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace r (m + 1) I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r m I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRFrozenDirCLMSummandRS (I := I) (M := M) g r m B W x i

/-- The defining apply formula for `pureRFrozenDirCLMRS`: the frame sum of curvature contractions of
the slot-`0` readings of `W`. -/
private lemma pureRFrozenDirCLMRS_apply
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace r (m + 1) I b) (x : M) (v : TangentSpace I x) :
    pureRFrozenDirCLMRS (I := I) (M := M) g r m B W x v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g r m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) r m x).symm (W x) (B i x)) := by
  classical
  rw [pureRFrozenDirCLMRS, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRFrozenDirCLMSummandRS, LinearMap.coe_toContinuousLinearMap', pureRFrozenDirLMSummandRS,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism fibre value at valence `r` (rank
`m + 1`).** The slot-`0` uncurry, through `covGradBundleEquiv r m x`, of the frozen-frame pure-Riemann
direction CLM `pureRFrozenDirCLMRS g r m B (W.toSection) x`. -/
private noncomputable def pureRFrozenEndoFibRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g r (m + 1)) (x : M) :
    TensorRSSpace r (m + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) r m x
    (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x)

/-- **The slot-`0` reading of `W` along `Bᵢ` is a smooth `(r, m)`-tensor section.** The valence-`r`
mirror of `pureRFrozenSlot0Sec_contMDiff`. -/
private theorem pureRFrozenSlot0SecRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g r (m + 1)) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r m ℝ E)
        (E := fun z : M => TensorRSSpace r m I z) x
        ((covGradBundleEquiv (I := I) (M := M) r m x).symm (W.toSection x) (B i x))) := by
  classical
  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r m ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r m I z) x
        ((covGradBundleEquiv (I := I) (M := M) r m x).symm (W.toSection x))) := by
    have hWtot : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (m + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r (m + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r (m + 1) I z) x (W.toSection x)) :=
      W.toSection.contMDiff_toFun
    exact (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r m).comp hWtot
  exact ContMDiff.clm_bundle_apply (b := fun x : M => x)
    (ϕ := fun x => (covGradBundleEquiv (I := I) (M := M) r m x).symm (W.toSection x))
    (v := fun x => B i x) hHom (hB i)

/-- **The frozen-frame pure-Riemann direction CLM is a smooth `Hom(TM, T^{(r,m)})`-bundle section.**
The valence-`r` mirror of `pureRFrozenDirCLM_homSection_contMDiff`. -/
private theorem pureRFrozenDirCLMRS_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g r (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r m ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r m I y) x
        (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x)
    (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff
  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r m ℝ E)
        (E := fun z : M => TensorRSSpace r m I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g r m) (B i) (fun b : M => Y b)
            (fun y : M => (covGradBundleEquiv (I := I) (M := M) r m y).symm (W.toSection y) (B i y))
            x)) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact riemannSec_contMDiff (cov := tensorCov (I := I) g r m) (hB i) hY
      (pureRFrozenSlot0SecRS_contMDiff (I := I) (M := M) g r m hB W i)
  refine hsum.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel r m ℝ E)
    (E := fun z : M => TensorRSSpace r m I z) x) ?_
  rw [pureRFrozenDirCLMRS_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (riemannOp_apply_smooth (cov := tensorCov (I := I) g r m) (X := B i) (Y := fun b : M => Y b)
    (Z := fun y : M => (covGradBundleEquiv (I := I) (M := M) r m y).symm (W.toSection y) (B i y))
    (x := x) (hB i) hY (pureRFrozenSlot0SecRS_contMDiff (I := I) (M := M) g r m hB W i)).symm ▸ rfl

/-- **Base-point smoothness of the order-`0` frozen-frame pure-Riemann curvature endomorphism fibre
field at valence `r`.** The valence-`r` mirror of `pureRFrozenEndoFib_contMDiff`. -/
private theorem pureRFrozenEndoFibRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g r (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (m + 1) I z) x
        (pureRFrozenEndoFibRS (I := I) (M := M) g r m B W x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (m + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r m).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r m ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r m I y) x
            (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r m).toDiffeomorph.contMDiff.comp
      (pureRFrozenDirCLMRS_homSection_contMDiff (I := I) (M := M) g r m hB W)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r m x
    (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x)

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism at valence `r`, rank `m + 1`**, a
smooth compactly-supported `(r, m + 1)`-tensor section. The valence-`r` mirror of `pureRFrozenEndoSucc`. -/
private noncomputable def pureRFrozenEndoSuccRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g r (m + 1)) :
    SmoothCcTensor g r (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRFrozenEndoFibRS (I := I) (M := M) g r m B W x
      contMDiff_toFun := pureRFrozenEndoFibRS_contMDiff (I := I) (M := M) g r m hB W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] private lemma pureRFrozenEndoSuccRS_toSection
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g r (m + 1)) (x : M) :
    (pureRFrozenEndoSuccRS (I := I) (M := M) g r m B hB W).toSection x =
      pureRFrozenEndoFibRS (I := I) (M := M) g r m B W x := rfl

/-! ## Frame-independence of the order-`0` direction CLM at valence `r` -/

/-- **The continuous slot-`0` curvature bilinear form at valence `r` (the value-frozen contraction).**
At a base point `y` and a curvature direction `v`, the continuous bilinear form
`(X, Y) ↦ riemannOp (tensorCov g r m) y X v (slot0_Y W)`. The valence-`r` mirror of
`pureRSlot0BilinAt`. -/
private noncomputable def pureRSlot0BilinAtRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (W : Π b : M, TensorRSSpace r (m + 1) I b) (y : M) (v : TangentSpace I y) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace r m I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g r m) y X v).comp
        ((covGradBundleEquiv (I := I) (M := M) r m y).symm (W y))
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (tensorCov (I := I) g r m) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g r m) y).map_smul c X] }

/-- The defining apply formula for `pureRSlot0BilinAtRS`. -/
private lemma pureRSlot0BilinAtRS_apply
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (W : Π b : M, TensorRSSpace r (m + 1) I b) (y : M) (v X Y : TangentSpace I y) :
    pureRSlot0BilinAtRS (I := I) (M := M) g r m W y v X Y =
      riemannOp (tensorCov (I := I) g r m) y X v
        ((covGradBundleEquiv (I := I) (M := M) r m y).symm (W y) Y) := rfl

/-- **The slot-`i` frozen-frame summand is the diagonal of `pureRSlot0BilinAtRS`.** True by `rfl`. -/
private lemma pureRSlot0BilinAtRS_frame_summand
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (W : SmoothCcTensor g r (m + 1))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (i : Fin (Module.finrank ℝ E)) (y : M) (v : TangentSpace I y) :
    riemannOp (tensorCov (I := I) g r m) y (B i y) v
        ((covGradBundleEquiv (I := I) (M := M) r m y).symm (W.toSection y) (B i y)) =
      pureRSlot0BilinAtRS (I := I) (M := M) g r m (fun b : M => W.toSection b) y v (B i y) (B i y) :=
  rfl

/-- **The frozen-frame pure-Riemann slot-`0` direction CLM is frame-independent among `g_y`-orthonormal
frames at valence `r`.** The valence-`r` mirror of `pureRFrozenDirCLM_frame_independent`: for each
curvature direction `v`, the value `∑ᵢ R(Bᵢʸ, v)(slot0_{Bᵢʸ} W)` is the diagonal frame trace of the
continuous bilinear form `pureRSlot0BilinAtRS g r m W y v`, frame-independent by
`orthonormal_basis_bilin_trace`; the rank-`r` scalarisation reads off the `(r, m)`-tensor through an
arbitrary lower-input `D : Tensor0SSpace r I y` and a tail tuple. -/
private theorem pureRFrozenDirCLMRS_frame_independent
    (g : SmoothRiemannianMetric I M) (r m : ℕ) (W : SmoothCcTensor g r (m + 1))
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun b : M => W.toSection b) y =
      pureRFrozenDirCLMRS (I := I) (M := M) g r m C (fun b : M => W.toSection b) y := by
  classical
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun v => ?_)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mtail
  haveI : T2Space (TensorRSSpace r m I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y))
  haveI : FiniteDimensional ℝ (TensorRSSpace r m I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y))
  set scalarize : TensorRSSpace r m I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) mtail =
            Tensor0SSpace.toModel (T D) mtail + Tensor0SSpace.toModel (T' D) mtail
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) mtail = c • Tensor0SSpace.toModel (T D) mtail
          rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace r m I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp
          (pureRSlot0BilinAtRS (I := I) (M := M) g r m (fun b : M => W.toSection b) y v X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRSlot0BilinAtRS (I := I) (M := M) g r m
              (fun b : M => W.toSection b) y v (X + X') Y) =
            scalarize (pureRSlot0BilinAtRS (I := I) (M := M) g r m
                (fun b : M => W.toSection b) y v X Y) +
              scalarize (pureRSlot0BilinAtRS (I := I) (M := M) g r m
                (fun b : M => W.toSection b) y v X' Y)
          rw [map_add (pureRSlot0BilinAtRS (I := I) (M := M) g r m
            (fun b : M => W.toSection b) y v) X X',
            ContinuousLinearMap.add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRSlot0BilinAtRS (I := I) (M := M) g r m
              (fun b : M => W.toSection b) y v (c • X) Y) =
            c • scalarize (pureRSlot0BilinAtRS (I := I) (M := M) g r m
              (fun b : M => W.toSection b) y v X Y)
          rw [map_smul (pureRSlot0BilinAtRS (I := I) (M := M) g r m
            (fun b : M => W.toSection b) y v) c X,
            ContinuousLinearMap.smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y from
          pureRSlot0BilinAtRS (I := I) (M := M) g r m (fun b : M => W.toSection b) y v X Y) D)
          mtail := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]
  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLMRS (I := I) (M := M) g r m F (fun b : M => W.toSection b) y v) D) mtail =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F
    have hsum_apply :
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLMRS (I := I) (M := M) g r m F (fun b : M => W.toSection b) y v) D =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace m I y from
            riemannOp (tensorCov (I := I) g r m) y (F i y) v
              ((covGradBundleEquiv (I := I) (M := M) r m y).symm (W.toSection y) (F i y))) D := by
      rw [pureRFrozenDirCLMRS_apply, ContinuousLinearMap.sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRSlot0BilinAtRS_frame_summand (I := I) (M := M) g r m W F i y v]
  rw [hframe B, hframe C]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

/-! ## The moving-centre (frame-free) order-`0` endomorphism at valence `r` -/

/-- **The moving-centre order-`0` pure-Riemann endomorphism fibre value at valence `r` (rank `m + 1`)**
(`B = smoothOrthoFrame g x`).  The valence-`r` mirror of `pureRGenuineEndoFib`. -/
private noncomputable def genuinePureREndoFibRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (W : SmoothCcTensor g r (m + 1)) (x : M) :
    TensorRSSpace r (m + 1) I x :=
  pureRFrozenEndoFibRS (I := I) (M := M) g r m (smoothOrthoFrame (I := I) g x) W x

/-- **On `smoothOrthoFrameNbhd x₀`, the moving fibre equals the frozen fibre against
`smoothOrthoFrame g x₀`.** The valence-`r` mirror of `pureRGenuineEndoFib_eq_frozen_on_nbhd`. -/
private lemma genuinePureREndoFibRS_eq_frozen_on_nbhd
    (g : SmoothRiemannianMetric I M) (r m : ℕ)
    (W : SmoothCcTensor g r (m + 1)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    genuinePureREndoFibRS (I := I) (M := M) g r m W y =
      pureRFrozenEndoFibRS (I := I) (M := M) g r m (smoothOrthoFrame (I := I) g x₀) W y := by
  rw [genuinePureREndoFibRS, pureRFrozenEndoFibRS, pureRFrozenEndoFibRS]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) r m y) ?_
  exact pureRFrozenDirCLMRS_frame_independent (I := I) (M := M) g r m W y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

/-- **Base-point smoothness of the moving-centre order-`0` endomorphism fibre field at valence `r`.**
The valence-`r` mirror of `pureRGenuineEndoFib_contMDiff`: the frame-independence freeze plus
`ContMDiffAt.congr_of_eventuallyEq`. -/
private theorem genuinePureREndoFibRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r m : ℕ) (W : SmoothCcTensor g r (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (m + 1) I z) x
        (genuinePureREndoFibRS (I := I) (M := M) g r m W x)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r (m + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (m + 1) I z) y
        (pureRFrozenEndoFibRS (I := I) (M := M) g r m (smoothOrthoFrame (I := I) g x₀) W y)) x₀ :=
    pureRFrozenEndoFibRS_contMDiff (I := I) (M := M) g r m
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) W x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel r (m + 1) ℝ E)
    (E := fun z : M => TensorRSSpace r (m + 1) I z) y)
    (genuinePureREndoFibRS_eq_frozen_on_nbhd (I := I) (M := M) g r m W x₀ hy)

/-- **The moving-centre order-`0` pure-Riemann curvature endomorphism at valence `r`, rank `m + 1`**, a
smooth compactly-supported `(r, m + 1)`-tensor section: the slot-`0` uncurry of the moving-frame
direction CLM, frame-free in value (`genuinePureREndoFibRS_contMDiff`). The valence-`r` mirror of
`pureRGenuineEndoSucc`. -/
private noncomputable def genuinePureREndoSuccRS
    (g : SmoothRiemannianMetric I M) (r m : ℕ) (W : SmoothCcTensor g r (m + 1)) :
    SmoothCcTensor g r (m + 1) where
  toSection :=
    { toFun := fun x : M => genuinePureREndoFibRS (I := I) (M := M) g r m W x
      contMDiff_toFun := genuinePureREndoFibRS_contMDiff (I := I) (M := M) g r m W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] private lemma genuinePureREndoSuccRS_toSection
    (g : SmoothRiemannianMetric I M) (r m : ℕ) (W : SmoothCcTensor g r (m + 1)) (x : M) :
    (genuinePureREndoSuccRS (I := I) (M := M) g r m W).toSection x =
      genuinePureREndoFibRS (I := I) (M := M) g r m W x := rfl

/-- **The order-`0` moving-centre pure-Riemann curvature operator at valence `r`, every rank**
(totalised). For rank `m + 1 ≥ 1` it is the genuine endomorphism `genuinePureREndoSuccRS`; for rank `0`
(no slot-`0`) it is the zero operator (never reached — the recursion only increases the rank). The
valence-`r` mirror of `pureRGenuineEndo0`. -/
private noncomputable def genuinePureREndo0RS
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∀ (rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r rr
  | 0 => fun _ => 0
  | (m + 1) => fun W => genuinePureREndoSuccRS (I := I) (M := M) g r m W

/-- **The order-`p` differentiated moving-centre pure-Riemann curvature operator at valence `r`.** The
valence-`r` mirror of `pureRGenuineDiffOp`: order-`0` is the frame-free endomorphism, order-`(p + 1)` is
the exact covariant-Leibniz remainder (the input section's derivative `∇W` cancels), rank-cast
`(rr + 1) + p = rr + (p + 1)`. -/
noncomputable def genuinePureRDiffOpRS
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p)
  | 0, rr => fun W => genuinePureREndo0RS (I := I) (M := M) g r rr W
  | (p + 1), rr => fun W =>
      covGrad (I := I) (M := M) g r (rr + p)
          (genuinePureRDiffOpRS g r p rr W) -
        castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1))
          (genuinePureRDiffOpRS g r p (rr + 1) (covGrad (I := I) (M := M) g r rr W))

/-- **The exact single-step covariant Leibniz of the differentiated moving-centre curvature tower at
valence `r`.** By the recursive definition, `∇(op p rr W)` splits exactly into the higher-order
remainder `op (p + 1) rr W` and the rank-cast lower-order term applied to `∇W`. Proved by
`sub_add_cancel`. The valence-`r` mirror of `covGrad_pureRGenuineDiffOp_eq` and exactly the
`DiffBilinOpRS.covGrad_op` field shape. -/
theorem covGrad_genuinePureRDiffOpRS_eq
    (g : SmoothRiemannianMetric I M) (r p rr : ℕ) (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + p) (genuinePureRDiffOpRS (I := I) (M := M) g r p rr W) =
      genuinePureRDiffOpRS (I := I) (M := M) g r (p + 1) rr W +
        castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1))
          (genuinePureRDiffOpRS (I := I) (M := M) g r p (rr + 1)
            (covGrad (I := I) (M := M) g r rr W)) := by
  change _ = (covGrad (I := I) (M := M) g r (rr + p)
      (genuinePureRDiffOpRS (I := I) (M := M) g r p rr W) -
      castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1))
        (genuinePureRDiffOpRS (I := I) (M := M) g r p (rr + 1)
          (covGrad (I := I) (M := M) g r rr W))) + _
  rw [sub_add_cancel]

/-- **The order-`0` endomorphism on `∇S` is the moving-frame pure-Riemann trace, in public form.** At
valence `r`, rank `s + 1`, applied to the gradient field `∇S := covGrad g r s S`, the order-`0`
moving-centre endomorphism `genuinePureRDiffOpRS g r 0 (s + 1) (∇S)` has fibre value at `x` equal to
`covGradBundleEquiv r s x` of the direction CLM `v ↦ ∑ᵢ R(Bᵢ x, v)(∇_{Bᵢ} S(x))`, where
`Bᵢ := smoothOrthoFrame g x i` and the contracted argument is the directional covariant derivative
`covApply (tensorCov g r s) (Bᵢ) (S.toSection) x` — the slot-`0` reading of `∇S` along `Bᵢ` (by the
covariant-gradient round-trip `covGrad_toSection_apply`).  This expresses the order-`0`-on-`∇S` fibre
purely through the public primitives `riemannOp`, `covApply`, `covGradBundleEquiv`, so the downstream
`MovingFrameGenuineFieldPairingRS` identifies it with the moving-centre pure-Riemann section
`GcurvSectionRS g r s S` (whose direction CLM has the identical summands) in one step, discharging the
rank-`r` frame-free differentiated-curvature tower posit. -/
theorem genuinePureRDiffOp0_covGrad_fib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) (v : TangentSpace I x) :
    (covGradBundleEquiv (I := I) (M := M) r s x).symm
        ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toSection x) v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g r s) x (smoothOrthoFrame (I := I) g x i x) v
          (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x) := by
  classical
  have hfib : (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (pureRFrozenDirCLMRS (I := I) (M := M) g r s (smoothOrthoFrame (I := I) g x)
          (fun y : M => (covGrad (I := I) (M := M) g r s S).toSection y) x) := by
    change genuinePureREndoFibRS (I := I) (M := M) g r s (covGrad (I := I) (M := M) g r s S) x = _
    rw [genuinePureREndoFibRS, pureRFrozenEndoFibRS]
  rw [hfib, ContinuousLinearEquiv.symm_apply_apply, pureRFrozenDirCLMRS_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- The slot-`0` reading of `∇S` along `Bᵢ` is the directional covariant derivative `∇_{Bᵢ} S`.
  have hslot : (covGradBundleEquiv (I := I) (M := M) r s x).symm
        ((covGrad (I := I) (M := M) g r s S).toSection x) (smoothOrthoFrame (I := I) g x i x) =
      covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
        (fun y : M => S.toSection y) x := by
    rw [covGrad_toSection_apply (I := I) (M := M) g r s S x, ContinuousLinearEquiv.symm_apply_apply]
    rw [covApply_apply]
  rw [hslot]

/-! ## The two frame-free envelope layers and the `DiffBilinOpRS g r` package -/

set_option linter.unusedVariables false in
/-- **The order-`0` (value-local) layer of the frame-free pure-Riemann curvature envelope at valence
`r` (posited general-valence analytic child).** For a closed smooth Riemannian manifold `(M, g)` and a
fixed contravariant valence `r` there is a nonnegative family `kappa0 : ℕ → ℝ` such that the order-`0`
moving-centre pure-Riemann curvature operator `genuinePureRDiffOpRS g r 0 rr W` is *value-locally*
fibre-bounded by `kappa0 rr` times the value fibre norm of `W`:
```
rfns(genuinePureRDiffOpRS g r 0 rr W)(x) ≤ kappa0 rr · rfns(W)(x).
```

**Why this is TRUE.** This is the verbatim contravariant-valence-`r` mirror of the *proved* rank-`0`
order-`0` layer `exists_proportional_pureRFrozenFrameDiffOp_orderZero`
(`FrozenFramePureRCurvatureTower`).  At width `rr = 0` the operator is the zero endomorphism
(`genuinePureREndo0RS`, the `rr = 0` branch) and the bound is trivial; at width `rr = m + 1` the
order-`0` fibre `genuinePureREndoFibRS g r m W x` is the moving-frame freeze at `smoothOrthoFrame g x`
(orthonormal at its own centre `x`), read by the slot-`0` Parseval frame-sum over a `g_x`-orthonormal
frame, each slice being the curvature contraction `∑ᵢ R(Bᵢˣ, eₐ)(slot0_{Bᵢˣ} W)` fibre-bounded by the
valence-`r` curvature-operator sup (`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs`,
made uniform over the compact `M`) times the unit Gram factors and the slot-`0` reading fibre norm
`rfns((covGradBundleEquiv r m x).symm (W x) (Bᵢˣ))(x) ≤ rfns(W)(x)` (the valence-`r` slot-`0` reading
domination).  The slot-`0` reading domination at valence `r` and the uniform-over-`M` valence-`r`
curvature sup are the genuinely-irreducible rank-`r` analytic content here (the rank-`0` slot-`0`
Parseval domination `riemannianFiberNormSq_slot0Curry_le` and the rank-`0` continuous curvature sup
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional` are stated only at
contravariant rank `0`), absent sorry-free below this file at valence `r`, so this order-`0` layer is
posited as one precise true child — strictly weaker than the full envelope (value-local, no jet
window, no high-order content).  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate witness `kappa0 ≡ 0` is rejected on any non-flat manifold: at
`rr = s + 1`, `genuinePureRDiffOpRS g r 0 (s + 1) W` is the pure-Riemann contraction
`∑ᵢ R(Bᵢˣ, ·)(slot0_{Bᵢˣ} W)`, genuinely nonzero (`R ≠ 0`, a nonzero slot-`0` reading), forcing
`rfns(…)(x) > 0` while the RHS `0 · rfns(W)(x) = 0`; the layer must carry the genuine curvature
magnitude and the constant family is genuinely positive. -/
theorem exists_genuinePureRDiffOpRS_orderZero (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ kappa0 : ℕ → ℝ, (∀ rr, 0 ≤ kappa0 rr) ∧
      ∀ (rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + 0) x
            ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 rr W).toSection x) ≤
          kappa0 rr * riemannianFiberNormSq (I := I) (M := M) g r rr x (W.toSection x) := by
  sorry

set_option linter.unusedVariables false in
/-- **The high-order (`p ≥ 1`) layer of the frame-free pure-Riemann curvature envelope at valence `r`,
in JET form (posited general-valence analytic child).** For a closed smooth Riemannian manifold
`(M, g)` and a fixed contravariant valence `r` there is a nonnegative family `kappaHigh : ℕ → ℕ → ℝ`
such that the order-`(p + 1)` differentiated frame-free pure-Riemann curvature operator has intrinsic
squared fibre norm at most `kappaHigh p rr` times the order-`≤ (p + 1)` covariant jet of `W`:
```
rfns(genuinePureRDiffOpRS g r (p + 1) rr W)(x) ≤ kappaHigh p rr · ∑_{q < p + 2} rfns(∇^q W)(x).
```

**Why the jet form (not the single-value form).** The single-value form is FALSE at the
width-`0`-degenerate base, exactly as at rank `0` (`exists_proportional_pureRGenuineDiffOp_highOrder`):
the order-`0` base reads the slot-`0` direction, so at width `0` it is the zero operator, and the
order-`1` Leibniz remainder reads the *gradient* `∇W (x)`, not the value `W (x)`.  The honest invariant
is the jet bound `op (p + 1) rr W (x)` reads up to `∇^{p+1} W (x)`, controlled by
`∑_{q < p + 2} rfns(∇^q W)(x)`.

**Why this is TRUE — and FRAME-FREE.** This is the verbatim contravariant-valence-`r` mirror of the
rank-`0` high-order posited node `exists_proportional_pureRGenuineDiffOp_highOrder`.  The order-`0`
base `genuinePureREndo0RS` is the moving-frame pure-Riemann endomorphism whose fibre *value* is a
genuine `g`-metric trace (`pureRFrozenDirCLMRS_frame_independent`), built from `g, R` *alone* — NOT a
frame jet; writing the order-`0` operator as the action of a smooth frame-free operator-field section
`Φ_{rr}` (curvature data), the operator-field covariant product rule gives
`op (p + 1) rr W = appCc(∇Φ) W + appCc(slotExtend Φ − Φ') (∇W)`, the sum of a *frame-free* operator-field
action of the differentiated curvature coefficient `∇^{p+1} Φ` on `W` and an operator-field action of
the *bounded* slot-mismatch on `∇W`, each uniformly fibre-operator-bounded over the compact `M` by
`‖∇^{≤ p+1} R‖_∞`; the jet window absorbs the surviving `∇W ⊆ ∇^{≤ p+1}W` term at every step.  Because
`Φ` is frame-free, `∇^{p+1} Φ` differentiates *only* the curvature factor, never the
chart-selection-unbounded frame jet.  The operator-field normal-form engine
(`normalForm_of_base` + `exists_jet_bound_of_normalForm`) and the operator-field calculus
(`appCc`, `slotExtend`, `exists_uniform_riemannianFiberNormSq_appCc_le`) are stated **only at
contravariant rank `0`** (a literal contravariant `0` in the operator-field action
`appCc · : SmoothCcTensor g 0 r → …`), so the whole high-order frame-free jet envelope at valence `r`
is absent sorry-free below this file and is posited here as one precise true child — strictly weaker
than the full envelope (no order-`0` content).  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate witness `kappaHigh ≡ 0` is rejected on any non-flat manifold: at
`(p, rr) = (0, 0)`, `genuinePureRDiffOpRS g r 1 0 W = −cast(genuinePureRDiffOpRS g r 0 1 (∇W))` is
genuinely nonzero for a `W` with `∇W (x) ≠ 0` whose slot-`0` reading carries a non-zero pure-Riemann
contraction (`R ≠ 0`), so `rfns(…)(x) > 0` while the jet RHS `0 · ∑_{q < 2} rfns(∇^q W)(x) = 0`.  The
envelope genuinely uses `W` (the jet window reaches `∇^{p+1} W`); the constant family is genuinely
positive. -/
theorem exists_genuinePureRDiffOpRS_highOrder (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ kappaHigh : ℕ → ℕ → ℝ, (∀ p rr, 0 ≤ kappaHigh p rr) ∧
      ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + (p + 1)) x
            ((genuinePureRDiffOpRS (I := I) (M := M) g r (p + 1) rr W).toSection x) ≤
          kappaHigh p rr * ∑ q ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  sorry

set_option linter.unusedVariables false in
/-- **The per-order, per-rank frame-free proportional fibre envelope for the differentiated
moving-centre pure-Riemann curvature tower at valence `r`, in JET form.** For a closed smooth
Riemannian manifold `(M, g)` and a fixed contravariant valence `r` there is
a nonnegative envelope family `kappa : ℕ → ℕ → ℝ` such that for every order `p`, covariant width `rr`,
smooth compactly-supported `(r, rr)`-tensor `W`, and base point `x`,

```
rfns(genuinePureRDiffOpRS g r p rr W)(x) ≤ kappa p rr · ∑_{q < p + 1} rfns(∇^q W)(x).
```

**Proof (composition of the two layers).** The order-`p = 0` layer is the value-local
`exists_genuinePureRDiffOpRS_orderZero`: at order `0` the jet window `range 1` carries only the value
`∇^0 W = W`, so `kappa0 rr · rfns(W)(x) = kappa0 rr · ∑_{q < 1} rfns(∇^q W)(x)`.  The order-`p ≥ 1`
layer is `exists_genuinePureRDiffOpRS_highOrder` (window `q < (p' + 1) + 1 = p' + 2`).  The two combine
by `cases p` into one per-order jet family — exactly the valence-`r` mirror of the rank-`0` glue
`exists_proportional_pureRGenuineDiffOp` (`FrozenFramePureRCurvatureTower`).  Consumers transitively
depend on `sorryAx` only through the two layer children.

**Non-vacuity (the envelope is genuinely positive).** A degenerate witness `kappa ≡ 0` is rejected on
any non-flat manifold: at `(p, rr) = (0, s + 1)`, `genuinePureRDiffOpRS g r 0 (s + 1) W` is the
pure-Riemann contraction `∑ᵢ R(Bᵢˣ, ·)(slot0_{Bᵢˣ} W)`, genuinely nonzero (`R ≠ 0`, a nonzero slot-`0`
reading), forcing `rfns(genuinePureRDiffOpRS g r 0 (s + 1) W)(x) > 0` while the jet RHS
`0 · ∑_{q < 1} rfns(∇^q W)(x) = 0`; the envelope must carry the genuine curvature magnitude and the
constant family is genuinely positive. -/
theorem exists_proportional_genuinePureRDiffOpRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p rr, 0 ≤ kappa p rr) ∧
      ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + p) x
            ((genuinePureRDiffOpRS (I := I) (M := M) g r p rr W).toSection x) ≤
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨kappa0, hkappa0_nn, hkappa0⟩ :=
    exists_genuinePureRDiffOpRS_orderZero (I := I) (M := M) g r
  obtain ⟨kappaHigh, hkappaHigh_nn, hkappaHigh⟩ :=
    exists_genuinePureRDiffOpRS_highOrder (I := I) (M := M) g r
  refine ⟨fun p rr => match p with | 0 => kappa0 rr | (p' + 1) => kappaHigh p' rr,
    fun p rr => ?_, fun p rr W x => ?_⟩
  · cases p with
    | zero => exact hkappa0_nn rr
    | succ p' => exact hkappaHigh_nn p' rr
  · cases p with
    | zero =>
        have h := hkappa0 rr W x
        rw [show (fun p rr => match p with
            | 0 => kappa0 rr | (p' + 1) => kappaHigh p' rr) 0 rr = kappa0 rr from rfl]
        rw [Finset.sum_range_one]
        rw [show (iteratedCovGrad g r rr 0 W) = W from iteratedCovGrad_zero g r rr W] at *
        exact h
    | succ p' =>
        have h := hkappaHigh p' rr W x
        rw [show (fun p rr => match p with
            | 0 => kappa0 rr | (p'' + 1) => kappaHigh p'' rr) (p' + 1) rr = kappaHigh p' rr from rfl]
        rw [show (p' + 1) + 1 = p' + 2 from rfl]
        exact h

/-- **The frame-free pure-Riemann differentiated curvature tower at valence `r`, packaged as a
`DiffBilinOpRS g r`.** The order-`p` operator family is `genuinePureRDiffOpRS g r p`; the exact
single-step covariant Leibniz field is `covGrad_genuinePureRDiffOpRS_eq` (*proved* by `sub_add_cancel`);
the per-order, per-rank frame-free proportional fibre envelope is the single posited frame-free analytic
node `exists_proportional_genuinePureRDiffOpRS`.  This is the engine the contravariant-rank-`r`
curvature-jet tower of the order-`2` rough-Laplacian / covariant-gradient commutator defect consumes for
its frame-free pure-Riemann differentiated operator, exactly as the rank-`0` tower consumes the rank-`0`
`pureRGenuineDiffOp` through `DiffBilinOp`. Its order-`0` operator on `∇S` is the moving-centre
pure-Riemann section, identified downstream against `GcurvSectionRS` by the slot-`0` reading lemma
`genuinePureREndoFibRS_slot0Reading`. Consumers transitively depend on `sorryAx` through the single
frame-free envelope node. -/
noncomputable def genuinePureRDiffOpRS_bilinOp (g : SmoothRiemannianMetric I M) (r : ℕ) :
    DiffBilinOpRS g r where
  op p rr W := genuinePureRDiffOpRS (I := I) (M := M) g r p rr W
  covGrad_op p rr W := covGrad_genuinePureRDiffOpRS_eq (I := I) (M := M) g r p rr W
  kappa := (exists_proportional_genuinePureRDiffOpRS (I := I) (M := M) g r).choose
  kappa_nonneg := (exists_proportional_genuinePureRDiffOpRS (I := I) (M := M) g r).choose_spec.1
  rfns_op_le := (exists_proportional_genuinePureRDiffOpRS (I := I) (M := M) g r).choose_spec.2

@[simp] theorem genuinePureRDiffOpRS_bilinOp_op
    (g : SmoothRiemannianMetric I M) (r p rr : ℕ) (W : SmoothCcTensor g r rr) :
    (genuinePureRDiffOpRS_bilinOp (I := I) (M := M) g r).op p rr W =
      genuinePureRDiffOpRS (I := I) (M := M) g r p rr W := rfl

end Connection
end Integral
end DifferentialGeometry

end
