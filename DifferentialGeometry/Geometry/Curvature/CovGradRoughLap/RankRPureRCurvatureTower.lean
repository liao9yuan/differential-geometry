import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffBilinGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairing
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RankRReadingDominationUniformSup
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RankRUniformProportionalCurvatureSup

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

/-- **The forward-uncurry frame component is the slot-`0`-shifted per-direction component.** For a
frame `e`, the `(K, J)` frame component of the slot-`0` uncurry `covGradBundleEquiv r s x Φ` — an
`(r, s + 1)`-tensor — at a `Fin (s + 1)`-index `J` equals the `(K, Matrix.vecTail J)` frame component
of the per-direction value `Φ (e (J 0))` — an `(r, s)`-tensor.  This is the forward mirror of
`reading_fiberNormSqComponent_eq` (`RankRReadingDominationUniformSup`): through the rank-generic
forward evaluation bridge `covGradBundleEquiv_apply_eval`, the leftmost slot reads the tangent
direction `e (J 0)` and the remaining slots read `e ∘ Matrix.vecTail J`. -/
private lemma forward_fiberNormSqComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin (s + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r (s + 1)
        (covGradBundleEquiv (I := I) (M := M) r s x Φ) n e K J =
      fiberNormSqComponent (I := I) (M := M) g x r s (Φ (e (J 0))) n e K (Matrix.vecTail J) := by
  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace r I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K k))) with hωK
  rw [show ((covGradBundleEquiv (I := I) (M := M) r s x Φ) ωK (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) r s x Φ) ωK) (fun k => e (J k)) from rfl]
  rw [show (((Φ (e (J 0))) ωK) (fun k => e (Matrix.vecTail J k)) : ℝ) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ (e (J 0))) ωK)
        (fun k => e (Matrix.vecTail J k)) from rfl]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r s x Φ ωK (fun k => e (J k))]
  congr 1

/-- **Frame-summed forward-uncurry fibre bound for a covariant-gradient bundle image at valence `r`
(posited general-valence Parseval child).** If every per-direction value `Φ v` of a curvature-direction
continuous-linear map `Φ : T_x M →L T^{(r,s)}_x` along a *unit* tangent direction (`g(v, v) = 1`) has
intrinsic fibre norm bounded by a single nonnegative `b`, then the fibre norm of the slot-`0` uncurry
`covGradBundleEquiv r s x Φ` is bounded by `finrank ℝ E · b`:
```
rfns(covGradBundleEquiv r s x Φ)(x) ≤ (finrank ℝ E) · b.
```

**Why this is TRUE.** This is the verbatim contravariant-valence-`r` mirror of the *proved*
contravariant-`0` `riemannianFiberNormSq_covGradBundleEquiv_le_card_mul`
(`CovGradBundleEquivFiberNormFrameSum`), whose home this lemma belongs to.  Its proof is the
forward-uncurry rank-`(r, s + 1)` Parseval frame-sum
`rfns(covGradBundleEquiv r s x Φ)(x) = ∑ₐ rfns(Φ (eₐ))(x)` over a `g_x`-orthonormal frame
`e := stdOrthonormalBasis`, dominated termwise by `b` because each `eₐ` is a unit direction; the
contravariant-`0` version routes that frame-sum through the slot-`0` curry chain
(`riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame`, hard-locked to contravariant `0` through
`slot0Curry`).  The valence-`r` forward Parseval frame-sum is the rank-generic analogue, proved through
the rank-generic component Parseval `rfns_rs_eq_sum_fiberNormSqComponent_sq_of_basis`
(`RankRReadingDominationUniformSup`) and the forward evaluation bridge `covGradBundleEquiv_apply_eval`,
absent sorry-free at valence `r`, so this forward-uncurry bound is posited here as one precise true
child.  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate `b < 0` is rejected: the conclusion `rfns(…) ≤ finrank · b` forces
`finrank · b ≥ 0` (the LHS is a nonnegative fibre norm and `finrank ℝ E > 0` by `NeZero`), so the
constant must be genuinely nonnegative; and on a nonzero `Φ` (a unit-direction value with positive
fibre norm) the smallest valid `b` is genuinely positive. -/
theorem riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x) (b : ℝ)
    (hbound : ∀ v : TangentSpace I x, g.inner x v v = 1 →
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ v) ≤ b) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        (covGradBundleEquiv (I := I) (M := M) r s x Φ) ≤
      (Module.finrank ℝ E : ℝ) * b := by
  classical
  -- Build the `stdOrthonormalBasis` frame on `TangentSpace I x` and its δ-form Gram.
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  set e : Fin n → TangentSpace I x := fun i => eob i with he_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have horthb : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horthb i j
    rw [he_def, ← hinner_eq (eob i) (eob j)]
    exact hite
  -- The rank-`(r, s)` and rank-`(r, s + 1)` fibre norms unfold to the frame-component sum by `rfl`.
  have hreprS : ∀ S : TensorRSSpace r s I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x S =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s S n e K J := by
    intro S; rfl
  have hreprSucc : ∀ S : TensorRSSpace r (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x S =
        ∑ K : Fin r → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r (s + 1) S n e K J := by
    intro S; rfl
  -- Parseval-expand the `(r, s + 1)` fibre norm of the slot-`0` uncurry in the frame `e`.
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x r (s + 1) e hreprSucc]
  -- Rewrite each forward component as a slot-`0`-shifted per-direction component.
  have hforward : ∀ K : Fin r → Fin n, ∀ J : Fin (s + 1) → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x r (s + 1)
          (covGradBundleEquiv (I := I) (M := M) r s x Φ) n e K J) ^ 2 =
        (fiberNormSqComponent (I := I) (M := M) g x r s (Φ (e (J 0))) n e K
          (Matrix.vecTail J)) ^ 2 := by
    intro K J
    rw [forward_fiberNormSqComponent_eq (I := I) (M := M) g r s x Φ e K J]
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hforward K J))]
  -- Reindex `J : Fin (s + 1) → Fin n` as `(a, J') ↦ Fin.cons a J'` (`J 0 = a`, tail = `J'`).
  have hreindex : ∀ K : Fin r → Fin n,
      (∑ J : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s (Φ (e (J 0))) n e K
          (Matrix.vecTail J)) ^ 2) =
      ∑ a : Fin n, ∑ J' : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s (Φ (e a)) n e K J') ^ 2 := by
    intro K
    rw [← (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n)).sum_comp
      (fun J => (fiberNormSqComponent (I := I) (M := M) g x r s (Φ (e (J 0))) n e K
        (Matrix.vecTail J)) ^ 2)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun J' _ => ?_))
    simp only [Fin.consEquiv_apply, Fin.cons_zero]
    rfl
  rw [Finset.sum_congr rfl (fun K _ => hreindex K)]
  -- Swap the `∑_K ∑_a` order to collect, per direction `a`, the full `(r, s)` Parseval sum.
  rw [Finset.sum_comm]
  -- Each per-direction inner sum is exactly `rfns (Φ (e a))`; bound it by `b` (unit direction).
  have hper : ∀ a : Fin n,
      (∑ K : Fin r → Fin n, ∑ J' : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s (Φ (e a)) n e K J') ^ 2) ≤ b := by
    intro a
    rw [← riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x r s e hreprS]
    refine hbound (e a) ?_
    have := horth a a; rwa [if_pos rfl] at this
  refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfr : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  rw [hn_def, hfr]

/-- Local model `NormedSpace`/`FiniteDimensional` instances (the bundle-level instances are
noncomputable; reproduced from `RankRUniformProportionalCurvatureSup`). -/
private instance tensor0SModelNormedSpace_rrct {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

private instance tensorRSModelNormedSpace_rrct {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) := by
  unfold TensorRSModel
  infer_instance

/-- **Per-point single dual-frame curvature-term bound at valence `(r, s)`.** For a `g`-orthonormal
frame `e` (`horth`) and the Levi-Civita base-curvature `g`-norm bound `Kbase` (CHILD), the intrinsic
fibre norm squared of one dual-frame curvature term at valence `(r, s)` is bounded by
`(finrank E)^(r + s) · ((r + s) · √Kbase)²`. Each Parseval component (read off the internal
`g`-orthonormal frame) is the unit-evaluation of the `(r, s)` curvature on the dual frame, split by
`riemannOp_tensorCovRS_apply_eval` into a covariant `(0, s)` branch on the `g`-coframe and a
contravariant `(0, r)` branch on the `g`-coframe, each bounded by `abs_toModel_riemannOp_tensor0SCov_`
`coframeS_le`. -/
private lemma riemannianFiberNormSq_riemannOp_tensorCovRS_dualTensorFrameRS_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (i j : Fin n)
    (K : Fin r → Fin n) (J : Fin s → Fin n)
    (Kbase : ℝ) (hKbase : 0 ≤ Kbase)
    (hKb : ∀ (a b c : TangentSpace I x),
      g.inner x (riemannOp (cov := LeviCivita (I := I) g) x a b c)
          (riemannOp (cov := LeviCivita (I := I) g) x a b c) ≤
        Kbase * g.inner x a a * g.inner x b b * g.inner x c c)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
          (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) ≤
      (Module.finrank ℝ E : ℝ) ^ (r + s) * (((r + s : ℕ) : ℝ) * Real.sqrt Kbase) ^ 2 := by
  classical
  have hii : g.inner x (e i) (e i) ≤ 1 := by rw [horth i i, if_pos rfl]
  have hjj : g.inner x (e j) (e j) ≤ 1 := by rw [horth j j, if_pos rfl]
  -- Build the internal `g`-orthonormal frame `eb` of `riemannianFiberNormSq`.
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun z : TangentSpace I x => cd.inner z z) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {z : TangentSpace I x |
      RCLike.re (cd.inner z z) < 1} := g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set nb : ℕ := Module.finrank ℝ (TangentSpace I x) with hnb_def
  set eob : OrthonormalBasis (Fin nb) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with heob_def
  set eb : Fin nb → TangentSpace I x := fun a => eob a with heb_def
  have hinner_eq : ∀ a b : TangentSpace I x, (inner ℝ a b : ℝ) = g.inner x a b := fun _ _ => rfl
  have hnbE : nb = Module.finrank ℝ E := rfl
  have hnorm_sq : ∀ a : TangentSpace I x, ‖a‖ ^ 2 = g.inner x a a := by
    intro a; rw [← hinner_eq a a]; exact (real_inner_self_eq_norm_sq a).symm
  have horthb : ∀ a b : Fin nb, g.inner x (eb a) (eb b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp eob.orthonormal a b
    rw [← hinner_eq (eb a) (eb b)]; exact hite
  have hreprT : ∀ S : TensorRSSpace r s I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x S =
        ∑ K : Fin r → Fin nb, ∑ Jp : Fin s → Fin nb,
          fiberNormSqSummand (I := I) (M := M) g x r s S nb eb K Jp := fun S => rfl
  -- `e`-frame and `eb`-frame are `g`-unit.
  have he_unit : ∀ a : Fin n, ‖e a‖ ≤ 1 := by
    intro a
    have h1 : ‖e a‖ ^ 2 = 1 := by rw [hnorm_sq (e a), horth a a, if_pos rfl]
    nlinarith [norm_nonneg (e a), h1]
  have heb_unit : ∀ a : Fin nb, ‖eb a‖ ≤ 1 := by
    intro a
    have h1 : ‖eb a‖ ^ 2 = 1 := by rw [hnorm_sq (eb a), horthb a a, if_pos rfl]
    nlinarith [norm_nonneg (eb a), h1]
  set V : TensorRSSpace r s I x :=
    riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
      (dualTensorFrameRS (I := I) (M := M) g x r s e K J) with hV_def
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x r s eb hreprT V]
  -- Per-component split via `riemannOp_tensorCovRS_apply_eval`.
  have hsplit : ∀ (K' : Fin r → Fin nb) (J' : Fin s → Fin nb),
      fiberNormSqComponent (I := I) (M := M) g x r s V nb eb K' J' =
        Tensor0SSpace.toModel
            (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
                  dualTensorFrameRS (I := I) (M := M) g x r s e K J)
                (coframeS (I := I) (M := M) g x r eb K')))
            (fun k => eb (J' k)) -
          Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
                dualTensorFrameRS (I := I) (M := M) g x r s e K J)
              (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x (e i) (e j)
                (coframeS (I := I) (M := M) g x r eb K')))
            (fun k => eb (J' k)) := by
    intro K' J'
    rw [hV_def]
    rw [show fiberNormSqComponent (I := I) (M := M) g x r s
          (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
            (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) nb eb K' J' =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
              riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
                (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
            (coframeS (I := I) (M := M) g x r eb K')) (fun k => eb (J' k)) from rfl]
    exact riemannOp_tensorCovRS_apply_eval (I := I) (M := M) g r s x (e i) (e j)
      (dualTensorFrameRS (I := I) (M := M) g x r s e K J)
      (coframeS (I := I) (M := M) g x r eb K') (fun k => eb (J' k))
  -- Each component is bounded in absolute value by `(r + s) · √Kbase`.
  have hcomp_bnd : ∀ (K' : Fin r → Fin nb) (J' : Fin s → Fin nb),
      |fiberNormSqComponent (I := I) (M := M) g x r s V nb eb K' J'| ≤
        ((r + s : ℕ) : ℝ) * Real.sqrt Kbase := by
    intro K' J'
    rw [hsplit K' J']
    -- Covariant branch: `D(coframeS_r eb K') = scalar_cov • coframeS_s e J`.
    set scov : ℝ := tensorEvalAtFrame (I := I) (M := M) x r e K
      (coframeS (I := I) (M := M) g x r eb K') with hscov_def
    have hcovbr :
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            dualTensorFrameRS (I := I) (M := M) g x r s e K J)
          (coframeS (I := I) (M := M) g x r eb K') =
          scov • coframeS (I := I) (M := M) g x s e J := by
      rw [dualTensorFrameRS_apply (I := I) (M := M) g x r s e K J
        (coframeS (I := I) (M := M) g x r eb K')]
    have hcov_eval :
        Tensor0SSpace.toModel
            (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
                  dualTensorFrameRS (I := I) (M := M) g x r s e K J)
                (coframeS (I := I) (M := M) g x r eb K')))
            (fun k => eb (J' k)) =
          scov * Tensor0SSpace.toModel
            (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
              (coframeS (I := I) (M := M) g x s e J)) (fun k => eb (J' k)) := by
      rw [hcovbr, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    -- |scov| ≤ 1.
    have hscov_le : |scov| ≤ 1 := by
      rw [hscov_def, tensorEvalAtFrame_apply (I := I) (M := M) x r e K,
        coframeS_apply (I := I) (M := M) g x r eb K' (fun k => e (K k))]
      rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun k _ => abs_nonneg _) (fun k _ => ?_)
      rw [← hinner_eq (eb (K' k)) (e (K k))]
      refine le_trans (abs_real_inner_le_norm (eb (K' k)) (e (K k))) ?_
      calc ‖eb (K' k)‖ * ‖e (K k)‖ ≤ 1 * 1 :=
            mul_le_mul (heb_unit (K' k)) (he_unit (K k)) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    -- Contravariant branch: `D(R^{(0,r)} coframeS_r eb K') = scon • coframeS_s e J`.
    set scon : ℝ := tensorEvalAtFrame (I := I) (M := M) x r e K
      (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x (e i) (e j)
        (coframeS (I := I) (M := M) g x r eb K')) with hscon_def
    have hconbr :
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            dualTensorFrameRS (I := I) (M := M) g x r s e K J)
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x (e i) (e j)
            (coframeS (I := I) (M := M) g x r eb K')) =
          scon • coframeS (I := I) (M := M) g x s e J := by
      rw [dualTensorFrameRS_apply (I := I) (M := M) g x r s e K J _]
    have hcon_eval :
        Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
                dualTensorFrameRS (I := I) (M := M) g x r s e K J)
              (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x (e i) (e j)
                (coframeS (I := I) (M := M) g x r eb K')))
            (fun k => eb (J' k)) =
          scon * Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x s e J)
            (fun k => eb (J' k)) := by
      rw [hconbr, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    -- scon = toModel(R^{(0,r)}(coframeS_r eb K'))(e∘K); |scon| ≤ r·√Kbase.
    have hscon_eq : scon =
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x (e i) (e j)
            (coframeS (I := I) (M := M) g x r eb K')) (fun k => e (K k)) := by
      rw [hscon_def, tensorEvalAtFrame_apply (I := I) (M := M) x r e K]
      rfl
    have hscon_le : |scon| ≤ ((r : ℕ) : ℝ) * Real.sqrt Kbase := by
      rw [hscon_eq]
      exact abs_toModel_riemannOp_tensor0SCov_coframeS_le (I := I) (M := M) g r x (e i) (e j)
        eb K' (fun k => e (K k)) Kbase hKbase hKb hii hjj horthb
        (fun k => by rw [horth (K k) (K k), if_pos rfl])
    -- coframe-output factor of contravariant branch: |coframeS_s e J (eb∘J')| ≤ 1.
    have hcofo_le : |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x s e J)
        (fun k => eb (J' k))| ≤ 1 := by
      rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x s e J)
            (fun k => eb (J' k)) = coframeS (I := I) (M := M) g x s e J (fun k => eb (J' k)) from rfl,
        coframeS_apply (I := I) (M := M) g x s e J (fun k => eb (J' k))]
      rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun l _ => abs_nonneg _) (fun l _ => ?_)
      rw [← hinner_eq (e (J l)) (eb (J' l))]
      refine le_trans (abs_real_inner_le_norm (e (J l)) (eb (J' l))) ?_
      calc ‖e (J l)‖ * ‖eb (J' l)‖ ≤ 1 * 1 :=
            mul_le_mul (he_unit (J l)) (heb_unit (J' l)) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    -- covariant-curvature factor: |toModel(R^{(0,s)}(coframeS_s e J))(eb∘J')| ≤ s·√Kbase.
    have hcovc_le : |Tensor0SSpace.toModel
        (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
          (coframeS (I := I) (M := M) g x s e J)) (fun k => eb (J' k))| ≤
          ((s : ℕ) : ℝ) * Real.sqrt Kbase :=
      abs_toModel_riemannOp_tensor0SCov_coframeS_le (I := I) (M := M) g s x (e i) (e j)
        e J (fun k => eb (J' k)) Kbase hKbase hKb hii hjj horth
        (fun k => by rw [horthb (J' k) (J' k), if_pos rfl])
    rw [hcov_eval, hcon_eval]
    -- |scov · A − scon · B| ≤ |scov||A| + |scon||B| ≤ 1·s√K + r√K·1 = (r+s)√K.
    have hKsqrt_nn : 0 ≤ Real.sqrt Kbase := Real.sqrt_nonneg _
    calc |scov * Tensor0SSpace.toModel
              (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
                (coframeS (I := I) (M := M) g x s e J)) (fun k => eb (J' k)) -
            scon * Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x s e J)
              (fun k => eb (J' k))|
        ≤ |scov * Tensor0SSpace.toModel
              (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
                (coframeS (I := I) (M := M) g x s e J)) (fun k => eb (J' k))| +
            |scon * Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x s e J)
              (fun k => eb (J' k))| := abs_sub _ _
      _ = |scov| * |Tensor0SSpace.toModel
              (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x (e i) (e j)
                (coframeS (I := I) (M := M) g x s e J)) (fun k => eb (J' k))| +
            |scon| * |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x s e J)
              (fun k => eb (J' k))| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (((s : ℕ) : ℝ) * Real.sqrt Kbase) +
            (((r : ℕ) : ℝ) * Real.sqrt Kbase) * 1 := by
            refine add_le_add (mul_le_mul hscov_le hcovc_le (abs_nonneg _) zero_le_one)
              (mul_le_mul hscon_le hcofo_le (abs_nonneg _) ?_)
            exact mul_nonneg (by positivity) hKsqrt_nn
      _ = ((r + s : ℕ) : ℝ) * Real.sqrt Kbase := by push_cast; ring
  -- Sum the `nb^(r+s)` squared components, each ≤ ((r+s)√K)².
  calc (∑ K' : Fin r → Fin nb, ∑ J' : Fin s → Fin nb,
          (fiberNormSqComponent (I := I) (M := M) g x r s V nb eb K' J') ^ 2)
      ≤ ∑ _K' : Fin r → Fin nb, ∑ _J' : Fin s → Fin nb,
          (((r + s : ℕ) : ℝ) * Real.sqrt Kbase) ^ 2 := by
        refine Finset.sum_le_sum (fun K' _ => Finset.sum_le_sum (fun J' _ => ?_))
        have h := hcomp_bnd K' J'
        exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
    _ = (Module.finrank ℝ E : ℝ) ^ (r + s) * (((r + s : ℕ) : ℝ) * Real.sqrt Kbase) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_pi, Fintype.card_pi]
        simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, nsmul_eq_mul]
        rw [hnbE]
        push_cast
        ring

/-- **Uniform-over-`M` single dual-frame curvature-term bound at valence `(r, s)`.** A single
nonnegative constant `K`, independent of the base point, of the `g`-orthonormal frame `e`, and of the
frame indices, bounding one dual-frame curvature term — the valence-`(r, s)` mirror of
`exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound'`. The constant is
`(finrank E)^(r + s) · ((r + s) · √Kbase)²`, `Kbase` the uniform Levi-Civita base-curvature `g`-norm
bound from `exists_uniform_riemannOp_LeviCivita_gNorm_bound`. -/
private lemma exists_uniform_riemannOp_tensorCovRS_dualFrameEnergy_single_term
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∀ (i j : Fin n) (K' : Fin r → Fin n) (J : Fin s → Fin n),
          riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
              (dualTensorFrameRS (I := I) (M := M) g x r s e K' J)) ≤ K := by
  obtain ⟨Kbase, hKbase, hKb⟩ := exists_uniform_riemannOp_LeviCivita_gNorm_bound (g := g)
  refine ⟨(Module.finrank ℝ E : ℝ) ^ (r + s) * (((r + s : ℕ) : ℝ) * Real.sqrt Kbase) ^ 2, ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
  intro x n e horth i j K' J
  exact riemannianFiberNormSq_riemannOp_tensorCovRS_dualTensorFrameRS_le (I := I) (M := M) g r s x
    e i j K' J Kbase hKbase (fun a b c => hKb x a b c) horth

/-- **Uniform-over-`M` dual-frame curvature energy constant at valence `(r, s)`.** A single
nonnegative constant `C`, independent of the base point and of the chosen `g`-orthonormal frame,
bounding the dual-frame curvature energy
`∑_{i, j, K, J} riemannianFiberNormSq g r s x (R_x(e_i, e_j)(dualTensorFrameRS g x r s e K J))` — the
valence-`(r, s)` mirror of `exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const`.  The energy is
a sum of `n^(r + s + 2)` single dual-frame terms with `n ≤ d := finrank E` (a `g`-orthonormal family
is linearly independent), so it is bounded by `d^(r + s + 2) · K`. -/
private lemma exists_uniform_riemannOp_tensorCovRS_dualFrameEnergy_const
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        (∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
                (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) ≤ C := by
  classical
  obtain ⟨K, hK_nonneg, hK_term⟩ :=
    exists_uniform_riemannOp_tensorCovRS_dualFrameEnergy_single_term (I := I) (M := M) g r s
  set d : ℕ := Module.finrank ℝ E with hd_def
  refine ⟨(d : ℝ) ^ (r + s + 2) * K, ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) hK_nonneg
  intro x n e horth
  -- `n ≤ d`: the `g`-orthonormal family `e` is linearly independent in `T_x M`.
  have hn_le_d : n ≤ d := by
    let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
    have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
      g.toRiemannianMetric.continuousAt x
    have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
        RCLike.re (cd.inner v v) < 1} := g.toRiemannianMetric.isVonNBounded x
    letI nag : NormedAddCommGroup (TangentSpace I x) :=
      cd.toNormedAddCommGroupOfTopology hc hbnd
    letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
      InnerProductSpace.ofCoreOfTopology cd hc hbnd
    have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v := fun u v => rfl
    have horthonormal : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro a b; rw [hinner_eq (e a) (e b)]; exact horth a b
    have hcard := horthonormal.linearIndependent.fintype_card_le_finrank
    have hcardE : Module.finrank ℝ (TangentSpace I x) = d := rfl
    rw [hcardE] at hcard
    simpa using hcard
  -- Bound the energy term-by-term by `K`, then count `n^(r + s + 2)` terms.
  have hsum_le_const :
      (∑ i : Fin n, ∑ j : Fin n, ∑ K' : Fin r → Fin n, ∑ J : Fin s → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
              (dualTensorFrameRS (I := I) (M := M) g x r s e K' J))) ≤
        ∑ _i : Fin n, ∑ _j : Fin n, ∑ _K' : Fin r → Fin n, ∑ _J : Fin s → Fin n, K := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun K' _ => ?_)
    refine Finset.sum_le_sum (fun J _ => ?_)
    exact hK_term x e horth i j K' J
  refine le_trans hsum_le_const ?_
  have hconst_eq :
      (∑ _i : Fin n, ∑ _j : Fin n, ∑ _K' : Fin r → Fin n, ∑ _J : Fin s → Fin n, K) =
        (n : ℝ) ^ (r + s + 2) * K := by
    rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst_eq]
  refine mul_le_mul_of_nonneg_right ?_ hK_nonneg
  exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hn_le_d) (r + s + 2)

/-- **The uniform-over-`M` proportional curvature-operator fibre bound at valence `(r, s)` (posited
general-valence analytic child — the "mirror-2" uniform curvature sup).** For a closed smooth
Riemannian manifold `(M, g)` and fixed valence `(r, s)` there is a single nonnegative constant `Csup`,
independent of the base point, such that for every point `x`, tangent vectors `v, w`, and
`(r, s)`-tensor `T`,
```
rfns(R^{(r,s)}_x(v, w) T)(x) ≤ Csup · g(v, v) · g(w, w) · rfns(T)(x).
```

**Why this is TRUE.** This is the verbatim contravariant-valence-`r` mirror of the *proved*
contravariant-`0` `exists_uniform_riemannOp_tensorCov_proportional`
(`FrozenFramePureRCurvatureTower`) / `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`
(`UniformProportionalCurvatureSup`), and is exactly the headline this file's intended home
`RankRUniformProportionalCurvatureSup` documents (`exists_uniform_riemannianFiberNormSq_riemannOp_`
`tensorCovRS_proportional`) but does not yet assemble.  Its proof is the documented dual-frame route:
the per-point bound `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs`
(`RiemannianFiberNormSqRiemannOpHigherRankParseval`) re-run with the *uniformised* single dual-frame
curvature energy term, which the point-level slot-wise curvature formula `riemannOp_tensorCovRS_apply_eval`
(`RankRUniformProportionalCurvatureSup`) splits into a covariant `(0, s)` and a contravariant `(0, r)`
branch, each dominated through the coframe-curvature magnitude bound
`abs_toModel_riemannOp_tensor0SCov_coframeS_le` (`TensorCurvatureUnitEvalBridge`) by the valence-free
Levi-Civita base-curvature `g`-norm bound `exists_uniform_riemannOp_LeviCivita_gNorm_bound` (`Kbase`) —
exactly the valence-`r` mirror of the contravariant-`0` dual-frame energy constant
`exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const` (`CurvatureFrameEnergyContinuity`).  The
per-point constant of `exists_Cx_…_le_rs` is built from the pointwise `stdOrthonormalBasis`, hence not
continuous in `x`, so it cannot be supremised directly; the dual-frame-energy uniformisation is the
genuinely-irreducible analytic content, absent sorry-free at valence `r`, posited here as one precise
true child.  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate witness `Csup ≡ 0` is rejected on any non-flat manifold: the bundled
curvature operator `R^{(r,s)}_x(v, w)` is genuinely nonzero (`R ≠ 0`) on a tensor `T` it does not
annihilate, so `rfns(R^{(r,s)}_x(v, w) T)(x) > 0` for suitable `(v, w, T)` while the RHS
`0 · g(v, v) · g(w, w) · rfns(T)(x) = 0`; the constant must carry the genuine curvature magnitude and
is genuinely positive. -/
theorem exists_uniform_riemannianFiberNormSq_riemannOp_tensorCovRS_proportional
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Csup : ℝ, 0 ≤ Csup ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace r s I x),
        riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x v w T) ≤
          Csup * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  obtain ⟨C, hC_nonneg, hC_energy⟩ :=
    exists_uniform_riemannOp_tensorCovRS_dualFrameEnergy_const (I := I) (M := M) g r s
  refine ⟨C, hC_nonneg, fun x v w T => ?_⟩
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g r s x
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hrfns_nonneg : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s x T :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x T
  -- `(v, w)`-factorisation: `rfns(R(v,w)T) ≤ g(v,v)·g(w,w)·∑_{i,j} rfns(R(eᵢ,eⱼ)T)`.
  have hvw : riemannianFiberNormSq (I := I) (M := M) g r s x (R v w T) ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := by
    rw [hrepr (R v w T)]
    have hterm : ∀ K : Fin r → Fin n, ∀ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x r s (R v w T) n e K J ≤
          g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J :=
      fun K J => fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
        (I := I) (M := M) g x r s e hpars hexpand v w T K J
    calc
      (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s (R v w T) n e K J)
          ≤ ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              g.inner x v v * g.inner x w w *
                ∑ i : Fin n, ∑ j : Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
            exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
      _ = g.inner x v v * g.inner x w w *
            ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun K _ => ?_)
            rw [Finset.mul_sum]
      _ = g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := by
            congr 1
            set F : (Fin r → Fin n) → (Fin s → Fin n) → Fin n → Fin n → ℝ :=
              fun K J i j =>
                fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J
              with hF_def
            have hRHS_eq : (∑ i : Fin n, ∑ j : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T)) =
                ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  F K J i j := by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              rw [hF_def]
              exact hrepr (R (e i) (e j) T)
            rw [hRHS_eq]
            have hLHS : (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
              calc
                (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                    ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                    = ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                        ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                      refine Finset.sum_congr rfl (fun K _ =>
                        Finset.sum_congr rfl (fun J _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
                _ = ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                        ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun K J =>
                        ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
            have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, F K J i j) =
                ∑ p : Fin n × Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 p.1 p.2 := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, F K J i j)
                    = ∑ i : Fin n, ∑ j : Fin n,
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 i j := by
                      refine Finset.sum_congr rfl (fun i _ =>
                        Finset.sum_congr rfl (fun j _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
                _ = ∑ p : Fin n × Fin n,
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun i j =>
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 i j)).symm
            rw [hLHS, hRHS]
            exact Finset.sum_comm
  -- `∑_{i,j} rfns(R(eᵢ,eⱼ)T) ≤ (energy)·rfns(T) ≤ C·rfns(T)`.
  have hCxT : (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T)) ≤
      C * riemannianFiberNormSq (I := I) (M := M) g r s x T := by
    refine le_trans (sum_riemannianFiberNormSq_riemannOpRS_le_Cx
      (I := I) (M := M) g x r s e bse hbse horth hrepr T) ?_
    exact mul_le_mul_of_nonneg_right (hC_energy x e horth) hrfns_nonneg
  calc
    riemannianFiberNormSq (I := I) (M := M) g r s x (R v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (C * riemannianFiberNormSq (I := I) (M := M) g r s x T) := by
          refine mul_le_mul_of_nonneg_left hCxT ?_
          exact mul_nonneg hvv_nonneg hww_nonneg
    _ = C * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by ring

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
  classical
  set N : ℝ := (Module.finrank ℝ E : ℝ) with hN_def
  -- The valence-`r` uniform curvature sups (one per rank `m`) give the order-`0` constant family.
  choose Csup hCsup_nonneg hCsup using fun m =>
    exists_uniform_riemannianFiberNormSq_riemannOp_tensorCovRS_proportional (I := I) (M := M) g r m
  refine ⟨fun rr => match rr with | 0 => (0 : ℝ) | (m + 1) => N ^ 3 * Csup m,
    fun rr => ?_, fun rr W x => ?_⟩
  · -- Nonnegativity of the constant family.
    cases rr with
    | zero => exact le_refl 0
    | succ m => exact mul_nonneg (by positivity) (hCsup_nonneg m)
  -- Case on the rank; the order-`0` operator is `genuinePureREndo0RS g r rr W`.
  cases rr with
  | zero =>
      -- Rank `0`: the endomorphism is the zero operator, fibre norm `0`.
      rw [show (genuinePureRDiffOpRS (I := I) (M := M) g r 0 0 W).toSection x =
          (0 : TensorRSSpace r (0 + 0) I x) from rfl]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g r (0 + 0) x]
      show (0 : ℝ) ≤ (0 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g r 0 x (W.toSection x)
      exact le_of_eq (zero_mul _).symm
  | succ m =>
      -- Rank `m + 1`: the genuine moving-frame endomorphism at the centre `x`.
      set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
        smoothOrthoFrame (I := I) g x with hB_def
      have hBorth : ∀ i j : Fin (Module.finrank ℝ E),
          g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0 := by
        intro i j; rw [hB_def]; exact smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
      -- The order-`0` endomorphism fibre at `x` is the slot-`0` uncurry of the direction CLM.
      have hfib : (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (m + 1) W).toSection x =
          covGradBundleEquiv (I := I) (M := M) r m x
            (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x) := by
        change genuinePureREndoFibRS (I := I) (M := M) g r m W x = _
        rw [genuinePureREndoFibRS, pureRFrozenEndoFibRS]
      rw [hfib]
      -- Per-unit-direction fibre bound on the direction CLM: `rfns(Φ v) ≤ N² · Csup m · rfns(W x)`.
      set rW : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x (W.toSection x) with hrW_def
      have hrW_nonneg : 0 ≤ rW :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x (W.toSection x)
      have hper : ∀ v : TangentSpace I x, g.inner x v v = 1 →
          riemannianFiberNormSq (I := I) (M := M) g r m x
              (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x v) ≤
            N * (N * (Csup m * rW)) := by
        intro v hv
        rw [pureRFrozenDirCLMRS_apply (I := I) (M := M) g r m B (fun y : M => W.toSection y) x v]
        -- `N`-subadditivity over the frame index `i`.
        refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r m x
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _) ?_
        rw [Finset.card_univ, Fintype.card_fin]
        have hcard : (Module.finrank ℝ E : ℝ) = N := by rw [hN_def]
        rw [hcard]
        refine mul_le_mul_of_nonneg_left ?_ (by rw [hN_def]; positivity)
        -- Each summand: curvature sup × unit Gram × slot-`0` reading domination.
        have hsummand : ∀ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g r m x
                (riemannOp (tensorCov (I := I) g r m) x (B i x) v
                  ((covGradBundleEquiv (I := I) (M := M) r m x).symm (W.toSection x) (B i x))) ≤
              Csup m * rW := by
          intro i
          have hgB : g.inner x (B i x) (B i x) = 1 := by
            have := hBorth i i; rwa [if_pos rfl] at this
          have hbound := hCsup m x (B i x) v
            ((covGradBundleEquiv (I := I) (M := M) r m x).symm (W.toSection x) (B i x))
          rw [hgB, hv, mul_one, mul_one] at hbound
          refine le_trans hbound ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCsup_nonneg m)
          -- The slot-`0` reading along `B i x` is dominated by the full `(r, m+1)` fibre norm.
          rw [hrW_def]
          exact riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le_rs (I := I) (M := M) g r m x
            (W.toSection x) B hBorth i
        refine le_trans (Finset.sum_le_sum (fun i _ => hsummand i)) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcard]
      -- Forward-uncurry frame-sum bound: `rfns(covGradBundleEquiv r m x Φ) ≤ N · (N²·Csup m·rW)`.
      refine le_trans (riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs (I := I) (M := M)
        g r m x (pureRFrozenDirCLMRS (I := I) (M := M) g r m B (fun y : M => W.toSection y) x)
        (N * (N * (Csup m * rW))) hper) ?_
      -- Assemble: `N · (N · (N · Csup m · rW)) = N³ · Csup m · rW = kappa0 (m+1) · rfns(W x)`.
      rw [show (Module.finrank ℝ E : ℝ) = N from by rw [hN_def]]
      show N * (N * (N * (Csup m * rW))) ≤ N ^ 3 * Csup m * rW
      exact le_of_eq (by ring)

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
