import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParallelRankReducingContractionGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldDifferentiatedTowerNormalForm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceCovJet

/-! # The rank-generic cometric `g₀⁻¹` double trace as a parallel rank-reducing contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **passenger-passing** rank-generic cometric `g₀⁻¹`
double-trace operator family and its two `∇`-compatibility laws, the building blocks of a
`ParallelRankReducingContraction g₀ (p + 2) p` realised on top of the smooth, parallel cometric
double-trace field `cometricDoubleTraceField g₀ p` (`CometricDoubleTraceField.lean`).

The rank-generic cometric double trace `cometricDoubleTraceField g₀ p : SmoothCcTensor g₀ (p + 2) p`
contracts the two leading covariant slots `{0, 1}` against the cometric `g₀⁻¹` (raise slot `0` by the
smooth cometric `♯`, then the FRAME-FREE natural trace against the original slot — ONE inverse,
`D : g₀⁻¹`), and is `∇₀`-parallel (`cometricDoubleTraceField_covGrad_eq_zero`, the genuine cometric
core `∇₀ g₀⁻¹ = 0`).  Its operator-field action `appCc (cometricDoubleTraceField g₀ p) R` is the
section-level `(0, p + 2) → (0, p)` double trace; the consumer (the Lie-half P1b quadratic Rest arm's
double-cometric-trace jet analysis,
`appCc(cometricDoubleTrace 2)(appCc(cometricDoubleTrace 4)(cartanCrossProductDiff))`) reads its
covariant jet through the parallel rank-reducing `rfns` grid `ParallelRankReducingContraction
.rfns_iteratedCovGrad_le`.

## What this file builds

* `cometricDoubleTraceFieldRec g₀ p a` — the **passenger-passing** double-trace operator field at
  gradient-shift `a`, the `a`-fold leading-passenger-slot extension `slotExtendᵃ` of the base
  `cometricDoubleTraceField g₀ p` (each `slotExtend` prepends one covariant passenger slot read first
  and passed unchanged).  `cometricDoubleTraceFieldRec g₀ p (a + 1) = slotExtend (... a)` by
  construction (the rank equalities `((p + 2) + a) + 1 = (p + 2) + (a + 1)`, `(p + a) + 1 = p + (a + 1)`
  are definitional, `Nat.add`-on-the-right).
* `cometricDoubleTraceFieldRec_covGrad_eq_zero` — the passenger-passing field is `∇₀`-parallel at every
  gradient-shift (base parallelism + slot-extension parallelism
  `covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`).
* `cometricDoubleTraceRecOp g₀ p a` — the section-level `(0, (p + 2) + a) → (0, p + a)` operator at
  gradient-shift `a`, the operator-field action `appCc` of `cometricDoubleTraceFieldRec g₀ p a`.
* `cometricDoubleTraceRecOp_covGrad` — the **exact parallel single-step covariant Leibniz** (no
  differentiated-operator cross term, since the cometric is parallel): `∇₀(op a R) = (rank-cast)
  op (a + 1) (∇₀ R)`.  This is the `covGrad_op` field of `ParallelRankReducingContraction`, and the
  rank-generic, `−2`-unscaled twin of the curvature-side `ricciModelTrace42Op_covGrad`.

These are the `op` and `covGrad_op` fields of `ParallelRankReducingContraction g₀ (p + 2) p`.  The
remaining `kappa` / `rfns_op_le` fields are the order-uniform `g`-operator-norm fibre envelope of the
cometric double trace (uniform over the passenger count, the leading passenger slot being an isometric
ampliation of the cometric-bounded base operator); they are NOT included here — see the module note. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The passenger-passing rank-generic cometric `g₀⁻¹` double-trace operator field at
gradient-shift `a`**, a smooth `(0, (p + 2) + a) → (0, p + a)`-operator field defined as the `a`-fold
leading-passenger-slot extension `slotExtendᵃ` of the base double-trace field
`cometricDoubleTraceField g₀ p` (which contracts the two leading covariant slots `{0, 1}` against the
cometric `g₀⁻¹`).  Each `slotExtend` prepends one leading covariant passenger slot (read first, passed
unchanged to the output, `slotExtendFib_apply_eval`), so this field contracts the cometric `g₀⁻¹`
against slots `{a, a + 1}` (after the `a` accumulated leading gradient-passenger slots).

The defining feature, **by construction**: `cometricDoubleTraceFieldRec g₀ p (a + 1) = slotExtend
(cometricDoubleTraceFieldRec g₀ p a)` (the `Nat`-equalities `((p + 2) + a) + 1 = (p + 2) + (a + 1)` and
`(p + a) + 1 = p + (a + 1)` are definitional).  This is what makes the index-bump covariant Leibniz
`cometricDoubleTraceRecOp_covGrad` genuinely TRUE: the surviving operator factor of the `appCc` B-rule,
when the gradient differentiates the contracted section, is exactly `slotExtend` of the operator field,
which advances `a → a + 1`.  At `a = 0` it is the base double trace itself. -/
noncomputable def cometricDoubleTraceFieldRec (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∀ a : ℕ, SmoothCcTensor g₀ ((p + 2) + a) (p + a)
  | 0 => PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceField (I := I) g₀ p
  | (a + 1) =>
    Integral.Connection.slotExtend (I := I) (M := M) g₀ ((p + 2) + a) (p + a)
      (cometricDoubleTraceFieldRec g₀ p a)

set_option linter.unusedSectionVars false in
/-- The base of the passenger-passing field recursion is the leading-`{0, 1}` cometric double trace.
Definitional. -/
@[simp] theorem cometricDoubleTraceFieldRec_zero (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    cometricDoubleTraceFieldRec (I := I) g₀ p 0 =
      PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceField (I := I) g₀ p := rfl

set_option linter.unusedSectionVars false in
/-- **The successor step of the passenger-passing field recursion is one `slotExtend`.**  Advancing the
gradient-shift `a → a + 1` is exactly prepending one leading passenger covariant slot.  Definitional
(the rank equalities `((p + 2) + a) + 1 = (p + 2) + (a + 1)`, `(p + a) + 1 = p + (a + 1)` hold by
`Nat.add`-on-the-right). -/
@[simp] theorem cometricDoubleTraceFieldRec_succ (g₀ : SmoothRiemannianMetric I M) (p a : ℕ) :
    cometricDoubleTraceFieldRec (I := I) g₀ p (a + 1) =
      Integral.Connection.slotExtend (I := I) (M := M) g₀ ((p + 2) + a) (p + a)
        (cometricDoubleTraceFieldRec (I := I) g₀ p a) := rfl

set_option linter.unusedSectionVars false in
/-- **The cometric `∇₀`-parallelism core: the passenger-passing cometric `g₀⁻¹` double-trace field is
`∇₀`-parallel** at every gradient-shift `a`:
```
covGrad g₀ ((p + 2) + a) (p + a) (cometricDoubleTraceFieldRec g₀ p a) = 0.
```
Induction on `a`.  At `a = 0` the field is the base double trace, whose parallelism is the genuine
cometric core `cometricDoubleTraceField_covGrad_eq_zero` (`∇₀ g₀⁻¹ = 0`).  At `a + 1` the field is
`slotExtend (cometricDoubleTraceFieldRec g₀ p a)`, and the covariant gradient annihilates the
slot-extension of the inductively-parallel field
(`covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`).  It is **non-vacuous**: the genuine
differential-geometric assertion that the background cometric is parallel; false for a non-parallel
ambient frame. -/
theorem cometricDoubleTraceFieldRec_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (p a : ℕ) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ ((p + 2) + a) (p + a)
        (cometricDoubleTraceFieldRec (I := I) g₀ p a) = 0 := by
  induction a with
  | zero =>
    rw [cometricDoubleTraceFieldRec_zero]
    exact PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceField_covGrad_eq_zero
      (I := I) g₀ p
  | succ a ih =>
    rw [cometricDoubleTraceFieldRec_succ]
    exact PDE.RicciFlow.IntrinsicSpectral.DeTurck.covGrad_slotExtend_eq_zero_of_covGrad_eq_zero
      (I := I) g₀ ((p + 2) + a) (p + a) (cometricDoubleTraceFieldRec (I := I) g₀ p a) ih

/-- **The section-level rank-generic cometric `g₀⁻¹` double-trace operator `(0, (p + 2) + a) → (0,
p + a)`** at gradient-shift `a`: the operator-field action `appCc` of the passenger-passing smooth
double-trace operator field `cometricDoubleTraceFieldRec g₀ p a` (contracting the cometric `g₀⁻¹`
against the slots `{a, a + 1}` after the `a` leading gradient-passenger slots) on the input
`(0, (p + 2) + a)`-tensor.  The same smooth-section route as the curvature operator-field action
`appCc`.  At `a = 0` it is the action of the base field `cometricDoubleTraceField g₀ p`. -/
noncomputable def cometricDoubleTraceRecOp (g₀ : SmoothRiemannianMetric I M) (p a : ℕ) :
    SmoothCcTensor g₀ 0 ((p + 2) + a) → SmoothCcTensor g₀ 0 (p + a) :=
  fun R => Integral.Connection.appCc (I := I) (M := M) g₀ ((p + 2) + a) (p + a)
    (cometricDoubleTraceFieldRec (I := I) g₀ p a) R

set_option linter.unusedSectionVars false in
/-- **The fibre value of `cometricDoubleTraceRecOp` is the fibrewise composition of the
passenger-passing double-trace fibre operator with the input section.**  Definitional via
`appCc_toSection`. -/
@[simp] theorem cometricDoubleTraceRecOp_toSection (g₀ : SmoothRiemannianMetric I M) (p a : ℕ)
    (R : SmoothCcTensor g₀ 0 ((p + 2) + a)) (x : M) :
    (cometricDoubleTraceRecOp (I := I) g₀ p a R).toSection x =
      (show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (p + a) I x from
        (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from R.toSection x) := by
  rw [cometricDoubleTraceRecOp, appCc_toSection]

set_option linter.unusedSectionVars false in
/-- **Fibrewise `ℝ`-additivity of the section-level cometric double-trace operator over a difference.**
`cometricDoubleTraceRecOp` distributes over a section difference: it is the operator-field action
`appCc` of the fixed passenger-passing double-trace field, additive in the contracted section
(`appCc_add_right` / `appCc_smul_right`). -/
theorem cometricDoubleTraceRecOp_sub (g₀ : SmoothRiemannianMetric I M) (p a : ℕ)
    (A B : SmoothCcTensor g₀ 0 ((p + 2) + a)) :
    cometricDoubleTraceRecOp (I := I) g₀ p a (A - B) =
      cometricDoubleTraceRecOp (I := I) g₀ p a A - cometricDoubleTraceRecOp (I := I) g₀ p a B := by
  rw [cometricDoubleTraceRecOp, cometricDoubleTraceRecOp, cometricDoubleTraceRecOp, sub_eq_add_neg,
    appCc_add_right, show (-B) = (-1 : ℝ) • B by rw [neg_one_smul], appCc_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
/-- **The exact parallel single-step covariant Leibniz of the rank-generic cometric `g₀⁻¹` double
trace.**  No differentiated-operator cross term (the moving-coframe corrections cancel against the
cometric parallelism):
```
∇₀(cometricDoubleTraceRecOp g₀ p a R) = (rank-cast) cometricDoubleTraceRecOp g₀ p (a + 1) (∇₀ R),
```
the new gradient slot carried at the front, rank-cast from `p + (a + 1)` to `(p + a) + 1` by
`castRankCc_db`.  This is genuinely TRUE because the contraction is against the `∇₀`-parallel cometric
`g₀⁻¹` (NOT a fixed, non-`∇₀`-parallel ambient basis): the B-rule for the operator-field action
(`covGrad_appCc_eq`) splits `∇₀(op a R)` into the differentiated-field cross term — which VANISHES by
the cometric parallelism `cometricDoubleTraceFieldRec_covGrad_eq_zero` — plus the surviving
`slotExtend`-of-field action on `∇₀ R`, and `slotExtend (FieldRec a) = FieldRec (a + 1)` advances the
gradient-shift.  This is the `covGrad_op` field of `ParallelRankReducingContraction g₀ (p + 2) p`, the
rank-generic, `−2`-unscaled twin of the curvature-side `ricciModelTrace42Op_covGrad`. -/
theorem cometricDoubleTraceRecOp_covGrad (g₀ : SmoothRiemannianMetric I M) (p a : ℕ)
    (R : SmoothCcTensor g₀ 0 ((p + 2) + a)) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 (p + a)
        (cometricDoubleTraceRecOp (I := I) g₀ p a R) =
      Integral.Connection.castRankCc_db g₀ 0 (by omega : p + (a + 1) = (p + a) + 1)
        (cometricDoubleTraceRecOp (I := I) g₀ p (a + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 ((p + 2) + a) R)) := by
  rw [cometricDoubleTraceRecOp,
    covGrad_appCc_eq (I := I) (M := M) g₀ ((p + 2) + a) (p + a)
      (cometricDoubleTraceFieldRec (I := I) g₀ p a) R,
    cometricDoubleTraceFieldRec_covGrad_eq_zero (I := I) g₀ p a,
    appCc_zero_left (I := I) (M := M) g₀ ((p + 2) + a) ((p + a) + 1) R, zero_add]
  rw [← cometricDoubleTraceFieldRec_succ (I := I) g₀ p a]
  exact (eq_of_heq (Integral.Connection.castRankCc_db_heq g₀ 0
    (by omega : p + (a + 1) = (p + a) + 1)
    (cometricDoubleTraceRecOp (I := I) g₀ p (a + 1)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 ((p + 2) + a) R)))).symm

set_option linter.unusedSectionVars false in
/-- **The post-composition fibre operator applied to `R.toSection x` is the fibre value of
`cometricDoubleTraceRecOp` at `x`.**  For any fibrewise operator `A : (0, (p + 2) + a)-tensor →L
(0, p + a)-tensor` that post-composes the passenger-passing cometric `g₀⁻¹` double-trace fibre operator
`(cometricDoubleTraceFieldRec g₀ p a).toSection x` after the `(0, (p + 2) + a)`-tensor, the image
`A (R.toSection x)` is the fibre value `(cometricDoubleTraceRecOp g₀ p a R).toSection x` of the
operator-field action (`cometricDoubleTraceRecOp_toSection`).  This exhibits the operator-field-action
fibre value as a `g₀`-fibre Hom-bundle operator's action, the bridge feeding the sharp `g`-operator-norm
fibre-norm bound. -/
private theorem cometricDoubleTraceRecOp_toSection_eq_postcomp (g₀ : SmoothRiemannianMetric I M)
    (p a : ℕ) (x : M) (R : Integral.L2.SmoothCcTensor g₀ 0 ((p + 2) + a))
    (A : Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace 0 (p + a) I x)
    (hA : ∀ v : Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x,
      A v = (show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (p + a) I x from
        (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from v)) :
    A (R.toSection x) = (cometricDoubleTraceRecOp (I := I) g₀ p a R).toSection x := by
  rw [hA (R.toSection x), cometricDoubleTraceRecOp_toSection]

set_option linter.unusedSectionVars false in
/-- **The all-ranks frame witness of the intrinsic fibre norm.**  At a base point `x` there is a single
tangent frame `e` (with `n = finrank` directions, the `g₀(x)`-orthonormal frame internal to
`riemannianFiberNormSq`) representing the intrinsic `(0, s)` fibre norm as the frame double sum at
**every** covariant rank `s` simultaneously.  This is `tangent_orthonormalBasisS_witness` with the rank
quantified inside the existential (the internal construction does not depend on the rank). -/
private theorem cometric_rfns_allRanks_frame_witness (g₀ : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      ∀ (s : ℕ) (S : Tensor0SBundle.TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
            Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 s S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g₀.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g₀.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g₀.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  exact ⟨n, fun i => eob i, rfl, fun s S => rfl⟩

set_option linter.unusedSectionVars false in
/-- **The leading-slot slice of the slot-extended cometric double-trace action is the action on the
slice.**  The slot-`0` curry of the slot-extended passenger-passing field's post-composition action,
along a frame direction `e b`, is the one-step-lower field's post-composition action on the slot-`0`
curry of the input (`slotExtendFib` reads the passenger slot first and passes it unchanged). -/
private theorem slot0Curry_cometricFieldRec_postcomp (g₀ : SmoothRiemannianMetric I M) (p a : ℕ)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (v : Tensor0SBundle.TensorRSSpace 0 ((p + 2) + (a + 1)) I x) (b : Fin n) :
    Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (p + a) e K₀
        ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + (a + 1)) I x from
          (cometricDoubleTraceFieldRec (I := I) g₀ p (a + 1)).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x from v)) b =
      (show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (p + a) I x from
        (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from
          Integral.Connection.slot0Curry (I := I) (M := M) g₀ x ((p + 2) + a) e K₀ v b) := by
  classical
  apply ContinuousLinearMap.ext
  intro τ
  have hLHS : (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (p + a) e K₀
        ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + (a + 1)) I x from
          (cometricDoubleTraceFieldRec (I := I) g₀ p (a + 1)).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x from v)) b :
        Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + a) I x) τ =
      Integral.Connection.tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + a) I x from
          (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x)
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) ((p + 2) + a) x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x from v)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K₀ k)))))
            (e b))) := by
    rw [Integral.Connection.slot0Curry_apply]
    congr 1
  have hRHS : ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (p + a) I x from
        (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from
          Integral.Connection.slot0Curry (I := I) (M := M) g₀ x ((p + 2) + a) e K₀ v b)) τ =
      Integral.Connection.tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + a) I x from
          (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x)
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) ((p + 2) + a) x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x from v)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K₀ k)))))
            (e b))) := by
    rw [ContinuousLinearMap.comp_apply, Integral.Connection.slot0Curry_apply, map_smul]
    rfl
  exact hLHS.trans hRHS.symm

set_option linter.unusedSectionVars false in
/-- **The order-uniform postcomposition envelope over the passenger-passing recursion.**  From the
base-level (`a = 0`) uniform fibre envelope, the same constant bounds the post-composition action of the
slot-extended field at **every** gradient-shift `a`: by induction, slicing the leading passenger
covariant slot with the all-ranks frame Parseval split
(`riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame`) and passing each slice through
`slot0Curry_cometricFieldRec_postcomp` to the inductive hypothesis — the leading passenger slot is an
isometric ampliation for the intrinsic fibre envelope. -/
private theorem cometricDoubleTrace_postcomp_rfns_le_aux (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (κ₀ : ℝ)
    (hbase : ∀ (x : M) (v : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace p I x from
            (cometricDoubleTraceFieldRec (I := I) g₀ p 0).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 2) I x from v)) ≤
        κ₀ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + 2) x v) :
    ∀ (a : ℕ) (x : M) (v : Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + a) x
          ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (p + a) I x from
            (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from v)) ≤
        κ₀ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((p + 2) + a) x v := by
  intro a
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro x v
    classical
    obtain ⟨n, e, hn, hrepr⟩ := cometric_rfns_allRanks_frame_witness (I := I) g₀ x
    have hL : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + (a + 1)) x
          ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (p + (a + 1)) I x from
            (cometricDoubleTraceFieldRec (I := I) g₀ p (a + 1)).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x from v)) =
        ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + a) x
            (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (p + a) e
              (fun k => k.elim0)
              ((show Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + (a + 1)) I x from
                (cometricDoubleTraceFieldRec (I := I) g₀ p (a + 1)).toSection x).comp
                (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace ((p + 2) + (a + 1)) I x from v)) b) :=
      Integral.Connection.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame
        (I := I) (M := M) g₀ (p + a) x e (fun k => k.elim0)
        (hrepr (p + a)) (hrepr (p + a + 1)) _
    have hR : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((p + 2) + (a + 1)) x v =
        ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((p + 2) + a) x
            (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x ((p + 2) + a) e
              (fun k => k.elim0) v b) :=
      Integral.Connection.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame
        (I := I) (M := M) g₀ ((p + 2) + a) x e (fun k => k.elim0)
        (hrepr ((p + 2) + a)) (hrepr ((p + 2) + a + 1)) _
    rw [hL, hR, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [slot0Curry_cometricFieldRec_postcomp (I := I) g₀ p a x e (fun k => k.elim0) v b]
    exact ih x (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x ((p + 2) + a) e
      (fun k => k.elim0) v b)

/-- **The post-composition operator of the passenger-passing cometric `g₀⁻¹` double-trace fibre
operator**, as a continuous-linear map on the `(0, (p + 2) + a)`-tensor fibre:
`v ↦ (cometricDoubleTraceFieldRec g₀ p a).toSection x ∘ v` (post-composition is `ℝ`-linear; closed to a
continuous-linear map on the finite-dimensional fibre). -/
private noncomputable def cometricFieldRecPostcompCLM (g₀ : SmoothRiemannianMetric I M) (p a : ℕ)
    (x : M) :
    Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace 0 (p + a) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x))
  haveI : T2Space (Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        (show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + a) I x from
          (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from v)
      map_add' := fun _ _ => ContinuousLinearMap.comp_add _ _ _
      map_smul' := fun _ _ => ContinuousLinearMap.comp_smul _ _ _ }

set_option linter.unusedSectionVars false in
/-- Defining evaluation of `cometricFieldRecPostcompCLM`: post-composition by the passenger-passing
cometric double-trace fibre operator. -/
private theorem cometricFieldRecPostcompCLM_apply (g₀ : SmoothRiemannianMetric I M) (p a : ℕ) (x : M)
    (v : Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x) :
    cometricFieldRecPostcompCLM (I := I) g₀ p a x v =
      (show Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (p + a) I x from
        (cometricDoubleTraceFieldRec (I := I) g₀ p a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x from v) := by
  haveI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x))
  haveI : T2Space (Tensor0SBundle.TensorRSSpace 0 ((p + 2) + a) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace ((p + 2) + a) I x))
  exact congrFun (LinearMap.coe_toContinuousLinearMap' _) v

set_option linter.unusedSectionVars false in
/-- **The order-uniform `g₀`-operator-norm fibre envelope of the rank-generic cometric `g₀⁻¹` double
trace.**  For the passenger-passing double-trace field there is a single nonnegative `κ`, uniform over
the gradient-shift `a`, the section `R`, and the base point `x`, controlling the intrinsic squared fibre
norm of the operator-field action:
```
rfns_{(0, p + a)}((cometricDoubleTraceRecOp g₀ p a R).toSection x) ≤ κ · rfns_{(0, (p + 2) + a)}(R)(x).
```

**Decomposition.**  The base passenger-count uniform `g`-operator-norm envelope
`exists_uniform_cometricDoubleTraceField_postcomp_gOpNorm_rfns_le` is itself uniform over the cometric
field's own passenger count, so at the recursion base `cometricDoubleTraceFieldRec g₀ p 0 =
cometricDoubleTraceField g₀ p` it supplies the base-level (`a = 0`) fibre-value envelope `hbase`.  The
order-uniform passenger ampliation `cometricDoubleTrace_postcomp_rfns_le_aux` then carries that single
constant to every gradient-shift `a` (the leading passenger slot is an isometric ampliation for the
intrinsic fibre envelope — the `g`-operator-norm route, *a*-uniform unlike the HS route which grows by a
`dim`-factor per passenger slot).  The fibre value `(cometricDoubleTraceRecOp g₀ p a R).toSection x` is
exactly the post-composition action `A (R.toSection x)`
(`cometricDoubleTraceRecOp_toSection_eq_postcomp`), so the envelope at `v = R.toSection x` is the claim.
It is **non-vacuous** (a degenerate `κ = 0` is rejected whenever `op a R ≠ 0`). -/
theorem exists_uniform_cometricDoubleTraceRecOp_rfns_le (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (a : ℕ) (R : Integral.L2.SmoothCcTensor g₀ 0 ((p + 2) + a)) (x : M),
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + a) x
          ((cometricDoubleTraceRecOp (I := I) g₀ p a R).toSection x) ≤
        κ * Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((p + 2) + a) x
          (R.toSection x) := by
  classical
  obtain ⟨κ, hκ0, hκ⟩ :=
    exists_uniform_cometricDoubleTraceField_postcomp_gOpNorm_rfns_le (I := I) g₀
  -- The base-level (`a = 0`) fibre-value envelope, from the passenger-count-uniform base envelope at
  -- the recursion base `cometricDoubleTraceFieldRec g₀ p 0 = cometricDoubleTraceField g₀ p`.
  have hbase : ∀ (x : M) (v : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace p I x from
            (cometricDoubleTraceFieldRec (I := I) g₀ p 0).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 2) I x from v)) ≤
        κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + 2) x v := by
    intro x v
    obtain ⟨A, hAdef, hAbound⟩ := hκ p x
    have hb := hAbound v
    rw [hAdef v] at hb
    rw [cometricDoubleTraceFieldRec_zero]
    exact hb
  refine ⟨κ, hκ0, fun a R x => ?_⟩
  rw [← cometricDoubleTraceRecOp_toSection_eq_postcomp (I := I) g₀ p a x R
    (cometricFieldRecPostcompCLM (I := I) g₀ p a x)
    (fun v => cometricFieldRecPostcompCLM_apply (I := I) g₀ p a x v)]
  rw [cometricFieldRecPostcompCLM_apply (I := I) g₀ p a x (R.toSection x)]
  exact cometricDoubleTrace_postcomp_rfns_le_aux (I := I) g₀ p κ hbase a x (R.toSection x)

/-- **The `(0, p + 2) → (0, p)` intrinsic `g₀⁻¹` double-trace parallel rank-reducing contraction.**  The
parallel rank-reducing single-section contraction realising the cometric double trace `g₀^{ij}·` of the
two leading covariant slots, a `ParallelRankReducingContraction g₀ (p + 2) p`, assembled from its five
fields: the section-level cometric `g₀⁻¹` double trace `cometricDoubleTraceRecOp` (contracting the
leading two covariant slots against the cometric `g₀⁻¹`, NOT a chart-selected ambient basis), its exact
parallel single-step covariant Leibniz `cometricDoubleTraceRecOp_covGrad` (the cometric parallelism
`∇₀ g₀⁻¹ = 0`, carried through `castRankCc_db`), the order-uniform envelope constant `κ` (the squared
uniform cometric trace, `exists_uniform_cometricDoubleTraceRecOp_rfns_le`), and its single-value fibre
envelope (value-locality of the trace).  The contraction is **genuine** (non-degenerate): its envelope
`kappa = κ ≥ 0` is the value-local bound genuinely using the section. -/
noncomputable def cometricDoubleTraceContraction (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ (p + 2) p where
  op := fun a => cometricDoubleTraceRecOp (I := I) g₀ p a
  covGrad_op := fun a R => cometricDoubleTraceRecOp_covGrad (I := I) g₀ p a R
  kappa := (exists_uniform_cometricDoubleTraceRecOp_rfns_le (I := I) g₀ p).choose
  kappa_nonneg := (exists_uniform_cometricDoubleTraceRecOp_rfns_le (I := I) g₀ p).choose_spec.1
  rfns_op_le := fun a R x =>
    (exists_uniform_cometricDoubleTraceRecOp_rfns_le (I := I) g₀ p).choose_spec.2 a R x

/-- **The `(0, 6) → (0, 4)` cometric `g₀⁻¹` double-trace parallel rank-reducing contraction**
(`p = 4`).  The outer cometric double trace of the Lie-half P1b quadratic Rest arm's
double-cometric-trace jet analysis, contracting the two leading covariant slots of the rank-`6` operand
against the cometric `g₀⁻¹`. -/
noncomputable def cometricDoubleTraceContraction64 (g₀ : SmoothRiemannianMetric I M) :
    Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 6 4 :=
  cometricDoubleTraceContraction (I := I) g₀ 4

/-- **The `(0, 4) → (0, 2)` cometric `g₀⁻¹` double-trace parallel rank-reducing contraction**
(`p = 2`).  The inner cometric double trace of the Lie-half P1b quadratic Rest arm's
double-cometric-trace jet analysis, contracting the two leading covariant slots of the rank-`4` operand
against the cometric `g₀⁻¹`. -/
noncomputable def cometricDoubleTraceContraction42 (g₀ : SmoothRiemannianMetric I M) :
    Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2 :=
  cometricDoubleTraceContraction (I := I) g₀ 2

end Connection
end Integral
end DifferentialGeometry

end
