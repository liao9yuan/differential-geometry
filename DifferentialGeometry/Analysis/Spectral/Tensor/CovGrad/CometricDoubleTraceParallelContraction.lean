import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParallelRankReducingContractionGrid
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

end Connection
end Integral
end DifferentialGeometry

end
