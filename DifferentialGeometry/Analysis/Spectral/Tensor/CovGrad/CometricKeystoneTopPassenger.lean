import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricCrossContractionCalculus
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceCovariantSection
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionContractionTopRest
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct

/-! # The cometric keystone-top passenger cell and its sharp `δ²` fibre bound

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file delivers the **cometric `(0, 2)` keystone product-level top cell**
and its sharp `δ²` passenger fibre bound, mirroring at the smaller `(0, 2) ⊗ (0, 2)` arithmetic the
proven `(0, 3)` keystone of `CrossCorrectionParallelContraction`.

It also discharges the `∇₀`-parallelism of the fixed cometric double-trace operator field
`cometricCcOp` (`cometricCcOp_covGrad_eq_zero`), through the operator-field factorisation
`cometricCcOp = appCcRS (cometricDoubleTraceField g₀ (2 + a + b)) (cometricCcSourceReindex)`: the
rank-generic field is parallel (`cometricDoubleTraceField_covGrad_eq_zero`, the cometric `∇₀ g₀⁻¹ = 0`)
and the fixed source-rank reindex is parallel (a constant model rank cast).

## What this file provides

* `cometricCcOp_covGrad_eq_zero` — the `∇₀`-parallelism of the fixed cometric double-trace field.
* `cometricKeystoneTop` — the keystone product-level top cell: the `p`-fold slot-extended cometric
  operator on the slot-permuted bare product of the order-`p` jet factor `Z` with the realized
  symmetric perturbation `realizeSymm T₁`.
* `cometricKeystoneTop_rfns_le_sq_passenger` — the sharp `δ²` passenger fibre bound, uniform in `p`,
  built from the frame-Riesz slice reconstruction at the keystone contracted slot.

This is the inverse-Gram (cometric) keystone analog of the proven `(0, 3)` cross-correction keystone;
the reusable engines (`slotExtendPow`, `bareTensorRfnsBilinearProduct`, the operator-field calculus,
the frame Parseval) are shared, not rebuilt — only the `(0, 2)` slot arithmetic differs. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.Measure (chartModelBasis)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Gap 1 — the `∇₀`-parallelism of the fixed cometric double-trace operator field

Mirrors the proven `(0, 3)` `crossCorrCometricOp_covGrad_eq_zero` via the operator-field
factorisation `cometricCcOp = appCcRS (cometricDoubleTraceField g₀ (2 + a + b)) (cometricCcSourceReindex)`. -/

set_option linter.unusedSectionVars false in
/-- **`appCcRS` is zero on a zero contracted section** (file-local; the right-zero companion of
`appCcRS_zero_left`).  Fibrewise the operator post-composes with the zero fibre map. -/
private theorem appCcRS_zero_right (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    appCcRS (I := I) (M := M) g₀ a b c Φ 0 = 0 := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection (I := I) (M := M) g₀ a b c Φ 0 x]
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
  ext D
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero]

set_option linter.unusedVariables false in
/-- **The fixed cometric source-rank reindex operator field**
`(0, (2 + b) + (2 + a)) → (0, (2 + a + b) + 2)`, the pure `Nat`-rank reindex of the source covariant
slots along `(2 + b) + (2 + a) = (2 + a + b) + 2` (both `= 4 + a + b`), built fibrewise as
`equiv((2 + a + b) + 2).symm ∘ modelRankCast H ∘ equiv((2 + b) + (2 + a))`, frame-free. -/
private noncomputable def cometricCcSourceReindexFib (g₀ : SmoothRiemannianMetric I M) (a b : ℕ)
    (x : M) :
    Tensor0SBundle.TensorRSSpace ((2 + b) + (2 + a)) ((2 + a + b) + 2) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) ((2 + a + b) + 2) x).symm.toContinuousLinearMap.comp
    ((modelRankCast (E := E)
        (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) ((2 + b) + (2 + a)) x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- `toModel` of the cometric source reindex is the model rank cast. -/
private theorem cometricCcSourceReindexFib_toModel (g₀ : SmoothRiemannianMetric I M) (a b : ℕ)
    (x : M) (P : Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (cometricCcSourceReindexFib (I := I) g₀ a b x P) =
      modelRankCast (E := E) (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel P) := rfl

private theorem cometricCcSourceReindexFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel ((2 + b) + (2 + a)) ((2 + a + b) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel ((2 + b) + (2 + a)) ((2 + a + b) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace ((2 + b) + (2 + a)) ((2 + a + b) + 2) I z) x
        (cometricCcSourceReindexFib (I := I) g₀ a b x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel ((2 + a + b) + 2) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I x)
    (φ := fun x => cometricCcSourceReindexFib (I := I) g₀ a b x)
  intro Y
  exact (tensor0SField_castRank_contMDiff
    (I := I) (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2) (fun x => Y x) Y.contMDiff).congr
    (fun x => rfl)

/-- **The fixed cometric source-rank reindex operator field** as a `SmoothCcTensor`. -/
private noncomputable def cometricCcSourceReindex (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    SmoothCcTensor g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2) where
  toSection :=
    { toFun := fun x : M => cometricCcSourceReindexFib (I := I) g₀ a b x
      contMDiff_toFun := cometricCcSourceReindexFib_contMDiff (I := I) g₀ a b }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The cometric double-trace operator field factors as the rank-generic double-trace field after
the source reindex.**  Fibrewise the single cometric trace `cometricCcOpFib` is
`cometricDoubleTraceFib g₀ (2 + a + b)` post-composed after the source reindex (both `toModel`-equal
`modelDoubleTrace (2 + a + b) (cometricLmodel) ∘ modelRankCast H`). -/
private theorem cometricCcOp_eq_appCcRS_cometricDoubleTraceField (g₀ : SmoothRiemannianMetric I M)
    (a b : ℕ) :
    cometricCcOp (I := I) g₀ a b =
      appCcRS (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2) (2 + a + b)
        (cometricDoubleTraceField (I := I) g₀ (2 + a + b)) (cometricCcSourceReindex (I := I) g₀ a b) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro P
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
      ((cometricCcOp (I := I) g₀ a b).toSection x P) =
      modelDoubleTrace (E := E) (2 + a + b) (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2) (Tensor0SBundle.Tensor0SSpace.toModel P)) :=
    cometricCcOpFib_toModel (I := I) g₀ a b x P
  have hR : Tensor0SBundle.Tensor0SSpace.toModel
      ((appCcRS (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2) (2 + a + b)
          (cometricDoubleTraceField (I := I) g₀ (2 + a + b))
          (cometricCcSourceReindex (I := I) g₀ a b)).toSection x P) =
      modelDoubleTrace (E := E) (2 + a + b) (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2) (Tensor0SBundle.Tensor0SSpace.toModel P)) := by
    rw [appCcRS_toSection (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2) (2 + a + b)
      (cometricDoubleTraceField (I := I) g₀ (2 + a + b)) (cometricCcSourceReindex (I := I) g₀ a b) x,
      ContinuousLinearMap.comp_apply]
    change Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₀ (2 + a + b) x
          (cometricCcSourceReindexFib (I := I) g₀ a b x P)) = _
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ (2 + a + b) x
        (cometricCcSourceReindexFib (I := I) g₀ a b x P),
      cometricCcSourceReindexFib_toModel (I := I) g₀ a b x P]
  exact hL.trans hR.symm

set_option linter.unusedSectionVars false in
/-- **The fixed cometric source-rank reindex operator field is `∇₀`-parallel.**  The reindex is a fixed
slot relabelling of the operator's source covariant slots (the model `modelRankCast` along a `Nat`-rank
equality), carrying NO cometric and independent of the metric jets, so its covariant gradient
vanishes. -/
private theorem cometricCcSourceReindex_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    covGrad (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2)
        (cometricCcSourceReindex (I := I) g₀ a b) = 0 := by
  classical
  have hnat : ∀ {m n : ℕ} (h : m = n) (w : ∀ y : M, Tensor0SBundle.Tensor0SSpace m I y) (x : M) (v : E),
      (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g₀))
          (fun y : M => Tensor0SBundle.Tensor0SSpace.ofModel
            (modelRankCast (E := E) h (Tensor0SBundle.Tensor0SSpace.toModel (w y)))) x v =
        Tensor0SBundle.Tensor0SSpace.ofModel
          (modelRankCast (E := E) h
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g₀)) w x v))) := by
    intro m n h w x v
    subst h
    simp only [modelRankCast_refl, Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  have hΦval : ∀ (y : M) (P : Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I y),
      (show Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I y →L[ℝ]
          Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I y from
        (cometricCcSourceReindex (I := I) g₀ a b).toSection y) P =
        Tensor0SBundle.Tensor0SSpace.ofModel
          (modelRankCast (E := E)
            (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
            (Tensor0SBundle.Tensor0SSpace.toModel P)) := by
    intro y P
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    exact cometricCcSourceReindexFib_toModel (I := I) g₀ a b y P
  have hdir : ∀ (x : M) (v : E),
      tensorCovDerivAt (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2)
        (cometricCcSourceReindex (I := I) g₀ a b) x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I y) (n := (⊤ : ℕ∞)) x D
    rw [tensorCovDerivAt_def (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2)
        (cometricCcSourceReindex (I := I) g₀ a b) x v, ContinuousLinearMap.zero_apply, ← hw]
    rw [TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) ((2 + b) + (2 + a))
      ((2 + a + b) + 2) (LeviCivita (I := I) g₀) (cometricCcSourceReindex (I := I) g₀ a b).toSection
      w x v]
    rw [show (fun y : M =>
          (show Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I y →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I y from
            (cometricCcSourceReindex (I := I) g₀ a b).toSection y) (w y)) =
        (fun y : M => Tensor0SBundle.Tensor0SSpace.ofModel
          (modelRankCast (E := E)
            (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
            (Tensor0SBundle.Tensor0SSpace.toModel (w y)))) from funext (fun y => hΦval y (w y))]
    rw [hnat (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2) (fun y => w y) x v]
    rw [hΦval x ((Tensor0SNabla.tensor0SCovariantDerivative I M ((2 + b) + (2 + a))
      (LeviCivita (I := I) g₀)) (fun y => w y) x v)]
    rw [sub_self]
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g₀
      ((2 + b) + (2 + a)) ((2 + a + b) + 2) (cometricCcSourceReindex (I := I) g₀ a b) x D m,
    hdir x (m 0), ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

/-- **The fixed cometric double-trace operator field is `∇₀`-parallel.**
`covGrad g₀ ((2 + b) + (2 + a)) (2 + a + b) (cometricCcOp g₀ a b) = 0`.  Through the operator-field
factorisation `cometricCcOp = appCcRS (cometricDoubleTraceField g₀ (2 + a + b)) (cometricCcSourceReindex)`,
the operator-field B-rule `covGrad_appCcRS_eq` splits the gradient into the rank-generic field's gradient
(zero by `cometricDoubleTraceField_covGrad_eq_zero`, the cometric `∇₀ g₀⁻¹ = 0`) post-composed after the
reindex, plus the slot-extended field post-composed after the reindex's gradient (zero by
`cometricCcSourceReindex_covGrad_eq_zero`). -/
theorem cometricCcOp_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    covGrad (I := I) (M := M) g₀ ((2 + b) + (2 + a)) (2 + a + b)
        (cometricCcOp (I := I) g₀ a b) = 0 := by
  rw [cometricCcOp_eq_appCcRS_cometricDoubleTraceField (I := I) g₀ a b]
  rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2) (2 + a + b)
    (cometricDoubleTraceField (I := I) g₀ (2 + a + b)) (cometricCcSourceReindex (I := I) g₀ a b),
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ (2 + a + b),
    appCcRS_zero_left (I := I) (M := M) g₀ ((2 + b) + (2 + a)) ((2 + a + b) + 2) ((2 + a + b) + 1)
      (cometricCcSourceReindex (I := I) g₀ a b), zero_add,
    cometricCcSourceReindex_covGrad_eq_zero (I := I) g₀ a b,
    appCcRS_zero_right (I := I) (M := M) g₀ ((2 + b) + (2 + a)) (((2 + a + b) + 2) + 1) ((2 + a + b) + 1)
      (slotExtend (I := I) (M := M) g₀ ((2 + a + b) + 2) (2 + a + b)
        (cometricDoubleTraceField (I := I) g₀ (2 + a + b)))]

/-! ## Gap 2 — slot/curry/frame infrastructure (file-local, the `(0, 2)` rebuilds)

These reproduce, at the cometric `(0, 2) ⊗ (0, 2)` arithmetic, the private slot/curry/frame helpers
that the `(0, 3)` keystone of `CrossCorrectionParallelContraction` uses (those are `private`; the
generic engines they build on — `slotExtendFib_apply_eval`, `tensor0S_curry`, `covGrad_permuteCcTensor`,
`riemannianFiberNormSq_eq_sum_componentS_sq`, the cometric frame Parseval — are public). -/

/-- **The leading-identity extension of a slot permutation by `p` gradient slots.** -/
private def leadExtPerm {s : ℕ} (σ : Equiv.Perm (Fin s)) : ∀ p : ℕ, Equiv.Perm (Fin (s + p))
  | 0 => σ
  | (p + 1) => Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p)

set_option linter.unusedSectionVars false in
/-- The lead-extended permutation fixes the leading `p` (gradient) slots. -/
private lemma leadExtPerm_apply_of_lt {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    ∀ (p : ℕ) (k : Fin (s + p)), k.val < p → leadExtPerm σ p k = k := by
  intro p
  induction p with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ p ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
    · have hk' : k = (0 : Fin ((s + p) + 1)) := Fin.ext hk0
      rw [hk']
      change (Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p)) (0 : Fin ((s + p) + 1)) = _
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    · have hk' : k = Fin.succ (⟨k.val - 1, by omega⟩ : Fin (s + p)) :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [hk']
      change (Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p))
          (Fin.succ (⟨k.val - 1, by omega⟩ : Fin (s + p))) = _
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
      rw [ih ⟨k.val - 1, by omega⟩ (by change k.val - 1 < p; omega)]

set_option linter.unusedSectionVars false in
/-- The lead-extended permutation on the `natAdd p`-block applies `σ` (shifted by `p`). -/
private lemma leadExtPerm_apply_natAdd {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    ∀ (p : ℕ) (j : Fin s),
      leadExtPerm σ p (Fin.cast (by omega : p + s = s + p) (Fin.natAdd p j)) =
        Fin.cast (by omega : p + s = s + p) (Fin.natAdd p (σ j)) := by
  intro p
  induction p with
  | zero =>
    intro j
    rw [show (Fin.cast (by omega : 0 + s = s + 0) (Fin.natAdd 0 j)) = (j : Fin (s + 0)) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
    change σ j = _
    exact Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)
  | succ p ih =>
    intro j
    rw [show (Fin.cast (by omega : (p + 1) + s = s + (p + 1)) (Fin.natAdd (p + 1) j))
        = Fin.succ (Fin.cast (by omega : p + s = s + p) (Fin.natAdd p j)) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega)]
    change (Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p)) (Fin.succ _) = _
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, ih j]
    exact Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega)

set_option linter.unusedSectionVars false in
/-- **The covariant gradient commutes with a slot permutation** (file-local).
`∇(permute σ R) = permute (decomposeFin.symm (0, σ)) (∇R)`. -/
private theorem covGrad_permuteCcTensor_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (R : Integral.L2.SmoothCcTensor g₀ 0 s) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s + 1)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s
    (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R) x
    (Integral.Connection.unitZeroSec (I := I) (M := M) x) m]
  have hnat : Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 s
              (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R) x (m 0))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 s R x (m 0))
            (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_unit_toModel_domDomCongr_of_section
      (I := I) (M := M) g₀ s σ R (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R)
      (fun y => PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ R y) x (m 0)
  rw [hnat, ContinuousMultilinearMap.domDomCongr_apply]
  have hR : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ))
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R) x
  rw [hR, ContinuousMultilinearMap.domDomCongr_apply]
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s
    R x (Integral.Connection.unitZeroSec (I := I) (M := M) x)
    (fun k => m ((Equiv.Perm.decomposeFin.symm (0, σ)) k))]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have htail : Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
      fun j : Fin s => Matrix.vecTail m (σ j) := by
    funext j
    change m ((Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.succ j)) = m (Fin.succ (σ j))
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  rw [htail]

set_option linter.unusedSectionVars false in
/-- **The iterated covariant gradient commutes with a slot permutation**:
`∇^p (permuteCcTensor σ W) = permuteCcTensor (leadExtPerm σ p) (∇^p W)`. -/
private theorem iteratedCovGrad_permuteCcTensor_eq (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : Integral.L2.SmoothCcTensor g₀ 0 s) (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s p
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ W) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σ p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s p W) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [PDE.RicciFlow.iteratedCovGrad_succ, ih,
      covGrad_permuteCcTensor_local (I := I) g₀ (leadExtPerm σ p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s p W),
      PDE.RicciFlow.iteratedCovGrad_succ]
    rfl

/-- **The `p`-fold leading-slot curry of a `(0, r + p)`-fibre tensor** (file-local; matches the
`slotExtendPow` recursion order, newest-passenger first). -/
private noncomputable def passengerCurry (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (x : M) :
    ∀ (p : ℕ), Tensor0SBundle.Tensor0SSpace (r + p) I x → (Fin p → E) →
      Tensor0SBundle.Tensor0SSpace r I x
  | 0, D, _ => D
  | (p + 1), D, q =>
      passengerCurry g₀ r x p
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
          (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
        (fun j : Fin p => q (Fin.succ j))

set_option linter.unusedSectionVars false in
/-- The model value of the `p`-fold passenger curry reads the inner tensor on the appended tuple. -/
private lemma passengerCurry_toModel (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (x : M) :
    ∀ (p : ℕ) (D : Tensor0SBundle.Tensor0SSpace (r + p) I x) (q : Fin p → E) (w : Fin r → E),
      Tensor0SBundle.Tensor0SSpace.toModel (passengerCurry (I := I) (M := M) g₀ r x p D q) w =
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Matrix.vecAppend (by omega : r + p = p + r) q w) := by
  intro p
  induction p with
  | zero =>
    intro D q w
    change Tensor0SBundle.Tensor0SSpace.toModel D w = _
    congr 1
    funext k
    rw [Matrix.vecAppend_eq_ite]
    simp only [Nat.not_lt_zero, dif_neg, not_false_iff]
    apply congrArg
    apply Fin.ext
    simp
  | succ p ih =>
    intro D q w
    rw [show passengerCurry (I := I) (M := M) g₀ r x (p + 1) D q
        = passengerCurry (I := I) (M := M) g₀ r x p
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
              (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
            (fun j : Fin p => q (Fin.succ j)) from rfl]
    rw [ih ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
        (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
      (fun j : Fin p => q (Fin.succ j)) w]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0)
      (Matrix.vecAppend (by omega : r + p = p + r) (fun j : Fin p => q (Fin.succ j)) w)]
    congr 1
    funext k
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [Fin.cons_zero]
      exact (Matrix.vecAppend_apply_zero (by omega : r + (p + 1) = (p + 1) + r) q w).symm
    · rw [Fin.cons_succ]
      rw [Matrix.vecAppend_eq_ite, Matrix.vecAppend_eq_ite]
      simp only [Fin.val_succ]
      by_cases hk : (k' : ℕ) < p
      · rw [dif_pos hk, dif_pos (by omega)]
        apply congrArg
        apply Fin.ext
        simp
      · rw [dif_neg hk, dif_neg (by omega)]
        apply congrArg
        simp only [Fin.mk.injEq]
        omega

set_option linter.unusedSectionVars false in
/-- **The `p`-fold slot extension reads its `p` leading slots as passengers** (file-local, against the
public `slotExtendPow`). -/
private theorem slotExtendPow_toModel_consSlots (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s) :
    ∀ (p : ℕ) (D : Tensor0SBundle.Tensor0SSpace (r + p) I x) (q : Fin p → E) (vs : Fin s → E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace (r + p) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (s + p) I x from
              (slotExtendPow (I := I) (M := M) g₀ r s p Φ).toSection x) D)
          (Matrix.vecAppend (by omega : s + p = p + s) q vs) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              Φ.toSection x)
            (passengerCurry (I := I) (M := M) g₀ r x p D q)) vs := by
  intro p
  induction p with
  | zero =>
    intro D q vs
    change Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          Φ.toSection x) D) (Matrix.vecAppend (by omega : s + 0 = 0 + s) q vs) = _
    congr 1
    funext k
    rw [Matrix.vecAppend_eq_ite]
    simp only [Nat.not_lt_zero, dif_neg, not_false_iff]
    apply congrArg
    apply Fin.ext
    simp
  | succ p ih =>
    intro D q vs
    set m : Fin ((s + p) + 1) → E :=
      (Matrix.vecAppend (by omega : s + (p + 1) = (p + 1) + s) q vs :
        Fin (s + (p + 1)) → E) with hm_def
    have hm0 : m 0 = q 0 := by
      rw [hm_def]
      exact Matrix.vecAppend_apply_zero (by omega : s + (p + 1) = (p + 1) + s) q vs
    have hmtail : Matrix.vecTail m
        = Matrix.vecAppend (by omega : s + p = p + s) (fun j : Fin p => q (Fin.succ j)) vs := by
      funext k
      have hL : Matrix.vecTail m k = m k.succ := rfl
      rw [hL, hm_def]
      rw [Matrix.vecAppend_eq_ite (by omega : s + (p + 1) = (p + 1) + s) q vs,
        Matrix.vecAppend_eq_ite (by omega : s + p = p + s) (fun j : Fin p => q (Fin.succ j)) vs]
      simp only []
      by_cases hk : (k : ℕ) < p
      · rw [dif_pos (by simpa [Fin.val_succ] using hk : (k.succ : ℕ) < p + 1), dif_pos hk]
        apply congrArg
        apply Fin.ext
        simp [Fin.val_succ]
      · rw [dif_neg (by simpa [Fin.val_succ] using hk : ¬ (k.succ : ℕ) < p + 1), dif_neg hk]
        apply congrArg
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
    rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
    rw [hm0]
    rw [show Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace (r + (p + 1)) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (s + (p + 1)) I x from
              (slotExtendPow (I := I) (M := M) g₀ r s (p + 1) Φ).toSection x) D)
            (Fin.cons (q 0) (Matrix.vecTail m))
        = Tensor0SBundle.Tensor0SSpace.toModel
            (slotExtendFib (I := I) (M := M) g₀ (r + p) (s + p) x
              (show Tensor0SBundle.Tensor0SSpace (r + p) I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (s + p) I x from
                (slotExtendPow (I := I) (M := M) g₀ r s p Φ).toSection x) D)
            (Fin.cons (q 0) (Matrix.vecTail m)) from rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ (r + p) (s + p) x
      (show Tensor0SBundle.Tensor0SSpace (r + p) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + p) I x from
        (slotExtendPow (I := I) (M := M) g₀ r s p Φ).toSection x)
      D (q 0) (Matrix.vecTail m)]
    rw [hmtail]
    rw [show passengerCurry (I := I) (M := M) g₀ r x (p + 1) D q
          = passengerCurry (I := I) (M := M) g₀ r x p
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
                (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
              (fun j : Fin p => q (Fin.succ j)) from rfl]
    exact ih ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
        (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
      (fun j : Fin p => q (Fin.succ j)) vs

set_option linter.unusedSectionVars false in
/-- **The dual-frame squared sum operator bound** (file-local).  For a `g₀`-orthonormal frame `e` with
Parseval, a fibre bilinear field `h` with `gFibreOpBound h δ`, and any `u`,
`∑_k h(u, e_k)² ≤ δ² · g₀(u, u)`. -/
private lemma gFibreOpBound_dualFrame_sq_sum_le
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) g₀ h δ) (u : TangentSpace I x) :
    ∑ k : Fin n, (h x u (e k)) ^ 2 ≤ δ ^ 2 * g₀.inner x u u := by
  classical
  set Q : ℝ := ∑ k : Fin n, (h x u (e k)) ^ 2 with hQ_def
  set P : TangentSpace I x := ∑ k : Fin n, (h x u (e k)) • e k with hP_def
  have hhuP : h x u P = Q := by
    rw [hP_def, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [hQ_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [sq]
  have hcoord : ∀ k : Fin n, g₀.inner x (e k) P = h x u (e k) := by
    intro k
    rw [hP_def, map_sum]
    rw [Finset.sum_eq_single k]
    · rw [ContinuousLinearMap.map_smul, smul_eq_mul, horth k k, if_pos rfl, mul_one]
    · intro l _ hl
      rw [ContinuousLinearMap.map_smul, smul_eq_mul, horth k l, if_neg (fun he => hl he.symm),
        mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hPP : g₀.inner x P P = Q := by
    rw [← hpars P, hQ_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoord k]
  have hQnn : 0 ≤ Q := by
    rw [hQ_def]; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have huu_nn : 0 ≤ g₀.inner x u u :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  have hbound : Q ≤ δ * Real.sqrt (g₀.inner x u u) * Real.sqrt Q := by
    have hb := hδ x u P
    rw [hhuP, hPP] at hb
    calc Q = |Q| := (abs_of_nonneg hQnn).symm
      _ ≤ δ * Real.sqrt (g₀.inner x u u) * Real.sqrt Q := hb
  rcases eq_or_lt_of_le hQnn with hQ0 | hQpos
  · rw [← hQ0]; positivity
  · have hsqQ_pos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
    have hQ_sqrt : Q = Real.sqrt Q * Real.sqrt Q := (Real.mul_self_sqrt hQnn).symm
    have hstep : Real.sqrt Q ≤ δ * Real.sqrt (g₀.inner x u u) := by
      have hb2 : Real.sqrt Q * Real.sqrt Q ≤ (δ * Real.sqrt (g₀.inner x u u)) * Real.sqrt Q := by
        rw [← hQ_sqrt]; linarith [hbound]
      exact le_of_mul_le_mul_right hb2 hsqQ_pos
    have hsqrtuu : Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x u u) = g₀.inner x u u :=
      Real.mul_self_sqrt huu_nn
    have hstep_nn : 0 ≤ δ * Real.sqrt (g₀.inner x u u) :=
      le_trans (Real.sqrt_nonneg Q) hstep
    calc Q = Real.sqrt Q * Real.sqrt Q := hQ_sqrt
      _ ≤ (δ * Real.sqrt (g₀.inner x u u)) * (δ * Real.sqrt (g₀.inner x u u)) :=
          mul_le_mul hstep hstep (Real.sqrt_nonneg _) hstep_nn
      _ = δ ^ 2 * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x u u)) := by ring
      _ = δ ^ 2 * g₀.inner x u u := by rw [hsqrtuu]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **Frame-Riesz reconstruction pair and norm** (file-local).  The frame-reconstructed vector
`W = ∑_c ψ(e_c) • e_c` pairs as `g₀(W, ·) = ψ` and has `g₀(W, W) = ∑_c ψ(e_c)²`. -/
private lemma frameRiesz_pair_and_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hexpand : ∀ v : TangentSpace I x, v = ∑ i : Fin n, g₀.inner x (e i) v • e i)
    (ψ : TangentSpace I x →L[ℝ] ℝ) :
    (∀ u : TangentSpace I x,
        g₀.inner x (∑ c : Fin n, ψ (e c) • e c) u = ψ u) ∧
      g₀.inner x (∑ c : Fin n, ψ (e c) • e c) (∑ c : Fin n, ψ (e c) • e c)
        = ∑ c : Fin n, (ψ (e c)) ^ 2 := by
  classical
  set W : TangentSpace I x := ∑ c : Fin n, ψ (e c) • e c with hW_def
  have hpair : ∀ u : TangentSpace I x, g₀.inner x W u = ψ u := by
    intro u
    rw [hW_def]
    rw [map_sum (g₀.inner x) (fun c : Fin n => ψ (e c) • e c) Finset.univ,
      ContinuousLinearMap.sum_apply]
    rw [show (∑ c : Fin n, (g₀.inner x (ψ (e c) • e c)) u) = ∑ c : Fin n, ψ (e c) * g₀.inner x (e c) u
        from by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_smul (g₀.inner x) (ψ (e c)) (e c), ContinuousLinearMap.smul_apply, smul_eq_mul]]
    conv_rhs => rw [hexpand u, map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_smul, smul_eq_mul, g₀.symm x (e c) u, mul_comm]
  refine ⟨hpair, ?_⟩
  rw [hpair W, hW_def, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_smul, smul_eq_mul, sq]

set_option linter.unusedSectionVars false in
/-- **The rank-`0` frame component reads a `(0, s)` operator at the canonical unit** (file-local). -/
private theorem componentS_zero_eq_unit_local (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n)
    (op : Tensor0SBundle.TensorRSSpace 0 s I x) :
    Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 s op n e K₀ J =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from op)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (fun k => e (J k)) := by
  classical
  have hcoframe :
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g₀.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
    apply Tensor0SBundle.tensor0SSpace_ext
    intro v
    rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g₀.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
        Integral.Connection.coframeS (I := I) (M := M) g₀ x 0 e K₀ from rfl,
      Integral.Connection.coframeS_apply, Finset.prod_of_isEmpty]
    rfl
  unfold Integral.Connection.fiberNormSqComponent
  rw [hcoframe]
  rw [Tensor0SBundle.Tensor0SSpace.toModel, Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  rfl

/-! ## Gap 2 — the cometric keystone product-level top cell and its sharp `δ²` passenger bound -/

/-- **The cometric keystone product-level top cell of the order-`p` cometric cross-correction covariant
jet.**  The `i = 0` binomial cell of the operator-reduced covariant Leibniz of the parallel cometric
contraction `h ⌟ D` at the `(0, 2) ⊗ (0, 2)` arithmetic: the `p`-fold slot-extended cometric operator
(`slotExtendPow p (cometricCcOp g₀ 0 0)`) applied to the slot-permuted bare product of the order-`p` jet
factor `Z` (in the contraction's original `D`-slot layout, the `p` gradient directions riding as
spectators) with the realized symmetric perturbation `realizeSymm T₁`.  This is the cometric analog of
the proven `(0, 3)` `crossCorrKeystoneTop`. -/
noncomputable def cometricKeystoneTop (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (Z : Integral.L2.SmoothCcTensor g₀ 0 (2 + p)) :
    Integral.L2.SmoothCcTensor g₀ 0 (2 + p) :=
  appCcRS (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p) ((2 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) p
      (cometricCcOp (I := I) g₀ 0 0))
    (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (cometricCcPerm 0 0) p)
      (castRankCc_db g₀ 0 (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p)
        ((bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod (a := 0 + p) (b := 0)
          (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
          (realizeSymmCcTensor (I := I) g₀ T₁))))

set_option linter.unusedSectionVars false in
/-- Concrete values of the `(a, b) = (0, 0)` cometric cross slot permutation on `Fin 4`. -/
private lemma cometricCcPerm00_val (j : Fin ((2 + 0) + (2 + 0))) :
    ((cometricCcPerm 0 0) j).val =
      if j.val < 2 then 1 + j.val else if j.val = 2 then 0 else 3 := by
  by_cases h2 : j.val < 2
  · rw [show j = Fin.castAdd (2 + 0) (⟨j.val, h2⟩ : Fin (2 + 0)) from Fin.ext rfl,
      cometricCcPerm_castAdd 0 0]
    simp only [Fin.val_castAdd]
    rw [if_pos h2]
  · have hjlt : j.val < 4 := j.isLt
    rw [show j = Fin.natAdd (2 + 0) (⟨j.val - 2, by omega⟩ : Fin (2 + 0)) from
      Fin.ext (by simp only [Fin.val_natAdd]; omega),
      cometricCcPerm_natAdd 0 0]
    simp only [Fin.val_natAdd]
    by_cases h3 : j.val - 2 = 0
    · rw [if_pos h3, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h3, if_neg (by omega), if_neg (by omega)]
      omega

set_option linter.unusedSectionVars false in
/-- Defining evaluation of the `modelRankCast` model rank cast (file-local). -/
private lemma modelRankCast_apply_local {m n : ℕ} (h : m = n)
    (T : Tensor0SBundle.Tensor0SModel m ℝ E) (v : Fin n → E) :
    modelRankCast (E := E) h T v = T (fun i => v (finCongr h i)) := by
  change (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T v = _
  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T
      = ContinuousMultilinearMap.domDomCongr (finCongr h) T from rfl,
    ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
/-- The unit-model value of a rank-cast section reads the original on the cast tuple (file-local). -/
private lemma unitModel_castRankCc_db_local (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ 0 a) (x : M) (v : Fin b → TangentSpace I x) :
    Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ b
        (castRankCc_db g₀ 0 h W) x v =
      Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ a W x
        (fun i => v (Fin.cast h i)) := by
  subst h
  rfl

set_option linter.unusedSectionVars false in
/-- The model image of the cometric double-trace operator section value (file-local). -/
private lemma cometricCcOp_toSection_toModel (g₀ : SmoothRiemannianMetric I M) (a b : ℕ)
    (x : M) (P : Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + a + b) I x from
          (cometricCcOp (I := I) g₀ a b).toSection x) P) =
      modelDoubleTrace (E := E) (2 + a + b) (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel P)) := rfl

set_option linter.unusedSectionVars false in
/-- Evaluation of `vecAppend q w` below the passenger threshold (file-local). -/
private lemma vecAppend_lt_eval {α : Type*} {r p : ℕ} (q : Fin p → α) (w : Fin r → α)
    (k : Fin (r + p)) (hk : k.val < p) :
    Matrix.vecAppend (by omega : r + p = p + r) q w k = q ⟨k.val, hk⟩ := by
  simp only [Matrix.vecAppend_eq_ite]
  rw [dif_pos hk]

set_option linter.unusedSectionVars false in
/-- Evaluation of `vecAppend q w` on the `w`-block (file-local). -/
private lemma vecAppend_natAdd_eval {α : Type*} {r p : ℕ} (q : Fin p → α) (w : Fin r → α)
    (j : Fin r) :
    Matrix.vecAppend (by omega : r + p = p + r) q w
        (Fin.cast (by omega : p + r = r + p) (Fin.natAdd p j)) = w j := by
  simp only [Matrix.vecAppend_eq_ite]
  rw [dif_neg (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
  apply congrArg
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd]
  omega

set_option linter.unusedSectionVars false in
/-- Leading-slot evaluation of the double-`cons` model tuple (file-local). -/
private lemma consPair_eval_zero {s2 : ℕ} (A B : E) (m : Fin s2 → E) (i : Fin (s2 + 2))
    (hi : i.val = 0) :
    (Fin.cons A (Fin.cons B m) : Fin (s2 + 2) → E) i = A := by
  rw [show i = (0 : Fin (s2 + 2)) from Fin.ext (by rw [Fin.val_zero]; exact hi)]
  rw [show (0 : Fin (s2 + 2)) = (0 : Fin ((s2 + 1) + 1)) from rfl, Fin.cons_zero]

set_option linter.unusedSectionVars false in
/-- Second-slot evaluation of the double-`cons` model tuple (file-local). -/
private lemma consPair_eval_one {s2 : ℕ} (A B : E) (m : Fin s2 → E) (i : Fin (s2 + 2))
    (hi : i.val = 1) :
    (Fin.cons A (Fin.cons B m) : Fin (s2 + 2) → E) i = B := by
  rw [show i = Fin.succ (0 : Fin (s2 + 1)) from Fin.ext (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
  rw [Fin.cons_succ, Fin.cons_zero]

set_option linter.unusedSectionVars false in
/-- Tail evaluation of the double-`cons` model tuple (file-local). -/
private lemma consPair_eval_tail {s2 : ℕ} (A B : E) (m : Fin s2 → E) (i : Fin (s2 + 2))
    (l : Fin s2) (hi : i.val = 2 + l.val) :
    (Fin.cons A (Fin.cons B m) : Fin (s2 + 2) → E) i = m l := by
  rw [show i = Fin.succ (Fin.succ l) from Fin.ext (by simp only [Fin.val_succ]; omega)]
  rw [Fin.cons_succ, Fin.cons_succ]

set_option linter.unusedSectionVars false in
/-- The unit-model value of the keystone's slot-permuted bare-product argument: the `Z`-factor reads the
(val-identity) leading `2 + p` product slots through the keystone permutation, the realized-perturbation
factor the trailing `2`. -/
private lemma keystoneArg_unit_toModel (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (T₁ : SmoothCcTensor g₀ 0 2) (Z : SmoothCcTensor g₀ 0 ((2 + 0) + p)) (x : M)
    (u : Fin (((2 + 0) + (2 + 0)) + p) → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (((2 + 0) + (2 + 0)) + p) I x from
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (cometricCcPerm 0 0) p)
            (castRankCc_db g₀ 0 (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p)
              ((bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod (a := 0 + p) (b := 0)
                (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
                (realizeSymmCcTensor (I := I) g₀ T₁)))).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        u =
      cometricCcUnitModel (I := I) g₀ Z x
          (fun t : Fin ((2 + 0) + p) =>
            u (leadExtPerm (cometricCcPerm 0 0) p
              (⟨t.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p)))) *
        cometricCcUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
          (fun l : Fin (2 + 0) =>
            u (leadExtPerm (cometricCcPerm 0 0) p
              (⟨((2 + 0) + p) + l.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p)))) := by
  classical
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (((2 + 0) + (2 + 0)) + p) I x from
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (cometricCcPerm 0 0) p)
            (castRankCc_db g₀ 0 (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p)
              ((bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod (a := 0 + p) (b := 0)
                (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
                (realizeSymmCcTensor (I := I) g₀ T₁)))).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      = Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ (((2 + 0) + (2 + 0)) + p)
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (cometricCcPerm 0 0) p)
            (castRankCc_db g₀ 0 (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p)
              ((bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod (a := 0 + p) (b := 0)
                (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
                (realizeSymmCcTensor (I := I) g₀ T₁)))) x from rfl]
  rw [permuteCcTensor_unitModel (I := I) g₀ (leadExtPerm (cometricCcPerm 0 0) p) _ x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel_castRankCc_db_local (I := I) g₀
    (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p) _ x]
  rw [show (bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod (a := 0 + p) (b := 0)
        (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
        (realizeSymmCcTensor (I := I) g₀ T₁)
      = castRankCc_db g₀ 0 (by omega : (2 + (0 + p)) + (2 + 0) = (2 + 2) + (0 + p) + 0)
          (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) g₀
            (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
            (realizeSymmCcTensor (I := I) g₀ T₁)) from rfl]
  rw [unitModel_castRankCc_db_local (I := I) g₀
    (by omega : (2 + (0 + p)) + (2 + 0) = (2 + 2) + (0 + p) + 0) _ x]
  rw [Analysis.Parabolic.TensorSpectral.unitModelProdSection_unitModel (I := I) g₀
    (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
    (realizeSymmCcTensor (I := I) g₀ T₁) x]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [unitModel_castRankCc_db_local (I := I) g₀ (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z x]
  rw [show Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ ((2 + 0) + p) Z x
      = cometricCcUnitModel (I := I) g₀ Z x from rfl]
  rw [show Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ (2 + 0)
        (realizeSymmCcTensor (I := I) g₀ T₁) x
      = cometricCcUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x from rfl]
  congr 1
  congr 1
  funext t
  refine congrArg u (congrArg (leadExtPerm (cometricCcPerm 0 0) p) (Fin.ext ?_))
  simp only [Fin.val_cast, Fin.val_natAdd]
  omega

set_option linter.unusedSectionVars false in
/-- Last-slot grouping of a `Fin ((2 + 0 + 0) + p)` index sum (file-local). -/
private lemma sum_index_lastSlot_group' {n p : ℕ} (f : (Fin ((2 + 0 + 0) + p) → Fin n) → ℝ) :
    (∑ J : Fin ((2 + 0 + 0) + p) → Fin n, f J) =
      ∑ c : Fin n, ∑ J' : Fin (1 + p) → Fin n,
        f (fun k : Fin ((2 + 0 + 0) + p) =>
          (Fin.snoc J' c : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1) k)) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((Fin.snocEquiv (fun _ : Fin ((1 + p) + 1) => Fin n)).trans
      (Equiv.arrowCongr (finCongr (by omega : (1 + p) + 1 = (2 + 0 + 0) + p)) (Equiv.refl (Fin n))))
    _ _ ?_).symm
  intro pr
  simp only [Equiv.trans_apply, finCongr_apply]
  congr 1

set_option linter.unusedSectionVars false in
/-- Middle-slot (position `p`) grouping of a `Fin ((2 + 0) + p)` index sum (file-local). -/
private lemma sum_index_midSlot_group {n p : ℕ} (f : (Fin ((2 + 0) + p) → Fin n) → ℝ) :
    (∑ J : Fin ((2 + 0) + p) → Fin n, f J) =
      ∑ c : Fin n, ∑ J' : Fin (1 + p) → Fin n,
        f (fun k : Fin ((2 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) c J' : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((Fin.insertNthEquiv (fun _ : Fin ((1 + p) + 1) => Fin n) ⟨p, by omega⟩).trans
      (Equiv.arrowCongr (finCongr (by omega : (1 + p) + 1 = (2 + 0) + p)) (Equiv.refl (Fin n))))
    _ _ ?_).symm
  intro pr
  simp only [Equiv.trans_apply, finCongr_apply]
  congr 1

set_option linter.unusedSectionVars false in
/-- The keystone `Z`-factor tuple identity: through the lead-extended cometric permutation, the
bare-product `Z`-block reads the passenger slots, the model-basis vector in the contracted
(position-`p`) slot, and the one following frame slot — the `insertNth` slice tuple. -/
private lemma keystone_tupleZ_eval (x : M) {nn p : ℕ} (e : Fin nn → TangentSpace I x)
    (J : Fin ((2 + 0 + 0) + p) → Fin nn) (A B : E) :
    (fun t : Fin ((2 + 0) + p) =>
      Matrix.vecAppend (by omega : ((2 + 0) + (2 + 0)) + p = p + ((2 + 0) + (2 + 0)))
          (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
          (fun i : Fin ((2 + 0) + (2 + 0)) =>
            (Fin.cons A (Fin.cons B
                (fun l : Fin (2 + 0 + 0) => (e (J ⟨p + l.val, by omega⟩) : E))) :
              Fin ((2 + 0 + 0) + 2) → E)
              (finCongr (by omega : (2 + 0) + (2 + 0) = (2 + 0 + 0) + 2) i))
        (leadExtPerm (cometricCcPerm 0 0) p
          (⟨t.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p))))
    = fun t : Fin ((2 + 0) + p) =>
        (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) B
          (fun j : Fin (1 + p) => (e (J ⟨j.val, by omega⟩) : E)) : Fin ((1 + p) + 1) → E)
          (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) t) := by
  funext t
  by_cases ht : t.val < p
  · rw [leadExtPerm_apply_of_lt (cometricCcPerm 0 0) p
      (⟨t.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p)) ht]
    rw [vecAppend_lt_eval _ _ (⟨t.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p)) ht]
    have hsa : (⟨p, by omega⟩ : Fin ((1 + p) + 1)).succAbove (⟨t.val, by omega⟩ : Fin (1 + p))
        = finCongr (by omega : (2 + 0) + p = (1 + p) + 1) t := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        exact ht)]
      exact Fin.ext (by simp only [Fin.val_castSucc, finCongr_apply, Fin.val_cast])
    rw [← hsa, Fin.insertNth_apply_succAbove]
  · rw [show (⟨t.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p))
        = Fin.cast (by omega : p + ((2 + 0) + (2 + 0)) = ((2 + 0) + (2 + 0)) + p)
            (Fin.natAdd p (⟨t.val - p, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
    rw [leadExtPerm_apply_natAdd (cometricCcPerm 0 0) p
      (⟨t.val - p, by omega⟩ : Fin ((2 + 0) + (2 + 0)))]
    rcases (by omega : t.val - p = 0 ∨ t.val - p = 1) with h0 | h1
    · rw [show (⟨t.val - p, by omega⟩ : Fin ((2 + 0) + (2 + 0))) = ⟨0, by omega⟩ from Fin.ext h0]
      rw [show (cometricCcPerm 0 0) (⟨0, by omega⟩ : Fin ((2 + 0) + (2 + 0)))
          = (⟨1, by omega⟩ : Fin ((2 + 0) + (2 + 0))) from
        Fin.ext (by rw [cometricCcPerm00_val]; rfl)]
      rw [vecAppend_natAdd_eval]
      rw [consPair_eval_one A B _
        (finCongr (by omega : (2 + 0) + (2 + 0) = (2 + 0 + 0) + 2)
          (⟨1, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) rfl]
      rw [show finCongr (by omega : (2 + 0) + p = (1 + p) + 1) t
          = (⟨p, by omega⟩ : Fin ((1 + p) + 1)) from
        Fin.ext (by simp only [finCongr_apply, Fin.val_cast]; omega)]
      rw [Fin.insertNth_apply_same]
    · rw [show (⟨t.val - p, by omega⟩ : Fin ((2 + 0) + (2 + 0))) = ⟨1, by omega⟩ from Fin.ext h1]
      rw [show (cometricCcPerm 0 0) (⟨1, by omega⟩ : Fin ((2 + 0) + (2 + 0)))
          = (⟨2, by omega⟩ : Fin ((2 + 0) + (2 + 0))) from
        Fin.ext (by rw [cometricCcPerm00_val]; rfl)]
      rw [vecAppend_natAdd_eval]
      rw [consPair_eval_tail A B _
        (finCongr (by omega : (2 + 0) + (2 + 0) = (2 + 0 + 0) + 2)
          (⟨2, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) (⟨0, by omega⟩ : Fin (2 + 0 + 0)) rfl]
      have hsa : (⟨p, by omega⟩ : Fin ((1 + p) + 1)).succAbove (⟨p, by omega⟩ : Fin (1 + p))
          = finCongr (by omega : (2 + 0) + p = (1 + p) + 1) t := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by
          simp only [Fin.le_def, Fin.val_castSucc]; omega)]
        exact Fin.ext (by simp only [Fin.val_succ, finCongr_apply, Fin.val_cast]; omega)
      rw [← hsa, Fin.insertNth_apply_succAbove]
      exact congrArg (fun z => (e (J z) : E)) (Fin.ext (by change p + 0 = p; omega))

set_option linter.unusedSectionVars false in
/-- The keystone realized-perturbation tuple identity: through the lead-extended cometric permutation,
the perturbation block reads the cometric-raised covector and the last frame slot. -/
private lemma keystone_tupleS_eval (x : M) {nn p : ℕ} (e : Fin nn → TangentSpace I x)
    (J : Fin ((2 + 0 + 0) + p) → Fin nn) (A B : E) :
    (fun l : Fin (2 + 0) =>
      Matrix.vecAppend (by omega : ((2 + 0) + (2 + 0)) + p = p + ((2 + 0) + (2 + 0)))
          (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
          (fun i : Fin ((2 + 0) + (2 + 0)) =>
            (Fin.cons A (Fin.cons B
                (fun l2 : Fin (2 + 0 + 0) => (e (J ⟨p + l2.val, by omega⟩) : E))) :
              Fin ((2 + 0 + 0) + 2) → E)
              (finCongr (by omega : (2 + 0) + (2 + 0) = (2 + 0 + 0) + 2) i))
        (leadExtPerm (cometricCcPerm 0 0) p
          (⟨((2 + 0) + p) + l.val, by omega⟩ : Fin (((2 + 0) + (2 + 0)) + p))))
    = ![A, (e (J ⟨1 + p, by omega⟩) : E)] := by
  funext l
  rcases (by omega : l.val = 0 ∨ l.val = 1) with hl | hl
  · rw [show l = (0 : Fin (2 + 0)) from Fin.ext (by rw [Fin.val_zero]; exact hl)]
    rw [show (⟨((2 + 0) + p) + (0 : Fin (2 + 0)).val, by omega⟩ :
          Fin (((2 + 0) + (2 + 0)) + p))
        = Fin.cast (by omega : p + ((2 + 0) + (2 + 0)) = ((2 + 0) + (2 + 0)) + p)
            (Fin.natAdd p (⟨2, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero]; omega)]
    rw [leadExtPerm_apply_natAdd (cometricCcPerm 0 0) p (⟨2, by omega⟩ : Fin ((2 + 0) + (2 + 0)))]
    rw [show (cometricCcPerm 0 0) (⟨2, by omega⟩ : Fin ((2 + 0) + (2 + 0)))
        = (⟨0, by omega⟩ : Fin ((2 + 0) + (2 + 0))) from
      Fin.ext (by rw [cometricCcPerm00_val]; rfl)]
    rw [vecAppend_natAdd_eval]
    rw [consPair_eval_zero A B _
      (finCongr (by omega : (2 + 0) + (2 + 0) = (2 + 0 + 0) + 2)
        (⟨0, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) rfl]
    rw [Matrix.cons_val_zero]
  · rw [show l = (1 : Fin (2 + 0)) from Fin.ext (by rw [Fin.val_one]; exact hl)]
    rw [show (⟨((2 + 0) + p) + (1 : Fin (2 + 0)).val, by omega⟩ :
          Fin (((2 + 0) + (2 + 0)) + p))
        = Fin.cast (by omega : p + ((2 + 0) + (2 + 0)) = ((2 + 0) + (2 + 0)) + p)
            (Fin.natAdd p (⟨3, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_one]; omega)]
    rw [leadExtPerm_apply_natAdd (cometricCcPerm 0 0) p (⟨3, by omega⟩ : Fin ((2 + 0) + (2 + 0)))]
    rw [show (cometricCcPerm 0 0) (⟨3, by omega⟩ : Fin ((2 + 0) + (2 + 0)))
        = (⟨3, by omega⟩ : Fin ((2 + 0) + (2 + 0))) from
      Fin.ext (by rw [cometricCcPerm00_val]; rfl)]
    rw [vecAppend_natAdd_eval]
    rw [consPair_eval_tail A B _
      (finCongr (by omega : (2 + 0) + (2 + 0) = (2 + 0 + 0) + 2)
        (⟨3, by omega⟩ : Fin ((2 + 0) + (2 + 0)))) (⟨1, by omega⟩ : Fin (2 + 0 + 0)) rfl]
    rw [show ((![A, (e (J ⟨1 + p, by omega⟩) : E)] : Fin 2 → E) (1 : Fin (2 + 0)))
        = (e (J ⟨1 + p, by omega⟩) : E) from rfl]
    beta_reduce
    exact congrArg (fun z => (e (J z) : E)) (Fin.ext (by change p + 1 = 1 + p; omega))

set_option maxHeartbeats 12800000 in
set_option linter.unusedSectionVars false in
/-- **The sharp `δ²` passenger fibre bound of the cometric keystone product-level top cell.**
Under the `g₀`-fibre operator bound `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, the intrinsic squared
fibre norm of the cometric keystone top cell `cometricKeystoneTop g₀ p T₁ Z` is dominated *sharply* — with
the operator-norm constant `δ²`, NO dimension factor, NO envelope constant, uniformly in the passenger
order `p` — by that of the jet factor `Z`:
`rfns(cometricKeystoneTop g₀ p T₁ Z)(x) ≤ δ² · rfns(Z)(x)`.

The cometric analog of the proven `(0, 3)` `crossCorrKeystoneTop_rfns_le_sq_passenger`: the same
frame-Riesz Parseval argument at the cometric `(0, 2)` slot layout, the keystone tracing the realized
perturbation `h = ccTensorBilinSymm g₀ T₁` (fibre operator norm `≤ δ`) through the `g₀`-cometric against
the factor's ORIGINAL contraction slot (position `p`, the `1 + p` passengers/spectators around it). -/
theorem cometricKeystoneTop_rfns_le_sq_passenger
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ)
    (Z : Integral.L2.SmoothCcTensor g₀ 0 (2 + p)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + p) x
        ((cometricKeystoneTop (I := I) g₀ p T₁ Z).toSection x) ≤
      δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + p) x (Z.toSection x) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hreprS⟩ :=
    Integral.Connection.tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ (2 + p) x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- The slice functional of `Z` at the contracted (position-`p`) slot, as a CLM.
  set leadFun : (Fin (1 + p) → Fin n) → (TangentSpace I x →L[ℝ] ℝ) := fun J' =>
    ContinuousMultilinearMap.toContinuousLinearMap (cometricCcUnitModel (I := I) g₀ Z x)
      (fun k : Fin ((2 + 0) + p) =>
        (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) (0 : E)
          (fun j : Fin (1 + p) => (e (J' j) : E)) : Fin ((1 + p) + 1) → E)
          (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k))
      (finCongr (by omega : (1 + p) + 1 = (2 + 0) + p) (⟨p, by omega⟩ : Fin ((1 + p) + 1)))
    with hleadFun_def
  have hleadFun_apply : ∀ (J' : Fin (1 + p) → Fin n) (u : TangentSpace I x),
      leadFun J' u = cometricCcUnitModel (I := I) g₀ Z x
        (fun k : Fin ((2 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) (u : E)
            (fun j : Fin (1 + p) => (e (J' j) : E)) : Fin ((1 + p) + 1) → E)
            (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)) := by
    intro J' u
    rw [hleadFun_def]
    change (ContinuousMultilinearMap.toContinuousLinearMap (cometricCcUnitModel (I := I) g₀ Z x)
        (fun k : Fin ((2 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) (0 : E)
            (fun j : Fin (1 + p) => (e (J' j) : E)) : Fin ((1 + p) + 1) → E)
            (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k))
        (finCongr (by omega : (1 + p) + 1 = (2 + 0) + p)
          (⟨p, by omega⟩ : Fin ((1 + p) + 1)))) u = _
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext k
    rcases eq_or_ne k (finCongr (by omega : (1 + p) + 1 = (2 + 0) + p)
        (⟨p, by omega⟩ : Fin ((1 + p) + 1))) with hk | hk
    · rw [hk, Function.update_self]
      rw [show (finCongr (by omega : (2 + 0) + p = (1 + p) + 1)
            (finCongr (by omega : (1 + p) + 1 = (2 + 0) + p)
              (⟨p, by omega⟩ : Fin ((1 + p) + 1)))) = (⟨p, by omega⟩ : Fin ((1 + p) + 1)) from
        Fin.ext (by simp)]
      rw [Fin.insertNth_apply_same]
    · rw [Function.update_of_ne hk]
      have hne : (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)
          ≠ (⟨p, by omega⟩ : Fin ((1 + p) + 1)) := by
        intro hc
        apply hk
        apply Fin.ext
        have := congrArg Fin.val hc
        simpa [Fin.val_cast] using this
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hne
      rw [← hj', Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
  -- The slice-Riesz vector and its two reconstruction facts.
  set W : (Fin (1 + p) → Fin n) → TangentSpace I x := fun J' =>
    ∑ c : Fin n, leadFun J' (e c) • e c with hW_def
  have hWfacts : ∀ J' : Fin (1 + p) → Fin n,
      (∀ u : TangentSpace I x, g₀.inner x (W J') u = leadFun J' u) ∧
        g₀.inner x (W J') (W J') = ∑ c : Fin n, (leadFun J' (e c)) ^ 2 := by
    intro J'
    rw [hW_def]
    exact frameRiesz_pair_and_normSq (I := I) g₀ x e horth hexpand (leadFun J')
  -- Frame expansion of both sides.
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x
      ((2 + 0 + 0) + p) e hreprS ((cometricKeystoneTop (I := I) g₀ p T₁ Z).toSection x) K₀,
    Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x
      ((2 + 0) + p) e hreprS (Z.toSection x) K₀]
  -- The keystone frame component at a tuple `J`.
  have hCcomp : ∀ J : Fin ((2 + 0 + 0) + p) → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 ((2 + 0 + 0) + p)
          ((cometricKeystoneTop (I := I) g₀ p T₁ Z).toSection x) n e K₀ J =
        ccTensorBilinSymm (I := I) g₀ T₁ x
          (W (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩)) (e (J ⟨1 + p, by omega⟩)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ ((2 + 0 + 0) + p) x e K₀ J
      ((cometricKeystoneTop (I := I) g₀ p T₁ Z).toSection x)]
    rw [show cometricKeystoneTop (I := I) g₀ p T₁ Z
        = appCcRS (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p) ((2 + 0 + 0) + p)
            (slotExtendPow (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) p
              (cometricCcOp (I := I) g₀ 0 0))
            (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (cometricCcPerm 0 0) p)
              (castRankCc_db g₀ 0
                  (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p)
                ((bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod (a := 0 + p) (b := 0)
                  (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p)) Z)
                  (realizeSymmCcTensor (I := I) g₀ T₁)))) from rfl]
    rw [appCcRS_toSection (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p) ((2 + 0 + 0) + p)]
    rw [ContinuousLinearMap.comp_apply]
    rw [show (fun k : Fin ((2 + 0 + 0) + p) => (e (J k) : E))
        = Matrix.vecAppend (by omega : (2 + 0 + 0) + p = p + (2 + 0 + 0))
            (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
            (fun l : Fin (2 + 0 + 0) => (e (J ⟨p + l.val, by omega⟩) : E)) from by
      funext k
      simp only [Matrix.vecAppend_eq_ite]
      by_cases hk : k.val < p
      · rw [dif_pos hk]
      · rw [dif_neg hk]
        exact congrArg (fun z => (e (J z) : E)) (Fin.ext (by change k.val = p + (k.val - p); omega))]
    rw [slotExtendPow_toModel_consSlots (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) x
      (cometricCcOp (I := I) g₀ 0 0) p _
      (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
      (fun l : Fin (2 + 0 + 0) => (e (J ⟨p + l.val, by omega⟩) : E))]
    rw [cometricCcOp_toSection_toModel (I := I) g₀ 0 0 x _]
    rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace_apply
      (2 + 0 + 0) (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel
        (I := I) g₀ x) _ _]
    rw [show DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel
          (I := I) g₀ x = cometricCcReadingModel (I := I) g₀ x from rfl]
    simp only [modelRankCast_apply_local, passengerCurry_toModel]
    simp only [keystoneArg_unit_toModel (I := I) g₀ p T₁ Z x]
    simp only [keystone_tupleZ_eval (I := I) x e J, keystone_tupleS_eval (I := I) x e J]
    have hSfac : ∀ w₁ w₂ : TangentSpace I x,
        cometricCcUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ![(w₁ : E), (w₂ : E)]
          = ccTensorBilinSymm (I := I) g₀ T₁ x w₁ w₂ := by
      intro w₁ w₂
      rw [← realizeSymmCcTensor_ccTensorBilin_apply, ccTensorBilin_apply]
      rfl
    have hper : ∀ kk : Fin (Module.finrank ℝ E),
        cometricCcUnitModel (I := I) g₀ Z x
            (fun t : Fin ((2 + 0) + p) =>
              (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1))
                ((Module.finBasis ℝ E) kk : E)
                (fun j : Fin (1 + p) => (e (J ⟨j.val, by omega⟩) : E)) :
                  Fin ((1 + p) + 1) → E)
                (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) t)) *
          cometricCcUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
            ![(cometricCcReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)) : E),
              (e (J ⟨1 + p, by omega⟩) : E)]
        = leadFun (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) kk) *
            ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricCcReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)))
              (e (J ⟨1 + p, by omega⟩)) := by
      intro kk
      rw [hleadFun_apply (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩)
        ((Module.finBasis ℝ E) kk)]
      rw [hSfac]
    rw [Finset.sum_congr rfl (fun kk _ => hper kk)]
    set φ : TangentSpace I x →L[ℝ] ℝ := (ccTensorBilinSymm (I := I) g₀ T₁ x).flip
      (e (J ⟨1 + p, by omega⟩)) with hφ_def
    rw [show (∑ kk : Fin (Module.finrank ℝ E),
          leadFun (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) kk) *
            ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricCcReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)))
              (e (J ⟨1 + p, by omega⟩)))
        = ∑ kk : Fin (Module.finrank ℝ E),
            φ (cometricCcReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)))
              * g₀.inner x (W (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩))
                  ((Module.finBasis ℝ E) kk) from by
      refine Finset.sum_congr rfl (fun kk _ => ?_)
      rw [hφ_def, ContinuousLinearMap.flip_apply, mul_comm]
      congr 1
      rw [(hWfacts (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩)).1 ((Module.finBasis ℝ E) kk)]]
    rw [cometricCc_sum_phi_cometric_inner_basis (I := I) g₀ x
      (fun i => cometricCcReadingModel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i)))
      (fun k u => cometricCcReadingModel_dualBasis_inner (I := I) g₀ x k u)
      φ (W (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩))]
    rfl
  -- The `Z` frame component at a tuple `J`.
  have hZcomp : ∀ J : Fin ((2 + 0) + p) → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 ((2 + 0) + p)
          (Z.toSection x) n e K₀ J = cometricCcUnitModel (I := I) g₀ Z x (fun k => e (J k)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ ((2 + 0) + p) x e K₀ J (Z.toSection x)]
    rfl
  simp only [hCcomp, hZcomp]
  -- Group the LHS by the LAST slot.
  rw [sum_index_lastSlot_group' (n := n) (p := p)
    (fun J : Fin ((2 + 0 + 0) + p) → Fin n =>
      ccTensorBilinSymm (I := I) g₀ T₁ x
        (W (fun j : Fin (1 + p) => J ⟨j.val, by omega⟩)) (e (J ⟨1 + p, by omega⟩)) ^ 2)]
  have hLslice : ∀ (c : Fin n) (J' : Fin (1 + p) → Fin n),
      ccTensorBilinSymm (I := I) g₀ T₁ x
          (W (fun j : Fin (1 + p) =>
            (Fin.snoc J' c : Fin ((1 + p) + 1) → Fin n)
              (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1) ⟨j.val, by omega⟩)))
          (e ((Fin.snoc J' c : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1) ⟨1 + p, by omega⟩))) ^ 2
        = ccTensorBilinSymm (I := I) g₀ T₁ x (W J') (e c) ^ 2 := by
    intro c J'
    have hsliceArg : (fun j : Fin (1 + p) =>
          (Fin.snoc J' c : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1) ⟨j.val, by omega⟩)) = J' := by
      funext j
      rw [show (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1)
            (⟨j.val, by omega⟩ : Fin ((2 + 0 + 0) + p)))
            = Fin.castSucc (n := 1 + p) j from by apply Fin.ext; simp, Fin.snoc_castSucc]
    have hsliceLast : ((Fin.snoc J' c : Fin ((1 + p) + 1) → Fin n)
          (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1) ⟨1 + p, by omega⟩)) = c := by
      rw [show (finCongr (by omega : (2 + 0 + 0) + p = (1 + p) + 1)
            (⟨1 + p, by omega⟩ : Fin ((2 + 0 + 0) + p)))
            = Fin.last (1 + p) from by apply Fin.ext; simp, Fin.snoc_last]
    rw [hsliceArg, hsliceLast]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun J' _ => hLslice c J'))]
  rw [Finset.sum_comm]
  -- Group the RHS (`Z`'s frame components) by the MIDDLE (position-`p`) slot.
  rw [sum_index_midSlot_group (n := n) (p := p)
    (fun J : Fin ((2 + 0) + p) → Fin n =>
      (cometricCcUnitModel (I := I) g₀ Z x (fun k => e (J k))) ^ 2)]
  have hRslice : ∀ (c : Fin n) (J' : Fin (1 + p) → Fin n),
      (cometricCcUnitModel (I := I) g₀ Z x (fun k => e ((fun k : Fin ((2 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) c J' : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)) k))) ^ 2
        = (leadFun J' (e c)) ^ 2 := by
    intro c J'
    rw [hleadFun_apply J' (e c)]
    have hsliceArg : (fun k : Fin ((2 + 0) + p) => (e ((fun k : Fin ((2 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) c J' : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)) k) : E))
        = (fun k : Fin ((2 + 0) + p) =>
            (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) ((e c : TangentSpace I x) : E)
              (fun j : Fin (1 + p) => (e (J' j) : E)) : Fin ((1 + p) + 1) → E)
              (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)) := by
      funext k
      beta_reduce
      rcases eq_or_ne (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)
          (⟨p, by omega⟩ : Fin ((1 + p) + 1)) with hk | hk
      · rw [hk, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hk
        rw [← hj', Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    rw [hsliceArg]
  rw [show (∑ c : Fin n, ∑ J' : Fin (1 + p) → Fin n,
        (cometricCcUnitModel (I := I) g₀ Z x (fun k => e ((fun k : Fin ((2 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((1 + p) + 1)) c J' : Fin ((1 + p) + 1) → Fin n)
            (finCongr (by omega : (2 + 0) + p = (1 + p) + 1) k)) k))) ^ 2)
      = ∑ J' : Fin (1 + p) → Fin n, ∑ c : Fin n, (leadFun J' (e c)) ^ 2 from by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun J' _ => Finset.sum_congr rfl (fun c _ => hRslice c J'))]
  -- Both sides grouped by `J'`; bound each slice sharply.
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun J' _ => ?_)
  have hcross_inner :
      (∑ c : Fin n, ccTensorBilinSymm (I := I) g₀ T₁ x (W J') (e c) ^ 2) ≤
        δ ^ 2 * g₀.inner x (W J') (W J') :=
    gFibreOpBound_dualFrame_sq_sum_le (I := I) g₀ x e horth hpars
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hδ (W J')
  rw [(hWfacts J').2] at hcross_inner
  exact hcross_inner

/-! ## The integrated `L²` keystone bound and the cometric envelope constant -/

set_option linter.unusedSectionVars false in
/-- **The integrated sharp `δ²` keystone-top bound at an arbitrary jet factor.**  The squared metric
`L²` norm of the cometric keystone product-level top cell `cometricKeystoneTop g₀ p T₁ Z` is at most
`δ² · ‖Z‖²` — the pointwise sharp keystone passenger bound integrated against the Riemannian volume. -/
theorem cometricKeystoneTop_norm_sq_le (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hfib : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ)
    (Z : Integral.L2.SmoothCcTensor g₀ 0 (2 + p)) :
    ‖cometricKeystoneTop (I := I) g₀ p T₁ Z‖ ^ 2 ≤ δ ^ 2 * ‖Z‖ ^ 2 := by
  classical
  rw [Integral.L2.SmoothCcTensor.norm_def, Integral.L2.SmoothCcTensor.norm_def,
    Integral.Connection.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g₀ (2 + p) (cometricKeystoneTop (I := I) g₀ p T₁ Z),
    Integral.Connection.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g₀ (2 + p) Z]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
    ((Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M)
      g₀ 0 (2 + p) Z).const_mul (δ ^ 2)) (Filter.Eventually.of_forall (fun x => ?_))
  · exact riemannianFiberNormSq_nonneg _ _ _ _ _
  · exact cometricKeystoneTop_rfns_le_sq_passenger (I := I) g₀ p T₁ hfib Z x

/-- **The `appCcRS` fibre-envelope constant of the `p`-fold slot-extended cometric operator** (the
`Classical.choose` of `exists_uniform_riemannianFiberNormSq_appCcRS_le` at the operator
`slotExtendPow p (cometricCcOp g₀ 0 0)`). -/
noncomputable def cometricCrossEnvelopeConst (g₀ : SmoothRiemannianMetric I M) (p : ℕ) : ℝ :=
  (exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀ 0
    (((2 + 0) + (2 + 0)) + p) ((2 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) p
      (cometricCcOp (I := I) g₀ 0 0))).choose

/-- The cometric envelope constant is nonnegative, and it satisfies its defining fibre envelope. -/
theorem cometricCrossEnvelopeConst_spec (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    0 ≤ cometricCrossEnvelopeConst (I := I) g₀ p ∧
      ∀ (W : Integral.L2.SmoothCcTensor g₀ 0 (((2 + 0) + (2 + 0)) + p)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 0 + 0) + p) x
            ((appCcRS (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p) ((2 + 0 + 0) + p)
              (slotExtendPow (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) p
                (cometricCcOp (I := I) g₀ 0 0)) W).toSection x) ≤
          cometricCrossEnvelopeConst (I := I) g₀ p *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p) x
              (W.toSection x) :=
  (exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀ 0
    (((2 + 0) + (2 + 0)) + p) ((2 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) p
      (cometricCcOp (I := I) g₀ 0 0))).choose_spec

/-! ## Support bricks for the cometric rest-peel and grid assembly (file-local) -/

set_option linter.unusedSectionVars false in
/-- `‖S‖² = ∫ rfns(S)` (file-local). -/
private lemma normSq_eq_integral_rfns (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖S‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x)
      ∂(Integral.Measure.riemannianVolumeMeasure I M g₀) := by
  rw [Integral.L2.SmoothCcTensor.norm_def]
  exact Integral.Connection.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g₀ s S

set_option linter.unusedSectionVars false in
/-- Squared `L²`-norm scaling of an iterated covariant jet (file-local). -/
private lemma iteratedCovGrad_normSq_smul (g₀ : SmoothRiemannianMetric I M) (s j : ℕ) (c : ℝ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j (c • S)‖ ^ 2 =
      c ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S‖ ^ 2 := by
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.iteratedCovGrad_smul
    (I := I) g₀ 0 s j c S, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

set_option linter.unusedSectionVars false in
/-- `2`-subadditivity of the squared `L²` norm on a difference of iterated covariant jets (file-local). -/
private lemma iteratedCovGrad_normSq_sub_le (g₀ : SmoothRiemannianMetric I M) (s j : ℕ)
    (S T : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j (S - T)‖ ^ 2 ≤
      2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S‖ ^ 2
        + 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 := by
  rw [PDE.RicciFlow.iteratedCovGrad_sub]
  set A := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S with hA
  set Bb := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j T with hBb
  have h := norm_sub_sq_real A Bb
  have hcs2 := abs_real_inner_le_norm A Bb
  have hcs := neg_le_abs (@inner ℝ _ _ A Bb)
  nlinarith [h, hcs, hcs2, sq_nonneg (‖A‖ - ‖Bb‖), norm_nonneg A, norm_nonneg Bb]

set_option linter.unusedSectionVars false in
/-- The squared metric `L²` norm of every iterated covariant jet is slot-permutation invariant
(file-local). -/
private theorem norm_sq_iteratedCovGrad_permute (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : Integral.L2.SmoothCcTensor g₀ 0 s) (i : ℕ) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s i
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ W)‖ ^ 2 =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s i W‖ ^ 2 := by
  rw [normSq_eq_integral_rfns, normSq_eq_integral_rfns]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact PDE.DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M)
    g₀ σ W i x

set_option linter.unusedSectionVars false in
/-- The margin-chosen scale `t := (1 − 2δ)/(1 + 2δ)` relaxes the `2(1+t)δ²`-principal to `δ`
(file-local). -/
private theorem marginScale_absorb {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    2 * (1 + (1 - 2 * δ) / (1 + 2 * δ)) * δ ^ 2 ≤ δ := by
  have hden : (0 : ℝ) < 1 + 2 * δ := by linarith
  have hcollapse : 1 + (1 - 2 * δ) / (1 + 2 * δ) = 2 / (1 + 2 * δ) := by
    field_simp
    ring
  rw [hcollapse, show 2 * (2 / (1 + 2 * δ)) * δ ^ 2 = (4 * δ ^ 2) / (1 + 2 * δ) from by ring,
    div_le_iff₀ hden]
  nlinarith

set_option linter.unusedSectionVars false in
/-- The margin scale `t := (1 − 2δ)/(1 + 2δ) ∈ (0, 1]` for `0 ≤ δ < 1/2` (file-local). -/
private theorem marginScale_mem {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    0 < (1 - 2 * δ) / (1 + 2 * δ) ∧ (1 - 2 * δ) / (1 + 2 * δ) ≤ 1 := by
  have hden : (0 : ℝ) < 1 + 2 * δ := by linarith
  exact ⟨div_pos (by linarith) hden, (div_le_one hden).2 (by linarith)⟩

set_option linter.unusedSectionVars false in
/-- **The cometric product section is the slot-permuted bare unit-model product** (file-local).
`cometricCcProdSection g₀ S T = permute (cometricCcPerm a b) (unitModelProdSection T S)`. -/
private theorem cometricCcProdSection_eq_permute_unitModelProdSection
    (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    cometricCcProdSection (I := I) g₀ S T =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (cometricCcPerm a b)
        (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) g₀ T S) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M)
    (s := (2 + b) + (2 + a))
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
      ((cometricCcProdSection (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
          (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)) := by
    change Tensor0SBundle.Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
            (cometricCcProdField (I := I) g₀ S T x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) = _
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
            (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)))) = _
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [hL]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ (cometricCcPerm a b)
          (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) g₀ T S)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))
      = Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ ((2 + b) + (2 + a))
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (cometricCcPerm a b)
            (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) g₀ T S)) x from rfl]
  rw [permuteCcTensor_unitModel (I := I) g₀ (cometricCcPerm a b)
      (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) g₀ T S) x,
    Analysis.Parabolic.TensorSpectral.unitModelProdSection_unitModel (I := I) g₀ T S x]
  rfl

set_option linter.unusedSectionVars false in
/-- The realized-perturbation order-`0` `C⁰` fibre sup under fibre-smallness (file-local):
`rfns(realizeSymm T₁)(x) ≤ (finrank · δ)²`. -/
private theorem realizeSymm_rfns_le_of_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hfib : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * δ) ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hreprS⟩ :=
    Integral.Connection.tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ 2 x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 2 e
      hreprS ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) K₀]
  have hcomp : ∀ J : Fin 2 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) n e K₀ J =
        ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e (J 1)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ 2 x e K₀ J
      ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x)]
    rw [show (fun k => e (J k)) = ![e (J 0), e (J 1)] from by
      funext k; fin_cases k <;> rfl]
    rw [← realizeSymmCcTensor_ccTensorBilin_apply (I := I) g₀ T₁ x (e (J 0)) (e (J 1)),
      ccTensorBilin_apply (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x (e (J 0)) (e (J 1))]
    rfl
  have hterm : ∀ J : Fin 2 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) n e K₀ J ^ 2 ≤ δ ^ 2 := by
    intro J
    rw [hcomp J]
    have hbd := gFibreOpBound_dualFrame_sq_sum_le (I := I) g₀ x e horth hpars
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hfib (e (J 0))
    have he00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hsingle : (ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e (J 1))) ^ 2 ≤
        ∑ k : Fin n, (ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e k)) ^ 2 := by
      refine Finset.single_le_sum (f := fun k : Fin n =>
        (ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e k)) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ (J 1))
    calc (ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e (J 1))) ^ 2
        ≤ ∑ k : Fin n, (ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e k)) ^ 2 := hsingle
      _ ≤ δ ^ 2 * g₀.inner x (e (J 0)) (e (J 0)) := hbd
      _ = δ ^ 2 := by rw [he00, mul_one]
  -- The frame sum has `n²` terms, each `≤ δ²`; `n = finrank`.
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by
    have hnn : n = Module.finrank ℝ E := by rw [hn]; rfl
    rw [hnn]
  calc (∑ J : Fin 2 → Fin n,
        Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) n e K₀ J ^ 2)
      ≤ ∑ _J : Fin 2 → Fin n, δ ^ 2 := Finset.sum_le_sum (fun J _ => hterm J)
    _ = ((n : ℝ) ^ 2) * δ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ = ((Module.finrank ℝ E : ℝ) * δ) ^ 2 := by rw [hnE]; ring

set_option linter.unusedSectionVars false in
/-- **The summed realized-perturbation `L²` no-gain jet fold** (file-local).  One constant per `(g₀, N)`,
folding `∑_{i ≤ N} ‖∇^i (realizeSymm T)‖²` into `∑_{l ≤ N} ‖∇^l T‖²`. -/
private theorem realize_jet_norm_sq_sum_fold (g₀ : SmoothRiemannianMetric I M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
        (∑ i ∈ Finset.range (N + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ T)‖ ^ 2) ≤
          C * ∑ l ∈ Finset.range (N + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T‖ ^ 2 := by
  classical
  choose Ci hCi0 hCi using fun i => realizeSymm_iteratedCovGrad_normSq_le_jetSum (I := I) g₀ i
  refine ⟨∑ i ∈ Finset.range (N + 1), Ci i,
    Finset.sum_nonneg fun i _ => hCi0 i, fun T => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  refine le_trans (hCi i T) (mul_le_mul_of_nonneg_left ?_ (hCi0 i))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by have := Finset.mem_range.mp hi; omega))
    (fun l _ _ => by positivity)

set_option linter.unusedSectionVars false in
/-- The slot permutation distributes over a section difference (file-local). -/
private theorem permuteCcTensor_sub_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A - B) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
        - PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ (A - B) x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ A x
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ B x
  have hsubval : (A - B).toSection x = A.toSection x - B.toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hsubval' : ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
        - PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B)).toSection x =
      (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
        - (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  calc Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
      = (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by rw [hL]
    _ = (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m
          - (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by
        rw [hsubval]; rfl
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
          - Tensor0SBundle.Tensor0SSpace.toModel
          ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hA, hB]
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
            - PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hsubval']; rfl

set_option linter.unusedSectionVars false in
/-- The operator-field action distributes over a section difference (file-local). -/
private theorem appCcRS_sub_right_local (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ b c) (W₁ W₂ : Integral.L2.SmoothCcTensor g₀ a b) :
    appCcRS (I := I) (M := M) g₀ a b c Φ (W₁ - W₂) =
      appCcRS (I := I) (M := M) g₀ a b c Φ W₁ - appCcRS (I := I) (M := M) g₀ a b c Φ W₂ := by
  rw [sub_eq_add_neg, show -W₂ = (-1 : ℝ) • W₂ from (neg_one_smul ℝ W₂).symm,
    appCcRS_add_right, appCcRS_smul_right, neg_one_smul, ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
/-- `rfns` order-0 slot-permutation invariance (file-local). -/
private lemma rfns_permuteCcTensor_zero (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : Integral.L2.SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (W.toSection x) :=
  PDE.DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M) g₀ σ W 0 x

/-! ## The cometric `t`-scaled Gagliardo–Nirenberg integrated peeled rest bound -/

set_option maxHeartbeats 12800000 in
set_option linter.unusedSectionVars false in
/-- **The section-uniform `t`-scaled Gagliardo–Nirenberg integrated peeled bound on the cometric
parallel-contraction `Rest` arm.**  For the parallel `g₀`-single cometric contraction of the realized
perturbation `realizeSymm T₁` against an arbitrary rank-`2` section `Y` with `C⁰` fibre sup
`√rfns(Y) ≤ Λ_Y`, the squared metric `L²` mass of the rest cell — the difference
`∇^p (cometricParallelContraction (realizeSymm T₁) Y) − cometricKeystoneTop g₀ p T₁ (∇^p Y)` — is
dominated, for every free scale `t ∈ (0, 1]`, by
`t·δ²·‖∇^p Y‖² + Cpk·(1/t)^p·(∑_{q<p} ‖∇^q Y‖² + Λ_Y²·∑_{i ≤ p+1} ‖∇^i (realizeSymm T₁)‖²)`.
The cometric `(0, 2)` analog of the proven `(0, 3)` `contraction_rest_peel_uniform`. -/
private theorem cometricCross_rest_peel_uniform (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) :
    ∃ Cpk : ℝ, 0 ≤ Cpk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (Y : Integral.L2.SmoothCcTensor g₀ 0 2)
        (ΛY : ℝ), 0 ≤ ΛY →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (Y.toSection x) ≤ ΛY ^ 2) →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0 + 0) p
              (cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
                (realizeSymmCcTensor (I := I) g₀ T₁) Y)
            - cometricKeystoneTop (I := I) g₀ p T₁
                (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) p Y)‖ ^ 2 ≤
          t * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2
            + Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2
              + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) := by
  classical
  set μ := Integral.Measure.riemannianVolumeMeasure I M g₀ with hμ
  obtain ⟨hCenv0, hCenvB⟩ := cometricCrossEnvelopeConst_spec (I := I) g₀ p
  obtain ⟨cGlow, hcGlow0, hGNlow⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
      (I := I) (M := M) g₀ 2 2 (p - 1)
  obtain ⟨cAnti, hcAnti0, hAnti⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_antiDiagGrid_topArm_scaled_le
      (I := I) (M := M) g₀ 2 2 p
  set nE : ℝ := (Module.finrank ℝ E : ℝ) with hnE
  have hnE0 : 0 ≤ nE := by rw [hnE]; positivity
  set cE := cometricCrossEnvelopeConst (I := I) g₀ p with hcE
  set Ar : ℝ := cE * 4 ^ p * nE ^ 2 + 1 with hAr
  have hAr1 : (1 : ℝ) ≤ Ar := by
    rw [hAr]
    have : (0 : ℝ) ≤ cE * 4 ^ p * nE ^ 2 := by positivity
    linarith
  have hAr0 : (0 : ℝ) < Ar := lt_of_lt_of_le zero_lt_one hAr1
  refine ⟨cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ p),
    by positivity, ?_⟩
  intro t ht0 ht1 T₁ Y ΛY hΛY0 hfib hYsup
  set wS := realizeSymmCcTensor (I := I) g₀ T₁ with hwS
  set Xp := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0 + 0) p
      (cometricParallelContraction (I := I) g₀ (a := 0) (b := 0) wS Y)
    with hXpd
  set Φb := bareTensorRfnsBilinearProduct (I := I) g₀ 2 2 with hΦbd
  set Φp := slotExtendPow (I := I) (M := M) g₀ ((2 + 0) + (2 + 0)) (2 + 0 + 0) p
      (cometricCcOp (I := I) g₀ 0 0) with hΦpd
  set U := Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
      (p := 2 + 0) (q := 2 + 0) g₀ Y wS with hUd
  set TopU := castRankCc_db g₀ 0
      (by omega : ((2 + 2) + (0 + p) + 0) = ((2 + 2) + 0 + 0) + p)
      (Φb.prod (a := 0 + p) (b := 0)
        (castRankCc_db g₀ 0 (by omega : ((2 + 0) + p) = 2 + (0 + p))
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) p Y)) wS) with hTopUd
  set σcc := cometricCcPerm 0 0 with hσccd
  set Ztop := PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p) TopU with hZtopd
  set Ap := cometricKeystoneTop (I := I) g₀ p T₁
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) p Y) with hApd
  have hApeq : Ap =
      appCcRS (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p)
        ((2 + 0 + 0) + p) Φp Ztop := rfl
  -- (1) The operator-reduced iterated Leibniz: `∇^p Φc = appCcRS Φp (∇^p P)`.
  have hXeq : Xp =
      appCcRS (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p)
        ((2 + 0 + 0) + p) Φp
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((2 + 0) + (2 + 0)) p
          (cometricCcProdSection (I := I) g₀ (a := 0) (b := 0) wS Y)) := by
    rw [hXpd, cometricParallelContraction_eq_appCcRS (I := I) g₀ (a := 0) (b := 0) wS Y]
    exact iteratedCovGrad_appCcRS_of_parallel (I := I) g₀ 0 ((2 + 0) + (2 + 0)) (2 + 0 + 0)
      (cometricCcOp (I := I) g₀ 0 0)
      (cometricCcOp_covGrad_eq_zero (I := I) g₀ 0 0)
      (cometricCcProdSection (I := I) g₀ (a := 0) (b := 0) wS Y) p
  -- (2) The product section is the slot-permuted bare product.
  have hPU : cometricCcProdSection (I := I) g₀ (a := 0) (b := 0) wS Y =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ σcc U :=
    cometricCcProdSection_eq_permute_unitModelProdSection (I := I) (a := 0) (b := 0) g₀ wS Y
  have hUb : U = Φb.prod (a := 0) (b := 0) Y wS := rfl
  -- (3) The iterated gradient commutes with the slot permutation.
  have hPp : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((2 + 0) + (2 + 0)) p
        (cometricCcProdSection (I := I) g₀ (a := 0) (b := 0) wS Y) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((2 + 0) + (2 + 0)) p U) := by
    rw [hPU]
    exact iteratedCovGrad_permuteCcTensor_eq (I := I) g₀ σcc U p
  -- (4) `Xp − Ap` as a single operator action on the permuted product-level difference.
  have hXAeq : Xp - Ap =
      appCcRS (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p)
        ((2 + 0 + 0) + p) Φp
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((2 + 0) + (2 + 0)) p U - TopU)) := by
    rw [hApeq, permuteCcTensor_sub_local, appCcRS_sub_right_local, ← hPp, ← hXeq]
  -- (5) The pointwise peeled binomial-Leibniz grid of the bare product (constant `4^p`).
  have hpeel : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((2 + 0) + (2 + 0)) p
          (Φb.prod (a := 0) (b := 0) Y wS) - TopU).toSection x) ≤
    (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
        ∑ l ∈ Finset.range (p + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
    intro x
    have hgrid := Φb.rfns_iteratedCovGrad_prod_topRest_le_peeledDiagGrid p (a := 0) (b := 0) Y wS x
    have hmu : Φb.mu = 1 := rfl
    rw [hmu, one_mul] at hgrid
    exact hgrid
  -- (6) The fibre-small `C⁰` sup of the realized factor.
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (wS.toSection x) ≤
      (nE * δ) ^ 2 := by
    intro x
    rw [hwS, hnE]
    exact realizeSymm_rfns_le_of_gFibreOpBound (I := I) g₀ T₁ hfib x
  -- (7) The pointwise envelope bound on `rfns(Xp − Ap)` against the PEELED grid (window `i < p`).
  have hXApt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 0 + 0) + p) x
      ((Xp - Ap).toSection x) ≤
    cE * (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
        ∑ l ∈ Finset.range (p + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
    intro x
    rw [hXAeq]
    refine le_trans (hCenvB _ x) ?_
    rw [rfns_permuteCcTensor_zero, hUb]
    calc cE * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (((2 + 0) + (2 + 0)) + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((2 + 0) + (2 + 0)) p
              (Φb.prod (a := 0) (b := 0) Y wS)
            - TopU).toSection x)
        ≤ cE * ((4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) :=
          mul_le_mul_of_nonneg_left (hpeel x) hCenv0
      _ = cE * (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
          ring
  -- (8) The two engine instances.
  obtain ⟨hint_low, hlow⟩ := hGNlow Y wS ΛY (nE * δ) hΛY0 (by positivity) hYsup hTsup
  set tt : ℝ := t / Ar with htt
  have htt0 : 0 < tt := by rw [htt]; positivity
  have htt1 : tt ≤ 1 := by
    rw [htt, div_le_one hAr0]
    linarith
  obtain ⟨hint_anti, hanti⟩ := hAnti Y wS ΛY (nE * δ) hΛY0 (by positivity) hYsup hTsup tt htt0 htt1
  -- (9) The named jet sums.
  set Lp := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2 with hLpd
  set Slow := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2 with hSlowd
  set Sw := ∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i wS‖ ^ 2 with hSwd
  have hLp_nn : 0 ≤ Lp := by rw [hLpd]; positivity
  have hSlow_nn : 0 ≤ Slow := by rw [hSlowd]; positivity
  have hSw_nn : 0 ≤ Sw := by rw [hSwd]; positivity
  have hSwfold : ∀ N : ℕ, N ≤ p + 1 + 1 → (∑ l ∈ Finset.range N,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw := by
    intro N hN
    rw [hSwd]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 hN) (fun l _ _ => by positivity)
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- Degenerate order `p = 0`: the peeled grid is empty.
    subst hp0
    have hzero : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 0 + 0) + 0) x
        ((Xp - Ap).toSection x) ≤ 0 := by
      intro x
      refine le_trans (hXApt x) (le_of_eq ?_)
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    have hXA0 : ‖Xp - Ap‖ ^ 2 ≤ 0 := by
      rw [normSq_eq_integral_rfns]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
              ((Xp - Ap).toSection x) ∂μ)
          ≤ ∫ x, (0 : ℝ) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => ?_))
              (MeasureTheory.integrable_zero _ _ _)
              (Filter.Eventually.of_forall (fun x => hzero x))
            exact riemannianFiberNormSq_nonneg _ _ _ _ _
        _ = 0 := by simp
    have hrhs_nn : 0 ≤ t * δ ^ 2 * Lp
        + cE * 4 ^ 0 * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ 0)
          * (1 / t) ^ 0 * (Slow + ΛY ^ 2 * Sw) := by
      have h1 : 0 ≤ t * δ ^ 2 * Lp := by positivity
      have h2 : 0 ≤ cE * (4 : ℝ) ^ 0 * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ 0)
          * (1 / t) ^ 0 * (Slow + ΛY ^ 2 * Sw) := by positivity
      linarith
    linarith [hXA0, hrhs_nn]
  · -- Genuine order `p ≥ 1`.
    have hp1 : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hppos
    rw [hp1] at hlow hint_low
    have hgrid_split : ∀ x : M, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
          ∑ l ∈ Finset.range (p + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) =
        (∑ i ∈ Finset.range p,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
            ∑ l ∈ Finset.range (p - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x))
        + ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x) := by
      intro x
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hip : i < p := Finset.mem_range.mp hi
      rw [show p + 1 - i = (p - i) + 1 from by omega, Finset.sum_range_succ, mul_add]
    have hXAint : ‖Xp - Ap‖ ^ 2 ≤ cE * (4 : ℝ) ^ p *
        ((∫ x, (∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
              ∑ l ∈ Finset.range (p - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) := by
      rw [normSq_eq_integral_rfns]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + p) x
              ((Xp - Ap).toSection x) ∂μ)
          ≤ ∫ x, (cE * (4 : ℝ) ^ p * ((∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x))
            + ∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x))) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => ?_))
              ((hint_low.add hint_anti).const_mul _)
              (Filter.Eventually.of_forall (fun x => ?_))
            · exact riemannianFiberNormSq_nonneg _ _ _ _ _
            · refine le_trans (hXApt x) (le_of_eq ?_)
              rw [hgrid_split x]
        _ = cE * (4 : ℝ) ^ p * ((∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
            + ∫ x, (∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add hint_low hint_anti]
    have hSw_low : (∑ l ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw :=
      hSwfold p (by omega)
    have hSw_anti : (∑ l ∈ Finset.range (p + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw :=
      hSwfold (p + 1) (by omega)
    have hlow' : (∫ x, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
          ∑ l ∈ Finset.range (p - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ) ≤
        cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw) := by
      refine le_trans hlow ?_
      have h2 : ΛY ^ 2 * (∑ l ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ ΛY ^ 2 * Sw :=
        mul_le_mul_of_nonneg_left hSw_low (by positivity)
      nlinarith [hcGlow0, h2]
    have hanti' : (∫ x, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
        tt * ((nE * δ) ^ 2 * Lp) + cAnti * (1 / tt) ^ p * (ΛY ^ 2 * Sw) := by
      refine le_trans hanti ?_
      have h2 : ΛY ^ 2 * (∑ l ∈ Finset.range (p + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ ΛY ^ 2 * Sw :=
        mul_le_mul_of_nonneg_left hSw_anti (by positivity)
      have hc : 0 ≤ cAnti * (1 / tt) ^ p := by positivity
      nlinarith [hc, h2]
    have htopscale : cE * (4 : ℝ) ^ p * (tt * ((nE * δ) ^ 2 * Lp)) ≤ t * δ ^ 2 * Lp := by
      rw [htt]
      rw [show cE * (4 : ℝ) ^ p * (t / Ar * ((nE * δ) ^ 2 * Lp))
          = (cE * 4 ^ p * nE ^ 2) / Ar * (t * δ ^ 2 * Lp) from by ring]
      have hfrac : (cE * 4 ^ p * nE ^ 2) / Ar ≤ 1 := by
        rw [div_le_one hAr0, hAr]
        linarith
      have hmass : 0 ≤ t * δ ^ 2 * Lp := by positivity
      nlinarith [hfrac, hmass]
    have hinv_tt : (1 / tt) ^ p = Ar ^ p * (1 / t) ^ p := by
      rw [htt, one_div_div, show Ar / t = Ar * (1 / t) from by ring, mul_pow]
    have h1t1 : (1 : ℝ) ≤ (1 / t) ^ p := one_le_pow₀ (by rw [le_div_iff₀ ht0]; linarith)
    have hfinal : cE * (4 : ℝ) ^ p *
        ((∫ x, (∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
              ∑ l ∈ Finset.range (p - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
        t * δ ^ 2 * Lp
          + cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ p)
            * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
      have hcE4 : (0 : ℝ) ≤ cE * 4 ^ p := by positivity
      have hsum_le := add_le_add hlow' hanti'
      have hstep : cE * (4 : ℝ) ^ p *
          ((∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
            + ∫ x, (∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i Y).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
          cE * 4 ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw))
            + cE * 4 ^ p * (tt * ((nE * δ) ^ 2 * Lp))
            + cE * 4 ^ p * (cAnti * (1 / tt) ^ p * (ΛY ^ 2 * Sw)) := by
        nlinarith [hsum_le, hcE4]
      refine le_trans hstep ?_
      rw [hinv_tt]
      have hΛSw_nn : 0 ≤ ΛY ^ 2 * Sw := by positivity
      have hlow_piece : cE * (4 : ℝ) ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw)) ≤
          cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
        have hbase : cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw) ≤
            cGlow * (nE ^ 2 * δ ^ 2 + 1) * (Slow + ΛY ^ 2 * Sw) := by
          nlinarith [hcGlow0, hSlow_nn, hΛSw_nn, sq_nonneg (nE * δ),
            mul_nonneg hcGlow0 (mul_nonneg (sq_nonneg (nE * δ)) hΛSw_nn),
            mul_nonneg hcGlow0 (mul_nonneg (sq_nonneg ΛY) hSlow_nn),
            mul_nonneg hcGlow0 hSlow_nn]
        calc cE * (4 : ℝ) ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw))
            ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) * (Slow + ΛY ^ 2 * Sw)) :=
              mul_le_mul_of_nonneg_left hbase hcE4
          _ = cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 : ℝ) * (Slow + ΛY ^ 2 * Sw) := by
              ring
          _ ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 / t) ^ p
                * (Slow + ΛY ^ 2 * Sw) := by
              have hmono : cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 : ℝ) ≤
                  cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 / t) ^ p := by
                have hc : (0 : ℝ) ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) := by
                  positivity
                nlinarith [h1t1, hc]
              exact mul_le_mul_of_nonneg_right hmono (by linarith [hSlow_nn, hΛSw_nn])
      have hanti_piece : cE * (4 : ℝ) ^ p * (cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛY ^ 2 * Sw)) ≤
          cE * 4 ^ p * (cAnti * Ar ^ p) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
        have hc : (0 : ℝ) ≤ cAnti * Ar ^ p * (1 / t) ^ p := by positivity
        have hbase : cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛY ^ 2 * Sw) ≤
            cAnti * Ar ^ p * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
          nlinarith [hSlow_nn, hc]
        calc cE * (4 : ℝ) ^ p * (cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛY ^ 2 * Sw))
            ≤ cE * 4 ^ p * (cAnti * Ar ^ p * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw)) :=
              mul_le_mul_of_nonneg_left hbase hcE4
          _ = cE * 4 ^ p * (cAnti * Ar ^ p) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by ring
      have hdistr : cE * (4 : ℝ) ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1))
            * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw)
          + cE * 4 ^ p * (cAnti * Ar ^ p) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw)
          = cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ p)
            * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by ring
      linarith [hlow_piece, hanti_piece, htopscale, hdistr.le, hdistr.ge]
    exact le_trans hXAint hfinal

set_option linter.unusedSectionVars false in
/-- **The cometric `t`-scaled top/rest split of the parallel contraction.**  Assembles the sharp `δ²`
keystone-top (`cometricKeystoneTop_norm_sq_le`) with the rest peel (`cometricCross_rest_peel_uniform`)
through `2`-subadditivity. -/
private theorem cometricCross_topRest_split_uniform (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) :
    ∃ Cpk : ℝ, 0 ≤ Cpk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (Y : Integral.L2.SmoothCcTensor g₀ 0 2)
        (ΛY : ℝ), 0 ≤ ΛY →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (Y.toSection x) ≤ ΛY ^ 2) →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0 + 0) p
              (cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
                (realizeSymmCcTensor (I := I) g₀ T₁) Y)‖ ^ 2 ≤
          2 * (1 + t) * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2
            + 2 * Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2
              + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) := by
  classical
  obtain ⟨Cpk, hCpk0, hCpk⟩ := cometricCross_rest_peel_uniform (I := I) g₀ p δ hδ0
  refine ⟨Cpk, hCpk0, ?_⟩
  intro t ht0 ht1 T₁ Y ΛY hΛY0 hfib hYsup
  set Xp := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0 + 0) p
      (cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
        (realizeSymmCcTensor (I := I) g₀ T₁) Y) with hXpd
  set Ap := cometricKeystoneTop (I := I) g₀ p T₁
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) p Y) with hApd
  have htop : ‖Ap‖ ^ 2 ≤
      δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2 := by
    rw [hApd]
    exact cometricKeystoneTop_norm_sq_le (I := I) g₀ p T₁ hfib
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) p Y)
  have hrest := hCpk t ht0 ht1 T₁ Y ΛY hΛY0 hfib hYsup
  rw [← hXpd, ← hApd] at hrest
  have h2sub : ‖Xp‖ ^ 2 ≤ 2 * ‖Ap‖ ^ 2 + 2 * ‖Xp - Ap‖ ^ 2 := by
    have hXeq : Xp = Ap + (Xp - Ap) := (add_sub_cancel Ap Xp).symm
    have hns := norm_add_sq_real Ap (Xp - Ap)
    have hcs := abs_real_inner_le_norm Ap (Xp - Ap)
    have hcs' := le_abs_self (inner (𝕜 := ℝ) Ap (Xp - Ap))
    calc ‖Xp‖ ^ 2 = ‖Ap + (Xp - Ap)‖ ^ 2 := by rw [← hXeq]
      _ ≤ 2 * ‖Ap‖ ^ 2 + 2 * ‖Xp - Ap‖ ^ 2 := by
          nlinarith [hns, hcs, hcs', sq_nonneg (‖Ap‖ - ‖Xp - Ap‖), norm_nonneg Ap,
            norm_nonneg (Xp - Ap)]
  calc ‖Xp‖ ^ 2 ≤ 2 * ‖Ap‖ ^ 2 + 2 * ‖Xp - Ap‖ ^ 2 := h2sub
    _ ≤ 2 * (δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2)
        + 2 * (t * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2
          + Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2
            + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2)) := by
        have := mul_le_mul_of_nonneg_left htop (by norm_num : (0 : ℝ) ≤ 2)
        have := mul_le_mul_of_nonneg_left hrest (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = 2 * (1 + t) * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p Y‖ ^ 2
        + 2 * Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2
          + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) := by ring

set_option linter.unusedSectionVars false in
/-- **The δ-separated integrated cometric cross grid.**  The order-`p` cometric cross correction
`L²` jet bounded by `δ·‖∇^p cometricInverseDiff‖²` plus the lower-order `< p` `cometricInverseDiff`
jets and the `≤ (p+1)`-jet of `T₁`.  Assembles the `t`-scaled top/rest split at the margin scale
`t = (1 − 2δ)/(1 + 2δ)`, the margin absorption `marginScale_absorb`, the order-`0` `C⁰` sup of
`cometricInverseDiff` (`riemannianFiberNormSq_cometricInverseDiffSection_order0_le`), and the
realize-jet `L²` fold.  The cometric analog of the proven `(0, 3)` `cc_grid_le_low` shape (carrying the
lower-order jet term that the strong-induction headline folds away). -/
theorem cometricCrossSection_iteratedCovGrad_grid_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cgrid : ℝ, 0 ≤ Cgrid ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
              (crossCometricSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
              (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2
          + Cgrid * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q
                    (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
  classical
  set ΛD : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ^ 2) with hΛDd
  have hΛD0 : 0 ≤ ΛD := Real.sqrt_nonneg _
  obtain ⟨Cpk, hCpk0, hCpk⟩ := cometricCross_topRest_split_uniform (I := I) g₀ p δ hδ0
  obtain ⟨Cr, hCr0, hCr⟩ := realize_jet_norm_sq_sum_fold (I := I) g₀ (p + 1)
  obtain ⟨ht0', ht1'⟩ := marginScale_mem (δ := δ) hδ0 hδ1
  set t : ℝ := (1 - 2 * δ) / (1 + 2 * δ) with htdef
  refine ⟨2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr), by positivity, ?_⟩
  intro T₁ g₁ hr hfib
  set D := cometricInverseDiffSection (I := I) g₁ g₀ with hDd
  set Y := PDE.DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0] D with hYd
  have hYsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (Y.toSection x) ≤
      ΛD ^ 2 := by
    intro x
    rw [hYd, rfns_permuteCcTensor_zero, hDd]
    rw [hΛDd, Real.sq_sqrt (by positivity)]
    exact riemannianFiberNormSq_cometricInverseDiffSection_order0_le (I := I) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hr (by linarith) hδ0 hfib x
  -- The contraction realization of the cometric cross-correction section.
  have hccid : crossCometricSection (I := I) g₁ g₀ T₁ =
      cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
        (realizeSymmCcTensor (I := I) g₀ T₁) Y :=
    (cometricParallelContraction_eq_cometricCrossSection (I := I) g₀ g₁ T₁).symm
  have hsplit := hCpk t ht0' ht1' T₁ Y ΛD hΛD0 hfib hYsup
  -- The permutation `L²`-norm invariances `‖∇^q Y‖² = ‖∇^q D‖²`.
  have hYD : ∀ q : ℕ, ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2 =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := by
    intro q
    rw [hYd]
    exact norm_sq_iteratedCovGrad_permute (I := I) g₀ c[(1 : Fin 2), 0] D q
  rw [hccid]
  -- The margin absorption `2(1+t)δ² ≤ δ`.
  have habsorb : 2 * (1 + t) * δ ^ 2 ≤ δ := marginScale_absorb hδ0 hδ1
  set Lp := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p D‖ ^ 2 with hLpd
  set Slow := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 with hSlowd
  set ST := ∑ l ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSTd
  have hLp_nn : 0 ≤ Lp := by rw [hLpd]; positivity
  have hSlow_nn : 0 ≤ Slow := by rw [hSlowd]; positivity
  have hST_nn : 0 ≤ ST := by rw [hSTd]; positivity
  have hSlowY : (∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q Y‖ ^ 2) = Slow := by
    rw [hSlowd]
    exact Finset.sum_congr rfl fun q _ => hYD q
  have hSw_fold : (∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤ Cr * ST := by
    rw [hSTd]
    exact hCr T₁
  rw [hYD p, ← hLpd, hSlowY] at hsplit
  have h1t : (0 : ℝ) ≤ (1 / t) ^ p := by positivity
  have hprin : 2 * (1 + t) * δ ^ 2 * Lp ≤ δ * Lp :=
    mul_le_mul_of_nonneg_right habsorb hLp_nn
  have hrest_fold : 2 * Cpk * (1 / t) ^ p * (Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤
      2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by
    have hin : Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 ≤
        (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by
      have h2 : ΛD ^ 2 * (∑ i ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤ ΛD ^ 2 * (Cr * ST) :=
        mul_le_mul_of_nonneg_left hSw_fold (by positivity)
      nlinarith [hSlow_nn, hST_nn, sq_nonneg ΛD, mul_nonneg (sq_nonneg ΛD)
        (mul_nonneg hCr0 hST_nn), mul_nonneg (mul_nonneg (sq_nonneg ΛD) hCr0) hSlow_nn]
    calc 2 * Cpk * (1 / t) ^ p * (Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2)
        ≤ 2 * Cpk * (1 / t) ^ p * ((1 + ΛD ^ 2 * Cr) * (Slow + ST)) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by ring
  -- Assemble: `‖∇^p crossCometric‖² ≤ δ·Lp + Cgrid·(Slow + ST)`.
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
          (cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
            (realizeSymmCcTensor (I := I) g₀ T₁) Y)‖ ^ 2
      ≤ 2 * (1 + t) * δ ^ 2 * Lp
          + 2 * Cpk * (1 / t) ^ p * (Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) := hsplit
    _ ≤ δ * Lp + 2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by
        linarith [hprin, hrest_fold]
    _ = δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p D‖ ^ 2
          + 2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by rw [hLpd]
    _ = δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
            (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2
          + 2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr)
            * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q
                    (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
        rw [hDd, hSlowd, hSTd]

end Connection
end Integral
end DifferentialGeometry

end
