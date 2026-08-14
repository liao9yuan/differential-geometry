import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmDiff
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise

/-!
# Integration by parts in the forward-uniqueness lane's currency

The forward-uniqueness lane (`ForwardUniqueRmDiff.lean` and its consumers) works with
*field-level* `(0,s)` tensors — `Tensor0SField … s` — and the everywhere-defined operators
`metricNabla0S` (one Levi-Civita step, derivative slot `0`) and `covDiv0SField`
(`g`-trace of slots `0,1` of `metricNabla0S`).  The Green/IBP machinery
(`Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/`) instead consumes the *bundled*
compactly-supported type `SmoothCcTensor g 0 s` and its operators `covGrad`, `covDivergence`.

This file is the bridge (brick `K2.7`).  On a closed manifold it

* packages a lane field as a `SmoothCcTensor` (`ccLift0S`, compact support from
  `CompactSpace M`);
* identifies the two `∇` and the two `div` under that lift
  (`covGradLift_eq`, `covDivLift_eq`);
* and specialises the pairing theorem
  `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence` to lane currency
  (`l2Inner_nabla_eq_neg_div`), together with the principal Dirichlet partner
  (`l2Inner_nabla_self_eq_neg_lap`).

## Instance note

Unlike the rest of the lane, this file carries `[InnerProductSpace ℝ E]` on the model space.
That is *not* a choice: `covDivergence` and `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`
are stated over `[InnerProductSpace ℝ E]` (their orthonormal frame `smoothOrthoFrame` is built in
the model), so the identification theorems below cannot even be *typed* without it.  Removing the
taint is a producer-side `omit` campaign in the Green/IBP layer, not a job for this bridge.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

section Lift

variable {s : ℕ}

/-- **The lane lift.**  A smooth field-level `(0,s)` tensor on a closed manifold, packaged as
the bundled compactly-supported `(0,s)` tensor consumed by the Green/IBP layer.  The section is
the canonical unit-scalar lift `Tensor0SSpace s ≃ TensorRSSpace 0 s`; compact support is free
from `CompactSpace M`. -/
def ccLift0S (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    SmoothCcTensor g 0 s where
  toSection := unitScalarRSLiftCₛ (I := I) (M := M) T
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem ccLift0S_toSection (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    (ccLift0S (I := I) g T).toSection x =
      unitScalarRSLiftSection (I := I) (M := M) (fun y : M => T y) x := rfl

/-- **Unit evaluation of the lift returns the original field.** -/
@[simp] theorem ccLift0S_unit (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (ccLift0S (I := I) g T).toSection x)
        (unitZeroSec (I := I) (M := M) x) = T x :=
  unitScalarRSLiftSection_apply_unit (I := I) (M := M) (fun y : M => T y) x

/-- The model `(0,s)`-form of the lift is the model form of the field. -/
@[simp] theorem ccLift0S_unitModel (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    unitModel (I := I) (M := M) g s (ccLift0S (I := I) g T) x =
      Tensor0SSpace.toModel (T x) := by
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (ccLift0S (I := I) g T).toSection x)
        (unitZeroSec (I := I) (M := M) x)) = Tensor0SSpace.toModel (T x)
  rw [ccLift0S_unit]

end Lift

section Identification

variable {s : ℕ}

/-- **Directional covariant derivative of the lift, read at the unit.**  The bundled
`(r = 0, s)` covariant derivative of `ccLift0S g T` in the direction `v` is the lane's
`metricNabla0S g T` with `v` in its slot-`0` derivative position. -/
theorem covDerivLift_unit (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (v : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => (ccLift0S (I := I) g T).toSection y) x v)
        (unitZeroSec (I := I) (M := M) x) slots =
      metricNabla0S (I := I) g T x (Fin.cons v slots) := by
  classical
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  subst hX
  have hsec : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[Real] Tensor0SSpace s I y from
        (ccLift0S (I := I) g T).toSection y) (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M => T y) := by
    funext y
    exact ccLift0S_unit (I := I) g T y
  have key :
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => (ccLift0S (I := I) g T).toSection y) x (X x))
        (unitZeroSec (I := I) (M := M) x) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
        (LeviCivita (I := I) g) X T x := by
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s
      (ccLift0S (I := I) g T).toSection x (X x)]
    rw [hsec]
    exact (nabla0SFun_eq_tensor0SCovariantDerivative (I := I) g s X T x).symm
  have hslot :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (LeviCivita (I := I) g) X T x slots =
        metricNabla0S (I := I) g T x (Fin.cons (X x) slots) :=
    (totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
      (LeviCivita (I := I) g) X T x slots).symm
  exact (congrArg (fun A : Tensor0SSpace s I x => A slots) key).trans hslot

/-- Pointwise evaluation distributes over a finite sum of `(0,s)` fibre tensors.  (The fibre
`AddCommGroup` is `inferInstanceAs` the multilinear-map one, so each step is `rfl`; this lemma
exists only to give `rw` a syntactic handle.) -/
private theorem tensor0SSum_apply {x : M} {s : ℕ} {ι : Type*} (t : Finset ι)
    (F : ι → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (m : Fin s → TangentSpace I x) :
    (∑ i ∈ t, F i) m = ∑ i ∈ t, F i m := by
  classical
  refine Finset.cons_induction_on t ?_ ?_
  · rfl
  · intro a u ha ih
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

/-- A `g`-orthonormal basis of `TangentSpace I x` realised by the centred smooth frame
`smoothOrthoFrame g x`.  (Local replica of the private `centeredFrame_basis_exists` of
`TensorCovDivergence.lean`.) -/
private theorem orthoBasisAt (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ frame : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
      (∀ i, frame i = smoothOrthoFrame (I := I) g x i x) ∧
      (∀ i j, g.inner x (frame i) (frame j) = if i = j then (1 : Real) else 0) := by
  classical
  have hON : ∀ i j, g.inner x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent Real
      (fun i : Fin (Module.finrank Real E) => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk
    have hzero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at hzero
    have hpull : ∀ j ∈ fs,
        g.inner x (smoothOrthoFrame (I := I) g x k x)
          (c j • smoothOrthoFrame (I := I) g x j x) =
        c j * (if k = j then (1 : Real) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul
        (c j) (smoothOrthoFrame (I := I) g x j x), smul_eq_mul, hON k j]
    rw [Finset.sum_congr rfl hpull] at hzero
    rw [Finset.sum_eq_single_of_mem k hk] at hzero
    · rw [if_pos rfl, mul_one] at hzero
      exact hzero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank Real E)) = Module.finrank Real E :=
    Fintype.card_fin _
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_⟩
  · intro i
    change (basisOfLinearIndependentOfCardEqFinrank hli hcard :
      Fin (Module.finrank Real E) → TangentSpace I x) i =
        smoothOrthoFrame (I := I) g x i x
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  · intro i j
    rw [show (basisOfLinearIndependentOfCardEqFinrank hli hcard :
          Fin (Module.finrank Real E) → TangentSpace I x) i =
            smoothOrthoFrame (I := I) g x i x from by
          rw [coe_basisOfLinearIndependentOfCardEqFinrank],
      show (basisOfLinearIndependentOfCardEqFinrank hli hcard :
          Fin (Module.finrank Real E) → TangentSpace I x) j =
            smoothOrthoFrame (I := I) g x j x from by
          rw [coe_basisOfLinearIndependentOfCardEqFinrank]]
    exact hON i j

/-- The `g`-trace of the first two slots of a `(0,s+2)` tensor is the diagonal frame sum over
any `g`-orthonormal basis. -/
private theorem traceFirstTwo_eq_frame_sum (g : SmoothRiemannianMetric I M) {x : M}
    (frame : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (frame i) (frame j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (slots : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g A slots =
      ∑ i : Fin (Module.finrank Real E), A (Fin.cons (frame i) (Fin.cons (frame i) slots)) := by
  classical
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g frame
    (fun a k => if a = k then (1 : Real) else 0)
    (metricInverseInBasis_of_orthonormal (I := I) g frame hON) A slots]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · change (if i = i then (1 : Real) else 0) *
        A (metricTraceInput (I := I) (frame i) (frame i) slots) = _
    rw [if_pos rfl, one_mul]
    rfl
  · intro j _ hji
    change (if i = j then (1 : Real) else 0) *
        A (metricTraceInput (I := I) (frame i) (frame j) slots) = 0
    rw [if_neg (fun h => hji h.symm), zero_mul]

/-- **The lane divergence is the bundled divergence.**  Under `ccLift0S`, the bundled
`covDivergence` of the Green/IBP layer, read at the unit `(0,0)`-tensor, is the lane's
`covDiv0SField`.  Both contract the new derivative slot against the tensor's slot `0`
with `g`. -/
theorem covDivLift_unit (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) (x : M) :
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V)).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      covDiv0SField (I := I) g V x := by
  classical
  obtain ⟨frame, hfr, hON⟩ := orthoBasisAt (I := I) g x
  have hraw : (covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V)).toSection x =
      ∑ i : Fin (Module.finrank Real E),
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          covDivergenceBilinear (I := I) (M := M) g s (ccLift0S (I := I) g V) x
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)) := rfl
  rw [hraw, ContinuousLinearMap.sum_apply]
  refine DFunLike.ext _ _ fun slots => ?_
  have hterm : ∀ i : Fin (Module.finrank Real E),
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        covDivergenceBilinear (I := I) (M := M) g s (ccLift0S (I := I) g V) x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) slots =
      metricNabla0S (I := I) g V x
        (Fin.cons (frame i) (Fin.cons (frame i) slots)) := by
    intro i
    have hsmooth : MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
          (smoothOrthoFrame (I := I) g x i z)) x :=
      (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
    rw [codiffPsi_apply (I := I) (M := M) g s (ccLift0S (I := I) g V) x hsmooth hsmooth]
    have hcontract :
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          contract_covariant 0 s x (smoothOrthoFrame (I := I) g x i x)
            (TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)
              (fun z : M => (ccLift0S (I := I) g V).toSection z) x
              (smoothOrthoFrame (I := I) g x i x)))
          (unitZeroSec (I := I) (M := M) x) slots =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace (s + 1) I x from
          TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)
            (fun z : M => (ccLift0S (I := I) g V).toSection z) x
            (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x)
          (Fin.cons (smoothOrthoFrame (I := I) g x i x) slots) := rfl
    rw [hcontract, hfr i]
    exact covDerivLift_unit (I := I) g V x (smoothOrthoFrame (I := I) g x i x)
      (Fin.cons (smoothOrthoFrame (I := I) g x i x) slots)
  rw [tensor0SSum_apply (I := I) (M := M) Finset.univ
    (fun i : Fin (Module.finrank Real E) =>
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        covDivergenceBilinear (I := I) (M := M) g s (ccLift0S (I := I) g V) x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x)) slots]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [covDiv0SField, metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply]
  exact (traceFirstTwo_eq_frame_sum (I := I) g frame hON
    (metricNabla0S (I := I) g V x) slots).symm

/-- **The lane divergence is the bundled divergence (bundled form).** -/
theorem covDivLift_eq (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V) =
      ccLift0S (I := I) g (covDiv0SField (I := I) g V) := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [ccLift0S_unitModel]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
    Tensor0SSpace.toModel (covDiv0SField (I := I) g V x)
  rw [covDivLift_unit]

/-- **The lane covariant derivative is the bundled gradient.**  Under `ccLift0S`, `covGrad`
of the Green/IBP layer is the lane's `metricNabla0S`. -/
theorem covGradLift_eq (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    covGrad (I := I) (M := M) g 0 s (ccLift0S (I := I) g T) =
      ccLift0S (I := I) g (metricNabla0S (I := I) g T) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [ccLift0S_unitModel]
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hcons : v = Fin.cons (v 0) (Matrix.vecTail v) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro k; simp [Matrix.vecTail]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s (ccLift0S (I := I) g T)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) v =
    Tensor0SSpace.toModel (metricNabla0S (I := I) g T x) v
  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g s (ccLift0S (I := I) g T) x v]
  rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s (ccLift0S (I := I) g T) x (v 0)]
  have hval := covDerivLift_unit (I := I) g T x (v 0) (Matrix.vecTail v)
  refine hval.trans ?_
  conv_rhs => rw [hcons]
  rfl

end Identification

section Payoff

variable {s : ℕ}

/-- **Integration by parts in lane currency.**  For a smooth field-level `(0,s)` tensor `T` and
a smooth field-level `(0,s+1)` tensor `V` on a closed manifold,
`⟨∇^g T, V⟩_{L²(g)} = −⟨T, div_g V⟩_{L²(g)}`,
with `∇^g = metricNabla0S g` and `div_g = covDiv0SField g` the lane's operators.  This is the
K4 entry point: the rate estimates consume this without touching `SmoothCcTensor` plumbing
beyond `ccLift0S`. -/
theorem l2Inner_nabla_eq_neg_div (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ccLift0S (I := I) g (metricNabla0S (I := I) g T)).toFun
        (ccLift0S (I := I) g V).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (ccLift0S (I := I) g T).toFun
          (ccLift0S (I := I) g (covDiv0SField (I := I) g V)).toFun := by
  rw [← covGradLift_eq (I := I) g T, ← covDivLift_eq (I := I) g V]
  exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence (I := I) (M := M) g s
    (ccLift0S (I := I) g T) (ccLift0S (I := I) g V)

/-- **Dirichlet form in lane currency.**  `⟨∇^g T, ∇^g T⟩_{L²(g)} = −⟨T, Δ_g T⟩_{L²(g)}` with
`Δ_g = roughLap0SField g = div_g ∘ ∇^g` the lane's rough Laplacian.  Specialisation of
`l2Inner_nabla_eq_neg_div` at `V = ∇^g T`. -/
theorem l2Inner_nabla_self_eq_neg_lap (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ccLift0S (I := I) g (metricNabla0S (I := I) g T)).toFun
        (ccLift0S (I := I) g (metricNabla0S (I := I) g T)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (ccLift0S (I := I) g T).toFun
          (ccLift0S (I := I) g (roughLap0SField (I := I) g T)).toFun :=
  l2Inner_nabla_eq_neg_div (I := I) g T (metricNabla0S (I := I) g T)

end Payoff

end DifferentialGeometry.PDE.RicciFlow
