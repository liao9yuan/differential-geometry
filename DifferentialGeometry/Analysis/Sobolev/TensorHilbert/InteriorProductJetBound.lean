import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound

/-!
# Interior-product-with-lowered-vector jet bound

The **ip-vector Leibniz jet engine**: for a metric `g` and a `(0, 1)`-tensor `om` (the
`g`-lowered form of a vector field `V`), the `(2, 1)`-operator field

    ipLowCc g om = (g-cometric double trace) ∘ (slot swap) ∘ (A ↦ A ⊗ om)

acts on `(0, 2)`-tensors as the interior product `A ↦ A(♯om, ·)` (`ipLowCc_toSec_ip`), and its
iterated covariant jets are dominated, order by order, by the jets of `om` alone
(`rfns_icg_ipLow_le`, pointwise; `norm_icg_ipLow_le`, jet-`L²`).

This is the interior-product sibling of `rfns_iteratedCovGrad_slotExtend_le`.  It is *not*
placed next to that lemma in `OperatorFieldFibreNormJet` because its proof consumes the
`appCcRS` diagonal product grid, which lives one layer up in `MetricArmCoeffJetTower`; the
composition `ipLowCc` is built from committed pieces (`cometricDoubleTraceField` — parallel by
`cometricDoubleTraceField_covGrad_eq_zero` — a source-slot reindex, and a double `slotExtend`
of `om`), so all jets reduce to committed engines with no new Leibniz induction.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad covGrad_zero unitTensor unitModel
    reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen reindexCoeffFibGen_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The slot arrangement feeding the cometric double trace in `ipLowCc`: the trace contracts
its diagonal pair against slot `0` of `A` and the `om`-slot of `A ⊗ om`, so the trace tuple
`(e, e, w)` must be read by `A ⊗ om` as `(e, w, e)`. -/
def ipTracePerm : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- **Interior product with a lowered vector, as a `(2, 1)`-operator field.**  For a
`(0, 1)`-tensor `om` over `g`, the operator `A ↦ A(♯om, ·)` on `(0, 2)`-tensors, realized as
the `g`-cometric double trace of `A ⊗ om` (with the `om`-slot permuted against slot `0` of `A`).
When `om = V♭` (`g`-flat of a vector field `V`) this is the slot-`0` interior product `ι_V`
(`ipLowCc_toSec_ip`).  Built entirely from committed operator-field constructions, so its
covariant jets reduce to the jets of `om` (`rfns_icg_ipLow_le`). -/
noncomputable def ipLowCc (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1) :
    SmoothCcTensor g 2 1 :=
  appCcRS (I := I) (M := M) g 2 3 1
    (reindexCoeffGen (I := I) (M := M) g 3 1
      (cometricDoubleTraceField (I := I) g 1) ipTracePerm)
    (slotExtend (I := I) (M := M) g 1 2 (slotExtend (I := I) (M := M) g 0 1 om))

section Eval

set_option linter.unusedSectionVars false in
/-- Rank-`0` tensors are scalar multiples of the unit tensor. -/
private lemma ipjb_rank0_smul_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have h1 : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

set_option linter.unusedSectionVars false in
/-- The smooth orthonormal frame at its center is a basis of the tangent space. -/
private theorem ipjb_orthoFrame_basis (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (smoothOrthoFrame (I := I) g x k x)
        (c j • smoothOrthoFrame (I := I) g x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

/-- Orthonormal-frame expansion of a tangent vector at the frame center. -/
private theorem ipjb_orthoFrame_expansion (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x i x) •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  obtain ⟨bse, hbse⟩ := ipjb_orthoFrame_basis (I := I) (M := M) g x
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x j x) = bse.repr u j := by
    intro j
    rw [g.symm x u (smoothOrthoFrame (I := I) g x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g.inner x (smoothOrthoFrame (I := I) g x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g.inner x u (smoothOrthoFrame (I := I) g x i x) •
          smoothOrthoFrame (I := I) g x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

/-- Center evaluation of the rank-`1` cometric double trace: the `g`-orthonormal diagonal sum. -/
private lemma ipjb_trace_center (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (m : Fin 1 → E) :
    Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g 1 x D) m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E) m)) := by
  rw [show Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g 1 x D) m =
      modelDoubleTrace (E := E) 1 (cometricLmodel (I := I) g x)
        (Tensor0SSpace.toModel D) m from by
    rw [cometricDoubleTraceFib_toModel (I := I) g 1 x D]]
  rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g x)
    (Tensor0SSpace.toModel D) m]
  exact cometric_dualTrace_eq_orthoFrame_diag (I := I) g (s := 1) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) m

/-- Tuple evaluation of the double `slotExtend`: the `(A ⊗ om)`-reading. -/
private lemma ipjb_slotExt2_toModel (g : SmoothRiemannianMetric I M)
    (om : SmoothCcTensor g 0 1) (x : M) (A : Tensor0SSpace 2 I x) (u0 u1 u2 : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g 1 2
            (slotExtend (I := I) (M := M) g 0 1 om)).toSection x) A)
        ![u0, u1, u2] =
      Tensor0SSpace.toModel A ![u0, u1] *
        unitModel (I := I) (M := M) g 1 om x ![u2] := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 om)).toSection x) A) ![u0, u1, u2] =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g 1 2 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (slotExtend (I := I) (M := M) g 0 1 om).toSection x) A)
        (Fin.cons u0 ![u1, u2]) := rfl
  rw [h0]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g 1 2 x
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      (slotExtend (I := I) (M := M) g 0 1 om).toSection x) A u0 ![u1, u2]]
  have h1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotExtend (I := I) (M := M) g 0 1 om).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x A u0)) ![u1, u2] =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g 0 1 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from om.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x A u0))
        (Fin.cons u1 ![u2]) := rfl
  rw [h1]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g 0 1 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from om.toSection x)
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x A u0) u1 ![u2]]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x A u0) u1 =
      Tensor0SSpace.toModel A ![u0, u1] • unitTensor (I := I) (M := M) x := by
    have h2 := ipjb_rank0_smul_unit (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x A u0) u1)
    rw [h2]
    congr 1
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [unitModel]

set_option linter.unusedSectionVars false in
/-- Slot-`0` multilinear expansion under a finite `smul`-sum. -/
private lemma ipjb_cons_sum_smul {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

end Eval

set_option linter.unusedSectionVars false in
/-- **`ipLowCc` is the interior product with the raised vector.**  If `om` reads at `x` as the
`g`-pairing with a vector `V` (i.e. `om = V♭` at `x`), then the fibre of `ipLowCc g om` at `x`
is the slot-`0` interior product `ι_V` on `(0, 2)`-tensors. -/
theorem ipLowCc_toSec_ip (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1)
    (x : M) (V : TangentSpace I x)
    (hflat : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g 1 om x (fun _ : Fin 1 => z) = g.inner x V z) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (ipLowCc (I := I) (M := M) g om).toSection x) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V := by
  classical
  apply ContinuousLinearMap.ext
  intro A
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V A) m =
      Tensor0SSpace.toModel A (Fin.cons (show E from V) (fun k => m k)) := by
    have h1 : Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V A) =
        Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) 1 (show E from V)
          (Tensor0SSpace.toModel A) := rfl
    rw [h1]
    rfl
  rw [hRHS]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (ipLowCc (I := I) (M := M) g om).toSection x) A) =
      reindexCoeffFibGen (I := I) 3 1 ipTracePerm x
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricDoubleTraceField (I := I) g 1).toSection x)
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g 1 2
            (slotExtend (I := I) (M := M) g 0 1 om)).toSection x) A) from rfl]
  set S : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtend (I := I) (M := M) g 1 2
        (slotExtend (I := I) (M := M) g 0 1 om)).toSection x) A with hS_def
  rw [reindexCoeffFibGen_apply (I := I) 3 1 ipTracePerm x
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
      (cometricDoubleTraceField (I := I) g 1).toSection x) S]
  rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
      (cometricDoubleTraceField (I := I) g 1).toSection x)
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ipTracePerm
            (Tensor0SSpace.toModel S)))) =
      cometricDoubleTraceFib (I := I) g 1 x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ipTracePerm
            (Tensor0SSpace.toModel S))) from by
    rw [cometricDoubleTraceField_toSection]]
  rw [ipjb_trace_center (I := I) (M := M) g x _ m]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr ipTracePerm
              (Tensor0SSpace.toModel S)))
          (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E) m)) =
      g.inner x V (smoothOrthoFrame (I := I) g x c x) *
        Tensor0SSpace.toModel A
          (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
            (fun k => m k)) := by
    intro c
    rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    have htuple : (fun i : Fin 3 =>
        ((Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E) m) :
            Fin 3 → E))
          (ipTracePerm i)) =
        (![((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E), m 0,
          ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)] : Fin 3 → E) := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
    rw [htuple]
    rw [hS_def, ipjb_slotExt2_toModel (I := I) (M := M) g om x A _ _ _]
    have hω : unitModel (I := I) (M := M) g 1 om x
        ![((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)] =
        g.inner x V (smoothOrthoFrame (I := I) g x c x) := by
      rw [show (![((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)] :
          Fin 1 → E) =
          (fun _ : Fin 1 => ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E))
          from by funext k; fin_cases k; rfl]
      exact hflat (smoothOrthoFrame (I := I) g x c x)
    rw [hω]
    rw [show (![((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E), m 0] :
        Fin 2 → E) =
        Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
          (fun k : Fin 1 => m k) from by
      funext k
      fin_cases k <;> rfl]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  have hVexp : (show E from V) =
      ∑ c : Fin (Module.finrank ℝ E),
        g.inner x V (smoothOrthoFrame (I := I) g x c x) •
          ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E) :=
    ipjb_orthoFrame_expansion (I := I) (M := M) g x V
  rw [show Tensor0SSpace.toModel A (Fin.cons (show E from V) (fun k => m k)) =
      Tensor0SSpace.toModel A
        (Fin.cons (∑ c : Fin (Module.finrank ℝ E),
          g.inner x V (smoothOrthoFrame (I := I) g x c x) •
            ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E))
          (fun k => m k)) from by rw [← hVexp]]
  exact (ipjb_cons_sum_smul (Tensor0SSpace.toModel A)
    (Module.finrank ℝ E)
    (fun c => g.inner x V (smoothOrthoFrame (I := I) g x c x))
    (fun c => ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E))
    (fun k => m k)).symm

/-! ## Jets -/

private lemma ipjb_icg_zero (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j (0 : SmoothCcTensor g r s) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedCovGrad_succ, ih]
      exact covGrad_zero (I := I) (M := M) (g := g) (r := r) (s := s + j)

set_option linter.unusedSectionVars false in
/-- The jets of the fixed rank-`1` cometric double trace vanish from order `1` on:
`∇(g⁻¹-double-trace) = 0` (`cometricDoubleTraceField_covGrad_eq_zero`). -/
private lemma ipjb_rfns_trace_succ (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g 3 1 (i + 1)
          (cometricDoubleTraceField (I := I) g 1)).toSection x) = 0 := by
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g 3 1 i
    (cometricDoubleTraceField (I := I) g 1) x]
  rw [show covGrad (I := I) (M := M) g 3 1 (cometricDoubleTraceField (I := I) g 1) =
      (0 : SmoothCcTensor g 3 2) from
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g 1]
  rw [ipjb_icg_zero (I := I) (M := M) g 3 2 i]
  rw [show ((0 : SmoothCcTensor g 3 (2 + i)).toSection x) =
      (0 : TensorRSSpace 3 (2 + i) I x) from rfl]
  exact riemannianFiberNormSq_zero (I := I) (M := M) g 3 (1 + 1 + i) x

set_option linter.unusedSectionVars false in
/-- **Pointwise jet bound for the interior product with a lowered vector.**  There are
constants `c l` (depending only on `g`, `l`, `dim E`) with
`|∇ˡ(ipLowCc g om)|² ≤ c l · ∑_{m ≤ l} |∇ᵐ om|²` pointwise, for every `om`.  The
interior-product sibling of `rfns_iteratedCovGrad_slotExtend_le`: the trace factor is
`∇`-parallel, so only its order-`0` fibre bound survives the product grid, and the
`slotExtend` factors each cost one dimension factor. -/
theorem rfns_icg_ipLow_le (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ l, 0 ≤ c l) ∧
      ∀ (om : SmoothCcTensor g 0 1) (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 2 (1 + l) x
            ((iteratedCovGrad (I := I) g 2 1 l
              (ipLowCc (I := I) (M := M) g om)).toSection x) ≤
          c l * ∑ m ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (1 + m) x
              ((iteratedCovGrad (I := I) g 0 1 m om).toSection x) := by
  classical
  obtain ⟨NC, hNC_nn, hNC⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g 3 1 (cometricDoubleTraceField (I := I) g 1)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : 0 ≤ n := by rw [hn_def]; positivity
  refine ⟨fun l => appCcGdiag (E := E) l * NC * (n * n), fun l =>
    mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) l) hNC_nn)
      (mul_nonneg hn_nn hn_nn), ?_⟩
  intro om l x
  set Carm : SmoothCcTensor g 3 1 :=
    reindexCoeffGen (I := I) (M := M) g 3 1
      (cometricDoubleTraceField (I := I) g 1) ipTracePerm with hCarm_def
  set P : SmoothCcTensor g 2 3 :=
    slotExtend (I := I) (M := M) g 1 2 (slotExtend (I := I) (M := M) g 0 1 om) with hP_def
  have hgrid := rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g l 2 3 1 Carm P x
  have hCarm_jets : ∀ i : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g 3 (1 + i) x
          ((iteratedCovGrad (I := I) g 3 1 i Carm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 3 (1 + i) x
          ((iteratedCovGrad (I := I) g 3 1 i
            (cometricDoubleTraceField (I := I) g 1)).toSection x) := by
    intro i
    rw [hCarm_def]
    exact rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g 3 1
      (cometricDoubleTraceField (I := I) g 1) ipTracePerm i x
  have hP_jets : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g 2 (3 + m) x
          ((iteratedCovGrad (I := I) g 2 3 m P).toSection x) ≤
        n * (n * riemannianFiberNormSq (I := I) (M := M) g 0 (1 + m) x
          ((iteratedCovGrad (I := I) g 0 1 m om).toSection x)) := by
    intro m
    rw [hP_def]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g 1 2
      (slotExtend (I := I) (M := M) g 0 1 om) m x) ?_
    refine mul_le_mul_of_nonneg_left ?_ hn_nn
    exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g 0 1 om m x
  set Pj : ℕ → ℝ := fun m => riemannianFiberNormSq (I := I) (M := M) g 2 (3 + m) x
    ((iteratedCovGrad (I := I) g 2 3 m P).toSection x) with hPj_def
  set Wj : ℕ → ℝ := fun m => riemannianFiberNormSq (I := I) (M := M) g 0 (1 + m) x
    ((iteratedCovGrad (I := I) g 0 1 m om).toSection x) with hWj_def
  have hPj_nn : ∀ m, 0 ≤ Pj m := fun m =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 2 (3 + m) x _
  have hWj_nn : ∀ m, 0 ≤ Wj m := fun m =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (1 + m) x _
  have hsingle : (∑ i ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g 3 (1 + i) x
            ((iteratedCovGrad (I := I) g 3 1 i Carm).toSection x) *
          ∑ m ∈ Finset.range (l + 1 - i), Pj m) ≤
      NC * ∑ m ∈ Finset.range (l + 1), Pj m := by
    rw [Finset.sum_eq_single 0]
    · rw [hCarm_jets 0]
      have h0 : riemannianFiberNormSq (I := I) (M := M) g 3 (1 + 0) x
          ((iteratedCovGrad (I := I) g 3 1 0
            (cometricDoubleTraceField (I := I) g 1)).toSection x) ≤ NC := hNC x
      have hsum_nn : 0 ≤ ∑ m ∈ Finset.range (l + 1 - 0), Pj m :=
        Finset.sum_nonneg (fun m _ => hPj_nn m)
      refine le_trans (mul_le_mul_of_nonneg_right h0 hsum_nn) ?_
      exact mul_le_mul_of_nonneg_left (le_refl _) hNC_nn
    · intro i hi hi0
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hCarm_jets (i' + 1), ipjb_rfns_trace_succ (I := I) (M := M) g i' x, zero_mul]
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0
  have hPsum : ∑ m ∈ Finset.range (l + 1), Pj m ≤
      (n * n) * ∑ m ∈ Finset.range (l + 1), Wj m := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m _ => ?_)
    calc Pj m ≤ n * (n * Wj m) := hP_jets m
      _ = (n * n) * Wj m := by ring
  calc riemannianFiberNormSq (I := I) (M := M) g 2 (1 + l) x
        ((iteratedCovGrad (I := I) g 2 1 l
          (ipLowCc (I := I) (M := M) g om)).toSection x)
      ≤ appCcGdiag (E := E) l * ∑ i ∈ Finset.range (l + 1),
          riemannianFiberNormSq (I := I) (M := M) g 3 (1 + i) x
              ((iteratedCovGrad (I := I) g 3 1 i Carm).toSection x) *
            ∑ m ∈ Finset.range (l + 1 - i), Pj m := hgrid
    _ ≤ appCcGdiag (E := E) l * (NC * ∑ m ∈ Finset.range (l + 1), Pj m) :=
        mul_le_mul_of_nonneg_left hsingle (appCcGdiag_nonneg (E := E) l)
    _ ≤ appCcGdiag (E := E) l * (NC * ((n * n) * ∑ m ∈ Finset.range (l + 1), Wj m)) := by
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) l)
        exact mul_le_mul_of_nonneg_left hPsum hNC_nn
    _ = appCcGdiag (E := E) l * NC * (n * n) * ∑ m ∈ Finset.range (l + 1), Wj m := by
        ring

set_option linter.unusedSectionVars false in
/-- **Jet-`L²` bound for the interior product with a lowered vector**: the integrated form of
`rfns_icg_ipLow_le`, `‖∇ˡ(ipLowCc g om)‖² ≤ c l · ∑_{m ≤ l} ‖∇ᵐ om‖²`. -/
theorem norm_icg_ipLow_le (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ l, 0 ≤ c l) ∧
      ∀ (om : SmoothCcTensor g 0 1) (l : ℕ),
        ‖iteratedCovGrad (I := I) g 2 1 l (ipLowCc (I := I) (M := M) g om)‖ ^ 2 ≤
          c l * ∑ m ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2 := by
  classical
  obtain ⟨c, hc_nn, hc⟩ := rfns_icg_ipLow_le (I := I) (M := M) g
  refine ⟨c, hc_nn, ?_⟩
  intro om l
  have hint : MeasureTheory.Integrable
      (fun x => c l * ∑ m ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (1 + m) x
          ((iteratedCovGrad (I := I) g 0 1 m om).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.Integrable.const_mul ?_ _
    exact MeasureTheory.integrable_finset_sum _ (fun m _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (1 + m)
        (iteratedCovGrad (I := I) g 0 1 m om))
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g 2 (1 + l)
    (iteratedCovGrad (I := I) g 2 1 l (ipLowCc (I := I) (M := M) g om)) _ hint
    (fun x => hc om l x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hc_nn l)
  rw [MeasureTheory.integral_finset_sum _ (fun m _ =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (1 + m)
      (iteratedCovGrad (I := I) g 0 1 m om))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 (1 + m)
      (iteratedCovGrad (I := I) g 0 1 m om),
    ← SmoothCcTensor.norm_def]

end DifferentialGeometry.Integral.Connection
