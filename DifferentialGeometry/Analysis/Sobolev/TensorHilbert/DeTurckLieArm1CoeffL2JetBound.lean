import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open TensorMultilinear
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem exists_fn_of_forall_exists_bounded (N : ℕ) (Q : ℕ → ℝ → Prop)
    (h : ∀ k, k ≤ N → ∃ c : ℝ, 0 ≤ c ∧ Q k c) :
    ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ k, k ≤ N → Q k (f k) := by
  induction N with
  | zero =>
    obtain ⟨c, hc0, hc⟩ := h 0 le_rfl
    refine ⟨fun _ => c, fun _ => hc0, ?_⟩
    intro k hk
    rw [Nat.le_zero.mp hk]
    exact hc
  | succ N ih =>
    obtain ⟨f, hf0, hf⟩ := ih (fun k hk => h k (le_trans hk (Nat.le_succ N)))
    obtain ⟨c, hc0, hc⟩ := h (N + 1) le_rfl
    refine ⟨Function.update f (N + 1) c, ?_, ?_⟩
    · intro k
      by_cases hk : k = N + 1
      · rw [hk, Function.update_self]; exact hc0
      · rw [Function.update_of_ne hk]; exact hf0 k
    · intro k hk
      by_cases hkN : k = N + 1
      · rw [hkN, Function.update_self]; exact hc
      · rw [Function.update_of_ne hkN]
        exact hf k (by omega)

private theorem lieArm1_metricInner_injective (g : SmoothRiemannianMetric I M) (x : M)
    {v w : TangentSpace I x} (h : ∀ u : TangentSpace I x, g.inner x v u = g.inner x w u) :
    v = w := by
  by_contra hne
  have hvw : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.pos x (v - w) hvw
  have hzero : g.inner x (v - w) (v - w) = 0 := by
    have h' := h (v - w)
    rw [show (g.inner x) (v - w) = (g.inner x) v - (g.inner x) w from
        map_sub (g.inner x) v w,
      ContinuousLinearMap.sub_apply, h', sub_self]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

private def lieArm1SharpModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  cometricLmodel (I := I) g₁ x
    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis k))

private theorem lieArm1_cometric_collapse (g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) • lieArm1SharpModel (I := I) g₁ x k = w := by
  classical
  refine lieArm1_metricInner_injective (I := I) g₁ x (fun u => ?_)
  rw [show g₁.inner x (∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x w ((Module.finBasis ℝ E) k) • lieArm1SharpModel (I := I) g₁ x k) u =
      ∑ k : Fin (Module.finrank ℝ E), g₁.inner x w ((Module.finBasis ℝ E) k) *
        g₁.inner x (lieArm1SharpModel (I := I) g₁ x k) u from by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl]
  have hdual : ∀ k : Fin (Module.finrank ℝ E),
      g₁.inner x (lieArm1SharpModel (I := I) g₁ x k) u =
        ((Module.finBasis ℝ E).cDualBasis k) (u : E) := fun k =>
    cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((Module.finBasis ℝ E).cDualBasis k) u
  rw [Finset.sum_congr rfl fun k _ => by rw [hdual k]]
  have hcd : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k) (u : E) =
        (Module.finBasis ℝ E).repr (u : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k : E →L[ℝ] ℝ)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).dualBasis k) from rfl,
      LinearMap.coe_toContinuousLinearMap']
    exact Module.Basis.dualBasis_apply (Module.finBasis ℝ E) k (u : E)
  rw [Finset.sum_congr rfl fun k _ => by rw [hcd k]]
  have hrepr : (u : TangentSpace I x) = ∑ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).repr (u : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    exact_mod_cast ((Module.finBasis ℝ E).sum_repr (u : E)).symm
  conv_rhs => rw [hrepr]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [smul_eq_mul, mul_comm]

def lieArm1Piece (g₀ g₁ : SmoothRiemannianMetric I M) (σ' : Equiv.Perm (Fin 4))
    (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2) : SmoothCcTensor g₀ 3 2 :=
  reindexCoeffGen (I := I) (M := M) g₀ 3 2
    (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
      (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
    ρ

private def lieArm1TraceArg (g₁ : SmoothRiemannianMetric I M) (σ' : Equiv.Perm (Fin 4)) (x : M)
    (m : Fin 2 → TangentSpace I x) (k : Fin (Module.finrank ℝ E)) : Fin 4 → E :=
  (Fin.cons ((lieArm1SharpModel (I := I) g₁ x k : TangentSpace I x) : E)
    (Fin.cons (((Module.finBasis ℝ E) k : E)) (fun j : Fin 2 => ((m j : TangentSpace I x) : E)))) ∘ σ'

set_option linter.unusedSectionVars false in
private theorem lieArm1Piece_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (Ψ : SmoothCcTensor g₀ 1 2)
    (K : ∀ y : M, TangentSpace I y → TangentSpace I y → TangentSpace I y) (x : M)
    (hΨ : ∀ (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x),
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) om) YZ =
        om (fun _ : Fin 1 => K x (YZ 0) (YZ 1)))
    (D : Tensor0SSpace 3 I x) (m : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) D)
        (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ((Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 0)
            (Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 1)
              (fun _ : Fin 1 =>
                ((K x ((lieArm1TraceArg (I := I) g₁ σ' x m k 2 : E) : TangentSpace I x)
                    ((lieArm1TraceArg (I := I) g₁ σ' x m k 3 : E) : TangentSpace I x) :
                  TangentSpace I x) : E)))) ∘ ρ) := by
  classical
  set D' : Tensor0SSpace 3 I x :=
    Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel D))
    with hD'
  have happ : (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ).toSection x) D =
      deTurckLieTraceFib (I := I) g₁ σ' x
        (slotExtendFib (I := I) (M := M) g₀ 2 3 x
          (slotExtendFib (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x)) D') := by
    rw [lieArm1Piece, reindexCoeffGen_toSection]
    rw [reindexCoeffFibGen_apply (I := I) 3 2 ρ x
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection x)
      D]
    rw [appCcRS_toSection]
    rw [ContinuousLinearMap.comp_apply]
    rw [deTurckLieTraceCoeff_toSection]
    rfl
  rw [happ]
  set U : Tensor0SSpace 4 I x :=
    slotExtendFib (I := I) (M := M) g₀ 2 3 x
      (slotExtendFib (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x)) D' with hU
  have htr : Tensor0SSpace.toModel (deTurckLieTraceFib (I := I) g₁ σ' x U)
      (fun j : Fin 2 => ((m j : TangentSpace I x) : E)) =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel U (lieArm1TraceArg (I := I) g₁ σ' x m k) := by
    rw [show deTurckLieTraceFib (I := I) g₁ σ' x U =
        cometricDoubleTraceFib (I := I) g₁ 2 x (domDomCongrFibPerm (I := I) σ' x U) from rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [domDomCongrFibPerm_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [modelDoubleTrace_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [htr]
  refine Finset.sum_congr rfl fun k _ => ?_
  set w : Fin 4 → E := lieArm1TraceArg (I := I) g₁ σ' x m k with hw
  set D₂ : Tensor0SSpace 2 I x :=
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x) D' (w 0) with hD₂
  set om : Tensor0SSpace 1 I x :=
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D₂ (w 1) with hom
  set kE : E := ((K x ((w 2 : E) : TangentSpace I x) ((w 3 : E) : TangentSpace I x) :
    TangentSpace I x) : E) with hkE
  calc Tensor0SSpace.toModel U w
      = Tensor0SSpace.toModel U (Fin.cons (w 0) (Matrix.vecTail w)) :=
        congrArg (Tensor0SSpace.toModel U) (Fin.cons_self_tail w).symm
    _ = Tensor0SSpace.toModel
          (slotExtendFib (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) D₂)
          (Matrix.vecTail w) := by
        rw [hU]
        exact slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 3 x _ D' (w 0) (Matrix.vecTail w)
    _ = Tensor0SSpace.toModel
          (slotExtendFib (I := I) (M := M) g₀ 1 2 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) D₂)
          (Fin.cons (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))) :=
        congrArg (Tensor0SSpace.toModel _) (Fin.cons_self_tail (Matrix.vecTail w)).symm
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from Ψ.toSection x) om)
          (Matrix.vecTail (Matrix.vecTail w)) := by
        exact slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x _ D₂ (Matrix.vecTail w 0)
          (Matrix.vecTail (Matrix.vecTail w))
    _ = om (fun _ : Fin 1 =>
          K x ((w 2 : E) : TangentSpace I x) ((w 3 : E) : TangentSpace I x)) :=
        hΨ om (fun j : Fin 2 => ((Matrix.vecTail (Matrix.vecTail w) j : E) : TangentSpace I x))
    _ = Tensor0SSpace.toModel om (fun _ : Fin 1 => kE) := rfl
    _ = Tensor0SSpace.toModel D₂ (Fin.cons (w 1) (fun _ : Fin 1 => kE)) := by
        rw [hom]
        exact tensor0S_curry_apply_eval (I := I) (M := M) (n := 1) D₂ (w 1) (fun _ : Fin 1 => kE)
    _ = Tensor0SSpace.toModel D' (Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin 1 => kE))) := by
        rw [hD₂]
        exact tensor0S_curry_apply_eval (I := I) (M := M) (n := 2) D' (w 0)
          (Fin.cons (w 1) (fun _ : Fin 1 => kE))
    _ = Tensor0SSpace.toModel D
          ((Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin 1 => kE))) ∘ ρ) := by
        rw [hD', Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.domDomCongr_apply]
        rfl
    _ = Tensor0SSpace.toModel D
          ((Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 0)
            (Fin.cons (lieArm1TraceArg (I := I) g₁ σ' x m k 1)
              (fun _ : Fin 1 =>
                ((K x ((lieArm1TraceArg (I := I) g₁ σ' x m k 2 : E) : TangentSpace I x)
                    ((lieArm1TraceArg (I := I) g₁ σ' x m k 3 : E) : TangentSpace I x) :
                  TangentSpace I x) : E)))) ∘ ρ) := rfl

def lieArm1ConnDiffBgCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₁ g_bg).toSection
  hasCompactSupport := (connDiffSection (I := I) g₁ g_bg).hasCompactSupport

set_option linter.unusedSectionVars false in
@[simp] theorem lieArm1ConnDiffBgCc_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      connDiffFib (I := I) g₁ g_bg x := rfl

def lieArm1LoweredBgKappa (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection := (connDiffLoweredCc (I := I) g₁ g_bg).toSection
  hasCompactSupport := (connDiffLoweredCc (I := I) g₁ g_bg).hasCompactSupport

def lieArm1PsiB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  appCcRS (I := I) (M := M) g₀ 1 1 2
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ (⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ :
        Equiv.Perm (Fin 3))
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
    (sharpFlatEndoCc (I := I) g₀ g₁)

def lieArm1RhoSlot0 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

def lieArm1RhoSlot1 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

def lieArm1SigmaA : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

def lieArm1SigmaASwap : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩

def lieArm1SigmaC : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

def lieArm1SigmaCSwap : Equiv.Perm (Fin 4) := ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

def lieArm1SigmaD : Equiv.Perm (Fin 4) := ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩

def lieArm1SigmaDSwap : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

def lieArm1SigmaESwap : Equiv.Perm (Fin 4) := ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

def lieArm1SigmaF : Equiv.Perm (Fin 4) := ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩

def lieArm1SigmaFSwap : Equiv.Perm (Fin 4) := ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

theorem deTurckLieArm1Coeff_eq_lieArm1Piece_sum (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg =
      lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
        + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)
          - lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀) := by
  sorry

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            P i := by
  sorry

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiffBg_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  sorry

set_option linter.unusedVariables false in
theorem lieArm1Piece_psiB_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  sorry

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiff_realizedFam_rfns_order0_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                  g₀)).toSection x) ≤ Λ := by
  sorry

set_option linter.unusedVariables false in
theorem lieArm1Piece_connDiffBg_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  sorry

set_option linter.unusedVariables false in
theorem lieArm1Piece_psiB_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  sorry

private theorem lieArm1_norm_block6_le {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 - b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 - b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 - b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 - b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 - b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3) b4
        linarith
    _ ≤ (((‖b1 - b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_sq_le_of_norm_le {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {S : ℝ} (h : ‖v‖ ≤ S) : ‖v‖ ^ 2 ≤ S ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg v) h 2

private theorem lieArm1_norm_le_sqrt {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {P : ℝ} (h : ‖v‖ ^ 2 ≤ P) : ‖v‖ ≤ Real.sqrt P := by
  have h1 : ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt h

set_option linter.unusedVariables false in
theorem deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨Pc, hPc_nn, hPc⟩ :=
    lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Pbg, hPbg_nn, hPbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    lieArm1Piece_psiB_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => (11 * Real.sqrt (Pc i) + 2 * Real.sqrt (Pb i) + Real.sqrt (Pbg i)) ^ 2,
    fun i => sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ (connDiffSection (I := I) g₁ g₀))‖ ≤
        Real.sqrt (Pc i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hbg : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pbg i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pb i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg]
  simp only [iteratedCovGrad_add, iteratedCovGrad_sub]
  refine lieArm1_norm_sq_le_of_norm_le ?_
  have hsqrtPc_nn : 0 ≤ Real.sqrt (Pc i) := Real.sqrt_nonneg _
  have hsqrtPb_nn : 0 ≤ Real.sqrt (Pb i) := Real.sqrt_nonneg _
  have hblock1 := lieArm1_norm_block6_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have hblock2 := lieArm1_norm_block6_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have htri1 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
  have htri2 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have htri3 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have h1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have h2 := hpb lieArm1SigmaA (Equiv.refl (Fin 3))
  have h3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have h4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have h5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have h6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have h7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h8 := hpb lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have h10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have h11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have h12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have h13 := hbg lieArm1SigmaC lieArm1RhoSlot0
  have h14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [htri1, htri2, htri3, hblock1, hblock2]

private theorem lieArm1_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

private theorem lieArm1_rfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  rw [sub_eq_add_neg]
  have h := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
  rw [lieArm1_rfns_neg (I := I) (M := M) g r s x b] at h
  exact h

private theorem lieArm1_rfns_block6_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5) b6
  have h5 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4) b5
  have h4 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3) b4
  have h3 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2) b3
  have h2 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

set_option linter.unusedVariables false in
theorem deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    lieArm1Piece_connDiff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Λbg, hΛbg_nn, hΛbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λb, hΛb_nn, hΛb⟩ :=
    lieArm1Piece_psiB_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨8 * Λbg + 800 * Λc + 400 * Λb, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λc := fun σ' ρ =>
    hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ s hs x
  have hbg : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      ((lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λbg :=
    hΛbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball lieArm1SigmaC lieArm1RhoSlot0 s hs x
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((lieArm1Piece (I := I) (M := M) g₀ g₁ σ' (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λb := fun σ' =>
    hΛb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' (Equiv.refl (Fin 3)) s hs x
  have hsec := congrArg (fun (W : SmoothCcTensor g₀ 3 2) =>
      (show TensorRSSpace 3 2 I x from W.toSection x))
    (deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg)
  simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply] at hsec
  rw [hsec]
  set A := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B1 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B2 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B3 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B4 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B5 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B6 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C1 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C2 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set C3 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C4 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C5 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C6 := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set Dz := (show TensorRSSpace 3 2 I x from
    (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  have houter1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 - B2 - B3 - B4 - B5 - B6) + (C1 - C2 - C3 - C4 - C5 - C6)) Dz
  have houter2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 - B2 - B3 - B4 - B5 - B6)) (C1 - C2 - C3 - C4 - C5 - C6)
  have houter3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    A (B1 - B2 - B3 - B4 - B5 - B6)
  have hblkB := lieArm1_rfns_block6_le (I := I) (M := M) g₀ 3 2 x B1 B2 B3 B4 B5 B6
  have hblkC := lieArm1_rfns_block6_le (I := I) (M := M) g₀ 3 2 x C1 C2 C3 C4 C5 C6
  have e1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have e2 := hpb lieArm1SigmaA
  have e3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have e4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have e5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have e6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have e7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have e8 := hpb lieArm1SigmaASwap
  have e9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have e10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have e11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have e12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have e14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [houter1, houter2, houter3, hblkB, hblkC, hbg, hΛc_nn, hΛb_nn, hΛbg_nn]

end DifferentialGeometry.Integral.Connection

end
