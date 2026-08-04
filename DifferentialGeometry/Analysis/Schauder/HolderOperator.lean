import DifferentialGeometry.Analysis.Schauder.HolderNormedSpace

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

section Map

variable {X F G : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]

omit [MetricSpace X] in
theorem eSupNormOn_comp_continuousLinearMap_le
    (L : F →L[Real] G) (f : X → F) :
    eSupNormOn Set.univ (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f := by
  rw [eSupNormOn_le]
  intro x _hx
  calc
    ENNReal.ofReal ‖L (f x)‖ ≤ ENNReal.ofReal (‖L‖ * ‖f x‖) :=
      ENNReal.ofReal_le_ofReal (L.le_opNorm (f x))
    _ = (‖L‖₊ : ENNReal) * ENNReal.ofReal ‖f x‖ := by
      rw [ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm_eq_enorm,
        enorm_eq_nnnorm]
    _ ≤ (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f :=
      mul_le_mul_right
        (norm_le_eSupNormOn Set.univ f x (Set.mem_univ x)) _

theorem eHolderNorm_comp_continuousLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G) {f : X → F}
    (hf : MemHolder alpha f) :
    eHolderNorm alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eHolderNorm alpha f := by
  have hcomp := L.lipschitz.holderWith.comp hf.holderWith
  calc
    eHolderNorm alpha (fun x ↦ L (f x)) ≤
        ((‖L‖₊ * nnHolderNorm alpha f : NNReal) : ENNReal) := by
      simpa only [Function.comp_apply, NNReal.coe_one, NNReal.rpow_one,
        mul_one, one_mul] using hcomp.eHolderNorm_le
    _ = (‖L‖₊ : ENNReal) * (nnHolderNorm alpha f : ENNReal) := by
      rw [ENNReal.coe_mul]
    _ ≤ (‖L‖₊ : ENNReal) * eHolderNorm alpha f :=
      mul_le_mul_right coe_nnHolderNorm_le_eHolderNorm _

theorem eHolderGauge_comp_continuousLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G) {f : X → F}
    (hf : IsBoundedHolder alpha f) :
    eHolderGauge alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eHolderGauge alpha f := by
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ (fun x ↦ L (f x)) +
        eHolderNorm alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f +
        (‖L‖₊ : ENNReal) * eHolderNorm alpha f :=
      add_le_add (eSupNormOn_comp_continuousLinearMap_le L f)
        (eHolderNorm_comp_continuousLinearMap_le L hf.memHolder)
    _ = (‖L‖₊ : ENNReal) *
        (eSupNormOn Set.univ f + eHolderNorm alpha f) := by
      rw [mul_add]

private def boundedHolderSpaceMapLinearMap
    (alpha : NNReal) (L : F →L[Real] G) :
    BoundedHolderSpace (X := X) (F := F) alpha →ₗ[Real]
      BoundedHolderSpace (X := X) (F := G) alpha where
  toFun f := ⟨fun x ↦ L (f x), by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2)
      (eHolderGauge_comp_continuousLinearMap_le L f.2)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    exact L.map_add (f x) (g x)
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    exact L.map_smul c (f x)

private theorem norm_boundedHolderSpaceMapLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖boundedHolderSpaceMapLinearMap alpha L f‖ ≤ ‖L‖ * ‖f‖ := by
  rw [norm_boundedHolderSpace_eq, norm_boundedHolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2)
    (eHolderGauge_comp_continuousLinearMap_le L f.2)
  simpa only [ENNReal.toReal_mul, ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    using hreal

def boundedHolderSpaceMap (alpha : NNReal) (L : F →L[Real] G) :
    BoundedHolderSpace (X := X) (F := F) alpha →L[Real]
      BoundedHolderSpace (X := X) (F := G) alpha :=
  LinearMap.mkContinuous (boundedHolderSpaceMapLinearMap alpha L) ‖L‖
    (norm_boundedHolderSpaceMapLinearMap_le L)

@[simp]
theorem boundedHolderSpaceMap_apply
    (alpha : NNReal) (L : F →L[Real] G)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    boundedHolderSpaceMap alpha L f x = L (f x) :=
  rfl

theorem norm_boundedHolderSpaceMap_le
    (alpha : NNReal) (L : F →L[Real] G) :
    ‖boundedHolderSpaceMap (X := X) alpha L‖ ≤ ‖L‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg L)
    (norm_boundedHolderSpaceMapLinearMap_le L)

end Map

end DifferentialGeometry.Analysis.Schauder
