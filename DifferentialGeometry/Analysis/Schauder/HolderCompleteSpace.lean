import DifferentialGeometry.Analysis.Schauder.HolderNormedSpace
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Topology.Instances.NNReal.Lemmas

noncomputable section

open Set
open scoped BigOperators NNReal Topology

namespace DifferentialGeometry.Analysis.Schauder

section Elliptic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private theorem exists_contDiffHolderSpace_pointwise_tsum
    {k : Nat} {alpha : NNReal}
    (f : Nat → ContDiffHolderSpace (V := V) (F := F) k alpha)
    (hf : Summable fun n ↦ ‖f n‖) :
    ∃ g : ContDiffHolderSpace (V := V) (F := F) k alpha,
      (∀ x, g x = ∑' n, f n x) ∧
      ‖g‖ ≤ ((((k + 2 : Nat) : NNReal) * ∑' n, ‖f n‖₊ : NNReal) : Real) := by
  let g : V → F := fun x ↦ ∑' n, f n x
  have hfNN : Summable fun n ↦ ‖f n‖₊ := by
    rw [← NNReal.summable_coe]
    simpa only [coe_nnnorm] using hf
  let S : NNReal := ∑' n, ‖f n‖₊
  have hcont : ∀ n, ContDiff Real k (contDiffHolderSpaceFun (f n)) := by
    intro n
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (f n).2.1.1 x (Set.mem_univ x)
  have hjetBound : ∀ (j n : Nat) (x : V), (j : ℕ∞) ≤ k →
      ‖iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x‖ ≤ ‖f n‖ := by
    intro j n x hj
    exact contDiffHolderSpace_iteratedFDeriv_norm_le (f n)
      (by exact_mod_cast hj) x
  have hgCont : ContDiff Real k g := by
    exact contDiff_tsum (v := fun _ n ↦ ‖f n‖) hcont
      (fun _ _ ↦ hf) hjetBound
  have hjetEq : ∀ (j : Nat), (j : ℕ∞) ≤ k → ∀ x,
      iteratedFDeriv Real j g x =
        ∑' n, iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x := by
    intro j hj x
    exact iteratedFDeriv_tsum_apply (v := fun _ n ↦ ‖f n‖) hcont
      (fun _ _ ↦ hf) hjetBound hj x
  have hjetNormSummable : ∀ (j : Nat), (j : ℕ∞) ≤ k → ∀ x,
      Summable fun n ↦
        ‖iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x‖ := by
    intro j hj x
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ hjetBound j n x hj) hf
  have hjetSummable : ∀ (j : Nat), (j : ℕ∞) ≤ k → ∀ x,
      Summable fun n ↦
        iteratedFDeriv Real j (contDiffHolderSpaceFun (f n)) x := by
    intro j hj x
    exact Summable.of_norm_bounded hf fun n ↦ hjetBound j n x hj
  have htermHolder : ∀ n, HolderWith ‖f n‖₊ alpha
      (Set.univ.restrict
        (iteratedFDeriv Real k (contDiffHolderSpaceFun (f n)))) := by
    intro n
    apply topSpatialJet_holderWith_restrict
    rw [eContDiffHolderGaugeOn_eq_ofReal_norm]
    simp only [ofReal_norm_eq_enorm, enorm_eq_nnnorm, le_refl]
  have hfinsetHolder : ∀ s : Finset Nat,
      HolderWith (∑ n ∈ s, ‖f n‖₊) alpha
        (fun x : (Set.univ : Set V) ↦
          ∑ n ∈ s,
            Set.univ.restrict
              (iteratedFDeriv Real k
                (contDiffHolderSpaceFun (f n))) x) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (HolderWith.zero : HolderWith 0 alpha
            (0 : {x : V // x ∈ (Set.univ : Set V)} →
              V [×k]→L[Real] F))
    | @insert n s hn ih =>
        simpa only [Finset.sum_insert hn, Pi.add_apply] using
          (htermHolder n).add ih
  have hpartialHolder : ∀ N,
      HolderWith S alpha
        (fun x : (Set.univ : Set V) ↦
          ∑ n ∈ Finset.range N,
            Set.univ.restrict
              (iteratedFDeriv Real k
                (contDiffHolderSpaceFun (f n))) x) := by
    intro N
    exact (hfinsetHolder (Finset.range N)).mono
      (hfNN.sum_le_tsum (Finset.range N) fun _ _ ↦ zero_le _)
  have htopHolderTsum : HolderWith S alpha
      (fun x : (Set.univ : Set V) ↦
        ∑' n, Set.univ.restrict
          (iteratedFDeriv Real k
            (contDiffHolderSpaceFun (f n))) x) := by
    intro x y
    exact le_of_tendsto
      ((hjetSummable k (by exact_mod_cast (le_refl k)) x).hasSum.tendsto_sum_nat.edist
        (hjetSummable k (by exact_mod_cast (le_refl k)) y).hasSum.tendsto_sum_nat)
      (Filter.Eventually.of_forall fun N ↦ hpartialHolder N x y)
  have htopHolder : HolderWith S alpha
      (Set.univ.restrict (iteratedFDeriv Real k g)) := by
    intro x y
    change edist (iteratedFDeriv Real k g x)
      (iteratedFDeriv Real k g y) ≤ _
    rw [hjetEq k (by exact_mod_cast (le_refl k)) x,
      hjetEq k (by exact_mod_cast (le_refl k)) y]
    exact htopHolderTsum x y
  have hspatial : ∀ j ≤ k, ∀ x ∈ (Set.univ : Set V),
      ‖iteratedFDeriv Real j g x‖ ≤ S := by
    intro j hj x _hx
    rw [hjetEq j (by exact_mod_cast hj) x]
    calc
      ‖∑' n, iteratedFDeriv Real j
          (contDiffHolderSpaceFun (f n)) x‖ ≤
          ∑' n, ‖iteratedFDeriv Real j
            (contDiffHolderSpaceFun (f n)) x‖ :=
        norm_tsum_le_tsum_norm (hjetNormSummable j (by exact_mod_cast hj) x)
      _ ≤ ∑' n, ‖f n‖ :=
        (hjetNormSummable j (by exact_mod_cast hj) x).tsum_le_tsum
          (fun n ↦ hjetBound j n x (by exact_mod_cast hj)) hf
      _ = S := by
        dsimp only [S]
        rw [NNReal.coe_tsum]
        simp only [coe_nnnorm]
  have hgauge : eContDiffHolderGaugeOn k alpha Set.univ g ≤
      (∑ _j ∈ Finset.range (k + 1), (S : ENNReal)) + S :=
    eContDiffHolderGaugeOn_le (fun _ ↦ S) S hspatial htopHolder
  have hfinite : eContDiffHolderGaugeOn k alpha Set.univ g ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.coe_ne_top,
        ENNReal.coe_ne_top⟩) hgauge
  let G : ContDiffHolderSpace (V := V) (F := F) k alpha :=
    ⟨g, ⟨⟨fun x _ ↦ hgCont.contDiffAt, htopHolder.memHolder⟩, hfinite⟩⟩
  have hgauge' : eContDiffHolderGaugeOn k alpha Set.univ g ≤
      (((k + 2 : Nat) : NNReal) * S : NNReal) := by
    calc
      eContDiffHolderGaugeOn k alpha Set.univ g ≤
          (∑ _j ∈ Finset.range (k + 1), (S : ENNReal)) + S := hgauge
      _ = (((k + 2 : Nat) : NNReal) * S : NNReal) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  refine ⟨G, fun x ↦ rfl, ?_⟩
  rw [norm_contDiffHolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (show ((((k + 2 : Nat) : NNReal) * S : NNReal) : ENNReal) ≠ ⊤ from
      ENNReal.coe_ne_top) hgauge'
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    Nat.cast_ofNat, G, g, S] using hreal

instance (k : Nat) (alpha : NNReal) :
    CompleteSpace (ContDiffHolderSpace (V := V) (F := F) k alpha) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro f hf
  obtain ⟨g, hg, _hgnorm⟩ :=
    exists_contDiffHolderSpace_pointwise_tsum f hf
  refine ⟨g, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hfPoint : ∀ x, Summable fun n ↦ f n x := by
    intro x
    exact Summable.of_norm_bounded hf fun n ↦
      norm_contDiffHolderSpace_apply_le (f n) x
  have htailBound : ∀ N,
      ‖(∑ n ∈ Finset.range N, f n) - g‖ ≤
        ((((k + 2 : Nat) : NNReal) *
          ∑' m, ‖f (m + N)‖₊ : NNReal) : Real) := by
    intro N
    have htailSummable : Summable fun m ↦ ‖f (m + N)‖ :=
      (summable_nat_add_iff N).mpr hf
    obtain ⟨tail, htail, htailNorm⟩ :=
      exists_contDiffHolderSpace_pointwise_tsum
        (fun m ↦ f (m + N)) htailSummable
    have hdiff : (∑ n ∈ Finset.range N, f n) - g = -tail := by
      apply contDiffHolderSpace_ext
      intro x
      rw [contDiffHolderSpace_sub_apply, contDiffHolderSpace_neg_apply,
        contDiffHolderSpace_sum_apply]
      rw [hg x, htail x]
      have hsum := (hfPoint x).sum_add_tsum_nat_add N
      rw [← hsum]
      abel
    rw [hdiff, norm_neg]
    exact htailNorm
  have htailZero : Filter.Tendsto
      (fun N ↦ ((((k + 2 : Nat) : NNReal) *
        ∑' m, ‖f (m + N)‖₊ : NNReal) : Real))
      Filter.atTop (nhds 0) := by
    have hNN :=
      (NNReal.tendsto_sum_nat_add (fun n ↦ ‖f n‖₊)).const_mul
        ((k + 2 : Nat) : NNReal)
    have hNN' : Filter.Tendsto
        (fun N ↦ ((k + 2 : Nat) : NNReal) *
          ∑' m, ‖f (m + N)‖₊)
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hNN
    have hR : Filter.Tendsto
        (fun N ↦ ((((k + 2 : Nat) : NNReal) *
          ∑' m, ‖f (m + N)‖₊ : NNReal) : Real))
        Filter.atTop (nhds (((0 : NNReal) : Real))) :=
      NNReal.tendsto_coe.mpr hNN'
    simpa only [NNReal.coe_zero] using hR
  exact squeeze_zero (fun _ ↦ norm_nonneg _) htailBound htailZero

end Elliptic

end DifferentialGeometry.Analysis.Schauder
