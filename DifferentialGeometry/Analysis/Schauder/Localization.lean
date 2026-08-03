import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X V F : Type*} [MetricSpace X]
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [MetricSpace X] [NormedSpace Real F]
    [NormedAddCommGroup V] [NormedSpace Real V] in
theorem eSupNormOn_mono {s t : Set X} (hst : s ⊆ t) (f : X → F) :
    eSupNormOn s f ≤ eSupNormOn t f := by
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x, hst x.2⟩ le_rfl

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem eHolderSeminormOn_mono {s t : Set X} (hst : s ⊆ t)
    (alpha : NNReal) (f : X → F) :
    eHolderSeminormOn alpha s f ≤ eHolderSeminormOn alpha t f := by
  unfold eHolderSeminormOn eHolderNorm
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  exact HolderWith.eHolderNorm_le
    ((HolderWith.restrict_iff.mp hC).mono hst).holderWith

theorem eContDiffHolderGaugeOn_mono {s t : Set V} (hst : s ⊆ t)
    (k : Nat) (alpha : NNReal) (f : V → F) :
    eContDiffHolderGaugeOn k alpha s f ≤
      eContDiffHolderGaugeOn k alpha t f := by
  unfold eContDiffHolderGaugeOn
  gcongr with j
  · exact eSupNormOn_mono hst _
  · exact eHolderSeminormOn_mono hst alpha _

omit [MetricSpace X] [NormedSpace Real F]
    [NormedAddCommGroup V] [NormedSpace Real V] in
theorem eSupNormOn_congr {s : Set X} {f g : X → F}
    (hfg : Set.EqOn f g s) :
    eSupNormOn s f = eSupNormOn s g := by
  unfold eSupNormOn
  congr 1
  funext x
  rw [hfg x.2]

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem eHolderSeminormOn_congr {s : Set X} {f g : X → F}
    (hfg : Set.EqOn f g s) (alpha : NNReal) :
    eHolderSeminormOn alpha s f = eHolderSeminormOn alpha s g := by
  unfold eHolderSeminormOn
  congr 1
  funext x
  exact hfg x.2

theorem eContDiffHolderGaugeOn_congr {s : Set V} {f g : V → F}
    {k : Nat} (hfg : ∀ j ≤ k,
      Set.EqOn (iteratedFDeriv Real j f) (iteratedFDeriv Real j g) s)
    (alpha : NNReal) :
    eContDiffHolderGaugeOn k alpha s f =
      eContDiffHolderGaugeOn k alpha s g := by
  unfold eContDiffHolderGaugeOn
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact eSupNormOn_congr
      (hfg j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  · exact eHolderSeminormOn_congr (hfg k le_rfl) alpha

theorem eContDiffHolderGaugeOn_congr_of_eqOn_open
    {s U : Set V} (hU : IsOpen U) (hsU : s ⊆ U)
    {f g : V → F} (hfg : Set.EqOn f g U)
    (k : Nat) (alpha : NNReal) :
    eContDiffHolderGaugeOn k alpha s f =
      eContDiffHolderGaugeOn k alpha s g := by
  apply eContDiffHolderGaugeOn_congr
  intro j hj x hx
  have heq : f =ᶠ[nhds x] g :=
    Filter.mem_of_superset (hU.mem_nhds (hsU hx)) hfg
  exact (Filter.EventuallyEq.iteratedFDeriv Real heq j).eq_of_nhds

theorem holderWith_smul_of_norm_le
    {alpha C D M N : NNReal} {f : X → Real} {g : X → F}
    (hf : HolderWith C alpha f) (hg : HolderWith D alpha g)
    (hfnorm : ∀ x, ‖f x‖ ≤ M) (hgnorm : ∀ x, ‖g x‖ ≤ N) :
    HolderWith (M * D + N * C) alpha (f • g) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hreal : dist (f x • g x) (f y • g y) ≤
      ((M * D + N * C : NNReal) : Real) *
        dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm]
    calc
      ‖f x • g x - f y • g y‖ =
          ‖f x • (g x - g y) + (f x - f y) • g y‖ := by
        congr 1
        module
      _ ≤ ‖f x • (g x - g y)‖ +
          ‖(f x - f y) • g y‖ := norm_add_le _ _
      _ ≤ (M : Real) * ((D : Real) * dist x y ^ (alpha : Real)) +
          ((C : Real) * dist x y ^ (alpha : Real)) * (N : Real) := by
        rw [norm_smul, norm_smul]
        gcongr
        · simpa only [Real.norm_eq_abs] using hfnorm x
        · simpa only [dist_eq_norm] using hg.dist_le x y
        · simpa only [Real.dist_eq] using hf.dist_le x y
        · exact hgnorm y
      _ = ((M * D + N * C : NNReal) : Real) *
          dist x y ^ (alpha : Real) := by
        push_cast
        ring
  calc
    ENNReal.ofReal (dist (f x • g x) (f y • g y)) ≤
        ENNReal.ofReal (((M * D + N * C : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = ((M * D + N * C : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ ((M * D + N * C : NNReal) : Real))]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = ((M * D + N * C : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

theorem eHolderSeminormOn_smul_le
    {s : Set X} {alpha C D M N : NNReal}
    {f : X → Real} {g : X → F}
    (hf : HolderWith C alpha (s.restrict f))
    (hg : HolderWith D alpha (s.restrict g))
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ N) :
    eHolderSeminormOn alpha s (f • g) ≤ M * D + N * C := by
  apply HolderWith.eHolderNorm_le
  have hproduct := holderWith_smul_of_norm_le hf hg
    (fun x ↦ hfnorm x x.2) (fun x ↦ hgnorm x x.2)
  simpa only [Pi.smul_apply] using hproduct

end DifferentialGeometry.Analysis.Schauder

end
