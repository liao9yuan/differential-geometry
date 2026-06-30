import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

private lemma chainGrid_step_le (n : ℝ) (hn : 0 ≤ n) (j : ℕ) (cΦ cW : ℕ → ℝ)
    (hcΦ : ∀ i, 0 ≤ cΦ i) (hcW : ∀ l, 0 ≤ cW l) :
    (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
        n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) ≤
      (n + 1) * ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
  classical
  set D : ℝ := ∑ i ∈ Finset.range (j + 1 + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l
    with hD_def
  have hcell_nn : ∀ i, 0 ≤ cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
    intro i; exact mul_nonneg (hcΦ i) (Finset.sum_nonneg (fun l _ => hcW l))
  have hWshift : ∀ m : ℕ, (∑ l ∈ Finset.range m, cW (l + 1)) ≤ ∑ l ∈ Finset.range (m + 1), cW l := by
    intro m
    rw [Finset.sum_range_succ' (fun l => cW l) m]
    exact le_add_of_nonneg_right (hcW 0)
  have hA : (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ' (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn 0))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hcΦ (i + 1))
    rw [show j + 1 + 1 - (i + 1) = j + 1 - i from by omega]
  have hB : (∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn (j + 1)))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left ?_ (hcΦ i)
    refine le_trans (hWshift (j + 1 - i)) (le_of_eq ?_)
    rw [show j + 1 - i + 1 = j + 1 + 1 - i from by omega]
  calc (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
          n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
      ≤ D + n * D := by
        refine add_le_add hA ?_
        exact mul_le_mul_of_nonneg_left hB hn
    _ = (n + 1) * D := by ring

set_option maxHeartbeats 6400000 in
private theorem rfns_iteratedCovGrad_appCcRS_chainBase_le (g : SmoothRiemannianMetric I M) :
    ∀ (j p a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g p a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g p (b + j) x
          ((iteratedCovGrad (I := I) g p b j
            (appCcRS (I := I) (M := M) g p a b Φ W)).toSection x) ≤
        appCcGdiag (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
                ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
                  ((iteratedCovGrad (I := I) g p a l W).toSection x) := by
  intro j
  induction j with
  | zero =>
      intro p a b Φ W x
      rw [iteratedCovGrad_zero, appCcGdiag, pow_zero, one_mul]
      rw [Finset.sum_range_one, Finset.sum_range_one, iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [appCcRS_toSection (I := I) (M := M) g p a b Φ W x]
      have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p a b x
        (show TensorRSSpace a b I x from Φ.toSection x)
        (show TensorRSSpace p a I x from W.toSection x)
      simpa using h
  | succ j ih =>
      intro p a b Φ W x
      classical
      rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p b j
        (appCcRS (I := I) (M := M) g p a b Φ W) x]
      rw [covGrad_appCcRS_eq (I := I) (M := M) g p a b Φ W]
      rw [iteratedCovGrad_add]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g p ((b + 1) + j) x
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (appCcRS (I := I) (M := M) g p a (b + 1)
            (covGrad (I := I) (M := M) g a b Φ) W)).toSection x)
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (appCcRS (I := I) (M := M) g p (a + 1) (b + 1)
            (slotExtend (I := I) (M := M) g a b Φ)
            (covGrad (I := I) (M := M) g p a W))).toSection x)) ?_
      set cΦ : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i Φ).toSection x) with hcΦ_def
      set cW : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
        ((iteratedCovGrad (I := I) g p a l W).toSection x) with hcW_def
      have hcΦ_nn : ∀ i, 0 ≤ cΦ i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (b + i) x _
      have hcW_nn : ∀ l, 0 ≤ cW l := fun l =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + l) x _
      have hGj_nn : (0 : ℝ) ≤ appCcGdiag (E := E) j := appCcGdiag_nonneg (E := E) j
      have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have hArmA : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (appCcRS (I := I) (M := M) g p a (b + 1)
                (covGrad (I := I) (M := M) g a b Φ) W)).toSection x) ≤
          appCcGdiag (E := E) j *
            ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l := by
        refine le_trans (ih p a (b + 1) (covGrad (I := I) (M := M) g a b Φ) W x) ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hGj_nn
        rw [hcΦ_def]
        dsimp only
        rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g a b i Φ x]
      have hArmB : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (appCcRS (I := I) (M := M) g p (a + 1) (b + 1)
                (slotExtend (I := I) (M := M) g a b Φ)
                (covGrad (I := I) (M := M) g p a W))).toSection x) ≤
          appCcGdiag (E := E) j *
            ((Module.finrank ℝ E : ℝ) *
              ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
        refine le_trans (ih p (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b Φ)
          (covGrad (I := I) (M := M) g p a W) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ hGj_nn
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hWinner : (∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g p ((a + 1) + l) x
                ((iteratedCovGrad (I := I) g p (a + 1) l
                  (covGrad (I := I) (M := M) g p a W)).toSection x)) =
            ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcW_def]
          dsimp only
          rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p a l W x]
        rw [hWinner]
        have hΦle : riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
              ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                (slotExtend (I := I) (M := M) g a b Φ)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) * cΦ i := by
          rw [hcΦ_def]
          dsimp only
          exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g a b Φ i x
        calc riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
                ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                  (slotExtend (I := I) (M := M) g a b Φ)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
            ≤ ((Module.finrank ℝ E : ℝ) * cΦ i) * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) :=
                mul_le_mul_of_nonneg_right hΦle
                  (Finset.sum_nonneg (fun l _ => hcW_nn (l + 1)))
          _ = (Module.finrank ℝ E : ℝ) * (cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
                ring
      refine le_trans (add_le_add
        (mul_le_mul_of_nonneg_left hArmA (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hArmB (by norm_num : (0:ℝ) ≤ 2))) ?_
      set Gj : ℝ := appCcGdiag (E := E) j with hGj_def
      set SA : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l
        with hSA_def
      set SB : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
        with hSB_def
      set DG : ℝ := ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l with hDG_def
      have hstep : SA + (Module.finrank ℝ E : ℝ) * SB ≤ ((Module.finrank ℝ E : ℝ) + 1) * DG := by
        rw [hSA_def, hSB_def, hDG_def]
        exact chainGrid_step_le (Module.finrank ℝ E : ℝ) hn_nn j cΦ cW hcΦ_nn hcW_nn
      have hGdiag_succ : appCcGdiag (E := E) (j + 1) = (2 * ((Module.finrank ℝ E : ℝ) + 1)) * Gj := by
        rw [hGj_def, appCcGdiag, appCcGdiag, pow_succ]; ring
      rw [hGdiag_succ]
      have hGj_nn' : (0 : ℝ) ≤ Gj := hGj_nn
      nlinarith [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * Gj), hGj_nn',
        hstep]

def compEndoChain (g : SmoothRiemannianMetric I M) (a : ℕ) :
    (n : ℕ) → (Fin (n + 1) → SmoothCcTensor g a a) → SmoothCcTensor g a a
  | 0, c => c 0
  | n + 1, c => appCcRS (I := I) (M := M) g a a a (c 0) (compEndoChain g a n (fun m => c m.succ))

private lemma antidiagonalTuple_cons_prod_sum (N k' : ℕ) (f : Fin (N + 1) → ℕ → ℝ) :
    ∑ e ∈ Finset.Nat.antidiagonalTuple (N + 1) k', ∏ m : Fin (N + 1), f m (e m)
      = ∑ p ∈ Finset.antidiagonal k',
          ∑ e' ∈ Finset.Nat.antidiagonalTuple N p.2,
            f 0 p.1 * ∏ m : Fin N, f m.succ (e' m) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun e => (⟨(e 0, ∑ j : Fin N, Fin.tail e j), Fin.tail e⟩ :
      Σ _p : ℕ × ℕ, Fin N → ℕ))
    (j := fun x => Fin.cons x.1.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_sigma]
    rw [Finset.Nat.mem_antidiagonalTuple] at he
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_antidiagonal, ← he, Fin.sum_univ_succ]
      rfl
    · rw [Finset.Nat.mem_antidiagonalTuple]
  · intro x hx
    obtain ⟨p, e'⟩ := x
    rw [Finset.mem_sigma] at hx
    obtain ⟨hp, he'⟩ := hx
    rw [Finset.mem_antidiagonal] at hp
    rw [Finset.Nat.mem_antidiagonalTuple] at he' ⊢
    dsimp only
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [he', hp]
  · intro e he
    exact Fin.cons_self_tail e
  · intro x hx
    obtain ⟨p, e'⟩ := x
    obtain ⟨p1, p2⟩ := p
    rw [Finset.mem_sigma] at hx
    obtain ⟨hp, he'⟩ := hx
    rw [Finset.mem_antidiagonal] at hp
    rw [Finset.Nat.mem_antidiagonalTuple] at he'
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [he']
  · intro e he
    rw [Fin.prod_univ_succ]
    rfl

private lemma triangle_antidiagonal_reindex (k : ℕ) (φ : ℕ → ℕ → ℝ) :
    ∑ k' ∈ Finset.range (k + 1), ∑ p ∈ Finset.antidiagonal k', φ p.1 p.2
      = ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i), φ i l := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x => (⟨x.2.1, x.2.2⟩ : Σ _i : ℕ, ℕ))
    (j := fun y => (⟨y.1 + y.2, (y.1, y.2)⟩ : Σ _k' : ℕ, ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k', a, b⟩ hx
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx
    dsimp only at hx
    show (⟨a, b⟩ : Σ _i : ℕ, ℕ) ∈ (Finset.range (k + 1)).sigma (fun i => Finset.range (k + 1 - i))
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
    dsimp only
    omega
  · rintro ⟨i, l⟩ hy
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hy
    dsimp only at hy
    show (⟨i + l, (i, l)⟩ : Σ _k' : ℕ, ℕ × ℕ) ∈
      (Finset.range (k + 1)).sigma (fun k' => Finset.antidiagonal k')
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
    dsimp only
    omega
  · rintro ⟨k', a, b⟩ hx
    rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx
    dsimp only at hx
    show (⟨a + b, (a, b)⟩ : Σ _k' : ℕ, ℕ × ℕ) = ⟨k', (a, b)⟩
    rw [hx.2]
  · rintro ⟨i, l⟩ hy
    rfl
  · rintro ⟨k', a, b⟩ hx
    rfl

private lemma nested_triangle_mul_le (k i : ℕ) (H : ℕ → ℝ) (hH : ∀ l, 0 ≤ H l) :
    ∑ l ∈ Finset.range (k + 1 - i), ∑ l' ∈ Finset.range (l + 1), H l'
      ≤ (k + 1 : ℝ) * ∑ l' ∈ Finset.range (k + 1 - i), H l' := by
  have hstep : ∀ l ∈ Finset.range (k + 1 - i),
      ∑ l' ∈ Finset.range (l + 1), H l' ≤ ∑ l' ∈ Finset.range (k + 1 - i), H l' := by
    intro l hl
    rw [Finset.mem_range] at hl
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr ?_) (fun l' _ _ => hH l')
    rw [Finset.mem_range] at hx
    omega
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun l' _ => hH l'))
  have h1 : (k + 1 - i : ℕ) ≤ k + 1 := by omega
  exact_mod_cast h1

set_option maxHeartbeats 6400000 in
theorem exists_rfns_iteratedCovGrad_compEndoChain_triangleGrid_le
    (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∀ n : ℕ, ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (c : Fin (n + 1) → SmoothCcTensor g a a) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g a (a + k) x
            ((iteratedCovGrad (I := I) g a a k
              (compEndoChain (I := I) (M := M) g a n c)).toSection x) ≤
          C k * ∑ k' ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple (n + 1) k',
              ∏ m : Fin (n + 1),
                riemannianFiberNormSq (I := I) (M := M) g a (a + e m) x
                  ((iteratedCovGrad (I := I) g a a (e m) (c m)).toSection x) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun _ => 1, fun _ => zero_le_one, fun c k x => ?_⟩
      rw [one_mul]
      have hRHS : (∑ k' ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple 1 k',
              ∏ m : Fin 1,
                riemannianFiberNormSq (I := I) (M := M) g a (a + e m) x
                  ((iteratedCovGrad (I := I) g a a (e m) (c m)).toSection x))
          = ∑ k' ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g a (a + k') x
                ((iteratedCovGrad (I := I) g a a k' (c 0)).toSection x) := by
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, Fin.prod_univ_one]
        rfl
      rw [hRHS]
      show riemannianFiberNormSq (I := I) (M := M) g a (a + k) x
          ((iteratedCovGrad (I := I) g a a k (c 0)).toSection x) ≤ _
      refine Finset.single_le_sum
        (f := fun k' => riemannianFiberNormSq (I := I) (M := M) g a (a + k') x
          ((iteratedCovGrad (I := I) g a a k' (c 0)).toSection x))
        (fun k' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g a (a + k') x _)
        (Finset.mem_range.mpr (by omega))
  | succ n ih =>
      obtain ⟨Cn, hCn_nn, hCn⟩ := ih
      refine ⟨fun k => appCcGdiag (E := E) k *
          ((k + 1 : ℝ) * ∑ j ∈ Finset.range (k + 1), Cn j),
        fun k => mul_nonneg (appCcGdiag_nonneg (E := E) k)
          (mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hCn_nn j))), ?_⟩
      intro c k x
      classical
      set F0 : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (a + i) x
        ((iteratedCovGrad (I := I) g a a i (c 0)).toSection x) with hF0
      set Hs : ℕ → ℝ := fun l' => ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) l',
        ∏ m : Fin (n + 1), riemannianFiberNormSq (I := I) (M := M) g a (a + e' m) x
          ((iteratedCovGrad (I := I) g a a (e' m) (c m.succ)).toSection x) with hHs
      have hF0_nn : ∀ i, 0 ≤ F0 i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (a + i) x _
      have hHs_nn : ∀ l', 0 ≤ Hs l' := fun l' => Finset.sum_nonneg (fun e' _ =>
        Finset.prod_nonneg (fun m _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g a (a + e' m) x _))
      set Csum : ℝ := ∑ j ∈ Finset.range (k + 1), Cn j with hCsum
      have hCsum_nn : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hCn_nn j)
      set REST : SmoothCcTensor g a a :=
        compEndoChain (I := I) (M := M) g a n (fun m => c m.succ) with hREST
      have hcomp : compEndoChain (I := I) (M := M) g a (n + 1) c =
          appCcRS (I := I) (M := M) g a a a (c 0) REST := rfl
      rw [hcomp]
      refine le_trans (rfns_iteratedCovGrad_appCcRS_chainBase_le (I := I) (M := M) g k a a a
        (c 0) REST x) ?_
      have hIH : ∀ l, riemannianFiberNormSq (I := I) (M := M) g a (a + l) x
            ((iteratedCovGrad (I := I) g a a l REST).toSection x) ≤
          Cn l * ∑ l' ∈ Finset.range (l + 1), Hs l' := by
        intro l
        exact hCn (fun m => c m.succ) l x
      have hGrid : (∑ k' ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple (n + 1 + 1) k',
              ∏ m : Fin (n + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g a (a + e m) x
                  ((iteratedCovGrad (I := I) g a a (e m) (c m)).toSection x))
          = ∑ i ∈ Finset.range (k + 1), F0 i * ∑ l' ∈ Finset.range (k + 1 - i), Hs l' := by
        have hinner : ∀ k', (∑ e ∈ Finset.Nat.antidiagonalTuple (n + 1 + 1) k',
              ∏ m : Fin (n + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g a (a + e m) x
                  ((iteratedCovGrad (I := I) g a a (e m) (c m)).toSection x))
            = ∑ p ∈ Finset.antidiagonal k', F0 p.1 * Hs p.2 := by
          intro k'
          rw [antidiagonalTuple_cons_prod_sum (n + 1) k'
            (fun m j => riemannianFiberNormSq (I := I) (M := M) g a (a + j) x
              ((iteratedCovGrad (I := I) g a a j (c m)).toSection x))]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [hHs, hF0]
          dsimp only
          rw [← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun k' _ => hinner k')]
        rw [triangle_antidiagonal_reindex k (fun i l => F0 i * Hs l)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
      rw [hGrid]
      have hBound : ∀ i ∈ Finset.range (k + 1),
          F0 i * ∑ l ∈ Finset.range (k + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g a (a + l) x
                ((iteratedCovGrad (I := I) g a a l REST).toSection x) ≤
          F0 i * (Csum * ((k + 1 : ℝ) * ∑ l' ∈ Finset.range (k + 1 - i), Hs l')) := by
        intro i _
        refine mul_le_mul_of_nonneg_left ?_ (hF0_nn i)
        have hstep1 : ∑ l ∈ Finset.range (k + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g a (a + l) x
                ((iteratedCovGrad (I := I) g a a l REST).toSection x) ≤
            ∑ l ∈ Finset.range (k + 1 - i), Csum * ∑ l' ∈ Finset.range (l + 1), Hs l' := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine le_trans (hIH l) ?_
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun l' _ => hHs_nn l'))
          rw [hCsum]
          refine Finset.single_le_sum (fun j _ => hCn_nn j) ?_
          rw [Finset.mem_range] at hl ⊢
          omega
        refine le_trans hstep1 ?_
        have heq : ∑ l ∈ Finset.range (k + 1 - i), Csum * ∑ l' ∈ Finset.range (l + 1), Hs l'
            = Csum * ∑ l ∈ Finset.range (k + 1 - i), ∑ l' ∈ Finset.range (l + 1), Hs l' :=
          (Finset.mul_sum (Finset.range (k + 1 - i))
            (fun l => ∑ l' ∈ Finset.range (l + 1), Hs l') Csum).symm
        rw [heq]
        exact mul_le_mul_of_nonneg_left (nested_triangle_mul_le k i Hs hHs_nn) hCsum_nn
      refine le_trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum hBound) (appCcGdiag_nonneg (E := E) k)) ?_
      have hfactor : ∑ i ∈ Finset.range (k + 1),
            F0 i * (Csum * ((k + 1 : ℝ) * ∑ l' ∈ Finset.range (k + 1 - i), Hs l'))
          = Csum * ((k + 1 : ℝ) * ∑ i ∈ Finset.range (k + 1),
              F0 i * ∑ l' ∈ Finset.range (k + 1 - i), Hs l') := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [hfactor]
      exact le_of_eq (by ring)

end Connection
end Integral
end DifferentialGeometry

end
