import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.LimitMetrics
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.BallCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
/-- The transition map of the tail-ball direct system is the corresponding
composite of the underlying partial diffeomorphisms. -/
theorem tailSystem_apply
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n k : ℕ) (x : tailBallOpen b j₀ n) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    cast (congrArg M (Nat.add_assoc j₀ n k).symm)
        ((S.toSeqSystem.F (Nat.le_add_right n k) x : tailBallOpen b j₀ (n + k)) :
          M (j₀ + (n + k))) =
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k :
        M (j₀ + n) → M ((j₀ + n) + k)) x := by
  letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  dsimp only
  induction k with
  | zero =>
      simpa only [Nat.add_zero] using
        congrArg Subtype.val (S.toSeqSystem.map_self n x)
  | succ k ih =>
      let hnk : n ≤ n + k := Nat.le_add_right n k
      let hstep : n + k ≤ n + (k + 1) := by omega
      have hmap :
          S.toSeqSystem.F (Nat.le_add_right n (k + 1)) x =
            S.toSeqSystem.F hstep (S.toSeqSystem.F hnk x) := by
        rw [← S.toSeqSystem.map_map hnk hstep x]
      rw [hmap]
      let hU := fun m => tailBall_source (I := I) b Ψ g j₀ m (D₀ m)
      let hmaps : ∀ m,
          (chainComp (I := I) (Mf := M) Ψ (j₀ + m) 1 :
            M (j₀ + m) → M (j₀ + (m + 1))) ''
              (tailBallOpen b j₀ m : Set (M (j₀ + m))) ⊆
            (tailBallOpen b j₀ (m + 1) : Set (M (j₀ + (m + 1)))) := fun m => by
        simpa only [tailBallOpen, Nat.add_assoc] using
          tailBall_image (I := I) b Ψ hbase g hnorm j₀ m (D₀ m 1)
      have hF (y : tailBallOpen b j₀ (n + k)) :
          S.toSeqSystem.F hstep y =
            PartialDiffeomorph.opensMap
              (chainComp (I := I) (Mf := M) Ψ (j₀ + (n + k)) 1)
              (hU (n + k) 1) (hmaps (n + k)) y := by
        calc
          S.toSeqSystem.F hstep y =
              S.toSeqSystem.F (Nat.le_succ (n + k)) y :=
            S.toSeqSystem.F_apply_irrel _ _ _
          _ = _ := by
            unfold S tailBallSystem chainBallSystem
            rw [SmoothSeqSystem.ofSucc_F_succ]
      rw [hF]
      change cast (congrArg M (Nat.add_assoc j₀ n (k + 1)).symm)
          ((chainComp (I := I) (Mf := M) Ψ (j₀ + (n + k)) 1 :
            M (j₀ + (n + k)) → M (j₀ + (n + k) + 1))
              (S.toSeqSystem.F hnk x : M (j₀ + (n + k)))) = _
      rw [chainComp_apply_succ, chainComp_apply_succ]
      change cast (congrArg M (Nat.add_assoc j₀ n (k + 1)).symm)
          ((Ψ (j₀ + (n + k)) :
            M (j₀ + (n + k)) → M (j₀ + (n + k) + 1))
              (S.toSeqSystem.F hnk x : M (j₀ + (n + k)))) = _
      rw [← ih]
      have cast_app : ∀ {a c : ℕ} (h : a = c) (y : M c),
          cast (congrArg M (congrArg Nat.succ h).symm)
              ((Ψ c : M c → M (c + 1)) y) =
            (Ψ a : M a → M (a + 1)) (cast (congrArg M h).symm y) := by
        intro a c h y
        cases h
        rfl
      exact cast_app (Nat.add_assoc j₀ n k)
        (S.toSeqSystem.F hnk x : M (j₀ + (n + k)))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
/-- Pulling an earlier tail-ball point back through a later direct-limit chart
recovers the corresponding ambient chain composite. -/
theorem tailInvIncl_apply
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n k : ℕ) (x : tailBallOpen b j₀ n) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    cast (congrArg M (Nat.add_assoc j₀ n k).symm)
        ((Function.invFun (S.toSeqSystem.incl (n + k))
            (S.toSeqSystem.incl n x) : tailBallOpen b j₀ (n + k)) :
          M (j₀ + (n + k))) =
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k :
        M (j₀ + n) → M ((j₀ + n) + k)) x := by
  letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  have hinv := S.invIncl_incl_le (Nat.le_add_right n k) x
  have hval := congrArg Subtype.val hinv
  calc
    cast (congrArg M (Nat.add_assoc j₀ n k).symm)
        ((Function.invFun (S.toSeqSystem.incl (n + k))
            (S.toSeqSystem.incl n x) : tailBallOpen b j₀ (n + k)) :
          M (j₀ + (n + k))) =
      cast (congrArg M (Nat.add_assoc j₀ n k).symm)
        ((S.toSeqSystem.F (Nat.le_add_right n k) x : tailBallOpen b j₀ (n + k)) :
          M (j₀ + (n + k))) := congrArg _ hval
    _ = _ := tailSystem_apply (I := I) b Ψ hbase g hnorm j₀ D₀ n k x

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
/-- A fixed compact core in the tail direct limit eventually maps onto every
prescribed ambient ball about the tail basepoint. -/
theorem tailBall_capture
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    ∀ (A : ℝ), 0 < A →
      letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
      let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
      ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧
        ∀ᶠ m : ℕ in Filter.atTop,
          let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim (M (j₀ + m))
              (∞ : WithTop ℕ∞) :=
            PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
          K ⊆ Φ.source ∧ Metric.ball (b (j₀ + m)) A ⊆ (Φ : _ → _) '' K := by
  intro A hA
  letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  have hevPow : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (Real.sqrt (1 + (1 / 2 : ℝ)) * A + 1) < (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually
      (Filter.eventually_gt_atTop (2 * (Real.sqrt (1 + (1 / 2 : ℝ)) * A + 1)))
  obtain ⟨n, hn⟩ := hevPow.exists
  have hmargin : Real.sqrt (1 + (1 / 2 : ℝ)) * A + 1 < coreRadius n := by
    dsimp only [coreRadius]
    nlinarith
  refine ⟨limitCore b j₀ S n, ?_, ?_⟩
  · exact (tailCore_compact b j₀ n).image (S.toSeqSystem.continuous_incl n)
  · filter_upwards [Filter.eventually_ge_atTop n] with m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    dsimp only
    constructor
    · change limitCore b j₀ S n ⊆ Set.range (S.toSeqSystem.incl (n + k))
      rintro q ⟨x, hx, rfl⟩
      exact ⟨S.toSeqSystem.F (Nat.le_add_right n k) x,
        S.toSeqSystem.incl_comp (Nat.le_add_right n k) x⟩
    · have hRle : coreRadius n ≤ (2 : ℝ) ^ (j₀ + n) := by
        rw [pow_add]
        have hn0 : 0 ≤ (2 : ℝ) ^ n := by positivity
        have hj1 : 1 ≤ (2 : ℝ) ^ j₀ := one_le_pow₀ (by norm_num)
        dsimp only [coreRadius]
        nlinarith
      let Dcore := (D₀ n k).mono
        (Metric.closedBall_subset_closedBall hRle) (le_refl (1 / 2 : ℝ)) (by norm_num)
      have hball := ball_subset_image (I := I)
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
        (hnorm (j₀ + n)) (hnorm ((j₀ + n) + k)) hA
        (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) hmargin Dcore
      have hball' : Metric.ball (b ((j₀ + n) + k)) A ⊆
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k :
            M (j₀ + n) → M ((j₀ + n) + k)) ''
              Metric.closedBall (b (j₀ + n)) (coreRadius n) := by
        change Metric.ball
            ((chainComp (I := I) (Mf := M) Ψ (j₀ + n) k) (b (j₀ + n))) A ⊆ _
          at hball
        rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) k] at hball
        exact hball
      intro y hy
      let e : M (j₀ + (n + k)) = M ((j₀ + n) + k) :=
        congrArg M (Nat.add_assoc j₀ n k).symm
      let y' : M ((j₀ + n) + k) := cast e y
      have hyball : y' ∈ Metric.ball (b ((j₀ + n) + k)) A := by
        have cast_ball : ∀ {a c : ℕ} (h : a = c) {z : M a},
            z ∈ Metric.ball (b a) A →
              cast (congrArg M h) z ∈ Metric.ball (b c) A := by
          intro a c h z hz
          cases h
          exact hz
        exact cast_ball (Nat.add_assoc j₀ n k).symm hy
      obtain ⟨z, hz, hzy⟩ := hball' hyball
      let x : tailBallOpen b j₀ n := ⟨z, core_subset_tail b j₀ n hz⟩
      have hx : x ∈ tailCore b j₀ n := by
        simpa only [x, tailCore, Set.mem_setOf_eq, Metric.mem_closedBall, dist_comm] using hz
      refine ⟨S.toSeqSystem.incl n x, ⟨x, hx, rfl⟩, ?_⟩
      have hmember := tailInvIncl_apply (I := I) b Ψ hbase g hnorm j₀ D₀ n k x
      have hcast : cast e
          ((PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl :
            S.toSeqSystem.Lim → M (j₀ + (n + k))) (S.toSeqSystem.incl n x)) =
          cast e y := by
        calc
          cast e
              ((PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (n + k)) rfl :
                S.toSeqSystem.Lim → M (j₀ + (n + k))) (S.toSeqSystem.incl n x)) =
              (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k :
                M (j₀ + n) → M ((j₀ + n) + k)) x := by
            simpa only [e] using hmember
          _ = y' := hzy
          _ = cast e y := rfl
      exact (Equiv.cast e).injective hcast

end HCGCompactness
end DifferentialGeometry
