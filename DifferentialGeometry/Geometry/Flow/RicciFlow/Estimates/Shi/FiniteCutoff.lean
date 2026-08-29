import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Complete

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators Bundle Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

private theorem prop_of_eq {α : Sort*} {a b : α} (hab : a = b)
    (P : α → Prop) (hb : P b) : P a := by
  subst b
  exact hb

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
private theorem support_cross
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    (w : Nat → Real → M → Real) (i p : Nat)
    {T eps t : Real} {chi : Real → M → Real} {x : M}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (ht : t ∈ Set.Icc 0 T) (heps : 0 ≤ eps)
    (hwi : 0 ≤ w i t x) (hnext : 0 ≤ w (i + 1) t x)
    (hnorm :
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (w i t) x)
          (gradientFun (I := I) (G.metric t) (w i t) x) ≤
        4 * w i t x * w (i + 1) t x) :
    -2 * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t)
          (fun y : M => support.phi t y ^ (p + 1)) x)
        (gradientFun (I := I) (G.metric t) (w i t) x) ≤
      (1 / 2 : Real) * support.phi t x ^ (p + 1) * w (i + 1) t x +
        8 * (((p + 1 : Nat) : Real) ^ 2) * eps *
          support.phi t x ^ p * w i t x := by
  let a := gradientFun (I := I) (G.metric t) (support.phi t) x
  let b := gradientFun (I := I) (G.metric t) (w i t) x
  let c₀ := (G.metric t).inner x a b
  let c := (G.metric t).inner x
    (gradientFun (I := I) (G.metric t)
      (fun y : M => support.phi t y ^ (p + 1)) x) b
  let r : Real := ((p + 1 : Nat) : Real) * support.phi t x ^ p
  let q₁ : Real := (1 / 2 : Real) * support.phi t x ^ (p + 1) * w (i + 1) t x
  let q₂ : Real := 8 * (((p + 1 : Nat) : Real) ^ 2) * eps *
    support.phi t x ^ p * w i t x
  have hphi0 : 0 ≤ support.phi t x :=
    (support.lower_nhds.self_of_nhdsWithin
      (show (t, x) ∈ spacetimeSlab (M := M) T from ⟨ht, Set.mem_univ x⟩)).1
  have hsq₀ : c₀ ^ 2 ≤
      (eps * support.phi t x) * (4 * w i t x * w (i + 1) t x) := by
    calc
      c₀ ^ 2 ≤ (G.metric t).inner x a a * (G.metric t).inner x b b :=
        DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          (I := I) (M := M) (G.metric t) x a b
      _ ≤ (eps * support.phi t x) * (4 * w i t x * w (i + 1) t x) :=
        mul_le_mul support.grad_sq_le hnorm
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) (G.metric t) x b)
          (mul_nonneg heps hphi0)
  have hc : c = r * c₀ := by
    dsimp [c, r, c₀, a]
    rw [gradientFun_pow (I := I) (G.metric t) p
      support.space_diff_nhds.self_of_nhds]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsq : c ^ 2 ≤ q₁ * q₂ := by
    rw [hc]
    calc
      (r * c₀) ^ 2 = r ^ 2 * c₀ ^ 2 := by ring
      _ ≤ r ^ 2 * ((eps * support.phi t x) *
          (4 * w i t x * w (i + 1) t x)) :=
        mul_le_mul_of_nonneg_left hsq₀ (sq_nonneg r)
      _ = q₁ * q₂ := by
        dsimp [r, q₁, q₂]
        rw [pow_succ]
        ring
  have hq₁ : 0 ≤ q₁ := by
    dsimp [q₁]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hphi0 (p + 1))) hnext
  have hq₂ : 0 ≤ q₂ := by
    dsimp [q₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) heps)
      (pow_nonneg hphi0 p)) hwi
  have hhalf : q₁ * q₂ ≤ ((q₁ + q₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (q₁ - q₂)]
  have habs : |c| ≤ (q₁ + q₂) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (q₁ + q₂) / 2 := (neg_le_abs c).trans habs
  dsimp [c, q₁, q₂, b] at hneg ⊢
  linarith

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
private theorem level_data
    {D : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (w wLap : Nat → Real → M → Real) (T c eps a : Real) (i : Nat)
    {t : Real} {x : M} {chi : Real → M → Real}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (hT : 0 < T) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (ha : 0 ≤ a) (heps : 0 ≤ eps)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ s ∈ Set.Icc 0 T, 0 < s → s ∈ D.regular)
    (hheat : TowerHeatBoundOn (D := D) w wLap c i)
    (hLap : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      heatOperatorWithDrift (I := I) G s
        (fun z : M ↦ (0 : TangentSpace I z)) (w i s) y = wLap i s y)
    (hw_space : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I 𝓘(Real, Real) (w i s) y)
    (hw_grad : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric s) (w i s) z) y)
    (hwi : 0 ≤ w i t x) (hnext : 0 ≤ w (i + 1) t x)
    (hnorm :
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (w i t) x)
          (gradientFun (I := I) (G.metric t) (w i t) x) ≤
        4 * w i t x * w (i + 1) t x) :
    let term : Real → M → Real := fun s y =>
      a * (s ^ i * support.phi s y ^ (i + 1) * w i s y)
    DifferentiableWithinAt Real (fun s => term s x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (term t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (term t) y) x ∧
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) term t x ≤
        a *
          (support.phi t x ^ (i + 1) *
              ((i : Real) * t ^ (i - 1) * w i t x +
                t ^ i * (-2 * w (i + 1) t x +
                  towerReactionSum (M := M) w c i t x)) +
            (1 / 2 : Real) * t ^ i * support.phi t x ^ (i + 1) *
              w (i + 1) t x +
            cutErrCoeff i * eps * t ^ i * support.phi t x ^ i * w i t x) := by
  dsimp only
  let qpow : Real → M → Real := fun s y => support.phi s y ^ (i + 1)
  let v : Real → M → Real := fun s y => s ^ i * w i s y
  let tau : RealTimeInterval.RegularTime D :=
    ⟨t, hregular t ht htpos⟩
  obtain ⟨d, hdD, hdle⟩ := hheat tau x
  have hd : HasDerivWithinAt (fun s : Real => w i s x) d (Set.Icc 0 T) t :=
    hdD.mono hslab
  have hheat' : d - wLap i t x ≤
      -2 * w (i + 1) t x + towerReactionSum (M := M) w c i t x := by
    have hdle' : d ≤ wLap i t x +
        (-2 * w (i + 1) t x + towerReactionSum (M := M) w c i t x) := by
      simpa only [tau] using hdle
    linarith
  have hq_time : DifferentiableWithinAt Real
      (fun s : Real => qpow s x) (Set.Icc 0 T) t := by
    simpa [qpow] using support.time_diff.pow (i + 1)
  have hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 T) t :=
    (((hasDerivWithinAt_id t (Set.Icc 0 T)).pow i).mul hd).differentiableWithinAt
  have hq_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (qpow t) y := by
    filter_upwards [support.space_diff_nhds] with y hy
    simpa [qpow] using hy.pow (i + 1)
  have hv_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y := by
    intro y
    have h := (hw_space t ht htpos y).const_smul (t ^ i)
    simpa [v, smul_eq_mul] using h
  have hq_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (qpow t) z) x := by
    have hrhs := (((support.space_diff_nhds.self_of_nhds.pow i).const_smul
      (((i + 1 : Nat) : Real))).smul_section support.grad_diff)
    refine hrhs.congr_of_eventuallyEq ?_
    filter_upwards [support.space_diff_nhds] with y hy
    exact congrArg (fun b =>
      (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (gradientFun_pow (I := I) (G.metric t) i hy)
  have hv_grad : ∀ y : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (v t) z) y := by
    intro y
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t) (v t) z) =
          (t ^ i • fun z : M =>
            gradientFun (I := I) (G.metric t) (w i t) z) := by
      funext z
      rw [show v t = t ^ i • w i t by
        funext q
        simp [v, smul_eq_mul]]
      exact gradientFun_const_smul (I := I) (G.metric t) (t ^ i)
        (hw_space t ht htpos z)
    have hsection :
        (T% fun z : M => gradientFun (I := I) (G.metric t) (v t) z) =
          (T% (t ^ i • fun z : M =>
            gradientFun (I := I) (G.metric t) (w i t) z)) := by
      funext z
      simpa using congrFun hplain z
    rw [hsection]
    exact (hw_grad t ht htpos y).smul_const_section (a := t ^ i)
  have hprod_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t)
          (fun y : M => qpow t y * v t y) z) x := by
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t)
          (fun y : M => qpow t y * v t y) z) =ᶠ[𝓝 x]
        (fun z : M => qpow t z • gradientFun (I := I) (G.metric t) (v t) z +
          v t z • gradientFun (I := I) (G.metric t) (qpow t) z) := by
      filter_upwards [hq_space] with z hqz
      exact gradientFun_mul (I := I) (G.metric t) hqz (hv_space z)
    exact (mdifferentiableAt_add_section
      (hq_space.self_of_nhds.smul_section (hv_grad x))
      ((hv_space x).smul_section hq_grad)).congr_of_eventuallyEq (by
        filter_upwards [hplain] with z hz
        exact congrArg (fun b =>
          (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) hz)
  have hv_parabolic :
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) v t x =
        (i : Real) * t ^ (i - 1) * w i t x +
          t ^ i * (d - wLap i t x) := by
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
    have htime : derivWithin (fun s : Real => v s x) (Set.Icc 0 T) t =
        (i : Real) * t ^ (i - 1) * w i t x + t ^ i * d := by
      simpa [v] using
        (((hasDerivWithinAt_id t (Set.Icc 0 T)).pow i).mul hd).derivWithin huniq
    have hheatv : heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) (v t) x =
        t ^ i * wLap i t x := by
      have hscale := heatOperatorWithDrift_const_smul
        (I := I) G t (fun y : M => (0 : TangentSpace I y)) (t ^ i)
        (hw_space t ht htpos) (hw_grad t ht htpos x)
      rw [show v t = t ^ i • w i t by
        funext y
        simp [v, smul_eq_mul]]
      rw [hscale, hLap t ht htpos x]
    rw [parabolicOperatorWithDrift_eq, htime, hheatv]
    ring
  have hv_gradient : gradientAt (I := I) G t (v t) x =
      t ^ i • gradientAt (I := I) G t (w i t) x := by
    unfold gradientAt
    rw [show v t = t ^ i • w i t by
      funext y
      simp [v, smul_eq_mul]]
    exact gradientFun_const_smul (I := I) (G.metric t) (t ^ i)
      (hw_space t ht htpos x)
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hmul := parabolic_mul_nhds (I := I) T
    (fun _ y => (0 : TangentSpace I y)) qpow v t x
    hq_time hv_time hq_space (Filter.Eventually.of_forall hv_space)
    hq_grad (hv_grad x)
  have hscale := parabolic_smul_nhds (I := I) T
    (fun _ y => (0 : TangentSpace I y)) a
    (fun s y => qpow s y * v s y) t x
    (hq_time.mul hv_time)
    (by
      filter_upwards [hq_space] with y hy
      exact hy.mul (hv_space y))
    hprod_grad huniq
  have hq_bound := support_pow_para (I := I) support ht i
  have hcross := support_cross (I := I) w i i support ht heps
    hwi hnext hnorm
  have hti0 : 0 ≤ t ^ i := pow_nonneg ht.1 i
  have hq_term :
      v t x * parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) qpow t x ≤
        (((i + 1 : Nat) : Real) * eps) *
          t ^ i * support.phi t x ^ i * w i t x := by
    have hmult := mul_le_mul_of_nonneg_left hq_bound
      (mul_nonneg hti0 hwi)
    dsimp [qpow, v]
    convert hmult using 1
    ring
  have hcross_term :
      -2 * (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (v t) x) ≤
        (1 / 2 : Real) * t ^ i * support.phi t x ^ (i + 1) *
            w (i + 1) t x +
          8 * (((i + 1 : Nat) : Real) ^ 2) * eps * t ^ i *
            support.phi t x ^ i * w i t x := by
    rw [hv_gradient]
    simp only [map_smul, smul_eq_mul]
    have hmult := mul_le_mul_of_nonneg_left hcross hti0
    dsimp [qpow]
    unfold gradientAt
    convert hmult using 1 <;> ring
  have hheat_mul :
      support.phi t x ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * w i t x + t ^ i * (d - wLap i t x)) ≤
        support.phi t x ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * w i t x +
            t ^ i * (-2 * w (i + 1) t x +
              towerReactionSum (M := M) w c i t x)) := by
    apply mul_le_mul_of_nonneg_left _
      (pow_nonneg
        (support.lower_nhds.self_of_nhdsWithin
          (show (t, x) ∈ spacetimeSlab (M := M) T from
            ⟨ht, Set.mem_univ x⟩)).1 (i + 1))
    linarith [mul_le_mul_of_nonneg_left hheat' hti0]
  have hop :
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y))
          (fun s y => a * (qpow s y * v s y)) t x ≤
        a *
          (support.phi t x ^ (i + 1) *
              ((i : Real) * t ^ (i - 1) * w i t x +
                t ^ i * (-2 * w (i + 1) t x +
                  towerReactionSum (M := M) w c i t x)) +
            (1 / 2 : Real) * t ^ i * support.phi t x ^ (i + 1) *
              w (i + 1) t x +
            cutErrCoeff i * eps * t ^ i * support.phi t x ^ i * w i t x) := by
    rw [hscale, hmul, hv_parabolic]
    apply mul_le_mul_of_nonneg_left _ ha
    calc
      qpow t x *
            ((i : Real) * t ^ (i - 1) * w i t x + t ^ i * (d - wLap i t x)) +
          v t x * parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) qpow t x -
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t (qpow t) x)
            (gradientAt (I := I) G t (v t) x) ≤
        support.phi t x ^ (i + 1) *
            ((i : Real) * t ^ (i - 1) * w i t x + t ^ i * (d - wLap i t x)) +
          (((i + 1 : Nat) : Real) * eps) * t ^ i *
            support.phi t x ^ i * w i t x +
          ((1 / 2 : Real) * t ^ i * support.phi t x ^ (i + 1) *
              w (i + 1) t x +
            8 * (((i + 1 : Nat) : Real) ^ 2) * eps * t ^ i *
              support.phi t x ^ i * w i t x) := by
        dsimp [qpow, v]
        linarith
      _ ≤ support.phi t x ^ (i + 1) *
            ((i : Real) * t ^ (i - 1) * w i t x +
              t ^ i * (-2 * w (i + 1) t x +
                towerReactionSum (M := M) w c i t x)) +
          (1 / 2 : Real) * t ^ i * support.phi t x ^ (i + 1) *
            w (i + 1) t x +
          cutErrCoeff i * eps * t ^ i * support.phi t x ^ i * w i t x := by
        rw [cutErrCoeff]
        simp only [Nat.cast_add, Nat.cast_one]
        linarith [hheat_mul]
  have hterm_eq :
      (fun s y => a * (s ^ i * support.phi s y ^ (i + 1) * w i s y)) =
        (fun s y => a * (qpow s y * v s y)) := by
    funext s y
    dsimp [qpow, v]
    ring
  have htime_eq :
      (fun s => a * (s ^ i * support.phi s x ^ (i + 1) * w i s x)) =
        (fun s => a * (qpow s x * v s x)) :=
    congrArg (fun f : Real → M → Real => fun s => f s x) hterm_eq
  have hspace_eq :
      (fun y => a * (t ^ i * support.phi t y ^ (i + 1) * w i t y)) =
        (fun y => a * (qpow t y * v t y)) :=
    congrArg (fun f : Real → M → Real => f t) hterm_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htime_eq]
    exact (hq_time.mul hv_time).const_mul a
  · filter_upwards [hq_space] with y hy
    rw [hspace_eq]
    exact (hy.mul (hv_space y)).const_smul a
  · rw [hspace_eq]
    have hs := hprod_grad.smul_const_section (a := a)
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [hq_space] with y hy
    exact congrArg (fun b =>
      (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) (by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          gradientFun_const_smul (I := I) (G.metric t) a
            (hy.mul (hv_space y)))
  · rw [hterm_eq]
    exact hop

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
private theorem support_reg
    {D : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (w wLap : Nat → Real → M → Real)
    (T c alpha eps : Real)
    {t : Real} {x : M} {chi : Real → M → Real}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (hT : 0 < T) (hc : 0 ≤ c) (halpha : 0 ≤ alpha)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ s ∈ Set.Icc 0 T, 0 < s → s ∈ D.regular)
    (heps : 0 ≤ eps)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (hw_nonneg : ∀ k ≤ 2, ∀ s ∈ Set.Icc 0 T, ∀ y, 0 ≤ w k s y)
    (hheat : ∀ k ≤ 1, TowerHeatBoundOn (D := D) w wLap c k)
    (hLap : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      heatOperatorWithDrift (I := I) G s
        (fun z : M ↦ (0 : TangentSpace I z)) (w k s) y = wLap k s y)
    (hw_space : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I 𝓘(Real, Real) (w k s) y)
    (hw_grad : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric s) (w k s) z) y)
    (hnorm : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      (G.metric s).inner y
          (gradientFun (I := I) (G.metric s) (w k s) y)
          (gradientFun (I := I) (G.metric s) (w k s) y) ≤
        4 * w k s y * w (k + 1) s y) :
    let beta := towerBeta c alpha (towerConst c alpha) 1
    let F : Real → M → Real := fun s y =>
      beta * support.phi s y * w 0 s y +
        s * support.phi s y ^ 2 * w 1 s y
    DifferentiableWithinAt Real (fun s => F s x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (F t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x := by
  classical
  dsimp only
  set beta : Real := towerBeta c alpha (towerConst c alpha) 1 with hbeta
  let u0 : Real → M → Real := fun s y =>
    beta * (s ^ 0 * support.phi s y ^ (0 + 1) * w 0 s y)
  let u1 : Real → M → Real := fun s y =>
    1 * (s ^ 1 * support.phi s y ^ (1 + 1) * w 1 s y)
  let term : Nat → Real → M → Real := fun i => if i = 0 then u0 else u1
  let F : Real → M → Real := fun s y =>
    beta * support.phi s y * w 0 s y +
      s * support.phi s y ^ 2 * w 1 s y
  have hbeta0 : 0 ≤ beta := by
    simpa only [hbeta] using towerBeta_nonneg hc halpha 1
  have h0 := level_data (I := I) (D := D) G w wLap T c eps beta 0 support
    hT ht htpos hbeta0 heps hslab hregular
    (hheat 0 (by omega))
    (hLap 0 (by omega)) (hw_space 0 (by omega)) (hw_grad 0 (by omega))
    (hw_nonneg 0 (by omega) t ht x) (hw_nonneg 1 (by omega) t ht x)
    (hnorm 0 (by omega) t ht htpos x)
  have h1 := level_data (I := I) (D := D) G w wLap T c eps 1 1 support
    hT ht htpos (by norm_num) heps hslab hregular
    (hheat 1 (by omega))
    (hLap 1 (by omega)) (hw_space 1 (by omega)) (hw_grad 1 (by omega))
    (hw_nonneg 1 (by omega) t ht x) (hw_nonneg 2 (by omega) t ht x)
    (hnorm 1 (by omega) t ht htpos x)
  have hu0 : u0 = fun s y =>
      beta * (s ^ 0 * support.phi s y ^ (0 + 1) * w 0 s y) := rfl
  have hu1 : u1 = fun s y =>
      1 * (s ^ 1 * support.phi s y ^ (1 + 1) * w 1 s y) := rfl
  rw [← hu0] at h0
  rw [← hu1] at h1
  have htime : ∀ i ∈ Finset.range 2,
      DifferentiableWithinAt Real (fun s => term i s x) (Set.Icc 0 T) t := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · simpa only [term, if_pos rfl] using h0.1
    · simpa only [term, if_neg (by omega : (1 : Nat) ≠ 0)] using h1.1
  have hspace : ∀ i ∈ Finset.range 2, ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (term i t) y := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · simpa only [term, if_pos rfl] using h0.2.1
    · simpa only [term, if_neg (by omega : (1 : Nat) ≠ 0)] using h1.2.1
  have hgrad : ∀ i ∈ Finset.range 2,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (term i t) y) x := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · simpa only [term, if_pos rfl] using h0.2.2.1
    · simpa only [term, if_neg (by omega : (1 : Nat) ≠ 0)] using h1.2.2.1
  have hFsum : F = fun s y => ∑ i ∈ Finset.range 2, term i s y := by
    funext s y
    rw [show (∑ i ∈ Finset.range 2, term i s y) = term 0 s y + term 1 s y by
      norm_num [Finset.sum_range_succ]]
    (simp [F, term, u0, u1]; ring)
  have hreg := sum_reg_nhds (I := I) (G := G)
    (Finset.range 2) term T t x htime hspace hgrad
  have hFx :
      (fun s => F s x) = (fun s => ∑ i ∈ Finset.range 2, term i s x) :=
    congrArg (fun f : Real → M → Real => fun s => f s x) hFsum
  have hFt : F t = (fun y => ∑ i ∈ Finset.range 2, term i t y) :=
    congrFun hFsum t
  have hFtRaw :
      (fun y => beta * support.phi t y * w 0 t y +
        t * support.phi t y ^ 2 * w 1 t y) =
        (fun y => ∑ i ∈ Finset.range 2, term i t y) := by
    simpa only [F] using hFt
  have hgradEq :
      (T% fun y : M => gradientFun (I := I) (G.metric t)
        (fun z => beta * support.phi t z * w 0 t z +
          t * support.phi t z ^ 2 * w 1 t z) y) =
        (T% fun y : M => gradientFun (I := I) (G.metric t)
          (fun z => ∑ i ∈ Finset.range 2, term i t z) y) :=
    congrArg (fun f : M → Real =>
      (T% fun y : M => gradientFun (I := I) (G.metric t) f y)) hFtRaw
  refine ⟨?_, ?_, ?_⟩
  · have htimeF : DifferentiableWithinAt Real (fun s => F s x)
        (Set.Icc 0 T) t := hFx.symm ▸ hreg.1
    simpa only [F] using htimeF
  · have hspaceF : ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (F t) y := hFt.symm ▸ hreg.2.1
    simpa only [F] using hspaceF
  · exact prop_of_eq hgradEq
      (fun f => MDifferentiableAt I (I.prod 𝓘(Real, E)) f x) hreg.2.2

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
private theorem support_raw_bound
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (w : Nat → Real → M → Real)
    (T c K alpha eps beta barTop : Real)
    {t : Real} {x : M} {chi : Real → M → Real}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (hc : 0 ≤ c) (hK : 0 < K) (halpha : 0 ≤ alpha)
    (hTK : T ≤ alpha / K)
    (hsmall : 2 * eps * T * cutErrCoeff 1 ≤ 1)
    (heps : 0 ≤ eps)
    (ht : t ∈ Set.Icc 0 T)
    (hchi : chi t x ∈ Set.Icc (0 : Real) 1)
    (hw_nonneg : ∀ k ≤ 2, ∀ s ∈ Set.Icc 0 T, ∀ y, 0 ≤ w k s y)
    (hw0 : w 0 t x ≤ K ^ 2)
    (hbeta : beta = towerBeta c alpha (towerConst c alpha) 1)
    (hbarTop : barTop = towerBarTop c (towerConst c alpha) 1) :
    beta *
          (support.phi t x *
              (-2 * w 1 t x + towerReactionSum (M := M) w c 0 t x) +
            (1 / 2 : Real) * support.phi t x * w 1 t x +
            9 * eps * w 0 t x) +
        (support.phi t x ^ 2 *
              (w 1 t x + t * (-2 * w 2 t x +
                towerReactionSum (M := M) w c 1 t x)) +
            (1 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x +
            34 * eps * t * support.phi t x * w 1 t x) ≤
      (barTop + beta * towerFactCoeff 1 0 *
          towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
        9 * eps * beta * K ^ 2 := by
  have hbeta0 : 0 ≤ beta := by
    simpa only [hbeta] using towerBeta_nonneg hc halpha 1
  have hq0 : 0 ≤ support.phi t x :=
    (support.lower_nhds.self_of_nhdsWithin
      (show (t, x) ∈ spacetimeSlab (M := M) T from ⟨ht, Set.mem_univ x⟩)).1
  have hq1 : support.phi t x ≤ 1 := by
    simpa only [support.eq_at] using hchi.2
  have hw0n := hw_nonneg 0 (by omega) t ht x
  have hw1n := hw_nonneg 1 (by omega) t ht x
  have hw2n := hw_nonneg 2 (by omega) t ht x
  have hsqrt0 : Real.sqrt (w 0 t x) ≤ K := by
    calc
      Real.sqrt (w 0 t x) ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt hw0
      _ = K := Real.sqrt_sq (le_of_lt hK)
  have hreact0 : towerReactionSum (M := M) w c 0 t x ≤ c * K ^ 3 := by
    have hs0 : Real.sqrt (w 0 t x) * Real.sqrt (w 0 t x) = w 0 t x := by
      nlinarith [Real.sq_sqrt hw0n]
    have heq : towerReactionSum (M := M) w c 0 t x =
        c * w 0 t x * Real.sqrt (w 0 t x) := by
      calc
        towerReactionSum (M := M) w c 0 t x =
            c * Real.sqrt (w 0 t x) * Real.sqrt (w 0 t x) *
              Real.sqrt (w 0 t x) := by
          rw [towerReactionSum]
          norm_num [Finset.sum_range_succ]
        _ = c * w 0 t x * Real.sqrt (w 0 t x) := by
          have h := congrArg
            (fun z : Real => c * z * Real.sqrt (w 0 t x)) hs0
          simpa only [mul_assoc] using h
    rw [heq]
    calc
      c * w 0 t x * Real.sqrt (w 0 t x) ≤
          c * K ^ 2 * Real.sqrt (w 0 t x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw0 hc)
          (Real.sqrt_nonneg _)
      _ ≤ c * K ^ 2 * K :=
        mul_le_mul_of_nonneg_left hsqrt0
          (mul_nonneg hc (pow_nonneg (le_of_lt hK) 2))
      _ = c * K ^ 3 := by ring
  have hreact1 : towerReactionSum (M := M) w c 1 t x ≤
      2 * c * K * w 1 t x := by
    have hs1 : Real.sqrt (w 1 t x) * Real.sqrt (w 1 t x) = w 1 t x := by
      nlinarith [Real.sq_sqrt hw1n]
    have heq : towerReactionSum (M := M) w c 1 t x =
        2 * (c * Real.sqrt (w 0 t x) * w 1 t x) := by
      calc
        towerReactionSum (M := M) w c 1 t x =
            2 * (c * Real.sqrt (w 0 t x) *
              (Real.sqrt (w 1 t x) * Real.sqrt (w 1 t x))) := by
          rw [towerReactionSum]
          norm_num [Finset.sum_range_succ]
          ring
        _ = 2 * (c * Real.sqrt (w 0 t x) * w 1 t x) := by
          exact congrArg (fun z : Real =>
            2 * (c * Real.sqrt (w 0 t x) * z)) hs1
    rw [heq]
    have hterm : c * Real.sqrt (w 0 t x) * w 1 t x ≤
        c * K * w 1 t x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt0 hc) hw1n
    calc
      2 * (c * Real.sqrt (w 0 t x) * w 1 t x) ≤
          2 * (c * K * w 1 t x) :=
        mul_le_mul_of_nonneg_left hterm (by norm_num)
      _ = 2 * c * K * w 1 t x := by ring
  have htK : t * K ≤ alpha := by
    calc
      t * K ≤ (alpha / K) * K :=
        mul_le_mul_of_nonneg_right (ht.2.trans hTK) (le_of_lt hK)
      _ = alpha := div_mul_cancel₀ alpha (ne_of_gt hK)
  have herr : 34 * eps * t ≤ (1 / 2 : Real) := by
    have htprod : eps * t ≤ eps * T :=
      mul_le_mul_of_nonneg_left ht.2 heps
    calc
      34 * eps * t = 34 * (eps * t) := by ring
      _ ≤ 34 * (eps * T) :=
        mul_le_mul_of_nonneg_left htprod (by norm_num)
      _ = (1 / 2 : Real) * (2 * eps * T * cutErrCoeff 1) := by
        norm_num [cutErrCoeff]
        ring
      _ ≤ (1 / 2 : Real) * 1 :=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = (1 / 2 : Real) := by ring
  have hbeta_eq : beta = 2 * c * alpha + 1 := by
    have hbar1 : towerBarTop c (towerConst c alpha) 1 = 2 * c :=
      towerBarTop_one c (towerConst c alpha)
    rw [hbeta, towerBeta, hbar1]
    ring
  have hqreact0 : support.phi t x * towerReactionSum (M := M) w c 0 t x ≤
      c * K ^ 3 := by
    calc
      support.phi t x * towerReactionSum (M := M) w c 0 t x ≤
          support.phi t x * (c * K ^ 3) :=
        mul_le_mul_of_nonneg_left hreact0 hq0
      _ ≤ 1 * (c * K ^ 3) :=
        mul_le_mul_of_nonneg_right hq1
          (mul_nonneg hc (pow_nonneg (le_of_lt hK) 3))
      _ = c * K ^ 3 := one_mul _
  have hqpow : support.phi t x ^ 2 ≤ support.phi t x := by
    calc
      support.phi t x ^ 2 = support.phi t x * support.phi t x := by
        rw [pow_two]
      _ ≤ support.phi t x * 1 :=
        mul_le_mul_of_nonneg_left hq1 hq0
      _ = support.phi t x := mul_one _
  have hqreact1 : t * support.phi t x ^ 2 *
        towerReactionSum (M := M) w c 1 t x ≤
      2 * c * alpha * support.phi t x * w 1 t x := by
    have hleft : t * support.phi t x ^ 2 *
          towerReactionSum (M := M) w c 1 t x ≤
        t * support.phi t x ^ 2 * (2 * c * K * w 1 t x) :=
      mul_le_mul_of_nonneg_left hreact1
        (mul_nonneg ht.1 (pow_nonneg hq0 2))
    have hmid : t * support.phi t x ^ 2 * (2 * c * K * w 1 t x) ≤
        2 * c * (t * K) * support.phi t x * w 1 t x := by
      have htK0 : 0 ≤ t * K := mul_nonneg ht.1 (le_of_lt hK)
      have hnonneg : 0 ≤ 2 * c * (t * K) * w 1 t x :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) htK0) hw1n
      calc
        t * support.phi t x ^ 2 * (2 * c * K * w 1 t x) =
            (2 * c * (t * K) * w 1 t x) * support.phi t x ^ 2 := by ring
        _ ≤ (2 * c * (t * K) * w 1 t x) * support.phi t x :=
          mul_le_mul_of_nonneg_left hqpow hnonneg
        _ = 2 * c * (t * K) * support.phi t x * w 1 t x := by ring
    have hright : 2 * c * (t * K) * support.phi t x * w 1 t x ≤
        2 * c * alpha * support.phi t x * w 1 t x := by
      have h2c0 : 0 ≤ 2 * c := mul_nonneg (by norm_num) hc
      have hbase : 2 * c * (t * K) ≤ 2 * c * alpha :=
        mul_le_mul_of_nonneg_left htK h2c0
      calc
        2 * c * (t * K) * support.phi t x * w 1 t x =
            (2 * c * (t * K)) * (support.phi t x * w 1 t x) := by ring
        _ ≤ (2 * c * alpha) * (support.phi t x * w 1 t x) :=
          mul_le_mul_of_nonneg_right hbase (mul_nonneg hq0 hw1n)
        _ = 2 * c * alpha * support.phi t x * w 1 t x := by ring
    exact hleft.trans (hmid.trans hright)
  have herr0 : 9 * eps * w 0 t x ≤ 9 * eps * K ^ 2 :=
    mul_le_mul_of_nonneg_left hw0 (mul_nonneg (by norm_num) heps)
  have herr1 : 34 * eps * t * support.phi t x * w 1 t x ≤
      (1 / 2 : Real) * support.phi t x * w 1 t x := by
    calc
      34 * eps * t * support.phi t x * w 1 t x =
          (34 * eps * t) * (support.phi t x * w 1 t x) := by ring
      _ ≤ (1 / 2 : Real) * (support.phi t x * w 1 t x) :=
        mul_le_mul_of_nonneg_right herr (mul_nonneg hq0 hw1n)
      _ = (1 / 2 : Real) * support.phi t x * w 1 t x := by ring
  have htime1 : support.phi t x ^ 2 * w 1 t x ≤
      support.phi t x * w 1 t x :=
    mul_le_mul_of_nonneg_right hqpow hw1n
  have hw2drop :
      -(3 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x ≤ 0 := by
    have hprod0 : 0 ≤ t * support.phi t x ^ 2 * w 2 t x :=
      mul_nonneg (mul_nonneg ht.1 (pow_nonneg hq0 2)) hw2n
    calc
      -(3 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x =
          -(3 / 2 : Real) * (t * support.phi t x ^ 2 * w 2 t x) := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) hprod0
  have hpart0 :
      support.phi t x *
            (-2 * w 1 t x + towerReactionSum (M := M) w c 0 t x) +
          (1 / 2 : Real) * support.phi t x * w 1 t x +
          9 * eps * w 0 t x ≤
        -(3 / 2 : Real) * support.phi t x * w 1 t x +
          c * K ^ 3 + 9 * eps * K ^ 2 := by
    linarith [hqreact0, herr0]
  have hpart0beta := mul_le_mul_of_nonneg_left hpart0 hbeta0
  have hpart1 :
      support.phi t x ^ 2 *
            (w 1 t x + t * (-2 * w 2 t x +
              towerReactionSum (M := M) w c 1 t x)) +
          (1 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x +
          34 * eps * t * support.phi t x * w 1 t x ≤
        ((3 / 2 : Real) + 2 * c * alpha) *
          support.phi t x * w 1 t x := by
    linarith [hqreact1, herr1, htime1, hw2drop]
  have hraw :
      beta *
          (support.phi t x *
              (-2 * w 1 t x + towerReactionSum (M := M) w c 0 t x) +
            (1 / 2 : Real) * support.phi t x * w 1 t x +
            9 * eps * w 0 t x) +
        (support.phi t x ^ 2 *
              (w 1 t x + t * (-2 * w 2 t x +
                towerReactionSum (M := M) w c 1 t x)) +
            (1 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x +
            34 * eps * t * support.phi t x * w 1 t x) ≤
      beta * c * K ^ 3 + 9 * eps * beta * K ^ 2 := by
    have hqW : 0 ≤ support.phi t x * w 1 t x := mul_nonneg hq0 hw1n
    have hca : 0 ≤ c * alpha := mul_nonneg hc halpha
    calc
      beta *
            (support.phi t x *
                (-2 * w 1 t x + towerReactionSum (M := M) w c 0 t x) +
              (1 / 2 : Real) * support.phi t x * w 1 t x +
              9 * eps * w 0 t x) +
          (support.phi t x ^ 2 *
                (w 1 t x + t * (-2 * w 2 t x +
                  towerReactionSum (M := M) w c 1 t x)) +
              (1 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x +
              34 * eps * t * support.phi t x * w 1 t x) ≤
          beta * (-(3 / 2 : Real) * support.phi t x * w 1 t x +
              c * K ^ 3 + 9 * eps * K ^ 2) +
            ((3 / 2 : Real) + 2 * c * alpha) *
              support.phi t x * w 1 t x :=
        add_le_add hpart0beta hpart1
      _ = beta * c * K ^ 3 + 9 * eps * beta * K ^ 2 -
          (c * alpha) * (support.phi t x * w 1 t x) := by
        rw [hbeta_eq]
        ring
      _ ≤ beta * c * K ^ 3 + 9 * eps * beta * K ^ 2 :=
        sub_le_self _ (mul_nonneg hca hqW)
  have hcore : beta * c * K ^ 3 + 9 * eps * beta * K ^ 2 ≤
      (barTop + beta * towerFactCoeff 1 0 *
          towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
        9 * eps * beta * K ^ 2 := by
    have hfact : towerFactCoeff 1 0 = 1 := by
      norm_num [towerFactCoeff]
    have hgood : towerBarGood c (towerConst c alpha) 0 = c := by
      norm_num [towerBarGood, towerConst_zero, Finset.sum_range_succ]
    have hK3 : 0 ≤ K ^ 3 := pow_nonneg (le_of_lt hK) 3
    have hextra : 0 ≤ 2 * c * K ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hc) hK3
    have hbase : beta * c * K ^ 3 ≤ (2 * c + beta * c) * K ^ 3 := by
      calc
        beta * c * K ^ 3 ≤ 2 * c * K ^ 3 + beta * c * K ^ 3 :=
          le_add_of_nonneg_left hextra
        _ = (2 * c + beta * c) * K ^ 3 := by ring
    rw [hbarTop, towerBarTop_one, hfact, hgood]
    simp only [mul_one]
    simpa only [add_comm] using
      add_le_add_right hbase (9 * eps * beta * K ^ 2)
  exact hraw.trans hcore

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
private theorem support_bound
    {D : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (w wLap : Nat → Real → M → Real)
    (T c K alpha eps : Real)
    {t : Real} {x : M} {chi : Real → M → Real}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (hT : 0 < T) (hc : 0 ≤ c) (hK : 0 < K) (halpha : 0 ≤ alpha)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ s ∈ Set.Icc 0 T, 0 < s → s ∈ D.regular)
    (hTK : T ≤ alpha / K)
    (hsmall : 2 * eps * T * cutErrCoeff 1 ≤ 1)
    (heps : 0 ≤ eps)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (hchi : chi t x ∈ Set.Icc (0 : Real) 1)
    (hw_nonneg : ∀ k ≤ 2, ∀ s ∈ Set.Icc 0 T, ∀ y, 0 ≤ w k s y)
    (hw0 : w 0 t x ≤ K ^ 2)
    (hheat : ∀ k ≤ 1, TowerHeatBoundOn (D := D) w wLap c k)
    (hLap : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      heatOperatorWithDrift (I := I) G s
        (fun z : M ↦ (0 : TangentSpace I z)) (w k s) y = wLap k s y)
    (hw_space : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I 𝓘(Real, Real) (w k s) y)
    (hw_grad : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric s) (w k s) z) y)
    (hnorm : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      (G.metric s).inner y
          (gradientFun (I := I) (G.metric s) (w k s) y)
          (gradientFun (I := I) (G.metric s) (w k s) y) ≤
        4 * w k s y * w (k + 1) s y) :
    let beta := towerBeta c alpha (towerConst c alpha) 1
    let barTop := towerBarTop c (towerConst c alpha) 1
    let F : Real → M → Real := fun s y =>
      beta * support.phi s y * w 0 s y +
        s * support.phi s y ^ 2 * w 1 s y
    parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) F t x ≤
      (barTop + beta * towerFactCoeff 1 0 *
          towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
        9 * eps * beta * K ^ 2 := by
  classical
  dsimp only
  set beta : Real := towerBeta c alpha (towerConst c alpha) 1 with hbeta
  set barTop : Real := towerBarTop c (towerConst c alpha) 1 with hbarTop
  let u0 : Real → M → Real := fun s y =>
    beta * (s ^ 0 * support.phi s y ^ (0 + 1) * w 0 s y)
  let u1 : Real → M → Real := fun s y =>
    1 * (s ^ 1 * support.phi s y ^ (1 + 1) * w 1 s y)
  let term : Nat → Real → M → Real := fun i => if i = 0 then u0 else u1
  let F : Real → M → Real := fun s y =>
    beta * support.phi s y * w 0 s y +
      s * support.phi s y ^ 2 * w 1 s y
  have hbeta0 : 0 ≤ beta := by
    simpa only [hbeta] using towerBeta_nonneg hc halpha 1
  have h0 := level_data (I := I) (D := D) G w wLap T c eps beta 0 support
    hT ht htpos hbeta0 heps hslab hregular
    (hheat 0 (by omega))
    (hLap 0 (by omega)) (hw_space 0 (by omega)) (hw_grad 0 (by omega))
    (hw_nonneg 0 (by omega) t ht x) (hw_nonneg 1 (by omega) t ht x)
    (hnorm 0 (by omega) t ht htpos x)
  have h1 := level_data (I := I) (D := D) G w wLap T c eps 1 1 support
    hT ht htpos (by norm_num) heps hslab hregular
    (hheat 1 (by omega))
    (hLap 1 (by omega)) (hw_space 1 (by omega)) (hw_grad 1 (by omega))
    (hw_nonneg 1 (by omega) t ht x) (hw_nonneg 2 (by omega) t ht x)
    (hnorm 1 (by omega) t ht htpos x)
  have hu0 : u0 = fun s y =>
      beta * (s ^ 0 * support.phi s y ^ (0 + 1) * w 0 s y) := rfl
  have hu1 : u1 = fun s y =>
      1 * (s ^ 1 * support.phi s y ^ (1 + 1) * w 1 s y) := rfl
  rw [← hu0] at h0
  rw [← hu1] at h1
  have htime : ∀ i ∈ Finset.range 2,
      DifferentiableWithinAt Real (fun s => term i s x) (Set.Icc 0 T) t := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · simpa only [term, if_pos rfl] using h0.1
    · simpa only [term, if_neg (by omega : (1 : Nat) ≠ 0)] using h1.1
  have hspace : ∀ i ∈ Finset.range 2, ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (term i t) y := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · simpa only [term, if_pos rfl] using h0.2.1
    · simpa only [term, if_neg (by omega : (1 : Nat) ≠ 0)] using h1.2.1
  have hgrad : ∀ i ∈ Finset.range 2,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (term i t) y) x := by
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · simpa only [term, if_pos rfl] using h0.2.2.1
    · simpa only [term, if_neg (by omega : (1 : Nat) ≠ 0)] using h1.2.2.1
  have hFsum : F = fun s y => ∑ i ∈ Finset.range 2, term i s y := by
    funext s y
    rw [show (∑ i ∈ Finset.range 2, term i s y) = term 0 s y + term 1 s y by
      norm_num [Finset.sum_range_succ]]
    (simp [F, term, u0, u1]; ring)
  have hsum := parabolic_sum_nhds (I := I) (G := G)
    (Finset.range 2) T (fun _ y => (0 : TangentSpace I y)) term t x
    htime hspace hgrad
  have hop0 := h0.2.2.2
  have hop1 := h1.2.2.2
  have hsum_le :
      (∑ i ∈ Finset.range 2,
        parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) (term i) t x) ≤
      beta *
          (support.phi t x *
              (-2 * w 1 t x + towerReactionSum (M := M) w c 0 t x) +
            (1 / 2 : Real) * support.phi t x * w 1 t x +
            9 * eps * w 0 t x) +
        (support.phi t x ^ 2 *
              (w 1 t x + t * (-2 * w 2 t x +
                towerReactionSum (M := M) w c 1 t x)) +
            (1 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x +
            34 * eps * t * support.phi t x * w 1 t x) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hop0' :
        parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) u0 t x ≤
          beta *
            (support.phi t x *
                (-2 * w 1 t x + towerReactionSum (M := M) w c 0 t x) +
              (1 / 2 : Real) * support.phi t x * w 1 t x +
              9 * eps * w 0 t x) := by
      norm_num [u0, cutErrCoeff] at hop0 ⊢
      exact hop0
    have hop1' :
        parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y)) u1 t x ≤
          support.phi t x ^ 2 *
                (w 1 t x + t * (-2 * w 2 t x +
                  towerReactionSum (M := M) w c 1 t x)) +
              (1 / 2 : Real) * t * support.phi t x ^ 2 * w 2 t x +
              34 * eps * t * support.phi t x * w 1 t x := by
      norm_num [u1, cutErrCoeff] at hop1 ⊢
      exact hop1
    simpa only [term, if_pos rfl, if_neg (by omega : (1 : Nat) ≠ 0)] using
      add_le_add hop0' hop1'
  have hraw_bound := support_raw_bound (I := I) G w
    T c K alpha eps beta barTop support hc hK halpha hTK hsmall heps
    ht hchi hw_nonneg hw0 hbeta hbarTop
  have hFraw :
      (fun s y => beta * support.phi s y * w 0 s y +
        s * support.phi s y ^ 2 * w 1 s y) =
        (fun s y => ∑ i ∈ Finset.range 2, term i s y) := by
    simpa only [F] using hFsum
  have hsum_bound :
      (∑ i ∈ Finset.range 2,
        parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) (term i) t x) ≤
        (barTop + beta * towerFactCoeff 1 0 *
            towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
          9 * eps * beta * K ^ 2 :=
    hsum_le.trans hraw_bound
  have hopSum : parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y))
          (fun s y => ∑ i ∈ Finset.range 2, term i s y) t x ≤
        (barTop + beta * towerFactCoeff 1 0 *
            towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
          9 * eps * beta * K ^ 2 := by
    rw [hsum]
    exact hsum_bound
  exact prop_of_eq hFraw
    (fun f => parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) f t x ≤
        (barTop + beta * towerFactCoeff 1 0 *
            towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
          9 * eps * beta * K ^ 2) hopSum

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
private theorem support_data
    {D : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (w wLap : Nat → Real → M → Real)
    (T c K alpha eps : Real)
    {t : Real} {x : M} {chi : Real → M → Real}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (hT : 0 < T) (hc : 0 ≤ c) (hK : 0 < K) (halpha : 0 ≤ alpha)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ s ∈ Set.Icc 0 T, 0 < s → s ∈ D.regular)
    (hTK : T ≤ alpha / K)
    (hsmall : 2 * eps * T * cutErrCoeff 1 ≤ 1)
    (heps : 0 ≤ eps)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (hchi : chi t x ∈ Set.Icc (0 : Real) 1)
    (hw_nonneg : ∀ k ≤ 2, ∀ s ∈ Set.Icc 0 T, ∀ y, 0 ≤ w k s y)
    (hw0 : w 0 t x ≤ K ^ 2)
    (hheat : ∀ k ≤ 1, TowerHeatBoundOn (D := D) w wLap c k)
    (hLap : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      heatOperatorWithDrift (I := I) G s
        (fun z : M ↦ (0 : TangentSpace I z)) (w k s) y = wLap k s y)
    (hw_space : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I 𝓘(Real, Real) (w k s) y)
    (hw_grad : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric s) (w k s) z) y)
    (hnorm : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      (G.metric s).inner y
          (gradientFun (I := I) (G.metric s) (w k s) y)
          (gradientFun (I := I) (G.metric s) (w k s) y) ≤
        4 * w k s y * w (k + 1) s y) :
    let beta := towerBeta c alpha (towerConst c alpha) 1
    let barTop := towerBarTop c (towerConst c alpha) 1
    let F : Real → M → Real := fun s y =>
      beta * support.phi s y * w 0 s y +
        s * support.phi s y ^ 2 * w 1 s y
    DifferentiableWithinAt Real (fun s => F s x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (F t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x ∧
      parabolicOperatorWithDrift (I := I) G T
          (fun _ y => (0 : TangentSpace I y)) F t x ≤
        (barTop + beta * towerFactCoeff 1 0 *
            towerBarGood c (towerConst c alpha) 0) * K ^ 3 +
          9 * eps * beta * K ^ 2 := by
  have hreg := support_reg (I := I) (D := D) G w wLap T c alpha eps support
    hT hc halpha hslab hregular heps ht htpos hw_nonneg
    hheat hLap hw_space hw_grad hnorm
  have hop := support_bound (I := I) (D := D) G w wLap T c K alpha eps support
    hT hc hK halpha hslab hregular hTK hsmall heps ht htpos hchi
    hw_nonneg hw0 hheat hLap hw_space hw_grad hnorm
  dsimp only at hreg hop ⊢
  exact ⟨hreg.1, hreg.2.1, hreg.2.2, hop⟩

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- A fixed compactly supported cutoff gives the finite-error first Bernstein
estimate using only a zeroth-order bound where the cutoff is positive. -/
theorem estimate_cutoff_one
    {D : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (w wLap : Nat → Real → M → Real)
    (T c K alpha eps : Real)
    (cut : ShiFixedCutoff (I := I) G T eps)
    (hT : 0 < T)
    (hc : 0 ≤ c) (hK : 0 < K) (halpha : 0 ≤ alpha)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Set.Icc 0 T, 0 < t → t ∈ D.regular)
    (hTK : T ≤ alpha / K)
    (hsmall : 2 * eps * T * cutErrCoeff 1 ≤ 1)
    (hw_nonneg : ∀ k ≤ 2, ∀ t ∈ Set.Icc 0 T, ∀ x, 0 ≤ w k t x)
    (hw0_cut : ∀ t ∈ Set.Icc 0 T, ∀ x,
      0 < cut.chi t x → w 0 t x ≤ K ^ 2)
    (hheat : ∀ k ≤ 1, TowerHeatBoundOn (D := D) w wLap c k)
    (hLap : ∀ k ≤ 1, ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x,
      heatOperatorWithDrift (I := I) G t
        (fun y : M ↦ (0 : TangentSpace I y)) (w k t) x = wLap k t x)
    (hw_cont : ∀ k ≤ 1,
      ContinuousOn (fun p : Real × M ↦ w k p.1 p.2)
        (spacetimeSlab (M := M) T))
    (hw_space : ∀ k ≤ 1, ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x,
      MDifferentiableAt I 𝓘(Real, Real) (w k t) x)
    (hw_grad : ∀ k ≤ 1, ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w k t) y) x)
    (hnorm : ∀ k ≤ 1, ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x,
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (w k t) x)
          (gradientFun (I := I) (G.metric t) (w k t) x) ≤
        4 * w k t x * w (k + 1) t x) :
    let beta := towerBeta c alpha (towerConst c alpha) 1
    ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x,
      t * cut.chi t x ^ 2 * w 1 t x ≤
        (towerConst c alpha 1) ^ 2 * K ^ 2 +
          9 * eps * beta * K ^ 2 * t := by
  classical
  dsimp only
  set C : Nat → Real := towerConst c alpha with hC
  set beta : Real := towerBeta c alpha C 1 with hbeta
  set barTop : Real := towerBarTop c C 1 with hbarTop
  set aBar : Real := beta * K ^ 2 with haBar
  set bCore : Real :=
    (barTop + beta * towerFactCoeff 1 0 * towerBarGood c C 0) * K ^ 3
      with hbCore
  set bErr : Real := 9 * eps * beta * K ^ 2 with hbErr
  set bBar : Real := bCore + bErr with hbBar
  let F : Real → M → Real := fun s y =>
    beta * cut.chi s y * w 0 s y + s * cut.chi s y ^ 2 * w 1 s y
  let v : Real → M → Real := fun s y => (aBar + bBar * s) - F s y
  have hbeta0 : 0 ≤ beta := by
    simpa only [hbeta, hC] using towerBeta_nonneg hc halpha 1
  have hbarTop0 : 0 ≤ barTop := by
    simpa only [hbarTop, hC] using towerBarTop_nonneg hc alpha 1
  have haBar0 : 0 ≤ aBar := by
    rw [haBar]
    exact mul_nonneg hbeta0 (pow_nonneg (le_of_lt hK) 2)
  have hgood0 : 0 ≤ towerBarGood c C 0 := by
    simpa only [hC] using towerBarGood_nonneg hc alpha 0
  have hfact0 : 0 ≤ towerFactCoeff 1 0 := towerFactCoeff_nonneg 1 0
  have hbCore0 : 0 ≤ bCore := by
    rw [hbCore]
    exact mul_nonneg
      (add_nonneg hbarTop0 (mul_nonneg (mul_nonneg hbeta0 hfact0) hgood0))
      (pow_nonneg (le_of_lt hK) 3)
  have hbErr0 : 0 ≤ bErr := by
    rw [hbErr]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) cut.err_nonneg) hbeta0)
      (pow_nonneg (le_of_lt hK) 2)
  have hbBar0 : 0 ≤ bBar := by
    rw [hbBar]
    exact add_nonneg hbCore0 hbErr0
  have hFcont : ContinuousOn (fun p : Real × M => F p.1 p.2)
      (Set.Icc 0 T ×ˢ cut.support) := by
    have hw0c : ContinuousOn (fun p : Real × M => w 0 p.1 p.2)
        (Set.Icc 0 T ×ˢ cut.support) :=
      (hw_cont 0 (by omega)).mono (by
        intro p hp
        exact ⟨hp.1, Set.mem_univ p.2⟩)
    have hw1c : ContinuousOn (fun p : Real × M => w 1 p.1 p.2)
        (Set.Icc 0 T ×ˢ cut.support) :=
      (hw_cont 1 (by omega)).mono (by
        intro p hp
        exact ⟨hp.1, Set.mem_univ p.2⟩)
    exact (((continuous_const.continuousOn.mul cut.joint_cont).mul hw0c).add
      (((continuous_fst.continuousOn.mul (cut.joint_cont.pow 2))).mul hw1c))
  have hinit : ∀ y : M, F 0 y ≤ aBar := by
    intro y
    have h0mem : (0 : Real) ∈ Set.Icc 0 T := ⟨le_rfl, le_of_lt hT⟩
    by_cases hpos : 0 < cut.chi 0 y
    · have hw0 := hw0_cut 0 h0mem y hpos
      have hchi := cut.range 0 h0mem y
      change beta * cut.chi 0 y * w 0 0 y + 0 * cut.chi 0 y ^ 2 * w 1 0 y ≤ aBar
      simp only [zero_mul, add_zero]
      rw [haBar]
      calc
        beta * cut.chi 0 y * w 0 0 y ≤ beta * 1 * w 0 0 y :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hchi.2 hbeta0)
            (hw_nonneg 0 (by omega) 0 h0mem y)
        _ ≤ beta * K ^ 2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hw0 hbeta0
    · have hzero : cut.chi 0 y = 0 :=
        le_antisymm (le_of_not_gt hpos) (cut.range 0 h0mem y).1
      simp [F, hzero, haBar0]
  have hv_out : ∀ s ∈ Set.Icc 0 T, ∀ y, y ∉ cut.support → 0 ≤ v s y := by
    intro s hs y hy
    have hchi := cut.support_zero s hs y hy
    have hFzero : F s y = 0 := by simp [F, hchi]
    dsimp only [v]
    rw [hFzero, sub_zero]
    exact add_nonneg haBar0 (mul_nonneg hbBar0 hs.1)
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (Set.Icc 0 T ×ˢ cut.support) := by
    have haff : ContinuousOn (fun p : Real × M => aBar + bBar * p.1)
        (Set.Icc 0 T ×ˢ cut.support) :=
      (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn
    exact haff.sub hFcont
  have hv0 : ∀ y : M, 0 ≤ v 0 y := by
    intro y
    dsimp only [v]
    simpa only [mul_zero, add_zero] using sub_nonneg.mpr (hinit y)
  have hv_support : ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y, v s y < 0 →
      ParabolicUpperSupportAt (I := I) G T
        (fun _ z => (0 : TangentSpace I z)) v s y := by
    intro s hs hspos y hneg
    have haff0 : 0 ≤ aBar + bBar * s :=
      add_nonneg haBar0 (mul_nonneg hbBar0 hs.1)
    have hFpos : 0 < F s y := by
      dsimp only [v] at hneg
      linarith
    have hchiPos : 0 < cut.chi s y := by
      by_contra hnot
      have hchi0 : cut.chi s y = 0 :=
        le_antisymm (le_of_not_gt hnot) (cut.range s hs y).1
      have : F s y = 0 := by simp [F, hchi0]
      linarith
    let support : ShiCutoffLowerSupportAt (I := I) G T eps cut.chi s y :=
      Classical.choice (cut.lower_support s hs hspos y hchiPos)
    let Fs : Real → M → Real := fun r z =>
      beta * support.phi r z * w 0 r z +
        r * support.phi r z ^ 2 * w 1 r z
    let u : Real → M → Real := fun r z => (aBar + bBar * r) - Fs r z
    have hrec := support_data (I := I) (D := D) G w wLap T c K alpha eps support
      hT hc hK halpha hslab hregular hTK hsmall cut.err_nonneg hs hspos (cut.range s hs y)
      hw_nonneg (hw0_cut s hs y hchiPos) hheat hLap hw_space hw_grad hnorm
    have hFs_eq : Fs s y = F s y := by
      simp only [Fs, F, support.eq_at]
    refine
      { v := u
        eq_at := by simp only [u, v, hFs_eq]
        upper_nhds := ?_
        time_diff := ?_
        space_diff_nhds := ?_
        grad_diff := ?_
        operator_nonneg := ?_ }
    · filter_upwards [support.lower_nhds, self_mem_nhdsWithin] with p hp hpslab
      have hw0n := hw_nonneg 0 (by omega) p.1 hpslab.1 p.2
      have hw1n := hw_nonneg 1 (by omega) p.1 hpslab.1 p.2
      have hmono0 : support.phi p.1 p.2 * w 0 p.1 p.2 ≤
          cut.chi p.1 p.2 * w 0 p.1 p.2 :=
        mul_le_mul_of_nonneg_right hp.2 hw0n
      have hpow : support.phi p.1 p.2 ^ 2 ≤ cut.chi p.1 p.2 ^ 2 :=
        pow_le_pow_left₀ hp.1 hp.2 2
      have hmono1 : p.1 * support.phi p.1 p.2 ^ 2 * w 1 p.1 p.2 ≤
          p.1 * cut.chi p.1 p.2 ^ 2 * w 1 p.1 p.2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hpslab.1.1) hw1n
      have hmono : Fs p.1 p.2 ≤ F p.1 p.2 := by
        dsimp only [Fs, F]
        simpa only [mul_assoc] using
          add_le_add (mul_le_mul_of_nonneg_left hmono0 hbeta0) hmono1
      dsimp only [u, v]
      linarith
    · exact ((differentiableWithinAt_const aBar).add
        ((differentiableWithinAt_id'
          (𝕜 := Real) (s := Set.Icc 0 T) (x := s)).const_mul bBar)).sub hrec.1
    · filter_upwards [hrec.2.1] with z hz
      simpa only [u] using mdifferentiableAt_const.sub hz
    · refine (hrec.2.2.1.smul_const_section
          (a := (-1 : Real))).congr_of_eventuallyEq ?_
      filter_upwards [hrec.2.1] with z hz
      exact congrArg (fun b =>
        (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) (by
          calc
            gradientFun (I := I) (G.metric s) (u s) z =
                gradientFun (I := I) (G.metric s)
                    (fun _ : M => aBar + bBar * s) z -
                  gradientFun (I := I) (G.metric s) (Fs s) z := by
              simpa only [u] using gradientFun_sub (I := I) (G.metric s)
                mdifferentiableAt_const hz
            _ = -gradientFun (I := I) (G.metric s) (Fs s) z := by
              rw [gradientFun_const]
              simp
            _ = (-1 : Real) • gradientFun (I := I) (G.metric s) (Fs s) z := by simp)
    · have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) s :=
        (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hs
      have hop := parabolic_aff_nhds (I := I) T
        (fun _ z => (0 : TangentSpace I z)) Fs aBar bBar s y
        huniq hrec.1 hrec.2.1 hrec.2.2.1
      rw [show u = (fun r z => (aBar + bBar * r) - Fs r z) from rfl, hop]
      dsimp only [bBar, bCore, bErr]
      linarith [hrec.2.2.2]
  have hv_nonneg := strict_barrier_cpt_of_upperSupport
    (I := I) G T (fun _ z => (0 : TangentSpace I z)) v cut.support
    cut.support_compact hv_out hv_cont hv0 hv_support
  intro t ht htpos x
  have hvx := hv_nonneg t ht x
  have hFle : F t x ≤ aBar + bBar * t := by
    dsimp only [v] at hvx
    linarith
  have hleft : t * cut.chi t x ^ 2 * w 1 t x ≤ aBar + bBar * t := by
    have hfirst : 0 ≤ beta * cut.chi t x * w 0 t x :=
      mul_nonneg (mul_nonneg hbeta0 (cut.range t ht x).1)
        (hw_nonneg 0 (by omega) t ht x)
    dsimp only [F] at hFle
    linarith
  have htK : t * K ≤ alpha := by
    calc
      t * K ≤ (alpha / K) * K :=
        mul_le_mul_of_nonneg_right (ht.2.trans hTK) (le_of_lt hK)
      _ = alpha := div_mul_cancel₀ alpha (ne_of_gt hK)
  have hbase : aBar + bCore * t ≤ (towerConst c alpha 1) ^ 2 * K ^ 2 := by
    rw [towerConst_sq hc halpha, towerConstSq_pos c alpha (by omega : 0 < 1),
      haBar, hbCore, ← hbeta, ← hbarTop, ← hC]
    have hcoeff : 0 ≤ barTop + beta * towerFactCoeff 1 0 * towerBarGood c C 0 :=
      add_nonneg hbarTop0 (mul_nonneg (mul_nonneg hbeta0 hfact0) hgood0)
    have hK2 : 0 ≤ K ^ 2 := pow_nonneg (le_of_lt hK) 2
    simp only [Nat.reduceSub, Nat.factorial_zero, Nat.cast_one,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    nlinarith [mul_nonneg hcoeff hK2]
  rw [hbBar] at hleft
  rw [hC, hbErr]
  linarith

end DifferentialGeometry.PDE.RicciFlow
