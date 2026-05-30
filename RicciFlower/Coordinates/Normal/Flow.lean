import RicciFlower.Coordinates.Normal.Spray

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate normal coordinates

This file contains the reusable coordinate-defined normal-coordinate front end.
It deliberately starts with relation-valued endpoint data instead of defining
an exponential map as a function.  A functional exponential map requires the
next analytic layer: uniqueness and smooth dependence of the local geodesic
flow on initial velocity.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open scoped Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-- The model-spray nonlinear residual is uniformly little-o along the chosen
Picard trajectories, on any time interval where the flow is controlled.

This is the first real propagation step from the strict linearization of the
spray to the endpoint estimate. -/
lemma sprayRem_uniform
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε τ ρ : Real} {rModel : NNReal} {L' : NNReal}
    {α : E × E -> Real -> E × E}
    (hρ : 0 < ρ)
    (hτ : 0 < τ)
    (hsub : Set.Icc (0 : Real) τ ⊆ Set.Icc (-ε) ε)
    (hsmall : ∀ v ∈ Metric.ball (0 : TangentSpace I x) ρ,
      initPhase (I := I) x v ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel)
    (hzero : ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x))
    (hLip : ∀ t ∈ Set.Icc (-ε) ε,
      LipschitzOnWith L' (fun z => α z t)
        (Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel)) :
    ∀ c > 0, ∀ᶠ p : TangentSpace I x × TangentSpace I x in
      𝓝 ((0, 0) : TangentSpace I x × TangentSpace I x),
      ∀ t ∈ Set.Icc (0 : Real) τ,
        ‖modelSpray (I := I) g x
            (α (initPhase (I := I) x (τ⁻¹ • p.1)) t) -
          modelSpray (I := I) g x
            (α (initPhase (I := I) x (τ⁻¹ • p.2)) t) -
          modelSprayLin (E := E)
            (α (initPhase (I := I) x (τ⁻¹ • p.1)) t -
              α (initPhase (I := I) x (τ⁻¹ • p.2)) t)‖
          ≤ c * ‖p.1 - p.2‖ := by
  intro c hc
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  let rem : (E × E) × (E × E) -> E × E := fun q =>
    modelSpray (I := I) g x q.1 -
      modelSpray (I := I) g x q.2 -
      modelSprayLin (E := E) (q.1 - q.2)
  let Csep : Real := (L' : Real) * ‖τ⁻¹‖
  let η : Real := c / (Csep + 1)
  have hCsep_nonneg : 0 ≤ Csep := by
    dsimp [Csep]
    positivity
  have hdenη : 0 < Csep + 1 := by positivity
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hremEvt :
      {q : (E × E) × (E × E) |
        ‖rem q‖ ≤ η * ‖q.1 - q.2‖} ∈ 𝓝 (z0, z0) := by
    simpa [rem, z0, η] using
      (spray_o (I := I) g x).bound hη
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hremEvt
  let Clip : Real := (L' : Real) + 1
  have hClip : 0 < Clip := by
    dsimp [Clip]
    positivity
  let σ : Real := min ρ (δ / Clip)
  have hσ : 0 < σ := by
    dsimp [σ]
    exact lt_min hρ (div_pos hδ hClip)
  have hcont1 :
      ContinuousAt
        (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.1)
        ((0, 0) : TangentSpace I x × TangentSpace I x) := by
    fun_prop
  have hcont2 :
      ContinuousAt
        (fun p : TangentSpace I x × TangentSpace I x => τ⁻¹ • p.2)
        ((0, 0) : TangentSpace I x × TangentSpace I x) := by
    fun_prop
  have hnear1 := hcont1.preimage_mem_nhds (Metric.ball_mem_nhds _ hσ)
  have hnear2 := hcont2.preimage_mem_nhds (Metric.ball_mem_nhds _ hσ)
  filter_upwards [hnear1, hnear2] with p hp1 hp2 t ht
  let z1 : E × E := initPhase (I := I) x (τ⁻¹ • p.1)
  let z2 : E × E := initPhase (I := I) x (τ⁻¹ • p.2)
  have htE : t ∈ Set.Icc (-ε) ε := hsub ht
  have hp1ball : τ⁻¹ • p.1 ∈ Metric.ball (0 : TangentSpace I x) σ := by
    simpa using hp1
  have hp2ball : τ⁻¹ • p.2 ∈ Metric.ball (0 : TangentSpace I x) σ := by
    simpa using hp2
  have hp1ρ : τ⁻¹ • p.1 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hp1ball ⊢
    exact lt_of_lt_of_le hp1ball (min_le_left _ _)
  have hp2ρ : τ⁻¹ • p.2 ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hp2ball ⊢
    exact lt_of_lt_of_le hp2ball (min_le_left _ _)
  have hz1 : z1 ∈ Metric.closedBall z0 rModel := by
    simpa [z1, z0] using hsmall (τ⁻¹ • p.1) hp1ρ
  have hz2 : z2 ∈ Metric.closedBall z0 rModel := by
    simpa [z2, z0] using hsmall (τ⁻¹ • p.2) hp2ρ
  have hz0 : z0 ∈ Metric.closedBall z0 rModel :=
    Metric.mem_closedBall_self (NNReal.coe_nonneg rModel)
  have hp1δ : ‖τ⁻¹ • p.1‖ < δ / Clip := by
    rw [Metric.mem_ball, dist_zero_right] at hp1ball
    exact lt_of_lt_of_le hp1ball (min_le_right _ _)
  have hp2δ : ‖τ⁻¹ • p.2‖ < δ / Clip := by
    rw [Metric.mem_ball, dist_zero_right] at hp2ball
    exact lt_of_lt_of_le hp2ball (min_le_right _ _)
  have hLδ : (L' : Real) * (δ / Clip) < δ := by
    have hLlt : (L' : Real) < Clip := by
      dsimp [Clip]
      linarith [NNReal.coe_nonneg L']
    have hδdiv : 0 < δ / Clip := div_pos hδ hClip
    calc
      (L' : Real) * (δ / Clip) < Clip * (δ / Clip) :=
        mul_lt_mul_of_pos_right hLlt hδdiv
      _ = δ := by
        field_simp [hClip.ne']
  have hclose1 : ‖α z1 t - z0‖ < δ := by
    have hle := lip_norm_sub_le (hLip t htE) hz1 hz0
    have hz := hzero t htE
    dsimp [z1] at hle
    rw [hz] at hle
    have hinit : ‖z1 - z0‖ < δ / Clip := by
      simpa [z1, z0] using
        (norm_initPhase_zero (I := I) x (τ⁻¹ • p.1)).trans_lt hp1δ
    exact lt_of_le_of_lt hle
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hinit.le (NNReal.coe_nonneg L'))
        hLδ)
  have hclose2 : ‖α z2 t - z0‖ < δ := by
    have hle := lip_norm_sub_le (hLip t htE) hz2 hz0
    have hz := hzero t htE
    dsimp [z2] at hle
    rw [hz] at hle
    have hinit : ‖z2 - z0‖ < δ / Clip := by
      simpa [z2, z0] using
        (norm_initPhase_zero (I := I) x (τ⁻¹ • p.2)).trans_lt hp2δ
    exact lt_of_le_of_lt hle
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hinit.le (NNReal.coe_nonneg L'))
        hLδ)
  have hqball : (α z1 t, α z2 t) ∈ Metric.ball (z0, z0) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖(α z1 t - z0, α z2 t - z0)‖ < δ
    change max ‖α z1 t - z0‖ ‖α z2 t - z0‖ < δ
    exact max_lt hclose1 hclose2
  have hrem := hδsub hqball
  have hsep : ‖α z1 t - α z2 t‖ ≤ Csep * ‖p.1 - p.2‖ := by
    have hle := lip_norm_sub_le (hLip t htE) hz1 hz2
    have hinit : ‖z1 - z2‖ = ‖τ⁻¹ • (p.1 - p.2)‖ := by
      simp [z1, z2, norm_initPhase_sub, smul_sub]
    calc
      ‖α z1 t - α z2 t‖ ≤ (L' : Real) * ‖z1 - z2‖ := hle
      _ = (L' : Real) * ‖τ⁻¹ • (p.1 - p.2)‖ := by rw [hinit]
      _ = Csep * ‖p.1 - p.2‖ := by
        simp [Csep, norm_smul, mul_assoc, mul_comm, mul_left_comm]
  have hηC : η * Csep ≤ c := by
    dsimp [η]
    field_simp [hdenη.ne']
    nlinarith [mul_le_mul_of_nonneg_left
      (show Csep ≤ Csep + 1 by linarith) hc.le]
  calc
    ‖modelSpray (I := I) g x (α z1 t) -
          modelSpray (I := I) g x (α z2 t) -
          modelSprayLin (E := E) (α z1 t - α z2 t)‖
        = ‖rem (α z1 t, α z2 t)‖ := by rfl
    _ ≤ η * ‖α z1 t - α z2 t‖ := by
      simpa [rem] using hrem
    _ ≤ η * (Csep * ‖p.1 - p.2‖) :=
      mul_le_mul_of_nonneg_left hsep hη.le
    _ = (η * Csep) * ‖p.1 - p.2‖ := by ring
    _ ≤ c * ‖p.1 - p.2‖ :=
      mul_le_mul_of_nonneg_right hηC (norm_nonneg _)

/-- The zero phase point is an equilibrium of the fixed-chart model spray. -/
theorem modelSpray_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    modelSpray (I := I) g x
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) = 0 := by
  have hq :
      phaseOfModel (I := I) x
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) =
        phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc :
      (phaseOfModel (I := I) x
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))).proj ∈
        (extChartAt I x).source := by
    rw [hq]
    simp [phaseZero]
  rw [modelSpray_eq_fiber (I := I) g x hsrc, hq]
  have hv :
      chartFiberCoordAt (I := I) x (phaseZero (I := I) x) = 0 := by
    simp [phaseZero]
    simpa [phaseZero] using
      chartFiberCoordAt_self (I := I)
        (u := (phaseZero (I := I) x))
  change
    (chartFiberCoordAt (I := I) x (phaseZero (I := I) x),
      leviCivitaGeodesicSprayAcceleration (I := I) g x
        (extChartAt I x (phaseZero (I := I) x).proj)
        (chartFiberCoordAt (I := I) x (phaseZero (I := I) x))) = (0, 0)
  rw [hv]
  simp [leviCivitaGeodesicSprayAcceleration,
    leviCivitaGeodesicSprayQuadratic, modelCoord]

/-- Local Picard-Lindelof data for the fixed-chart model spray near the zero
phase point.

This is uniform for initial phase points in a small closed model ball, but only
on a short time interval.  Extending this checked local flow to time `1` is the
remaining continuation argument for `exists_exp_one`. -/
theorem modelSpray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => modelSpray (I := I) g x)
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x))
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (modelSpray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

/-- Picard-Lindelof local solutions stay in the controlling closed ball.

Mathlib's public existence theorem returns the derivative equation but hides
this bound.  The normal-coordinate endpoint proof needs the bound to keep the
model solution inside the fixed tangent-bundle chart source. -/
theorem plSol_bounded
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 x : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (hx : x ∈ Metric.closedBall x0 r) :
    ∃ α : Real -> F, α t0 = x ∧
      (∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt α (f t (α t)) (Set.Icc tmin tmax) t) ∧
      ∀ t : Real, α t ∈ Metric.closedBall x0 a := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t
    exact α.compProj_mem_closedBall hf.mul_max_le

/-- Functional Picard-Lindelof flow with both Lipschitz dependence on the
initial condition and the closed-ball bound for the same chosen flow. -/
theorem plFlow_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K) :
    ∃ α : F -> Real -> F,
      (∀ x ∈ Metric.closedBall x0 r, α x t0 = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t)) (Set.Icc tmin tmax) t) ∧
      (∀ x ∈ Metric.closedBall x0 r, ∀ t : Real,
        α x t ∈ Metric.closedBall x0 a) ∧
      (∀ x ∈ Metric.closedBall x0 r, ∀ t ∈ Set.Icc tmin tmax,
        α x t = ODE.picard f t0 x (α x) t) ∧
      ∃ L' : NNReal, ∀ t ∈ Set.Icc tmin tmax,
        LipschitzOnWith L' (fun x => α x t) (Metric.closedBall x0 r) := by
  classical
  have hfixed (x : F) (hx : x ∈ Metric.closedBall x0 r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose β hβ using hfixed
  let α : F -> Real -> F := fun x =>
    if hx : x ∈ Metric.closedBall x0 r then (β x hx).compProj else 0
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · change (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t0 = x
      rw [dif_pos hx, ODE.FunSpace.compProj_val, ← hβ x hx,
        ODE.FunSpace.next_apply₀]
    · intro t ht
      change HasDerivWithinAt
        (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0)
        (f t ((if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t))
        (Set.Icc tmin tmax) t
      rw [dif_pos hx]
      apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
        (β x hx).continuous_compProj.continuousOn
        (fun _ _ => (β x hx).compProj_mem_closedBall hf.mul_max_le)
        x ht).congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hβ x hx]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro x hx t
    change (if hx' : x ∈ Metric.closedBall x0 r then
        (β x hx').compProj else 0) t ∈ Metric.closedBall x0 a
    rw [dif_pos hx]
    exact (β x hx).compProj_mem_closedBall hf.mul_max_le
  · intro x hx t ht
    change (if hx' : x ∈ Metric.closedBall x0 r then
        (β x hx').compProj else 0) t =
      ODE.picard f t0 x
        (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t
    rw [dif_pos hx, ODE.FunSpace.compProj_of_mem ht]
    have hfixed :=
      (ODE.FunSpace.isFixedPt_next_iff hf hx).mp (hβ x hx)
    simpa [dif_pos hx] using hfixed (⟨t, ht⟩ : Set.Icc tmin tmax)
  · obtain ⟨L', hL'⟩ :=
      ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    have : Nonempty (Set.Icc tmin tmax) := ⟨t0⟩
    have hdist :=
      hL' x y hx hy (β x hx) (β y hy) (hβ x hx) (hβ y hy)
    have hpoint :=
      (ContinuousMap.dist_le_iff_of_nonempty.mp hdist)
        (⟨t, ht⟩ : Set.Icc tmin tmax)
    change dist
        ((if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t)
        ((if hy' : y ∈ Metric.closedBall x0 r then
          (β y hy').compProj else 0) t) ≤
      ↑L' * dist x y
    rw [dif_pos hx, dif_pos hy]
    rw [ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.compProj_of_mem ht]
    simpa [ODE.FunSpace.toContinuousMap_apply_eq_apply] using hpoint

/-- A functional Picard-Lindelof flow agrees with any other solution through
the same initial point, as long as both curves stay in the controlling closed
ball. -/
theorem plFlow_eq_of_solution
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (ht0 : (t0 : Real) ∈ Set.Ioo tmin tmax)
    {α : F -> Real -> F}
    (hflow : ∀ x ∈ Metric.closedBall x0 r,
      α x t0 = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t))
            (Set.Icc tmin tmax) t)
    (hbound : ∀ x ∈ Metric.closedBall x0 r, ∀ t : Real,
      α x t ∈ Metric.closedBall x0 a)
    {β : Real -> F}
    (hβ0 : β t0 = x0)
    (hβcont : ContinuousOn β (Set.Icc tmin tmax))
    (hβderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt β (f t (β t)) t)
    (hβbound : ∀ t ∈ Set.Icc tmin tmax,
      β t ∈ Metric.closedBall x0 a) :
    ∀ t ∈ Set.Icc tmin tmax, α x0 t = β t := by
  have hx0r : x0 ∈ Metric.closedBall x0 r :=
    Metric.mem_closedBall_self (NNReal.coe_nonneg r)
  have hαcont : ContinuousOn (α x0) (Set.Icc tmin tmax) := by
    exact HasDerivWithinAt.continuousOn
      (fun t ht => (hflow x0 hx0r).2 t ht)
  have hαderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt (α x0) (f t (α x0 t)) t := by
    intro t ht
    have hwithin := (hflow x0 hx0r).2 t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc tmin tmax ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hinit : α x0 t0 = β t0 := by
    rw [(hflow x0 hx0r).1, hβ0]
  have hEq : Set.EqOn (α x0) β (Set.Icc tmin tmax) := by
    exact ODE_solution_unique_of_mem_Icc
      (v := f) (s := fun _ : Real => Metric.closedBall x0 a)
      (K := K) (t₀ := (t0 : Real)) (a := tmin) (b := tmax)
      (fun t ht => hf.lipschitzOnWith t (Set.Ioo_subset_Icc_self ht))
      ht0 hαcont hαderiv
      (fun _ _ => hbound x0 hx0r _)
      hβcont hβderiv
      (fun t ht => hβbound t (Set.Ioo_subset_Icc_self ht))
      hinit
  intro t ht
  exact hEq ht

/-- A functional Picard-Lindelof flow agrees with any controlled solution
through any initial point in the controlling closed ball. -/
theorem plFlow_eq_of_solution_at
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 x : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (ht0 : (t0 : Real) ∈ Set.Ioo tmin tmax)
    (hx : x ∈ Metric.closedBall x0 r)
    {alpha : F -> Real -> F}
    (hflow : ∀ y ∈ Metric.closedBall x0 r,
      alpha y t0 = y ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (alpha y) (f t (alpha y t))
            (Set.Icc tmin tmax) t)
    (hbound : ∀ y ∈ Metric.closedBall x0 r, ∀ t : Real,
      alpha y t ∈ Metric.closedBall x0 a)
    {beta : Real -> F}
    (hbeta0 : beta t0 = x)
    (hbetacont : ContinuousOn beta (Set.Icc tmin tmax))
    (hbetaderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt beta (f t (beta t)) t)
    (hbetabound : ∀ t ∈ Set.Icc tmin tmax,
      beta t ∈ Metric.closedBall x0 a) :
    ∀ t ∈ Set.Icc tmin tmax, alpha x t = beta t := by
  have halphacont : ContinuousOn (alpha x) (Set.Icc tmin tmax) := by
    exact HasDerivWithinAt.continuousOn
      (fun t ht => (hflow x hx).2 t ht)
  have halphaderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt (alpha x) (f t (alpha x t)) t := by
    intro t ht
    have hwithin := (hflow x hx).2 t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc tmin tmax ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hinit : alpha x t0 = beta t0 := by
    rw [(hflow x hx).1, hbeta0]
  have hEq : Set.EqOn (alpha x) beta (Set.Icc tmin tmax) := by
    exact ODE_solution_unique_of_mem_Icc
      (v := f) (s := fun _ : Real => Metric.closedBall x0 a)
      (K := K) (t₀ := (t0 : Real)) (a := tmin) (b := tmax)
      (fun t ht => hf.lipschitzOnWith t (Set.Ioo_subset_Icc_self ht))
      ht0 halphacont halphaderiv
      (fun _ _ => hbound x hx _)
      hbetacont hbetaderiv
      (fun t ht => hbetabound t (Set.Ioo_subset_Icc_self ht))
      hinit
  intro t ht
  exact hEq ht

/-- Picard-Lindelof vector fields are interval-integrable along a controlled
continuous trajectory. -/
lemma pl_int
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    {α : Real -> F}
    (hα : ContinuousOn α (Set.Icc tmin tmax))
    (hbound : ∀ s : Real, α s ∈ Metric.closedBall x0 a)
    {t : Real} (ht : t ∈ Set.Icc tmin tmax) :
    IntervalIntegrable (fun s : Real => f s (α s))
      MeasureTheory.volume (t0 : Real) t := by
  have hpair :
      ContinuousOn (fun s : Real => (s, α s)) (Set.Icc tmin tmax) :=
    continuousOn_id.prodMk hα
  have hF :
      ContinuousOn (fun s : Real => f s (α s)) (Set.Icc tmin tmax) := by
    refine hf.continuousOn_uncurry.comp hpair ?_
    intro s hs
    exact ⟨hs, hbound s⟩
  have hsub : Set.uIcc (t0 : Real) t ⊆ Set.Icc tmin tmax :=
    Set.uIcc_subset_Icc t0.2 ht
  exact (hF.mono hsub).intervalIntegrable

lemma fst_int_sub
    {f g : Real -> E × E} {a b : Real}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ((∫ s in a..b, f s).1 - (∫ s in a..b, g s).1) =
      ∫ s in a..b, (f s - g s).1 := by
  calc
    ((∫ s in a..b, f s).1 - (∫ s in a..b, g s).1)
        = ((∫ s in a..b, f s) - (∫ s in a..b, g s)).1 := by
      rfl
    _ = (∫ s in a..b, f s - g s).1 := by
      rw [intervalIntegral.integral_sub hf hg]
    _ = ∫ s in a..b, (f s - g s).1 := by
      exact ((ContinuousLinearMap.fst Real E E).intervalIntegral_comp_comm
        (hf.sub hg)).symm

lemma snd_int_sub
    {f g : Real -> E × E} {a b : Real}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ((∫ s in a..b, f s).2 - (∫ s in a..b, g s).2) =
      ∫ s in a..b, (f s - g s).2 := by
  calc
    ((∫ s in a..b, f s).2 - (∫ s in a..b, g s).2)
        = ((∫ s in a..b, f s) - (∫ s in a..b, g s)).2 := by
      rfl
    _ = (∫ s in a..b, f s - g s).2 := by
      rw [intervalIntegral.integral_sub hf hg]
    _ = ∫ s in a..b, (f s - g s).2 := by
      exact ((ContinuousLinearMap.snd Real E E).intervalIntegral_comp_comm
        (hf.sub hg)).symm

lemma int_const_zero (τ : Real) (c : E) :
    (∫ _s in (0 : Real)..τ, c) = τ • c := by
  calc
    (∫ _s in (0 : Real)..τ, c) = (τ - 0) • c := by
      rw [intervalIntegral.integral_const]
    _ = τ • c := by
      rw [sub_zero]

lemma const_int (τ : Real) (c : E) :
    IntervalIntegrable (fun _ : Real => c) MeasureTheory.volume (0 : Real) τ :=
  continuousOn_const.intervalIntegrable

lemma int_sub_const
    {f h : Real -> E} {τ : Real} {c : E}
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : Real) τ)
    (hc : IntervalIntegrable (fun _ : Real => c) MeasureTheory.volume (0 : Real) τ)
    (heq : Set.EqOn f (fun t : Real => c + h t) (Set.uIcc (0 : Real) τ)) :
    (∫ t in (0 : Real)..τ, f t) - τ • c =
      ∫ t in (0 : Real)..τ, h t := by
  calc
    (∫ t in (0 : Real)..τ, f t) - τ • c
        = (∫ t in (0 : Real)..τ, f t) -
            ∫ _t in (0 : Real)..τ, c := by
      rw [int_const_zero]
    _ = ∫ t in (0 : Real)..τ, f t - c := by
      rw [intervalIntegral.integral_sub hf hc]
    _ = ∫ t in (0 : Real)..τ, h t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.uIcc (0 : Real) τ := by simpa using ht
      change f t - c = h t
      rw [heq ht']
      change (c + h t) - c = h t
      abel

/-- A Picard-Lindelof solution whose controlling ball lies in the fixed chart
source gives an ordinary model ODE solution on the open time interval, with
source control for `phaseOfModel`. -/
theorem modelFlow_src_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => modelSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
      a r L K)
    (hsrc : Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) a ⊆
        {z : E × E |
          z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source})
    {z : E × E}
    (hz : z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r) :
    ∃ α : Real -> E × E,
      α 0 = z ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt α (modelSpray (I := I) g x (α t)) t) ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x (α t)).proj ∈
              (extChartAt I x).source := by
  obtain ⟨α, hα0, hαderiv, hαbound⟩ :=
    plSol_bounded (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl hz
  refine ⟨α, by simpa using hα0, ?_, ?_⟩
  · intro t ht
    have htIcc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
    have hwithin := hαderiv t (by simpa using htIcc)
    have hIcc_mem : Set.Icc (0 - ε) (0 + ε) ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  · intro t ht
    exact hsrc (hαbound t)

/-- The fixed tangent-bundle model chart is a valid source neighborhood for
points whose model coordinates are close to the zero phase. -/
theorem modelSrc_nhds
    [I.Boundaryless] (x : M) :
    {z : E × E |
      z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source} ∈
      𝓝 (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseZero (I := I) x) := by
    have hproj :
        ContinuousAt
          (fun q : TangentBundle I M => q.proj)
          (phaseZero (I := I) x) :=
      (FiberBundle.continuous_proj E
        (TangentSpace I : M -> Type _)).continuousAt
    exact hproj.preimage_mem_nhds
      (by
        simpa [extChartAt_source] using
          extChartAt_source_mem_nhds (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc_nhds' :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hsrc_nhds
  have hphase_cont := (phaseOfModel_cdAt (I := I) x).continuousAt
  have htarget :
      (extChartAt I.tangent (phaseZero (I := I) x)).target ∈ 𝓝 z0 :=
    (isOpen_extChartAt_target (I := I.tangent)
      (phaseZero (I := I) x)).mem_nhds
      ((extChartAt I.tangent (phaseZero (I := I) x)).map_source
        (mem_extChartAt_source (I := I.tangent) (phaseZero (I := I) x)))
  exact Filter.inter_mem htarget
    (by
      simpa [z0, Set.preimage, Function.comp_def] using
        hphase_cont.preimage_mem_nhds hsrc_nhds')

/-- Picard-Lindelof data at time `0`, shrunk so the whole controlling model
ball stays in the fixed tangent-bundle chart source. -/
theorem modelSpray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a ⊆
          {z : E × E |
            z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x z).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => modelSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (modelSrc_nhds (I := I) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a δnn
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have ha' : 0 < a' := by
    exact lt_min ha hδnn
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => modelSpray (I := I) g x)
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro z hz
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist z z0 ≤ (a' : Real) := by
    simpa [z0] using Metric.mem_closedBall.mp hz
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist z z0 ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

/-- Uniform short-time model flow with source control in the fixed
tangent-bundle chart around `0_x`. -/
theorem modelFlow_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r,
        ∃ α : Real -> E × E,
          α 0 = z ∧
            (∀ t ∈ Set.Ioo (-ε) ε,
              HasDerivAt α (modelSpray (I := I) g x (α t)) t) ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (α t)).proj ∈
                  (extChartAt I x).source := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  refine ⟨ε, hε, r, hr, ?_⟩
  intro z hz
  exact modelFlow_src_of_pl (I := I) g x hε hpl hsrc hz

/-- Uniform short-time model flow with Lipschitz dependence on the initial
phase point.

This is the first analytic upgrade beyond relation-valued endpoint existence:
the Picard-Lindelof package supplies a single local flow `α z t` and a
Lipschitz estimate in the initial model phase `z`.  It does not yet assert
source control or strict differentiability of the endpoint map. -/
theorem modelFlow_lipschitz
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ α : E × E -> Real -> E × E,
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          α z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (α z)
                (modelSpray (I := I) g x (α z t))
                (Set.Icc (-ε) ε) t) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun z => α z t)
                (Metric.closedBall
                  (extChartAt I.tangent (phaseZero (I := I) x)
                    (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨ε, hε, r, hr, α, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- Uniform short-time model flow with source control and Lipschitz dependence
for the same chosen functional flow. -/
theorem modelFlow_srcLip
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ α : E × E -> Real -> E × E,
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          α z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (α z)
                (modelSpray (I := I) g x (α z t))
                (Set.Icc (-ε) ε) t) ∧
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          ∀ t ∈ Set.Icc (-ε) ε,
            α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x (α z t)).proj ∈
                (extChartAt I x).source) ∧
        ∃ L' : NNReal,
          ∀ t ∈ Set.Icc (-ε) ε,
            LipschitzOnWith L'
              (fun z => α z t)
              (Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl
  refine ⟨ε, hε, r, hr, α, ?_, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    exact hsrc (hbound z hz' t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- Functional Picard-Lindelof flow with all raw data retained.

This is the package needed for the strict endpoint frontier: the same chosen
flow carries the derivative equation, the Picard-Lindelof vector-field
Lipschitz bound, the closed-ball bound, chart-source control, and Lipschitz
dependence on the initial phase. -/
theorem modelFlow_pack
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a ⊆
          {z : E × E |
            z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x z).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => modelSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
          a r L K ∧
        ∃ α : E × E -> Real -> E × E,
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            α z 0 = z ∧
              ∀ t ∈ Set.Icc (-ε) ε,
                HasDerivWithinAt (α z)
                  (modelSpray (I := I) g x (α z t))
                  (Set.Icc (-ε) ε) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t : Real,
              α z t ∈ Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) a) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              α z t =
                ODE.picard (fun _ : Real => modelSpray (I := I) g x)
                  (⟨0, by simp [le_of_lt hε]⟩ :
                    Set.Icc (0 - ε) (0 + ε)) z (α z) t) ∧
          (∀ z ∈ Metric.closedBall
              (extChartAt I.tangent (phaseZero (I := I) x)
                (phaseZero (I := I) x)) r,
            ∀ t ∈ Set.Icc (-ε) ε,
              α z t ∈ (extChartAt I.tangent
                (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (α z t)).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun z => α z t)
                (Metric.closedBall
                  (extChartAt I.tangent (phaseZero (I := I) x)
                    (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, hbound, hpicard, L', hLip⟩ :=
    plFlow_bound (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl
  refine ⟨ε, hε, a, r, L, K, hr, hsrc, hpl, α, ?_, ?_, ?_, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro z hz t
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    simpa [z0] using hbound z hz' t
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hpicard z hz' t ht'
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    exact hsrc (hbound z hz' t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- The functional Picard-Lindelof flow fixes an equilibrium point.

This is a generic ODE uniqueness wrapper for the exact flow returned by the
Picard-Lindelof package.  In the normal-coordinate application the equilibrium
is the zero phase coordinate and the zero vector-field fact is
`modelSpray_zero`. -/
theorem plFlow_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (ht0 : (t0 : Real) ∈ Set.Ioo tmin tmax)
    {α : F -> Real -> F}
    (hflow : ∀ x ∈ Metric.closedBall x0 r,
      α x t0 = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t))
            (Set.Icc tmin tmax) t)
    (hbound : ∀ x ∈ Metric.closedBall x0 r, ∀ t : Real,
      α x t ∈ Metric.closedBall x0 a)
    (hzero : ∀ t ∈ Set.Ioo tmin tmax, f t x0 = 0) :
    ∀ t ∈ Set.Icc tmin tmax, α x0 t = x0 := by
  have hx0r : x0 ∈ Metric.closedBall x0 r :=
    Metric.mem_closedBall_self (NNReal.coe_nonneg r)
  have hαcont : ContinuousOn (α x0) (Set.Icc tmin tmax) := by
    exact HasDerivWithinAt.continuousOn
      (fun t ht => (hflow x0 hx0r).2 t ht)
  have hαderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt (α x0) (f t (α x0 t)) t := by
    intro t ht
    have hwithin := (hflow x0 hx0r).2 t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc tmin tmax ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hconstcont :
      ContinuousOn (fun _ : Real => x0) (Set.Icc tmin tmax) :=
    continuous_const.continuousOn
  have hconstderiv : ∀ t ∈ Set.Ioo tmin tmax,
      HasDerivAt (fun _ : Real => x0)
        (f t ((fun _ : Real => x0) t)) t := by
    intro t ht
    simpa [hzero t ht] using
      (hasDerivAt_const (x := t) (c := x0))
  have hEq : Set.EqOn (α x0) (fun _ : Real => x0)
      (Set.Icc tmin tmax) := by
    exact ODE_solution_unique_of_mem_Icc
      (v := f) (s := fun _ : Real => Metric.closedBall x0 a)
      (K := K) (t₀ := (t0 : Real)) (a := tmin) (b := tmax)
      (fun t ht => hf.lipschitzOnWith t (Set.Ioo_subset_Icc_self ht))
      ht0 hαcont hαderiv
      (fun _ _ => hbound x0 hx0r _)
      hconstcont hconstderiv
      (fun _ _ => Metric.mem_closedBall_self (NNReal.coe_nonneg a))
      (hflow x0 hx0r).1
  intro t ht
  exact hEq ht

/-- The model flow produced at the zero phase keeps the zero phase fixed. -/
theorem modelFlow_zero
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => modelSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
      a r L K)
    {α : E × E -> Real -> E × E}
    (hflow : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      α z 0 = z ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (α z)
            (modelSpray (I := I) g x (α z t))
            (Set.Icc (-ε) ε) t)
    (hbound : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t : Real,
        α z t ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a) :
    ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have ht0 : ((⟨0, by simp [le_of_lt hε]⟩ :
      Set.Icc (0 - ε) (0 + ε)) : Real) ∈
      Set.Ioo (0 - ε) (0 + ε) := by
    simpa using hε
  have hzero : ∀ t ∈ Set.Ioo (0 - ε) (0 + ε),
      (fun _ : Real => modelSpray (I := I) g x) t z0 = 0 := by
    intro t ht
    simpa [z0] using modelSpray_zero (I := I) g x
  have hfix := plFlow_zero
    (F := E × E)
    (f := fun _ : Real => modelSpray (I := I) g x)
    (tmin := 0 - ε) (tmax := 0 + ε)
    (t0 := ⟨0, by simp [le_of_lt hε]⟩)
    (x0 := z0) (a := a) (r := r) (L := L) (K := K)
    hpl ht0
    (α := α)
    (by
      intro z hz
      simpa [z0] using hflow z hz)
    (by
      intro z hz t
      simpa [z0] using hbound z hz t)
    hzero
  intro t ht
  have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
    simpa using ht
  simpa [z0] using hfix t ht'

/-- Short-time model flow produced by the local Picard-Lindelof package.

This is still a short-time statement.  It is the checked analytic producer
that should feed either a continuation argument or the homogeneous rescaling
argument for `exists_exp_one`. -/
theorem modelFlow_short
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r,
        ∃ α : Real -> E × E,
          α 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt α
                (modelSpray (I := I) g x (α t))
                (Set.Icc (-ε) ε) t := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  refine ⟨ε, hε, r, hr, ?_⟩
  intro z hz
  obtain ⟨α, hα0, hαderiv⟩ :=
    (hpl 0).exists_eq_forall_mem_Icc_hasDerivWithinAt
      (x := z) (by simpa [z0] using hz)
  refine ⟨α, hα0, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
    simpa using ht
  simpa using hαderiv t ht'

/-- Chart coordinate of the time-one endpoint produced from a fixed functional
model flow and the homogeneous time rescaling. -/
def chartEnd
    (α : E × E -> Real -> E × E) (τ : Real) (x : M)
    (v : TangentSpace I x) : E :=
  (α (initPhase (I := I) x (τ⁻¹ • v)) τ).1

/-- Manifold endpoint produced from a fixed functional model flow and the
homogeneous time rescaling. -/
def manifoldEnd
    (α : E × E -> Real -> E × E) (τ : Real) (x : M)
    (v : TangentSpace I x) : M :=
  (phaseOfModel (I := I) x
    (chartEnd (I := I) α τ x v,
      τ • (α (initPhase (I := I) x (τ⁻¹ • v)) τ).2)).proj

/-- Zero initial velocity has zero chart endpoint for a functional model flow
that fixes the zero phase. -/
theorem chartEnd_zero
    {α : E × E -> Real -> E × E} {ε τ : Real} (x : M)
    (hτ : τ ∈ Set.Icc (-ε) ε)
    (hzero : ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :
    chartEnd (I := I) α τ x (0 : TangentSpace I x) =
      extChartAt I x x := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hinit :
      initPhase (I := I) x (τ⁻¹ • (0 : TangentSpace I x)) = z0 := by
    simp [z0]
  have hz : α z0 τ = z0 := by
    simpa [z0] using hzero τ hτ
  calc
    chartEnd (I := I) α τ x (0 : TangentSpace I x)
        = (α z0 τ).1 := by
          simp [chartEnd, z0]
    _ = z0.1 := by rw [hz]
    _ = extChartAt I x x := by
      simpa [z0] using congrArg Prod.fst (phaseZero_pair (I := I) x)

/-- Zero initial velocity gives the base point for a functional model flow
that fixes the zero phase. -/
theorem manifoldEnd_zero
    {α : E × E -> Real -> E × E} {ε τ : Real} (x : M)
    (hτ : τ ∈ Set.Icc (-ε) ε)
    (hzero : ∀ t ∈ Set.Icc (-ε) ε,
      α (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) t =
        extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :
    manifoldEnd (I := I) α τ x (0 : TangentSpace I x) = x := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hτzero : α z0 τ = z0 := by
    simpa [z0] using hzero τ hτ
  have hfst := chartEnd_zero (I := I) (α := α) (ε := ε)
    (τ := τ) x hτ hzero
  have hpair :
      (chartEnd (I := I) α τ x (0 : TangentSpace I x),
        τ • (α (initPhase (I := I) x
          (τ⁻¹ • (0 : TangentSpace I x))) τ).2) = z0 := by
    have hinit :
        initPhase (I := I) x (τ⁻¹ • (0 : TangentSpace I x)) = z0 := by
      simp [z0]
    rw [hfst, hinit, hτzero]
    apply Prod.ext
    · simpa [z0] using congrArg Prod.fst (phaseZero_pair (I := I) x)
    · have hsnd : z0.2 = (0 : E) := by
        simpa [z0] using congrArg Prod.snd (phaseZero_pair (I := I) x)
      rw [hsnd, smul_zero]
  have hphase :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  change (phaseOfModel (I := I) x
    (chartEnd (I := I) α τ x (0 : TangentSpace I x),
      τ • (α (initPhase (I := I) x
        (τ⁻¹ • (0 : TangentSpace I x))) τ).2)).proj = x
  rw [hpair]
  simpa [z0, phaseZero] using congrArg Bundle.TotalSpace.proj hphase

/-- In the fixed base chart, the manifold endpoint has coordinate
`chartEnd` whenever the underlying model phase is in the fixed tangent-bundle
chart target. -/
theorem manifoldEnd_chart
    [I.Boundaryless]
    {α : E × E -> Real -> E × E} {τ : Real} (x : M)
    {v : TangentSpace I x}
    (htarget : α (initPhase (I := I) x (τ⁻¹ • v)) τ ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    extChartAt I x (manifoldEnd (I := I) α τ x v) =
      chartEnd (I := I) α τ x v := by
  let z : E × E := α (initPhase (I := I) x (τ⁻¹ • v)) τ
  let zβ : E × E := (z.1, τ • z.2)
  have hzβtarget :
      zβ ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target := by
    simpa [zβ] using
      phaseTarget_smul (I := I) x (z := z) (a := τ) (by simpa [z] using htarget)
  have hzβsrc :
      (phaseOfModel (I := I) x zβ).proj ∈ (extChartAt I x).source := by
    simpa [zβ] using
      phaseSrc_smul (I := I) x (z := z) (a := τ) (by simpa [z] using htarget)
  have hchart := phaseOfModel_chart (I := I) x hzβtarget hzβsrc
  simpa [manifoldEnd, chartEnd, z, zβ] using hchart

/-- Near zero, the manifold-valued functional endpoint has chart coordinate
`chartEnd`, provided the model flow stays in the fixed tangent-bundle chart
target. -/
theorem chartEnd_eventually_eq
    [I.Boundaryless]
    {α : E × E -> Real -> E × E} {ε τ ρ : Real} {rModel : NNReal}
    (x : M) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hsmall : ∀ v ∈ Metric.ball (0 : TangentSpace I x) ρ,
      initPhase (I := I) x v ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) rModel)
    (hsrc : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) rModel,
      ∀ t ∈ Set.Icc (-ε) ε,
        α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x (α z t)).proj ∈
            (extChartAt I x).source)
    (hτmem : τ ∈ Set.Icc (-ε) ε) :
    chartEnd (I := I) α τ x =ᶠ[𝓝 (0 : TangentSpace I x)]
      fun v : TangentSpace I x =>
        extChartAt I x (manifoldEnd (I := I) α τ x v) := by
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  have hball : Metric.ball (0 : TangentSpace I x) R ∈
      𝓝 (0 : TangentSpace I x) :=
    Metric.ball_mem_nhds _ hR
  filter_upwards [hball] with v hv
  let u : TangentSpace I x := τ⁻¹ • v
  let z : E × E := initPhase (I := I) x u
  have hu : u ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hv ⊢
    have hvnorm : ‖v‖ < τ * ρ := by
      simpa [R, dist_zero_right] using hv
    have hscale := mul_lt_mul_of_pos_left hvnorm (inv_pos.mpr hτ)
    have hnormu : ‖τ⁻¹ • v‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      rw [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul] at hscale
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscale
    simpa [u, dist_zero_right] using hnormu
  have hz : z ∈ Metric.closedBall
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) rModel := by
    exact hsmall u hu
  have htarget := (hsrc z hz τ hτmem).1
  have hchart := manifoldEnd_chart (I := I) (α := α) (τ := τ) x
    (v := v) htarget
  simpa [z, u] using hchart.symm

/-- First-coordinate Picard integral equation for the fixed chart endpoint. -/
theorem chartEnd_picard
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε τ : Real} (hε : 0 < ε) {r : NNReal}
    {α : E × E -> Real -> E × E}
    (hpicard : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t ∈ Set.Icc (-ε) ε,
        α z t =
          ODE.picard (fun _ : Real => modelSpray (I := I) g x)
            (⟨0, by simp [le_of_lt hε]⟩ :
              Set.Icc (0 - ε) (0 + ε)) z (α z) t)
    {v : TangentSpace I x}
    (hv : initPhase (I := I) x (τ⁻¹ • v) ∈
      Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r)
    (hτmem : τ ∈ Set.Icc (-ε) ε) :
    chartEnd (I := I) α τ x v =
      (initPhase (I := I) x (τ⁻¹ • v)).1 +
        (∫ s in (0 : Real)..τ,
          modelSpray (I := I) g x
            (α (initPhase (I := I) x (τ⁻¹ • v)) s)).1 := by
  let z : E × E := initPhase (I := I) x (τ⁻¹ • v)
  have hp := hpicard z (by simpa [z] using hv) τ hτmem
  have hpfst := congrArg Prod.fst hp
  simpa [chartEnd, z, ODE.picard_apply] using hpfst


end Coordinates
end RicciFlower
