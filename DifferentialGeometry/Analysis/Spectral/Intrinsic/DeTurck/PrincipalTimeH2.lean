import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocalNemytskii
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalLowRegH2

/-!
# Time-dependent low-regularity DeTurck principal operators

This file restricts the low-regularity Ricci--DeTurck principal operator to a
small spectral `H2` metric ball and evaluates it on almost-everywhere
ball-valued time fields.  The resulting operator family is strongly measurable
and uniformly small as an `H4 -> H2` operator family.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank2H4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev rank2H2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

/-- The closed spectral `H2` ball on which the principal coefficient is
uniformly controlled. -/
def principalBall (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    Set (metricH2 (I := I) (M := M) g) :=
  {T | ‖T‖ ≤ ρ}

omit [BoundarylessManifold I M] in
/-- The zero metric deviation belongs to every nonnegative principal ball. -/
theorem principalBall_zero (g : SmoothRiemannianMetric I M)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : metricH2 (I := I) (M := M) g) ∈
      principalBall (I := I) (M := M) g ρ := by
  simpa only [principalBall, Set.mem_setOf_eq, norm_zero] using hρ

/-- The low-regularity principal coefficient restricted to its controlled
spectral `H2` ball. -/
def principalOnBall (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    principalBall (I := I) (M := M) g ρ →
      (rank2H4 (I := I) (M := M) g →L[ℝ]
        rank2H2 (I := I) (M := M) g) :=
  fun T => lowRegPrincipal (I := I) (M := M) g T.1

/-- In dimension three, one small spectral `H2` ball carries both a Lipschitz
principal coefficient and a uniform bound linear in the ball radius. -/
theorem principalBall_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ (ρ : ℝ) (C : NNReal), 0 < ρ ∧
      (∀ T U : principalBall (I := I) (M := M) g ρ,
        ‖principalOnBall (I := I) (M := M) g ρ T -
            principalOnBall (I := I) (M := M) g ρ U‖ ≤
          (C : ℝ) *
            ‖(T : metricH2 (I := I) (M := M) g) - (U : metricH2 (I := I) (M := M) g)‖) ∧
      ∀ T : principalBall (I := I) (M := M) g ρ,
        ‖principalOnBall (I := I) (M := M) g ρ T‖ ≤
          (C : ℝ) * ‖(T : metricH2 (I := I) (M := M) g)‖ := by
  obtain ⟨ρn, Cn, hρn, hCn, hn⟩ :=
    lowRegPrincipal_norm (I := I) (M := M) hDim g
  obtain ⟨ρl, Cl, hρl, hCl, hl⟩ :=
    lowRegPrincipal_lip (I := I) (M := M) hDim g
  let ρ : ℝ := min ρn ρl
  let C : NNReal := ⟨max Cn Cl, hCn.trans (le_max_left Cn Cl)⟩
  have hρ : 0 < ρ := lt_min hρn hρl
  refine ⟨ρ, C, hρ, ?_, ?_⟩
  · intro T U
    have hTρ : ‖(T : metricH2 (I := I) (M := M) g)‖ ≤ ρ := T.property
    have hUρ : ‖(U : metricH2 (I := I) (M := M) g)‖ ≤ ρ := U.property
    have hT : ‖(T : metricH2 (I := I) (M := M) g)‖ ≤ ρl :=
      hTρ.trans (min_le_right ρn ρl)
    have hU : ‖(U : metricH2 (I := I) (M := M) g)‖ ≤ ρl :=
      hUρ.trans (min_le_right ρn ρl)
    have hLip := hl T.1 U.1 hT hU
    calc
      ‖principalOnBall (I := I) (M := M) g ρ T -
          principalOnBall (I := I) (M := M) g ρ U‖ =
          ‖lowRegPrincipal (I := I) (M := M) g T.1 -
            lowRegPrincipal (I := I) (M := M) g U.1‖ := rfl
      _ ≤ Cl * ‖T.1 - U.1‖ := hLip
      _ ≤ max Cn Cl * ‖T.1 - U.1‖ :=
        mul_le_mul_of_nonneg_right (le_max_right Cn Cl) (norm_nonneg _)
      _ = (C : ℝ) * ‖T.1 - U.1‖ := rfl
  · intro T
    have hTρ : ‖(T : metricH2 (I := I) (M := M) g)‖ ≤ ρ := T.property
    have hT : ‖(T : metricH2 (I := I) (M := M) g)‖ ≤ ρn :=
      hTρ.trans (min_le_left ρn ρl)
    calc
      ‖principalOnBall (I := I) (M := M) g ρ T‖ =
          ‖lowRegPrincipal (I := I) (M := M) g T.1‖ := rfl
      _ ≤ Cn * ‖T.1‖ := hn T.1 hT
      _ ≤ max Cn Cl * ‖(T : metricH2 (I := I) (M := M) g)‖ :=
        mul_le_mul_of_nonneg_right (le_max_left Cn Cl) (norm_nonneg _)
      _ = (C : ℝ) * ‖(T : metricH2 (I := I) (M := M) g)‖ := rfl

/-- An operator-norm Lipschitz bound on a principal ball gives continuity for
the canonical continuous-linear-map topology. -/
theorem principalOnBall_cont
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} {C : NNReal}
    (hL : ∀ T U : principalBall (I := I) (M := M) g ρ,
      ‖principalOnBall (I := I) (M := M) g ρ T -
          principalOnBall (I := I) (M := M) g ρ U‖ ≤
        (C : ℝ) *
          ‖(T : metricH2 (I := I) (M := M) g) -
            (U : metricH2 (I := I) (M := M) g)‖) :
    Continuous (principalOnBall (I := I) (M := M) g ρ) := by
  rw [continuous_iff_continuousAt]
  intro T
  have hsub :
      Tendsto
        (fun U : principalBall (I := I) (M := M) g ρ =>
          ‖(U : metricH2 (I := I) (M := M) g) -
            (T : metricH2 (I := I) (M := M) g)‖)
        (𝓝 T) (𝓝 0) := by
    have hcont : Continuous
        (fun U : principalBall (I := I) (M := M) g ρ =>
          ‖(U : metricH2 (I := I) (M := M) g) -
            (T : metricH2 (I := I) (M := M) g)‖) :=
      (continuous_subtype_val.sub
        (continuous_const :
          Continuous
            (fun _ : principalBall (I := I) (M := M) g ρ =>
              (T : metricH2 (I := I) (M := M) g)))).norm
    have ht :
        Tendsto
          (fun U : principalBall (I := I) (M := M) g ρ =>
            ‖(U : metricH2 (I := I) (M := M) g) -
              (T : metricH2 (I := I) (M := M) g)‖)
          (𝓝 T)
          (𝓝 ‖(T : metricH2 (I := I) (M := M) g) -
            (T : metricH2 (I := I) (M := M) g)‖) :=
      hcont.continuousAt
    simpa only [sub_self, norm_zero] using ht
  have hdiff :
      Tendsto
        (fun U : principalBall (I := I) (M := M) g ρ =>
          principalOnBall (I := I) (M := M) g ρ U -
            principalOnBall (I := I) (M := M) g ρ T)
        (𝓝 T) (𝓝 0) := by
    refine (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (E := rank2H4 (I := I) (M := M) g)
      (F := rank2H2 (I := I) (M := M) g)
      Metric.nhds_basis_closedBall).tendsto_right_iff.mpr ?_
    rintro ⟨S, ε⟩ ⟨hS, hε⟩
    obtain ⟨r, hr⟩ :=
      (NormedSpace.isVonNBounded_iff'
        (E := rank2H4 (I := I) (M := M) g) ℝ).mp hS
    let B : ℝ := max r 0
    let D : ℝ := (C : ℝ) * B + 1
    have hB : 0 ≤ B := le_max_right r 0
    have hD : 0 < D := by
      dsimp only [D]
      positivity
    have hnear :=
      hsub.eventually_lt_const (div_pos hε hD)
    filter_upwards [hnear] with U hU
    intro x hx
    have hxB : ‖x‖ ≤ B :=
      (hr x hx).trans (le_max_left r 0)
    have hop :
        ‖(principalOnBall (I := I) (M := M) g ρ U -
            principalOnBall (I := I) (M := M) g ρ T) x‖ ≤
          ((C : ℝ) *
              ‖(U : metricH2 (I := I) (M := M) g) -
                (T : metricH2 (I := I) (M := M) g)‖) * B := by
      exact
        ((principalOnBall (I := I) (M := M) g ρ U -
          principalOnBall (I := I) (M := M) g ρ T).le_opNorm x).trans
          (mul_le_mul (hL U T) hxB (norm_nonneg _)
            (mul_nonneg C.coe_nonneg (norm_nonneg _)))
    have hstrict :
        ((C : ℝ) *
            ‖(U : metricH2 (I := I) (M := M) g) -
              (T : metricH2 (I := I) (M := M) g)‖) * B < ε := by
      calc
        _ = ((C : ℝ) * B) *
            ‖(U : metricH2 (I := I) (M := M) g) -
              (T : metricH2 (I := I) (M := M) g)‖ := by ring
        _ ≤ D *
            ‖(U : metricH2 (I := I) (M := M) g) -
              (T : metricH2 (I := I) (M := M) g)‖ := by
          apply mul_le_mul_of_nonneg_right
          · dsimp only [D]
            linarith
          · exact norm_nonneg _
        _ < D * (ε / D) := mul_lt_mul_of_pos_left hU hD
        _ = ε := by field_simp [ne_of_gt hD]
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hop.trans hstrict.le
  have hto := hdiff.add_const
    (principalOnBall (I := I) (M := M) g ρ T)
  simpa only [sub_add_cancel, zero_add] using hto

/-- The principal operator family obtained from the canonical
almost-everywhere lift of an `H2` time field into a principal ball. -/
def principalTime (g : SmoothRiemannianMetric I M) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {T : ℝ}
    (f : timeL2 (metricH2 (I := I) (M := M) g) T) :
    ℝ → (rank2H4 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g) :=
  fun t => principalOnBall (I := I) (M := M) g ρ
    (aeSetLift (principalBall_zero (I := I) (M := M) g hρ) f t)

/-- A Lipschitz principal coefficient produces a strongly measurable operator
family along every almost-everywhere ball-valued `H2` time field. -/
theorem principalTime_aesm
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {C : NNReal}
    (hL : ∀ U V : principalBall (I := I) (M := M) g ρ,
      ‖principalOnBall (I := I) (M := M) g ρ U -
          principalOnBall (I := I) (M := M) g ρ V‖ ≤
        (C : ℝ) *
          ‖(U : metricH2 (I := I) (M := M) g) -
            (V : metricH2 (I := I) (M := M) g)‖)
    {T : ℝ} (f : timeL2 (metricH2 (I := I) (M := M) g) T)
    (hf : ∀ᵐ t ∂timeMeasure T, ‖f t‖ ≤ ρ) :
    AEStronglyMeasurable
      (principalTime (I := I) (M := M) g hρ f) (timeMeasure T) := by
  have hf' :
      ∀ᵐ t ∂timeMeasure T,
        f t ∈ principalBall (I := I) (M := M) g ρ := by
    simpa only [principalBall, Set.mem_setOf_eq] using hf
  exact (principalOnBall_cont (I := I) (M := M) g hL).comp_aestronglyMeasurable
    (aeSetLift_aesm
      (principalBall_zero (I := I) (M := M) g hρ) f hf')

/-- On the almost-everywhere state ball, the lifted principal family agrees
with direct evaluation of the low-regularity principal coefficient. -/
theorem principalTime_ae
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {T : ℝ} (f : timeL2 (metricH2 (I := I) (M := M) g) T)
    (hf : ∀ᵐ t ∂timeMeasure T, ‖f t‖ ≤ ρ) :
    principalTime (I := I) (M := M) g hρ f =ᵐ[timeMeasure T]
      fun t => lowRegPrincipal (I := I) (M := M) g (f t) := by
  filter_upwards [hf] with t ht
  have hmem :
      f t ∈ principalBall (I := I) (M := M) g ρ := by
    simpa only [principalBall, Set.mem_setOf_eq] using ht
  simp only [principalTime, principalOnBall, aeSetLift, dif_pos hmem]

/-- The spatial principal-ball bound gives the required almost-everywhere
uniform operator bound for the time-dependent family. -/
theorem principalTime_ae_le
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {C : NNReal}
    (hbound : ∀ U : principalBall (I := I) (M := M) g ρ,
      ‖principalOnBall (I := I) (M := M) g ρ U‖ ≤
        (C : ℝ) * ‖(U : metricH2 (I := I) (M := M) g)‖)
    {T : ℝ} (f : timeL2 (metricH2 (I := I) (M := M) g) T) :
    ∀ᵐ t ∂timeMeasure T,
      ‖principalTime (I := I) (M := M) g hρ f t‖ ≤ (C : ℝ) * ρ := by
  refine Eventually.of_forall fun t => ?_
  let U := aeSetLift
    (principalBall_zero (I := I) (M := M) g hρ) f t
  exact (hbound U).trans
    (mul_le_mul_of_nonneg_left U.property C.coe_nonneg)

/-- The complete dimension-three time-family producer: one positive radius
controls every smaller state radius, every time horizon, and every
almost-everywhere ball-valued `H2` metric path. -/
theorem principalTime_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ (ρ : ℝ) (C : NNReal), 0 < ρ ∧
      ∀ {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (f : timeL2 (metricH2 (I := I) (M := M) g) T),
        (∀ᵐ t ∂timeMeasure T, ‖f t‖ ≤ R) →
          AEStronglyMeasurable
              (principalTime (I := I) (M := M) g hR f)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖principalTime (I := I) (M := M) g hR f t‖ ≤
                (C : ℝ) * R) ∧
            principalTime (I := I) (M := M) g hR f
              =ᵐ[timeMeasure T]
                fun t => lowRegPrincipal (I := I) (M := M) g (f t) := by
  obtain ⟨ρ, C, hρ, hLip, hbound⟩ :=
    principalBall_data (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, ?_⟩
  intro R hR hRρ T f hf
  have hLipR :
      ∀ U V : principalBall (I := I) (M := M) g R,
        ‖principalOnBall (I := I) (M := M) g R U -
            principalOnBall (I := I) (M := M) g R V‖ ≤
          (C : ℝ) *
            ‖(U : metricH2 (I := I) (M := M) g) -
              (V : metricH2 (I := I) (M := M) g)‖ := by
    intro U V
    let Uρ : principalBall (I := I) (M := M) g ρ :=
      ⟨U, U.property.trans hRρ⟩
    let Vρ : principalBall (I := I) (M := M) g ρ :=
      ⟨V, V.property.trans hRρ⟩
    simpa only [principalOnBall, Uρ, Vρ] using hLip Uρ Vρ
  have hboundR :
      ∀ U : principalBall (I := I) (M := M) g R,
        ‖principalOnBall (I := I) (M := M) g R U‖ ≤
          (C : ℝ) * ‖(U : metricH2 (I := I) (M := M) g)‖ := by
    intro U
    let Uρ : principalBall (I := I) (M := M) g ρ :=
      ⟨U, U.property.trans hRρ⟩
    simpa only [principalOnBall, Uρ] using hbound Uρ
  exact ⟨principalTime_aesm (I := I) (M := M) g hR hLipR f hf,
    principalTime_ae_le (I := I) (M := M) g hR hboundR f,
    principalTime_ae (I := I) (M := M) g hR f hf⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
