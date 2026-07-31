import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDenseSolve

/-!
# Closed-form radii and horizon for the low-regularity Ricci--DeTurck solve

`lowreg_partial_sol` (`ShortTime/LowRegDenseSolve.lean`) produces the
order-one fixed-background Ricci--DeTurck solution, but every scalar it uses
is a witness of an existential: the coefficient radius, the state radius and
the existence time are all opaque.  This file re-runs that construction with
the six scalars that actually drive it supplied as hypotheses, so that the
exported existence time is a *closed formula* in those six numbers.

The six numbers are

* `Ctop` -- the top-arm coefficient of the outer tame estimate (upper bound);
* `B0` -- the fixed lower-order arm coefficient (upper bound);
* `B1` -- the high-size times lower-difference arm coefficient (upper bound);
* `D` -- the size of the nonlinearity at the zero state (upper bound);
* `ρ` -- the outer radius on which the tame estimate is valid (lower bound);
* `P` -- the radius on which the metric realization bound is valid
  (lower bound).

The three closed scalars are, in the order the original proof composes them,

```
lowregOuterRad Ctop ρ P     = min (ρ / 2) (min (P / 2) (1 / (32 * (Ctop + 1))))
lowregStateRad Ctop B1 ρ P  = min (lowregOuterRad Ctop ρ P / 2)
                                  (1 / (32 * (B1 + 1)))
lowregHorizon Ctop B0 B1 D ρ P =
  min 1 (min (1 / (64 * (B0 + 1) ^ 2))
             ((lowregStateRad Ctop B1 ρ P / 4 / (2 * (D + 1))) ^ 2))
```

The first cap freezes the coefficients so that the top arm contracts
(`Ctop * lowregOuterRad ≤ 1/16`), the second shrinks the solver state ball so
that the high-size arm contracts (`B1 * lowregStateRad ≤ 1/16`), and the third
is exactly `partial_sol_tame`'s horizon
`min 1 (min (1 / (64 * (B + 1) ^ 2)) (((R / 4) / (2 * (D + 1))) ^ 2))`
evaluated at `B = B0` and `R = lowregStateRad`.

All three are antitone in `Ctop`, `B0`, `B1`, `D` and monotone in `ρ` and `P`
(`lowregHorizon_mono`), so bounding the six numbers uniformly over a class of
metrics gives a uniform positive existence time.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

/-! ### The three closed scalars -/

/-- The outer coefficient-freezing radius.  It is capped by half the validity
radius `ρ` of the tame estimate, half the validity radius `P` of the metric
realization bound, and the top-arm contraction cap `1 / (32 * (Ctop + 1))`. -/
def lowregOuterRad (Ctop ρ P : ℝ) : ℝ :=
  min (ρ / 2) (min (P / 2) (1 / (32 * (Ctop + 1))))

/-- The solver state radius.  It is half the outer coefficient radius, capped
by the high-size arm contraction cap `1 / (32 * (B1 + 1))`. -/
def lowregStateRad (Ctop B1 ρ P : ℝ) : ℝ :=
  min (lowregOuterRad Ctop ρ P / 2) (1 / (32 * (B1 + 1)))

/-- The closed existence time of the order-one low-regularity Ricci--DeTurck
solve, as a function of the six numbers `Ctop, B0, B1, D, ρ, P`.  This is
`partial_sol_tame`'s horizon evaluated at the tame constant `B0` and the state
radius `lowregStateRad Ctop B1 ρ P`. -/
def lowregHorizon (Ctop B0 B1 D ρ P : ℝ) : ℝ :=
  min 1 (min (1 / (64 * (B0 + 1) ^ 2))
    ((lowregStateRad Ctop B1 ρ P / 4 / (2 * (D + 1))) ^ 2))

/-! ### Elementary bounds -/

theorem lowregOuterRad_le_rho {Ctop ρ P : ℝ} :
    lowregOuterRad Ctop ρ P ≤ ρ / 2 :=
  min_le_left _ _

theorem lowregOuterRad_le_P {Ctop ρ P : ℝ} :
    lowregOuterRad Ctop ρ P ≤ P / 2 :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem lowregOuterRad_le_cap {Ctop ρ P : ℝ} :
    lowregOuterRad Ctop ρ P ≤ 1 / (32 * (Ctop + 1)) :=
  le_trans (min_le_right _ _) (min_le_right _ _)

theorem lowregOuterRad_pos {Ctop ρ P : ℝ} (hCtop : 0 ≤ Ctop) (hρ : 0 < ρ)
    (hP : 0 < P) : 0 < lowregOuterRad Ctop ρ P := by
  refine lt_min (by linarith) (lt_min (by linarith) ?_)
  exact one_div_pos.mpr (by linarith)

/-- The top arm contracts on the outer coefficient radius. -/
theorem lowregOuterRad_small {Ctop ρ P : ℝ} (hCtop : 0 ≤ Ctop) :
    Ctop * lowregOuterRad Ctop ρ P ≤ 1 / 16 := by
  have hCtop1 : (0 : ℝ) < Ctop + 1 := by linarith
  calc
    Ctop * lowregOuterRad Ctop ρ P ≤ Ctop * (1 / (32 * (Ctop + 1))) :=
      mul_le_mul_of_nonneg_left lowregOuterRad_le_cap hCtop
    _ ≤ (Ctop + 1) * (1 / (32 * (Ctop + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 32 := by field_simp
    _ ≤ 1 / 16 := by norm_num

theorem lowregStateRad_le_Q {Ctop B1 ρ P : ℝ} :
    lowregStateRad Ctop B1 ρ P ≤ lowregOuterRad Ctop ρ P / 2 :=
  min_le_left _ _

theorem lowregStateRad_le_cap {Ctop B1 ρ P : ℝ} :
    lowregStateRad Ctop B1 ρ P ≤ 1 / (32 * (B1 + 1)) :=
  min_le_right _ _

theorem lowregStateRad_pos {Ctop B1 ρ P : ℝ} (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1)
    (hρ : 0 < ρ) (hP : 0 < P) : 0 < lowregStateRad Ctop B1 ρ P := by
  have hQ : 0 < lowregOuterRad Ctop ρ P := lowregOuterRad_pos hCtop hρ hP
  refine lt_min (by linarith) ?_
  exact one_div_pos.mpr (by linarith)

/-- The state radius is admissible for the metric realization bound. -/
theorem lowregStateRad_le_P {Ctop B1 ρ P : ℝ} (hP : 0 ≤ P) :
    lowregStateRad Ctop B1 ρ P ≤ P := by
  have h1 : lowregStateRad Ctop B1 ρ P ≤ lowregOuterRad Ctop ρ P / 2 :=
    lowregStateRad_le_Q
  have h2 : lowregOuterRad Ctop ρ P ≤ P / 2 := lowregOuterRad_le_P
  linarith

/-- The high-size arm contracts on the state radius. -/
theorem lowregStateRad_small {Ctop B1 ρ P : ℝ} (hB1 : 0 ≤ B1) :
    B1 * lowregStateRad Ctop B1 ρ P ≤ 1 / 16 := by
  have hB11 : (0 : ℝ) < B1 + 1 := by linarith
  calc
    B1 * lowregStateRad Ctop B1 ρ P ≤ B1 * (1 / (32 * (B1 + 1))) :=
      mul_le_mul_of_nonneg_left lowregStateRad_le_cap hB1
    _ ≤ (B1 + 1) * (1 / (32 * (B1 + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 32 := by field_simp
    _ ≤ 1 / 16 := by norm_num

theorem lowregHorizon_le_one {Ctop B0 B1 D ρ P : ℝ} :
    lowregHorizon Ctop B0 B1 D ρ P ≤ 1 :=
  min_le_left _ _

/-- The closed horizon is positive as soon as the six numbers have the
expected signs. -/
theorem lowregHorizon_pos {Ctop B0 B1 D ρ P : ℝ} (hCtop : 0 ≤ Ctop)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D) (hρ : 0 < ρ) (hP : 0 < P) :
    0 < lowregHorizon Ctop B0 B1 D ρ P := by
  have hB01 : (0 : ℝ) < B0 + 1 := by linarith
  have hR : 0 < lowregStateRad Ctop B1 ρ P := lowregStateRad_pos hCtop hB1 hρ hP
  refine lt_min one_pos (lt_min ?_ ?_)
  · exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hB01 2))
  · exact pow_pos (div_pos (by linarith) (by linarith)) 2

/-! ### Monotonicity in the six numbers

Primed inputs are the *worse* ones: larger coefficient bounds, smaller
validity radii.  They give a smaller horizon, so a class-uniform bound on the
six numbers yields a class-uniform positive existence time. -/

theorem lowregOuterRad_mono {Ctop Ctop' ρ ρ' P P' : ℝ} (hCtop : 0 ≤ Ctop)
    (hC : Ctop ≤ Ctop') (hρ : ρ' ≤ ρ) (hP : P' ≤ P) :
    lowregOuterRad Ctop' ρ' P' ≤ lowregOuterRad Ctop ρ P := by
  refine min_le_min (by linarith) (min_le_min (by linarith) ?_)
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem lowregStateRad_mono {Ctop Ctop' B1 B1' ρ ρ' P P' : ℝ} (hCtop : 0 ≤ Ctop)
    (hB1 : 0 ≤ B1) (hC : Ctop ≤ Ctop') (hB : B1 ≤ B1') (hρ : ρ' ≤ ρ)
    (hP : P' ≤ P) :
    lowregStateRad Ctop' B1' ρ' P' ≤ lowregStateRad Ctop B1 ρ P := by
  have hQ := lowregOuterRad_mono hCtop hC hρ hP
  refine min_le_min (by linarith) ?_
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem lowregHorizon_mono {Ctop Ctop' B0 B0' B1 B1' D D' ρ ρ' P P' : ℝ}
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D)
    (hRnn : 0 ≤ lowregStateRad Ctop' B1' ρ' P')
    (hC : Ctop ≤ Ctop') (hB0' : B0 ≤ B0') (hB1' : B1 ≤ B1') (hD' : D ≤ D')
    (hρ : ρ' ≤ ρ) (hP : P' ≤ P) :
    lowregHorizon Ctop' B0' B1' D' ρ' P' ≤ lowregHorizon Ctop B0 B1 D ρ P := by
  have hR := lowregStateRad_mono hCtop hB1 hC hB1' hρ hP
  refine min_le_min le_rfl (min_le_min ?_ ?_)
  · refine one_div_le_one_div_of_le ?_ ?_
    · nlinarith [sq_nonneg B0]
    · nlinarith [sq_nonneg B0, sq_nonneg B0']
  · have hq : lowregStateRad Ctop' B1' ρ' P' / 4 / (2 * (D' + 1)) ≤
        lowregStateRad Ctop B1 ρ P / 4 / (2 * (D + 1)) := by
      rw [div_eq_mul_one_div (lowregStateRad Ctop' B1' ρ' P' / 4),
        div_eq_mul_one_div (lowregStateRad Ctop B1 ρ P / 4)]
      refine mul_le_mul (by linarith)
        (one_div_le_one_div_of_le (by linarith) (by linarith)) ?_ (by linarith)
      exact (one_div_pos.mpr (by linarith)).le
    have hnn : 0 ≤ lowregStateRad Ctop' B1' ρ' P' / 4 / (2 * (D' + 1)) :=
      div_nonneg (by linarith) (by linarith)
    rw [pow_two, pow_two]
    exact mul_le_mul hq hq hnn (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The nonlinearity at the closed state radius -/

/-- A metric realization bound valid on the radius `P` restricts to the closed
state radius. -/
theorem lowregRealRad (g₀ : SmoothRiemannianMetric I M) {δ Ctop B1 ρ P : ℝ}
    (hP : 0 ≤ P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤
          lowregStateRad Ctop B1 ρ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ :=
  realizeOfLE (I := I) (M := M) g₀ (lowregStateRad_le_P hP) hreal

/-- The genuine lower-regularity Ricci--DeTurck nonlinearity on the state ball
of the closed radius `lowregStateRad Ctop B1 ρ P`. -/
def lowregNfun (g₀ g_bg : SmoothRiemannianMetric I M) {δ Ctop B1 ρ P : ℝ}
    (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P) →
      tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ) :=
  lowRegN (I := I) (M := M) g₀ g_bg (lowregStateRad_pos hCtop hB1 hρ hP) hδ
    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal)

/-! ### The six-number solve -/

/-- The six-number form of `lowreg_partial_sol`.

Given

* a metric realization bound valid on the radius `P`,
* continuity and the three-arm tame estimate for the nonlinearity on the
  closed state ball, with coefficients `Ctop * lowregOuterRad Ctop ρ P`, `B0`
  and `B1`,
* the bound `D` on the nonlinearity at the zero state,

the order-one fixed-background Ricci--DeTurck solve exists on every horizon
`T ≤ lowregHorizon Ctop B0 B1 D ρ P`, with forcing bounded by a quarter of the
closed state radius.  Both the state radius and the horizon are closed
formulas in the six numbers, so a class-uniform bound on the six numbers gives
a class-uniform existence time (`lowregHorizon_mono`, `lowregHorizon_pos`). -/
theorem lowreg_partial_sol_of_bounds (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcont : Continuous
      (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowregOuterRad Ctop ρ P *
            ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hzero : ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad_pos hCtop hB1 hρ hP).le⟩‖ ≤ D) :
    ∀ {T : ℝ} (hT : 0 < T)
      (_hTτ : T ≤ lowregHorizon Ctop B0 B1 D ρ P) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
        (gforce : timeL2
          (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
        let field := maxRegDuhamelSolField (I := I) (M := M)
          ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce
        u = maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ lowerState (I := I) (M := M) g₀ 1
              (lowregStateRad Ctop B1 ρ P)) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP
              hreal (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                (lowregStateRad_pos hCtop hB1 hρ hP).le) field t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ) field + gforce ∧
          ‖gforce‖ ≤ lowregStateRad Ctop B1 ρ P / 4 := by
  intro T hT hTτ hT1
  have hRpos : 0 < lowregStateRad Ctop B1 ρ P :=
    lowregStateRad_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowregOuterRad Ctop ρ P :=
    (lowregOuterRad_pos hCtop hρ hP).le
  let A : ℝ≥0 :=
    Real.toNNReal (Ctop * lowregOuterRad Ctop ρ P / lowregStateRad Ctop B1 ρ P)
  let B : ℝ≥0 := Real.toNNReal B0
  let C : ℝ≥0 := Real.toNNReal B1
  have hAarg : 0 ≤
      Ctop * lowregOuterRad Ctop ρ P / lowregStateRad Ctop B1 ρ P :=
    div_nonneg (mul_nonneg hCtop hQnn) hRpos.le
  have hAcoe : (A : ℝ) =
      Ctop * lowregOuterRad Ctop ρ P / lowregStateRad Ctop B1 ρ P :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = B0 := Real.coe_toNNReal _ hB0
  have hCcoe : (C : ℝ) = B1 := Real.coe_toNNReal _ hB1
  have hAR : (A : ℝ) * lowregStateRad Ctop B1 ρ P =
      Ctop * lowregOuterRad Ctop ρ P := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * lowregStateRad Ctop B1 ρ P ≤ 1 / 16 := by
    rw [hAR]
    exact lowregOuterRad_small hCtop
  have hsmallC : (C : ℝ) * lowregStateRad Ctop B1 ρ P ≤ 1 / 16 := by
    rw [hCcoe]
    exact lowregStateRad_small hB1
  have hsingle : ∀ u v : lowerState (I := I) (M := M) g₀ 1
      (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        (A : ℝ) * lowregStateRad Ctop B1 ρ P *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - (v : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (v : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (v : _))‖ := by
    intro u v
    rw [hAR, hBcoe, hCcoe]
    exact htame u v
  have hDnn : 0 ≤ D := le_trans (norm_nonneg _) hzero
  obtain ⟨T₀, hT₀eq, hT₀, hsol⟩ :=
    partial_sol_tame (I := I) (M := M) g₀ 1 hRpos
      (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal) hcont
      A B C D hDnn hzero hsmallA hsmallC hsingle
  have hτ : lowregHorizon Ctop B0 B1 D ρ P = T₀ := by
    rw [hT₀eq, hBcoe]
    rfl
  have hTT₀ : T ≤ T₀ := hTτ.trans hτ.le
  simpa only [Nat.cast_one] using hsol hT hTT₀ hT1

/-- Satisfiability of the six-number hypotheses.  For every metric the
existing per-metric producers supply constants `Ctop, B0, B1, D` and an outer
radius `ρ` for which the hypotheses of `lowreg_partial_sol_of_bounds` hold at
the given realization radius `P`, so that theorem recovers
`lowreg_partial_sol` with the horizon replaced by the closed formula.  Making
the horizon class-uniform is exactly the problem of bounding these five
numbers (and `P` from below) uniformly over a class of metrics. -/
theorem lowreg_bounds_exist (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ P : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ (Ctop B0 B1 D ρ : ℝ) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ),
      0 ≤ B0 ∧
      Continuous
        (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal) ∧
      (∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad Ctop B1 ρ P),
        ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
            lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowregOuterRad Ctop ρ P *
              ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖) ∧
      ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad_pos hCtop hB1 hρ hP).le⟩‖ ≤ D := by
  obtain ⟨ρ, Ctop, B0f, B1f, hρ, hCtop, hB0f, hB1f, houter⟩ :=
    lowRegN_outer (I := I) (M := M) hDim g₀ g_bg hδ0 hδ
  have hQpos : 0 < lowregOuterRad Ctop ρ P := lowregOuterRad_pos hCtop hρ hP
  have hB1Q : 0 ≤ B1f (lowregOuterRad Ctop ρ P) := hB1f _ hQpos.le
  have hRpos : 0 < lowregStateRad Ctop (B1f (lowregOuterRad Ctop ρ P)) ρ P :=
    lowregStateRad_pos hCtop hB1Q hρ hP
  have hQρ : lowregOuterRad Ctop ρ P ≤ ρ := by
    have := lowregOuterRad_le_rho (Ctop := Ctop) (ρ := ρ) (P := P)
    linarith
  have hRQ : lowregStateRad Ctop (B1f (lowregOuterRad Ctop ρ P)) ρ P ≤
      lowregOuterRad Ctop ρ P := by
    have := lowregStateRad_le_Q (Ctop := Ctop)
      (B1 := B1f (lowregOuterRad Ctop ρ P)) (ρ := ρ) (P := P)
    linarith
  have hrealQ : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤
          lowregOuterRad Ctop ρ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ := by
    refine realizeOfLE (I := I) (M := M) g₀ ?_ hreal
    have := lowregOuterRad_le_P (Ctop := Ctop) (ρ := ρ) (P := P)
    linarith
  obtain ⟨hcont0, _hcorecont0, hbound0⟩ :=
    houter hQpos.le hQρ hRpos hRQ hrealQ
  exact ⟨Ctop, B0f (lowregOuterRad Ctop ρ P),
    B1f (lowregOuterRad Ctop ρ P),
    ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1Q hρ hP hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩‖,
    ρ, hCtop, hB1Q, hρ, hB0f _ hQpos.le, hcont0, hbound0, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
