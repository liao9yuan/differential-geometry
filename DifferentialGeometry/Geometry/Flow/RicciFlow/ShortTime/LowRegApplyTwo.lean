import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegForceHi
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftHfLo
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftNTerm
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftSmall
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRealizeTwo
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds

/-!
# The adjacent-scale realization along the refolded low-regularity trajectory

This is the final-assembly junction of Lane C: it instantiates the abstract
adjacent-scale realization `lowreg_realize_two` at the concrete Sobolev pair
`(aLo, aHi) = (1, 2)` for the coefficient families that the refolded
low-regularity packet actually produces,

* second order: `lowAffA2Hi` / `lowAffA2` (from `lowA2Hi` / `lowA2Lo`, with the
  frozen radial passenger),
* first order: `refoldAffA1Hi` / `refoldAffA1` (from the trajectory-free affine
  packet `refold_aff`),
* forcing: `liftForceHi` / `liftForceLo`,

so that no hypothesis of the abstract lift is left as a parameter.  The two
commuting squares come from `lowAffA2_compat` and from the square exported by
`lowreg_hfLo_data`; the two contraction conditions come from `lift_small_aff`
on a single horizon.

The first-order sizes are certified in `L²_t`, never pointwise in time: maximal
regularity puts the order-one trajectory in `L²_t H³` and nothing more, so the
only honest first-order certificate is the affine bound of `memLp_clm_affine`,
`‖A1‖_{L²} ≤ 2L‖f‖ + √T·Z` (`norm_duhH3_le`).  The growth constants `Z, L` are
*parameters* of `lowreg_apply_two`, supplied by `refold_aff` before any
trajectory exists; that ordering is what lets the endpoint discharge the
smallness conditions itself.

`lowreg_solve_two` runs that instantiation along the *actual* trajectory: the
coefficient radius comes from `lowA2_small`, the metric realization radius from
`realize_at_thr`, and the trajectory from `lowreg_partial_sol_of_bounds` run at
a realization radius `P` capped by the coefficient radius *and* by
`(1-c)/(6(L+1))`.  The second cap makes the solver's own state radius small
enough that `‖f‖ ≤ P/4` meets the `T`-free margin `6·(2L‖f‖) < 1 - c`, and the
horizon condition `T ≤ lowregLiftHorizon' c Z` is folded into the reported
`T₀`.  So its hypotheses are only the dimension and the metric, and the caller
supplies just a contraction level `c` with `B2 ≤ c < 1` and a horizon below the
`T₀` reported for that `c`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The realized adjacent-scale package -/

/-- **The realized adjacent-scale `(1, 2)` package.**  For the forcing `f` on
the horizon `T` there is a `CrossScaleField` at scale `2` carrying its own
high-scale fixed-point equation for a refolded high first-order action,
vanishing initial trace, the clean tensor heat equation, and the carrier and
representative pins to the low-scale Duhamel solution driven by `f`.

Its high-scale **Nemytskii identity** at `aHi = 2` says that the high forcing is
the frozen split `liftHiN` (`ShortTime/LowRegForceHi.lean`) evaluated along the
`H⁴` field of the lift.  This is the honest `aHi = 2` form of `lowreg_force_id`;
no smooth representative of the trajectory is involved.

The package also re-exports the **producer certificates** that the fixed point
was built from — the low-scale radius `R` with its realization `hreal` and the
a.e. state-ball bound on the carrier, the two nonlinearity continuities
(`lowRegN`, `coreN`), the second-order continuities and smooth-core formula, the
completed first-order action `FLo` with its continuity and smooth-core formula,
and the two commuting squares.  Without them the package would determine no
smooth-state Nemytskii identity at all: `FHi` alone is an unconstrained
existential.  They are exactly what `lowreg_apply_two` already has in scope.

Its last conjunct is the **forcing floor** `√T · ‖fHi‖ ≤ Kf` at the caller's
level `Kf`.  It is the only conjunct that is not free of side conditions: the
producer must shrink the horizon to meet the requested `Kf` (`lowreg_apply_two`
does so through `lowregFloorHorizon`).  It is stated at a *parametric* level
rather than against a fixed constant so that the package stays independent of
the endpoint layer that eventually consumes it.

This is the conclusion of `lowreg_apply_two`, named so that the solved endpoint
`lowreg_solve_two` can state it without repeating the whole existential.  Apart
from the floor it carries no smallness side condition: the contraction level,
the margin and the horizon are hypotheses of the producers, not part of the
package. -/
def IsRealizedTwo
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
    (Kf : ℝ) : Prop :=
  ∃ (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
        (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
          tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (C2Hi : NNReal)
    (hA2Hi : AEStronglyMeasurable
      (lowAffA2Hi (I := I) (M := M) g
        hρ.le hδ0 hδ_le hreal' hT hT1 f) (timeMeasure T))
    (hC2Hi : ∀ᵐ t ∂timeMeasure T,
      ‖lowAffA2Hi (I := I) (M := M) g
        hρ.le hδ0 hδ_le hreal' hT hT1 f t‖ ≤ (C2Hi : ℝ))
    (hA1Hi : MemLp
      (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f) 2
        (timeMeasure T))
    (uHi : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (u : CrossScaleField (I := I) (M := M) g 0 2 (2 : ℝ) T)
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (R : ℝ) (hR : 0 < R)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ),
    u.lo = uHi ∧
      u.hiL2 =
        maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1 0 fHi ∧
      fHi =
        nonautL2Map (I := I) (M := M) hT hT1
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (lowAffA2Hi (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' hT hT1 f) hA2Hi C2Hi hC2Hi
            (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f)
            hA1Hi fHi +
          liftForceHi (I := I) (M := M) g g T ∧
      timeH1.trace0 _ T u.lo =
        (0 : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) ∧
      timeH1.timeDeriv _ T u.lo =
        timeScaleLaplacian (I := I) (M := M) (2 : ℝ) u.hiL2 + fHi ∧
      timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) fHi = f ∧
      (∀ᵐ t ∂timeMeasure T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = f t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (u.lo.toFun t) =
          (maxRegDuhamelMap (I := I) (M := M)
            (1 : ℝ) hT hT1 0 f).toFun t) ∧
      u.repr 0 =
        (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1)) ∧
      ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num) (u.repr t) =
          u.lo.toFun t) ∧
      ((fun t =>
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num) (u.repr t)) =ᵐ[
            timeMeasure T]
        fun t => maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1 0 f t) ∧
      ((fun t => fHi t) =ᵐ[timeMeasure T]
        fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (u.hiL2 t))) ∧
      R ≤ ρ ∧
      Continuous (lowRegN (I := I) (M := M) g g hR
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hreal) ∧
      Continuous (coreN (I := I) (M := M) g g
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hreal) ∧
      Continuous (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal') ∧
      (∀ S : SmoothCcTensor g 0 2,
        lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
            (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
          (refoldCore (I := I) (M := M) g
            hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M)) ∧
      Continuous (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal') ∧
      Continuous FHi ∧
      Continuous FLo ∧
      (∀ S : SmoothCcTensor g 0 2,
        FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
          (c0CoreData (I := I) (M := M)
              g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
            (oneCore (I := I) (M := M)
              g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M)) ∧
      (∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
            (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
          (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (3 : ℝ) ≤ 4 by norm_num))) ∧
      (∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
          (FLo x).comp
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num))) ∧
      (∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R) ∧
      Real.sqrt T * ‖fHi‖ ≤ Kf

/-! ## The Neumann bound for the high-scale forcing -/

/-- **The horizon on which the high forcing meets the floor `Kf`.**  On it the
frozen forcing `liftForceHi` — of size `‖staticForce g g 2‖·√T` — is small
enough that the Neumann bound of `norm_fix_le` at gap `(1-c)/4` gives
`√T·‖fHi‖ ≤ Kf`.  It is positive for every `0 < Kf` and `c < 1`, and involves
no coefficient constant of the lift. -/
def lowregFloorHorizon (g : SmoothRiemannianMetric I M) (c Kf : ℝ) : ℝ :=
  Kf * (1 - c) /
    (4 * (‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ + 1))

theorem lowregFloorHorizon_pos (g : SmoothRiemannianMetric I M) {c Kf : ℝ}
    (hKf : 0 < Kf) (hc1 : c < 1) :
    0 < lowregFloorHorizon (I := I) (M := M) g c Kf := by
  have hS : (0 : ℝ) ≤ ‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ :=
    norm_nonneg _
  exact div_pos (mul_pos hKf (by linarith)) (by linarith)

omit [BoundarylessManifold I M] in
/-- The non-autonomous forcing map fixes the origin: with zero initial datum
both of its arms vanish on the zero forcing.  (Canonical home:
`TensorMaximalRegularity/NonautonomousL2.lean`, beside `nonautL2_dist_le`; kept
here to leave that shared module untouched.) -/
private theorem nonautL2Map_zero {g : SmoothRiemannianMetric I M} {a T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (A2 : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 a)
    (hA1 : MemLp A1 2 (timeMeasure T)) :
    nonautL2Map (I := I) (M := M) hT hT1 h_compact A2 hA2 C2 hC2 A1 hA1 0 = 0 := by
  have hhom : maxRegHomogeneousSolField (I := I) (M := M) a T
      (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) = 0 := by
    refine norm_le_zero_iff.mp ?_
    simpa using maxRegHomogeneousSolField_norm_le (I := I) (M := M)
      (h_compact := h_compact) (a := a)
      (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) hT.le
  have hsol : maximalRegularitySolField (I := I) (M := M) a hT.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) = 0 := by
    refine norm_le_zero_iff.mp ?_
    simpa using maximalRegularitySolField_norm_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
  have hduh : maxRegDuhamelSolField (I := I) (M := M) a hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2))
      (0 : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) = 0 := by
    rw [maxRegDuhamelSolField, hhom, hsol, add_zero]
  have ha1 : a1L2Term (I := I) (M := M) hT hT1 h_compact A1 hA1 0 = 0 := by
    refine norm_le_zero_iff.mp ?_
    simpa using a1L2Term_norm (I := I) (M := M) hT hT1 h_compact A1 hA1 0
  simp only [nonautL2Map, hduh, ha1, map_zero, add_zero]

omit [BoundarylessManifold I M] in
/-- **The Neumann bound for the non-autonomous forcing fixed point.**  If the
Lipschitz constant of `nonautL2_dist_le` leaves the *uniform* gap `q`, then any
solution of the affine fixed-point equation `x = nonautL2Map … x + b` obeys
`q·‖x‖ ≤ ‖b‖`.  The strict contraction condition `… < 1` used to build the fixed
point is not enough: it yields no bound on `‖x‖` at all. -/
private theorem norm_fix_le {g : SmoothRiemannianMetric I M} {a T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (A2 : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 a)
    (hA2 : AEStronglyMeasurable A2 (timeMeasure T))
    (C2 : NNReal) (hC2 : ∀ᵐ t ∂timeMeasure T, ‖A2 t‖ ≤ (C2 : ℝ))
    (A1 : ℝ → tensorHs (I := I) (M := M) g 0 2 (a + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 a)
    (hA1 : MemLp A1 2 (timeMeasure T)) {q : ℝ}
    (hq : (C2 : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ ≤ 1 - q)
    (x b : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (hfix : x = nonautL2Map (I := I) (M := M) hT hT1 h_compact
      A2 hA2 C2 hC2 A1 hA1 x + b) :
    q * ‖x‖ ≤ ‖b‖ := by
  set κ : ℝ := (C2 : ℝ) * (1 + T) +
    2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ with hκ
  have hlip := nonautL2_dist_le (I := I) (M := M)
    hT hT1 h_compact A2 hA2 C2 hC2 A1 hA1 x 0
  rw [nonautL2Map_zero (I := I) (M := M) hT hT1 h_compact A2 hA2 C2 hC2 A1 hA1,
    dist_zero_right, dist_zero_right] at hlip
  have hx : ‖x‖ ≤ κ * ‖x‖ + ‖b‖ :=
    calc ‖x‖ = ‖nonautL2Map (I := I) (M := M) hT hT1 h_compact
                A2 hA2 C2 hC2 A1 hA1 x + b‖ := by rw [← hfix]
      _ ≤ ‖nonautL2Map (I := I) (M := M) hT hT1 h_compact
              A2 hA2 C2 hC2 A1 hA1 x‖ + ‖b‖ := norm_add_le _ _
      _ ≤ κ * ‖x‖ + ‖b‖ := by linarith
  have hgap : q * ‖x‖ ≤ (1 - κ) * ‖x‖ :=
    mul_le_mul_of_nonneg_right (by linarith only [hq]) (norm_nonneg x)
  linarith only [hx, hgap]

/-- **The adjacent-scale realization at `(aLo, aHi) = (1, 2)` along the
refolded low-regularity trajectory.**

The theorem *consumes* the trajectory-free affine packet of `refold_aff` at the
coefficient radius `ρ` — the two completed first-order actions `FHi`, `FLo`
with continuity, the low smooth-core formula, the growth constants `Z, L` and
the Sobolev-inclusion square — together with the second-order data at the same
radius (continuity, the uniform bounds `B2`, `B2Hi`, the low smooth-core
formula and the completed `H²`-state square) and a trajectory `f` in the
lower-state ball with the a.e. Nemytskii forcing identity.

The whole `lowreg_realize_two` package then exists as soon as a contraction
level `c < 1` dominates both second-order bounds with the `T`-free margin
`6·(2L‖f‖) ≤ (1-c)/2` and the horizon already lies below
`lowregLiftHorizon' c Z`.  Because `L` and `Z` arrive as parameters, a caller
can cap its state radius against `L` *before* producing `f`; that is what
`lowreg_solve_two` does.

The margin is stated with the halved, non-strict bound `(1-c)/2` rather than
`1 - c`: it is what the radius cap of `lowreg_solve_two` actually delivers, and
it leaves the *uniform* contraction gap `(1-c)/4` (`lift_aff_margin`) that the
Neumann bound `norm_fix_le` needs.  Together with `hTfloor` that is what makes
the package's forcing floor `√T·‖fHi‖ ≤ Kf` provable.

The first-order sizes are certified in `L²_t`, never pointwise in time: maximal
regularity puts the order-one trajectory in `L²_t H³` and nothing more, so the
only honest first-order certificate is the affine bound of `memLp_clm_affine`,
`‖A1‖_{L²} ≤ 2L‖f‖ + √T·Z` (`norm_duhH3_le`). -/
theorem lowreg_apply_two
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {R ρ δ T B2 B2Hi Z L c Kf : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g g hR hδ hreal))
    (hcoreN : Continuous (coreN (I := I) (M := M) g g hδ hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (hB2 : 0 ≤ B2)
    (hA2bd : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      ‖lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v‖ ≤ B2)
    (hA2Hicont : Continuous
      (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hB2Hi : 0 ≤ B2Hi)
    (hA2Hibd : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      ‖lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v‖ ≤ B2Hi)
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFHi : Continuous FHi) (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hFHiBd : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      ‖FHi x‖ ≤ Z + L * ‖x‖)
    (hFLoBd : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      ‖FLo x‖ ≤ Z + L * ‖x‖)
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      stateField (I := I) (M := M) g hT hT1 f t ∈
        lowerState (I := I) (M := M) g 1 R)
    (hforce : f =ᵐ[timeMeasure T] fun t =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g g hR hδ hreal
          (aeSetLift
            (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT hT1 f) t)))
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hB2c : B2 ≤ c) (hB2Hic : B2Hi ≤ c)
    (hmargin : 6 * (2 * L * ‖f‖) ≤ (1 - c) / 2)
    (hTle : T ≤ lowregLiftHorizon' c Z)
    (hTfloor : T ≤ lowregFloorHorizon (I := I) (M := M) g c Kf) :
    IsRealizedTwo (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Kf := by
  obtain ⟨C2, hA2, hC2, hA1, hA1Hi, hC2eq, hA1norm, hA1HiNorm,
      hA1compat, heq⟩ :=
    lowreg_hfLo_data (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδ
      hreal hreal' hNcont hcoreN hA2cont hA2core hB2 hA2bd hZ hL
      FHi FLo hFHi hFLo hFLoCore hFHiBd hFLoBd hFComm hT hT1 f hball hforce
  -- The `√T`-free part of both first-order sizes, through the core maximal
  -- regularity estimate `‖duhH3 f‖ ≤ (1 + T) ‖f‖ ≤ 2 ‖f‖`.
  have hduh : L * ‖duhH3 (I := I) (M := M) g hT hT1 f‖ ≤ 2 * L * ‖f‖ := by
    have h1 := mul_le_mul_of_nonneg_left
      (norm_duhH3_le (I := I) (M := M) g hT hT1 f) hL
    have h2 : (0 : ℝ) ≤ (1 - T) * (L * ‖f‖) :=
      mul_nonneg (by linarith) (mul_nonneg hL (norm_nonneg f))
    nlinarith
  obtain ⟨C2Hi, hC2Hieq, hA2Hi, hC2Hi⟩ :=
    lowAffA2Hi_data (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
      hA2Hicont hB2Hi hA2Hibd hT hT1 f
  have hnormHi : ‖hA1Hi.toLp
      (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f)‖ ≤
      2 * L * ‖f‖ + Real.sqrt T * Z := by linarith
  have hnormLo : ‖hA1.toLp
      (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f)‖ ≤
      2 * L * ‖f‖ + Real.sqrt T * Z := by linarith
  -- The high rung is certified with the *uniform* gap `(1-c)/4`; the Neumann
  -- bound on the fixed point needs it, and `hsmallHi` follows from it.
  have hmarginHi :
      (C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) *
          ‖hA1Hi.toLp (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f)‖ ≤
        1 - (1 - c) / 4 :=
    lift_aff_margin (A := 2 * L * ‖f‖) (Z := Z)
      hc0 hc1 hZ hmargin hT hTle
      (show (C2Hi : ℝ) ≤ c from hC2Hieq.trans_le hB2Hic)
      (norm_nonneg _) hnormHi
  have hsmallHi :
      (C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) *
          ‖hA1Hi.toLp (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f)‖ < 1 := by
    linarith only [hmarginHi, hc1]
  have hmarginLo : 6 * (2 * L * ‖f‖) < 1 - c := by linarith only [hmargin, hc1]
  have hsmallLo :=
    lift_small_aff
      (Y := tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))
      (A1 := refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) hA1
      (show (C2 : ℝ) ≤ c from hC2eq.trans_le hB2c)
      hc0 hc1 hZ hmarginLo hT hTle hnormLo
  obtain ⟨uHi, fHi, u, hpacket⟩ :=
    lowreg_realize_two (I := I) (M := M) (g := g)
      (aLo := (1 : ℝ)) (aHi := (2 : ℝ)) (T := T)
      (show (1 : ℝ) = (2 : ℝ) - 1 by norm_num)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (show (1 : ℝ) + 1 ≤ (2 : ℝ) + 1 by norm_num)
      (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 2 by norm_num)
      (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num)
      (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num)
      hT hT1
      (lowAffA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT hT1 f)
      hA2Hi C2Hi hC2Hi
      (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f) hA1Hi
      (liftForceHi (I := I) (M := M) g g T) hsmallHi
      (lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT hT1 f)
      hA2 C2 hC2
      (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) hA1
      (liftForceLo (I := I) (M := M) g g T) hsmallLo
      (Filter.Eventually.of_forall fun t =>
        lowAffA2_compat (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hA2sq
          hT hT1 f t)
      hA1compat (lift_force_incl (I := I) (M := M) g g T) f heq
  obtain ⟨hlo, hhi, hfHieq, htr, hpde, hL2incl, hincl, hlopin, hrepr0,
    hreprcont, hreprpin, hreprae⟩ := hpacket
  -- transitivity of the exponent transport
  have hctrans : ∀ {a b c : ℝ} (hab : a = b) (hbc : b = c)
      (x : tensorHs (I := I) (M := M) g 0 2 a),
      tensorHsCongr (I := I) (M := M) g 0 2 hbc
          (tensorHsCongr (I := I) (M := M) g 0 2 hab x) =
        tensorHsCongr (I := I) (M := M) g 0 2 (hab.trans hbc) x := by
    intro a b c hab hbc x
    cases hab
    cases hbc
    rfl
  have hstate := aeSetLift_coe_ae
    (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
    (stateField (I := I) (M := M) g hT hT1 f) hball
  have hsf : ∀ᵐ t ∂timeMeasure T,
      (stateField (I := I) (M := M) g hT hT1 f) t =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1 0 f t) := by
    filter_upwards [(tensorHsCongrL (I := I) (M := M) g 0 2
      (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f)] with t ht
    simpa only [tensorHsCongrL_apply] using ht
  -- the a.e. state-ball bound, read on the low carrier: the `H²` view of the
  -- `H³` representative is the `H²` view of the solver's state field
  have hballU : ∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R := by
    filter_upwards [hreprae, hsf, hball,
      ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hrae hsfa hbl htmem
    have hmem : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (stateField (I := I) (M := M) g hT hT1 f t)‖ ≤ R := hbl
    calc ‖u.lo.toFun t‖
        = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num) (u.repr t)‖ := by
          rw [hreprpin t htmem]
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num) (u.repr t))‖ := by
          rw [tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num)]
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1 0 f t)‖ := by
          rw [hrae]
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
            (tensorHsCongr (I := I) (M := M) g 0 2
              (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
              (maxRegDuhamelSolField (I := I) (M := M)
                (1 : ℝ) hT hT1 0 f t))‖ :=
          (norm_incl_congr (I := I) (M := M) g
            (show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num)
            (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
            (show (2 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num) _).symm
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
            (stateField (I := I) (M := M) g hT hT1 f t)‖ := by rw [hsfa]
      _ ≤ R := hmem
  -- The forcing floor: the Neumann bound at the uniform gap `(1-c)/4`, against
  -- the frozen forcing of size `‖staticForce g g 2‖·√T`.
  have hfloorHi : Real.sqrt T * ‖fHi‖ ≤ Kf := by
    have h1c : (0 : ℝ) < 1 - c := by linarith only [hc1]
    have hS : (0 : ℝ) ≤ ‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ :=
      norm_nonneg _
    have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
    have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
    have hneu := norm_fix_le (I := I) (M := M) (a := (2 : ℝ)) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      (lowAffA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT hT1 f)
      hA2Hi C2Hi hC2Hi
      (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f) hA1Hi
      hmarginHi fHi (liftForceHi (I := I) (M := M) g g T) hfHieq
    have hb : ‖liftForceHi (I := I) (M := M) g g T‖ ≤
        ‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ * Real.sqrt T :=
      norm_liftForceHi_le (I := I) (M := M) g g T le_rfl
    have hstep := mul_le_mul_of_nonneg_left (hneu.trans hb) hs0
    rw [show Real.sqrt T * (‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ *
          Real.sqrt T) =
        ‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ *
          (Real.sqrt T * Real.sqrt T) from by ring, hsT] at hstep
    -- `hstep : √T * ((1-c)/4 * ‖fHi‖) ≤ ‖SF‖ * T`
    have hden : (0 : ℝ) <
        4 * (‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ + 1) := by
      linarith only [hS]
    have hTf : T * (4 * (‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ + 1)) ≤
        Kf * (1 - c) := by
      unfold lowregFloorHorizon at hTfloor
      rwa [le_div_iff₀ hden] at hTfloor
    have hfinal : (1 - c) * (Real.sqrt T * ‖fHi‖) ≤ (1 - c) * Kf := by
      linarith only [hstep, hTf, hT.le]
    exact le_of_mul_le_mul_left hfinal h1c
  refine ⟨FHi, C2Hi, hA2Hi, hC2Hi, hA1Hi, uHi, fHi, u, FLo, R, hR, hreal,
    hlo, hhi, hfHieq, htr, hpde, hL2incl, hincl, hlopin, hrepr0, hreprcont,
    hreprpin, hreprae, ?_, hRρ, hNcont, hcoreN, hA2cont, hA2core, hA2Hicont,
    hFHi, hFLo, hFLoCore, hA2sq, hFComm, hballU, hfloorHi⟩
  -- the `H⁴` field of the lift is pinned to the low `H³` state
  have hpin : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (u.hiL2 t)) =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          ((aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT hT1 f) t).1) := by
    filter_upwards [u.link, hreprae, hstate, hsf,
      ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hlink hrae hst hsfa htmem
    -- the `H⁴` field really is the `H³` representative
    have h3 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) + 1 ≤ (2 : ℝ) + 2 by norm_num) (u.hiL2 t) =
        u.repr t := by
      apply tensorHsInclusion_injective (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num)
      rw [← tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ (2 : ℝ) + 1 by norm_num)
        (show (2 : ℝ) + 1 ≤ (2 : ℝ) + 2 by norm_num), hlink]
      exact (hreprpin t htmem).symm
    have hRHS : tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          ((aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT hT1 f) t).1) =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num) (u.repr t) := by
      rw [hst, hsfa, hctrans, ← hrae,
        tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num)
          (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num)
          (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 1 by norm_num)
          (show (3 : ℝ) ≤ (3 : ℝ) from le_rfl) (u.repr t)]
      exact tensorHsInclusion_refl_apply (I := I) (M := M) (g := g)
        (r := 0) (s := 2)
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num) (u.repr t))
    rw [← tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num)
        (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
        (show (2 : ℝ) + 1 ≤ (2 : ℝ) + 2 by norm_num)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num),
      h3, hRHS]
  filter_upwards [hincl, hforce, hpin] with t h1 h2 h3
  apply tensorHsInclusion_injective (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
  rw [h1, h2]
  exact hiN_lowreg (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδ
    hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
    hA2sq hFComm _ _ h3

omit [BoundarylessManifold I M] in
/-- The time-`L²` lift of an exponent transport along a reflexive equality of
exponents is the identity.  (Its canonical home is beside `tensorHsCongrL` in
`SobolevScale/ExponentCongr.lean`, which does not yet see the time-`L²`
layer.) -/
private theorem congrLp_self (g : SmoothRiemannianMetric I M) {a T : ℝ}
    (h : a = a) (u : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    (tensorHsCongrL (I := I) (M := M) g 0 2 h).compLpL 2 (timeMeasure T) u =
      u := by
  have hrfl : h = rfl := rfl
  rw [hrfl]
  apply MeasureTheory.Lp.ext
  filter_upwards [(tensorHsCongrL (I := I) (M := M) g 0 2
    (rfl : a = a)).coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht
  rw [ht, tensorHsCongrL_refl, ContinuousLinearMap.id_apply]

omit [BoundarylessManifold I M] in
/-- The affine Duhamel field with zero initial datum commutes with the
exponent transport of its forcing. -/
private theorem duhamel_congr (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (h : a = b) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    (tensorHsCongrL (I := I) (M := M) g 0 2
          (show b + 2 = a + 2 by rw [h])).compLpL 2 (timeMeasure T)
        (maxRegDuhamelSolField (I := I) (M := M) b hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (b + 2))
          ((tensorHsCongrL (I := I) (M := M) g 0 2 h).compLpL
            2 (timeMeasure T) u)) =
      maxRegDuhamelSolField (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) u := by
  cases h
  rw [congrLp_self, congrLp_self]

/-- The completed low second-order action depends on the low-base coefficient
bundle only through its top coefficient `C2`.  (Its canonical home is beside
`a2Lo_core` in `DeTurck/DeTurckRemainderLowBaseA2.lean`.) -/
private theorem a2Lo_congr (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {A B : LowBaseActionData g}
    (h : A.C2 = B.C2) :
    A.a2Lo (I := I) (M := M) = B.a2Lo (I := I) (M := M) := by
  have ha2 : ∀ W : SmoothCcTensor g 0 2,
      A.a2 (I := I) (M := M) W = B.a2 (I := I) (M := M) W := by
    intro W
    rw [LowBaseActionData.a2, LowBaseActionData.a2, h]
  refine ContinuousLinearMap.ext fun v => ?_
  refine (ccToHsLin_dense (I := I) (M := M) g 2
    (by norm_num : (0 : ℝ) ≤ (3 : ℝ))).induction_on v
      (isClosed_eq (A.a2Lo (I := I) (M := M)).continuous
        (B.a2Lo (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, a2Lo_core (I := I) (M := M) hDim g A W,
    a2Lo_core (I := I) (M := M) hDim g B W, ha2 W]

/-- **The realized `(1, 2)` cross-scale field along the low-regularity
Ricci--DeTurck trajectory.**

Every input of `lowreg_apply_two` is discharged here from its own producer: the
affine first-order packet from `refold_aff`, the metric realization radius from
`realize_at_thr`, the second-order coefficient data from `lowA2_small` and
`radialA2_lip`, the nonlinearity continuities from `lowRegN_outer`, and the
trajectory with its state ball and Nemytskii forcing identity from
`lowreg_partial_sol_of_bounds`.

Both smallness conditions of the lift are discharged internally.  The packet is
obtained *before* any trajectory exists, so its growth constant `L` is in scope
when the realization radius `P` is chosen; capping `P ≤ (1-c)/(6(L+1))` makes
the solver's own state radius small enough for the `T`-free margin
`6·(2L‖f‖) ≤ (1-c)/2`, since `‖f‖ ≤ P/4`.  The horizon conditions
`T ≤ lowregLiftHorizon' c Z` and `T ≤ lowregFloorHorizon g c Kf` are both folded
into the reported `T₀`.

The **forcing floor** `Kf` is a parameter: the caller names the level it needs
and the solver shrinks its horizon until the package meets it.  Keeping `Kf`
abstract is what stops this layer from depending on the endpoint constant that
eventually fixes it (`lowreg_joint_two` supplies `1/(4C)` for the fibre constant
`C` of `hs2_opBound_at_two`).

What the caller supplies is therefore only the floor `Kf`, the contraction level
`c` below `1` dominating the reported coefficient bound `B2`, and a horizon `T`
below the `T₀` reported for that pair. -/
theorem lowreg_solve_two
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {Kf : ℝ} (hKf : 0 < Kf) :
    ∃ (ρ δ : ℝ) (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
      (hreal' : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ)
      (B2 : ℝ), 0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (_ : T ≤ T₀) (hT1 : T ≤ 1),
            ∃ f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T,
              IsRealizedTwo (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Kf := by
  classical
  have hδ0 : 0 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) :=
    (deTurckArmContractionThreshold''_pos _).le
  have hδ_le : deTurckArmContractionThreshold'' (Module.finrank ℝ E) ≤ 1 / 3 :=
    deTurckArmContractionThreshold''_le_third' _
  have hδ : deTurckArmContractionThreshold'' (Module.finrank ℝ E) < 1 :=
    deTurckArmContractionThreshold''_lt_one' _
  obtain ⟨ρA, hρA, hpack⟩ := refold_aff (I := I) (M := M) hDim g
  obtain ⟨Pr, hPr, hrealPr⟩ := realize_at_thr (I := I) (M := M) hDim g
  obtain ⟨ρN, CtopN, B0N, B1N, hρN, -, -, -, houterN⟩ :=
    lowRegN_outer (I := I) (M := M) hDim g g hδ0 hδ
  have hcap : 0 < min ρA Pr := lt_min hρA hPr
  have hrealcap : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ min ρA Pr →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S)
          (deTurckArmContractionThreshold'' (Module.finrank ℝ E)) := by
    intro S hS
    refine hrealPr S ?_
    rw [norm_smoothCc_congr (I := I) (M := M) g
      (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S,
      smoothCcToTensorHs_eq_ccToHs]
    exact hS.trans (min_le_right _ _)
  obtain ⟨ρL, CL, hρL, hρL_le, hlip⟩ :=
    radialA2_lip (I := I) (M := M) hDim g hcap hδ0 hδ_le hrealcap
  have hrealL : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρL →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S)
          (deTurckArmContractionThreshold'' (Module.finrank ℝ E)) :=
    fun S hS => hrealcap S (hS.trans hρL_le)
  obtain ⟨ρ, C, hρ, hρ_le, hC, hA2small⟩ :=
    lowA2_small (I := I) (M := M) hDim g hρL hδ0 hδ_le hrealL
  have hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S)
          (deTurckArmContractionThreshold'' (Module.finrank ℝ E)) :=
    fun S hS => hrealL S (hS.trans hρ_le)
  obtain ⟨hA2Hicont, hA2cont, hA2Hibd, hA2bd, hA2sq⟩ := hA2small hρ.le hreal'
  obtain ⟨-, -, -, hcoreLo, -⟩ := hlip (r := ρ) hρ.le hρ_le
  have hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' S).a2Lo
          (I := I) (M := M) := by
    intro S
    refine (hcoreLo S).trans (a2Lo_congr (I := I) (M := M) hDim g ?_)
    rfl
  -- The affine packet, obtained BEFORE any trajectory: its growth constant `L`
  -- is what the realization radius is capped against below.
  obtain ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo, -, hFLoCore,
      hFHiBd, hFLoBd, hFComm⟩ :=
    hpack hρ (hρ_le.trans (hρL_le.trans (min_le_left _ _)))
      hδ0 hδ_le hreal'
  refine ⟨ρ, _, hρ, hδ0, hδ_le, hreal', C * ρ, mul_nonneg hC hρ.le, ?_⟩
  intro c hB2c hc1
  have hc0 : 0 ≤ c := (mul_nonneg hC hρ.le).trans hB2c
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hL1 : (0 : ℝ) < 6 * (L + 1) := by linarith
  set P : ℝ := min (min ρ ρN) ((1 - c) / (6 * (L + 1))) with hPdef
  have hPle1 : P ≤ min ρ ρN := min_le_left _ _
  have hPρ : P ≤ ρ := hPle1.trans (min_le_left _ _)
  have hPN : P ≤ ρN := hPle1.trans (min_le_right _ _)
  have hPc : P ≤ (1 - c) / (6 * (L + 1)) := min_le_right _ _
  have hPpos : 0 < P :=
    lt_min (lt_min hρ hρN) (div_pos h1c hL1)
  have hrealP := realizeOfLE (I := I) (M := M) g
    (show P ≤ Pr from
      hPρ.trans (hρ_le.trans (hρL_le.trans (min_le_right _ _)))) hrealPr
  obtain ⟨Ctop, B0, B1, D, ρout, hCtop, hB1, hρout, hB0, hcont, htame,
      hzero⟩ :=
    lowreg_bounds_exist (I := I) (M := M) hDim g g hδ0 hδ hPpos hrealP
  have hD : 0 ≤ D := (norm_nonneg _).trans hzero
  have hR : 0 < lowregStateRad Ctop B1 ρout P :=
    lowregStateRad_pos hCtop hB1 hρout hPpos
  have hRP : lowregStateRad Ctop B1 ρout P ≤ P :=
    lowregStateRad_le_P hPpos.le
  have hrealR := lowregRealRad (I := I) (M := M) g
    (Ctop := Ctop) (B1 := B1) (ρ := ρout) hPpos.le hrealP
  obtain ⟨-, hcoreN, -⟩ := houterN hR.le (hRP.trans hPN) hR le_rfl hrealR
  refine ⟨min (min (lowregHorizon Ctop B0 B1 D ρout P)
        (lowregLiftHorizon' c Z))
      (lowregFloorHorizon (I := I) (M := M) g c Kf),
    lt_min
      (lt_min (lowregHorizon_pos hCtop hB0 hB1 hD hρout hPpos)
        (lowregLiftHorizon'_pos hc0 hc1 hZ))
      (lowregFloorHorizon_pos (I := I) (M := M) g hKf hc1), ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨-, gforce, -, hball, hforce, -, -, hgf⟩ :=
    lowreg_partial_sol_of_bounds (I := I) (M := M) g g hδ hCtop hB0 hB1 hρout
      hPpos hrealP hcont htame hzero hT
      (hTT₀.trans ((min_le_left _ _).trans (min_le_left _ _))) hT1
  set f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T :=
    (tensorHsCongrL (I := I) (M := M) g 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).compLpL 2 (timeMeasure T)
      gforce with hfdef
  refine ⟨f, ?_⟩
  have hstate : stateField (I := I) (M := M) g hT hT1 f =
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) gforce := by
    rw [hfdef]
    exact duhamel_congr (I := I) (M := M) g
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) hT hT1 gforce
  have hfae : ∀ᵐ t ∂timeMeasure T,
      f t = tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (gforce t) := by
    rw [hfdef]
    exact (tensorHsCongrL (I := I) (M := M) g 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) gforce
  have hball' : ∀ᵐ t ∂timeMeasure T,
      stateField (I := I) (M := M) g hT hT1 f t ∈
        lowerState (I := I) (M := M) g 1
          (lowregStateRad Ctop B1 ρout P) := by
    rw [hstate]
    exact hball
  have hforce' : f =ᵐ[timeMeasure T] fun t =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g g hR hδ hrealR
          (aeSetLift
            (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT hT1 f) t)) := by
    rw [hstate]
    filter_upwards [hfae, hforce] with t h1 h2
    rw [h1, h2]
    rfl
  -- The margin, discharged by the radius cap: `‖f‖ = ‖gforce‖ ≤ R/4 ≤ P/4`
  -- and `3 L P < 1 - c` by the third component of `P`.
  have hfnorm : ‖f‖ = ‖gforce‖ := by
    rw [hfdef]
    exact norm_congrLp (I := I) (M := M) g
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) gforce
  have hfP : ‖f‖ ≤ P / 4 := by
    rw [hfnorm]
    refine hgf.trans ?_
    linarith
  have hkey : P * (6 * (L + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ hL1]
    exact hPc
  have hmargin : 6 * (2 * L * ‖f‖) ≤ (1 - c) / 2 := by
    have h1 : 12 * L * ‖f‖ ≤ 12 * L * (P / 4) :=
      mul_le_mul_of_nonneg_left hfP (by linarith : (0 : ℝ) ≤ 12 * L)
    linarith only [h1, hkey, hPpos]
  exact lowreg_apply_two (I := I) (M := M) hDim g hR hρ (hRP.trans hPρ)
    hδ0 hδ_le hδ hrealR hreal' hcont hcoreN hA2cont hA2core
    (mul_nonneg hC hρ.le) hA2bd hA2Hicont (mul_nonneg hC hρ.le) hA2Hibd hA2sq
    hZ hL FHi FLo hFHi hFLo hFLoCore hFHiBd hFLoBd hFComm
    hT hT1 f hball' hforce' hc0 hc1 hB2c hB2c hmargin
    (hTT₀.trans ((min_le_left _ _).trans (min_le_right _ _)))
    (hTT₀.trans (min_le_right _ _))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
