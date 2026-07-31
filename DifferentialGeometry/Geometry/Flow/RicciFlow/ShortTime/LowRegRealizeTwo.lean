import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftTwo
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRHSSymm
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Realize
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LowRegOperatorTime

/-!
# Realization of the adjacent-scale lift, and the Ricci--DeTurck forcing identity

Bricks C2 and C3 of the low-regularity Ricci--DeTurck bootstrap.

* `lowreg_realize_two` turns the six `L2`-class conclusions of `lowreg_lift_two`
  into one intrinsic `CrossScaleField` on the *unchanged* horizon, with zero
  trace, the clean tensor heat equation, and the pinned intermediate
  representative.  It is a pure composition: every hypothesis is the one
  `lowreg_lift_two` already asks for, and no new frontier is introduced.
* `lowRadial_eq_self_sol` discharges the spectral-symmetry input of
  `lowRadial_eq_self_along_sol` from `lowreg_sol_symm_h3`, so that along the
  order-one solution the *frozen radial* low-base coefficients are the genuine
  coefficients.  Its only remaining inputs are exported by `lowreg_partial_sol`.
* `lowreg_force_lo` is the unconditional half of the forcing identity: the
  lifted forcing, read at the lower scale, is the genuine low-regularity
  Ricci--DeTurck nonlinearity `lowRegN` at the genuine states.
* `lowreg_force_id` upgrades that to the high scale.  Because the scale
  inclusion is injective, *any* higher-order lift `N2` of `lowRegN` is hit
  exactly: `fHi =ᵐ N2 ∘ state`.  The residual frontier is therefore precisely
  the construction of `N2` -- an `H^σ`-valued Nemytskii map with
  `tensorHsInclusion ∘ N2 = lowRegN` -- and nothing else.
* `coreNAt` / `coreNAt_incl` exhibit that lift on the dense smooth core:
  `deTurckSmoothN` has order-independent spectral coordinates, so raising its
  order and including back is the identity.  What is missing for the full `N2`
  is only the completed (dense-extension) version of this map, i.e. an
  `H^σ`-valued tame estimate for the low-base nonlinearity.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Exponent normalization of a coefficient family

The Time-layer low-base families sit at *literal* Sobolev orders
(`H4 →L H2`, `H3 →L H2`), while the lift indexes their domains arithmetically
(`H^(aHi+2)`, `H^(aHi+1)`).  Precomposition with `tensorHsCongrL` moves them,
and — because the transport is the identity after `cases` on the exponent
equality — strong measurability, uniform operator bounds and time-`L²`
membership all survive unchanged. -/

omit [BoundarylessManifold I M] in
/-- Normalizing the domain exponent of an operator family preserves strong
measurability. -/
theorem congrOp_aemeas {g : SmoothRiemannianMetric I M} {p q b T : ℝ}
    (hpq : p = q)
    (A : ℝ → tensorHs (I := I) (M := M) g 0 2 q →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 b)
    (hA : AEStronglyMeasurable A (timeMeasure T)) :
    AEStronglyMeasurable
      (fun t => (A t).comp (tensorHsCongrL (I := I) (M := M) g 0 2 hpq))
      (timeMeasure T) := by
  cases hpq
  simpa only [tensorHsCongrL_refl, ContinuousLinearMap.comp_id] using hA

omit [BoundarylessManifold I M] in
/-- Normalizing the domain exponent of an operator family preserves time-`L²`
membership -- the `hA1 : MemLp A1 2` input of the non-autonomous fixed
point. -/
theorem congrOp_memLp {g : SmoothRiemannianMetric I M} {p q b T : ℝ}
    (hpq : p = q)
    (A : ℝ → tensorHs (I := I) (M := M) g 0 2 q →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 b)
    (hA : MemLp A 2 (timeMeasure T)) :
    MemLp (fun t => (A t).comp (tensorHsCongrL (I := I) (M := M) g 0 2 hpq)) 2
      (timeMeasure T) := by
  cases hpq
  simpa only [tensorHsCongrL_refl, ContinuousLinearMap.comp_id] using hA

omit [BoundarylessManifold I M] in
/-- Normalizing the domain exponent of an operator family preserves every
uniform operator bound. -/
theorem congrOp_norm_le {g : SmoothRiemannianMetric I M} {p q b T C : ℝ}
    (hpq : p = q)
    (A : ℝ → tensorHs (I := I) (M := M) g 0 2 q →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 b)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C) :
    ∀ᵐ t ∂timeMeasure T,
      ‖(A t).comp (tensorHsCongrL (I := I) (M := M) g 0 2 hpq)‖ ≤ C := by
  filter_upwards [hC] with t ht
  exact (opNorm_comp_congr_le (I := I) (M := M) hpq (A t)).trans ht

/-! ## The two Lane-B coefficient families at the lift's exponents -/

/-- The complete second-order low-base family along the order-one solution,
with its domain normalized from the literal `H4` to the `H^(aHi+2)` demanded by
the lift at `aHi = 2`. -/
def liftA2Two (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t =>
    (lowRegA2Total (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f hR hball
      t).comp
      (tensorHsCongrL (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num))

/-- The `A2` input packet of `lowreg_lift_two` at `aHi = 2`: strong
measurability and the uniform smallness of the *complete* second-order family,
consumed unconditionally from `lowRegA2Total_data`. -/
theorem liftA2Two_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
          (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2))
                f t)‖ ≤ R),
          AEStronglyMeasurable
              (liftA2Two (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' hT hT1 f hR
                hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖liftA2Two (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' hT hT1 f hR
                hball t‖ ≤ C * ρ) := by
  obtain ⟨ρ, C, hρ, hρle, hC, hdata⟩ :=
    lowRegA2Total_data (I := I) (M := M) hDim g hρ₀ hδ0 hδ_le hreal
  refine ⟨ρ, C, hρ, hρle, hC, ?_⟩
  intro hρ0 hreal' R hR hRρ T hT hT1 f hball
  obtain ⟨hmeas, hbd⟩ := hdata hρ0 hreal' hR hRρ hT hT1 f hball
  exact ⟨congrOp_aemeas (I := I) (M := M) _ _ hmeas,
    congrOp_norm_le (I := I) (M := M) _ _ hbd⟩

/-- The genuine first-order low-base family along the order-one solution, with
its domain normalized from the literal `H3` to the `H^(aHi+1)` demanded by the
lift at `aHi = 2`. -/
def liftA1Two (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t =>
    (lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t).comp
      (tensorHsCongrL (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num))

/-- The `A1` input packet of `lowreg_lift_two` at `aHi = 2`: strong
measurability and the time-`L²` membership of the first-order family, consumed
from `lowRegA1_memLp`.

`hcont` and `hlin` are *not* discharged here: they are the two facts about the
completed first-order coefficient map that the low-base lane still owes (an
operator bound **affine** in the `H3` state norm).  With the degree-six envelope
currently in the tree the `MemLp` conclusion is false, so passing them on as
hypotheses is the honest interface. -/
theorem liftA1Two_data
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous (lowA1Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hlin : ∀ v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      ‖show tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
          tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) from
        lowA1Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ Φ * (1 + ‖v‖))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) :
    AEStronglyMeasurable
        (liftA1Two (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
        (timeMeasure T) ∧
      MemLp (liftA1Two (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f) 2
        (timeMeasure T) := by
  obtain ⟨hmeas, -, hmem⟩ :=
    lowRegA1_memLp (I := I) (M := M) g hρ hδ0 hδ_le hreal hcont hΦ hlin hT hT1 f
  exact ⟨congrOp_aemeas (I := I) (M := M) _ _ hmeas,
    congrOp_memLp (I := I) (M := M) _ _ hmem⟩

/-! ## C2 -- the realized adjacent-scale cross-scale field -/

omit [BoundarylessManifold I M] in
/-- Intrinsic realization of the one-step adjacent-scale bootstrap.  The output
of `lowreg_lift_two` determines a canonical `CrossScaleField` on the same
horizon whose carrier solves the clean tensor heat equation with the lifted
forcing, whose intermediate `H^(aHi+1)` representative vanishes at time zero and
includes onto the order-one Duhamel field almost everywhere, and whose carrier
includes onto the order-one maximal-regularity solution on the closed slab.

Every hypothesis is a hypothesis of `lowreg_lift_two`; the three extra order
proofs `hOrdUp`, `hOrdRp` only name the inclusions that the realization layer
uses.  Nothing here is a new assumption about the Ricci--DeTurck coefficients. -/
theorem lowreg_realize_two
    {g : SmoothRiemannianMetric I M} {T aLo aHi : ℝ}
    (hlo : aLo = aHi - 1) (hOrd : aLo ≤ aHi)
    (hOrdA1 : aLo + 1 ≤ aHi + 1) (hOrdSt : aLo + 2 ≤ aHi + 2)
    (hOrdUp : aHi ≤ aHi + 1) (hOrdRp : aLo + 2 ≤ aHi + 1)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (A2Hi : ℝ → tensorHs (I := I) (M := M) g 0 2 (aHi + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aHi)
    (hA2Hi : AEStronglyMeasurable A2Hi (timeMeasure T))
    (C2Hi : NNReal) (hC2Hi : ∀ᵐ t ∂timeMeasure T, ‖A2Hi t‖ ≤ (C2Hi : ℝ))
    (A1Hi : ℝ → tensorHs (I := I) (M := M) g 0 2 (aHi + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aHi)
    (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    (f0Hi : timeL2 (tensorHs (I := I) (M := M) g 0 2 aHi) T)
    (hsmallHi : (C2Hi : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1)
    (A2Lo : ℝ → tensorHs (I := I) (M := M) g 0 2 (aLo + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aLo)
    (hA2Lo : AEStronglyMeasurable A2Lo (timeMeasure T))
    (C2Lo : NNReal) (hC2Lo : ∀ᵐ t ∂timeMeasure T, ‖A2Lo t‖ ≤ (C2Lo : ℝ))
    (A1Lo : ℝ → tensorHs (I := I) (M := M) g 0 2 (aLo + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aLo)
    (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    (f0Lo : timeL2 (tensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hsmallLo : (C2Lo : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1)
    (hA2compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A2Hi t) =
        (A2Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt))
    (hA1compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A1Hi t) =
        (A1Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdA1))
    (hf0 : timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd f0Hi = f0Lo)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hfLo : fLo =
      nonautL2Map (I := I) (M := M) hT hT1
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo fLo + f0Lo) :
    ∃ (uHi : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) aHi T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 aHi) T)
      (u : CrossScaleField (I := I) (M := M) g 0 2 aHi T),
      u.lo = uHi ∧
        u.hiL2 = maxRegDuhamelSolField (I := I) (M := M) aHi hT hT1 0 fHi ∧
        fHi =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi ∧
        timeH1.trace0 _ T u.lo =
          (0 : tensorHs (I := I) (M := M) g 0 2 aHi) ∧
        timeH1.timeDeriv _ T u.lo =
          timeScaleLaplacian (I := I) (M := M) aHi u.hiL2 + fHi ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi = fLo ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) = fLo t) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (u.lo.toFun t) =
            (maxRegDuhamelMap (I := I) (M := M) aLo hT hT1 0 fLo).toFun t) ∧
        u.repr 0 = (0 : tensorHs (I := I) (M := M) g 0 2 (aHi + 1)) ∧
        ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (Icc (0 : ℝ) T) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdUp (u.repr t) = u.lo.toFun t) ∧
        (fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrdRp (u.repr t)) =ᵐ[timeMeasure T]
            fun t => maxRegDuhamelSolField (I := I) (M := M)
              aLo hT hT1 0 fLo t := by
  subst hlo
  obtain ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield, hforce_ae, -⟩ :=
    lowreg_lift_two (I := I) (M := M) (g := g) rfl hOrd hOrdA1 hOrdSt hT hT1
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi hsmallHi
      A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo f0Lo hsmallLo
      hA2compat hA1compat hf0 fLo hfLo
  obtain ⟨u, hulo, huhi, htrace', hpde', -, hcarrier, hzero, hcontsq,
      hreprlo, hreprlow⟩ :=
    nonautL2_realize (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi fLo uHi fHi huHi hfHi htrace
      hderiv hforce hfield
  exact ⟨uHi, fHi, u, hulo, huhi, hfHi, htrace', hpde', hforce, hforce_ae,
    hcarrier, hzero, hcontsq, hreprlo, hreprlow⟩

/-! ## Radial inactivity along the order-one solution, symmetry discharged -/

omit [BoundarylessManifold I M] in
/-- The exponent transport does not move the lower-scale size of a state: the
`H2` view of a transported `H3` state has the norm of the untransported
`H^(1+1)` view.  This is `tensorHsCongr_incl` read through
`norm_tensorHsCongr`. -/
theorem norm_incl_congr (g : SmoothRiemannianMetric I M)
    {a b c d : ℝ} (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d)
    (u : tensorHs (I := I) (M := M) g 0 2 b) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hcd
        (tensorHsCongr (I := I) (M := M) g 0 2 hbd u)‖ =
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hab u‖ := by
  rw [← tensorHsCongr_incl (I := I) (M := M) hac hbd hab hcd u,
    norm_tensorHsCongr]

/-- **Along the order-one solution the frozen radial coefficients are the
genuine ones.**  Both total radial maps are the identity almost everywhere on
the transported solver path, with the spectral-symmetry input discharged by
`lowreg_sol_symm_h3` and the ball input taken in the form exported by
`lowreg_partial_sol` (`field t ∈ lowerState g₀ 1 R`). -/
theorem lowRadial_eq_self_sol
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T ρ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hT : 0 < T) (hT1 : T ≤ 1)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (u t))
    (hball : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t ∈
        lowerState (I := I) (M := M) g₀ 1 R) :
    (∀ᵐ t ∂timeMeasure T,
        lowRadialH3 (I := I) (M := M) g₀ ρ
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
              (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) gforce t)) =
          tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
            (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) gforce t)) ∧
      (∀ᵐ t ∂timeMeasure T,
        lowRadialHs (I := I) (M := M) g₀ ρ
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
              (tensorHsCongr (I := I) (M := M) g₀ 0 2
                (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2)) gforce t))) =
          tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
              (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) gforce t))) := by
  have hsymm := lowreg_sol_symm_h3 (I := I) (M := M) g₀ g_bg hR hδ hreal
    hcont hcore (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hT hT1 u gforce hforce
  have hballT : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
          (tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
            (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) gforce t))‖ ≤ R := by
    filter_upwards [hball] with t ht
    rw [norm_incl_congr (I := I) (M := M) g₀
      (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
      (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact ht
  exact lowRadial_eq_self_along_sol (I := I) (M := M) g₀ hρ hRρ hsymm hballT

/-! ## C3 -- the Ricci--DeTurck identification of the lifted forcing -/

/-- The genuine smooth Ricci--DeTurck nonlinearity at an arbitrary spectral
order, on the smooth part of the lower state ball.  At order one this is
`coreN`. -/
def coreNAt (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R δ : ℝ}
    (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ) :
    smoothCore (I := I) (M := M) g₀ R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun x => deTurckSmoothN (I := I) (M := M) g₀ g_bg a
    (symmS (I := I) (M := M) g₀ (coreRep g₀ x)) hδ
    (hreal _ (coreSymm_h2 (I := I) (M := M) g₀ x))

theorem coreNAt_one (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ) :
    coreNAt (I := I) (M := M) g₀ g_bg 1 hδ hreal =
      coreN (I := I) (M := M) g₀ g_bg hδ hreal :=
  rfl

/-- **The smooth Ricci--DeTurck nonlinearity is natural for the scale
inclusions.**  Its spectral coordinates are those of the smooth remainder and do
not depend on the order, so raising the order and including back is the
identity. -/
theorem deTurckSmoothN_incl (g₀ g_bg : SmoothRiemannianMetric I M)
    {a b : ℕ} (hab : (a : ℝ) ≤ (b : ℝ)) (S : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ S) δ) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hab
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg b S hδ_lt hδ) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a S hδ_lt hδ := by
  rw [smoothN_eq_embed (I := I) (M := M) g₀ g_bg b S hδ_lt hδ,
    smoothN_eq_embed (I := I) (M := M) g₀ g_bg a S hδ_lt hδ,
    tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hab]

/-- On the dense smooth core, the higher-order nonlinearity is a genuine lift of
`coreN` along the scale inclusion.  This is the smooth-core instance of the
hypothesis `hN2` of `lowreg_force_id`. -/
theorem coreNAt_incl (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    {a b : ℕ} (hab : (a : ℝ) ≤ (b : ℝ)) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (x : smoothCore (I := I) (M := M) g₀ R) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hab
        (coreNAt (I := I) (M := M) g₀ g_bg b hδ hreal x) =
      coreNAt (I := I) (M := M) g₀ g_bg a hδ hreal x :=
  deTurckSmoothN_incl (I := I) (M := M) g₀ g_bg hab _ hδ _

/-- **The lifted forcing is the genuine Ricci--DeTurck nonlinearity, read at the
lower scale.**  Unconditional: it combines the pointwise almost-everywhere
inclusion identity exported by `lowreg_lift_two` with the forcing
identification exported by `lowreg_partial_sol`. -/
theorem lowreg_force_lo
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T σ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hOrd : ((1 : ℕ) : ℝ) ≤ σ)
    (state : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 σ) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        hOrd (fHi t) = fLo t)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (state t)) :
    ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          hOrd (fHi t) =
        lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (state t) := by
  filter_upwards [hincl, hforce] with t h1 h2
  rw [h1, h2]

/-- **The Ricci--DeTurck Nemytskii identification of the lifted forcing.**  Given
any higher-order lift `N2` of the genuine low-regularity nonlinearity along the
scale inclusion, the lifted forcing is exactly `N2` at the genuine states.  No
regularity, smallness, or coefficient hypothesis is used: the scale inclusion is
injective, so the lower-scale identity `lowreg_force_lo` determines `fHi`
outright.

The single residual frontier of brick C3 is therefore the *construction* of
`N2`, i.e. an `H^σ`-valued Nemytskii map with
`tensorHsInclusion ∘ N2 = lowRegN`.  `coreNAt_incl` produces it on the dense
smooth core; completing it to the whole lower state ball needs an
`H^σ`-valued tame estimate for the low-base nonlinearity, which is the
outstanding low-base lane. -/
theorem lowreg_force_id
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T σ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hOrd : ((1 : ℕ) : ℝ) ≤ σ)
    (state : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 σ) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N2 : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 σ)
    (hN2 : ∀ v : lowerState (I := I) (M := M) g₀ 1 R,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          hOrd (N2 v) =
        lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal v)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        hOrd (fHi t) = fLo t)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (state t)) :
    (fun t => fHi t) =ᵐ[timeMeasure T] fun t => N2 (state t) := by
  filter_upwards [lowreg_force_lo (I := I) (M := M) g₀ g_bg hR hδ hreal hOrd
    state fHi fLo hincl hforce] with t ht
  exact tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) hOrd (ht.trans (hN2 (state t)).symm)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
