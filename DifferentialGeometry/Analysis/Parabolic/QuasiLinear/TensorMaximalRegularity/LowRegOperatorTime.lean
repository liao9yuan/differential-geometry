import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Cross
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTimeA1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalLowRegPair
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTimeA2
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegPrincipalTime

/-!
# Low-regularity Ricci--DeTurck operator fields along the order-one solution

`LowRegPrincipalTime` evaluates the *principal* `H4 → H2` coefficient along the
order-one Ricci--DeTurck solution.  This file adds the two remaining
operator-valued time fields consumed by the adjacent-scale bootstrap:

* `lowRegA1Time`, the genuine first-order low-base action `H3 → H2` evaluated
  along the solution's own `H3` field, with `lowRegA1_memLp` giving its strong
  measurability, its pointwise operator bound, and its time-`L²` membership --
  the hypothesis `hA1 : MemLp A1 2` of the non-autonomous `L²` fixed point;
* `lowRegA2Total`, the *complete* second-order family `principal + extra a2`,
  with `lowRegA2Total_data` giving strong measurability and uniform smallness.
  This family, not `lowRegA2Time`, is the one the bootstrap must consume.

The first-order family is the one whose time-`L²` membership needs an operator
bound **affine** in the `H3` state norm.  The bound currently available in the
tree (`remainder_low_pair`) is of degree six in that norm, so `lowRegA1_memLp`
takes the affine bound `hlin` and the state-map continuity `hcont` as explicit
hypotheses.  Both are consequences of one Lipschitz estimate for the completed
first-order coefficient map (`LipschitzWith.continuous`, then the triangle
inequality at the zero state); that estimate is the outstanding low-base
frontier.

Norms of the completed coefficient maps are written through an explicit
`show … from` at the adjacent-scale operator type.  The coefficient module
states `lowA1Hi` / `lowA2Hi` at *private* operator abbreviations, and instance
search for the operator-norm structure does not get through those heads from
another module.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

/-- The Sobolev scale carrying the order-one solution field. -/
private abbrev solH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)

/-- The Sobolev scale carrying the low-base first-order operator state. -/
private abbrev opH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

/-- The adjacent-scale first-order operator type. -/
private abbrev a1Op (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

/-- The adjacent-scale second-order operator type. -/
private abbrev a2Op (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

/-- The lower adjacent-scale first-order operator type. -/
private abbrev a1LoOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

/-- The lower adjacent-scale second-order operator type. -/
private abbrev a2LoOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

/-- The low principal operator type, at the `(1 : ℕ)`-spelled bottom exponent
in which `PrincipalLowRegPair` states it. -/
private abbrev pLoOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)

/-- The canonical identification of the order-one top exponent `1 + 2` with the
literal Sobolev exponent `3`, as an instance of the scale transport
`tensorHsCongr`. -/
private abbrev solToOpH3 (g : SmoothRiemannianMetric I M) :
    solH3 (I := I) (M := M) g ≃ₗᵢ[ℝ] opH3 (I := I) (M := M) g :=
  tensorHsCongr (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num)

/-! ## The first-order operator field -/

/-- The genuine first-order low-base action evaluated along the order-one
Ricci--DeTurck solution's own `H3` field.  The state is the full `H3` field,
not its `H2` inclusion, because `lowA1Hi` is an `H3`-state coefficient. -/
def lowRegA1Time
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t => lowA1Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
    (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f t))

/-- The first-order operator field is strongly measurable, inherits the affine
operator bound of its coefficient map, and is square-integrable in operator
norm.  The last conclusion is exactly the hypothesis `hA1 : MemLp A1 2` of the
non-autonomous time-`L²` fixed point.

`hcont` and `hlin` are the two facts about the completed first-order
coefficient map that the low-base lane still owes.  Both follow from a single
Lipschitz estimate `LipschitzWith C (lowA1Hi …)`: continuity is
`LipschitzWith.continuous`, and the affine bound is the triangle inequality at
the zero state with `Φ := max ‖lowA1Hi … 0‖ C`.  The bound must be affine: with
the degree-six envelope of `remainder_low_pair` the time-`L²` conclusion
fails. -/
theorem lowRegA1_memLp
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA1Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hlin : ∀ v : opH3 (I := I) (M := M) g,
      ‖show a1Op (I := I) (M := M) g from
        lowA1Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ Φ * (1 + ‖v‖))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
        (lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
        (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
          Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
            (0 : solH3 (I := I) (M := M) g) f t‖)) ∧
      MemLp (lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f) 2
        (timeMeasure T) := by
  have hufield : AEStronglyMeasurable
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f t) (timeMeasure T) :=
    Lp.aestronglyMeasurable _
  have hiso : AEStronglyMeasurable
      (fun t => solToOpH3 (I := I) (M := M) g
        (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)) (timeMeasure T) :=
    (LinearIsometry.toContinuousLinearMap
      (solToOpH3 (I := I) (M := M) g).toLinearIsometry).continuous
        |>.comp_aestronglyMeasurable hufield
  have hmeas : AEStronglyMeasurable
      (lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
      (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable hiso
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
        Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t‖) := by
    refine Eventually.of_forall fun t => ?_
    have h := hlin (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f t))
    rwa [LinearIsometryEquiv.norm_map] at h
  have haffine : ∀ᵐ t ∂timeMeasure T,
      ‖lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
        Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t‖ := by
    filter_upwards [hbound] with t ht
    calc
      _ ≤ Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
            (0 : solH3 (I := I) (M := M) g) f t‖) := ht
      _ = Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
            (0 : solH3 (I := I) (M := M) g) f t‖ := by ring
  obtain ⟨hmem, -⟩ :=
    memLp_clm_affine (T := T)
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f)
      (lowRegA1Time (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
      hmeas hΦ hΦ haffine
  exact ⟨hmeas, hbound, hmem⟩

/-! ## The completed first-order commuting square -/

private theorem coreLip
    {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {D : Set X} {C : ℝ} (hC : 0 ≤ C) (F : D → Y)
    (hF : ∀ x y : D, ‖F x - F y‖ ≤ C * ‖(x : X) - (y : X)‖) :
    LipschitzWith ⟨C, hC⟩ F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_mk, dist_eq_norm, Subtype.dist_eq] using hF x y

/-- A Lipschitz estimate for a smooth-core coefficient, read through the `H3`
smooth-core subtype on which the first-order coefficient maps are completed. -/
private theorem highCorePair {Y : Type*} [SeminormedAddCommGroup Y]
    (g : SmoothRiemannianMetric I M) {C : ℝ}
    (F : LowBaseTimeInternal.HighCore (I := I) (M := M) g → Y)
    (c : SmoothCcTensor g 0 2 → Y)
    (hval : ∀ T : SmoothCcTensor g 0 2,
      F ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ = c T)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖c T - c U‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (x y : LowBaseTimeInternal.HighCore (I := I) (M := M) g) :
    ‖F x - F y‖ ≤
      C * ‖(x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) -
        (y : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))‖ := by
  obtain ⟨T, hT⟩ := x.property
  obtain ⟨U, hU⟩ := y.property
  have hx : x = ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ :=
    Subtype.ext hT.symm
  have hy : y = ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U, ⟨U, rfl⟩⟩ :=
    Subtype.ext hU.symm
  rw [hx, hy, hval, hval, ← map_sub]
  simpa only [ccToHsLin_apply] using hpair T U

/-- Both completed first-order coefficient maps are Lipschitz on the `H3` state
space, both read off the smooth core, and they satisfy the `∀ v` commuting
inclusion square.

This is the first-order sibling of `radialA2_lip`.  The square itself is
unconditional on the smooth core (`radialA1_pair`) and the completion is a
dense extension, so the *only* inputs beyond the ones `lowA1Hi` / `lowA1Lo`
already carry are the two smooth-core Lipschitz estimates `hHiPair` /
`hLoPair` -- the first-order analogue of `a2_pair_lip`, and the single low-base
estimate the lane still owes.  The modulus is taken against the `H3` size of
the state difference, one order weaker than the `H2` modulus that the
second-order estimate achieves.

**WARNING -- `hHiPair` is unsatisfiable as stated, so this theorem is
vacuous.**  `a1Hi` is an `H³ → H²` operator, so its coefficient is read at the
`H²` jet, which costs the *third* jet of the state; the radial cutoff
`lowRadial` inside `lowCoreData` bounds only the spectral `H²` size, and leaves
that third jet free.  Concretely the coefficient difference contains the
cross term `(P(g_T⁻¹) - P(g_U⁻¹)) ∗ ∇T`, i.e. the `B1 · A · D2` slot of
`c1Diff_tame` (`DeTurckRemainderLowBaseLip`), which is sharp: taking `U = T + εV`
with `V` fixed and low-frequency and `T` oscillatory with `‖T‖_{H²} ≤ ρ/2` but
`‖T‖_{H³} = A → ∞` makes the left side `≍ εA` and the right side `≍ Cε`.  No
constant `C` independent of the states works.

The honest replacement is the *ball-local* estimate: for states with
`lowJetSq g 3 T, lowJetSq g 3 U ≤ A²`, the difference is bounded by
`K A · ‖T - U‖_{H³}` -- see `a1_pair_lip`
(`DeTurckRemainderLowBaseA1Pair`) for the currently available version of that
estimate, and the same-name `.md` for what the restatement then needs (a
dense-extension lemma for locally Lipschitz core maps, since the conclusion can
only be `Continuous`, never `LipschitzWith`).  `hLoPair` is by contrast
*plausibly true* -- `a1Lo` reads its coefficient at the `H¹` jet, which the `H²`
ball does control -- but the tree's `c0Diff_tame` / `c1Diff_tame` moduli are too
lossy in `A` to prove it. -/
theorem lowA1_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Hi
            (I := I) (M := M) -
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).a1Hi
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Lo
            (I := I) (M := M) -
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).a1Lo
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖) :
    LipschitzWith ⟨C, hC⟩
        (lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) ∧
      LipschitzWith ⟨C, hC⟩
        (lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) ∧
      (∀ T : SmoothCcTensor g 0 2,
        lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
            (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Hi
            (I := I) (M := M)) ∧
      (∀ T : SmoothCcTensor g 0 2,
        lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
            (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Lo
            (I := I) (M := M)) ∧
      (∀ v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v) =
          (lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v).comp
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ 3 by norm_num))) := by
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  let FHi : LowBaseTimeInternal.HighCore (I := I) (M := M) g →
      a1Op (I := I) (M := M) g :=
    LowBaseTimeInternal.a1HiCore (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
  let FLo : LowBaseTimeInternal.HighCore (I := I) (M := M) g →
      a1LoOp (I := I) (M := M) g :=
    LowBaseTimeInternal.a1LoCore (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
  have hFHi : LipschitzWith ⟨C, hC⟩ FHi :=
    coreLip hC FHi
      (highCorePair (I := I) (M := M) g FHi _
        (LowBaseTimeInternal.a1HiCore_value (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal) hHiPair)
  have hFLo : LipschitzWith ⟨C, hC⟩ FLo :=
    coreLip hC FLo
      (highCorePair (I := I) (M := M) g FLo _
        (LowBaseTimeInternal.a1LoCore_value (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal) hLoPair)
  have hlipHi : LipschitzWith ⟨C, hC⟩
      (lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) :=
    dense_lipschitz (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      FHi hFHi
  have hlipLo : LipschitzWith ⟨C, hC⟩
      (lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) :=
    dense_lipschitz (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      FLo hFLo
  have hcoreHi : ∀ T : SmoothCcTensor g 0 2,
      lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
        (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Hi
          (I := I) (M := M) := by
    intro T
    have hext :=
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
        hFHi.continuous
        (⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ :
          LowBaseTimeInternal.HighCore (I := I) (M := M) g)
    exact hext.trans
      (LowBaseTimeInternal.a1HiCore_value (I := I) (M := M)
        g hρ.le hδ0 hδ_le hreal T)
  have hcoreLo : ∀ T : SmoothCcTensor g 0 2,
      lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
        (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Lo
          (I := I) (M := M) := by
    intro T
    have hext :=
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
        hFLo.continuous
        (⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ :
          LowBaseTimeInternal.HighCore (I := I) (M := M) g)
    exact hext.trans
      (LowBaseTimeInternal.a1LoCore_value (I := I) (M := M)
        g hρ.le hδ0 hδ_le hreal T)
  refine ⟨hlipHi, hlipLo, hcoreHi, hcoreLo, ?_⟩
  obtain ⟨CP, K, hCP, hK, hpair⟩ :=
    radialA1_pair (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal
  have hleft : Continuous fun v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hlipHi.continuous)
  have hright : Continuous fun v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      (lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (hlipLo.continuous.prodMk continuous_const)
  intro v
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [hcoreHi T, hcoreLo T]
  exact (hpair T).2.2

/-- The completed first-order commuting square, in the shape the adjacent-scale
lift consumes.

**WARNING -- vacuous: `hHiPair` is unsatisfiable; see `lowA1_lip`.** -/
theorem lowA1_square
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Hi
            (I := I) (M := M) -
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).a1Hi
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Lo
            (I := I) (M := M) -
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).a1Lo
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (v : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (lowA1Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v) =
      (lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)) :=
  (lowA1_lip (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal hC
    hHiPair hLoPair).2.2.2.2 v

/-- The low sibling of the first-order operator field: the same `H3` state,
read through the completed `H2 → H1` coefficient. -/
def lowRegA1TimeLo
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
  fun t => lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
    (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f t))

/-- The two first-order operator fields along the order-one solution commute
with the Sobolev inclusions at *every* time, not merely almost everywhere:
the spatial square holds at every state.

**WARNING -- vacuous: `hHiPair` is unsatisfiable; see `lowA1_lip`.** -/
theorem lowRegA1_square
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Hi
            (I := I) (M := M) -
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).a1Hi
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    (hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal T).a1Lo
            (I := I) (M := M) -
          (lowCoreData (I := I) (M := M) g hρ.le hδ0 hδ_le hreal U).a1Lo
            (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    ∀ t : ℝ,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ 2 by norm_num)).comp
            (lowRegA1Time (I := I) (M := M)
              g hρ.le hδ0 hδ_le hreal hT hT1 f t) =
        (lowRegA1TimeLo (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal hT hT1 f t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num)) :=
  fun _ =>
    lowA1_square (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal hC
      hHiPair hLoPair _

/-- The low first-order operator field is strongly measurable and
square-integrable in operator norm.  This is the `hA1Lo : MemLp A1Lo 2` input
of the adjacent-scale lift; it takes the same two conditional facts about the
completed coefficient map as its high sibling `lowRegA1_memLp`. -/
theorem lowRegA1Lo_memLp
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hlin : ∀ v : opH3 (I := I) (M := M) g,
      ‖show a1LoOp (I := I) (M := M) g from
        lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ Φ * (1 + ‖v‖))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
        (lowRegA1TimeLo (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
        (timeMeasure T) ∧
      MemLp (lowRegA1TimeLo (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f) 2
        (timeMeasure T) := by
  have hufield : AEStronglyMeasurable
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f t) (timeMeasure T) :=
    Lp.aestronglyMeasurable _
  have hiso : AEStronglyMeasurable
      (fun t => solToOpH3 (I := I) (M := M) g
        (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)) (timeMeasure T) :=
    (LinearIsometry.toContinuousLinearMap
      (solToOpH3 (I := I) (M := M) g).toLinearIsometry).continuous
        |>.comp_aestronglyMeasurable hufield
  have hmeas : AEStronglyMeasurable
      (lowRegA1TimeLo (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
      (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable hiso
  have haffine : ∀ᵐ t ∂timeMeasure T,
      ‖lowRegA1TimeLo (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
        Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t‖ := by
    refine Filter.Eventually.of_forall fun t => ?_
    have h := hlin (solToOpH3 (I := I) (M := M) g
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f t))
    rw [LinearIsometryEquiv.norm_map] at h
    calc
      _ ≤ Φ * (1 + ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
            (0 : solH3 (I := I) (M := M) g) f t‖) := h
      _ = Φ + Φ * ‖maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
            (0 : solH3 (I := I) (M := M) g) f t‖ := by ring
  obtain ⟨hmem, -⟩ :=
    memLp_clm_affine (T := T)
      (maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
        (0 : solH3 (I := I) (M := M) g) f)
      (lowRegA1TimeLo (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f)
      hmeas hΦ hΦ haffine
  exact ⟨hmeas, hmem⟩

/-! ## The complete second-order operator field -/

/-- The complete second-order low-base family along the order-one solution: the
low-regularity principal `H4 → H2` coefficient plus the extra second-order arm
of the low-base action.  Downstream consumers must use this family and not
`lowRegA2Time`, which carries only the principal part. -/
def lowRegA2Total
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t =>
    lowRegA2Time (I := I) (M := M) g hT hT1 f hR hball t +
      lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t)

/-- A continuous completed second-order coefficient map that reads off the
smooth core and is uniformly bounded there is uniformly bounded everywhere. -/
private theorem a2Hi_total_le
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal S).a2Hi
          (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal S).a2Hi
        (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2Op (I := I) (M := M) g from
      lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2Op (I := I) (M := M) g from
        lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2Op (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

/-- The `H3 → H1` sibling of `a2Hi_total_le`. -/
private theorem a2Lo_total_le
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal S).a2Lo
          (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal S).a2Lo
        (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2LoOp (I := I) (M := M) g from
      lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2LoOp (I := I) (M := M) g from
        lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2LoOp (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

/-- One shrunken realized spectral `H2` cutoff on which **both** completed extra
second-order coefficient maps are continuous and uniformly small, and on which
they satisfy the `∀ v` commuting inclusion square.  The smallness is the `C2`
fibre and two-jet cap of `c2_h2_small`, transported by `radialA2_pair`; the
continuity and the square are `radialA2_lip`.  The two radii are matched by
running `radialA2_pair` inside the cutoff produced by `radialA2_lip`. -/
theorem lowA2_small
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
              (ccTensorBilinSymm (I := I) g S) δ),
        Continuous (lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          Continuous (lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2Op (I := I) (M := M) g from
              lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2LoOp (I := I) (M := M) g from
              lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                (show (1 : ℝ) ≤ 2 by norm_num)).comp
                  (lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v) =
              (lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρL, CL, hρL, hρL_le, hlipdata⟩ :=
    radialA2_lip (I := I) (M := M) hDim g hρ₀ hδ0 hδ_le hreal
  have hrealL : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρL →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans hρL_le)
  obtain ⟨ρA, CA, hρA, hρA_le, hCA, hpairdata⟩ :=
    radialA2_pair (I := I) (M := M) hDim g hρL hδ0 hδ_le hrealL
  refine ⟨ρA, CA, hρA, hρA_le.trans hρL_le, hCA, ?_⟩
  intro hρ0 hreal'
  obtain ⟨hlip, hlipLo, hcore, hcoreLo, hsq⟩ := hlipdata (r := ρA) hρ0 hρA_le
  refine ⟨hlip.continuous, hlipLo.continuous, fun v => ?_, fun v => ?_, hsq⟩
  · exact a2Hi_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlip.continuous hcore (fun S => (hpairdata S hρ0 hρA_le).1) v
  · exact a2Lo_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlipLo.continuous hcoreLo (fun S => (hpairdata S hρ0 hρA_le).2.1) v

/-- A non-vacuous version of `lowA2_small`: the realized cutoff is chosen after
the common pair coefficient, so the reported operator floor satisfies
`C * ρ < 1`.  The completed maps retain the same continuity, bounds, and
commuting square. -/
theorem lowA2_small_one
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧ C * ρ < 1 ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        Continuous (lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          Continuous (lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal') ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2Op (I := I) (M := M) g from
              lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2LoOp (I := I) (M := M) g from
              lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v‖ ≤ C * ρ) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                (show (1 : ℝ) ≤ 2 by norm_num)).comp
                  (lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v) =
              (lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρL, CL, hρL, hρL_le, hlipdata⟩ :=
    radialA2_lip (I := I) (M := M) hDim g hρ₀ hδ0 hδ_le hreal
  have hrealL : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρL →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans hρL_le)
  obtain ⟨ρA, CA, hρA_le, hρA, hCA, hpairdata⟩ :=
    radialA2_pairR (I := I) (M := M) hDim g hρL hδ0 hδ_le hrealL
  let ρ : ℝ := min ρA (1 / (CA + 1))
  have hden : 0 < CA + 1 := by linarith only [hCA]
  have hρ : 0 < ρ := lt_min hρA (one_div_pos.mpr hden)
  have hρA' : ρ ≤ ρA := min_le_left _ _
  have hρL' : ρ ≤ ρL := hρA'.trans hρA_le
  have hρ₀' : ρ ≤ ρ₀ := hρL'.trans hρL_le
  have hρcap : ρ ≤ 1 / (CA + 1) := min_le_right _ _
  have hsmall : CA * ρ < 1 := by
    calc
      CA * ρ ≤ CA * (1 / (CA + 1)) := mul_le_mul_of_nonneg_left hρcap hCA
      _ = CA / (CA + 1) := by ring
      _ < 1 := (div_lt_one hden).2 (by linarith only [hCA])
  refine ⟨ρ, CA, hρ, hρ₀', hCA, hsmall, ?_⟩
  intro hρ0 hreal'
  obtain ⟨hlip, hlipLo, hcore, hcoreLo, hsq⟩ :=
    hlipdata (r := ρ) hρ0 hρL'
  refine ⟨hlip.continuous, hlipLo.continuous, fun v => ?_, fun v => ?_, hsq⟩
  · exact a2Hi_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlip.continuous hcore (fun S => (hpairdata hρ0 hρA' S).1) v
  · exact a2Lo_total_le (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
      hlipLo.continuous hcoreLo (fun S => (hpairdata hρ0 hρA' S).2.1) v

/-- The complete second-order family along the order-one solution is strongly
measurable and uniformly small in operator norm, on one positive spectral `H2`
radius that also controls the solution's own state ball. -/
theorem lowRegA2Total_data
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
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M)
              (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maxRegDuhamelSolField (I := I) (M := M)
                (1 : ℝ) hT hT1
                (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegA2Total (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegA2Total (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t‖ ≤ C * ρ) := by
  obtain ⟨ρP, CP, hρP, hdataP⟩ :=
    lowRegA2_data (I := I) (M := M) hDim g
  have hρ₁ : 0 < min ρ₀ ρP := lt_min hρ₀ hρP
  have hreal₁ : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ min ρ₀ ρP →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (min_le_left _ _))
  obtain ⟨ρ, CA, hρ, hρ_le₁, hCA, hA2⟩ :=
    lowA2_small (I := I) (M := M) hDim g hρ₁ hδ0 hδ_le hreal₁
  refine ⟨ρ, (CP : ℝ) + CA, hρ, hρ_le₁.trans (min_le_left _ _),
    add_nonneg CP.coe_nonneg hCA, ?_⟩
  intro hρ0 hreal' R hR hRρ T hT hT1 f hball
  obtain ⟨hcont, -, hsmall, -, -⟩ := hA2 hρ0 hreal'
  obtain ⟨hmeasP, hboundP, -⟩ :=
    hdataP hR (hRρ.trans (hρ_le₁.trans (min_le_right _ _))) hT hT1 f hball
  have hstate : AEStronglyMeasurable
      (fun t => lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t))
      (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball))
  refine ⟨hmeasP.add hstate, ?_⟩
  filter_upwards [hboundP] with t ht
  have ht' : ‖show a2Op (I := I) (M := M) g from
      lowRegA2Time (I := I) (M := M) g hT hT1 f hR hball t‖ ≤ (CP : ℝ) * R := ht
  calc
    ‖lowRegA2Total (I := I) (M := M)
        g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t‖ ≤
        ‖show a2Op (I := I) (M := M) g from
            lowRegA2Time (I := I) (M := M) g hT hT1 f hR hball t‖ +
          ‖show a2Op (I := I) (M := M) g from
            lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
              (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (CP : ℝ) * R + CA * ρ :=
      add_le_add ht'
        (hsmall (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t))
    _ ≤ (CP : ℝ) * ρ + CA * ρ :=
      add_le_add (mul_le_mul_of_nonneg_left hRρ CP.coe_nonneg) le_rfl
    _ = ((CP : ℝ) + CA) * ρ := by ring

/-! ## The low sibling of the complete second-order family -/

/-- The low-regularity principal operator, normalized to the literal bottom
exponent `(1 : ℝ)`, evaluated along the order-one solution's own `H2` state
field.  The state is the *same* ball lift that `lowRegA2Time` evaluates at, so
the two families are compared at every time, not only almost everywhere. -/
def lowRegA2TimeLo
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
  fun t =>
    (tensorHsCongrL (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).comp
      (lowRegPrincipalLo (I := I) (M := M) g
        (aeSetLift (principalBall_zero (I := I) (M := M) g hR)
          (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) t).1)

/-- The complete low principal producer: one positive spectral `H2` radius on
which the low principal family along the order-one solution is strongly
measurable, linearly bounded, and forms the canonical Sobolev-inclusion square
with its `H4 → H2` sibling `lowRegA2Time` at *every* time.

Measurability needs no Lipschitz estimate for the `H3 → H1` correction: on the
ball the perturbed identity is a unit, so `principalLo_cont` gives continuity
directly from continuity of `Ring.inverse` at units. -/
theorem lowRegA2Lo_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball)
              (timeMeasure T) ∧
            (∀ t : ℝ,
              ‖show a2LoOp (I := I) (M := M) g from
                lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball t‖ ≤
                  C * R) ∧
            (∀ t : ℝ,
              (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (1 : ℝ) ≤ 2 by norm_num)).comp
                    (lowRegA2Time (I := I) (M := M) g hT hT1 f hR hball t) =
                (lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball t).comp
                  (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρc, hρc, hcomm⟩ := principal_comm (I := I) (M := M) hDim g
  obtain ⟨ρn, C42, C31, hρn, hC42, hC31, hnorm⟩ :=
    principal_pair_norm (I := I) (M := M) hDim g
  obtain ⟨ρk, hρk, hcontOn⟩ := principalLo_cont (I := I) (M := M) hDim g
  refine ⟨min ρc (min ρn ρk), C31, lt_min hρc (lt_min hρn hρk), hC31, ?_⟩
  intro R hR hRρ T hT hT1 f hball
  have hRc : R ≤ ρc := hRρ.trans (min_le_left _ _)
  have hRn : R ≤ ρn :=
    hRρ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRk : R ≤ ρk :=
    hRρ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : ∀ᵐ t ∂timeMeasure T,
      lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t ∈
        principalBall (I := I) (M := M) g R := by
    simpa only [principalBall, Set.mem_setOf_eq] using
      lowRegState_ae_le (I := I) (M := M) g hT hT1 f hR hball
  have hsub : principalBall (I := I) (M := M) g R ⊆
      {S : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) | ‖S‖ ≤ ρk} :=
    fun _ hS => le_trans hS hRk
  have hres : Continuous
      (Set.restrict (principalBall (I := I) (M := M) g R)
        (lowRegPrincipalLo (I := I) (M := M) g)) :=
    (hcontOn.mono hsub).restrict
  have hΦ : Continuous fun x : principalBall (I := I) (M := M) g R =>
      (tensorHsCongrL (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).comp
        (lowRegPrincipalLo (I := I) (M := M) g x.1) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hres)
  refine ⟨hΦ.comp_aestronglyMeasurable
      (aeSetLift_aesm (principalBall_zero (I := I) (M := M) g hR)
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) hmem),
    ?_, ?_⟩
  · intro t
    have hxR : ‖(aeSetLift (principalBall_zero (I := I) (M := M) g hR)
          (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) t).1‖ ≤ R :=
      (aeSetLift (principalBall_zero (I := I) (M := M) g hR)
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) t).2
    have heq : ‖show a2LoOp (I := I) (M := M) g from
          lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball t‖ =
        ‖show pLoOp (I := I) (M := M) g from
          lowRegPrincipalLo (I := I) (M := M) g
            (aeSetLift (principalBall_zero (I := I) (M := M) g hR)
              (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) t).1‖ :=
      norm_congr_comp (I := I) (M := M) _ _
    rw [heq]
    exact ((hnorm _ (hxR.trans hRn)).2).trans
      (mul_le_mul_of_nonneg_left hxR hC31)
  · intro t
    have hxR : ‖(aeSetLift (principalBall_zero (I := I) (M := M) g hR)
          (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) t).1‖ ≤ R :=
      (aeSetLift (principalBall_zero (I := I) (M := M) g hR)
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball) t).2
    have hsq := hcomm _ (hxR.trans hRc)
    have hstep := congrArg
      (fun L : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
          tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) =>
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).comp L) hsq
    simp only [← ContinuousLinearMap.comp_assoc] at hstep
    rw [tensorHsCongrL_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (rfl : (2 : ℝ) = (2 : ℝ))
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num),
      tensorHsCongrL_refl, ContinuousLinearMap.comp_id] at hstep
    exact hstep

/-- The low sibling of the complete second-order family: the low principal
family plus the low extra `a2` arm, both at the literal bottom exponent. -/
def lowRegA2TotalLo
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
  fun t =>
    lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball t +
      lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t)

/-- The complete low second-order family along the order-one solution is
strongly measurable and uniformly small in operator norm, on one positive
spectral `H2` radius, and it forms the canonical Sobolev-inclusion square with
`lowRegA2Total` at every time.  Together with `lowRegA2Total_data` this is the
`A2` half of the adjacent-scale lift's input packet. -/
theorem lowRegA2TotalLo_data
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
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : solH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegA2TotalLo (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegA2TotalLo (I := I) (M := M)
                g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t‖ ≤ C * ρ) ∧
            (∀ t : ℝ,
              (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show (1 : ℝ) ≤ 2 by norm_num)).comp
                    (lowRegA2Total (I := I) (M := M)
                      g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t) =
                (lowRegA2TotalLo (I := I) (M := M)
                    g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t).comp
                  (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (show (3 : ℝ) ≤ 4 by norm_num))) := by
  obtain ⟨ρP, CP, hρP, hCP, hdataP⟩ :=
    lowRegA2Lo_data (I := I) (M := M) hDim g
  have hρ₁ : 0 < min ρ₀ ρP := lt_min hρ₀ hρP
  have hreal₁ : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ min ρ₀ ρP →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (min_le_left _ _))
  obtain ⟨ρ, CA, hρ, hρ_le₁, hCA, hA2⟩ :=
    lowA2_small (I := I) (M := M) hDim g hρ₁ hδ0 hδ_le hreal₁
  refine ⟨ρ, CP + CA, hρ, hρ_le₁.trans (min_le_left _ _),
    add_nonneg hCP hCA, ?_⟩
  intro hρ0 hreal' R hR hRρ T hT hT1 f hball
  obtain ⟨-, hcontLo, -, hsmallLo, hsqA⟩ := hA2 hρ0 hreal'
  obtain ⟨hmeasP, hboundP, hsqP⟩ :=
    hdataP hR (hRρ.trans (hρ_le₁.trans (min_le_right _ _))) hT hT1 f hball
  have hstate : AEStronglyMeasurable
      (fun t => lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t))
      (timeMeasure T) :=
    hcontLo.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable
        (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball))
  refine ⟨hmeasP.add hstate, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun t => ?_
    calc
      ‖lowRegA2TotalLo (I := I) (M := M)
          g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t‖ ≤
          ‖show a2LoOp (I := I) (M := M) g from
              lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball t‖ +
            ‖show a2LoOp (I := I) (M := M) g from
              lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
                (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t)‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ CP * R + CA * ρ :=
        add_le_add (hboundP t)
          (hsmallLo (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t))
      _ ≤ CP * ρ + CA * ρ :=
        add_le_add (mul_le_mul_of_nonneg_left hRρ hCP) le_rfl
      _ = (CP + CA) * ρ := by ring
  · intro t
    have hHi : lowRegA2Total (I := I) (M := M)
          g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t =
        lowRegA2Time (I := I) (M := M) g hT hT1 f hR hball t +
          lowA2Hi (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
            (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t) := rfl
    have hLo : lowRegA2TotalLo (I := I) (M := M)
          g hρ0 hδ0 hδ_le hreal' hT hT1 f hR hball t =
        lowRegA2TimeLo (I := I) (M := M) g hT hT1 f hR hball t +
          lowA2Lo (I := I) (M := M) g hρ0 hδ0 hδ_le hreal'
            (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t) := rfl
    rw [hHi, hLo, ContinuousLinearMap.comp_add, hsqP t,
      hsqA (lowRegStateL2 (I := I) (M := M) g hT hT1 f hR hball t),
      ← ContinuousLinearMap.add_comp]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
