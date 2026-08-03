import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegApplyTwo
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegSolutionJointlySmooth

/-!
# The re-based all-order forcing-coordinate package at `a = 2`

Front 2 of the `(N)` discharge (`ShortTime/LOWREG_BOOTSTRAP_PLAN.md`, brick B1)
re-bases the existing joint-smoothness endpoint chain on the horizon that the
closed `(1, 2)` rung actually reports.  The endpoint
`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
(`HeatSemigroup/MaxRegSolutionJointlySmooth.lean`) is sorry-free and lands the
`(N)` `rr` fields — `F 0 = 0`, the `Ico`-slab PDE with `HasDerivWithinAt … (Ici 0)`,
and `JointChartGramSmooth T` through the `t = 0` corner — on the **full, unshrunk**
horizon.  Its `hC` slot already has a purpose-built dimension-three producer at
`a = 2` (`hs2_opBound_at_two`).  The one input with no producer at `a = 2` is the
all-order smooth-in-time forcing-coordinate package, and supplying it is this file.

## Layout

* `lowreg_spatialMass` — the single honest FRONTIER (`sorry`), and a purely
  **spatial** statement: for every real `σ`, a `t`-uniform `σ`-weighted spectral-mass
  bound for the per-mode convolutions of the trajectory's own forcing on `Icc 0 T`.
  No time derivative occurs in it.  It is pinned to the low-lane forcing identity
  (`force_hi_id`'s conclusion), so it is not vacuous, and to the state ball `hballU`
  together with the smooth-core bridge `hbridge`, without which it would be false.
* `liftN_smoothN_coeff` — the state-level bridge: the frozen split `liftHiN`,
  evaluated at the `H⁴` embedding of a smooth in-ball state, has the
  eigen-coordinates of `deTurckSmoothN g g 2 (symmS g ·)`.  This replaces the
  supercritical identification `deTurckSobolevNHa2_eq_smoothN`.
* `lowreg_forceJetStep` / `lowreg_forceDriver` — the `a = 2` transplant of the
  supercritical finite-order forcing bootstrap, on the FULL horizon (no shrink).
* `lowreg_forceJetMass` — sorry-free over `lowreg_spatialMass`: it runs the driver,
  diagonalizes the finite-order tower into `JetSpectralMassControl`, and reads the
  a-priori realizability radius off the `σ = 4`, `j = 0` majorant.
* `lowreg_allOrderJet` — sorry-free glue over that leaf: it unpacks
  `IsRealizedTwo`, identifies the low carrier with the affine Duhamel map
  (`timeH1.ext` against `maxRegDuhamelMap_init` / `maxRegDuhamelMap_timeDeriv_eq`),
  and turns the leaf's coordinate family into exactly the four forcing slots
  (`hf_smooth`, `hf_mass`, `hf_id`, and the folded `R₀` / `hball_full`) that the
  endpoint consumes.  CONDITIONAL on `lowreg_spatialMass`.
* `lowreg_joint_smooth` — sorry-free, and independent of the frontier: it runs the
  endpoint at `a = 2` on a supplied package, feeding `hs2_opBound_at_two` into the
  `hC` slot.  Its `hfloor` and `hForce` slots stay visible hypotheses; see below.

## Why the frontier is spatial and not "all-order time regularity"

`ForcingCoordinateTimeRegularity.lean` splits the supercritical statement into
(A) interior-time smoothing of the solution field and (B) order-preserving
jet-mass smoothness of the Nemytskii `deTurckSobolevNHa2Symm`.  Neither survives
verbatim at `a = 2`: there is no intrinsic `H⁴ → H²` Ricci–DeTurck Nemytskii
operator in the tree (`deTurckSobolevNHa2` exists only above
`2·finrank ℝ E + 10 ≤ a`); the only high-scale nonlinearity at the closed rung is
the frozen split `liftHiN` (`ShortTime/LowRegForceHi.lean`), whose first-order arm
`FHi` is an unconstrained existential inside `IsRealizedTwo` unless the producer
certificates are carried along.

What DOES survive is the supercritical template's *shape*.  Three of its four
stages are order-generic today (`FORCEJETMASS_PLAN.md` §2): the smooth-tensor
reconstruction from all-order spatial mass
(`exists_smoothCcPath_realizing_coeff`), the smooth-core chart chain rule
producing finite-order time jets
(`deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass`, de-vestigialized in
brick F1), and the a.e.-agreement diagonal.  The one supercritical step that is
genuinely order-gated — identifying the completed Nemytskii with its smooth core
on the realizability ball — is replaced here by `liftN_smoothN_coeff`, which is
proved from the widened `IsRealizedTwo` certificates alone.  What remains is
therefore exactly the a-priori estimate (S1₂), i.e. `lowreg_spatialMass`.

Both horizon shrinks of the supercritical driver are *dropped*, not transplanted:
they existed only to enter the completed Nemytskii's realizability ball, and at
`a = 2` that ball is the hypothesis `hballU` on all of `[0,T]`.

## `hForce` is discharged; `hfloor` is not

`IsRealizedTwo` now re-exports the producer certificates (`R` with `hreal` and
the a.e. state-ball bound on the carrier, `hNcont`, `hcoreN`, `hA2cont`,
`hA2core`, `hA2Hicont`, `FLo` with `hFLo`/`hFLoCore`, `Continuous FHi`, and the
two commuting squares `hA2sq`/`hFComm`).  With them `coord_eq_smoothN` proves the
endpoint's `hForce` slot outright for the concrete `lowregNsec`, so
`lowreg_joint_of_re` no longer carries it.

`hfloor` (`√T · ‖u.deriv‖ ≤ 1/(2C)`) stays visible, and this is not a packaging
gap.  `u.deriv = timeScaleLaplacian 2 u.hiL2 + fHi` and `IsRealizedTwo` carries
no size bound at the high scale; even granting one (a Neumann bound for the
exported fixed-point equation `fHi = nonautL2Map … fHi + liftForceHi`, which
would need the contraction certificate `hsmallHi` exported too), `hfloor` is a
*smallness condition on `T` itself*.  For an arbitrary `T` admitting an
`IsRealizedTwo` package it is simply false, so it can only be discharged by
shrinking the horizon `T₀` that `lowreg_solve_two` reports — a change to that
theorem, i.e. a separate brick.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
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

/-! ## Exponent-transport bookkeeping -/

omit [BoundarylessManifold I M] in
/-- The exponent transport does not move eigenbasis coordinates.  (Its canonical
home is beside `norm_tensorHsCongr` in `SobolevScale/ExponentCongr.lean`; it is
kept here because this brick does not claim that file.) -/
theorem tensorHsCongr_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) (v : tensorHs (I := I) (M := M) g r s a)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsCongr (I := I) (M := M) g r s h v).coeff i = v.coeff i := by
  cases h
  rfl

/-! ## The concrete `a = 2` smooth-state nonlinearity -/

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
/-- **The Ricci--DeTurck smooth-state nonlinearity in the endpoint's `Nsec`
shape.**  This is the same `Nsec` the supercritical lane uses (the symmetrized
smooth DeTurck remainder); naming it lets the `a = 2` lane discharge the
endpoint's `hForce` slot instead of carrying it as a hypothesis. -/
noncomputable def lowregNsec (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g (symmS (I := I) (M := M) g S) hδ_lt
    (gFibreOpBound_symmS (I := I) (M := M) g S hδ)

/-! ## The forcing-coordinate identity at `a = 2` -/

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
set_option linter.unusedVariables false in
/-- **The `a = 2` analogue of `realizedForcingCoord_eq_smoothNSymm`.**

Along a carrier `u` whose `H⁴` companion `hi` drives the high forcing `fHi`
through the frozen split `liftHiN`, any smooth family `F` pinned to `u` in `L²`
on the closed slab realizes the forcing coordinates as the coordinates of the
genuine smooth Ricci--DeTurck remainder on `Ico 0 T`.

The route is the one the low lane already owns:
`hiN_incl` moves the frozen split down to `refoldBaseN`, `lowreg_N_affine`
identifies `refoldBaseN` with the dense-extension nonlinearity `lowRegN` on the
state ball, and `lowRegN_on_smooth` evaluates the latter on a smooth
representative.  The a.e.-to-everywhere upgrade on `Ico 0 T` is
`Measure.eqOn_Ico_of_ae_eq` against the continuity of `refoldBaseN` composed
with the spectral continuity of the pinned smooth field.  The state-ball
membership at *every* time of `Ico 0 T` is the same upgrade applied to
`‖toFun u ·‖` (continuous by `timeH1.continuousOn_toFun`) against the a.e. bound
`hUball`.  No smallness or regularity input beyond those certificates. -/
private theorem coord_eq_smoothN
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδlt : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g g hR hδlt hreal))
    (hcoreN : Continuous (coreN (I := I) (M := M) g g hδlt hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    {T : ℝ} (hT : 0 < T)
    (u : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (hUball : ∀ᵐ t ∂timeMeasure T, ‖timeH1.toFun u t‖ ≤ R)
    (hi : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) T)
    (hlink : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num) (hi t) = timeH1.toFun u t)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hforceId : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (hi t)))
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (fc i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (fc i) t) ^ 2 ≤ B i)
    (hcpin : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t)
    (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ_lt : δ' < 1)
    (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (F t)) δ')
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
      SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
      fc i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (lowregNsec (I := I) (M := M) g (F t) hδ_lt (hδ' t))) i := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
  -- (1) the pinned smooth family, read in `H²` and on the eigen-coordinates
  have hsm2 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t) =
        timeH1.toFun u t := by
    intro t ht
    refine tensorHs.ext (funext fun j => ?_)
    rw [smoothCcToTensorHs_coeff, h_pin t ht, tensorHsToL2_tensorL2Coeff]
  -- (2) the `H³` view of that family is continuous on the closed slab
  have hφ_smooth : ∀ i, ContDiff ℝ ∞
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i)) :=
    fun i => perModeConv_contDiff_of_contDiff ⊤ _ (fc i) (hf_smooth i)
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
    perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (T := T) hT.le fc hf_smooth hf_mass 0
      ((3 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity)
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))
      (Set.Icc (0 : ℝ) T) := by
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g
      (σ := (3 : ℝ))
      (σ' := (3 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) ?_ _
      (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i))
      ?_ (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum ?_
    · have hring : (3 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) - 3 =
          ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by ring
      rw [hring]
      linarith
    · intro t ht i
      rw [smoothCcToTensorHs_coeff, h_pin t ht]
      exact hf_id t ht i
    · intro i t ht
      have h := hCmaj_le i t ht
      rwa [iteratedDeriv_zero] at h
  have hΨ_cont : ContinuousOn
      (fun t => refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t)))
      (Set.Icc (0 : ℝ) T) :=
    (refoldBaseN_cont (I := I) (M := M) g hρ hδ0 hδ_le hreal' FLo
      hA2cont hFLo).comp_continuousOn hfield_cont
  -- (3) the forcing coordinates agree a.e. with the low-scale frozen split
  have hae : ∀ i, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      fc i t =
        (refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
          (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))).coeff i := by
    intro i
    filter_upwards [hcpin i, hforceId, hlink,
      MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hcp hfo hlk htmem
    have hv : tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (hi t) =
        smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, h_pin t htmem,
        tensorHsToL2_tensorL2Coeff, ← hlk, tensorHsInclusion_coeff_apply]
    have hsplit := hiN_incl (I := I) (M := M) g hρ hδ0 hδ_le hreal' FHi FLo
      hA2sq hFComm (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t))
    rw [tensorHsInclusion_smoothCcToTensorHs] at hsplit
    rw [← hcp, hfo, hv, ← hsplit, tensorHsInclusion_coeff_apply]
  -- (4) both sides are continuous on `Ico 0 T`, so the a.e. identity is exact
  have heqOn : ∀ i, Set.EqOn (fc i)
      (fun t => (refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))).coeff i)
      (Set.Ico (0 : ℝ) T) := by
    intro i
    refine MeasureTheory.Measure.eqOn_Ico_of_ae_eq
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
      ((hf_smooth i).continuous.continuousOn) ?_
    · exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self (hae i)
    · exact (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (σ := (1 : ℝ)) i).continuous.comp_continuousOn
        (hΨ_cont.mono Set.Ico_subset_Icc_self)
  -- (5) the a.e. state-ball bound holds at every time of `Ico 0 T`
  have hnorm_cont : ContinuousOn (fun t => ‖timeH1.toFun u t‖)
      (Set.Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn (timeH1.continuousOn_toFun u)
  have hmin_cont : ContinuousOn (fun s => min ‖timeH1.toFun u s‖ R)
      (Set.Icc (0 : ℝ) T) := ContinuousOn.inf hnorm_cont continuousOn_const
  have hballIco : ∀ t ∈ Set.Ico (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ R := by
    intro t ht
    have hmin : (fun s => min ‖timeH1.toFun u s‖ R)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ico (0 : ℝ) T)] fun s => ‖timeH1.toFun u s‖ := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self hUball] with s hs
      exact min_eq_left hs
    have h := MeasureTheory.Measure.eqOn_Ico_of_ae_eq
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hmin
      (hmin_cont.mono Set.Ico_subset_Icc_self)
      (hnorm_cont.mono Set.Ico_subset_Icc_self) ht
    exact min_eq_left_iff.mp h
  -- (6) evaluate the low-scale action on the smooth representative
  intro t ht i
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      (smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R := by
    rw [tensorHsInclusion_smoothCcToTensorHs,
      norm_smoothCc_congr (I := I) (M := M) g
        (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) (F t), hsm2 t htIcc]
    exact hballIco t ht
  have hcongr3 : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) (F t)) =
      smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  have hAff : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g g hR hδlt hreal
          ⟨smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 2) (F t), hS⟩) =
      refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t)) := by
    rw [← hcongr3]
    exact lowreg_N_affine (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FLo hFLo hFLoCore
      ⟨smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) (F t), hS⟩
  refine (heqOn i ht).trans ?_
  change (refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
      (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))).coeff i = _
  rw [← hAff, tensorHsCongr_coeff,
    lowRegN_on_smooth (I := I) (M := M) g g hR hδlt hreal hcoreN (F t) hS,
    smoothN_wd (I := I) (M := M) g g 1
      (symmS (I := I) (M := M) g (F t)) (symmS (I := I) (M := M) g (F t))
      hδlt (hreal _ (symm_h2_of_state (I := I) (M := M) g (F t) hS))
      hδ_lt (gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδ' t)) rfl,
    deTurckSmoothN_coeff]
  rfl

/-! ## The state-level bridge -/

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
set_option linter.unusedVariables false in
/-- **The frozen split, read on a smooth in-ball state, IS the smooth Ricci--DeTurck
nonlinearity.**

`liftHiN` evaluated at the `H⁴` embedding of a smooth `S` whose `H²` view lies in the
producers' state ball has exactly the eigen-coordinates of
`deTurckSmoothN g g 2 (symmS g S)`.

This is the state-level half of the `a = 2` forcing bootstrap: it replaces the
supercritical identification `deTurckSobolevNHa2_eq_smoothN`, which does not exist below
`2·finrank ℝ E + 10 ≤ a`.  The route is the one the low lane already owns — `hiN_incl`
moves the frozen split down to `refoldBaseN`, `lowreg_N_affine` identifies `refoldBaseN`
with the dense-extension nonlinearity `lowRegN` on the state ball, and
`lowRegN_on_smooth` evaluates the latter on the smooth representative.  Only the producer
certificates that the widened `IsRealizedTwo` re-exports are used; no smallness and no
time regularity. -/
private theorem liftN_smoothN_coeff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδlt : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g g hR hδlt hreal))
    (hcoreN : Continuous (coreN (I := I) (M := M) g g hδlt hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (S : SmoothCcTensor g 0 2)
    (hS2 : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R)
    (δ' : ℝ) (hδ_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ')
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
      (deTurckSmoothN (I := I) (M := M) g g 2
        (symmS (I := I) (M := M) g S) hδ_lt
        (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i := by
  -- (1) the high frozen split lifts to the low frozen split of the same state
  have h1 : (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
      (refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) S)).coeff i := by
    have hsplit := hiN_incl (I := I) (M := M) g hρ hδ0 hδ_le hreal' FHi FLo
      hA2sq hFComm (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)
    rw [tensorHsInclusion_smoothCcToTensorHs] at hsplit
    rw [← hsplit, tensorHsInclusion_coeff_apply]
  -- (2) the state ball, in the shape `lowRegN` consumes
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      (smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R := by
    rw [tensorHsInclusion_smoothCcToTensorHs,
      norm_smoothCc_congr (I := I) (M := M) g
        (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S]
    exact hS2
  have hcongr3 : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) S) =
      smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) S := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  have hAff : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g g hR hδlt hreal
          ⟨smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 2) S, hS⟩) =
      refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) S) := by
    rw [← hcongr3]
    exact lowreg_N_affine (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FLo hFLo hFLoCore
      ⟨smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) S, hS⟩
  -- (3) evaluate the dense-extension nonlinearity on the smooth representative
  rw [h1, ← hAff, tensorHsCongr_coeff,
    lowRegN_on_smooth (I := I) (M := M) g g hR hδlt hreal hcoreN S hS,
    smoothN_wd (I := I) (M := M) g g 1
      (symmS (I := I) (M := M) g S) (symmS (I := I) (M := M) g S)
      hδlt (hreal _ (symm_h2_of_state (I := I) (M := M) g S hS))
      hδ_lt (gFibreOpBound_symmS (I := I) (M := M) g S hδ') rfl]
  rfl

/-! ## The finite-order forcing-coordinate driver at `a = 2` -/

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
set_option linter.unusedVariables false in
/-- **One rung of the `a = 2` forcing bootstrap.**  The `a = 2` analogue of
`deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving`, on the **full** horizon
`T`.

From a `C^k` coordinate family `φ` for the `H⁴` solution field `w` with `j ≤ k` spectral
mass on `Icc 0 T`, it produces a `C^k` coordinate family `ψ` for the forcing `fHi` with
the same control.  The three transplanted steps are: reconstruct a smooth path realizing
`φ` (`exists_smoothCcPath_realizing_coeff`), transport the coordinates across the
symmetrizer (`symmCoeffPath`), and run the order-generic smooth-core time-jet layer
(`deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass`).  The supercritical
identification of the completed Nemytskii with its smooth core is replaced by the
state-level bridge `hbridge`, and both horizon shrinks of the supercritical template are
dropped: at `a = 2` the state ball `hw_ball` is a hypothesis on all of `[0,T]`. -/
private theorem lowreg_forceJetStep
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i)
    {T : ℝ} (hT : 0 < T)
    (w : ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num) (w t)‖ ≤ R)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (w t)))
    (k : ℕ) (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (fHi t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] ψ i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  have hδlt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  -- (1) the zeroth-order spatial mass of the input coordinates
  have hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 (Nat.zero_le k) σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have h := hBle i t ht
    rwa [iteratedDeriv_zero] at h
  -- (2) a smooth path realizing the input coordinates, cut off outside the slab
  obtain ⟨F₀, hF₀_coeff⟩ :=
    exists_smoothCcPath_realizing_coeff (I := I) (M := M) g φ hmass0
  set F : ℝ → SmoothCcTensor g 0 2 :=
    fun t => if t ∈ Set.Icc (0 : ℝ) T then F₀ t else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    simp only [hF_def, ht, if_pos]
    exact hF₀_coeff t ht i
  have hF_hs2 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hF_coeff t ht i
  -- (3) the state ball holds at EVERY time of the closed slab
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t))
      (Set.Icc (0 : ℝ) T) := by
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmass0
      ((2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity)
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g
      (σ := (2 : ℝ))
      (σ' := (2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) ?_
      (s := Set.Icc (0 : ℝ) T)
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)) φ
      hF_hs2 (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum
      (fun i t ht => hCmaj_le i t ht)
    have hring : (2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) - 2 =
        ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by ring
    rw [hring]
    linarith
  have hball_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ ≤ R := by
    have hall : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        ∀ i, (w t).coeff i = φ i t := (MeasureTheory.ae_all_iff).2 hw
    filter_upwards [hw_ball, hall, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t hbt htall htmem
    have heq : smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t) =
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num) (w t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [hF_hs2 t htmem j, tensorHsInclusion_coeff_apply, htall j]
    rw [heq]
    exact hbt
  have hball_pt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ ≤ R := by
    have hcont_norm : ContinuousOn
        (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖)
        (Set.Icc (0 : ℝ) T) := continuous_norm.comp_continuousOn hfield_cont
    have hg_cont : ContinuousOn
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F s)‖ ⊓ R)
        (Set.Icc (0 : ℝ) T) := hcont_norm.inf continuousOn_const
    have hfg : (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F s)‖)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T)]
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F s)‖ ⊓ R) := by
      filter_upwards [hball_ae] with s hs
      exact (min_eq_left hs).symm
    have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hT) hfg
      hcont_norm hg_cont
    intro t ht
    have hmin : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ ⊓ R := heq ht
    rw [hmin]
    exact inf_le_right
  -- (4) the fibre-bound certificate at EVERY real time
  have hδF : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (F t)) δ := by
    intro t
    refine hreal' (F t) ?_
    have hcc : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (F t) =
        smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [ccTensorToHs_coeff, smoothCcToTensorHs_coeff]
    rw [hcc]
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · exact le_trans (hball_pt t ht) hRρ
    · have hF0 : F t = (0 : SmoothCcTensor g 0 2) := by
        simp only [hF_def, ht, if_neg, not_false_iff]
      have hz : smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
        have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
          (zero_smul ℝ _).symm
        rw [h0, smoothCcToTensorHs_smul, zero_smul]
      rw [hF0, hz, norm_zero]
      exact hρ.le
  have hδS : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (symmS (I := I) (M := M) g (F t))) δ :=
    fun t => gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδF t)
  -- (5) transport the coordinate control across the symmetrizer
  have hφ'_smooth : ∀ i, ContDiff ℝ (k : ℕ)
      (symmCoeffPath (I := I) (M := M) g φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g hφ_smooth
  have hφ'_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g φ i) t) ^ 2 ≤ B i := by
    intro j hjk τ hτ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g hT j
      (fun j' => (hφ_smooth j').of_le (mod_cast hjk)) τ
      (hφ_mass j hjk τ hτ)
      (hφ_mass j hjk (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (symmS (I := I) (M := M) g (F t))) i =
        symmCoeffPath (I := I) (M := M) g φ i t := fun t ht i =>
    symmCoeffPath_realizes (I := I) (M := M) g φ (F t) (fun j => hF_coeff t ht j) i
  -- (6) the order-generic smooth-core time-jet layer
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass (I := I) (M := M)
      g g 2 hT k (fun t => symmS (I := I) (M := M) g (F t)) hδlt hδS
      (symmCoeffPath (I := I) (M := M) g φ) hφ'_smooth hcoeff' hφ'_mass
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  -- (7) the a.e. identification of the forcing coordinate
  have hall : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ j, (w t).coeff j = φ j t := (MeasureTheory.ae_all_iff).2 hw
  filter_upwards [hfix, hall, MeasureTheory.ae_restrict_mem
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t hfx htall htmem
  have hv : tensorHsCongr (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (w t) =
      smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, htall j]
    exact (hF_coeff t htmem j).symm
  calc (fHi t).coeff i
      = (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (w t))).coeff i := by rw [hfx]
    _ = (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
          (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t))).coeff i := by rw [hv]
    _ = (deTurckSmoothN (I := I) (M := M) g g 2
          (symmS (I := I) (M := M) g (F t)) hδlt (hδS t)).coeff i :=
        hbridge (F t) (hball_pt t htmem) δ hδlt (hδF t) i
    _ = ψ i t := hψ_coeff t htmem i

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
set_option linter.unusedVariables false in
/-- **The `a = 2` finite-order forcing driver on the FULL horizon.**  The `a = 2`
analogue of `deTurckForcing_finiteOrderSmoothDriverSymm`, with **no horizon shrink**.

From the spatial posit `hspatial` — the all-`σ` uniform spectral-mass bound on the
trajectory — it produces, for every `k`, a `C^k` forcing coordinate family with `j ≤ k`
spectral mass on `Icc 0 T` and the a.e. pin.  The induction on `k` is the supercritical
one: the base rung needs only continuity of the solution coordinates, and the step feeds
the previous rung's forcing regularity through the per-mode convolution
(`perModeConv_finiteOrder_timeJet_spectralMass_gain`) before re-entering
`lowreg_forceJetStep`.  Both shrinks of the supercritical template are dropped: they
existed only to enter the completed Nemytskii's realizability ball, and at `a = 2` that
ball is the hypothesis `hballU` on all of `[0,T]`. -/
private theorem lowreg_forceDriver
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)))
    (hballU : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R)
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ Cσ) :
    ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (fHi t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] f i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  set w : ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2) :=
    fun t => maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t with hw_def
  set ρw : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρw_def
  have hρw_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρw := by rw [hρw_def]; linarith
  -- (a) a globally continuous representative of the per-mode convolution
  have hpmc_contOn : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      ContinuousOn (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u)) (Set.Icc (0 : ℝ) T) :=
    fun i => continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) fHi i) hT.le
  set c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := fun i =>
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) p.1) with hc_def
  have hc_cont : ∀ i, Continuous (c i) := fun i =>
    Continuous.Icc_extend' ((hpmc_contOn i).restrict)
  have hc_eqOn : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u)) (Set.Icc (0 : ℝ) T) := by
    intro i t ht
    exact Set.IccExtend_of_mem hT.le _ ht
  -- (b) the spatial mass of the per-mode convolution, from the posit
  have hs_mass : ∀ τ : ℝ, 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ B i := by
    intro τ hτ
    obtain ⟨Cτ, hCτ⟩ := hspatial (τ + ρw)
    refine ⟨fun i => Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρw),
      (tensorEigen_summable_negpow (I := I) (M := M) g ρw hρw_gt).mul_left Cτ, ?_⟩
    intro i t ht
    obtain ⟨hsum_t, hbd_t⟩ := hCτ t ht
    have hterm : tensorSobolevWeight (I := I) (M := M) i (τ + ρw)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ Cτ :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j (τ + ρw)) (sq_nonneg _))) hbd_t
    have hsplit : tensorSobolevWeight (I := I) (M := M) i τ
        = tensorSobolevWeight (I := I) (M := M) i (-ρw)
          * tensorSobolevWeight (I := I) (M := M) i (τ + ρw) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρw) (τ + ρw)]
      congr 1
      ring
    calc tensorSobolevWeight (I := I) (M := M) i τ
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρw)
            * (tensorSobolevWeight (I := I) (M := M) i (τ + ρw)
              * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2) := by
          rw [hsplit]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρw) * Cτ :=
          mul_le_mul_of_nonneg_left hterm
            (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρw))
      _ = Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρw) := by ring
  -- (c) the per-mode Duhamel identity, on the whole closed slab
  have hcoeff_id : ∀ i, (fun t => (w t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u)) := fun i =>
    timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hT1 hc fHi i
  have hfHi_tmc : ∀ i, (fun t => (fHi t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (fun s => (timeModeCoeff (I := I) (M := M) fHi i) s) := fun i =>
    (timeModeCoeff_coeFn (I := I) (M := M) fHi i).symm
  intro k
  induction k with
  | zero =>
    exact lowreg_forceJetStep (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal'
      FHi hbridge hT w hballU fHi hfix 0 c
      (fun i => by rw [Nat.cast_zero, contDiff_zero]; exact hc_cont i)
      (fun j hj τ hτ => by
        obtain rfl := Nat.le_zero.mp hj
        obtain ⟨B, hBs, hBle⟩ := hs_mass τ hτ
        refine ⟨B, hBs, fun i t ht => ?_⟩
        rw [iteratedDeriv_zero, hc_eqOn i ht]
        exact hBle i t ht)
      (fun i => by
        refine (hcoeff_id i).trans ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
        exact (hc_eqOn i ht).symm)
  | succ k ih =>
    obtain ⟨fk, hfk_cont, hfk_mass, hfk_ae⟩ := ih
    obtain ⟨hφ_cont, hφ_mass⟩ :=
      perModeConv_finiteOrder_timeJet_spectralMass_gain (I := I) (M := M)
        g hT.le k fk hfk_cont hfk_mass
    have hw_coeff : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
      intro i
      have hfk_tmc : (fun s => (timeModeCoeff (I := I) (M := M) fHi i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] (fk i) :=
        (hfHi_tmc i).symm.trans (hfk_ae i)
      have hpm : (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u))
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
        exact perModeConv_timeL2_congr (T := T)
          (TensorEigenIdx.lambda (I := I) (M := M) i) hfk_tmc ht
      exact (hcoeff_id i).trans hpm
    exact lowreg_forceJetStep (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal'
      FHi hbridge hT w hballU fHi hfix (k + 1)
      (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
      hφ_cont hφ_mass hw_coeff

/-! ## The carrier's per-mode Duhamel identity -/

omit [BoundarylessManifold I M] in
/-- **The carrier's eigen-coordinates are the per-mode convolutions of the forcing
coordinates.**  For a forcing coordinate family `fc` that is continuous, carries an `H²`
spatial mass majorant on the closed slab, and agrees a.e. with the bare forcing
coordinate, the zero-datum Duhamel carrier of `fHi` has `L²` coordinates
`perModeConv λᵢ (fc i) t` at *every* time of `Icc 0 T`.

The everywhere-representative built from the majorant is what upgrades the a.e. pin to
the closed slab, through `carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict`. -/
private theorem carrier_coeff_pmConv
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_cont : ∀ i, Continuous (fc i))
    (hf_mass0 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i t) ^ 2 ≤ B i)
    (hpin : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
            ((maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).toFun t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass0
  set pr : ℝ → ℝ :=
    fun t => ((Set.projIcc (0 : ℝ) T hT.le t : Set.Icc (0 : ℝ) T) : ℝ) with hpr_def
  have hpr_mem : ∀ t, pr t ∈ Set.Icc (0 : ℝ) T :=
    fun t => (Set.projIcc (0 : ℝ) T hT.le t).2
  have hpr_id : ∀ t ∈ Set.Icc (0 : ℝ) T, pr t = t := by
    intro t ht
    rw [hpr_def]
    simp only [Set.projIcc_of_mem hT.le ht]
  have hpr_cont : Continuous pr :=
    continuous_subtype_val.comp continuous_projIcc
  set Frep : ℝ → tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
    fun t => tensorHs_of_spectralMass_majorant (I := I) (M := M)
      (fun i => fc i (pr t)) B0 hB0_sum
      (fun i => hB0_le i (pr t) (hpr_mem t)) with hFrep_def
  have hFrep_coeff : ∀ (t : ℝ) (i : TensorEigenIdx (I := I) (M := M) g 0 2),
      (Frep t).coeff i = fc i (pr t) := fun _ _ => rfl
  have hFcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      ContinuousOn (fun t => (Frep t).coeff i) (Set.Icc (0 : ℝ) T) := fun i =>
    ((hf_cont i).comp hpr_cont).continuousOn
  have hall : ∀ᵐ t ∂(timeMeasure T),
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2, (fHi t).coeff i = fc i t :=
    (MeasureTheory.ae_all_iff).2 hpin
  have hF_rep : (⇑fHi) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] Frep := by
    filter_upwards [hall, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht htmem
    refine tensorHs.ext (funext fun i => ?_)
    rw [ht i, hFrep_coeff t i, hpr_id t htmem]
  intro t ht i
  rw [tensorHsToL2_tensorL2Coeff,
    carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
      (h_compact := hc) (a := (2 : ℝ)) hT hT1 hT le_rfl fHi hFcoord hF_rep i ht]
  refine perModeConv_timeL2_congr (T := T)
    (TensorEigenIdx.lambda (I := I) (M := M) i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with s hs
  rw [Set.IccExtend_of_mem hT.le _ hs, hFrep_coeff s i, hpr_id s hs]

/-! ## The honest analytic frontier -/

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
set_option linter.unusedVariables false in
/-- **FRONTIER (`sorry`) — (S1₂): the all-order uniform SPATIAL spectral mass of the
`a = 2` low-lane trajectory, on the state ball where the frozen split IS the smooth
core.**

For the high forcing `fHi` pinned to the frozen Ricci--DeTurck split along its own
zero-datum Duhamel trajectory (`hfix`), whose `H²` state stays in the radius-`R` ball
a.e. in time (`hballU`) and on which the frozen split agrees eigen-coordinate-wise with
the smooth core `deTurckSmoothN g g 2` (`hbridge`), and for **every real** `σ`, the
per-mode convolutions `perModeConv λᵢ (timeModeCoeff fHi i)` — the eigen-coordinates of
the solution field — carry a `t`-uniform `σ`-weighted spectral-mass bound on the closed
slab `Icc 0 T`.  No time derivative occurs anywhere in the statement: this is a purely
spatial a-priori estimate on the trajectory.

**Why `hbridge` and `hballU` are part of the statement.**  Without them the claim is
FALSE, not merely unproved: `FHi` is then an unconstrained map and
`FHi x := ⟪·, e⟫ • w` with `w ∈ H² ∖ H³` plants a permanently-`H²` component in
`liftHiN`'s third summand, so the `σ`-weighted mass of the trajectory diverges for `σ`
large.  `hbridge` is exactly what excludes this: on the radius-`R` state ball it
identifies `liftHiN … FHi` with the smooth core `deTurckSmoothN g g 2`, which is the
only reason a Galerkin argument can be run at all.  Both hypotheses are the ones
`lowreg_forceDriver` already consumes and are already stocked at the unique call site
(`lowreg_forceJetMass` builds `hbridge` from `liftN_smoothN_coeff` and binds `hballU`
itself), so the widening costs no producer work.  `hRρ` accompanies them because the
fibre-smallness certificate `hreal'` is stated at radius `ρ`.

**Role.**  This is the ONLY analytic input of the `a = 2` forcing-coordinate package.
`lowreg_forceDriver` turns it into the finite-order time-jet tower, and
`lowreg_forceJetMass` diagonalizes that tower into `JetSpectralMassControl` and reads the
realizability radius off its `σ = 4`, `j = 0` majorant.  Everything between here and
`lowreg_allOrderJet` is sorry-free wiring.

**Why it is true.**  It is the `a = 2` instance of the supercritical Galerkin estimate
`deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm`
(`HeatSemigroup/GalerkinLimitUniformMass.lean`): finite-dimensional Galerkin ODE,
per-scale energy closure, Grönwall, Fatou.  The Grönwall engine
`galerkin_energy_uniform_bound_perScale` (`GalerkinParabolicEnergy.lean`) is already
order-generic and sorry-free — its `σ₀ : ℝ` is free and it carries no metric, no `a` and
no nonlinearity.  In dimension three the state control at `a = 2` is `H⁴ ⊂ C^{2,1/2}`,
ample for the coefficients of a second-order operator, so the required per-scale
dissipation closure holds.

**Why it is not proved here.**  The per-scale closure that the engine consumes,
`deTurckGalerkin_forcing_dissipation_perScaleSymm`
(`GalerkinParabolicEnergyDeTurck.lean`), is gated on `4·finrank ℝ E + 10 ≤ a` (internally
weakened to `2·finrank ℝ E + 10 ≤ a`), i.e. `a ≥ 16` in dimension three, and it is built
from the *retracted completed* Nemytskii `deTurckSobolevNHa2Symm`, which does not exist
at `a = 2`.  Writing it at base order 2 needs (i) a Galerkin forcing defined directly
from `deTurckSmoothN g g (2 + k)` on the finite-dimensional eigen-combination space, and
(ii) a new tame-splitting estimate at base order 2.  That is a genuinely new estimate,
not a missing theory; see `ShortTime/FORCEJETMASS_PLAN.md` §7.2–§7.3 (brick F6) and the
brick sequence in `ShortTime/F6_ESTIMATE_RECON.md` §7.6.  Do not consume this downstream
except through `lowreg_forceJetMass`. -/
theorem lowreg_spatialMass (g : SmoothRiemannianMetric I M)
    {R ρ δ : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)))
    (hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i)
    (hballU : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R)
    (σ : ℝ) :
    ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ Cσ := by
  sorry

/-! ## The all-order forcing-coordinate leaf -/

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
set_option linter.unusedVariables false in
/-- **All-order interior-time smoothing of the closed `(1, 2)` rung, read on the forcing
coordinates.**

Let `fHi ∈ L²_t H²` be a high-scale forcing that satisfies the low-lane fixed-point
identity `hfix`: a.e. in `t` it is the frozen Ricci–DeTurck split `liftHiN` evaluated
along the `H⁴` field of the zero-datum Duhamel solution it itself drives.  This is
exactly the last conjunct of `IsRealizedTwo` (`ShortTime/LowRegApplyTwo.lean`), i.e. the
conclusion of `force_hi_id`, so the statement is pinned to a trajectory that actually
exists and is not vacuous.  The remaining hypotheses are the producer certificates that
the widened `IsRealizedTwo` re-exports, together with the a.e. state ball `hballU`.

The conclusion is the pair the joint-smoothness endpoint consumes at `a = 2`:

* an a-priori realizability radius `R₀` valid on the **whole closed slab** `[0,T]` —
  every smooth `H⁴` representative of the carrier `u(t)` has `‖·‖_{H^{2+2}} ≤ R₀` (the
  endpoint's `hball_full`);
* an eigen-coordinate family `fc` for the forcing which is `C^∞` in time and carries the
  full all-order time-jet / all-order spatial spectral-mass majorant on `[0,T]`
  (`JetSpectralMassControl`), agreeing a.e. with the bare coordinate
  `t ↦ (fHi t).coeff i`.

**Proof route.**  `lowreg_forceDriver` produces the finite-order tower on the full
horizon from the single spatial posit `lowreg_spatialMass`; all rungs agree a.e., hence
`EqOn` on the slab by continuity, so rung `0` is `ContDiffOn ℝ ∞` there and extends
globally by `contDiffOn_Icc_scalar_globalExtend`.  The radius is then read off the
`σ = 4`, `j = 0` majorant of `perModeConv_allOrder_timeDeriv_spectralMass_le` — no
horizon shrink is needed, because the low lane's state ball is a hypothesis on all of
`[0,T]`.

CONDITIONAL: through `lowreg_spatialMass` only. -/
theorem lowreg_forceJetMass (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδlt : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g g hR hδlt hreal))
    (hcoreN : Continuous (coreN (I := I) (M := M) g g hδlt hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)))
    (hballU : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
              ((maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).toFun t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀) ∧
      ∃ fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
        JetSpectralMassControl (I := I) (M := M) g fc T ∧
        ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  -- the state-level bridge
  have hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i :=
    fun S hS2 δ' hδ_lt hδ' i =>
      liftN_smoothN_coeff (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
        hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
        hA2sq hFComm S hS2 δ' hδ_lt hδ' i
  -- the finite-order tower, from the single spatial posit
  have hdrv := lowreg_forceDriver (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal'
    FHi hbridge hT hT1 fHi hfix hballU
    (fun σ => lowreg_spatialMass (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal' FHi
      hT hT1 fHi hfix hbridge hballU σ)
  choose Fk hFk_smooth hFk_mass hFk_ae using hdrv
  -- the diagonal glue
  set f0 : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := Fk 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) T ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (Fk k i) (f0 i) (Set.Icc (0 : ℝ) T) := by
    intro k i
    have hae : (Fk k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] (f0 i) :=
      (hFk_ae k i).symm.trans (hFk_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hFk_smooth k i).continuous).continuousOn
      ((hFk_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) T) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hFk_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) T) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hT (hf0_smoothOn i)
  choose fc hfc_smooth hfc_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) T →
      iteratedDeriv j (fc i) t =
        iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) T) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hfc_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
      ((hfc_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  have hfc_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (fc i) t) ^ 2 ≤ B i := by
    intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hFk_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (fc i) t = iteratedDeriv j (Fk j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
        ((hFk_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  have hfc_pin : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i := by
    intro i
    refine (hFk_ae 0 i).trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
    exact hfc_eqOn i ht
  -- the realizability radius, read off the `σ = 4`, `j = 0` majorant
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
    perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (T := T) hT.le fc hfc_smooth hfc_mass 0
      ((2 : ℝ) + 2) (by norm_num)
  have hCmaj_nn : ∀ i, 0 ≤ Cmaj i := fun i =>
    le_trans (mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) i ((2 : ℝ) + 2)) (sq_nonneg _))
      (hCmaj_le i 0 ⟨le_rfl, hT.le⟩)
  have hcarr := carrier_coeff_pmConv (I := I) (M := M) g hT hT1 fHi fc
    (fun i => (hfc_smooth i).continuous)
    (by
      obtain ⟨B, hBs, hBle⟩ := hfc_mass 0 (2 : ℝ) (by norm_num)
      refine ⟨B, hBs, fun i t ht => ?_⟩
      have h := hBle i t ht
      rwa [iteratedDeriv_zero] at h)
    hfc_pin
  refine ⟨Real.sqrt (∑' i, Cmaj i) + 1, ?_, ?_,
    fc, ⟨hfc_smooth, hfc_mass⟩, hfc_pin⟩
  · linarith only [Real.sqrt_nonneg (∑' i, Cmaj i)]
  · intro t ht S hS
    have hcoeff : ∀ i,
        (smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).coeff i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
      intro i
      rw [smoothCcToTensorHs_coeff, hS]
      exact hcarr t ht i
    have hptwise : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℝ) + 2) *
        ((smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).coeff i) ^ 2 ≤
          Cmaj i := by
      intro i
      rw [hcoeff i]
      have h := hCmaj_le i t ht
      rwa [iteratedDeriv_zero] at h
    have hsq_le : ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ^ 2 ≤
        ∑' i, Cmaj i := by
      rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
      exact Summable.tsum_le_tsum hptwise
        ((smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).weighted_summable)
        hCmaj_sum
    have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤
        Real.sqrt (∑' i, Cmaj i) := by
      rw [show ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ =
        Real.sqrt (‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq_le
    linarith only [hnorm_le]

/-! ## The re-based forcing-coordinate package -/

/-- **The all-order forcing-coordinate package at `a = 2` (brick B1).**

From the realized adjacent-scale `(1, 2)` package `IsRealizedTwo` — the output of
`lowreg_solve_two`, whose horizon is built from `hDim` and `g` alone — produce the
four forcing slots of `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`
on the **full, unshrunk** horizon `T`:

* the low carrier `u` with vanishing initial trace, identified with the affine
  zero-datum Duhamel map of the high forcing `fHi`;
* smooth-in-time spectral coordinates `fc` for `fHi` with the all-`(j, τ)`
  summable spectral-mass majorant on `Icc 0 T` and the a.e. coordinate pin;
* the per-mode Duhamel identity `hf_id` for the carrier, obtained from the pin
  through `carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict`;
* the realizability radius `R₀` with the endpoint's `hball_full` on all of
  `Icc 0 T`;
* the endpoint's `hForce` slot for the concrete `lowregNsec`, discharged from
  the producer certificates the widened `IsRealizedTwo` now carries (and with a
  *weaker* hypothesis than the endpoint asks: no `hball` on `Ico 0 T` is
  needed, the `L²` pin alone suffices);
* the package's forcing floor `√T·‖fHi‖ ≤ Kf`, forwarded verbatim.  Composed
  with `‖u.deriv‖ ≤ 2‖fHi‖` (the zero-datum Duhamel derivative split) it is
  what discharges the endpoint's `hfloor` in `lowreg_joint_of_re`.

CONDITIONAL: the coordinate family and the radius come from
`lowreg_forceJetMass`, so this theorem transitively depends on the single spatial
frontier `lowreg_spatialMass`.  The carrier identification, the per-mode identity
and the forcing-coordinate identity are sorry-free glue. -/
theorem lowreg_allOrderJet (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) {Kf : ℝ}
    (hre : IsRealizedTwo (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Kf) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := 0) (s := 2) (2 : ℝ) T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
      (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ) (R₀ : ℝ),
      timeH1.trace0 _ T u = 0 ∧
      u = maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi ∧
      (∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) ∧
      (∀ i, ContDiff ℝ ∞ (fc i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (fc i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t) ∧
      0 < R₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀) ∧
      (∀ (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ_lt : δ' < 1)
          (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g (F t)) δ'),
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) →
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
          fc i t = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
                (lowregNsec (I := I) (M := M) g (F t) hδ_lt (hδ' t))) i) ∧
      Real.sqrt T * ‖fHi‖ ≤ Kf := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  obtain ⟨FHi, C2Hi, hA2Hi, hC2Hi, hA1Hi, uHi, fHi, ucs, FLo, R, hR, hreal,
    -, hhiL2, -, htr, hder, -, -, -, -, -, -, -, hforceId,
    hRρ, hNcont, hcoreN, hA2cont, hA2core, -, -, hFLo, hFLoCore, hA2sq,
    hFComm, hballU, hfHiNorm⟩ := hre
  have hδlt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hfid0 := hforceId
  -- (1) the low carrier IS the affine zero-datum Duhamel map of `fHi`
  have hinit : ucs.lo.init = (0 : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) := by
    have h := htr
    rwa [timeH1.trace0_apply] at h
  have hduh : ucs.lo = maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi := by
    refine timeH1.ext ?_ ?_
    · rw [hinit, maxRegDuhamelMap_init]
      exact (map_zero _).symm
    · have e1 : ucs.lo.deriv =
          timeScaleLaplacian (I := I) (M := M) (2 : ℝ) ucs.hiL2 + fHi := by
        rw [← timeH1.timeDeriv_apply]
        exact hder
      have e2 : (maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).deriv =
          timeScaleLaplacian (I := I) (M := M) (2 : ℝ)
              (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi) + fHi := by
        rw [← timeH1.timeDeriv_apply]
        exact maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := hc)
          hT hT1 _ fHi
      rw [e1, e2, hhiL2]
  -- (2) the frontier, pinned to the low-lane forcing identity
  rw [hhiL2] at hforceId
  have hballD : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R := by
    filter_upwards [ucs.link, hballU] with t hlk hbt
    have hstep : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t) =
        timeH1.toFun ucs.lo t := by
      rw [← hhiL2]
      exact hlk
    rw [hstep]
    exact hbt
  obtain ⟨R₀, hR₀_pos, hball, fc, ⟨hf_smooth, hf_mass⟩, hpin⟩ :=
    lowreg_forceJetMass (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
      hA2sq hFComm hT hT1 fHi hforceId hballD
  -- (3) the per-mode Duhamel identity on the closed slab
  have hf_mass0 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i s) ^ 2 ≤ B i := by
    obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 (2 : ℝ) (by norm_num)
    refine ⟨B0, hB0_sum, fun i s hs => ?_⟩
    have h := hB0_le i s hs
    rwa [iteratedDeriv_zero] at h
  have hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M) hc
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun ucs.lo t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
    intro t ht i
    rw [hduh]
    exact carrier_coeff_pmConv (I := I) (M := M) g hT hT1 fHi fc
      (fun j => (hf_smooth j).continuous) hf_mass0 hpin t ht i
  refine ⟨ucs.lo, fHi, fc, R₀, htr, hduh, hpin, hf_smooth, hf_mass, hf_id,
    hR₀_pos, ?_, ?_, hfHiNorm⟩
  · intro t ht S hS
    exact hball t ht S (by rw [hS, hduh])
  · intro F δ' hδ_lt hδ' h_pin
    exact coord_eq_smoothN (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
      hA2sq hFComm hT ucs.lo hballU ucs.hiL2 ucs.link fHi hfid0 fc hf_smooth
      hf_mass hpin hf_id F hδ_lt hδ' h_pin

/-! ## The endpoint, re-run at `a = 2` -/

set_option linter.unusedVariables false in
/-- **The joint-smoothness endpoint at `a = 2` on the rung's own horizon
(brick B5).**

`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii` run at the
Sobolev index `a = 2`, with the `hC` slot filled by the dimension-three producer
`hs2_opBound_at_two` (its first consumer).  The conclusion is the `(N)`-shaped
triple on the FULL supplied horizon `T` — no `∃ T₁ ≤ T` shrink:

* `F 0 = 0` (the `rr 0 = g₀` field, after `tensorSectionRealizeMetric`);
* the `Ico`-slab PDE field with `HasDerivWithinAt … (Set.Ici 0)`;
* `JointChartGramSmooth T`, i.e. joint `C^∞` of the chart Gram entries on the
  CLOSED slab `Icc 0 T ×ˢ baseSet`, corner included — strictly stronger than
  `(N)`'s `Ico 0 τ₀`.

`lowreg_allOrderJet` is the producer of `u`, `htrace`, `fc`, `hf_smooth`,
`hf_mass`, `hf_id`, `R₀`, `hR₀_pos` and `hball_full` for the trajectory of
`lowreg_solve_two`.

`hfloor` and `hForce` stay parameters *here* because this theorem is the raw
endpoint wrapper.  Its caller `lowreg_joint_of_re` discharges `hForce` from
`lowreg_allOrderJet` (route `hiN_incl → lowreg_N_affine → lowRegN_on_smooth`,
with the a.e.-to-everywhere upgrade of `coord_eq_smoothN`); only `hfloor`, the
one-time horizon floor of `LOWREG_BOOTSTRAP_PLAN.md` §8.3, survives.  The
endpoint itself now takes the state ball `‖timeH1.toFun u t‖ ≤ 1 / (2 * C)` on
`[0,T]`; `hfloor` reaches it through `timeH1.state_le_of_sqrt_floor`, so a
caller with a state bound in hand may bypass the floor entirely.

`F_RHS`, `Nsec` and `hRepr` are kept generic, exactly as in the endpoint;
`DeTurckInitialDataExistence.lean` (the `hRepr` block of
`deTurckRicci_solution_with_jointReg`) is the order-free producer for
`F_RHS := deTurckRicciRHS g_bg` and the symmetrized DeTurck remainder.

This theorem is sorry-free and does NOT depend on `lowreg_spatialMass`. -/
theorem lowreg_joint_smooth (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ),
      SmoothCcTensor g 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (htrace : timeH1.trace0 _ T u = 0)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (fc i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (fc i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t)
    (hfloor : Real.sqrt T * ‖u.deriv‖ ≤
      1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hball_full : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀)
    (hForce : ∀ (F : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (F t)) δ)
        (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
          SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t))
        (hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) (F t)‖ ≤ R₀),
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
        fc i t = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
              (Nsec (F t) hδ_lt (hδ t))) i) :
    ∃ (F : ℝ → SmoothCcTensor g 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ t)) := by
  obtain ⟨hC_pos, hC⟩ := (hs2_opBound_at_two (I := I) (M := M) hDim g).choose_spec
  have hinit : u.init = 0 := by have := htrace; rwa [timeH1.trace0_apply] at this
  exact maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
    (I := I) (M := M) g 2 F_RHS Nsec hRepr hT hT1 u htrace fc hf_smooth hf_mass
    hf_id _ hC_pos hC (u.state_le_of_sqrt_floor hinit hfloor) hR₀_pos hball_full hForce

set_option linter.unusedVariables false in
/-- **Front 2, composed: the realized `(1, 2)` rung reaches the `(N)` fields on
its own horizon.**

Along the trajectory of `lowreg_solve_two` (i.e. from `IsRealizedTwo` alone) the
`(N)`-shaped triple holds on the FULL horizon `T` that the solver reported:
`F 0 = 0`, the `Ico`-slab PDE with `HasDerivWithinAt … (Set.Ici 0)`, and
`JointChartGramSmooth T` on the closed slab.  No horizon shrink is taken
anywhere in the chain.

Both endpoint slots that used to be visible here are now discharged.

* `hForce`: with the producer certificates carried by `IsRealizedTwo`,
  `coord_eq_smoothN` proves it outright for the concrete `lowregNsec`.
* `hfloor` (`√T·‖u.deriv‖ ≤ 1/(2C)` against the dimension-three fibre constant
  `C` of `hs2_opBound_at_two`, `LOWREG_BOOTSTRAP_PLAN.md` §8.3): the carrier is
  the zero-datum Duhamel map of `fHi`, so `maxRegDuhamelMap_deriv` together with
  `maxRegHomogeneousDerivField_norm_le` at `u₀ = 0` and
  `maximalRegularityDerivField_norm_le` gives `‖u.deriv‖ ≤ 2‖fHi‖`; the package's
  forcing floor `√T·‖fHi‖ ≤ Kf` then closes it as soon as `Kf ≤ 1/(4C)`.  The
  floor is a smallness condition on `T`, and it is met by shrinking the horizon
  that `lowreg_solve_two` reports — that is what `Kf` is for.

`hRepr` stays a hypothesis: it is the order-free Ricci--DeTurck representation
block of `deTurckRicci_solution_with_jointReg`
(`ShortTime/DeTurckInitialDataExistence.lean`), whose extraction is a separate
brick.

CONDITIONAL on the spatial frontier `lowreg_spatialMass` (through
`lowreg_forceJetMass` and `lowreg_allOrderJet`); the endpoint step itself is
sorry-free. -/
theorem lowreg_joint_of_re (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (lowregNsec (I := I) (M := M) g S hδ_lt hδ +
            rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) {Kf : ℝ}
    (hre : IsRealizedTwo (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Kf)
    (hKfC : Kf ≤
      1 / (4 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose)) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) (2 : ℝ) T)
        (F : ℝ → SmoothCcTensor g 0 2) (δ' : ℝ) (hδ_lt : δ' < 1)
        (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (F t)) δ'),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) := by
  obtain ⟨u, fHi, fc, R₀, htr, hduh, hpin, hf_smooth, hf_mass, hf_id,
    hR₀_pos, hball_full, hForce, hfHiNorm⟩ :=
    lowreg_allOrderJet (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal' hT hT1 f hre
  obtain ⟨hC_pos, -⟩ := (hs2_opBound_at_two (I := I) (M := M) hDim g).choose_spec
  -- The carrier is the zero-datum Duhamel map of `fHi`, so its `L²` time
  -- derivative is bounded by twice the forcing.
  have hderiv : ‖u.deriv‖ ≤ 2 * ‖fHi‖ := by
    have hhom : ‖maxRegHomogeneousDerivField (I := I) (M := M) (2 : ℝ) T
        (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2))‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      simpa using maxRegHomogeneousDerivField_norm_le (I := I) (M := M)
        (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (a := (2 : ℝ)) (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) hT.le
    have hreg : ‖maximalRegularityDerivField (I := I) (M := M) (2 : ℝ) hT.le fHi‖ ≤
        2 * ‖fHi‖ :=
      maximalRegularityDerivField_norm_le (I := I) (M := M)
        (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        hT.le fHi
    rw [hduh, maxRegDuhamelMap_deriv]
    refine (norm_add_le _ _).trans ?_
    linarith only [hhom, hreg]
  have hfloor : Real.sqrt T * ‖u.deriv‖ ≤
      1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose) := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
    have hC := hC_pos.ne'
    calc Real.sqrt T * ‖u.deriv‖ ≤ Real.sqrt T * (2 * ‖fHi‖) :=
          mul_le_mul_of_nonneg_left hderiv hs0
      _ = 2 * (Real.sqrt T * ‖fHi‖) := by ring
      _ ≤ 2 * (1 / (4 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose)) := by
          linarith only [hfHiNorm, hKfC]
      _ = 1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose) := by
          field_simp
          norm_num
  exact ⟨u, lowreg_joint_smooth (I := I) (M := M) hDim g F_RHS
    (lowregNsec (I := I) (M := M) g) hRepr hT hT1 u htr
    fc hf_smooth hf_mass hf_id hfloor hR₀_pos hball_full
    (fun F _ hδ_lt hδ' h_pin _ => hForce F hδ_lt hδ' h_pin)⟩

/-! ## The self-contained front-2 endpoint -/

/-- **Front 2, self-contained: the `(N)` fields on a horizon built from `hDim`
and `g` alone.**

`lowreg_solve_two` at the forcing floor `Kf = 1/(4C)` — `C` the dimension-three
fibre constant of `hs2_opBound_at_two` — composed with `lowreg_joint_of_re`.
The floor is exactly what the endpoint's `hfloor` needs after
`‖u.deriv‖ ≤ 2‖fHi‖`, and `lowreg_solve_two` meets it by folding
`lowregFloorHorizon g c Kf` into the horizon it reports.  So no size or horizon
obligation is left for the caller: it supplies only a contraction level `c`
between the reported coefficient bound `B2` and `1`, and a horizon below the
`T₀` reported for that `c`.

The two remaining inputs are the spatial frontier `lowreg_spatialMass` (through
`lowreg_forceJetMass` and `lowreg_allOrderJet`, whose `sorry` this theorem
transitively depends on) and `hRepr` (the order-free Ricci--DeTurck
representation block, brick B6). -/
theorem lowreg_joint_two (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (lowregNsec (I := I) (M := M) g S hδ_lt hδ +
            rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w) :
    ∃ B2 : ℝ, 0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (_hT : 0 < T) (_ : T ≤ T₀) (_hT1 : T ≤ 1),
            ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
                (g := g) (r := 0) (s := 2) (2 : ℝ) T)
                (F : ℝ → SmoothCcTensor g 0 2) (δ' : ℝ) (hδ_lt : δ' < 1)
                (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g (F t)) δ'),
              F 0 = 0 ∧
              (∀ t ∈ Set.Icc (0 : ℝ) T,
                SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
                  tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                    (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
              (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
                HasDerivWithinAt
                  (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
                  (F_RHS
                    (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t))
                      x v w)
                  (Set.Ici 0) t) ∧
              JointChartGramSmooth (I := I) T
                (fun t : ℝ =>
                  tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) := by
  obtain ⟨hC_pos, -⟩ := (hs2_opBound_at_two (I := I) (M := M) hDim g).choose_spec
  obtain ⟨ρ, δ, hρ, hδ0, hδ_le, hreal', B2, hB2, hsolve⟩ :=
    lowreg_solve_two (I := I) (M := M) hDim g
      (Kf := 1 / (4 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose))
      (div_pos one_pos (by linarith only [hC_pos]))
  refine ⟨B2, hB2, ?_⟩
  intro c hB2c hc1
  obtain ⟨T₀, hT₀, hpack⟩ := hsolve hB2c hc1
  refine ⟨T₀, hT₀, ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨f, hre⟩ := hpack hT hTT₀ hT1
  exact lowreg_joint_of_re (I := I) (M := M) hDim g F_RHS hRepr hρ hδ0 hδ_le
    hreal' hT hT1 f hre le_rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
