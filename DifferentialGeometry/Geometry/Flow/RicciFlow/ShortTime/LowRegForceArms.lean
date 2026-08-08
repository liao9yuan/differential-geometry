import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSmoothBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegGalerkinSol
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifNZeroBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# The forcing arms along the order-one Galerkin trajectory

The order-one Galerkin system (`lowregGalSol`) reports its forcing through
`galTameForce`, which evaluates the *dense* nonlinearity `lowregNfun` at the
retracted spectral state `galTameStateC`.  A per-scale energy estimate has to
price that forcing against the covariant jets of a genuine smooth tensor, so it
first needs the state written as a smooth representative and the forcing written
as the canonical low-base action split.

This module supplies exactly that translation layer, in three steps.

* **The state is in the smooth core with a named representative.**
  `galCoreRep` is the retracted finite eigen-combination
  `(min 1 (R / ‖·‖)) • finiteEigenCombo g₀ S c`; `galCoreRep_eq` identifies its
  spectral embedding with `galTameStateC`, and `galState_core` records the
  resulting `smoothCore` membership.  No density or continuity input is used
  here: the representative is exhibited, not chosen.
* **The nonlinearity is evaluated on it.**  `galN_eval` runs the existing
  evaluation layer (`lowRegN_on_smooth`) at that representative, so the forcing
  along the trajectory is the genuine smooth Ricci--DeTurck nonlinearity
  `deTurckSmoothN g₀ g₀ 1 (symmS g₀ (galCoreRep …))`.
* **The forcing, minus its static seed, is the embedded arm sum.**  `galArmId`
  subtracts `𝒩(0)` — the same zero-state element the seed mass
  `lowRegSeedMass` and the `D`-field of `IsLowSolve` speak about — and rewrites
  the difference as `smoothCcToTensorHs g₀ 1 (A.a2 T + A.a1 T)` for the
  canonical low-base data `A = lowBaseData g₀ g₀ T`, `T = symmS g₀ (galCoreRep …)`.
  `galArmCap` carries the accompanying `C2` fibre cap with the constant hoisted
  out of the trajectory, in the shape `a2PerIdxLin`'s `hfib` binder consumes.
  `galForceArm` reads the whole package on a single Galerkin forcing
  coordinate, which is the form the ODE's right-hand side exposes.

## Inputs

Every statement takes the certificates of `IsLowSolve` directly — the fibre
threshold `0 ≤ δ ≤ 1/3` together with `δ < 1`, the metric realization bound
`hreal`, and continuity of the smooth core `coreN`.  Constants and certificates
precede the trajectory data `(S, c)` throughout, so a consumer destructures once
and applies per time.  `lowreg_proj_tendsto` now re-exports exactly these
certificates at its own bound constants, so a caller working on the projected
trajectory can feed that one package here without re-destructuring `IsLowSolve`
(which would produce an incomparable witness tuple).

The `lowBaseData` witness written here uses the ambient `hδ : δ < 1`; the
per-index ladder estimates (`a2PerIdxLin`, `a1PerIdxLin`) write the
definitionally equal `lt_of_le_of_lt hδ3 (by norm_num)` in the same slot, so the
two readings of `lowBaseData … .a2` are the same term.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The named smooth representative of a retracted Galerkin state -/

/-- **The smooth representative of the retracted Galerkin state.**

`galTameStateC g₀ 1 R S c` is the radial retraction, at the lower `H²` radius
`R`, of the spectral combination of the coefficient family `c` over the finite
mode set `S`.  Its smooth representative is the same retraction applied to the
genuine smooth finite eigen-combination `finiteEigenCombo g₀ S c`. -/
def galCoreRep (g₀ : SmoothRiemannianMetric I M) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    SmoothCcTensor g₀ 0 2 :=
  (min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀ S c (((1 : ℕ) : ℝ) + 2))‖)) •
    finiteEigenCombo (I := I) (M := M) g₀ S c

/-- The spectral embedding of `galCoreRep` is the retracted Galerkin state. -/
theorem galCoreRep_eq (g₀ : SmoothRiemannianMetric I M) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (galCoreRep (I := I) (M := M) g₀ R S c) =
      galTameStateC (I := I) (M := M) g₀ 1 R S c := by
  rw [galCoreRep, smoothCcToTensorHs_smul, ← finiteEigenComboHs_eq, galTameStateC]

/-- The retracted, symmetrized Galerkin representative retains its exact
radial scale in every spectral Sobolev norm.  This zero-safe form is used when
a homogeneous tensor estimate is transferred back to the unretracted modal
coefficients. -/
theorem galRepHs_scale (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ≤
      θ * Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
    (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  refine (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ σ _).trans ?_
  have hrep : galCoreRep (I := I) (M := M) g₀ R F c =
      θ • finiteEigenCombo (I := I) (M := M) g₀ F c := rfl
  rw [hrep, smoothCcToTensorHs_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ0]
  have hnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ =
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    rw [← finiteEigenComboHs_eq]
    rw [← Real.sqrt_sq (norm_nonneg _),
      finiteEigenCombo_spectral_normSq (I := I) (M := M)]
    rfl
  rw [hnorm]

/-- The retracted, symmetrized Galerkin representative is a contraction at
every spectral Sobolev order.  In particular, the coefficient of a highest
derivative term is not enlarged by an order-dependent comparison constant. -/
theorem galRepHs_le (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ≤
      Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
  refine (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ σ _).trans ?_
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
    (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  have hθ1 : θ ≤ 1 := by
    dsimp only [θ]
    exact min_le_left _ _
  have hrep : galCoreRep (I := I) (M := M) g₀ R F c =
      θ • finiteEigenCombo (I := I) (M := M) g₀ F c := rfl
  rw [hrep, smoothCcToTensorHs_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ0]
  have hnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ =
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    rw [← finiteEigenComboHs_eq]
    rw [← Real.sqrt_sq (norm_nonneg _),
      finiteEigenCombo_spectral_normSq (I := I) (M := M)]
    rfl
  calc
    θ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ ≤
        1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ :=
      mul_le_mul_of_nonneg_right hθ1 (norm_nonneg _)
    _ = _ := by rw [one_mul, hnorm]

/-- The smooth representative of the retracted Galerkin state stays in the
lower `H²` ball of radius `R`; this is `galTameStateC_mem` read through
`galCoreRep_eq`. -/
theorem galCoreRep_ball (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (galCoreRep (I := I) (M := M) g₀ R S c))‖ ≤ R := by
  rw [galCoreRep_eq]
  exact galTameStateC_mem (I := I) (M := M) g₀ 1 hR S c

/-- **The Galerkin trajectory lives in the smooth core.**  Every retracted
Galerkin state is a point of `smoothCore g₀ R`, with `galCoreRep` as witness. -/
theorem galState_core (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    (⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
        galTameStateC_mem (I := I) (M := M) g₀ 1 hR S c⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) ∈
      smoothCore (I := I) (M := M) g₀ R :=
  ⟨galCoreRep (I := I) (M := M) g₀ R S c,
    galCoreRep_eq (I := I) (M := M) g₀ R S c⟩

/-! ### Transport of the fibre certificates to the trajectory -/

/-- The metric realization bound at the symmetrized trajectory
representative.  This is the `hδg` slot of `lowData_split`, `a2PerIdxLin` and
`a1PerIdxLin` along the Galerkin trajectory. -/
theorem galRepFib (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 ≤ R)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R S c))) δ :=
  hreal _ (symm_h2_of_state (I := I) (M := M) g₀
    (galCoreRep (I := I) (M := M) g₀ R S c)
    (galCoreRep_ball (I := I) (M := M) g₀ hR S c))

/-- The metric realization bound at the zero perturbation.  This is the `hδZ`
slot of `lowData_split`, `a2PerIdxLin` and `a1PerIdxLin`. -/
theorem lowregFibZero (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 ≤ R)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ := by
  refine hreal (0 : SmoothCcTensor g₀ 0 2) ?_
  rw [smoothCcToTensorHs_zero, norm_zero]
  exact hR

/-! ### The forcing along the trajectory -/

/-- **The dense nonlinearity on the Galerkin trajectory is the genuine smooth
one.**  Evaluated at a retracted Galerkin state, `lowRegN` is the order-one
spectral embedding of the smooth Ricci--DeTurck remainder at the symmetrized
representative `symmS g₀ (galCoreRep …)`.  This is `lowRegN_on_smooth` at the
representative supplied by `galCoreRep_eq`; `lowRegSeedMass` is the same
pattern at the zero state. -/
theorem galN_eval (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
        ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
          galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
        (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) := by
  have hsub : (⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
        galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) =
      ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (galCoreRep (I := I) (M := M) g₀ R S c),
        galCoreRep_ball (I := I) (M := M) g₀ hR.le S c⟩ :=
    Subtype.ext (galCoreRep_eq (I := I) (M := M) g₀ R S c).symm
  rw [hsub]
  exact lowRegN_on_smooth (I := I) (M := M) g₀ g₀ hR hδ hreal hcore
    (galCoreRep (I := I) (M := M) g₀ R S c)
    (galCoreRep_ball (I := I) (M := M) g₀ hR.le S c)

/-- **The trajectory forcing, minus its static seed, is the embedded arm sum.**

Along the order-one Galerkin trajectory the difference between the
nonlinearity at a retracted Galerkin state and the nonlinearity at the zero
state is the order-one spectral embedding of the canonical low-base action
split `A.a2 T + A.a1 T`, with `T = symmS g₀ (galCoreRep g₀ R S c)` and
`A = lowBaseData g₀ g₀ T`.  The zero-state element is the one
`lowRegSeedMass` bounds, so the seed handle composes without transport.

The arms are exactly the objects the per-index ladder estimates
`a2PerIdxLin` and `a1PerIdxLin` bound, at the same `lowBaseData`. -/
theorem galArmId (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        ((lowBaseData (I := I) (M := M) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).a2
            (I := I) (M := M)
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) +
          (lowBaseData (I := I) (M := M) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).a1
            (I := I) (M := M)
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c))) := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  calc lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩
      = deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
            (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) -
          deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
            (0 : SmoothCcTensor g₀ 0 2) hδ
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal) := by
        rw [galN_eval (I := I) (M := M) g₀ hR hδ hreal hcore S c,
          nZero_eq_static (I := I) (M := M) g₀ g₀ hR hδ hreal hcore,
          ← deTurckSmoothN_zero (I := I) (M := M) g₀ g₀ 1 hδ
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)]
    _ = smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) -
            deTurckSmoothRemainder (I := I) g₀ g₀
              (0 : SmoothCcTensor g₀ 0 2) hδ
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)) :=
        deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub (I := I) (M := M)
          g₀ g₀ 1 _ _ hδ _ hδ _
    _ = _ :=
        congrArg (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ))
          (hsplit _
            (DeTurckRemainderTameLipschitz.ccTensorBilin_symmS_symm
              (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
            hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).1

/-- **The `C2` fibre cap along the trajectory, with the constant hoisted.**

`lowData_split`'s second clause, read at the symmetrized Galerkin
representative: one constant `Cδ`, independent of the mode set and of the
coefficient family — hence of the Galerkin level — caps the complete
second-order coefficient of every state on the trajectory.  This is exactly the
`hfib` binder of `a2PerIdxLin`. -/
theorem galArmCap (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((lowBaseData (I := I) (M := M) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR hreal)).C2.toSection x) ≤
          Cδ ^ 2 := by
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  refine ⟨K * (δ / (1 - δ) ^ 2),
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro S c x
  exact (hsplit _
    (DeTurckRemainderTameLipschitz.ccTensorBilin_symmS_symm (I := I) (M := M)
      g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
    hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR hreal S c)
    (lowregFibZero (I := I) (M := M) g₀ hR hreal)).2 x

open scoped Classical in
/-- **The Galerkin forcing coordinate as seed plus arms.**

The right-hand side of the `V_S` Galerkin ODE reports its forcing through
`galTameForce`; on the truncation this coordinate is the corresponding
eigen-coefficient of the static seed `𝒩(0)` plus that of the embedded arm sum,
and it vanishes off the truncation.  Combined with `lowRegSeedMass` for the
seed and with `a2PerIdxLin` / `a1PerIdxLin` for the arms, this is the per-mode
form a Galerkin energy estimate pairs against.

The hypotheses are the fields of `IsLowSolve` at the six numbers: `δ < 1`,
`0 ≤ δ ≤ 1/3`, the realization bound at radius `P`, and continuity of the
smooth core `coreN` at the very realization `lowregNfun` uses. -/
theorem galForceArm (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galTameForce (I := I) (M := M) g₀ 1
        (lowregStateRad_pos hCtop hB1 hρ hP).le
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal) S c i =
      if i ∈ S then
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowregStateRad_pos hCtop hB1 hρ hP).le⟩).coeff i +
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowBaseData (I := I) (M := M) g₀ g₀
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowregStateRad Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (lowregFibZero (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).a2 (I := I) (M := M)
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)) +
              (lowBaseData (I := I) (M := M) g₀ g₀
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowregStateRad Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (lowregFibZero (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).a1 (I := I) (M := M)
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)))).coeff i
      else 0 := by
  classical
  have harm := galArmId (I := I) (M := M) g₀
    (lowregStateRad_pos hCtop hB1 hρ hP) hδ hδ0 hδ3
    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal) hcore S c
  have hval : lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨galTameStateC (I := I) (M := M) g₀ 1
            (lowregStateRad Ctop B1 ρ P) S c,
          galTameStateC_mem (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le S c⟩ =
      lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le⟩ +
        smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          ((lowBaseData (I := I) (M := M) g₀ g₀
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)) hδ
                (galRepFib (I := I) (M := M) g₀
                  (lowregStateRad_pos hCtop hB1 hρ hP).le
                  (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                (lowregFibZero (I := I) (M := M) g₀
                  (lowregStateRad_pos hCtop hB1 hρ hP).le
                  (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal))).a2 (I := I) (M := M)
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀
                  (lowregStateRad Ctop B1 ρ P) S c)) +
            (lowBaseData (I := I) (M := M) g₀ g₀
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)) hδ
                (galRepFib (I := I) (M := M) g₀
                  (lowregStateRad_pos hCtop hB1 hρ hP).le
                  (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                (lowregFibZero (I := I) (M := M) g₀
                  (lowregStateRad_pos hCtop hB1 hρ hP).le
                  (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal))).a1 (I := I) (M := M)
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀
                  (lowregStateRad Ctop B1 ρ P) S c))) :=
    sub_eq_iff_eq_add'.mp harm
  rw [galTameForce_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, hval, tensorHs.add_coeff]
  · rw [if_neg hi, if_neg hi]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
