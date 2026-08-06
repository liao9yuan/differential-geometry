import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegAdaptedSolve
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegGalerkinIdent

/-!
# The rung-3 energy bound along the projected forcing sequence

`lowregRung3` (`ShortTime/LowRegRungThree.lean`) bounds the `H³` Galerkin
energy of *any* coefficient trajectory that solves the order-one `V_N` system.
This file instantiates it at the trajectory the identification package
`lowreg_proj_tendsto` / `lowreg_projMode_tendsto` already hands out — the mode
coordinates

  `lowregProjMode g₀ fseq N t i = perModeConv λᵢ (timeModeCoeff (fseq N) i) t`

of the *projected* forcing sequence.  No ODE uniqueness is needed: the rung's
trajectory is universally quantified, so it suffices to verify its three
trajectory hypotheses on this concrete family.

## Main results

* `lowregProjMode` — the mode coordinates of the projected Duhamel field.
* `lowregProjMode_zero`, `lowregProjMode_cont` — the rung's `hUinit`/`hUcont`.
* `lowregFieldCombo` — the spatial identification: almost everywhere the
  Duhamel field of `fseq N` **is** the finite spectral combination of its own
  mode coordinates.  This is what turns the a.e. state ball into the `hc`
  hypothesis of `galTameForce_eq`.
* `lowregForceMode` — the a.e. per-mode forcing identity
  `timeModeCoeff (fseq N) i =ᵐ galTameForce … (lowregProjMode …) i`.
* `lowregForceCont` — the Galerkin forcing is continuous in time along the
  projected mode coordinates (`tame_lip_balls` at the package's constants,
  then `galTameForce_contOn`).
* `lowregModeDeriv` — the rung's `hUderiv`: the per-mode scalar ODE.
* `lowregFatouE3At` / `lowregFatouE3` — **the endpoint**: the `N`-uniform `H³`
  energy bound along
  the projected sequence, i.e. Fatou's `hbound`.
* `lowregL2H3` — the time-integrated `H³` energy bound `∫₀^T E₃ ≤ ((1+T)b)²`
  for a forcing of size `b`, which **discharges** the honest input `hL2H3` of
  `lowregFatouE3`.
* `lowregFatouPackAt` / `lowregFatouPack` — the exact or compatibility endpoint
  fed from the corresponding projected-mode theorem, with `hL2H3` already
  discharged: Fatou's `hconv` and `hbound` from one call.

The a.e.-to-everywhere crossing happens once, in `lowregModeDeriv`: the forcing
is only pinned down almost everywhere, but `perModeConv_timeL2_congr` converts
an a.e. identity of forcings into a *pointwise* identity of convolutions on
`[0,T]`, and `Set.IccExtend` supplies the globally continuous representative
that `perModeConv_hasDerivAt` demands.

Historically, the compatibility theorem `lowregFatouE3` exposed two honest
inputs: the rung's absorption gate (the former GAP-ADAPTH), which stays an
explicit hypothesis of its produced `∀ ε` statement, and the time-integrated
energy bound `hL2H3`.  The second is **discharged** here by `lowregL2H3` — the
projected maximal-regularity replay — so compatibility endpoint
`lowregFatouPack` remains conditional on the gate alone.  The active exact
endpoint `lowregFatouPackAt` consumes `IsAdaptedLowSolve`, whose stored budget
discharges it.
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
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## The projected mode coordinates -/

/-- **The mode coordinates of the projected Duhamel field.**  For the forcing
sequence `fseq` produced by `lowreg_proj_tendsto`, this is the eigen-coordinate
family of the associated maximal-regularity solution: by
`timeModeCoeff_eq_perModeConv_forcing` the `i`-th coordinate of the Duhamel
field agrees almost everywhere with the scalar convolution
`perModeConv λᵢ (timeModeCoeff (fseq N) i)`, and it is that convolution — a
function defined at *every* time — which is taken as the definition. -/
def lowregProjMode (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N : ℕ) (t : ℝ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
    (fun u => (timeModeCoeff (I := I) (M := M) (fseq N) i) u) t

omit [BoundarylessManifold I M] in
/-- The projected mode coordinates start at zero: the rung's `hUinit`. -/
@[simp] theorem lowregProjMode_zero (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    lowregProjMode (I := I) (M := M) g₀ fseq N 0 i = 0 :=
  perModeConv_zero_left _ _

omit [BoundarylessManifold I M] in
/-- The projected mode coordinates are continuous on the closed slab: the
rung's `hUcont`. -/
theorem lowregProjMode_cont (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 ≤ T)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => lowregProjMode (I := I) (M := M) g₀ fseq N t i)
      (Set.Icc (0 : ℝ) T) :=
  continuousOn_perModeConv_timeL2 _ _ hT

/-! ## The spatial identification -/

/-- **The Duhamel field is the finite spectral combination of its own mode
coordinates.**  The forcing is a value of the truncated nonlinearity, so its
Duhamel field is fixed by `Π_N` (`projField_fixed`); a `Π_N`-fixed state is the
spectral combination over `eigenIdxFinset g₀ N` of its coefficients, and those
coefficients are almost everywhere the per-mode convolutions.  Only finitely
many coordinates are involved, so the finitely many a.e. identities intersect.

This is the producer of the `hc` hypothesis of `galTameForce_eq`: an a.e. bound
on the Duhamel field becomes an a.e. bound on `finiteEigenComboHs` of the mode
coordinates, which is the state the Galerkin forcing evaluates. -/
theorem lowregFieldCombo (g₀ : SmoothRiemannianMetric I M) {R T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun (u t)) :
    ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t =
        finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (lowregProjMode (I := I) (M := M) g₀ fseq N t) (((1 : ℕ) : ℝ) + 2) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set fld := maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) with hfld
  -- the field is fixed by the spectral truncation at the gained regularity
  have hfix : timeL2EigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) T N fld
      = fld := projField_fixed (I := I) (M := M) g₀ 1 hT hT1 N (fseq N) u hnem
  have hproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) T N fld)
      =ᵐ[timeMeasure T] fun t =>
        spatialEigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) N (fld t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hpt : (fun t => fld t) =ᵐ[timeMeasure T] fun t =>
      spatialEigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) N (fld t) := by
    rw [hfix] at hproj
    exact hproj
  -- the finitely many coordinate identities
  have hmodes : ∀ᵐ t ∂(timeMeasure T),
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        (fld t).coeff i = lowregProjMode (I := I) (M := M) g₀ fseq N t i := by
    refine Filter.eventually_all_finset _ |>.2 (fun i _ => ?_)
    exact timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M)
      (h_compact := h_compact) hT hT1 (fseq N) i
  filter_upwards [hpt, hmodes] with t h1 h2
  rw [h1, spatialEigenProj_apply]
  refine tensorHs.ext (funext fun j => ?_)
  rw [finiteEigenComboHs_coeff, finiteEigenComboHs_coeff]
  by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · rw [if_pos hj, if_pos hj, h2 j hj]
  · rw [if_neg hj, if_neg hj]

/-! ## The a.e. forcing identity -/

/-- **The projected forcing is the Galerkin forcing of the projected mode
coordinates.**  Almost everywhere in time the `i`-th coordinate of `fseq N` is
the `i`-th slot of `galTameForce` evaluated at `lowregProjMode g₀ fseq N t`:
the a.e. Nemytskii identity supplies the truncated nonlinearity, the a.e. state
ball makes the `aeSetLift` branch the honest one, `lowregFieldCombo` identifies
the state as a finite spectral combination, and `galTameForce_eq` says the
Galerkin retraction is inert there. -/
theorem lowregForceMode (g₀ : SmoothRiemannianMetric I M) {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N)) t))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ⇑(timeModeCoeff (I := I) (M := M) (fseq N) i) =ᵐ[timeMeasure T]
      fun t => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t) i := by
  classical
  set fld := maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) with hfld
  set lift := aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR) fld
    with hlift
  have hcombo := lowregFieldCombo (I := I) (M := M) g₀ hT hT1 N (Nfun := Nfun)
    fseq lift hnem
  have hcoe := aeSetLift_coe_ae (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR)
    fld hball
  filter_upwards [timeModeCoeff_coeFn (I := I) (M := M) (fseq N) i, hnem, hball,
    hcombo, hcoe] with t h1 h2 h3 h4 h5
  -- the lifted state is the finite spectral combination of the mode coordinates
  have hstate : ‖galLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t) (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
    rw [← h4]; exact h3
  have hsub : lift t =
      (⟨finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t) (((1 : ℕ) : ℝ) + 2),
        hstate⟩ : lowerState (I := I) (M := M) g₀ 1 R) :=
    Subtype.ext (h5.trans h4)
  rw [h1, h2, hsub]
  simp only [projNfun, spatialProj_coeff]
  rw [galTameForce_eq (I := I) (M := M) g₀ 1 hR Nfun
    (eigenIdxFinset (I := I) (M := M) g₀ N) hstate i]

/-! ## Time continuity of the Galerkin forcing -/

/-- **The Galerkin forcing is continuous in time along the projected mode
coordinates.**  The three-arm tame estimate at the package's own constants
gives, through `tame_lip_balls`, a Lipschitz constant for `lowregNfun` on the
truncation ball `galTameBall`, which is exactly the gate `galTameForce_contOn`
asks for; the truncation bound `1 + λᵢ ≤ N + 1` is `mem_eigenIdxFinset`.

Stated for an arbitrary continuous coefficient family, since that is all the
proof uses. -/
theorem lowregForceCont (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowregOuterRad Ctop ρ P *
            ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    {T : ℝ} (N : ℕ) (c : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hc : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => c t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => galTameForce (I := I) (M := M) g₀ 1
        (lowregStateRad_pos hCtop hB1 hρ hP).le
        (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (c t) i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  have hRpos : 0 < lowregStateRad Ctop B1 ρ P :=
    lowregStateRad_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowregOuterRad Ctop ρ P :=
    (lowregOuterRad_pos hCtop hρ hP).le
  have hκ0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hκ : ∀ j ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      1 + TensorEigenIdx.lambda (I := I) (M := M) j ≤ (N : ℝ) + 1 := by
    intro j hj
    rw [mem_eigenIdxFinset] at hj
    linarith
  obtain ⟨K, hK⟩ :=
    tame_lip_balls
      (X := tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
      (D := lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P))
      (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) id isometry_id rfl
      (galLowView (I := I) (M := M) g₀ 1) Ctop B0 B1
      (lowregOuterRad Ctop ρ P) hCtop hB0 hB1 hQnn htame
      (Real.sqrt ((N : ℝ) + 1) * lowregStateRad Ctop B1 ρ P)
  exact galTameForce_contOn (I := I) (M := M) g₀ 1 hRpos.le
    (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
    (eigenIdxFinset (I := I) (M := M) g₀ N) hκ0 hκ hK c hc i

/-! ## The per-mode ODE -/

omit [BoundarylessManifold I M] in
/-- **The rung's `hUderiv` for the projected mode coordinates.**  The Galerkin
forcing along the mode coordinates is continuous on `[0,T]` and agrees almost
everywhere with the mode coordinate of the forcing, so its `Set.IccExtend` is a
globally continuous representative; `perModeConv_hasDerivAt` differentiates the
convolution of that representative, and `perModeConv_timeL2_congr` identifies
the convolution with `lowregProjMode` pointwise on `[0,T]`.

At an interior initial time `t < T` the slab `[0,T]` is a neighbourhood of `t`
within `Set.Ici t`, which is what carries the identification across to the
right-derivative the rung states. -/
theorem lowregModeDeriv (g₀ : SmoothRiemannianMetric I M) {R T : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hFcont : ContinuousOn (fun t => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t) i) (Set.Icc (0 : ℝ) T))
    (hFmode : ⇑(timeModeCoeff (I := I) (M := M) (fseq N) i) =ᵐ[timeMeasure T]
      fun t => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t) i)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => lowregProjMode (I := I) (M := M) g₀ fseq N s i)
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
          lowregProjMode (I := I) (M := M) g₀ fseq N t i +
        galTameForce (I := I) (M := M) g₀ 1 hR Nfun
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (lowregProjMode (I := I) (M := M) g₀ fseq N t) i)
      (Set.Ici t) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
  set G : ℝ → ℝ := fun s => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
    (eigenIdxFinset (I := I) (M := M) g₀ N)
    (lowregProjMode (I := I) (M := M) g₀ fseq N s) i with hG
  set F : ℝ → ℝ := Set.IccExtend hT.le (fun p : Set.Icc (0 : ℝ) T => G p.1) with hF
  have hFc : Continuous F := Continuous.Icc_extend' hFcont.restrict
  have hFeq : ∀ s ∈ Set.Icc (0 : ℝ) T, F s = G s := fun s hs =>
    Set.IccExtend_of_mem hT.le _ hs
  -- the forcing coordinate agrees a.e. with the continuous representative
  have hae : (fun s => (timeModeCoeff (I := I) (M := M) (fseq N) i) s)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] F := by
    filter_upwards [hFmode, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with s hs hsmem
    rw [hs, hFeq s hsmem]
  -- hence the convolutions agree pointwise on the slab
  have hconv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      lowregProjMode (I := I) (M := M) g₀ fseq N s i = perModeConv lam F s :=
    fun s hs => perModeConv_timeL2_congr lam hae hs
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hderiv := perModeConv_hasDerivAt lam hFc t
  rw [hFeq t htIcc, ← hconv t htIcc] at hderiv
  have hval : G t - lam * lowregProjMode (I := I) (M := M) g₀ fseq N t i =
      -lam * lowregProjMode (I := I) (M := M) g₀ fseq N t i + G t := by ring
  rw [hval] at hderiv
  -- the slab is a neighbourhood of `t` inside `Set.Ici t`
  have hmem : Set.Icc (0 : ℝ) T ∈ 𝓝[Set.Ici t] t := by
    have h1 : Set.Iio T ∈ 𝓝[Set.Ici t] t :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
    refine Filter.mem_of_superset (Filter.inter_mem h1 self_mem_nhdsWithin) ?_
    rintro s ⟨hs1, hs2⟩
    exact ⟨le_trans ht.1 hs2, hs1.le⟩
  refine (hderiv.hasDerivWithinAt (s := Set.Ici t)).congr_of_eventuallyEq ?_
    (hconv t htIcc)
  filter_upwards [hmem] with s hs using hconv s hs

/-! ## The endpoint: Fatou's `N`-uniform bound -/

/-- **The `N`-uniform `H³` energy bound along the projected sequence.**

This is `lowregRung3` instantiated at the trajectory `lowregProjMode g₀ fseq`,
i.e. Fatou's `hbound`.  Its hypotheses are, in order: the dimension, the nine
nonlinearity certificates of the identification package
(`lowreg_proj_tendsto`, destructured once by the caller at *one* tuple of
constants), the three per-`N` conjuncts of that package which the trajectory
block consumes (a.e. state ball and a.e. Nemytskii identity), and the honest
input `hL2H3` — the time-integrated `H³` energy bound, whose producer is the
projected maximal-regularity replay.

The conclusion keeps the rung's own shape, so the absorption gate
`Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1` remains an explicit hypothesis of the
produced `∀ ε` statement: nothing in the Fatou stage discharges it. -/
theorem lowregFatouE3At
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P T Bd Ctop₂ Kr2 Kr1 Kcap ε : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowregOuterRad Ctop ρ P *
            ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤ Bd)
    (hrung : IsRung3Ord (I := I) (M := M) g₀ Ctop₂ Kr2 Kr1 Kcap)
    (hε : 0 < ε)
    (habs : Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
      Kr2 * lowregStateRad Ctop B1 ρ P +
      Kr1 * lowregStateRad Ctop B1 ρ P + ε < 1) :
    ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  classical
  set U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    lowregProjMode (I := I) (M := M) g₀ fseq with hU
  -- the trajectory block
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun N i _ => lowregProjMode_cont (I := I) (M := M) g₀ hT.le fseq N i
  have hUinit : ∀ N i, U N 0 i = 0 :=
    fun N i => lowregProjMode_zero (I := I) (M := M) g₀ fseq N i
  have hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun s => U N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le
            (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
        (Set.Ici t) t := by
    intro N t ht i _
    refine lowregModeDeriv (I := I) (M := M) g₀ hT
      (lowregStateRad_pos hCtop hB1 hρ hP).le N fseq i ?_ ?_ ht
    · exact lowregForceCont (I := I) (M := M) g₀ g₀ hδ hCtop hB0 hB1 hρ hP hreal
        htame N (U N) (fun j _ => hUcont N j (by assumption)) i
    · exact lowregForceMode (I := I) (M := M) g₀
        (lowregStateRad_pos hCtop hB1 hρ hP).le hT hT1 N fseq (hball N) (hnem N) i
  -- the primitive `Pr` of the `H³` energy, from the time-integrated bound
  set EE : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 p.1) with hEE
  have hEEc : ∀ N, Continuous (EE N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 (hUcont N)).restrict
  have hEEnn : ∀ N, ∀ s : ℝ, 0 ≤ EE N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEEeq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  set Pr : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE N s with hPr
  have hPrHas : ∀ N, ∀ t : ℝ, HasDerivAt (Pr N) (EE N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEEc N).intervalIntegrable 0 t)
      (hEEc N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEEc N).continuousAt
  have hPr0 : ∀ N, Pr N 0 = 0 := fun N => intervalIntegral.integral_same
  have hPrnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Pr N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEEnn N s)
  have hPrcont : ∀ N, ContinuousOn (Pr N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hPrHas N t).continuousAt)).continuousOn
  have hPrderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (Pr N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) (Set.Ici t) t := by
    intro N t ht
    have h := hPrHas N t
    rw [hEEeq N t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hPrbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, Pr N t ≤ Bd := by
    intro N t ht
    have hTint : ∫ s in (0 : ℝ)..T, EE N s = ∫ s, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s ∂(timeMeasure T) := by
      rw [intervalIntegral.integral_congr
        (g := fun s => galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s)
        (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEEeq N s hs),
        intervalIntegral.integral_of_le hT.le, timeMeasure,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hsplit : Pr N t + ∫ s in t..T, EE N s = ∫ s in (0 : ℝ)..T, EE N s :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hEEc N).intervalIntegrable 0 t) ((hEEc N).intervalIntegrable t T)
    have hrest : 0 ≤ ∫ s in t..T, EE N s :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => hEEnn N s)
    have hfin := hL2H3 N
    rw [← hTint] at hfin
    linarith
  exact hrung.2.2.2.2 hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore hUcont hUderiv
    hUinit hPr0 hPrnn hPrcont hPrderiv hPrbd hε habs

/-- Compatibility form of `lowregFatouE3At`.  It selects one ordered rung
certificate and retains the former conditional absorption interface. -/
theorem lowregFatouE3 (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ Ctop B0 B1 ρ P T Bd : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowregOuterRad Ctop ρ P *
            ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤ Bd) :
    ∃ Ctop₂ Kr2 Kr1 Cδ : ℝ, 0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Cδ ∧
      ∀ {ε : ℝ}, 0 < ε →
        Ctop₂ * Cδ + Kr2 * lowregStateRad Ctop B1 ρ P +
            Kr1 * lowregStateRad Ctop B1 ρ P + ε < 1 →
        ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hrung⟩ :=
    lowregRung3Pack (I := I) (M := M) hDim g₀
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  refine ⟨Ctop₂, Kr2, Kr1, Cδ, hrung.1, hrung.2.1, hrung.2.2.1,
    mul_nonneg hrung.2.2.2.1 (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro ε hε habs
  exact lowregFatouE3At (I := I) (M := M) g₀ hT hT1 hδ hδ0 hδ3 hCtop hB0
    hB1 hρ hP hreal hcore htame fseq hball hnem hL2H3 hrung hε
    (by simpa only [Cδ] using habs)

/-! ## The time-integrated energy: discharging `hL2H3` -/

/-- **The time-integrated `H³` Galerkin energy of the projected trajectory is
controlled by the size of its forcing.**  This is the honest input `hL2H3` of
`lowregFatouE3`, discharged.

Almost everywhere the Duhamel field of `fseq N` *is* the finite spectral
combination of its own mode coordinates (`lowregFieldCombo`), and the squared
`H³` norm of such a combination is exactly the weighted finite sum
`∑_{i ∈ F} (1 + λᵢ)³ cᵢ²` (`finiteEigenCombo_spectral_normSq`), i.e. the
Galerkin energy at `σ = 3`.  Integrating in time turns the left-hand side into
the squared time-`L²` norm of the field, and maximal regularity with zero
initial datum bounds that by `(1 + T)‖fseq N‖`
(`norm_maxRegDuhamelSolField_zero_le`).

No integrability hypothesis appears: the integrand is almost everywhere the
squared pointwise norm of an `L²` element, and `timeMeasure T` is *by
definition* Lebesgue measure restricted to `[0,T]`, so the Bochner integral
against it is literally the set integral of `norm_sq_eq_integral`.  This is why
the Bochner form — rather than an interval integral — is the shape `hL2H3`
carries. -/
theorem lowregL2H3 (g₀ : SmoothRiemannianMetric I M) {R T b : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun (u t))
    (hnorm : ‖fseq N‖ ≤ b) :
    ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤
      ((1 + T) * b) ^ 2 := by
  classical
  set fld := maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) with hfld
  have hexp : ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) := by norm_num
  -- the pointwise identification: the energy is the squared `H³` norm
  have hae : (fun t => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N)
      (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t)
      =ᵐ[timeMeasure T] fun t => ‖fld t‖ ^ 2 := by
    filter_upwards [lowregFieldCombo (I := I) (M := M) g₀ hT hT1 N
      (Nfun := Nfun) fseq u hnem] with t ht
    rw [ht, finiteEigenCombo_spectral_normSq, hexp]
    simp only [galerkinEnergy, tensorSobolevWeight]
  rw [MeasureTheory.integral_congr_ae hae]
  -- the time integral of the squared pointwise norm is the squared time-`L²` norm
  have hint : ∫ t, ‖fld t‖ ^ 2 ∂(timeMeasure T) = ‖fld‖ ^ 2 :=
    (norm_sq_eq_integral fld).symm
  rw [hint]
  have hle : ‖fld‖ ≤ (1 + T) * b :=
    le_trans (norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) (g₀ := g₀)
      hT hT1 (fseq N))
      (mul_le_mul_of_nonneg_left hnorm (by linarith))
  nlinarith [norm_nonneg fld, hle]

/-- The calibrated Fatou package at one explicit adapted solve.  The stored
ordered rung continuation is invoked with the package's already-proved budget,
so no conditional absorption gate remains. -/
theorem lowregFatouPackAt
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowSolve (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => lowregProjMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  have hsol := hlo.toIsLowSolveAt
  obtain ⟨fseq, _hconv, hmode, hpack⟩ :=
    lowreg_projMode_at (I := I) (M := M) g₀ hT hT1 fLo hsol
  obtain ⟨ε, hε, habs⟩ := hlo.absorb
  refine ⟨fseq, hmode, ?_⟩
  refine lowregFatouE3At (I := I) (M := M) g₀ hT hT1 hsol.hδ hsol.hδ0
    hsol.hδ3 hsol.hCtop hsol.hB0 hsol.hB1 hsol.hρ hsol.hP hsol.hreal
    hsol.hcore hsol.htame fseq (fun N => (hpack N).2.1)
    (fun N => (hpack N).2.2.1) (Bd := ((1 + T) *
      (lowregStateRad Ctop B1 ρ P / 4)) ^ 2) (fun N => ?_)
    hlo.toIsRung3Ord hε habs
  exact lowregL2H3 (I := I) (M := M) g₀ hT hT1 N fseq _ ((hpack N).2.2.1)
    ((hpack N).2.2.2.2.2)

/-- **The Fatou stage's input package.**  `lowregFatouE3` fed directly from
`lowreg_projMode_tendsto`, with the honest input `hL2H3` already discharged by
`lowregL2H3`: for a low solve there is a projected forcing sequence whose mode
coordinates converge, at every mode and every time of the closed slab, to those
of the limit forcing, and which carries the rung's `N`-uniform `H³` energy
bound subject only to the absorption gate.

The two conjuncts are exactly Fatou's `hconv` and `hbound`.  The bound the
discharge supplies is `((1+T)·R/4)²` at the package's own state radius `R`,
read off the package's forcing ball `‖fseq N‖ ≤ R/4`; it is `N`-free, which is
all Fatou needs. -/
theorem lowregFatouPack (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g₀ hT hT1 fLo) :
    ∃ (Ctop B1 ρ P : ℝ)
      (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => lowregProjMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∃ Ctop₂ Kr2 Kr1 Cδ : ℝ, 0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Cδ ∧
        ∀ {ε : ℝ}, 0 < ε →
          Ctop₂ * Cδ + Kr2 * lowregStateRad Ctop B1 ρ P +
              Kr1 * lowregStateRad Ctop B1 ρ P + ε < 1 →
          ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N)
              (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  obtain ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    B0, hB0, hcont, htame, fseq, _hconv, hmode, hpack⟩ :=
    lowreg_projMode_tendsto (I := I) (M := M) g₀ hT hT1 fLo hlo
  refine ⟨Ctop, B1, ρ, P, fseq, hmode, ?_⟩
  refine lowregFatouE3 (I := I) (M := M) hDim g₀ hT hT1 hδ hδ0 hδ3 hCtop hB0 hB1
    hρ hP hreal hcore htame fseq (fun N => (hpack N).2.1)
    (fun N => (hpack N).2.2.1) (Bd := ((1 + T) *
      (lowregStateRad Ctop B1 ρ P / 4)) ^ 2) (fun N => ?_)
  exact lowregL2H3 (I := I) (M := M) g₀ hT hT1 N fseq _ ((hpack N).2.2.1)
    ((hpack N).2.2.2.2.2)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
