import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegFatouIdent
import DifferentialGeometry.Analysis.Spectral.Intrinsic.GalerkinCompactness

/-!
# The Fatou closure of the order-one low-lane spectral mass, up to `σ = 3`

`lowregFatouPackAt` and its compatibility form `lowregFatouPack`
(`ShortTime/LowRegFatouIdent.lean`) deliver both halves of a Fatou argument for
the low solve `fLo` at one tuple of constants:

* the **convergence** — at every eigen-mode `i` and every `t ∈ [0,T]` the mode
  coordinates `lowregProjMode g₀ fseq N t i` of the projected sequence converge
  to `perModeConv λᵢ (timeModeCoeff fLo i) t`, the mode coordinate of the
  *limit* forcing;
* the **`N`-uniform bound** — the rung-3 energy bound
  `galerkinEnergy (eigenIdxFinset g₀ N) (lowregProjMode g₀ fseq N) 3 t ≤ Φ`,
  with the gate already discharged in the exact adapted package.

This file closes the two with `fatou_sq_mass`
(`Analysis/Spectral/Intrinsic/GalerkinCompactness.lean`) and passes from the
energy exponent `3` down to every `σ ≤ 3` by weight domination: the Sobolev
weights are `(1 + λᵢ)^σ` with `λᵢ ≥ 0`, so `(1 + λᵢ)^σ ≤ (1 + λᵢ)^3` for
`σ ≤ 3` — the same argument as the high-regularity mirror
`deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm`.

## Main result

* `lowregMassLowAt` — **the exact Fatou deliverable**: for every `σ ≤ 3` the
  `σ`-weighted spectral mass is summable and uniformly bounded, with no
  remaining absorption antecedent.
* `lowregMassLow` — the compatibility form: for every `σ ≤ 3` the
  `σ`-weighted spectral mass of the limit forcing's mode coordinates is
  summable and `t`-uniformly bounded on `[0,T]`, granted the rung's absorption
  gate (GAP-ADAPTH).

## Scope

The conclusion is *literally* the conclusion of `lowreg_loMass`
(`ShortTime/LowRegAllOrderJet.lean`) — same limit object
`perModeConv λᵢ (timeModeCoeff fLo i) t`, same weight, same summability and
bound — but only for `σ ≤ 3`.  The exact theorem removes the absorption gap;
it still does **not** close `lowreg_loMass`, which is stated for every real `σ`:
the remaining exponents need the order-one energy rungs above `3`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
/-- Convert a pointwise uniform projected energy bound at exponent `τ` into
the limiting spectral mass bound at every weaker exponent `σ`.  The projected
sequence and its modewise convergence are explicit, so no solve witness is
reselected by this adapter. -/
theorem lowregMassOfEnergy
    (g₀ : SmoothRiemannianMetric I M) {T σ τ Φ : ℝ}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hconv : ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => lowregProjMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)))
    (hστ : σ ≤ τ)
    (hΦ : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) τ t ≤ Φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Φ := by
  classical
  intro t ht
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i τ := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hστ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (lowregProjMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => lowregProjMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

/-- The `σ ≤ 3` spectral mass bound at one explicit adapted solve.  The stored
ordered rung certificate and calibrated absorption budget remove the generic
theorem's conditional gate, while all solve constants remain literally those
of `hlo`. -/
theorem lowregMassLowAt
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowSolve (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∀ σ : ℝ, σ ≤ 3 → ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤
          Cσ := by
  classical
  obtain ⟨fseq, hconv, Φ, hΦ⟩ :=
    lowregFatouPackAt (I := I) (M := M) g₀ hT hT1 fLo hlo
  intro σ hσ
  refine ⟨Φ, fun t ht => ?_⟩
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i 3 := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hσ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (lowregProjMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => lowregProjMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

/-- **The `σ ≤ 3` spectral mass of the order-one low-lane forcing.**

For a low solve `fLo` and every exponent `σ ≤ 3`, the `σ`-weighted spectral
mass `∑ᵢ (1 + λᵢ)^σ · (perModeConv λᵢ (timeModeCoeff fLo i) t)²` of the mode
coordinates of `fLo`'s own Duhamel trajectory is summable and bounded by a
constant independent of `t ∈ [0,T]`.

The proof is the Fatou closure of the identification package: the projected
sequence's mode coordinates converge to the limit's, they satisfy the rung-3
energy bound uniformly in `N`, and `(1 + λᵢ)^σ ≤ (1 + λᵢ)^3` for `σ ≤ 3`
because `1 ≤ 1 + λᵢ`.

**In this compatibility theorem the absorption gate remains explicit.**  The
statement hands out the rung's four constants `Ctop₂, Kr2, Kr1, Cδ` alongside
the class constants and asks the caller for
`Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1` at the package's own state radius
`R = lowregStateRad Ctop B1 ρ P`.  The exact theorem `lowregMassLowAt` above
instead consumes `IsAdaptedLowSolve`, whose producer-side calibration has
already discharged this former GAP-ADAPTH obligation.

**This is the `σ ≤ 3` instance of `lowreg_loMass`, not `lowreg_loMass`.**  The
limit object is the same, but the exponent range is not: `lowreg_loMass` is
stated for every real `σ` and stays open. -/
theorem lowregMassLow (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g₀ hT hT1 fLo) :
    ∃ Ctop B1 ρ P Ctop₂ Kr2 Kr1 Cδ : ℝ,
      0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Cδ ∧
      ∀ {ε : ℝ}, 0 < ε →
        Ctop₂ * Cδ + Kr2 * lowregStateRad Ctop B1 ρ P +
            Kr1 * lowregStateRad Ctop B1 ρ P + ε < 1 →
        ∀ σ : ℝ, σ ≤ 3 → ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
            ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤
              Cσ := by
  classical
  obtain ⟨Ctop, B1, ρ, P, fseq, hconv, Ctop₂, Kr2, Kr1, Cδ, h2, hr2, hr1, hcδ,
    hgate⟩ := lowregFatouPack (I := I) (M := M) hDim g₀ hT hT1 fLo hlo
  refine ⟨Ctop, B1, ρ, P, Ctop₂, Kr2, Kr1, Cδ, h2, hr2, hr1, hcδ, ?_⟩
  intro ε hε habs σ hσ
  obtain ⟨Φ, hΦ⟩ := hgate hε habs
  refine ⟨Φ, fun t ht => ?_⟩
  -- the `σ`-weight is dominated by the `3`-weight, since `1 ≤ 1 + λᵢ`
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i 3 := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hσ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (lowregProjMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => lowregProjMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
