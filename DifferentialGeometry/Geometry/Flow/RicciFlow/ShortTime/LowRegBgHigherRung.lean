import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgRungClosure

/-!
# Higher-rung mass at an arbitrary fixed DeTurck background

This module begins the fixed-background higher-rung bridge.  The Sobolev
scale, eigenbasis, Galerkin state, and energy remain based at `g₀`, while the
smooth DeTurck remainder is evaluated against the independent metric `g_bg`.
-/

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The all-order smooth remainder package at an arbitrary fixed DeTurck
background, transported to the finite spectral arm of a retracted Galerkin
state.  A common fifth-order cap prices the lower coefficient, while the
highest-order coefficient remains `κ * δ / (1 - δ)²`. -/
theorem galArmMassHmBg (g₀ g_bg : SmoothRiemannianMetric I M)
    {κ R δ R5 : ℝ} (hhm : IsHmRungOrdBg (I := I) (M := M) g₀ g_bg κ)
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (m : ℕ) :
    ∃ Kmid : ℝ, 0 ≤ Kmid ∧
      ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2) ≤ R5 →
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            ((galArmVecBg (I := I) (M := M) g₀ g_bg hR hδ hreal F c).coeff i) ^ 2) ≤
          κ * (δ / (1 - δ) ^ 2) *
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 2) *
                  (c i) ^ 2) +
            Kmid * Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
                (c i) ^ 2) := by
  classical
  obtain ⟨Clower, hClower, hladder⟩ := hhm.2 hδ0 hδ3
  refine ⟨Clower R5 m, hClower R5 m, ?_⟩
  intro F c hE5
  let T : SmoothCcTensor g₀ 0 2 :=
    symmS (I := I) (M := M) g₀
      (galCoreRep (I := I) (M := M) g₀ R F c)
  have hsym : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x u v =
        ccTensorBilin (I := I) g₀ T x v u := by
    dsimp only [T]
    exact DeTurckRemainderTameLipschitz.ccTensorBilin_symmS_symm
      (I := I) (M := M) g₀ _
  have hδg : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ := by
    dsimp only [T]
    exact galRepFib (I := I) (M := M) g₀ hR hreal F c
  have hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ :=
    lowregFibZero (I := I) (M := M) g₀ hR hreal
  have hT5 :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ 5 T‖ ≤ R5 := by
    dsimp only [T]
    exact (galRepHs_le (I := I) (M := M) g₀ 5 hR F c).trans hE5
  have hb := hladder T hsym hδg hδZ hT5 m
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g_bg
  rw [(hsplit T hsym hδ3 hδ0 hδg hδZ).1] at hb
  have htop := galRepHs_le (I := I) (M := M) g₀ ((m : ℝ) + 2) hR F c
  have hmid := galRepHs_le (I := I) (M := M) g₀ ((m : ℝ) + 1) hR F c
  have hrate : 0 ≤ δ / (1 - δ) ^ 2 := div_nonneg hδ0 (sq_nonneg _)
  have hα : 0 ≤ κ * (δ / (1 - δ) ^ 2) := mul_nonneg hhm.1 hrate
  have hb' := hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left htop hα)
    (mul_le_mul_of_nonneg_left hmid (hClower R5 m)))
  have hmass := cc_partial_le_norm (I := I) (M := M) g₀ 2 (m : ℝ)
    ((lowBaseData (I := I) (M := M) g₀ g_bg T hδ hδg hδZ).a2
        (I := I) (M := M) T +
      (lowBaseData (I := I) (M := M) g₀ g_bg T hδ hδg hδZ).a1
        (I := I) (M := M) T) F
  refine le_trans (le_trans (Real.sqrt_le_sqrt hmass)
    (le_of_eq (Real.sqrt_sq (norm_nonneg _)))) ?_
  exact hb'

/-- Every energy rung `6 + k` is uniformly bounded on a fixed-background
rung-five trajectory.  All higher scales close directly from the common
`H⁵` cap; they do not recursively consume one another. -/
theorem lowregHighRungsBg
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    {T κ ε : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap : ℝ)
    (hsol : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap)
    {fseq : ℕ → timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (hpath : IsRung5PathBg (I := I) (M := M) g₀ g_bg K
      u gforce hsol fseq)
    (hhm : IsHmRungOrdBg (I := I) (M := M) g₀ g_bg κ)
    (hε : 0 < ε)
    (habs : κ * (K.threshold / (1 - K.threshold) ^ 2) + ε < 1) :
    ∀ k : ℕ, ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N)
        (6 + (k : ℝ)) t ≤ Φ := by
  classical
  let δ : ℝ := K.threshold
  let Ctop : ℝ := K.top
  let B1 : ℝ := K.slope
  let ρ : ℝ := K.outer
  let P : ℝ := K.realize
  change κ * (δ / (1 - δ) ^ 2) + ε < 1 at habs
  obtain ⟨Φ5, hE5⟩ := hpath.2.2.2.2
  let R5 : ℝ := Real.sqrt (max Φ5 0)
  have hE5cap : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Real.sqrt (galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 5 t) ≤ R5 := by
    intro N t ht
    dsimp only [R5]
    exact Real.sqrt_le_sqrt ((hE5 N t ht).trans (le_max_left _ _))
  have hRpos : 0 < lowregStateRad Ctop B1 ρ P :=
    lowregStateRad_pos hsol.hCtop hsol.hB1 hsol.hρ hsol.hP
  let hmassPack : ∀ k : ℕ, ∃ Kmid : ℝ, 0 ≤ Kmid ∧
      ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2) ≤ R5 →
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((5 + k : ℕ) : ℝ) *
            ((galArmVecBg (I := I) (M := M) g₀ g_bg hRpos.le hsol.hδ
              (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
                (ρ := ρ) hsol.hP.le hsol.hreal) F c).coeff i) ^ 2) ≤
          κ * (δ / (1 - δ) ^ 2) *
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i
                  (((5 + k : ℕ) : ℝ) + 2) * (c i) ^ 2) +
            Kmid * Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i
                (((5 + k : ℕ) : ℝ) + 1) * (c i) ^ 2) := fun k =>
    galArmMassHmBg (I := I) (M := M) g₀ g_bg hhm hRpos.le hsol.hδ hsol.hδ0 hsol.hδ3
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
        (ρ := ρ) hsol.hP.le hsol.hreal) (5 + k)
  let Kmid : ℕ → ℝ := fun k => (hmassPack k).choose
  have hKmid : ∀ k, 0 ≤ Kmid k := fun k => (hmassPack k).choose_spec.1
  have hmass : ∀ k : ℕ,
      ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2) ≤ R5 →
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((5 + k : ℕ) : ℝ) *
            ((galArmVecBg (I := I) (M := M) g₀ g_bg hRpos.le hsol.hδ
              (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
                (ρ := ρ) hsol.hP.le hsol.hreal) F c).coeff i) ^ 2) ≤
          κ * (δ / (1 - δ) ^ 2) *
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i
                  (((5 + k : ℕ) : ℝ) + 2) * (c i) ^ 2) +
            Kmid k * Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i
                (((5 + k : ℕ) : ℝ) + 1) * (c i) ^ 2) :=
    fun k => (hmassPack k).choose_spec.2
  obtain ⟨Cseed, hCseed, hseed⟩ := lowRegSeedMass (I := I) (M := M) g₀ g_bg
    hRpos hsol.hδ
    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
      (ρ := ρ) hsol.hP.le hsol.hreal) hsol.hcore
  let α : ℝ := κ * (δ / (1 - δ) ^ 2)
  have hα : 0 ≤ α := by
    dsimp only [α]
    exact mul_nonneg hhm.1 (div_nonneg hsol.hδ0 (sq_nonneg _))
  have hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i (6 + (k : ℝ)) *
            (lowregProjMode (I := I) (M := M) g₀ fseq N t i *
              galTameForce (I := I) (M := M) g₀ 1 hRpos.le
                (lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
                  hsol.hρ hsol.hP hsol.hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N)
                (lowregProjMode (I := I) (M := M) g₀ fseq N t) i) ≤
        (2 * α + ε) * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (lowregProjMode (I := I) (M := M) g₀ fseq N)
            (6 + (k : ℝ) + 1) t +
          (Kmid k ^ 2 / ε) * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (lowregProjMode (I := I) (M := M) g₀ fseq N)
            (6 + (k : ℝ)) t +
          2 * Cseed (6 + k) *
            Real.sqrt (galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N)
              (lowregProjMode (I := I) (M := M) g₀ fseq N)
              (6 + (k : ℝ)) t) := by
    intro N k t ht
    have hsplit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        galTameForce (I := I) (M := M) g₀ 1 hRpos.le
            (lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
              hsol.hρ hsol.hP hsol.hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (lowregProjMode (I := I) (M := M) g₀ fseq N t) i =
          (galArmVecBg (I := I) (M := M) g₀ g_bg hRpos.le hsol.hδ
            (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hsol.hP.le hsol.hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (lowregProjMode (I := I) (M := M) g₀ fseq N t)).coeff i +
          (lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
            hsol.hρ hsol.hP hsol.hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i := by
      intro i hi
      rw [galForceArmBg (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hδ0 hsol.hδ3
        hsol.hCtop hsol.hB1 hsol.hρ hsol.hP hsol.hreal hsol.hcore
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t) i, if_pos hi]
      exact add_comm _ _
    have hstatRaw := hseed (6 + k) (eigenIdxFinset (I := I) (M := M) g₀ N)
    have hstat : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        tensorSobolevWeight (I := I) (M := M) i (6 + (k : ℝ)) *
          ((lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
            hsol.hρ hsol.hP hsol.hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i) ^ 2 ≤
          Cseed (6 + k) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using hstatRaw
    have hladder :
        Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((6 + (k : ℝ)) - 1) *
            ((galArmVecBg (I := I) (M := M) g₀ g_bg hRpos.le hsol.hδ
              (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
                (ρ := ρ) hsol.hP.le hsol.hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N)
              (lowregProjMode (I := I) (M := M) g₀ fseq N t)).coeff i) ^ 2) ≤
            α * Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
              tensorSobolevWeight (I := I) (M := M) i ((6 + (k : ℝ)) + 1) *
                (lowregProjMode (I := I) (M := M) g₀ fseq N t i) ^ 2) +
              Kmid k * Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
                tensorSobolevWeight (I := I) (M := M) i (6 + (k : ℝ)) *
                  (lowregProjMode (I := I) (M := M) g₀ fseq N t i) ^ 2) := by
      have hm := hmass k (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t)
        (hE5cap N t (Set.Ico_subset_Icc_self ht))
      dsimp only [α]
      rw [show (6 + (k : ℝ)) - 1 = (((5 + k : ℕ) : ℝ)) by push_cast; ring,
        show (6 + (k : ℝ)) + 1 = (((5 + k : ℕ) : ℝ)) + 2 by push_cast; ring,
        show (6 + (k : ℝ)) = (((5 + k : ℕ) : ℝ)) + 1 by push_cast; ring]
      exact hm
    have hres := two_mul_sum_ladder_le (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (6 + (k : ℝ))
      (lowregProjMode (I := I) (M := M) g₀ fseq N t)
      (fun i => (galArmVecBg (I := I) (M := M) g₀ g_bg hRpos.le hsol.hδ
        (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1)
          (ρ := ρ) hsol.hP.le hsol.hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t)).coeff i)
      (fun i => (lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
        hsol.hρ hsol.hP hsol.hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩).coeff i)
      (galTameForce (I := I) (M := M) g₀ 1 hRpos.le
        (lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
          hsol.hρ hsol.hP hsol.hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N t))
      (hCseed (6 + k)) hε hsplit hladder hstat
    unfold galerkinEnergy
    exact hres
  refine galerkin_energy_uniform_bound_perScale (I := I) (M := M)
    (g := g₀) (r := 0) (s₀ := 2)
    (U := lowregProjMode (I := I) (M := M) g₀ fseq)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g₀ 1 hRpos.le
      (lowregNfun (I := I) (M := M) g₀ g_bg hsol.hδ hsol.hCtop hsol.hB1
        hsol.hρ hsol.hP hsol.hreal)
      (eigenIdxFinset (I := I) (M := M) g₀ N)
      (lowregProjMode (I := I) (M := M) g₀ fseq N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g₀ N)
    (T := T) (σ₀ := 6) (Cδ := 2 * α + ε)
    (Cmid := fun k => Kmid k ^ 2 / ε)
    (seed := fun k => 2 * Cseed (6 + k)) (B0 := fun _ => 0)
    (by dsimp only [α] at habs ⊢; nlinarith)
    (fun k => div_nonneg (sq_nonneg _) hε.le)
    hpath.2.1 hpath.2.2.1 hclosure ?_
  intro N k
  unfold galerkinEnergy
  have hz : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      tensorSobolevWeight (I := I) (M := M) i (6 + (k : ℝ)) *
        lowregProjMode (I := I) (M := M) g₀ fseq N 0 i ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hpath.2.2.2.1 N i]
    ring
  rw [hz]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
