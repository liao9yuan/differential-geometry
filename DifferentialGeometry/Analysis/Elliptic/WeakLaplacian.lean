import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- A distributional upper bound for the Riemannian Laplacian on an open set. -/
structure IsLapLEDistribOn
    (g : SmoothRiemannianMetric I M) (u b : M → Real) (U : Set M) : Prop where
  isOpen : IsOpen U
  locInt_left : LocallyIntegrableOn u U
    (riemannianVolumeMeasure (I := I) (M := M) g)
  locInt_right : LocallyIntegrableOn b U
    (riemannianVolumeMeasure (I := I) (M := M) g)
  test_le : ∀ φ : C^∞⟮I, M; Real⟯,
    φ ∈ compactlySupportedSmoothFunctions I M →
    tsupport (φ : M → Real) ⊆ U →
    (∀ x : M, 0 ≤ φ x) →
    (∫ x, u x * Δ_g (I := I) g φ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)

namespace IsLapLEDistribOn

/-- A distributional Laplacian upper bound restricts to an open subset. -/
theorem mono
    {g : SmoothRiemannianMetric I M} {u b : M → Real} {U V : Set M}
    (h : IsLapLEDistribOn (I := I) g u b U)
    (hV : IsOpen V) (hVU : V ⊆ U) :
    IsLapLEDistribOn (I := I) g u b V where
  isOpen := hV
  locInt_left := h.locInt_left.mono_set hVU
  locInt_right := h.locInt_right.mono_set hVU
  test_le φ hφ hφV hφ_nonneg :=
    h.test_le φ hφ (hφV.trans hVU) hφ_nonneg

end IsLapLEDistribOn

omit [I.Boundaryless] in
private theorem int_mul_test
    {g : SmoothRiemannianMetric I M} {f : M → Real} {U : Set M}
    (hf : LocallyIntegrableOn f U
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U) :
    Integrable (fun x : M ↦ f x * φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  have hf_on : IntegrableOn f (tsupport (φ : M → Real))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf.integrableOn_compact_subset hφU hφ_cs
  have hmul_on : IntegrableOn (fun x : M ↦ f x * φ x)
      (tsupport (φ : M → Real))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf_on.mul_continuousOn φ.contMDiff.continuous.continuousOn hφ_cs
  exact (integrableOn_iff_integrable_of_support_subset
    ((support_mul_subset_right f (φ : M → Real)).trans
      (subset_tsupport (φ : M → Real)))).mp hmul_on

omit [SigmaCompactSpace M] in
private theorem lap_tsupp_subset
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; Real⟯) :
    tsupport (Δ_g (I := I) g φ) ⊆ tsupport (φ : M → Real) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_not
  have heq : (φ : M → Real) =ᶠ[nhds x] (fun _ : M ↦ (0 : Real)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx_not)
  have hφ_eta :
      (⟨(φ : M → Real), φ.contMDiff⟩ : C^∞⟮I, M; Real⟯) = φ := by
    apply ContMDiffMap.ext
    intro y
    rfl
  have hlap := Δ_g_congr_of_eventuallyEq (I := I) g φ.contMDiff
    (contMDiff_const : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M ↦ (0 : Real))) heq
  have hzero : Δ_g (I := I) g φ x = 0 := by
    rw [← hφ_eta, hlap]
    exact Δ_g_const (I := I) g 0 x
  exact hx hzero

omit [SigmaCompactSpace M] in
private theorem lap_hasCompSupp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M) :
    HasCompactSupport (Δ_g (I := I) g φ) := by
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  refine HasCompactSupport.of_support_subset_isCompact hφ_cs ?_
  exact (subset_tsupport _).trans (lap_tsupp_subset (I := I) g φ)

namespace IsLapLEDistribOn

/-- Distributional Laplacian upper bounds are closed under addition. -/
theorem add
    {g : SmoothRiemannianMetric I M} {u₁ u₂ b₁ b₂ : M → Real} {U : Set M}
    (h₁ : IsLapLEDistribOn (I := I) g u₁ b₁ U)
    (h₂ : IsLapLEDistribOn (I := I) g u₂ b₂ U) :
    IsLapLEDistribOn (I := I) g (u₁ + u₂) (b₁ + b₂) U where
  isOpen := h₁.isOpen
  locInt_left := h₁.locInt_left.add h₂.locInt_left
  locInt_right := h₁.locInt_right.add h₂.locInt_right
  test_le φ hφ hφU hφ_nonneg := by
    let ψ : C^∞⟮I, M; Real⟯ :=
      ⟨Δ_g (I := I) g φ, Δ_g_contMDiff (I := I) g φ⟩
    have hψ_cs : ψ ∈ compactlySupportedSmoothFunctions I M := by
      simpa only [ψ] using lap_hasCompSupp (I := I) g φ hφ
    have hψU : tsupport (ψ : M → Real) ⊆ U := by
      simpa only [ψ] using (lap_tsupp_subset (I := I) g φ).trans hφU
    have hu₁Δ_int : Integrable
        (fun x : M ↦ u₁ x * Δ_g (I := I) g φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [ψ] using int_mul_test (I := I) h₁.locInt_left ψ hψ_cs hψU
    have hu₂Δ_int : Integrable
        (fun x : M ↦ u₂ x * Δ_g (I := I) g φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [ψ] using int_mul_test (I := I) h₂.locInt_left ψ hψ_cs hψU
    have hb₁φ_int : Integrable (fun x : M ↦ b₁ x * φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      int_mul_test (I := I) h₁.locInt_right φ hφ hφU
    have hb₂φ_int : Integrable (fun x : M ↦ b₂ x * φ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      int_mul_test (I := I) h₂.locInt_right φ hφ hφU
    calc
      (∫ x, (u₁ + u₂) x * Δ_g (I := I) g φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          (∫ x, u₁ x * Δ_g (I := I) g φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, u₂ x * Δ_g (I := I) g φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        simpa only [Pi.add_apply, add_mul] using integral_add hu₁Δ_int hu₂Δ_int
      _ ≤ (∫ x, b₁ x * φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, b₂ x * φ x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        add_le_add (h₁.test_le φ hφ hφU hφ_nonneg)
          (h₂.test_le φ hφ hφU hφ_nonneg)
      _ = ∫ x, (b₁ + b₂) x * φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        symm
        simpa only [Pi.add_apply, add_mul] using integral_add hb₁φ_int hb₂φ_int

end IsLapLEDistribOn

/-- A smooth pointwise Laplacian upper bound gives the corresponding
distributional upper bound. -/
theorem lapDistrib_of_smooth
    (g : SmoothRiemannianMetric I M)
    {u b : M → Real} {U : Set M}
    (hU : IsOpen U)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (hb : LocallyIntegrableOn b U
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (hub : ∀ x ∈ U, Δ_g (I := I) g ⟨u, hu⟩ x ≤ b x) :
    IsLapLEDistribOn (I := I) g u b U := by
  letI : IsLocallyFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  refine ⟨hU, hu.continuous.locallyIntegrable.locallyIntegrableOn U, hb, ?_⟩
  intro φ hφ hφU hφ_nonneg
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  have huΔφ_int : Integrable
      (fun x : M ↦ u x * Δ_g (I := I) g φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    exact (hu.continuous.mul
      (Δ_g_contMDiff (I := I) g φ).continuous).integrable_of_hasCompactSupport
        (lap_hasCompSupp (I := I) g φ hφ).mul_left
  have hφΔu_int : Integrable
      (fun x : M ↦ φ x * Δ_g (I := I) g ⟨u, hu⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    exact (φ.contMDiff.continuous.mul
      (Δ_g_contMDiff (I := I) g ⟨u, hu⟩).continuous).integrable_of_hasCompactSupport
        hφ_cs.mul_right
  have hbφ_int : Integrable (fun x : M ↦ b x * φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    int_mul_test (I := I) hb φ hφ hφU
  have hgreen := green_second_of_supp (I := I) g
    (f := u) (h := (φ : M → Real)) hu φ.contMDiff (Or.inr hφ_cs)
  have hφ_eta :
      (⟨(φ : M → Real), φ.contMDiff⟩ : C^∞⟮I, M; Real⟯) = φ := by
    apply ContMDiffMap.ext
    intro y
    rfl
  rw [hφ_eta] at hgreen
  rw [integral_sub huΔφ_int hφΔu_int] at hgreen
  have hgreen_eq :
      (∫ x, u x * Δ_g (I := I) g φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, φ x * Δ_g (I := I) g ⟨u, hu⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    sub_eq_zero.mp hgreen
  have hpoint : ∀ x : M,
      φ x * Δ_g (I := I) g ⟨u, hu⟩ x ≤ b x * φ x := by
    intro x
    by_cases hx : x ∈ U
    · calc
        φ x * Δ_g (I := I) g ⟨u, hu⟩ x ≤ φ x * b x :=
          mul_le_mul_of_nonneg_left (hub x hx) (hφ_nonneg x)
        _ = b x * φ x := mul_comm _ _
    · have hφx : φ x = 0 := by
        by_contra hne
        exact hx (hφU (subset_tsupport _ (Function.mem_support.mpr hne)))
      simp only [hφx, zero_mul, mul_zero]
      exact le_rfl
  calc
    (∫ x, u x * Δ_g (I := I) g φ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, φ x * Δ_g (I := I) g ⟨u, hu⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hgreen_eq
    _ ≤ ∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_mono_ae hφΔu_int hbφ_int (Filter.Eventually.of_forall hpoint)

end DifferentialGeometry
