import DifferentialGeometry.External.DeGiorgi.Localization

/-!
# Restriction of Scalar-Source Weak Equations

This module localizes an actual scalar-source weak equation from an open set to
an arbitrary smaller open set.  The test function is extended by zero, while
the coefficient and the solution witness use the existing native restriction
operations.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private noncomputable def extendTestWit
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    {v : E → ℝ} (hv0 : DeGiorgi.MemH01 v W)
    (hv : DeGiorgi.MemW1pWitness 2 v W) :
    DeGiorgi.MemW1pWitness 2 (W.indicator v) Omega := by
  let hv0Real : DeGiorgi.MemW01p (ENNReal.ofReal (2 : ℝ)) v W := by
    simpa using hv0
  let hvReal : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v W :=
    { memLp := by simpa using hv.memLp
      weakGrad := hv.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using hv.weakGrad_component_memLp i
      isWeakGrad := hv.isWeakGrad }
  let hExtRaw : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (W.indicator v) Set.univ :=
    DeGiorgi.zeroExtend_memW1pWitness_p (d := d) hW
      (p := 2) (by norm_num) hv0Real hvReal
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  simpa [htwo] using
    hExtRaw.restrict hOmega (by intro x hx; simp)

omit [NeZero d] in
@[simp] private theorem cast_wit_grad
    {p q : ENNReal} {Omega : Set E} {f : E → ℝ}
    (hpq : p = q) (h : DeGiorgi.MemW1pWitness p f Omega) :
    (Eq.mp (by cases hpq; rfl :
      DeGiorgi.MemW1pWitness p f Omega =
        DeGiorgi.MemW1pWitness q f Omega) h).weakGrad = h.weakGrad := by
  cases hpq
  rfl

@[simp] private theorem extendTestWit_grad
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    {v : E → ℝ} (hv0 : DeGiorgi.MemH01 v W)
    (hv : DeGiorgi.MemW1pWitness 2 v W) (x : E) (i : Fin d) :
    (extendTestWit (d := d) hOmega hW hv0 hv).weakGrad x i =
      W.indicator (fun y => hv.weakGrad y i) x := by
  let hv0Real : DeGiorgi.MemW01p (ENNReal.ofReal (2 : ℝ)) v W := by
    simpa using hv0
  let hvReal : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v W :=
    { memLp := by simpa using hv.memLp
      weakGrad := hv.weakGrad
      weakGrad_component_memLp := by
        intro j
        simpa using hv.weakGrad_component_memLp j
      isWeakGrad := hv.isWeakGrad }
  let hExtRaw : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (W.indicator v) Set.univ :=
    DeGiorgi.zeroExtend_memW1pWitness_p (d := d) hW
      (p := 2) (by norm_num) hv0Real hvReal
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  let hExtReal : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (W.indicator v) Omega :=
    hExtRaw.restrict hOmega (by intro y hy; simp)
  have hcast :
      (extendTestWit (d := d) hOmega hW hv0 hv).weakGrad =
        hExtReal.weakGrad := by
    unfold extendTestWit
    simpa [htwo, hExtRaw, hExtReal] using
      cast_wit_grad htwo hExtReal
  have hraw : hExtReal.weakGrad x i =
      W.indicator (fun y => hv.weakGrad y i) x := by
    simp [hExtReal, hExtRaw, DeGiorgi.zeroExtend_memW1pWitness_p,
      DeGiorgi.MemW1pWitness.restrict, hvReal]
  simpa [hcast] using hraw

private theorem testExt_memH01
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    (hsub : W ⊆ Omega) {v : E → ℝ}
    (hv0 : DeGiorgi.MemH01 v W) :
    DeGiorgi.MemH01 (W.indicator v) Omega := by
  classical
  rcases hv0 with
    ⟨hv_mem, hw, phi, hphi_smooth, hphi_compact, hphi_sub,
      hphi_fun, hphi_grad⟩
  let hv0' : DeGiorgi.MemH01 v W :=
    ⟨hv_mem, hw, phi, hphi_smooth, hphi_compact, hphi_sub,
      hphi_fun, hphi_grad⟩
  let hExt : DeGiorgi.MemW1pWitness 2 (W.indicator v) Omega :=
    extendTestWit (d := d) hOmega hW hv0' hw
  refine ⟨hExt.memW1p, hExt, phi, hphi_smooth, hphi_compact, ?_, ?_, ?_⟩
  · intro n
    exact (hphi_sub n).trans hsub
  · have hEq :
        (fun n => eLpNorm (fun x => phi n x - W.indicator v x) 2
          ((volume : Measure E).restrict Omega)) =
        fun n => eLpNorm (fun x => phi n x - v x) 2
          ((volume : Measure E).restrict W) := by
      funext n
      have hFn :
          (fun x => phi n x - W.indicator v x) =
            W.indicator (fun x => phi n x - v x) := by
        funext x
        by_cases hx : x ∈ W
        · simp [hx]
        · have hphi_zero : phi n x = 0 :=
            DeGiorgi.zero_outside_of_tsupport_subset (hphi_sub n) hx
          simp [hx, hphi_zero]
      rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := (volume : Measure E).restrict Omega) hW.measurableSet]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hEq]
    exact hphi_fun
  · intro i
    have hEq :
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
            hExt.weakGrad x i) 2
          ((volume : Measure E).restrict Omega)) =
        fun n => eLpNorm
          (fun x => (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i) 2
          ((volume : Measure E).restrict W) := by
      funext n
      have hFn :
          (fun x => (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
            hExt.weakGrad x i) =
            W.indicator (fun x =>
              (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
                hw.weakGrad x i) := by
        funext x
        by_cases hx : x ∈ W
        · simp [hExt, extendTestWit_grad, hx]
        · have hdx :
              (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) = 0 :=
            DeGiorgi.fderiv_apply_zero_outside_of_tsupport_subset
              (hf := hphi_smooth n) (hsub := hphi_sub n) hx i
          simp [hExt, extendTestWit_grad, hx, hdx]
      rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := (volume : Measure E).restrict Omega) hW.measurableSet]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hEq]
    exact hphi_grad i

private theorem bilin_restrict_eq
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    (hsub : W ⊆ Omega) (A : DeGiorgi.EllipticCoeff d Omega)
    {u v : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hv0 : DeGiorgi.MemH01 v W)
    (hv : DeGiorgi.MemW1pWitness 2 v W) :
    DeGiorgi.bilinFormOfCoeff (A.restrict hsub)
        (hu.restrict hW hsub) hv =
      DeGiorgi.bilinFormOfCoeff A hu
        (extendTestWit (d := d) hOmega hW hv0 hv) := by
  let hExt : DeGiorgi.MemW1pWitness 2 (W.indicator v) Omega :=
    extendTestWit (d := d) hOmega hW hv0 hv
  let A' : DeGiorgi.EllipticCoeff d W := A.restrict hsub
  let hu' : DeGiorgi.MemW1pWitness 2 u W := hu.restrict hW hsub
  let small : E → ℝ := fun x =>
    DeGiorgi.bilinFormIntegrandOfCoeff A' hu' hv x
  have hEq : (W.indicator small) =ᵐ[(volume : Measure E).restrict Omega]
      fun x => DeGiorgi.bilinFormIntegrandOfCoeff A hu hExt x := by
    filter_upwards with x
    by_cases hx : x ∈ W
    · have hgrad : hExt.weakGrad x = hv.weakGrad x := by
        apply PiLp.ext
        intro i
        simp [hExt, extendTestWit_grad, hx]
      simp [A', hu', small, hExt, hgrad, DeGiorgi.EllipticCoeff.restrict,
        DeGiorgi.MemW1pWitness.restrict, hx,
        DeGiorgi.bilinFormIntegrandOfCoeff]
    · have hgrad : hExt.weakGrad x = 0 := by
        apply PiLp.ext
        intro i
        simp [hExt, extendTestWit_grad, hx]
      simp [A', hu', small, hExt, hgrad, DeGiorgi.EllipticCoeff.restrict,
        DeGiorgi.MemW1pWitness.restrict, hx,
        DeGiorgi.bilinFormIntegrandOfCoeff]
  calc
    DeGiorgi.bilinFormOfCoeff A' hu' hv =
        ∫ x in W, small x ∂((volume : Measure E).restrict Omega) := by
          simp [DeGiorgi.bilinFormOfCoeff, small,
            Measure.restrict_restrict_of_subset hsub]
    _ = ∫ x, W.indicator small x ∂((volume : Measure E).restrict Omega) := by
          symm
          exact integral_indicator hW.measurableSet
    _ = ∫ x, DeGiorgi.bilinFormIntegrandOfCoeff A hu hExt x
          ∂((volume : Measure E).restrict Omega) := integral_congr_ae hEq
    _ = DeGiorgi.bilinFormOfCoeff A hu hExt := rfl

/-- An actual scalar-source `H₀¹` weak equation restricts to every smaller
open subset, using the native restricted coefficient and solution witness. -/
theorem srcEq_restrict
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    (hsub : W ⊆ Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f v : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hweak : ∀ z, DeGiorgi.MemH01 z Omega →
      ∀ hz : DeGiorgi.MemW1pWitness 2 z Omega,
        DeGiorgi.bilinFormOfCoeff A hu hz =
          ∫ x in Omega, f x * z x ∂(volume : Measure E))
    (hv0 : DeGiorgi.MemH01 v W)
    (hv : DeGiorgi.MemW1pWitness 2 v W) :
    DeGiorgi.bilinFormOfCoeff (A.restrict hsub)
        (hu.restrict hW hsub) hv =
      ∫ x in W, f x * v x ∂(volume : Measure E) := by
  let hExt : DeGiorgi.MemW1pWitness 2 (W.indicator v) Omega :=
    extendTestWit (d := d) hOmega hW hv0 hv
  have hExt0 : DeGiorgi.MemH01 (W.indicator v) Omega :=
    testExt_memH01 (d := d) hOmega hW hsub hv0
  calc
    DeGiorgi.bilinFormOfCoeff (A.restrict hsub)
        (hu.restrict hW hsub) hv =
        DeGiorgi.bilinFormOfCoeff A hu hExt :=
      bilin_restrict_eq (d := d) hOmega hW hsub A hu hv0 hv
    _ = ∫ x in Omega, f x * W.indicator v x
          ∂(volume : Measure E) := hweak _ hExt0 hExt
    _ = ∫ x, W.indicator (fun y => f y * v y) x
          ∂((volume : Measure E).restrict Omega) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ W <;> simp [hx]
    _ = ∫ x in W, f x * v x ∂((volume : Measure E).restrict Omega) :=
      integral_indicator hW.measurableSet
    _ = ∫ x in W, f x * v x ∂(volume : Measure E) := by
      rw [Measure.restrict_restrict_of_subset hsub]

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
