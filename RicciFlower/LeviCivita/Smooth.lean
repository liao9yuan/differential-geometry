import RicciFlower.LeviCivita.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smoothness frontier for the Levi-Civita connection

This file is intentionally RicciFlower-only.  Do not import the external
external geometry namespace here.

The previous attempt transferred smoothness from the external synthetic
`KoszulCov` construction.  That was the wrong dependency direction for this
project.  The intended proof of smoothness for `leviCivitaConnectionOfMetric`
should be built from the local-frame/Koszul coefficient route inside
`RicciFlower`, using the existing coordinate-frame Christoffel and tensor
regularity APIs.
-/

noncomputable section

namespace RicciFlower
namespace LeviCivita

open Bundle
open Realized
open Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- RicciFlower-only record of the already proved geometric Levi-Civita
predicate for the Koszul-defined connection.

The smoothness theorem itself is deliberately not asserted here until it is
proved from the in-tree local-frame/Koszul coefficient API. -/
theorem leviCivitaConnectionOfMetric_isLeviCivita_smoothFile
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g :=
  leviCivitaConnectionOfMetric_isLeviCivita (I := I) g

/-! ## Metric coordinate smoothness

The Christoffel formula in `Torsion.lean` reduces smoothness of the
Levi-Civita coefficients to smoothness of:

* coordinate-frame metric components `g_{ij}`;
* their coordinate directional derivatives;
* inverse-metric components `g^{ij}`.

This section discharges the first two directly from `g.contMDiff`. The inverse
metric is the remaining nontrivial layer: it should be obtained from the
smoothness of inversion on continuous linear maps, not assumed from a real
coordinate model space.
-/

private theorem extDerivFun_apply_contMDiffAt_of_section
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) x₀ := by
  rw [contMDiffAt_infty]
  intro n
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt Real p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(Real, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(Real, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := X)
          (x₀ := x₀)
          (by simp [e])).mp hX
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt Real p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hp
    simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(Real, Real) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt Real (f x₀)).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(Real, Real) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (f p)) (achart Real (f x₀)) (f p) = (1 : Real →L[Real] Real) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
        e.symmL Real p := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := Real) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL Real p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p)
  rw [htarget, hsource]
  change (mfderiv I 𝓘(Real, Real) f p) (X p) =
    (mfderiv I 𝓘(Real, Real) f p) (e.symmL Real p (Xcoord p))
  rw [hcancel]

/-- Coordinate-frame metric components are smooth at the chart center. -/
theorem metric_coordinateFrame_component_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        g.inner p (coordinateFrameAt (I := I) x₀ i p)
          (coordinateFrameAt (I := I) x₀ j p)) x₀ := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hi :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ i p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) i
  have hj :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ j p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun p : M =>
          (⟨p,
            g.inner p (coordinateFrameAt (I := I) x₀ i p)
              (coordinateFrameAt (I := I) x₀ j p)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x₀ :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hj
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

/-- Coordinate directional derivatives of metric components are smooth at the
chart center. -/
theorem metric_coordinateFrame_component_directional_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        extDerivFun (I := I)
          (fun q : M =>
            g.inner q (coordinateFrameAt (I := I) x₀ i q)
              (coordinateFrameAt (I := I) x₀ j q))
          p (coordinateFrameAt (I := I) x₀ a p)) x₀ := by
  have hf := metric_coordinateFrame_component_contMDiffAt
    (I := I) g x₀ i j
  have ha :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ a p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) a
  exact extDerivFun_apply_contMDiffAt_of_section
    (I := I) (f := fun q : M =>
      g.inner q (coordinateFrameAt (I := I) x₀ i q)
        (coordinateFrameAt (I := I) x₀ j q))
    (X := coordinateFrameAt (I := I) x₀ a) hf ha

/-! ## Fixed-chart metric flat map

The inverse metric components should be proved smooth by applying
`ContinuousLinearMap.inverse` to this fixed-chart flat map.  This keeps the
argument over an arbitrary finite-dimensional complete model space `E`, rather
than choosing `E = Real^n`.
-/

private noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  ((metricFlatEquiv (I := I) g x₀).trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

private theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w = g.inner x₀ v w := by
  change ((metricFlatEquiv (I := I) g x₀) v) w = g.inner x₀ v w
  rw [metricFlatEquiv_apply]

/-- The metric flat map represented in the tangent trivialization centered at
`x₀`, viewed over the model chart target. -/
noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  (trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
      ⟨(extChartAt I x₀).symm y, g.inner ((extChartAt I x₀).symm y)⟩).2

private theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) := by
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  ext v w
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀ x₀ x₀ x₀
        (g.inner x₀) v) w =
      ((metricFlatContinuousEquiv (I := I) g x₀) v) w
  have hxT :
      x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simp
  have hxDual :
      x₀ ∈ (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  simp [metricFlatContinuousEquiv, hom_trivializationAt,
    Trivialization.continuousLinearMap_apply]
  have hL :
      (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := x₀) (mem_chart_source H x₀)]
    ext z
    exact (tangentBundleCore I M).coordChange_self (achart H x₀) x₀
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x₀) z
  have hsymm (z : E) :
      (trivializationAt E (TangentSpace I) x₀).symm x₀ z = z := by
    change (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ z = z
    rw [hL]
    rfl
  rw [hsymm v, hsymm w]
  rfl

private theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The fixed-chart metric flat map is smooth on the model chart at the center. -/
theorem metricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hcoord :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2) x₀ := 
    by
      rw [contMDiffAt_totalSpace] at hg
      simpa [e] using hg.2
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => (e ⟨p, g.inner p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt
      (x := extChartAt I x₀ x₀) hsymm
  exact hcomp.contDiffWithinAt

/-- The inverse metric flat map is smooth in the fixed model chart. -/
theorem inverseMetricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact
    (metricFlatModelInChart_center_isInvertible (I := I) g x₀).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt
        (x := extChartAt I x₀ x₀)
        (metricFlatModelInChart_contDiffWithinAt (I := I) g x₀)

/-- Fixed-chart inverse metric coefficients are smooth model functions. -/
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis Real E).coord l))))
      (Set.range I) (extChartAt I x₀ x₀) := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv := inverseMetricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  simpa [εk, εl] using (contDiffWithinAt_const (c := εk)).clm_apply happ

private theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (Module.finBasis Real E).coord i
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord j))) =
      (Module.finBasis Real E).coord j
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i))) := by
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  rw [hInv]
  calc
    (Module.finBasis Real E).coord i (A.symm (ε j))
        = (ε i) (A.symm (ε j)) := rfl
    _ = (A (A.symm (ε i))) (A.symm (ε j)) := by
          rw [A.apply_symm_apply]
    _ = g.inner x₀ (A.symm (ε i)) (A.symm (ε j)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = g.inner x₀ (A.symm (ε j)) (A.symm (ε i)) := by
          exact g.symm x₀ (A.symm (ε i)) (A.symm (ε j))
    _ = (A (A.symm (ε j))) (A.symm (ε i)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = (ε j) (A.symm (ε i)) := by
          rw [A.apply_symm_apply]
    _ = (Module.finBasis Real E).coord j (A.symm (ε i)) := rfl

private theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAt_toBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
            (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))) := by
  classical
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀))) (ε l))
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  have hbasis :
      coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis Real E :=
    coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.symm (ε l)) := by
    dsimp [gInv]
    simpa [extChartAt] using
      congrArg (fun L : (E →L[Real] Real) →L[Real] E =>
        (Module.finBasis Real E).coord k (L (ε l))) hInv
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.symm (ε l))
          = (ε k) (A.symm (ε l)) := rfl
      _ = (A (A.symm (ε k))) (A.symm (ε l)) := by
            rw [A.apply_symm_apply]
      _ = g.inner x₀ (A.symm (ε k)) (A.symm (ε l)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = g.inner x₀ (A.symm (ε l)) (A.symm (ε k)) := by
            exact g.symm x₀ (A.symm (ε k)) (A.symm (ε l))
      _ = (A (A.symm (ε l))) (A.symm (ε k)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = (ε l) (A.symm (ε k)) := by
            rw [A.apply_symm_apply]
      _ = (Module.finBasis Real E).coord l (A.symm (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) i)
            ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    rw [hbasis]
    simp only [hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.symm (ε j)))
          = g.inner x₀ ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.symm (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (g.inner x₀ ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.symm (ε j)))
                ((Module.finBasis Real E) k)
            calc
              g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.symm (ε j))
                  = (Module.finBasis Real E).coord k (A.symm (ε j)) *
                      g.inner x₀ ((Module.finBasis Real E) i)
                        ((Module.finBasis Real E) k) := by ring
              _ = (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    g.inner x₀ ((Module.finBasis Real E) i)
                      ((Module.finBasis Real E) k) := by simp
              _ = g.inner x₀ ((Module.finBasis Real E) i)
                    ((Module.finBasis Real E).coord k (A.symm (ε j)) •
                      (Module.finBasis Real E) k) := hmap.symm
      _ = g.inner x₀ ((Module.finBasis Real E) i) (A.symm (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    (Module.finBasis Real E) k) = A.symm (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.symm (ε j))
            exact congrArg (fun v => g.inner x₀ ((Module.finBasis Real E) i) v) hsum
      _ = g.inner x₀ (A.symm (ε j)) ((Module.finBasis Real E) i) := by
            exact g.symm x₀ ((Module.finBasis Real E) i) (A.symm (ε j))
      _ = (A (A.symm (ε j))) ((Module.finBasis Real E) i) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = ε j ((Module.finBasis Real E) i) := by
            rw [A.apply_symm_apply]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := by exact fun h => hij h.symm
              simp [ε, hji, hij]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
            ((coordinateFrameAt_toBasis (I := I) x₀) j))
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) j)
                ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
              ((coordinateFrameAt_toBasis (I := I) x₀) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j

/-! ## Smooth Christoffel formula RHS in a fixed chart -/

/-- Fixed-chart metric coefficients as model functions. -/
noncomputable def metricFlatModelInChart_component
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  metricFlatModelInChart (I := I) g x₀ y
    ((Module.finBasis Real E) i) ((Module.finBasis Real E) j)

/-- At the chart center, the fixed-chart metric component is the intrinsic
coordinate-frame metric component. -/
theorem metricFlatModelInChart_component_center
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    metricFlatModelInChart_component (I := I) g x₀ i j (extChartAt I x₀ x₀) =
      g.inner x₀ (coordinateFrameAt (I := I) x₀ i x₀)
        (coordinateFrameAt (I := I) x₀ j x₀) := by
  rw [metricFlatModelInChart_component, metricFlatModelInChart_center_eq]
  change ((metricFlatContinuousEquiv (I := I) g x₀)
      ((Module.finBasis Real E) i)) ((Module.finBasis Real E) j) =
    g.inner x₀ (coordinateFrameAt (I := I) x₀ i x₀)
      (coordinateFrameAt (I := I) x₀ j x₀)
  rw [metricFlatContinuousEquiv_apply]
  have hi : coordinateFrameAt (I := I) x₀ i x₀ = (Module.finBasis Real E) i := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ i]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  have hj : coordinateFrameAt (I := I) x₀ j x₀ = (Module.finBasis Real E) j := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ j]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  rw [hi, hj]

private theorem metricFlatModelInChart_component_eq_coord_component_comp_eventually
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    metricFlatModelInChart_component (I := I) g x₀ i j
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
      fun y : E =>
        g.inner ((extChartAt I x₀).symm y)
          (coordinateFrameAt (I := I) x₀ i ((extChartAt I x₀).symm y))
          (coordinateFrameAt (I := I) x₀ j ((extChartAt I x₀).symm y)) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  unfold metricFlatModelInChart_component metricFlatModelInChart
  rw [hom_trivializationAt_apply]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀
        ((extChartAt I x₀).symm y) x₀ ((extChartAt I x₀).symm y)
        (g.inner ((extChartAt I x₀).symm y))
        ((Module.finBasis Real E) i)) ((Module.finBasis Real E) j) =
      g.inner ((extChartAt I x₀).symm y)
        (coordinateFrameAt (I := I) x₀ i ((extChartAt I x₀).symm y))
        (coordinateFrameAt (I := I) x₀ j ((extChartAt I x₀).symm y))
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
  have hyT :
      (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hy_src
  have hyDual :
      (extChartAt I x₀).symm y ∈
        (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hyT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hyT hyDual]
  rw [Trivialization.coe_continuousLinearEquivAt_eq'
    (e := trivializationAt (E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] Real) x₀) (R := Real) hyDual]
  rw [Trivialization.symm_continuousLinearEquivAt_eq'
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀) (R := Real) hyT]
  simp only [ContinuousLinearMap.comp_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base j]
  rw [(extChartAt I x₀).right_inv hy]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
  rw [(extChartAt I x₀).right_inv hy]
  have hj_symm :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symm
          ((extChartAt I x₀).symm y) ((Module.finBasis Real E) j) =
        (mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j) := by
    change (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
        ((extChartAt I x₀).symm y) ((Module.finBasis Real E) j) =
      (mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
        (Set.range I) y) ((Module.finBasis Real E) j)
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
    rw [(extChartAt I x₀).right_inv hy]
    rfl
  change
      (((Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)).toPretrivialization.linearMapAt Real
          ((extChartAt I x₀).symm y)
          ((g.inner ((extChartAt I x₀).symm y))
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
              (Set.range I) y) ((Module.finBasis Real E) i))))
        ((Module.finBasis Real E) j)) =
      g.inner ((extChartAt I x₀).symm y)
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) i))
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j))
  rw [Pretrivialization.linearMapAt_apply]
  have hyDual' :
      (extChartAt I x₀).symm y ∈
        (Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)).toPretrivialization.baseSet := by
    change (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet ∩
        (trivializationAt Real (fun _ : M => Real) x₀).baseSet
    exact ⟨hyT, by simp⟩
  rw [if_pos hyDual']
  change
      ((Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)
        (⟨(extChartAt I x₀).symm y,
          (g.inner ((extChartAt I x₀).symm y))
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
              (Set.range I) y) ((Module.finBasis Real E) i))⟩ :
          TotalSpace (E →L[Real] Real)
            (fun p : M => TangentSpace I p →L[Real] Real))).2
        ((Module.finBasis Real E) j)) =
      g.inner ((extChartAt I x₀).symm y)
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) i))
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j))
  rw [Bundle.Trivialization.continuousLinearMap_apply]
  simp [Trivial.trivialization, ContinuousLinearMap.comp_apply,
    Trivialization.linearMapAt_apply, Trivialization.symmL_apply]
  have hj_symm' :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symm
          ((chartAt H x₀).symm (I.symm y)) ((Module.finBasis Real E) j) =
        (mfderivWithin 𝓘(Real, E) I ((chartAt H x₀).symm ∘ I.symm)
          (Set.range I) y) ((Module.finBasis Real E) j) := by
    simpa [extChartAt] using hj_symm
  rw [hj_symm']
  rfl

/-- Fixed-chart metric coefficients are smooth model functions. -/
theorem metricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart_component (I := I) g x₀ i j)
      (Set.range I) (extChartAt I x₀ x₀) := by
  have h := metricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have hi :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          metricFlatModelInChart (I := I) g x₀ y ((Module.finBasis Real E) i))
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using h.clm_apply contDiffWithinAt_const
  simpa [metricFlatModelInChart_component] using hi.clm_apply contDiffWithinAt_const

/-- At the chart center, the model derivative of a fixed-chart metric coefficient
is the intrinsic directional derivative of the corresponding coordinate-frame
metric component. -/
theorem metricFlatModelInChart_component_deriv_center
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) (extChartAt I x₀ x₀) ((Module.finBasis Real E) a) =
      directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ a)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x₀ i y)
            (coordinateFrameAt (I := I) x₀ j y)) x₀ := by
  let z₀ : E := extChartAt I x₀ x₀
  let f : M -> Real := fun y : M =>
    g.inner y (coordinateFrameAt (I := I) x₀ i y)
      (coordinateFrameAt (I := I) x₀ j y)
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have heq :
      metricFlatModelInChart_component (I := I) g x₀ i j
        =ᶠ[𝓝[Set.range I] z₀]
        writtenInExtChartAt I 𝓘(Real, Real) x₀ f := by
    simpa [z₀, f, writtenInExtChartAt] using
      metricFlatModelInChart_component_eq_coord_component_comp_eventually
        (I := I) g x₀ i j
  have hfd :
      fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) z₀ =
        fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x₀ f)
          (Set.range I) z₀ :=
    heq.fderivWithin_eq_of_mem hzRange
  have hf_md : MDifferentiableAt I 𝓘(Real, Real) f x₀ :=
    (metric_coordinateFrame_component_contMDiffAt (I := I) g x₀ i j).mdifferentiableAt
      (by simp)
  have hframe_center :
      coordinateFrameAt (I := I) x₀ a x₀ = (Module.finBasis Real E) a := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ a]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  unfold directionalDeriv extDerivFun
  change
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) z₀ ((Module.finBasis Real E) a) =
      (mfderiv I 𝓘(Real, Real) f x₀) (coordinateFrameAt (I := I) x₀ a x₀)
  rw [hframe_center, hf_md.mfderiv, hfd]
  rfl

/-- Fixed-chart coordinate derivatives of metric coefficients are smooth model
functions. -/
theorem metricFlatModelInChart_component_deriv_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) y ((Module.finBasis Real E) a))
      (Set.range I) (extChartAt I x₀ x₀) := by
  have hf :=
    metricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ i j
  have hconst :
      ContDiffWithinAt Real ∞
        (fun _ : E => (Module.finBasis Real E) a)
        (Set.range I) (extChartAt I x₀ x₀) :=
    contDiffWithinAt_const
  exact hf.fderivWithin_right_apply hconst I.uniqueDiffOn (by simp)
    (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀))

/-- The fixed-chart right hand side of the coordinate Christoffel formula. -/
noncomputable def leviCivitaChristoffelModelRHS
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (1 / 2 : Real) *
    ∑ l : CoordinateIdx (𝕜 := Real) E,
      ((Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ y))
          (LinearMap.toContinuousLinearMap
            ((Module.finBasis Real E).coord l)))) *
        (fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) y ((Module.finBasis Real E) i) +
          fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) y ((Module.finBasis Real E) j) -
          fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) y ((Module.finBasis Real E) l))

/-- The fixed-chart right hand side of the Christoffel formula is smooth as a
model function. -/
theorem leviCivitaChristoffelModelRHS_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (leviCivitaChristoffelModelRHS (I := I) g x₀ i j k)
      (Set.range I) (extChartAt I x₀ x₀) := by
  classical
  unfold leviCivitaChristoffelModelRHS
  refine contDiffWithinAt_const.mul ?_
  refine ContDiffWithinAt.sum fun l _ => ?_
  have hinv :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ k l
  have h₁ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ i j l
  have h₂ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ j i l
  have h₃ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ l i j
  exact hinv.mul ((h₁.add h₂).sub h₃)

/-- At the chart center, the smooth model Christoffel RHS recovers the
coordinate Christoffel coefficient of the Koszul Levi-Civita connection. -/
theorem leviCivitaChristoffelModelRHS_center_eq_christoffel
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaChristoffelModelRHS (I := I) g x₀ i j k (extChartAt I x₀ x₀) =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i j k := by
  classical
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))
  have hinv : MetricInverseInBasis (I := I) g x₀
      (coordinateFrameAt_toBasis (I := I) x₀) gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x₀
  have hformula :=
    RicciFlower.LeviCivita.leviCivitaConnectionOfMetric_coordinate_christoffel_formula
      (I := I) g x₀ gInv hinv i j k
  rw [hformula]
  unfold leviCivitaChristoffelModelRHS
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  dsimp [gInv]
  congr 1
  ·
    have h₁ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) i) =
          directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ i)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ j y)
                (coordinateFrameAt (I := I) x₀ l y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ i j l
    have h₂ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) j) =
          directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ j)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ l y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ j i l
    have h₃ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) l) =
          directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ l)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ j y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ l i j
    rw [h₁, h₂, h₃]

end LeviCivita
end RicciFlower
