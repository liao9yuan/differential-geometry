import RicciFlower.VectorBundle.PartialMfderiv.ModelMixed

/-!
# Fixed-base time derivative producers

Chart-based fixed-base derivative predicates and local producers for time-dependent scalar functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Topology Manifold ContDiff

namespace RicciFlower

/-- For real-valued scalar functions, `extDerivFun` is just `mfderiv` applied to
the supplied tangent vector. -/
theorem extDerivFun_real_eq_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners Real E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> Real) (x : M) (V : TangentSpace I x) :
    extDerivFun (I := I) f x V =
      mfderiv I 𝓘(Real, Real) f x V := by
  simp [extDerivFun, NormedSpace.fromTangentSpace]

/-- If a scalar function has a chart representative near the base point, then
its exterior derivative at the base point is the model `fderiv` of that
representative. -/
theorem extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : M -> Real} {φ : E -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hφ :
      writtenInExtChartAt I 𝓘(Real, Real) x f
        =ᶠ[nhds (extChartAt I x x)] φ)
    (V : TangentSpace I x) :
    extDerivFun (I := I) f x V =
      fderiv Real φ (extChartAt I x x) V := by
  let z₀ : E := extChartAt I x x
  have hrange : Set.range I ∈ nhds z₀ := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  calc
    extDerivFun (I := I) f x V =
        mfderiv I 𝓘(Real, Real) f x V := by
          rw [extDerivFun_real_eq_mfderiv]
    _ = fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z₀ V := by
          simpa [z₀] using congrArg (fun L => L V) hf.mfderiv
    _ = fderiv Real
          (writtenInExtChartAt I 𝓘(Real, Real) x f) z₀ V := by
          rw [fderivWithin_of_mem_nhds hrange]
    _ = fderiv Real φ z₀ V := by
          rw [hφ.fderiv_eq]

/-- Fixed-base time derivative of a spatial exterior derivative.

This is the scalar mixed-partial frontier used by the Ricci-flow Christoffel
calculation.  It deliberately freezes the spatial base point and tangent vector:
the only varying parameter is the real time parameter.

The model-space analytic core is `fixedBaseFDerivTimeDerivativeAt_of_contDiff`.
To construct this predicate from manifold-level spacetime smoothness, the
remaining chart-local lemma should rewrite `extDerivFun` in a chart as the
model derivative and then apply that model-space theorem. -/
def FixedBaseExtDerivTimeDerivativeOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ) (x : M), x ∈ u ->
    forall V : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => extDerivFun (I := I) (F s) x V)
        (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t

/-- Regular-time version of `FixedBaseExtDerivTimeDerivativeOn`.

This is the version suited to Ricci-flow intervals: the derivative is still
within the full time carrier, but it is required only at regular evolution
times. -/
def FixedBaseExtDerivTimeDerivativeOnRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet regularSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ), t ∈ regularSet ->
    forall (x : M), x ∈ u ->
      forall V : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => extDerivFun (I := I) (F s) x V)
          (extDerivFun (I := I) (Ft t) x V)
          timeSet
          t

theorem fixedBaseExtDerivTimeDerivativeOn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft)
    {t : ℝ} {x : M} (hx : x ∈ u) (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => extDerivFun (I := I) (F s) x V)
      (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t :=
  h t x hx V

/-- Pointwise use of the regular-time fixed-base mixed derivative predicate. -/
theorem fixedBaseExtDerivTimeDerivativeOnRegular_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet u F Ft)
    {t : ℝ} (ht : t ∈ regularSet) {x : M} (hx : x ∈ u)
    (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => extDerivFun (I := I) (F s) x V)
      (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t :=
  h t ht x hx V

/-- The all-times predicate immediately implies the regular-time predicate. -/
theorem FixedBaseExtDerivTimeDerivativeOn.toRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t _ht x hx V
  exact h t x hx V

/-- Chart-level constructor for fixed-base mixed derivatives on a singleton.

The model-space scalar family `Φ` supplies the jointly `C²` chart expression.
The two eventual-equality hypotheses identify the manifold scalar families
`F` and `Ft` with `Φ` and with the time derivative of `Φ`, respectively, near
the chart center. -/
theorem fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M) F Ft := by
  intro t x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :=
    fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
      (E := E) Φ hΦ (timeSet := timeSet) (t := t) z₀ V
  have hleft :
      ∀ s : Real,
        extDerivFun (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s) (hFchart s) V
  have hright :
      extDerivFun (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
        (hFtdiff t) (hFtchart t) V
  exact
    (hmodel.congr
      (fun s _hs => hleft s)
      (hleft t)).congr_deriv hright.symm

/-- Chart-level constructor for regular-time fixed-base mixed derivatives on a
singleton.  This currently reuses the all-times chart constructor and then
restricts it to regular times. -/
theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  exact
    (fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
      (I := I) (timeSet := timeSet) (x₀ := x₀)
      (F := F) (Ft := Ft) (Φ := Φ)
      hΦ hFdiff hFchart hFtdiff hFtchart).toRegular
      (I := I) (regularSet := regularSet)

/-- Chart-level constructor for regular-time fixed-base mixed derivatives on a
singleton, with chart equalities required only on the time carrier and regular
times. -/
theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiffOnTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  intro t ht x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :=
    fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
      (E := E) Φ hΦ (timeSet := timeSet) (t := t) z₀ V
  have hleft :
      ∀ s : Real, s ∈ timeSet ->
        extDerivFun (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s hs
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s hs) (hFchart s hs) V
  have hright :
      extDerivFun (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
      (hFtdiff t ht) (hFtchart t ht) V
  exact
    (hmodel.congr
      (fun s hs => hleft s hs)
      (hleft t (hregular_subset ht))).congr_deriv hright.symm

/-- Model-space time-derivative identification for a smooth spacetime chart
representative.

If the slice derivative of `Φ` in the time variable is supplied as `Ψ`, and the
time set is a neighborhood of the regular time, then `Ψ` agrees locally with the
full Frechet derivative of `Φ` applied to the time direction `(1, 0)`. -/
theorem eventuallyEq_timeFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {timeSet : Set Real}
    {Φ Ψ : Real -> E -> Real}
    {t : Real} {y₀ : E}
    (htime : timeSet ∈ 𝓝 t)
    (hdiff : ∀ᶠ y in 𝓝 y₀,
      DifferentiableAt Real
        (fun p : Real × E => Φ p.1 p.2)
        (t, y))
    (hderiv : ∀ᶠ y in 𝓝 y₀,
      HasDerivWithinAt
        (fun s : Real => Φ s y)
        (Ψ t y)
        timeSet
        t) :
    Ψ t =ᶠ[𝓝 y₀]
      fun y : E =>
        (fderiv Real
          (fun p : Real × E => Φ p.1 p.2)
          (t, y)) (1, 0) := by
  filter_upwards [hdiff, hderiv] with y hy_diff hy_deriv
  let A : Real × E -> Real := fun p => Φ p.1 p.2
  let L : Real -> Real × E := fun s => (s, y)
  have hline : HasDerivAt L (1, 0) t := by
    exact (hasDerivAt_id t).prodMk (hasDerivAt_const (x := t) (c := y))
  have hchart :
      HasDerivAt
        (fun s : Real => A (L s))
        ((fderiv Real A (t, y)) (1, 0)) t := by
    simpa [A, L] using
      hy_diff.hasFDerivAt.comp_hasDerivAt t hline
  have htime_deriv :
      HasDerivAt (fun s : Real => Φ s y) (Ψ t y) t :=
    hy_deriv.hasDerivAt htime
  exact htime_deriv.unique hchart

/-- Pointwise chart-level constructor for regular-time fixed-base mixed
derivatives on a singleton.

This is the local version of
`fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiffOnTime`:
the chart representative only needs to be `C²` at the regular spacetime point
where the derivative is evaluated. -/
theorem fixedBaseAtReg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ∀ t : Real, t ∈ regularSet ->
      ContDiffAt Real 2 (fun p : Real × E => Φ p.1 p.2)
        (t, extChartAt I x₀ x₀))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  intro t ht x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :
      HasDerivWithinAt
        (fun s : Real => (fderiv Real (Φ s) z₀) V)
        ((fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀) V)
        timeSet t :=
    (fixedBaseFDerivTimeDerivativeAt_of_contDiffAt
      (E := E) (F := Φ) (t := t) (x := z₀) (V := V) (hΦ t ht)).hasDerivWithinAt
  have hleft :
      ∀ s : Real, s ∈ timeSet ->
        extDerivFun (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s hs
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s hs) (hFchart s hs) V
  have hright :
      extDerivFun (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
        (hFtdiff t ht) (hFtchart t ht) V
  exact
    (hmodel.congr
      (fun s hs => hleft s hs)
      (hleft t (hregular_subset ht))).congr_deriv hright.symm

/-- Chart expression of scalar spacetime smoothness on `Real × M`, centered at
the given spatial point. -/
theorem contDiffAt_prodChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} {F : Real × M -> Real} {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) n F (t, x)) :
    ContDiffAt Real n
      (fun p : Real × E => F (p.1, (extChartAt I x).symm p.2))
      (t, extChartAt I x x) := by
  have hsrc :=
    (contMDiffAt_iff_source
      (I := 𝓘(Real, Real).prod I) (I' := 𝓘(Real, Real))
      (f := F) (x := (t, x))).mp hF
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hsrc
  have hsrc' :
      ContDiffWithinAt Real n
        (fun p : Real × E => F (p.1, (extChartAt I x).symm p.2))
        Set.univ (t, extChartAt I x x) := by
    convert hsrc using 1
    · ext p
      have hp : p ∈ Set.range (Prod.map id (I : H -> E)) := by
        simp [Set.range_prodMap, ModelWithCorners.range_eq_univ]
      simp [hp]
  simpa [contDiffWithinAt_univ] using hsrc'

/-- Build regular-time fixed-base spatial derivative commutation from ordinary
time derivatives of the scalar slices and spacetime smoothness.

This is the manifold-level bridge from a Ricci-flow metric equation
`∂ₜ F = Ft` to the fixed-base derivative predicate used by the Christoffel
variation calculation. -/
theorem fixedBaseOnReg_of_timeDerivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hregular_nhds :
      ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ 𝓝 t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hFdiff :
      ∀ s, s ∈ timeSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x)
    (hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x)
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M,
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t ht x hx V
  let Φ : Real -> E -> Real := fun s y => F s ((extChartAt I x).symm y)
  have hsingle :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet ({x} : Set M) F Ft := by
    refine fixedBaseAtReg
      (I := I) (timeSet := timeSet) (regularSet := regularSet)
      (x₀ := x) (F := F) (Ft := Ft) (Φ := Φ)
      hregular_subset ?hΦ ?hFdiff ?hFchart ?hFtdiff ?hFtchart
    · intro τ hτ
      have hτs :
          ContMDiffAt
            (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
            (fun p : Real × M => F p.1 p.2)
            (τ, x) :=
        hSmooth τ hτ x hx
      simpa [Φ] using contDiffAt_prodChart (I := I) hτs
    · intro s hs
      exact hFdiff s hs x hx
    · intro s hs
      filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
      simp [Φ, writtenInExtChartAt, extChartAt]
    · intro τ hτ
      exact hFtdiff τ hτ x hx
    · intro τ hτ
      have hraw :
          (fun y : E => Ft τ ((extChartAt I x).symm y)) =ᶠ[𝓝 (extChartAt I x x)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (τ, y)) (1, 0) := by
        apply eventuallyEq_timeFDeriv
          (Φ := Φ)
          (Ψ := fun τ y => Ft τ ((extChartAt I x).symm y))
          (t := τ) (y₀ := extChartAt I x x)
        · exact hregular_nhds hτ
        · have hτs :
              ContDiffAt Real 2
                (fun p : Real × E => Φ p.1 p.2)
                (τ, extChartAt I x x) := by
            have hτm :
                ContMDiffAt
                  (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
                  (fun p : Real × M => F p.1 p.2)
                  (τ, x) :=
              hSmooth τ hτ x hx
            simpa [Φ] using contDiffAt_prodChart (I := I) hτm
          have hev :=
            (hτs.eventually (by norm_num)).mono fun y hy =>
              (hy.of_le (by norm_num)).differentiableAt_one
          have hev' :
              ∀ᶠ y in 𝓝 τ ×ˢ 𝓝 (extChartAt I x x),
                DifferentiableAt Real (fun p : Real × E => Φ p.1 p.2) y := by
            simpa [nhds_prod_eq] using hev
          exact
            (tendsto_const_nhds.prodMk Filter.tendsto_id).eventually hev'
        · filter_upwards with y
          exact hTime τ hτ ((extChartAt I x).symm y)
      have hFt_raw :
          writtenInExtChartAt I 𝓘(Real, Real) x (Ft τ)
            =ᶠ[𝓝 (extChartAt I x x)]
              fun y : E => Ft τ ((extChartAt I x).symm y) := by
        filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
        simp [writtenInExtChartAt, extChartAt]
      exact hFt_raw.trans hraw
  exact hsingle t ht x (by simp) V

/-- Local-domain version of `fixedBaseOnReg_of_timeDerivWithin`.

This is the form needed for local-frame component equations: the supplied time
derivative is only known on an open spatial domain, but the chart points near a
base point in that domain remain in the domain. -/
theorem fixedBaseOnRegLocal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hu : IsOpen u)
    (hregular_subset : regularSet ⊆ timeSet)
    (hregular_nhds :
      ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ 𝓝 t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hFdiff :
      ∀ s, s ∈ timeSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x)
    (hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x)
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t ht x hx V
  let Φ : Real -> E -> Real := fun s y => F s ((extChartAt I x).symm y)
  have hsingle :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet ({x} : Set M) F Ft := by
    refine fixedBaseAtReg
      (I := I) (timeSet := timeSet) (regularSet := regularSet)
      (x₀ := x) (F := F) (Ft := Ft) (Φ := Φ)
      hregular_subset ?hΦ ?hFdiff ?hFchart ?hFtdiff ?hFtchart
    · intro τ hτ
      have hτs :
          ContMDiffAt
            (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
            (fun p : Real × M => F p.1 p.2)
            (τ, x) :=
        hSmooth τ hτ x hx
      simpa [Φ] using contDiffAt_prodChart (I := I) hτs
    · intro s hs
      exact hFdiff s hs x hx
    · intro s hs
      filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
      simp [Φ, writtenInExtChartAt, extChartAt]
    · intro τ hτ
      exact hFtdiff τ hτ x hx
    · intro τ hτ
      have hleft : (extChartAt I x).symm ((extChartAt I x) x) = x :=
        (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
      have hsymm_tend :
          Filter.Tendsto (fun y : E => (extChartAt I x).symm y)
            (𝓝 (extChartAt I x x)) (𝓝 x) := by
        simpa only [ContinuousAt, hleft, Function.comp_def] using
          continuousAt_extChartAt_symm (I := I) x
      have hu_event :
          ∀ᶠ y in 𝓝 (extChartAt I x x), (extChartAt I x).symm y ∈ u :=
        hsymm_tend.eventually (hu.mem_nhds hx)
      have hraw :
          (fun y : E => Ft τ ((extChartAt I x).symm y)) =ᶠ[𝓝 (extChartAt I x x)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (τ, y)) (1, 0) := by
        apply eventuallyEq_timeFDeriv
          (Φ := Φ)
          (Ψ := fun τ y => Ft τ ((extChartAt I x).symm y))
          (t := τ) (y₀ := extChartAt I x x)
        · exact hregular_nhds hτ
        · have hτs :
              ContDiffAt Real 2
                (fun p : Real × E => Φ p.1 p.2)
                (τ, extChartAt I x x) := by
            have hτm :
                ContMDiffAt
                  (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
                  (fun p : Real × M => F p.1 p.2)
                  (τ, x) :=
              hSmooth τ hτ x hx
            simpa [Φ] using contDiffAt_prodChart (I := I) hτm
          have hev :=
            (hτs.eventually (by norm_num)).mono fun y hy =>
              (hy.of_le (by norm_num)).differentiableAt_one
          have hev' :
              ∀ᶠ y in 𝓝 τ ×ˢ 𝓝 (extChartAt I x x),
                DifferentiableAt Real (fun p : Real × E => Φ p.1 p.2) y := by
            simpa [nhds_prod_eq] using hev
          exact
            (tendsto_const_nhds.prodMk Filter.tendsto_id).eventually hev'
        · filter_upwards [hu_event] with y hyu
          exact hTime τ hτ ((extChartAt I x).symm y) hyu
      have hFt_raw :
          writtenInExtChartAt I 𝓘(Real, Real) x (Ft τ)
            =ᶠ[𝓝 (extChartAt I x x)]
              fun y : E => Ft τ ((extChartAt I x).symm y) := by
        filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
        simp [writtenInExtChartAt, extChartAt]
      exact hFt_raw.trans hraw
  exact hsingle t ht x (by simp) V


end RicciFlower
