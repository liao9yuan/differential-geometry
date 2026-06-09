import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.StrictParabolicity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSymbol

/-! # Strict parabolicity of the DeTurck-Ricci right-hand side

The concrete DeTurck-Ricci operator `g ↦ -2 Ric(g) + 𝓛_{X(g, g_bg)} g` is strictly
parabolic at every metric: the chart second-order part of its linearization is the
gauge-cancelled isotropic Laplacian symbol `−|ξ|²_g · id` on the symmetric perturbation
space, yielding `IsStrictlyParabolicMetricRHS` for the abstract short-time-existence
interface. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The Ricci–DeTurck right-hand side is a symmetric bilinear form.**
`deTurckRicciRHS g_bg g x v w = deTurckRicciRHS g_bg g x w v`, because it is a sum of two
symmetric `(0,2)`-tensors: the Ricci tensor (`ricciTensor_symm`) and the metric Lie
derivative (`lieDerivMetric_isPointwiseSymm`). -/
theorem deTurckRicciRHS_isPointwiseSymm
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w =
      deTurckRicciRHS (I := I) g_bg g x w v := by
  simp only [deTurckRicciRHS, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lieDerivMetricClm_apply]
  rw [DifferentialGeometry.Integral.Connection.ricciTensor_symm (I := I)
        (smoothRiemannianMetricToInfty (I := I) g) x v w,
    DeTurck.lieDerivMetric_isPointwiseSymm (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (DeTurck.deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w]

/-- **The chart `∂²h`-coefficient of the Ricci–DeTurck linearization at `g₀`.**

`deTurckRicciRHSChartSecondOrderPart g₀ g_bg` is the canonical chart second-order part of
`D(deTurckRicciRHS g_bg)(g₀)`: the part of the directional derivative carrying two chart
derivatives of the perturbation `h`, assembled from the `-2 Ric + 𝓛_W g` decomposition as
`(-2)·chartRicciSecondOrderPart g₀ + chartDeTurckCorrSecondOrderPart g₀ g_bg`.

This is the abstract `P` whose principal symbol — the `∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}`
substitution — is the bundled Ricci–DeTurck symbol `deTurckSymbol g₀ g_bg`, which the
gauge cancellation makes the isotropic `|ξ|²_{g₀} · t` on the symmetric perturbation
space (`StrictParabolicity.lean`). -/
noncomputable def deTurckRicciRHSChartSecondOrderPart
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → E → ℝ :=
  fun h α i j y =>
    (-2 : ℝ) * chartRicciSecondOrderPart (I := I) g₀ α h i j y +
      chartDeTurckCorrSecondOrderPart (I := I) g₀ g_bg α h i j y

/-- **The chart `∂²h`-coefficient of `deTurckRicciRHS g_bg` is the genuine chart second
order part of its linearization at `g₀`, and reads off the DeTurck symbol.**

This is the one genuine differential-geometry input that ties the abstract principal-symbol
predicate to the concrete Ricci–DeTurck operator.  It packages the two facts the predicate
needs about `P := deTurckRicciRHSChartSecondOrderPart g₀ g_bg`:

* **(linearization)** `P` is the chart second-order part of `D(deTurckRicciRHS g_bg)(g₀)`:
  along any realising family `gfam` of `g₀ ⊕ s·h`, the `s`-derivative at `0` of the chart
  `(i, j)`-component of `deTurckRicciRHS g_bg (gfam s)` equals `P h α i j y` plus a
  genuinely-first-order remainder (`IsChartLinearizationSecondOrderPart`).  This is the
  abstract analogue of the `-2 Ric + 𝓛_W g` chart linearization computed termwise in
  `chartRicciSecondOrderPart_eq_principalSymbol_add_remainder` and
  `chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder`.

* **(symbol read-off)** the principal-symbol substitution of `P` is the geometer-sign
  isotropic symbol `isotropicSymbol _ (deTurckSymbolCoeff g₀)` (coefficient `−|ξ|²_{g₀}`),
  i.e. evaluating `P` on the symbol test perturbation reproduces the negated symbol
  component (`IsPrincipalSymbolOfSecondOrderPart`).

The two genuine remaining obligations are isolated in
`deTurckRicciRHS_chartLinearization_and_readoff`:

* the chart linearization identity for `deTurckRicciRHS`
  (`(d/ds) [chart component of deTurckRicciRHS(g₀ ⊕ s·h)]|_{s=0} =
  P h + first-order remainder`, the `IsChartLinearizationSecondOrderPart` clause), the
  `s`-derivative bridge between the operator and its termwise chart second-order parts; and

* the test-perturbation read-off
  `P (symbolTestPerturbation x x ξ t) x i j (extChartAt I x x) = |ξ|²_{g₀} · t_{ij}`, the
  `∂_a∂_b h ↦ ξ_aξ_b t` substitution feeding the closed-form gauge cancellation
  `deTurckSymbol_apply_eq_smul_of_symm`.

Both are genuine chart-coordinate computations on the concrete operator; neither is yet
available as a project lemma, so this single obligation is left as one honest `sorry`.
The **strict-parabolicity** half of the principal-symbol clause — `σ x ξ t = −|ξ|²_{g₀}·t`
with `0 < |ξ|²_{g₀}` — is proven outright below from `isotropicSymbol_apply_apply` and
`metricCovectorNormSq_pos`. -/
theorem deTurckRicciRHS_chartLinearization_and_readoff
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsChartLinearizationSecondOrderPart (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀
        (deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg) ∧
      ∀ (x : M) (ξ : E), ξ ≠ 0 →
        ∀ t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ,
          (∀ ht : ∀ v w, t v w = t w v, ∀ i j : Fin (Module.finrank ℝ E),
            deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg
                (symbolTestPerturbation (I := I) x x ξ t ht) x i j (extChartAt I x x) =
              - (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
                    (E := E)
                    (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
                    (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t)
                  ((chartModelBasis E) i) ((chartModelBasis E) j)) :=
  sorry

/-- **The chart second-order part `deTurckRicciRHSChartSecondOrderPart g₀ g_bg` is the
chart `∂²h`-coefficient of `D(deTurckRicciRHS g_bg)(g₀)` and has the geometer-sign
isotropic Ricci–DeTurck symbol as its principal symbol.**

The chart-linearization clause and the test-perturbation read-off are supplied by
`deTurckRicciRHS_chartLinearization_and_readoff`; the strict-parabolicity clause
(`isotropicSymbol _ (deTurckSymbolCoeff g₀)` acts as `−|ξ|²_{g₀}·t`, `0 < |ξ|²_{g₀}`) is
proven here from `isotropicSymbol_apply_apply`, `deTurckSymbolCoeff_apply`, and
`metricCovectorNormSq_pos`. -/
theorem deTurckRicciRHS_chartSecondOrderPart_spec
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsChartLinearizationSecondOrderPart (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀
        (deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg) ∧
      IsPrincipalSymbolOfSecondOrderPart (I := I) g₀
        (deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg)
        (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
          (E := E)
          (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
          (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀)) := by
  obtain ⟨hlin, hreadoff⟩ := deTurckRicciRHS_chartLinearization_and_readoff (I := I) g₀ g_bg
  refine ⟨hlin, ?_⟩
  intro x ξ hξ t ht
  refine ⟨hreadoff x ξ hξ t, ?_, metricCovectorNormSq_pos (I := I) g₀ x hξ⟩
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]

/-- **Symbol-form identification on a symmetric input.**  The strictly-parabolic isotropic
symbol witness for `deTurckRicciRHS g_bg` at `g₀` (the isotropic symbol with coefficient
`-|ξ|²_{g₀}`) is the **negation** of the bundled Ricci–DeTurck linearized symbol
`DeTurck.deTurckSymbol g₀ g_bg`, on a **symmetric** input bilinear form `t`
(`t v w = t w v`).

The bundled `deTurckSymbol g₀ g_bg` is the linear combination
`-2 • ricciSymbol g₀ + deTurckCorrectionSymbol g₀ g_bg` whose gauge cancellation
(`DeTurck.deTurckSymbol_apply_eq_smul_of_symm`) reads, on symmetric `t`, as the action
`t ↦ |ξ|²_{g₀} · t` — the *positive* isotropic scaling, the substitution
`∂_a ∂_b ↦ +ξ_a ξ_b`.  The strictly-parabolic isotropic symbol used as the principal-symbol
witness in `deTurckRicciRHS_hasPrincipalSymbol_at_self` is its geometer-sign counterpart
`t ↦ -|ξ|²_{g₀} · t` (the substitution `∂_a ∂_b ↦ -ξ_a ξ_b`, consistent with the
geometer's Laplacian `Δ = div ∘ grad` having spectrum `⊆ (-∞, 0]`).  So the two agree up to
an overall sign on the symmetric input that downstream parabolic consumption actually uses. -/
theorem deTurckRicciRHS_principal_symbol_equals_deTurckSymbol
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t := by
  classical
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]
  rw [DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm
    (I := I) g₀ g_bg x ξ t ht]
  rw [neg_smul]

/-- The Ricci–DeTurck right-hand side `g ↦ -2 Rc(g) + 𝓛_{W(g, g_bg)} g` has the geometer-sign
isotropic Ricci–DeTurck symbol as the principal symbol of its linearization at its own base
metric `g₀`.

The witness symbol is the isotropic Ricci–DeTurck symbol with coefficient `-|ξ|²_{g₀}`
(see `DeTurck.isotropicSymbol` with `DeTurck.deTurckSymbolCoeff g₀`).  Its chart second order
part is `deTurckRicciRHSChartSecondOrderPart g₀ g_bg = -2·chartRicciSecondOrderPart +
chartDeTurckCorrSecondOrderPart` (`deTurckRicciRHS_chartSecondOrderPart_spec`), whose
gauge-cancelled principal symbol is the geometer-sign isotropic symbol. -/
theorem deTurckRicciRHS_hasPrincipalSymbol_at_self
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    HasPrincipalSymbol (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀
      (DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀)) :=
  ⟨deTurckRicciRHSChartSecondOrderPart (I := I) g₀ g_bg,
    (deTurckRicciRHS_chartSecondOrderPart_spec (I := I) g₀ g_bg).1,
    (deTurckRicciRHS_chartSecondOrderPart_spec (I := I) g₀ g_bg).2⟩

/-- The Ricci–DeTurck right-hand side `g ↦ -2 Rc(g) + 𝓛_{W(g, g_bg)} g` is strictly
parabolic at its own base metric `g₀`, in the sense of `IsStrictlyParabolicMetricRHS`:
it has a principal symbol there (`deTurckRicciRHS_hasPrincipalSymbol_at_self`). -/
theorem deTurckRicciRHS_isStrictlyParabolic_at_self
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsStrictlyParabolicMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ :=
  ⟨DifferentialGeometry.PDE.DeTurck.isotropicSymbol
      (E := E)
      (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
      (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀),
    deTurckRicciRHS_hasPrincipalSymbol_at_self g₀ g_bg⟩

/-- **Bridge from a principal-symbol witness to strict parabolicity of the metric RHS.**

If an operator `F` on smooth Riemannian metrics has *some* principal symbol `σ` at the
metric `g₀` (the existence of `σ` such that `HasPrincipalSymbol F g₀ σ`), then it is
strictly parabolic at `g₀` in the sense of `IsStrictlyParabolicMetricRHS`.

This is the trivial repackaging the downstream parabolic-existence consumer expects:
`IsStrictlyParabolicMetricRHS` is, by definition, the existence statement
`∃ σ, HasPrincipalSymbol F g₀ σ` — so any witness `(σ, h)` packages directly.  The
content of strict parabolicity is then carried by `HasPrincipalSymbol`'s body, namely the
chart second-order part data `IsChartLinearizationSecondOrderPart F g₀ P` and the
strictly-parabolic principal symbol `IsPrincipalSymbolOfSecondOrderPart g₀ P σ`. -/
theorem bridge_symbol_equality_to_is_strictly_parabolic_metric_rhs
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M)
    (h : HasPrincipalSymbol F g₀ σ) :
    IsStrictlyParabolicMetricRHS (I := I) F g₀ :=
  ⟨σ, h⟩

end DifferentialGeometry.PDE.RicciFlow
