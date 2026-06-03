import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination

/-! # The `Hᵃ` gauge-section-difference element of the `g₀`-anchored realize program

This file supplies the spectral `Hᵃ` element `deTurckG0SectionDiffHa Nsec u u'`
carrying the eigenbasis coordinates of the `L²` difference `toL2(Nsec u) − toL2(Nsec u')`
of a gauge section `Nsec : Hᵃ⁺¹(g₀) → SmoothCcTensor g₀ 0 2`.  By
`tensorHs.norm_sq_eq_tsum`, `‖deTurckG0SectionDiffHa Nsec u u'‖²` is exactly the
weighted square-sum of those coordinates — the left-hand side of the weighted-resolvent
Lipschitz certificate `deTurck_g0_nonlinearity_lipschitz` of
`DeTurckG0RealizeFrontier.lean`.  Its weighted square-summability witness is *not* open:
it is the spectral-side "smooth ⇒ in every `Hˢ`" fact
`smoothCcTensor_tensorL2Coeff_weighted_summable` applied to the smooth difference
`Nsec u − Nsec u'`.

The genuinely-open analytic content — the uniform `Hᵃ`-norm Lipschitz bound
`‖deTurckG0SectionDiffHa Nsec u u'‖ ≤ K · dist u u'` — is *not* posited here as a free
universal-over-`Nsec` statement: that statement is **false** for a generic discontinuous
`Nsec` (e.g. `Nsec u = f(u) · T₀` with `f` discontinuous in `u`, which is not
Lipschitz).  The bound holds only for the *concrete* DeTurck gauge, so it is bundled as a
conjunct of the concrete-gauge producer `deTurck_g0_decoupled_principal_match`
(`DeTurckG0RealizeFrontier.lean`) and threaded from there into
`deTurck_g0_nonlinearity_lipschitz`.  This file is therefore `sorry`-free; it only
defines the element constructor. -/

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The spectral `Hᵃ` element carrying the eigenbasis coordinates of the realize
gauge-section difference `Nsec u − Nsec u'`.**

Its coordinate family is `i ↦ tensorL2Coeff (resolvent) (toL2(Nsec u) − toL2(Nsec u')) i`,
the eigenbasis expansion of the `L²` difference of the two realize sections; the
weighted square-summability witness placing it in `Hᵃ` is the spectral "smooth ⇒ in
every `Hˢ`" fact applied to the smooth tensor `Nsec u − Nsec u'` (whose `toL2` is the
difference by linearity of `toL2`).

By `tensorHs.norm_sq_eq_tsum`, `‖deTurckG0SectionDiffHa Nsec u u'‖²` is exactly the
weighted square-sum of those coordinates, the left-hand side of the frontier
certificate `deTurck_g0_nonlinearity_lipschitz`. -/
noncomputable def deTurckG0SectionDiffHa
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        Integral.L2.SmoothCcTensor g₀ 0 2)
    (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (Integral.L2.SmoothCcTensor.toL2 (Nsec u)
        - Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i
  weighted_summable := by
    have h := smoothCcTensor_tensorL2Coeff_weighted_summable
      (I := I) (M := M) g₀ (a : ℝ) (Nsec u - Nsec u')
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
    have hsub : Integral.L2.SmoothCcTensor.toL2 (Nsec u - Nsec u')
        = Integral.L2.SmoothCcTensor.toL2 (Nsec u)
          - Integral.L2.SmoothCcTensor.toL2 (Nsec u') :=
      map_sub (Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2))
        (Nsec u) (Nsec u')
    rw [hsub] at h
    exact h

end DifferentialGeometry.PDE.RicciFlow
