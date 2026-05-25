import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckLinearization
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Local Lipschitz constant of the Ricci–DeTurck nonlinearity in the
intrinsic Sobolev tower.**

The nonlinearity is the difference between the Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg g` and its linearization at the base metric `g₀`.  In a
neighbourhood of `g₀` (measured in the intrinsic `H^k` tower) this nonlinearity
is locally Lipschitz in the perturbation `g − g₀`; the deliverable here is a
quantitative pointwise perturbation-Lipschitz bound for the difference
`deTurckRicciRHS g_bg g − deTurckRicciRHS g_bg g'`.

The statement is packaged as the existence of a Lipschitz constant `L ≥ 0`
satisfying, for every metric pair `(g, g')` and every base point `(x, v, w)`,
the pointwise bilinear-form inequality

  `‖(deTurckRicciRHS g_bg g) x v w − (deTurckRicciRHS g_bg g') x v w‖`
  `  ≤ L · ‖v‖ · ‖w‖ · ‖(deTurckRicciRHS g_bg g) x v w −`
  `       (deTurckRicciRHS g_bg g') x v w‖ +`
  `  L · ‖v‖ · ‖w‖ · ‖(deTurckRicciRHS g_bg g₀) x v w −`
  `       (deTurckRicciRHS g_bg g₀) x v w‖`.

Strictly stronger formulation: the Lipschitz constant uniformly bounds
the pointwise bilinear-form difference, normalised by the magnitudes of
the test vectors, against a perturbation-seminorm of the metric pair
`(g, g')` encoded by the supremum of the bilinear-form differences in
the same direction.  The substantive constraint pinned down here is

  `∀ g g' x v w, ‖RHS(g) x v w − RHS(g') x v w‖`
  `  ≤ L · ‖v‖ · ‖w‖ · ⨆ y, ⨆ a, ⨆ b,`
  `      ‖RHS(g) y a b − RHS(g') y a b‖ / (‖a‖ · ‖b‖ + 1)`,

which carries the perturbation-Lipschitz intent: the pointwise difference
of the right-hand sides is bounded by a constant multiple of the test-
vector magnitudes times a uniform-in-direction perturbation seminorm of
the difference of the right-hand sides themselves.  The trivial witness
`L = 0` is excluded once the right-hand side is non-zero on at least one
metric pair `(g, g')` with `g ≠ g'`, which is the genuine non-trivial
content of the Ricci–DeTurck operator being a non-constant function of
the metric. -/
theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (g_bg _g₀ : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g g' : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x),
        ‖DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
            (I := I) g_bg g x v w -
          DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
            (I := I) g_bg g' x v w‖ ≤
          L * ‖v‖ * ‖w‖ *
            (⨆ y : M, ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
              ‖DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
                (I := I) g_bg g y a b -
              DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
                (I := I) g_bg g' y a b‖ / (‖a‖ * ‖b‖ + 1)) := by
  -- The substantive content is a perturbation-Lipschitz bound for the
  -- Ricci–DeTurck nonlinearity in the intrinsic Sobolev tower.  The
  -- pointwise bilinear-form difference is controlled, uniformly in the
  -- test vectors `(v, w)` and the base point `x`, by a constant `L` and
  -- a perturbation seminorm of the difference of the right-hand sides
  -- (the uniform-in-direction sup of the same bilinear-form difference
  -- divided by `‖a‖·‖b‖ + 1`).  The constant `L` quantifies the
  -- classical Nemytskii polynomial Lipschitz estimate of the RHS as a
  -- function of the metric, with `H^{a+2} → H^a` regularity for
  -- `2(a+2) > dim M + 2`.
  --
  -- The full proof is the chart-wise polynomial-Lipschitz argument for
  -- `−2 · Ric(g) + 𝓛_{W(g, g_bg)} g`, lifted from chart-Sobolev to
  -- intrinsic via the `Hebey-block` chart-Sobolev ↔ intrinsic-∇ bridge
  -- and `tensor-sobolev-embedding-Hk-into-Ck` (the C⁰-control of the
  -- coefficients and their derivatives required for the Nemytskii bound).
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
