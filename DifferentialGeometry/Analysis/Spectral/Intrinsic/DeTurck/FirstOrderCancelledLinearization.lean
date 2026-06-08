import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.NonlinearitySpectral
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0GenuineNonlinearity

/-!
# The first-order-cancelled DeTurck linearization as a bounded tower operator

The gauge-cancellation fixed-point root leaf
`exists_deTurckGaugeCancellation_lipschitzSolution_of_towerCoercivity`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckG0GenuineNonlinearity.lean`) solves the nonlinear
gauge-correction equation by a Banach contraction over the *coercive* linearized operator
`−Δ_∇ + B₁`, where `B₁` is the genuinely **first-order** bounded remainder left once the
second-order principal symbol of the realized Ricci–DeTurck right-hand side cancels against the
linear rough Laplacian `Δ_∇`.  The cancellation is the symbol-level identity
`deTurckNonlinearitySpectral_principalPart_cancels` (sorry-free), and the realized-remainder class
split is `deTurckRealizeRemainderOf_toL2_retagClass_sub` (sorry-free)
`Φ(T) = toL2(deTurckRHSRetag g₀ g_bg g_T) − toL2(Δ_∇ T)`.

This file is the first of three Analysis-side foundations for that nonlinear solvability (the
`A → B → D` chain): it isolates the genuinely first-order linearization as a *bounded continuous
linear operator on the spectral Sobolev tower*.

## The concrete nonlinearity and its linearization

The genuine, on-disk-composable Ricci–DeTurck nonlinearity on the one-derivative-drop spectral
scale is

  `N(u) := deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (heatRepr u))`,
  `N : H^{a+1}(g₀) → Hᵃ(g₀)`

(`deTurckRealizeNonlinearityTower`), where `heatRepr` is the unit-time heat-smoothed smooth
realization `tensorHeatSemigroupHs_output_smoothRepr g₀ 0 2`.  Its eigenbasis coordinates are the
`L²` coordinates of the un-gated realized DeTurck remainder
`deTurckRealizeRemainderOf g₀ g_bg (heatRepr u)` against the rough-Laplacian eigenbasis
(`deTurckRealizeNonlinearityTower_coeff`, sorry-free) — exactly the synthesis-pin under which the
spectral-mass *affine first-order operator-loss* of this nonlinearity is already proven
(`deTurckGenuineN_firstOrder_operatorTsumLoss` over the realized-remainder synthesis), the
norm-level truth-maker that `N` loses at most one Sobolev order.

Because the second-order part of `N` cancels (`deTurckNonlinearitySpectral_principalPart_cancels`),
the Fréchet derivative of `N` at the origin is itself a bounded **first-order** operator
`H^{a+1} →L[ℝ] Hᵃ` (no leftover `−Δ_∇`: on the one-derivative-drop scale the second-order parts have
already cancelled).  This is `B₁`.

## What is delivered here

* `deTurckRealizeNonlinearityTower` — the concrete nonlinearity `N : H^{a+1} → Hᵃ`.
* `deTurckRealizeNonlinearityTower_coeff` — its eigenbasis coordinates are the `L²` coordinates of
  the realized DeTurck remainder of the heat-smoothed input (sorry-free; the synthesis-pin).
* `deTurckFirstOrderCancelledOperator` — the bounded first-order linearization `B₁ : H^{a+1} →L Hᵃ`.
* `deTurckFirstOrderCancelledOperator_hasFDerivAt` — the linearization identity: `B₁` is the Fréchet
  derivative of `N` at the origin.

The genuinely analytic content — that the realized Ricci–DeTurck nonlinearity is Fréchet
differentiable at the origin with the principal part cancelled — is posited as the single precise
node `exists_deTurckFirstOrderCancelledLinearization` (the Fréchet differentiability of a quasilinear
elliptic operator at a base point, with the bounded derivative whose second-order symbol has
cancelled), over which the named operator and its property are extracted.  `B₁` is consumed by the
coercive-inverse node (`L = −Δ_∇ + ι∘B₁` boundedly invertible by Gårding coercivity, transiting
`tensorScaleLaplacian`) and the global-Lipschitz fixed point on top of it.

## Sign convention

Geometer `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.  The realized
remainder is taken against the flow background `g_bg`, re-tagged to the anchor `g₀`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff NNReal Topology
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The concrete Ricci–DeTurck nonlinearity on the one-derivative-drop spectral Sobolev scale.**

For the anchor metric `g₀` and a flow background `g_bg`, this is the genuine geometric nonlinearity

  `N(u) := deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (heatRepr u))`,

a map `H^{a+1}(g₀) → Hᵃ(g₀)` of `(0,2)`-tensor spectral Sobolev spaces, where
`heatRepr u := tensorHeatSemigroupHs_output_smoothRepr g₀ 0 2 (unit time) u` is the unit-time
heat-smoothed smooth (`SmoothCcTensor`) realization of the spectral datum `u`, and
`deTurckRealizeRemainderOf g₀ g_bg ·` is the un-gated realized Ricci–DeTurck remainder
`deTurckRHSSection g_bg (realize ·) − Δ_∇ ·` (re-tagged to `g₀`).

This is the same operator whose spectral-mass *affine first-order operator-loss* is proven over the
realized-remainder synthesis (`deTurckGenuineN_firstOrder_operatorTsumLoss`), here packaged as the
fixed-order map the linearization is taken of. -/
def deTurckRealizeNonlinearityTower (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun u =>
    deTurckG0SpectralN (I := I) g₀ a
      (deTurckRealizeRemainderOf (I := I) g₀ g_bg
        (MetricRealization.tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M)
          g₀ 0 2 (one_pos) (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1) u))

/-- The eigenbasis coordinate of the concrete nonlinearity `N(u)` at `i` is the `L²` coordinate of
the realized DeTurck remainder of the heat-smoothed input `heatRepr u`, against the rough-Laplacian
eigenbasis.  This is the *synthesis-pin* (`hsynth`) shape under which the spectral-mass affine
first-order operator-loss of `N` is proven; it holds definitionally. -/
@[simp] theorem deTurckRealizeNonlinearityTower_coeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    (deTurckRealizeNonlinearityTower (I := I) g₀ g_bg a u).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (Integral.L2.SmoothCcTensor.toL2
          (deTurckRealizeRemainderOf (I := I) g₀ g_bg
            (MetricRealization.tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M)
              g₀ 0 2 (one_pos) (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1) u))) i := rfl

/-- **The first-order-cancelled DeTurck linearization exists as a bounded tower operator (posited
analytic node — the Fréchet differentiability of the realized Ricci–DeTurck nonlinearity at the
origin, with cancelled principal part).**

The concrete Ricci–DeTurck nonlinearity `deTurckRealizeNonlinearityTower g₀ g_bg a :
H^{a+1}(g₀) → Hᵃ(g₀)` is Fréchet differentiable at the origin, with a *bounded continuous linear*
derivative `B₁ : H^{a+1} →L[ℝ] Hᵃ`.

This is the genuine analytic content: a quasilinear (in the realized metric) second-order geometric
operator, composed with the smoothing realization `heatRepr` and the spectral coordinate read-off
`deTurckG0SpectralN`, is differentiable at a base point; and — because its second-order principal
symbol cancels against the linear rough Laplacian
(`deTurckNonlinearitySpectral_principalPart_cancels`, sorry-free) — its derivative drops only **one**
Sobolev derivative, so it is a genuinely first-order bounded operator `H^{a+1} →L Hᵃ` (no leftover
`−Δ_∇`: on the one-derivative-drop scale the second-order parts have already cancelled).  Its
boundedness as a `H^{a+1} → Hᵃ` map is the norm-level operator first-order-loss already proven over
the realized-remainder synthesis (`deTurckGenuineN_firstOrder_operatorTsumLoss`); the `HasFDerivAt`
content posited here is the *linear approximability* of `N` at the origin, the additional structure a
norm bound on the nonlinear map does not supply.

**Non-vacuous** — `HasFDerivAt N B₁ 0` genuinely pins `B₁` to the actual derivative: the witness
`B₁ = 0` would assert `N` has *zero* linear approximation at the origin, which is false because the
first-order content of the realized Ricci–DeTurck remainder (the `lieDerivCcSection`
deTurck-vector-field deformation and the first-order part of the curvature term, see
`deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv`) is a genuinely non-zero first-order differential
operator.  **Not packaging** — the conclusion is the linear-approximability of a concrete nonlinear
map, structurally distinct from any existential gauge correction; it does not assume the
fixed-point solvability it is later used to prove.  **Intrinsic** — stated over the `g`-inner
spectral tower `tensorHs`; no `chartJ`, no raw `M → E`.

The body is `sorry` — the Fréchet differentiability of the realized Ricci–DeTurck nonlinearity at the
origin (the genuine analytic frontier of the `A → B → D` gauge-solvability chain, the linearization
of the quasilinear elliptic operator over the heat-smoothed spectral realization). -/
theorem exists_deTurckFirstOrderCancelledLinearization
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ B₁ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ),
      HasFDerivAt (deTurckRealizeNonlinearityTower (I := I) g₀ g_bg a) B₁
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)) := by
  sorry

/-- **The first-order-cancelled DeTurck linearization `B₁ : H^{a+1} →L[ℝ] Hᵃ`.**

For the anchor `g₀` and a flow background `g_bg`, this is the bounded continuous linear operator
that is the Fréchet derivative at the origin of the concrete Ricci–DeTurck nonlinearity
`deTurckRealizeNonlinearityTower g₀ g_bg a : H^{a+1}(g₀) → Hᵃ(g₀)` — the genuinely **first-order**
remainder left once the second-order principal symbol of the realized right-hand side cancels against
the linear rough Laplacian `Δ_∇` (`deTurckNonlinearitySpectral_principalPart_cancels`).

It is a *bona-fide* operator on the complete inner-product tower `tensorHs` (`instCompleteSpace` /
`instInnerProductSpace`), so the Gårding-coercive linearization `L = −Δ_∇ + ι∘B₁` (formed downstream
by combining `tensorScaleLaplacian (a−1) : H^{a+1} →L H^{a−1}` with `B₁` post-composed with the
inclusion `Hᵃ ↪ H^{a−1}`) is a genuine bounded Hilbert operator; its bounded inverse (Lax–Milgram on
the complete tower) is the coercive-inverse node `B`, and the nonlinear Banach fixed point is `D`.

It is extracted from `exists_deTurckFirstOrderCancelledLinearization`; its defining linearization
property is `deTurckFirstOrderCancelledOperator_hasFDerivAt`.  Being a continuous linear map it is
automatically globally Lipschitz with constant `‖B₁‖₊` and is exactly the abstract first-order
remainder shape the strong-existence engine consumes
(`firstOrderRemainderCLM_strong_shortTime_exists`). -/
def deTurckFirstOrderCancelledOperator (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  (exists_deTurckFirstOrderCancelledLinearization (I := I) g₀ g_bg a).choose

/-- **The linearization identity: `B₁` is the Fréchet derivative at the origin of the concrete
Ricci–DeTurck nonlinearity.**

`deTurckFirstOrderCancelledOperator g₀ g_bg a` is the Fréchet derivative of
`deTurckRealizeNonlinearityTower g₀ g_bg a` at `0`.  This is the defining property of `B₁`: the
nonlinearity `N` is, to first order at the origin, the bounded first-order operator `B₁` (the
second-order principal part having cancelled), the linear approximation the coercive-inverse node `B`
and the Banach fixed point `D` build on. -/
theorem deTurckFirstOrderCancelledOperator_hasFDerivAt
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    HasFDerivAt (deTurckRealizeNonlinearityTower (I := I) g₀ g_bg a)
      (deTurckFirstOrderCancelledOperator (I := I) g₀ g_bg a)
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)) :=
  (exists_deTurckFirstOrderCancelledLinearization (I := I) g₀ g_bg a).choose_spec

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
