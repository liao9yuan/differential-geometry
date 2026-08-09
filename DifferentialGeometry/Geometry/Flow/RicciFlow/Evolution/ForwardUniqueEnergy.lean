import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueFields
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Kotschwar forward-uniqueness energy and its exact first variation (Route-K brick K3)

`ForwardUniqueFields.lean` supplies the three covariant difference carriers `h₀₂`, `A₀₃`,
`S₀₄` and their `g₁`-squared norms `metricDiffSq`, `connDiffSq`, `rmDiffSq`.  This file
assembles them into the Kotschwar energy of `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §3–§5,

`E(t) = ∫_M (|h₀₂|² + |A₀₃|² + |S₀₄|²)_{g₁(t)} dμ_{g₁(t)}`,

and differentiates it exactly.  **No estimate is proved here**: the whole content is the
three moving-norm derivatives, the moving-volume derivative, and differentiation under the
compact integral.  The Grönwall-facing estimate `forwardUniqueRate ≤ K · E − κ · D` is a
separate brick.

## Main definitions

* `movingReact0S g x s Q W` — the rank-uniform metric-variation ("reaction") term in the
  time derivative of `normSq0S g x s W` when the carrier satisfies `∂ₜg = −2Q`.
* `forwardUniqueDensity g₁ g₂ t x` — the energy density `|h₀₂|² + |A₀₃|² + |S₀₄|²`.
* `forwardUniqueEnergy g₁ g₂` — the energy, integrated against the moving volume `dμ_{g₁ t}`.
* `metricDiffDot g₁ g₂ t x` — `∂ₜh₀₂ = −2(Ric₁ − Ric₂)`, the one carrier speed that the
  Ricci-flow equations alone determine.
* `forwardUniqueDensityDot`, `forwardUniqueRate` — the exact pointwise and integrated rates.

## Main results

* `normSq0S_moving_deriv` — the rank-uniform invariant moving-norm time derivative.
* `metricDiff_hasDerivAt` — `∂ₜh₀₂` from the two Ricci-flow equations.
* `density_hasDerivAt` — the exact pointwise derivative of the energy density.
* `forwardUniqueEnergy_hasDerivAt` — `HasDerivAt (forwardUniqueEnergy g₁ g₂) (forwardUniqueRate …) t`.

## Hypothesis discipline

The metric difference's carrier speed is determined by the two flows, so `metricDiffDot` is a
`def`, not an argument.  The connection- and curvature-difference speeds are **not** determined
by the metric equations; they are supplied as explicit arguments `Adot`, `Sdot` together with
plain `∀`-quantified `HasDerivAt` hypotheses, exactly as K1/K2 will produce them.  This is why
`forwardUniqueRate` carries `Adot` and `Sdot` in its signature — the same way `movingRate`
carries its background metric.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section MovingNorm

/-! ## The rank-uniform moving-norm time derivative

`Tensor0SBundle.hasDerivWithinAt_normSq0S_ricciFlow` is already rank-uniform, but it is
stated in a chosen tangent basis with component arrays.  The two lemmas below package it
invariantly: `movingReact0S` names the metric-variation term and `normSq0S_moving_deriv`
states the product rule with both inputs invariant.  Only the canonical finite basis
`Module.finBasis` occurs, and only inside the definition. -/

/-- The **rank-uniform moving-metric reaction**: the metric-variation contribution to
`∂ₜ (normSq0S g x s W)` when the carrier metric evolves by `∂ₜg = −2Q`.  It is the
inverse-metric contraction `ricReactionContract` of `Q` against `W ⊗ W`, evaluated in the
canonical finite tangent basis; `normSq0S_moving_deriv` identifies it as a genuine
derivative, so the choice of basis is immaterial. -/
def movingReact0S (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (Q : Tensor0SSpace 2 I x) (W : Tensor0SSpace s I x) : Real :=
  ricReactionContract
    (basisInvMetric (I := I) g x (Module.finBasis Real (TangentSpace I x)))
    (fun i j =>
      Q (fun a : Fin 2 =>
        if a = 0 then Module.finBasis Real (TangentSpace I x) i
        else Module.finBasis Real (TangentSpace I x) j))
    (fun I0 =>
      tensor0SComponent (I := I) W
        (fun i => Module.finBasis Real (TangentSpace I x) i) I0)
    (fun J0 =>
      tensor0SComponent (I := I) W
        (fun i => Module.finBasis Real (TangentSpace I x) i) J0)

/-- **Rank-uniform invariant moving-norm time derivative.**  If the carrier metric family
satisfies `∂ₜg = −2Q` at `t` and the `(0,s)` fiber family `T` has time derivative `Tdot`,
then

`∂ₜ (normSq0S (g t) x s (T t)) = movingReact0S (g t) x s Q (T t) + 2 ⟪Tdot, T t⟫`.

Both hypotheses and both conclusion terms are basis free.  This is the rank-`s` form of the
`(0,2)` pattern used by the moving Ricci–DeTurck energy; ranks `2`, `3`, `4` are what the
three Kotschwar carriers need. -/
theorem normSq0S_moving_deriv {s : Nat} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace 2 I x)
    (T : Real → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hT : ∀ v : Fin s → TangentSpace I x,
      HasDerivAt (fun r : Real => T r v) (Tdot v) t) :
    HasDerivAt (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (movingReact0S (I := I) (g t) x s Q (T t) +
        2 * inner0S (I := I) (g t) x s Tdot (T t)) t := by
  classical
  let basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  let gInv : Real →
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  let ric :
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j =>
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let gInvDt :
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j =>
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let Tdt : (Fin s → Fin (Module.finrank Real (TangentSpace I x))) → Real := fun I0 =>
    tensor0SComponent (I := I) Tdot (fun i => basis i) I0
  have hinvAll (r : Real) :
      MetricInverseInBasis (I := I) (g r) x basis (gInv r) := by
    simpa [gInv] using basisInvMetric_real (I := I) (g r) x basis
  have hgInv (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) Set.univ t := by
    simpa [gInv, gInvDt, ric] using
      (basisInv_time (I := I) g
        (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hTcomp (I0 : Fin s → Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) Set.univ t :=
    (hT fun a => basis (I0 a)).hasDerivWithinAt
  have hTdot (I0 : Fin s → Fin (Module.finrank Real (TangentSpace I x))) :
      tensor0SComponent (I := I) Tdot (fun i => basis i) I0 = Tdt I0 := rfl
  have hflow (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      gInvDt i j = 2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) * (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) * (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hbase :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I) (s := s) (u := Set.univ) (t := t)
      g gInv gInvDt ric T Tdt Tdot basis hinvAll hgInv hTcomp hTdot hflow
  exact hbase.hasDerivAt (by simp)

end MovingNorm

section Carriers

/-! ## The one carrier speed determined by the two flows

Under `∂ₜg₁ = −2Ric₁` and `∂ₜg₂ = −2Ric₂` the metric-difference carrier evolves by
`∂ₜh₀₂ = −2(Ric₁ − Ric₂)`, a zero-order expression in the two Ricci tensors.  The
connection- and curvature-difference speeds are *not* determined this way; they are the
K1/K2 outputs and enter the energy derivative as supplied arguments. -/

/-- `∂ₜh₀₂ = −2(Ric₁ − Ric₂)`, as a `(0,2)` fiber tensor built from the two canonical
metric Ricci tensors. -/
def metricDiffDot (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    Tensor0SSpace 2 I x :=
  (-2 : Real) •
    (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)

/-- The time derivative of the metric-difference carrier `h₀₂` under the two Ricci flows. -/
theorem metricDiff_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M) {x : M} {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (v : Fin 2 → TangentSpace I x) :
    HasDerivAt (fun r : Real => metricDiffAt (I := I) (g₁ r) (g₂ r) x v)
      (metricDiffDot (I := I) g₁ g₂ t x v) t := by
  classical
  have hslots :
      (fun a : Fin 2 => if a = 0 then v 0 else v 1) = v := by
    funext a
    fin_cases a <;> simp
  have hsub := (hPDE₁ (v 0) (v 1)).sub (hPDE₂ (v 0) (v 1))
  have hfun :
      (fun r : Real => metricDiffAt (I := I) (g₁ r) (g₂ r) x v) =
        fun r : Real => (g₁ r).inner x (v 0) (v 1) - (g₂ r).inner x (v 0) (v 1) := by
    funext r
    exact metricDiffAt_apply (I := I) (g₁ r) (g₂ r) x v
  have hval :
      metricDiffDot (I := I) g₁ g₂ t x v =
        (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
            (fun a : Fin 2 => if a = 0 then v 0 else v 1) -
          (-2 : Real) * metricRicciAt (I := I) (g₂ t) x
            (fun a : Fin 2 => if a = 0 then v 0 else v 1) := by
    have hsmul :
        metricDiffDot (I := I) g₁ g₂ t x v =
          (-2 : Real) •
            ((metricRicciAt (I := I) (g₁ t) x -
                metricRicciAt (I := I) (g₂ t) x) v) :=
      Tensor0SSpace.smul_apply (I := I) 2 x (-2 : Real)
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) v
    have hdiff :
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) v =
          metricRicciAt (I := I) (g₁ t) x v - metricRicciAt (I := I) (g₂ t) x v :=
      Tensor0SSpace.sub_apply (I := I) 2 x
        (metricRicciAt (I := I) (g₁ t) x) (metricRicciAt (I := I) (g₂ t) x) v
    rw [hsmul, hdiff, hslots]
    simp only [smul_eq_mul]
    ring
  rw [hfun, hval]
  exact hsub

end Carriers

section Energy

variable [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The energy, its density, and the exact rate -/

/-- The Kotschwar energy density `|h₀₂|² + |A₀₃|² + |S₀₄|²`, all three norms taken in the
moving carrier `g₁ t`. -/
def forwardUniqueDensity (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    Real :=
  metricDiffSq (I := I) (g₁ t) (g₂ t) x + connDiffSq (I := I) (g₁ t) (g₂ t) x +
    rmDiffSq (I := I) (g₁ t) (g₂ t) x

/-- **The Kotschwar forward-uniqueness energy**
`E(t) = ∫_M (|h₀₂|² + |A₀₃|² + |S₀₄|²)_{g₁(t)} dμ_{g₁(t)}`.

The measure is the moving Riemannian volume of the carrier `g₁`, so that one metric supplies
the connection, the fiber inner product, and the measure simultaneously. -/
def forwardUniqueEnergy (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) : Real :=
  ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)

/-- The exact pointwise time derivative of the energy density: for each of the three
carriers, its moving-metric reaction plus twice its pairing with its own speed.  Only the
metric-difference speed is computed (`metricDiffDot`); the connection- and
curvature-difference speeds `Adot`, `Sdot` are supplied. -/
def forwardUniqueDensityDot
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (t : Real) (x : M) : Real :=
  (movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x)) +
  (movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
      (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
      (connDiffLowAt (I := I) (g₁ t) (g₂ t) x)) +
  (movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))

/-- **The exact energy rate.**  The integrand is the pointwise density derivative plus the
moving-volume term `½ tr_{g₁}(∂ₜg₁) · density`; under Ricci flow the latter factor is
`−scal(g₁)`, but no such identification is used here.  No estimate is involved: this is
literally the derivative produced by `forwardUniqueEnergy_hasDerivAt`. -/
def forwardUniqueRate
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (t : Real) : Real :=
  ∫ x, forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x +
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
        forwardUniqueDensity (I := I) g₁ g₂ t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)

/-- The exact pointwise derivative of the energy density: three applications of
`normSq0S_moving_deriv` with the common carrier speed `Q = Ric₁`. -/
theorem density_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    {x : M} {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ v : Fin 3 → TangentSpace I x,
      HasDerivAt (fun r : Real => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Adot t x v) t)
    (hS : ∀ v : Fin 4 → TangentSpace I x,
      HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Sdot t x v) t) :
    HasDerivAt (fun r : Real => forwardUniqueDensity (I := I) g₁ g₂ r x)
      (forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x) t := by
  have hh :
      HasDerivAt (fun r : Real => metricDiffSq (I := I) (g₁ r) (g₂ r) x)
        (movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
            (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
          2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
            (metricDiffAt (I := I) (g₁ t) (g₂ t) x)) t :=
    normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (fun r => metricDiffAt (I := I) (g₁ r) (g₂ r) x)
      (metricDiffDot (I := I) g₁ g₂ t x) hPDE₁
      (metricDiff_hasDerivAt (I := I) g₁ g₂ hPDE₁ hPDE₂)
  have hA' :
      HasDerivAt (fun r : Real => connDiffSq (I := I) (g₁ r) (g₂ r) x)
        (movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
            (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
          2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
            (connDiffLowAt (I := I) (g₁ t) (g₂ t) x)) t :=
    normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (fun r => connDiffLowAt (I := I) (g₁ r) (g₂ r) x) (Adot t x) hPDE₁ hA
  have hS' :
      HasDerivAt (fun r : Real => rmDiffSq (I := I) (g₁ r) (g₂ r) x)
        (movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
          2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)) t :=
    normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (fun r => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x) (Sdot t x) hPDE₁ hS
  exact (hh.add hA').add hS'

/-- **Exact first variation of the Kotschwar forward-uniqueness energy.**

On an open time window `U` the energy is differentiable with derivative exactly
`forwardUniqueRate`.  The hypotheses are: joint chart-Gram smoothness of the *carrier*
`g₁` (this is what the moving volume measure needs), joint smoothness of the scalar energy
density (the regularity input for differentiating under the compact integral), the two
Ricci-flow equations, and the two supplied carrier speeds for `A₀₃` and `S₀₄`.

No estimate occurs: cf. `forwardUniqueRate_le`, which is the separate analytic brick. -/
theorem forwardUniqueEnergy_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    {U : Set Real} {t : Real} (hU : IsOpen U) (ht : t ∈ U)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdens : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (U ×ˢ (Set.univ : Set M)))
    (hPDE₁ : ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : Real => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Adot t x v) t)
    (hS : ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Sdot t x v) t) :
    HasDerivAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
      (forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t) t := by
  have hbase := first_var_joint (I := I) (M := M) hU ht hgram hdens
  have hval :
      (∫ x, (deriv (fun s : Real => forwardUniqueDensity (I := I) g₁ g₂ s x) t +
            (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
              forwardUniqueDensity (I := I) g₁ g₂ t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)) =
        forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t := by
    simp only [forwardUniqueRate]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [(density_hasDerivAt (I := I) g₁ g₂ Adot Sdot
      (hPDE₁ x) (hPDE₂ x) (hA x) (hS x)).deriv]
  exact hbase.congr_deriv hval

end Energy

end DifferentialGeometry.PDE.RicciFlow

end
