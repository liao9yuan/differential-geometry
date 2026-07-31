import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJet1Diff
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifJetTowerMatch
import DifferentialGeometry.Tensor.Mixed.Field

/-!
# Packaging fixed geometric fields as `SmoothCcTensor`s (the curvature case)

`UnifJetTowerMatch.lean` bridges the two jet towers in the *section → field*
direction: `ccUnitField` reads the metric-free `(0, s)`-field out of a
`SmoothCcTensor`, `iterCovGrad_unit_eq` matches the two towers at every order,
and `rfns_iterCovGrad_eq` matches the two pointwise norms.  What is missing for
the `Λ`-class curvature estimates of `UnifCurvatureJetsLow.lean` /
`UnifCurvatureJet1Diff.lean` — all of which are stated on the *field*
`metricRm04 g` in `iterCov`/`normSq0S` currency — is the opposite direction: a
`SmoothCcTensor` whose unit field **is** the given field.

That is what this file supplies.

## Main definitions

* `ccOfField g s A` — a smooth `(0, s)`-tensor field `A` on a closed manifold,
  packaged as a `SmoothCcTensor g 0 s`.  The section is the scalar extension
  `MixedSection.fromMultilinearSection`; compact support is automatic
  (`HasCompactSupport.of_compactSpace`), so no support hypothesis is needed
  beyond the ambient `[CompactSpace M]` that the whole HCG layer already
  carries.  Precedent: `deTurckRHSSection` (`DeTurckRHSSection.lean`), the
  `(0,2)` Ricci–DeTurck instance of exactly this construction.
* `rmSection g` — the lowered Riemann tensor `metricRm04 g` as a
  `SmoothCcTensor g 0 4`.

## Main results

* `ccOfField_unit`, `rmSection_unit` — the packaging is a section of
  `ccUnitField`: `ccUnitField g s (ccOfField g s A) = A`.
* `rfns_ccOfField_eq`, `rfns_rmSection_eq` — the **transport equations**.  For
  every order `j`, the `g`-fibre squared norm of `∇^j` of the packaged section
  (the `iteratedCovGrad`/`riemannianFiberNormSq` currency that the Bochner /
  `N(0)` consumers speak) *equals* the `normSq0S` of the intrinsic `iterCov`
  tower of the field (the currency every `Λ`-class curvature estimate is stated
  in).  Composing these with an `iterCov`-currency bound is a rewrite.
* `exists_rmJetSup`, `exists_rmJetSups` — the **fixed-metric** transported
  bounds: a finite sup of `|∇^a Rm(g)|²_g` in the section currency, at a single
  order `a` and uniformly over a window `j ≤ a`.  Transported from
  `exists_curvJet_sup`.
* `unifRmSecSup` — the **`Λ`-class, order `0`** transported bound:
  `|Rm(g₀)|²_{g₀} ≤ C²` in the section currency, with `C` closed in `(Λ, gBase)`
  before any class member is named.  Transported from `unifRm04Sup`.

## Scope — what is *not* here

Neither family closes brick E3's `hcurv`
(`Analysis/Spectral/Tensor/SobolevScale/UnifBochnerGap.lean`).  That hypothesis
asks for a bound on `‖∇^p (pointwiseTensorCurv g₀ r S)‖_{L²}` for an *arbitrary*
section `S`, i.e. a Leibniz/Kato product estimate for the curvature *action*,
whose curvature input at order `p` would be a **class-uniform all-order** sup of
`∇^a Rm`.  The class-uniform side is still open at every order `≥ 1` (the
Palatini difference brick, see `UnifCurvatureJet1Diff.md`), and the product rule
for `pointwiseTensorCurv` is a separate missing lemma.  So no `unifFc` is
defined here: what is delivered is exactly the fixed-metric all-order sup and
the class-uniform order-`0` sup, under those honest names.
-/

set_option autoImplicit false

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Tensor

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Packaging a fixed field as a compactly-supported smooth section -/

set_option linter.unusedSectionVars false in
/-- **A smooth `(0, s)`-tensor field, packaged as a `SmoothCcTensor`.**

The underlying section is the scalar extension
`MixedSection.fromMultilinearSection` of `A` into the hom bundle
`Tensor0SSpace 0 →L Tensor0SSpace s`; on a closed manifold compact support is
automatic.  The metric argument `g` only names the type. -/
def ccOfField (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ A
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **`ccOfField` is a section of `ccUnitField`.**  The unit value of the packaged
section is the field it was built from, at every rank. -/
@[simp] theorem ccOfField_unit (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    ccUnitField (I := I) g s (ccOfField (I := I) g s A) = A :=
  MixedSection.toMultilinearSection_fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ A

/-- **The transport equation for a packaged field.**

For every order `j`, the `g`-fibre squared norm of the section-level iterated
covariant gradient of `ccOfField g s A` equals the intrinsic `normSq0S` of the
`iterCov` tower of `A`.  This is `rfns_iterCovGrad_eq` composed with
`ccOfField_unit`; it converts any `iterCov`-currency pointwise estimate into the
`iteratedCovGrad`/`riemannianFiberNormSq` currency of the Bochner and `N(0)`
consumers. -/
theorem rfns_ccOfField_eq (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j (ccOfField (I := I) g s A)).toSection x) =
      normSq0S (I := I) g x (s + j) (iterCov (I := I) g s A j x) := by
  rw [rfns_iterCovGrad_eq (I := I) g s j (ccOfField (I := I) g s A) x, ccOfField_unit]

/-! ### The curvature instance -/

set_option linter.unusedSectionVars false in
/-- **The lowered Riemann tensor as a smooth compactly-supported `(0,4)`-section.**

`metricRm04 g` is the fixed, globally smooth `(0,4)` curvature field; on a closed
manifold it is compactly supported, so it packages directly.  This is the object
the `SmoothCcTensor`-valued Sobolev machinery consumes. -/
def rmSection (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 4 :=
  ccOfField (I := I) g 4 (metricRm04 (I := I) (M := M) g)

set_option linter.unusedSectionVars false in
/-- **The unit field of `rmSection` is `metricRm04`.**  This is the defining
property of the packaging. -/
@[simp] theorem rmSection_unit (g : SmoothRiemannianMetric I M) :
    ccUnitField (I := I) g 4 (rmSection (I := I) (M := M) g) =
      metricRm04 (I := I) (M := M) g :=
  ccOfField_unit (I := I) g 4 (metricRm04 (I := I) (M := M) g)

/-- **The curvature transport equation.**

`|∇^j Rm(g)|²_g` measured in the section currency
(`riemannianFiberNormSq` of `iteratedCovGrad … (rmSection g)`) equals the same
quantity measured in the intrinsic currency (`normSq0S` of
`iterCov g 4 (metricRm04 g) j`).  Every curvature estimate of
`UnifCurvatureJetsLow.lean` / `UnifCurvatureJet1Diff.lean` crosses to the
consumer shapes through this single rewrite. -/
theorem rfns_rmSection_eq (g : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j (rmSection (I := I) (M := M) g)).toSection x) =
      normSq0S (I := I) g x (4 + j)
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) j x) :=
  rfns_ccOfField_eq (I := I) g 4 j (metricRm04 (I := I) (M := M) g) x

/-! ### Fixed-metric transported sups (all orders) -/

/-- Squaring a square-root bound: the `Real.sqrt`-shaped conclusion of the
`iterCov`-currency sups versus the squared-norm shape the section-currency
consumers use. -/
private theorem sqLeOfSqrtLe {a K : ℝ} (ha : 0 ≤ a) (h : Real.sqrt a ≤ K) :
    a ≤ K ^ 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

/-- **Fixed-metric curvature-jet sup at order `a`, in the section currency.**

The `iteratedCovGrad`/`riemannianFiberNormSq` face of `exists_curvJet_sup`: for a
single smooth metric on a closed manifold, `∇^a Rm(g)` has a finite squared
fibre-norm sup.  No class currency and no curvature-difference input. -/
theorem exists_rmJetSup (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + a) x
          ((iteratedCovGrad (I := I) g 0 4 a (rmSection (I := I) (M := M) g)).toSection x) ≤
        K ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_curvJet_sup (I := I) (M := M) g a
  refine ⟨K, hK0, fun x => ?_⟩
  refine sqLeOfSqrtLe (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (4 + a) x _) ?_
  rw [rfns_rmSection_eq (I := I) g a x]
  exact hK x

/-- **One fixed-metric constant for the whole order window `j ≤ a`.**

The form the `N(0)`-style consumers ask for (`hsup` takes a single `Ksup` valid
for every `j` below a threshold).  Obtained from `exists_rmJetSup` by taking the
running maximum. -/
theorem exists_rmJetSups (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ a, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j (rmSection (I := I) (M := M) g)).toSection x) ≤
        K ^ 2 := by
  induction a with
  | zero =>
      obtain ⟨K, hK0, hK⟩ := exists_rmJetSup (I := I) (M := M) g 0
      refine ⟨K, hK0, fun j hj x => ?_⟩
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact hK x
  | succ a ih =>
      obtain ⟨K, hK0, hK⟩ := ih
      obtain ⟨K', hK'0, hK'⟩ := exists_rmJetSup (I := I) (M := M) g (a + 1)
      refine ⟨max K K', le_trans hK0 (le_max_left _ _), fun j hj x => ?_⟩
      rcases eq_or_lt_of_le hj with rfl | hlt
      · have hmono : K' ^ 2 ≤ max K K' ^ 2 := by nlinarith [le_max_right K K']
        exact le_trans (hK' x) hmono
      · have hmono : K ^ 2 ≤ max K K' ^ 2 := by nlinarith [le_max_left K K']
        exact le_trans (hK j (Nat.lt_succ_iff.mp hlt) x) hmono

/-! ### The `Λ`-class transported sup (order `0`) -/

set_option linter.unusedSectionVars false in
/-- **Class-uniform order-`0` curvature sup, in the section currency.**

The `iteratedCovGrad`/`riemannianFiberNormSq` face of `unifRm04Sup`: under
`Λ`-comparability of `g₀` with `gBase` and the class metric-jet bounds at orders
`1` and `2`, the `g₀`-fibre squared norm of `rmSection g₀` is bounded by a
constant closed in `(Λ, gBase)` alone — no class member is named.

This is the order-`0` half of what brick E3 needs; the orders `≥ 1` are still
open (they wait on the Palatini difference identity, `UnifCurvatureJet1Diff.md`),
so this is deliberately *not* packaged as a curvature-order function. -/
theorem unifRmSecSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((rmSection (I := I) (M := M) g₀).toSection x) ≤ C ^ 2 := by
  obtain ⟨C, hC0, hC⟩ :=
    unifRm04Sup (I := I) (M := M) gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2
  refine ⟨C, hC0, fun x => ?_⟩
  -- the order-`0` instance of the transport equation, with `4 + 0` reduced to `4`
  have hkey : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((rmSection (I := I) (M := M) g₀).toSection x) =
      normSq0S (I := I) g₀ x 4 (metricRm04 (I := I) (M := M) g₀ x) :=
    rfns_rmSection_eq (I := I) g₀ 0 x
  refine sqLeOfSqrtLe (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x _) ?_
  rw [hkey]
  exact hC x

end RicciFlow
end PDE
end DifferentialGeometry
