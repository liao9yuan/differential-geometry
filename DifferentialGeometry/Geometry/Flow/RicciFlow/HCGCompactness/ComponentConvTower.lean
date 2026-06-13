import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceDeriv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Covariant-tower component convergence (P3 Gap B, `componentConv_covDeriv_of_chartCInf`)

The `a ≥ 1` covariant tower of the metric component convergence.  The induction
runs on the bump-extended chart representative of the level-`p` tower scalar
`s_p^V(w) = (∇^p_gRef A0) w (V·w)` (`A0 = metricTensorField g`), using the existing
A2 machinery:

* `MetricPreconv.fderiv_chartRep_eq_towerStep` — the chart `fderiv` of `s_p^V`
  along a chart-constant direction `v` is the chart rep of `towerStep` (the
  level-`(p+1)` scalar plus the `gRef`-Christoffel corrections), as a germ.
* `MapCInfConvOnCompacts.fderivApply` (B2) — directional-derivative closure.
* `MapCInfConvOnCompacts.mulLeft`/`.sum`/`.add` (producer 3) — convergence algebra.
* `MapCInfConvOnCompacts.congr` — locality, to transfer convergence across the
  germ identity / where the global sections equal the chart-constant frame.

This file currently provides the foundational `ContDiff` and the directional-step
plumbing; the full induction is assembled on top.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The chart representative of a level-`p` tower scalar `s_p^V` is `ContDiffOn`
the extended-chart target. -/
theorem chartRep_towerScalar_contDiffOn
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)))
      (extChartAt I x₀).target := by
  intro z hz
  have hy : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hz
  have hzeq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hcd := contDiffAt_chartRep (I := I)
    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w))
    (covDerivOfField_eval_contMDiff (I := I) gRef A0 p V) x₀ hy
  rw [hzeq] at hcd
  exact hcd.contDiffWithinAt

/-- **Bump-extended level-`p` tower scalar is globally `ContDiff`.**  Multiplying
the chart representative of `s_p^V` by a smooth bump supported in the chart target
gives a globally smooth function on the model space — the form `MapCInfConvOnCompacts`
and its derivative/algebra closures (`fderivApply`, `mulLeft`, `sum`) consume. -/
theorem bumpTowerScalar_contDiff
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) z) :=
  bumpMul_contDiff (isOpen_extChartAt_target (I := I) x₀) hχ htsupp
    (chartRep_towerScalar_contDiffOn (I := I) gRef A0 p V x₀)

/-- **Per-point bridge: bump-carrier chart `fderiv` is the bump-extended tower
step.**  On an open `U` where the bump `χ ≡ 1` and whose chart preimage lies in
`Kc` (the germ region of `fderiv_chartRep_eq_towerStep`), the directional chart
`fderiv` of the bump-extended level-`p` scalar equals the bump-extended
`towerStep` chart rep.  (`χ ≡ 1` ⇒ bump-`fderiv` = unbump-`fderiv`; then the A2
germ identity.) -/
theorem bumpFderiv_eq_chartTowerStep
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (v : E)
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    {χ : E → Real} {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {z : E} (hz : z ∈ U) :
    fderiv Real (fun z' : E => χ z' * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) z') z v
      = χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (towerStep (I := I) gRef A0 p V σ) z := by
  set f : E → Real := writtenInExtChartAt I 𝓘(Real, Real) x₀
    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) with hf
  have hztarget : z ∈ (extChartAt I x₀).target := hUtarget hz
  have hsymm : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hztarget
  have hbumpeq : (fun z' : E => χ z' * f z') =ᶠ[nhds z] f := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [hχU hw]; simp
  have hfd : fderiv Real (fun z' : E => χ z' * f z') z = fderiv Real f z :=
    hbumpeq.fderiv_eq
  have hgerm := fderiv_chartRep_eq_towerStep (I := I) gRef A0 p V x₀ v σ hσ hKchart
    (hUKc z hz)
  rw [hsymm] at hgerm
  have hval : fderiv Real f z v =
      writtenInExtChartAt I 𝓘(Real, Real) x₀ (towerStep (I := I) gRef A0 p V σ) z :=
    hgerm.eq_of_nhds
  rw [show fderiv Real (fun z' : E => χ z' * f z') z v = fderiv Real f z v from by rw [hfd]]
  rw [hval, hχU hz]
  simp

/-- **Directional convergence step (tower-step form).**  If the bump-extended
level-`p` tower scalars converge `C^∞`-on-compacts on the open chart patch `U`,
then so do the bump-extended `towerStep` chart reps.  Combines `fderivApply` (B2)
with the per-point bridge `bumpFderiv_eq_chartTowerStep` via `congr`. -/
theorem bumpTowerStep_chartConv
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (v : E)
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    (hconv : MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef (A0Seq k) p V σ) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef A0inf p V σ) z) := by
  have hB2 := hconv.fderivApply
    (fun k => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p V x₀ hχ htsupp)
    (bumpTowerScalar_contDiff (I := I) gRef A0inf p V x₀ hχ htsupp) v
  refine hB2.congr hU (fun k z hz => ?_) (fun z hz => ?_)
  · exact (bumpFderiv_eq_chartTowerStep (I := I) gRef (A0Seq k) p V x₀ v σ hσ hKchart
      hU hχU hUKc hUtarget hz).symm
  · exact (bumpFderiv_eq_chartTowerStep (I := I) gRef A0inf p V x₀ v σ hσ hKchart
      hU hχU hUKc hUtarget hz).symm

end HCGCompactness
end DifferentialGeometry
