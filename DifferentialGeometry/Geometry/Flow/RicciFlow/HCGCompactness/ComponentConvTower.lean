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

/-- The chart representative of a function smooth on the chart source is
`ContDiffOn` the extended-chart target.  (General version of
`chartRep_towerScalar_contDiffOn`, for the frame-coefficient functions that are
only smooth on the chart domain.) -/
theorem chartRep_contDiffOn (f : M → Real) (x₀ : M)
    (hf : ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f (chartAt H x₀).source) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀).target := by
  have hsymm : ContMDiffOn 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (extChartAt I x₀).symm (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have hmaps : Set.MapsTo (extChartAt I x₀).symm (extChartAt I x₀).target
      (chartAt H x₀).source := by
    intro z hz
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hz
  have hcomp : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target := hf.comp hsymm hmaps
  have hcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    contMDiffOn_iff_contDiffOn.mp hcomp
  have hwrite : writtenInExtChartAt I 𝓘(Real, Real) x₀ f
      = f ∘ (extChartAt I x₀).symm := by funext z; simp [writtenInExtChartAt]
  rw [hwrite]; exact hcd

/-- **Multilinear frame-expansion convergence.**  If one slot `j` of the section
tuple `V` is, on the chart source, the finite combination `∑ᵢ cᵢ • frameᵢ` of a
section family with smooth coefficients `cᵢ`, then the bump-extended level-`p`
tower carrier of `V` converges `C^∞`-on-compacts whenever each carrier of the
slot-replaced tuple `update V j frameᵢ` does.  (Multilinearity of
`covDerivOfField … w` in the slots + `mulLeft`/`sum`; the `χ²`/coefficient locality
is absorbed by `congr` on `U`.)  Used for the leading-slot expansion of the
`p → p+1` step and the order-`0` base. -/
theorem bumpTower_slotExpand_conv
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ) (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (c : ι → M → Real)
    (hc : ∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
      (chartAt H x₀).source)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (j : Fin (p + 2))
    (hexpand : ∀ w ∈ (chartAt H x₀).source,
      (V j) w = ∑ i ∈ s, c i w • frame i w)
    (hconv : ∀ i, MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w
          (fun a => (Function.update V j (frame i)) a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w
          (fun a => (Function.update V j (frame i)) a w)) z)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z) := by
  classical
  -- bump-extended coefficient `χ · chartRep(cᵢ)` is globally smooth
  have hg : ∀ i, ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀ (c i) z) :=
    fun i => bumpMul_contDiff (isOpen_extChartAt_target (I := I) x₀) hχ htsupp
      (chartRep_contDiffOn (I := I) (c i) x₀ (hc i))
  -- slot-replaced carriers are globally smooth
  have hcarrSeq : ∀ (i : ι) (k : ℕ), ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w
          (fun a => (Function.update V j (frame i)) a w)) z) :=
    fun i k => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p
      (Function.update V j (frame i)) x₀ hχ htsupp
  have hcarrInf : ∀ i : ι, ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w
          (fun a => (Function.update V j (frame i)) a w)) z) :=
    fun i => bumpTowerScalar_contDiff (I := I) gRef A0inf p
      (Function.update V j (frame i)) x₀ hχ htsupp
  -- each `gᵢ · carrierᵢ` converges, then sum over `s`
  have hsum := MapCInfConvOnCompacts.sum s
    (fun i => (hconv i).mulLeft (hg i) (fun k => hcarrSeq i k) (hcarrInf i))
    (fun i k => (hg i).mul (hcarrSeq i k)) (fun i => (hg i).mul (hcarrInf i))
  -- pointwise multilinear expansion, valid for every base field `A0` on the chart source
  have hmulti : ∀ (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2),
      ∀ q ∈ (chartAt H x₀).source,
      (covDerivOfField (I := I) gRef A0 p) q (fun a => V a q)
        = ∑ i ∈ s, c i q •
            (covDerivOfField (I := I) gRef A0 p) q
              (fun a => (Function.update V j (frame i)) a q) := by
    intro A0 q hq
    have hupd : ∀ i : ι,
        Function.update (fun a => V a q) j (frame i q)
          = fun a => (Function.update V j (frame i)) a q := by
      intro i
      funext a
      by_cases h : a = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    have hstep1 : (fun a => V a q)
        = Function.update (fun a => V a q) j (∑ i ∈ s, c i q • frame i q) := by
      rw [← hexpand q hq]
      exact (Function.update_eq_self j (fun a => V a q)).symm
    calc
      (covDerivOfField (I := I) gRef A0 p) q (fun a => V a q)
          = (covDerivOfField (I := I) gRef A0 p) q
              (Function.update (fun a => V a q) j (∑ i ∈ s, c i q • frame i q)) := by
            rw [← hstep1]
      _ = ∑ i ∈ s, (covDerivOfField (I := I) gRef A0 p) q
              (Function.update (fun a => V a q) j (c i q • frame i q)) := by
            simpa using ((covDerivOfField (I := I) gRef A0 p) q).toMultilinearMap.map_update_sum
              s j (fun i => c i q • frame i q) (fun a => V a q)
      _ = ∑ i ∈ s, c i q • (covDerivOfField (I := I) gRef A0 p) q
              (fun a => (Function.update V j (frame i)) a q) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [((covDerivOfField (I := I) gRef A0 p) q).map_update_smul, hupd i]
  -- the carrier of `V` agrees on `U` with the `Σ` of `gᵢ · carrierᵢ`
  refine hsum.congr hU (fun k z hz => ?_) (fun z hz => ?_)
  · have hsrc : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target (hUtarget hz)
    have hχz : χ z = 1 := (hχU hz).trans (Pi.one_apply z)
    simp only [writtenInExtChartAt_real_apply, hχz, one_mul]
    rw [hmulti (A0Seq k) ((extChartAt I x₀).symm z) hsrc]
    simp only [smul_eq_mul]
  · have hsrc : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target (hUtarget hz)
    have hχz : χ z = 1 := (hχU hz).trans (Pi.one_apply z)
    simp only [writtenInExtChartAt_real_apply, hχz, one_mul]
    rw [hmulti A0inf ((extChartAt I x₀).symm z) hsrc]
    simp only [smul_eq_mul]

/-- **`towerStep` split.**  Pointwise, the bump-extended level-`(p+1)` carrier with
leading slot `σ` is the bump-extended `towerStep` minus the bump-extended
`gRef`-Christoffel corrections, each of which is itself a level-`p` carrier for the
section tuple `update V' a (∇_σ V'ₐ)` (the covariant-derivative slot realised as a
`covSection`).  This is the algebraic identity behind extracting `s_{p+1}` from the
directional step via `MapCInfConvOnCompacts.sub`. -/
theorem bumpTowerStep_split
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V' : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x₀ : M) (χ : E → Real) (z : E) :
    χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z
      = χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (towerStep (I := I) gRef A0 p V' σ) z
        - ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
              (fun b => (Function.update V' a
                (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                    (I := I) gRef) σ (V' a))) b w)) z := by
  simp only [writtenInExtChartAt_real_apply, towerStep]
  set q : M := (extChartAt I x₀).symm z with hq
  have hupd : ∀ a : Fin (p + 2),
      (fun b : Fin (p + 2) =>
          (Function.update V' a
            (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                (I := I) gRef) σ (V' a))) b q)
        = Function.update (fun b : Fin (p + 2) => V' b q) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => V' a r) q) (σ q)) := by
    intro a
    funext b
    by_cases h : b = a
    · subst h; simp [covSection_apply]
    · simp [Function.update_of_ne h]
  simp only [hupd]
  rw [mul_add, Finset.mul_sum]
  ring

end HCGCompactness
end DifferentialGeometry
