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

set_option linter.unusedVariables false in
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
    {S : Set M} (hUS : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ S)
    (hexpand : ∀ w ∈ S, (V j) w = ∑ i ∈ s, c i w • frame i w)
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
      ∀ q ∈ S,
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
  · have hχz : χ z = 1 := (hχU hz).trans (Pi.one_apply z)
    simp only [writtenInExtChartAt_real_apply, hχz, one_mul]
    rw [hmulti (A0Seq k) ((extChartAt I x₀).symm z) (hUS z hz)]
    simp only [smul_eq_mul]
  · have hχz : χ z = 1 := (hχU hz).trans (Pi.one_apply z)
    simp only [writtenInExtChartAt_real_apply, hχz, one_mul]
    rw [hmulti A0inf ((extChartAt I x₀).symm z) (hUS z hz)]
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

/-- The bump-extended `towerStep` chart rep is globally `ContDiff` — obtained from
the `bumpTowerStep_split` (`bump-towerStep = bump-s_{p+1} + Σ bump-corrections`),
each summand a `bumpTowerScalar_contDiff`.  Needed as the minuend smoothness for
`MapCInfConvOnCompacts.sub` in the induction step. -/
theorem bumpTowerStepScalar_contDiff
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V' : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x₀ : M) {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef A0 p V' σ) z) := by
  have heq : (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef A0 p V' σ) z)
      = (fun z : E =>
          (χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
              (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
          + ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
                (fun b => (Function.update V' a
                  (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                      (I := I) gRef) σ (V' a))) b w)) z) := by
    funext z
    have h := bumpTowerStep_split (I := I) gRef A0 p V' σ x₀ χ z
    linarith [h]
  rw [heq]
  have hcons :
      (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w)))
        = (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
            (fun a : Fin (p + 3) =>
              (Fin.cons σ V' : Fin (p + 3) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M → Type _)) a w)) := by
    funext w
    congr 1
    funext a
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  refine ContDiff.add ?_ (ContDiff.sum fun a _ => ?_)
  · rw [hcons]
    exact bumpTowerScalar_contDiff (I := I) gRef A0 (p + 1) (Fin.cons σ V') x₀ hχ htsupp
  · exact bumpTowerScalar_contDiff (I := I) gRef A0 p
      (Function.update V' a
        (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) gRef)
          σ (V' a))) x₀ hχ htsupp

/-- **Per-frame-index convergence (induction step core).**  Given the level-`p`
inductive hypothesis (convergence of the bump carriers for ALL section tuples) and
a chart-constant leading slot `σ` (`= tangentConstInChart x₀ v` near `Kc`), the
bump carrier of the level-`(p+1)` tuple `Fin.cons σ V'` converges.  Combines the
directional step (`bumpTowerStep_chartConv`, from IH at `V'`), the correction
convergences (IH at the `covSection`-updated tuples), `MapCInfConvOnCompacts.sub`,
and the `towerStep` split. -/
theorem bumpTowerCons_conv
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
    {Kc : Set M} (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    (v : E) (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (V' : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (IH : ∀ (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z) := by
  classical
  set corrSec : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun a => covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) gRef)
      σ (V' a) with hcorrSec
  have hTS := bumpTowerStep_chartConv (I := I) gRef A0Seq A0inf p V' x₀ v σ hσ hKchart
    hχ htsupp hU hχU hUKc hUtarget (IH V')
  have hSumCorr := MapCInfConvOnCompacts.sum (Finset.univ : Finset (Fin (p + 2)))
    (fun a => IH (Function.update V' a (corrSec a)))
    (fun a k => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
    (fun a => bumpTowerScalar_contDiff (I := I) gRef A0inf p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
  have hsub := hTS.sub hSumCorr
    (fun k => bumpTowerStepScalar_contDiff (I := I) gRef (A0Seq k) p V' σ x₀ hχ htsupp)
    (bumpTowerStepScalar_contDiff (I := I) gRef A0inf p V' σ x₀ hχ htsupp)
    (fun k => ContDiff.sum fun a _ => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
    (ContDiff.sum fun a _ => bumpTowerScalar_contDiff (I := I) gRef A0inf p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
  have hfeq_seq : (fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
      = fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef (A0Seq k) p V' σ) z
          - ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w
                (fun b => (Function.update V' a (corrSec a)) b w)) z := by
    funext k z
    exact bumpTowerStep_split (I := I) gRef (A0Seq k) p V' σ x₀ χ z
  have hfeq_inf : (fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
      = fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef A0inf p V' σ) z
          - ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w
                (fun b => (Function.update V' a (corrSec a)) b w)) z := by
    funext z
    exact bumpTowerStep_split (I := I) gRef A0inf p V' σ x₀ χ z
  rw [hfeq_seq, hfeq_inf]
  exact hsub

/-- **The covariant-tower convergence induction step.**  If the level-`p` bump
carriers converge for ALL section tuples (IH), so do the level-`(p+1)` bump
carriers.  Expand the leading slot of `W` in the frame (`bumpTower_slotExpand_conv`,
chart-constant `frameᵢ`), reducing to the frame-leading case handled by
`bumpTowerCons_conv` (bridging `update W 0 frameᵢ` to `Fin.cons frameᵢ (tail W)`). -/
theorem bumpTowerCarrier_step
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
    {Kc : Set M} (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (vbasis : ι → E)
    (hframeσ : ∀ i, ∀ᶠ x in 𝓝ˢ Kc,
      frame i x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (vbasis i) x)
    (hspan : ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        ∃ c : ι → M → Real,
          (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
            (chartAt H x₀).source)
          ∧ ∀ w ∈ Kc, W0 w = ∑ i ∈ s, c i w • frame i w)
    (IH : ∀ (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z))
    (W : Fin (p + 3) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w (fun a => W a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w (fun a => W a w)) z) := by
  classical
  obtain ⟨c, hc, hexpand⟩ := hspan (W 0)
  refine bumpTower_slotExpand_conv (I := I) gRef A0Seq A0inf (p + 1) x₀ hχ htsupp
    hU hχU hUtarget s frame c hc W 0 hUKc hexpand ?_
  intro i
  have hslot : ∀ (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2),
      (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
          (fun a => (Function.update W 0 (frame i)) a w))
        = (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
            (Fin.cons (frame i w) (fun a : Fin (p + 2) => (Fin.tail W) a w))) := by
    intro A0
    funext w
    congr 1
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simp [Fin.tail]
  have hbr_seq : (fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
          (fun a => (Function.update W 0 (frame i)) a w)) z)
      = fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
            (Fin.cons (frame i w) (fun a : Fin (p + 2) => (Fin.tail W) a w))) z := by
    funext k z
    rw [hslot (A0Seq k)]
  have hbr_inf : (fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
          (fun a => (Function.update W 0 (frame i)) a w)) z)
      = fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
            (Fin.cons (frame i w) (fun a : Fin (p + 2) => (Fin.tail W) a w))) z := by
    funext z
    rw [hslot A0inf]
  rw [hbr_seq, hbr_inf]
  exact bumpTowerCons_conv (I := I) gRef A0Seq A0inf p x₀ hχ htsupp hU hχU hUtarget
    hKchart hUKc (vbasis i) (frame i) (hframeσ i) (Fin.tail W) IH

/-- **All-levels covariant-tower convergence (the `Nat.rec` induction).**  From the
order-`0` base (`hbase`) and the step `bumpTowerCarrier_step`, the bump carriers of
EVERY section tuple at EVERY covariant order `a` converge `C^∞`-on-compacts on `U`,
along the single subsequence baked into `A0Seq`. -/
theorem bumpTowerCarrier_all
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {Kc : Set M} (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (vbasis : ι → E)
    (hframeσ : ∀ i, ∀ᶠ x in 𝓝ˢ Kc,
      frame i x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (vbasis i) x)
    (hspan : ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        ∃ c : ι → M → Real,
          (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
            (chartAt H x₀).source)
          ∧ ∀ w ∈ Kc, W0 w = ∑ i ∈ s, c i w • frame i w)
    (hbase : ∀ (V : Fin (0 + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w (fun a => V a w)) z)) :
    ∀ (a : ℕ) (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) a) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf a) w (fun a => V a w)) z) := by
  intro a
  induction a with
  | zero => exact hbase
  | succ p IH =>
    exact bumpTowerCarrier_step (I := I) gRef A0Seq A0inf p x₀ hχ htsupp hU hχU hUtarget
      hKchart hUKc s frame vbasis hframeσ hspan IH

/-- **Frame-data package** for `bumpTowerCarrier_all`/`bumpTowerCarrier_step`.  For a
compact `Kc` inside a chart, produces global smooth sections `frame` agreeing with
the chart-constant coordinate frame `tangentConstInChart x₀ (finBasis i)` near `Kc`,
together with `hspan`: every smooth section's coordinate-frame coefficients are
smooth on the chart source and reconstruct it on `Kc`.  Built from
`exists_section_eqOn_compact` (globalization) and the Mathlib local-frame API
(`localFrame_coeff` smoothness `contMDiffOn_baseSet_localFrame_coeff` +
`eq_sum_localFrame_coeff_smul`), bridged to `tangentConstInChart` via `symmL`. -/
theorem exists_frameData (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _))
      (vbasis : Fin (Module.finrank Real E) → E),
      (∀ i, ∀ᶠ x in 𝓝ˢ Kc,
        frame i x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (vbasis i) x)
      ∧ ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
          ∃ c : Fin (Module.finrank Real E) → M → Real,
            (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
              (chartAt H x₀).source)
            ∧ ∀ w ∈ Kc, W0 w = ∑ i : Fin (Module.finrank Real E), c i w • frame i w := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
  set b := Module.finBasis Real E with hb
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := Real) (I := I) x₀
  have hσex : ∀ i : Fin (Module.finrank Real E),
      ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) x :=
    fun i => exists_section_eqOn_compact (I := I) x₀ (b i) hKc hKchart
  choose frame hframeσ using hσex
  refine ⟨frame, b, hframeσ, fun W0 => ⟨fun i w => e.localFrame_coeff I b i w (W0 w), ?_, ?_⟩⟩
  · intro i
    rw [← hbase]
    exact contMDiffOn_baseSet_localFrame_coeff b W0.contMDiff.contMDiffOn i
  · intro w hw
    have hwbase : w ∈ e.baseSet := by rw [hbase]; exact hKchart hw
    have hexp := e.eq_sum_localFrame_coeff_smul (I := I) (b := b)
      (s := (W0 : ∀ x : M, TangentSpace I x)) hwbase
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hframe_eq : frame i w = tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) w :=
      (hframeσ i).self_of_nhdsSet w hw
    have hlf_eq : e.localFrame b i w = tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) w := by
      rw [e.localFrame_apply_of_mem_baseSet b hwbase]
      simp [Bundle.Trivialization.basisAt, tangentConstInChart_apply, he]
    show e.localFrame_coeff I b i w (W0 w) • e.localFrame b i w
        = e.localFrame_coeff I b i w (W0 w) • frame i w
    rw [hlf_eq, hframe_eq]

/-- **Order-`0` base for an arbitrary section pair, from the frame-pair
convergence.**  Frame-expand BOTH slots of a `Fin 2` section tuple via
`bumpTower_slotExpand_conv` (using `hspan`), reducing the order-`0` carrier of any
`V : Fin 2 → ContMDiffSection` to the frame-pair carriers `![frameᵢ, frameⱼ]`.  This
is the `hbase` input to `bumpTowerCarrier_all`, given the (diagonalised) B0
frame-pair convergence `hpairs`. -/
theorem hbase_of_framePairs
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {Kc : Set M} (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hspan : ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        ∃ c : ι → M → Real,
          (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
            (chartAt H x₀).source)
          ∧ ∀ w ∈ Kc, W0 w = ∑ i ∈ s, c i w • frame i w)
    (hpairs : ∀ (i j : ι), MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z))
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w (fun a => V a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w (fun a => V a w)) z) := by
  classical
  obtain ⟨c0, hc0, hexp0⟩ := hspan (V 0)
  refine bumpTower_slotExpand_conv (I := I) gRef A0Seq A0inf 0 x₀ hχ htsupp
    hU hχU hUtarget s frame c0 hc0 V 0 hUKc hexp0 ?_
  intro i
  obtain ⟨c1, hc1, hexp1⟩ := hspan (V 1)
  have hexp1' : ∀ w ∈ Kc, (Function.update V 0 (frame i)) 1 w = ∑ j ∈ s, c1 j w • frame j w := by
    intro w hw
    rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    exact hexp1 w hw
  refine bumpTower_slotExpand_conv (I := I) gRef A0Seq A0inf 0 x₀ hχ htsupp
    hU hχU hUtarget s frame c1 hc1 (Function.update V 0 (frame i)) 1 hUKc hexp1' ?_
  intro j
  have hbridge : ∀ (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2),
      (fun w : M => (covDerivOfField (I := I) gRef A0 0) w
          (fun a => (Function.update (Function.update V 0 (frame i)) 1 (frame j)) a w))
        = (fun w : M => (covDerivOfField (I := I) gRef A0 0) w
            (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) := by
    intro A0
    funext w
    congr 1
    funext a
    fin_cases a <;>
      simp [Function.update_of_ne, Function.update_self]
  have hbr_seq : (fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w
          (fun a => (Function.update (Function.update V 0 (frame i)) 1 (frame j)) a w)) z)
      = fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w
            (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z := by
    funext k z; rw [hbridge (A0Seq k)]
  have hbr_inf : (fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w
          (fun a => (Function.update (Function.update V 0 (frame i)) 1 (frame j)) a w)) z)
      = fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w
            (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z := by
    funext z; rw [hbridge A0inf]
  rw [hbr_seq, hbr_inf]
  exact hpairs i j

end HCGCompactness
end DifferentialGeometry
