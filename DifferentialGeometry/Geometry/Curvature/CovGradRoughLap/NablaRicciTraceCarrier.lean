import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism

/-!
# The differentiated-Ricci-trace carrier `(∇_X Ric)(∇S)` and its smooth global section

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file constructs the
**differentiated-Ricci-trace carrier section** — the `∇`-derivative analogue of the Ricci-trace
carrier `ricTraceSection` (`RicciTraceCarrier`). It is the first-class, reusable, global-section
carrier of the differentiated-Ricci action `∇Ric · (∇S)` that the frame-summed covariant
integration-by-parts engine `integral_frameSummed_covDeriv_combined_eq_zero`
(`MovingFrameIntegratedNullity`) consumes as `SmoothCcTensor` currency.

## The smooth differentiated-Ricci endomorphism field

The differentiated-Ricci endomorphism `nablaRicciEndo g X x` (the `(1, 1)`-raise of the
differentiated Ricci tensor `(∇_X Ric)`, `DifferentiatedRicciEndomorphism`) is here proven to be a
**smooth section of the endomorphism bundle** (`nablaRicciEndo_contMDiff`) for every fixed smooth
derivation field `X`. The proof mirrors `ricEndoRaisedFib_contMDiff` (`RicciTraceCarrier`):

* `nablaRicci_contMDiff` — the differentiated-Ricci scalar `b ↦ (∇_X Ric)(V, W)(b)` is `C^∞` for
  smooth fields `X, V, W`. Through `nablaRicci_def` it is the difference of the leading directional
  derivative `extDerivFun (fun c => Ric(V c, W c)) b (X b)` (smooth by `extDerivFunApply_contMDiff`
  on the smooth Ricci pairing `ricciTensor_pairing_contMDiff`) and the two Leibniz Ricci-pairing
  corrections `Ric(∇_X V, W)`, `Ric(V, ∇_X W)` (smooth by `covApply_contMDiffOn` for the
  Levi-Civita connection together with `ricciTensor_pairing_contMDiff`).
* `nablaRicciBilin_chartBasis_contMDiffOn` — the chart-basis component of the differentiated-Ricci
  covector field `b ↦ (∇_X Ric)(Y, eⱼ^α)(b)` is `C^∞` on each chart source. At each point the
  chart-basis field is globalised to a smooth global field eventually-equal near the point
  (`exists_contMDiffSection_eqOn_nhd`); `nablaRicci`'s value-determinacy `nablaRicci_eq_of_VW_eq`
  then rewrites the bilinear chart evaluation to the global `nablaRicci`, smooth by
  `nablaRicci_contMDiff`.
* `nablaRicciEndo_contMDiff` — feeding the chart-basis covector smoothness into
  `metricSharp_contMDiff_total` and `cotangentCov_clmSection_smooth_aux` lifts to total-space
  smoothness of `x ↦ nablaRicciEndo g X x`.

## The carrier

* `nablaRicSlotOpFib g X s x` — the leading-slot precomposition by `nablaRicciEndo g X x` of a
  `(0, s + 1)`-tensor (the `∇Ric`-analogue of `ricSlotOpFib`), a continuous linear endomorphism of
  the `(0, s + 1)`-fibre.
* `nablaRicSlotOpField g X s : SmoothCcTensor g (s + 1) (s + 1)` — the fixed smooth operator field,
  smooth by `nablaRicSlotOpFib_contMDiff`.
* `nablaRicTraceSection g X s S : SmoothCcTensor g 0 (s + 1)` — the operator-field action
  `appCc (nablaRicSlotOpField g X s) (∇S)` of the field on `∇S = covGrad g 0 s S`, the smooth
  global section the frame-summed IBP engine reads.

## Reading lemmas

* `nablaRicSlotOpFib_apply_eval`, `nablaRicTraceSection_apply_leadingSlot` — the leading covariant
  slot `v0` is read first, the differentiated-Ricci endomorphism `nablaRicciEndo g X x` acts on it,
  and the remaining gradient slot is evaluated. With the public defining inner law
  `inner_nablaRicciEndo` (`g.inner x (nablaRicciEndo g X x v) w = (∇_X Ric)(v, w)`) the raised
  leading slot is the differentiated-Ricci contraction, identifying this carrier with the genuine
  `∇Ric`-trace content.

## Convention

`Ric := ricciTensor g` of the Levi-Civita connection; `(∇_X Ric)` is `nablaRicci`
(`ContractedBianchi`); all fibre operations are intrinsic to the metric `g`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle Tensor0SNabla

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Smoothness of the differentiated-Ricci endomorphism field -/

omit [CompactSpace M] in
/-- **Global smoothness of the differentiated-Ricci scalar.** For smooth fields `X, V, W` the
differentiated-Ricci scalar `b ↦ (∇_X Ric)(V, W)(b) = nablaRicci g X V W b` is `C^∞`. Through
`nablaRicci_def` it is the difference of the leading directional derivative of the smooth Ricci
pairing (`extDerivFunApply_contMDiff` on `ricciTensor_pairing_contMDiff`) and the two Leibniz
Ricci-pairing corrections with `∇_X` inserted into a slot (`covApply_contMDiffOn` for the
Levi-Civita connection together with `ricciTensor_pairing_contMDiff`). -/
theorem nablaRicci_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => V c) (fun c => W c) b) := by
  classical
  have hfun : (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => V c) (fun c => W c) b) =
      (fun b : M =>
        extDerivFun (I := I) (fun c => ricciTensor (I := I) g c (V c) (W c)) b (X b)
        - ricciTensor (I := I) g b ((LeviCivita (I := I) g).toFun (fun c => V c) b (X b)) (W b)
        - ricciTensor (I := I) g b (V b) ((LeviCivita (I := I) g).toFun (fun c => W c) b (X b))) := by
    funext b; rw [nablaRicci_def]
  rw [hfun]
  have hricVW : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun c : M => ricciTensor (I := I) g c (V c) (W c)) :=
    ricciTensor_pairing_contMDiff (I := I) g V.contMDiff W.contMDiff
  have hterm1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => extDerivFun (I := I) (fun c => ricciTensor (I := I) g c (V c) (W c)) b (X b)) :=
    extDerivFunApply_contMDiff (I := I) hricVW X.contMDiff
  have hcovV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (fun c => X c) (fun c => V c))) := by
    have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun c => V c)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact V.contMDiff
    exact contMDiffOn_univ.mp (covApply_contMDiffOn (I := I) (cov := LeviCivita (I := I) g)
      (X := fun c => X c) (Z := fun c => V c) X.contMDiff hZ)
  have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (fun c => X c) (fun c => W c))) := by
    have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun c => W c)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact W.contMDiff
    exact contMDiffOn_univ.mp (covApply_contMDiffOn (I := I) (cov := LeviCivita (I := I) g)
      (X := fun c => X c) (Z := fun c => W c) X.contMDiff hZ)
  have hterm2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b
        ((LeviCivita (I := I) g).toFun (fun c => V c) b (X b)) (W b)) :=
    ricciTensor_pairing_contMDiff (I := I) g hcovV W.contMDiff
  have hterm3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b (V b)
        ((LeviCivita (I := I) g).toFun (fun c => W c) b (X b))) :=
    ricciTensor_pairing_contMDiff (I := I) g V.contMDiff hcovW
  exact (hterm1.sub hterm2).sub hterm3

set_option linter.unusedSectionVars false in
/-- **Chart-source smoothness of the differentiated-Ricci covector chart component.** The chart-basis
component `b ↦ (∇_X Ric)(Y, eⱼ^α)(b) = nablaRicciBilin g X b (Y b) (chartBasisVecFiber α j b)` is
`C^∞` on the source of the chart at `α`. At each point the chart-basis field is globalised to a
smooth global field eventually-equal near the point (`exists_contMDiffSection_eqOn_nhd`);
`nablaRicci`'s two-slot value-determinacy `nablaRicci_eq_of_VW_eq` rewrites the bilinear chart
evaluation to the global differentiated-Ricci scalar, smooth by `nablaRicci_contMDiff`. -/
theorem nablaRicciBilin_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicciBilin (I := I) g X b (Y b) (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have hbasis_src : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) α j)
      (chartAt H α).source := by
    have h := chartBasisVec_contMDiffOn (I := I) α j
    rwa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] at h
  obtain ⟨s', hs'_eq⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (F := E) (V := fun b : M => TangentSpace I b) (n := (⊤ : ℕ∞))
    (s := fun _ : Unit => fun b : M => chartBasisVecFiber (I := I) α j b)
    (u := (chartAt H α).source) (p := x₀)
    (fun _ => hbasis_src) ((chartAt H α).open_source) hx₀
  set Yext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := s' () with hYext_def
  have hYext_eq : ∀ᶠ b in 𝓝 x₀, Yext b = chartBasisVecFiber (I := I) α j b := by
    filter_upwards [hs'_eq] with b hb using hb ()
  have hrw : (fun b : M => nablaRicciBilin (I := I) g X b (Y b)
        (chartBasisVecFiber (I := I) α j b)) =ᶠ[𝓝 x₀]
      (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => Y c) (fun c => Yext c) b) := by
    filter_upwards [hYext_eq] with b hb
    change nablaRicci (I := I) g (fun c => X c)
          (fun c => smoothExtensionTangent (I := I) b (Y b) c)
          (fun c => smoothExtensionTangent (I := I) b (chartBasisVecFiber (I := I) α j b) c) b =
        nablaRicci (I := I) g (fun c => X c) (fun c => Y c) (fun c => Yext c) b
    refine nablaRicci_eq_of_VW_eq (g := g) X
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) b (Y b))
        (smoothExtensionTangent_contMDiff (I := I) b (Y b))) Y
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) b (chartBasisVecFiber (I := I) α j b))
        (smoothExtensionTangent_contMDiff (I := I) b (chartBasisVecFiber (I := I) α j b))) Yext b
      ?_ ?_
    · change smoothExtensionTangent (I := I) b (Y b) b = Y b
      exact smoothExtensionTangent_eq (I := I) b (Y b)
    · change smoothExtensionTangent (I := I) b (chartBasisVecFiber (I := I) α j b) b = Yext b
      rw [smoothExtensionTangent_eq (I := I) b (chartBasisVecFiber (I := I) α j b), hb]
  have hsmooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicci (I := I) g (fun c => X c) (fun c => Y c) (fun c => Yext c) b) x₀ :=
    (nablaRicci_contMDiff (I := I) g X Y Yext).contMDiffAt
  have hAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => nablaRicciBilin (I := I) g X b (Y b) (chartBasisVecFiber (I := I) α j b)) x₀ :=
    hsmooth.congr_of_eventuallyEq hrw
  exact hAt.contMDiffWithinAt

set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the differentiated-Ricci endomorphism field.** For a fixed smooth
derivation field `X`, the `(1, 1)`-operator field `x ↦ nablaRicciEndo g X x` is a smooth section of
the endomorphism bundle. By `cotangentCov_clmSection_smooth_aux` it suffices that for every smooth
tangent field `Y` the section `x ↦ nablaRicciEndo g X x (Y x) = metricSharp g x ((∇_X Ric)(Y, ·))`
is smooth; that is the metric sharp (`metricSharp_contMDiff_total`) of the differentiated-Ricci
covector field, whose chart-basis components are smooth on each chart source
(`nablaRicciBilin_chartBasis_contMDiffOn`). -/
theorem nablaRicciEndo_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (nablaRicciEndo (I := I) g X x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => nablaRicciEndo (I := I) g X x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (nablaRicciBilin (I := I) g X b (Y b))
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source :=
    fun α j => nablaRicciBilin_chartBasis_contMDiffOn (I := I) g X Y α j
  have hsmooth := metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => nablaRicciBilin (I := I) g X b (Y b)) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (nablaRicciBilin (I := I) g X x (Y x))) =
    TotalSpace.mk' E x (nablaRicciEndo (I := I) g X x (Y x))
  congr 1

/-! ### The leading-slot differentiated-Ricci operator field and the trace carrier -/

set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot differentiated-Ricci fibre operator `nablaRicSlotOpFib g X s x`.** On a
`(0, s + 1)`-tensor `D` it precomposes the leading covariant slot with the differentiated-Ricci
endomorphism `nablaRicciEndo g X x`: the conjugation of right-composition by `nablaRicciEndo g X x`
through the leading-slot currying equivalence `tensor0S_curry`. The `∇Ric`-analogue of
`ricSlotOpFib`. -/
def nablaRicSlotOpFib (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
            (nablaRicciEndo (I := I) g X x))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_comp,
          map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_comp,
          map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `nablaRicSlotOpFib`. -/
@[simp] lemma nablaRicSlotOpFib_apply (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) :
    nablaRicSlotOpFib (I := I) (M := M) g X s x D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
          (nablaRicciEndo (I := I) g X x)) := by
  rw [nablaRicSlotOpFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot differentiated-Ricci operator reads the new slot first.** On a tuple
`Fin.cons v0 vs`, the operator reads `v0` off the leading covariant slot, applies the
differentiated-Ricci endomorphism `nablaRicciEndo g X x` to it, and evaluates the curried tensor at
the resulting direction and `vs`. -/
lemma nablaRicSlotOpFib_apply_eval (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (nablaRicSlotOpFib (I := I) (M := M) g X s x D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D
          (nablaRicciEndo (I := I) g X x v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (nablaRicSlotOpFib (I := I) (M := M) g X s x D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (nablaRicSlotOpFib (I := I) (M := M) g X s x D) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
        (nablaRicciEndo (I := I) g X x) := by
    rw [nablaRicSlotOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the leading-slot differentiated-Ricci operator field.** For a fixed
smooth derivation field `X`, the fibre field `x ↦ nablaRicSlotOpFib g X s x` is a smooth section of
the `(s + 1, s + 1)`-tensor bundle. By `contMDiff_clm_section_of_pointwise` it suffices that for
every smooth `(0, s + 1)`-tensor `Y` the section `x ↦ nablaRicSlotOpFib g X s x (Y x)` is smooth;
that value is the uncurry (`contMDiff_uncurriedSection_of_contMDiff_homSection`) of the smooth
`Hom(TM, T^{(0,s)})`-section `x ↦ (tensor0S_curry s x (Y x)).comp (nablaRicciEndo g X x)`, smooth as
the right-composition of the smooth curried section of `Y` with the smooth differentiated-Ricci
endomorphism field (`nablaRicciEndo_contMDiff`, `ContMDiff.clm_bundle_apply`). -/
theorem nablaRicSlotOpFib_contMDiff (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1) I z) x
        (nablaRicSlotOpFib (I := I) (M := M) g X s x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => nablaRicSlotOpFib (I := I) (M := M) g X s x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (nablaRicSlotOpFib (I := I) (M := M) g X s x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (nablaRicciEndo (I := I) g X x)))) := by
    funext x
    rw [nablaRicSlotOpFib_apply]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
    fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (nablaRicciEndo (I := I) g X x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
        (nablaRicciEndo (I := I) g X x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (nablaRicciEndo (I := I) g X x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)
          (nablaRicciEndo (I := I) g X x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (nablaRicciEndo (I := I) g X x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) (nablaRicciEndo_contMDiff (I := I) g X) Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
      (nablaRicciEndo (I := I) g X x)) hG

set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot differentiated-Ricci operator field `nablaRicSlotOpField g X s`**, as a
smooth compactly-supported `(s + 1, s + 1)`-tensor section. Its fibre value at `x` is the
leading-slot differentiated-Ricci operator `nablaRicSlotOpFib g X s x` (smooth by
`nablaRicSlotOpFib_contMDiff`); on the closed manifold it has compact support. The `∇Ric`-analogue
of `ricSlotOpField`. -/
def nablaRicSlotOpField (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) :
    SmoothCcTensor g (s + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 1) (s + 1) I x from nablaRicSlotOpFib (I := I) (M := M) g X s x)
      contMDiff_toFun := nablaRicSlotOpFib_contMDiff (I := I) (M := M) g X s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `nablaRicSlotOpField g X s` at `x` is the fibre operator
`nablaRicSlotOpFib g X s x`. Definitional. -/
@[simp] lemma nablaRicSlotOpField_toSection (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M) :
    (nablaRicSlotOpField (I := I) (M := M) g X s).toSection x =
      (show TensorRSSpace (s + 1) (s + 1) I x from
        nablaRicSlotOpFib (I := I) (M := M) g X s x) := rfl

/-- **The differentiated-Ricci-trace carrier `(∇_X Ric)(∇S)`.** For a smooth compactly-supported
`(0, s)`-tensor `S` and a fixed smooth derivation field `X`, the operator-field action of the
leading-slot differentiated-Ricci operator field `nablaRicSlotOpField g X s` on `∇S =
covGrad g 0 s S`:
```
nablaRicTraceSection g X s S := appCc (nablaRicSlotOpField g X s) (∇S),
```
the differentiated-Ricci-trace contraction `∑ⱼ (∇_X Ric)(·, eⱼ) (∇S)(eⱼ, …)`, a smooth
compactly-supported `(0, s + 1)`-tensor. The `∇Ric`-analogue of `ricTraceSection`; the smooth
global section the frame-summed covariant IBP engine
`integral_frameSummed_covDeriv_combined_eq_zero` consumes. -/
def nablaRicTraceSection (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g (s + 1) (s + 1)
    (nablaRicSlotOpField (I := I) (M := M) g X s) (covGrad (I := I) (M := M) g 0 s S)

set_option linter.unusedSectionVars false in
/-- **The fibre value of `nablaRicTraceSection`** is the fibrewise composition
`nablaRicSlotOpFib.comp (∇S)`. Definitional via `appCc_toSection`. -/
@[simp] lemma nablaRicTraceSection_toSection (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x =
      (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (nablaRicSlotOpField (I := I) (M := M) g X s).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  rw [nablaRicTraceSection,
    appCc_toSection (I := I) (M := M) g (s + 1) (s + 1)
      (nablaRicSlotOpField (I := I) (M := M) g X s) (covGrad (I := I) (M := M) g 0 s S) x]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The general-rank differentiated-Ricci-trace carrier reading.** The unit-`(0, 0)`-evaluation of
`nablaRicTraceSection g X s S`, read on a tuple `Fin.cons v0 vs`, equals the unit-evaluation of
`∇S = covGrad g 0 s S` with the **leading slot** precomposed by the differentiated-Ricci
endomorphism `nablaRicciEndo g X x`:
```
toModel ((nablaRicTraceSection g X s S)(unit)) (v0 ::ᵥ vs)
  = toModel ((∇S)(unit)) (nablaRicciEndo g X x v0 ::ᵥ vs).
```
With the public defining inner law `inner_nablaRicciEndo`
(`g.inner x (nablaRicciEndo g X x v) w = (∇_X Ric)(v, w)`) the raised leading slot is the
differentiated-Ricci contraction, identifying this carrier with the genuine `∇Ric`-trace content.
Proof mirrors `ricTraceSection_apply_leadingSlot`. -/
theorem nablaRicTraceSection_apply_leadingSlot
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v0 : E) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (nablaRicciEndo (I := I) g X x v0) vs) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (nablaRicTraceSection (I := I) (M := M) g X s S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      nablaRicSlotOpFib (I := I) (M := M) g X s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [nablaRicTraceSection_toSection, nablaRicSlotOpField_toSection]
    rfl
  rw [hval]
  rw [nablaRicSlotOpFib_apply_eval (I := I) (M := M) g X s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v0 vs]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (nablaRicciEndo (I := I) g X x v0) vs]

end Connection
end Integral
end DifferentialGeometry

end
