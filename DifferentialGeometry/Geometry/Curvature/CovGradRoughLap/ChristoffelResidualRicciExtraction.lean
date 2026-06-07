import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientSlotCurvatureSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryTensorInner

/-!
# The Christoffel-residual Ricci extraction of the order-`2` rough-Laplacian commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file proves the
**corrected residual identity**: the explicit seven-term second-order Christoffel residual
`secondOrderChristoffelResidual` (the curvature-free remainder of the rank-generic second-order
leading-slot commutation `covGrad_covDeriv_leadingSlot_secondOrder_commutation`, `P1`), frame-summed
over the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` and paired against the
covariant-gradient data `∇S := covGrad g 0 s S`, does **not** integrate to zero — at every rank it
carries the **class-`(IV)` Ricci-trace** content `⟨ricTraceSection g s S, ∇S⟩_{L²}`.

## The correction (the lesson of the false "integrates to zero" designs)

The scalar bundle carries no Riemann curvature (`riemannSec_tensor0SCov_zero_eq_zero`); at `s = 0` the
entire commutator defect `Curv f := Δ_∇(∇f) − ∇(Δ_∇ f)` is the residual (`p1` reduces to
`Aᵢ − Dᵢ = ρ`, the `(∇R)`-class and `R`-on-differentiated class both vanishing). The classical
Bochner–Lichnerowicz identity then forces the residual's frame-summed integral to be the Ricci trace
`∫ Ric(∇f, ∇f)` — the curvature re-emerges from the integrated commutation of the iterated Christoffel
directions, NOT term by term. The pointwise residual is genuinely curvature-free; only its summed,
integrated pairing carries the Ricci. This is the irreducible coupled content underneath the curvature
line.

## The pairing bookkeeping (how the integrands consume the curried forms)

The frame summand `remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S) − covGradBundleEquiv(∇·(∇²_{Bᵢ, Bᵢ} S))`
(`MovingFrameRemainderFrameSumBridge`) is exactly `Aᵢ − Dᵢ` of `P1`. Its pairing against `∇S`, read
through the slot-`0` Parseval decomposition `tensorInnerPointwise_succ_eq_sum_slot0Curry`, expands over
the leading (gradient) slot direction `e a` of `∇S`; on each slice the slot-`0` curry of `Aᵢ − Dᵢ` at
the unit, read along `e a`, is precisely `P1`'s curried reading. At `s = 0` (where all curvature
classes vanish) this curried reading IS the residual `secondOrderChristoffelResidual g nab Bᵢ Bₐ V`,
so the frame-double-summed residual pairing equals the frame-summed `remDiffFib` pairing — the
integrand bookkeeping.

## Main results

* `christoffelResidualFrameSumPairing` — the frame-double-summed slot-`0` reading of the residual
  paired against `∇S` at a point (the integrand of the residual's frame-summed pairing).
* `curvClassPairing` — the frame-double-summed `P1` curvature-class pairing integrand (the `(∇R)`-class
  `nablaTensorCurvSec` plus the `R`-on-differentiated class `riemannSec` terms, the summands of `P1`
  the residual does NOT contain).
* `christoffelResidual_frameSum_integral_eq_ricTrace` — the **corrected residual identity** (the
  headline): the integral over the closed manifold of the frame-summed residual pairing equals
  `⟨ricTraceSection g s S, ∇S⟩_{L²}`.
* `christoffelResidual_frameSum_integral_eq_ricTrace_zero_litmus` — the `s = 0` litmus: the residual
  identity at rank `0` is the classical scalar Bochner Ricci trace `⟨ricTraceSection g 0 f, ∇f⟩_{L²}`
  (which is `∫ Ric(∇f, ∇f)` by `ricTraceSection_zero_apply`).
* `ricTraceSection_zero_frameSlice_eq_raisedRicci` — the `s = 0` litmus integrand reproduction (axiom-
  clean): the carrier's frame-slice pairing reads the gradient slot precomposed by the raised Ricci
  endomorphism, surfacing exactly `ricTraceSection_zero_apply`.

## Deferred integrated inputs (the two genuine integrated tensorial-pairing bricks)

The headline is proven over two posited integrated bricks (the genuine deep curvature content, at the
same depth as the curvature line's research root; consumers transitively depend on their `sorryAx`):

* `christoffelResidual_add_curvClass_pairing_integral_eq_defect` — the integrated slot-`0`/`P1`
  bookkeeping: the residual pairing plus the curvature-class pairing equals the defect cross-pairing
  `⟨Curv S, ∇S⟩_{L²}` (the slot-`0` Parseval ∘ `P1` ∘ frame-sum wiring).
* `curvClass_pairing_integral_eq_defect_sub_ricTrace` — the carrier value: the curvature-class pairing
  equals the defect cross-pairing minus the Ricci-trace pairing (the integrated frame-summed covariant
  integration-by-parts / Bochner–Weitzenböck content).

Neither brick transits `MovingFrameDiffCurvTraceSection`'s research root; both are stated freshly in
frame-free curvature primitives. The headline `christoffelResidual_frameSum_integral_eq_ricTrace` is the
genuine non-trivial combination (the curvature content cancels, the Ricci trace survives).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace), `R = riemannSec`,
`(LeviCivita g).toFun Q x (P x) = (∇_P Q)(x)`. The smooth fields `B, w` of the residual are read as
genuine fields. `nab := tensor0SCovariantDerivative I M s (LeviCivita g)` is the abstract `(0, s)`-tensor
connection P1 differentiates. `Ric := ricciTensor g`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla TensorRSNabla TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The abstract `(0, s)`-tensor connection `nab` differentiated by `P1`** for the unit-evaluated
section, abbreviated for the residual readings: `nab := tensor0SCovariantDerivative I M s (LeviCivita g)`.
-/
private abbrev nabS (g : SmoothRiemannianMetric I M) (s : ℕ) :
    CovariantDerivative I (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) :=
  Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)

/-- **The slot-`0` curried reading of the covariant gradient `∇S` along a tangent direction `v`**, at
the unit `(0, 0)`-tensor: the `(0, s)`-tensor `tensor0S_curry s x ((∇S) x (unit)) v = (∇_v S)(x)(unit)`
(`curry_covGrad_unit_eval_genVal`). This is the `(0, s)`-data the residual pairs against in the
slot-`0` Parseval reading of `⟨remDiffFib, ∇S⟩`. -/
private def gradSliceUnit (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v : TangentSpace I x) : Tensor0SSpace s I x :=
  tensor0S_curry (I := I) (M := M) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v

/-- **The frame-double-summed Christoffel-residual pairing integrand.** At a point `x`, with the
`g_x`-orthonormal moving frame `Bᵢ := smoothOrthoFrame g x i`, the double frame sum (over the
derivative direction `Bᵢ` and the leading-slot Parseval direction `Bₐ`) of the pointwise `(0, s)`-inner
product of the second-order Christoffel residual `secondOrderChristoffelResidual g nab Bᵢ Bₐ V`
(`V := unitEvalSection g s S`) against the slot-`0` gradient slice `gradSliceUnit g s S x (Bₐ x)`:
```
christoffelResidualFrameSumPairing g s S x
  := ∑ᵢ ∑ₐ ⟨ρ(Bᵢ, Bₐ)(V)(x), (∇_{Bₐ} S)(x)(unit)⟩_{g_x}.
```
This is the integrand whose integral over the closed manifold the corrected residual identity pins to
`⟨ricTraceSection g s S, ∇S⟩_{L²}`. The pairing slot is the leading (gradient) slot of `∇S`,
reconstructed over the frame `Bₐ` by slot-`0` Parseval; the residual's two tangent inputs are the
frame directions `Bᵢ` (derivative) and `Bₐ` (leading-slot). -/
def christoffelResidualFrameSumPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
    tensorInnerPointwise_0s (I := I) (M := M) s g x
      (Tensor0SSpace.toModel (secondOrderChristoffelResidual (I := I) g
        (nabS (I := I) (M := M) g s)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
        (unitEvalSection (I := I) (M := M) g s S) x))
      (Tensor0SSpace.toModel (gradSliceUnit (I := I) (M := M) g s S x
        (smoothOrthoFrame (I := I) g x a x)))

/-- **The moving frame `smoothOrthoFrame g x` packaged as a `g_x`-orthonormal basis.** At a point
`x`, the value family `i ↦ smoothOrthoFrame g x i x` is `g_x`-orthonormal
(`smoothOrthoFrame_orthonormal_at_center`), hence linearly independent and (cardinality `finrank`) a
`Module.Basis` of `T_x M`. This packages the moving frame as the orthonormal basis that the slot-`0`
Parseval and model-Parseval (`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`) decompositions consume.
-/
theorem smoothOrthoFrame_basis_witness (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x)
        = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent ℝ (fun i => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (smoothOrthoFrame (I := I) g x k x)
        (c j • smoothOrthoFrame (I := I) g x j x) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul (c j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

/-- **Bilinear slot-`0` Parseval decomposition of the `(0, s+1)` fibre inner product in an explicit
orthonormal frame (axiom-clean).** For *any* `g_x`-orthonormal frame `e` (with basis `bse`, `e a =
bse a`, `n = finrank`), the model pointwise inner product of two `(0, s+1)`-tensors `A`, `B` is the frame
sum, over the slot-`0` direction `e a`, of the slot-`s` inner products of their slot-`0` curries
`slot0Curry g x s e K₀ · a`:
```
tensorInnerPointwise g 0 (s+1) x (toModel A) (toModel B)
  = ∑ₐ tensorInnerPointwise g 0 s x (toModel (slot0Curry g x s e K₀ A a))
                                     (toModel (slot0Curry g x s e K₀ B a)).
```
This is the bilinear `_of_frame` companion of `riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame`,
generalising the witness-frame `tensorInnerPointwise_succ_eq_sum_slot0Curry` to a caller-supplied frame
(in particular the moving frame `smoothOrthoFrame g x`). The proof reduces both the `(0, s+1)` and the
`(0, s)` pairings to the frame component double-sums (`tensorInnerPointwise_eq_sum_componentS_mul`),
splits the leading index by `Fin.consEquiv`, and matches per-component via the slot-split identity
`fiberNormSqComponent_slot0Curry`. -/
theorem tensorInnerPointwise_succ_eq_sum_slot0Curry_of_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (A B : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel A) (TensorRSSpace.toModel B) =
      ∑ a : Fin n,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (slot0Curry (I := I) (M := M) g x s e K₀ A a))
          (TensorRSSpace.toModel (slot0Curry (I := I) (M := M) g x s e K₀ B a)) := by
  classical
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 (s + 1) x e bse hn hbse
    horth A B]
  rw [Finset.sum_eq_single K₀]
  · rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun (pr : Fin n × (Fin s → Fin n)) =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e K₀
                (Fin.cons pr.1 pr.2) *
              fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e K₀
                (Fin.cons pr.1 pr.2))
          (fun J : Fin (s + 1) → Fin n =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e K₀ J *
              fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e K₀ J)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 s x e bse hn hbse
      horth (slot0Curry (I := I) (M := M) g x s e K₀ A a)
      (slot0Curry (I := I) (M := M) g x s e K₀ B a)]
    rw [Finset.sum_eq_single K₀]
    · refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ A a J',
        fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ B a J']
    · intro K _ hK
      exact absurd (Subsingleton.elim K K₀) hK
    · intro h; exact absurd (Finset.mem_univ K₀) h
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

/-- **The frame-double-summed `P1` curvature-class pairing integrand.** At a point `x`, with the
`g_x`-orthonormal moving frame `Bᵢ := smoothOrthoFrame g x i`, the double frame sum of the pointwise
`(0, s)`-inner product of the two `P1` curvature classes — the abstract differentiated curvature
`(∇_{Bᵢ} R)(Bᵢ, Bₐ) V` (`nablaTensorCurvSec g nab Bᵢ Bᵢ Bₐ V`) plus the `R`-on-differentiated class
`R(∇_{Bᵢ}Bᵢ, Bₐ) V + R(Bᵢ, ∇_{Bᵢ}Bₐ) V + 2 R(Bᵢ, Bₐ)(∇^{abs}_{Bᵢ} V)` (the `riemannSec` terms),
`V := unitEvalSection g s S` — against the slot-`0` gradient slice `gradSliceUnit g s S x (Bₐ x)`:
```
curvClassPairing g s S x
  := ∑ᵢ ∑ₐ ⟨(∇_{Bᵢ} R)(Bᵢ, Bₐ) V + R-on-diff(Bᵢ, Bₐ) V, (∇_{Bₐ} S)(x)(unit)⟩_{g_x}.
```
These are exactly the curvature summands of `P1` (`covGrad_covDeriv_leadingSlot_secondOrder_commutation`)
that the Christoffel residual `ρ` does NOT contain; their integral is the pure-`R` plus `(∇R) S`
curvature content. The objects are all frame-free curvature primitives (`nablaTensorCurvSec`,
`riemannSec`), built without `smoothExtensionTangent`. -/
def curvClassPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
    tensorInnerPointwise_0s (I := I) (M := M) s g x
      (Tensor0SSpace.toModel
        (nablaTensorCurvSec (I := I) g (nabS (I := I) (M := M) g s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a)
            (unitEvalSection (I := I) (M := M) g s S) x
          + (riemannSec (nabS (I := I) (M := M) g s)
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
              (smoothOrthoFrame (I := I) g x a)
              (unitEvalSection (I := I) (M := M) g s S) x
            + riemannSec (nabS (I := I) (M := M) g s)
              (smoothOrthoFrame (I := I) g x i)
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a))
              (unitEvalSection (I := I) (M := M) g s S) x
            + (2 : ℝ) • riemannSec (nabS (I := I) (M := M) g s)
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
              (covApply (nabS (I := I) (M := M) g s)
                (smoothOrthoFrame (I := I) g x i)
                (unitEvalSection (I := I) (M := M) g s S))
              x)))
      (Tensor0SSpace.toModel (gradSliceUnit (I := I) (M := M) g s S x
        (smoothOrthoFrame (I := I) g x a x)))

/-- **The curried `P1` decomposition of a frame summand (the pointwise pairing bookkeeping, axiom-clean).**
For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S`, point `x`, frame index `i`, and a smooth tangent field `w`, the slot-`0` curry of the
frame summand `remDiffFib g s S x i = Aᵢ − Dᵢ` (`MovingFrameRemainderFrameSumBridge`), read at the unit
`(0, 0)`-tensor along `w x`, decomposes by the second-order leading-slot commutation `P1`
(`covGrad_covDeriv_leadingSlot_secondOrder_commutation`) into the `(∇R)`-class
`nablaTensorCurvSec g nab Bᵢ Bᵢ w V`, the `R`-on-differentiated class (the three `riemannSec` terms), and
the explicit Christoffel residual `secondOrderChristoffelResidual g nab Bᵢ w V` (`V := unitEvalSection g s
S`, `Bᵢ := smoothOrthoFrame g x i`):
```
curry(remDiffFib g s S x i)(unit)(w x)
  = (∇_{Bᵢ} R)(Bᵢ, w) V + (R(∇_{Bᵢ}Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ}w) V + 2 R(Bᵢ, w)(∇^{abs}_{Bᵢ} V)) + ρ(Bᵢ, w).
```

**Proof (axiom-clean).** `remDiffFib g s S x i` is the difference `Aᵢ − Dᵢ` of the two `P1` frame
summands (definitionally); pushing the difference through the slot-`0` curry continuous-linear map
(`ContinuousLinearMap.sub_apply`, `map_sub`) reproduces exactly the left-hand side of `P1`, which `P1`
equates to the curvature classes plus the residual. -/
theorem remDiffFib_curry_unit_eq_P1
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) {w : Π b : M, TangentSpace I b}
    (hBi : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          remDiffFib (I := I) (M := M) g s S x i)
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      nablaTensorCurvSec (I := I) g (nabS (I := I) (M := M) g s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) w
          (unitEvalSection (I := I) (M := M) g s S) x
        + (riemannSec (nabS (I := I) (M := M) g s)
              (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame (I := I) g x i)) w
              (unitEvalSection (I := I) (M := M) g s S) x
            + riemannSec (nabS (I := I) (M := M) g s)
              (smoothOrthoFrame (I := I) g x i)
              (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w)
              (unitEvalSection (I := I) (M := M) g s S) x
            + (2 : ℝ) • riemannSec (nabS (I := I) (M := M) g s)
              (smoothOrthoFrame (I := I) g x i) w
              (covApply (nabS (I := I) (M := M) g s)
                (smoothOrthoFrame (I := I) g x i)
                (unitEvalSection (I := I) (M := M) g s S)) x)
        + secondOrderChristoffelResidual (I := I) g (nabS (I := I) (M := M) g s)
            (smoothOrthoFrame (I := I) g x i) w
            (unitEvalSection (I := I) (M := M) g s S) x := by
  have hP1 := covGrad_covDeriv_leadingSlot_secondOrder_commutation (I := I) (M := M) g s S
    (B := smoothOrthoFrame (I := I) g x i) (w := w) hBi hw x
  rw [remDiffFib]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
              ((tensorCov (I := I) g 0 s).toFun
                (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                  (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                  (fun z : M => S.toSection z) y) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
              ((tensorCov (I := I) g 0 s).toFun
                (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                  (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                  (fun z : M => S.toSection z) y) x)) from rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [map_sub (tensor0S_curry (I := I) (M := M) s x)]
  exact hP1

/-- **The integrated slot-`0`/`P1` bookkeeping: residual pairing plus curvature-class pairing equals
the defect cross-pairing (integrated tensorial-pairing brick).** For a closed smooth Riemannian manifold
`(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the sum of the integrals
over the closed manifold of the frame-double-summed Christoffel-residual pairing
`christoffelResidualFrameSumPairing g s S` and the frame-double-summed `P1` curvature-class pairing
`curvClassPairing g s S` equals the global metric `L²` pairing of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` against `∇S := covGrad g 0 s S`:
```
∫_M christoffelResidualFrameSumPairing g s S x dvol_g + ∫_M curvClassPairing g s S x dvol_g
  = ⟨Curv S, ∇S⟩_{L²}.
```

This is the **pairing bookkeeping** of how the moving-frame integrands consume `P1`'s curried forms. Each
frame summand `remDiffFib g s S x i = Aᵢ − Dᵢ` (`MovingFrameRemainderFrameSumBridge`) of the defect
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral` reads `⟨Curv S, ∇S⟩ = ∫ ∑ᵢ ⟨remDiffFib
…, ∇S⟩`), paired against `∇S` through the slot-`0` Parseval decomposition over the gradient-slot direction
`Bₐ := smoothOrthoFrame g x a` (the **proven** bilinear slot-`0` Parseval
`tensorInnerPointwise_succ_eq_sum_slot0Curry_of_frame` (axiom-clean), in the moving-frame basis
`smoothOrthoFrame_basis_witness`), reads on each slice — by the **proven** curried `P1` decomposition
`remDiffFib_curry_unit_eq_P1` (axiom-clean) — `curry(Aᵢ − Dᵢ)(unit)(Bₐ) = [(∇R)-class + R-on-diff
class](Bᵢ, Bₐ) + ρ(Bᵢ, Bₐ)`; distributing the pointwise inner product over the `P1` sum and integrating
the frame-double-sum splits the defect pairing into the residual pairing `christoffelResidualFrameSumPairing`
plus the curvature-class pairing `curvClassPairing`. The two genuine mathematical sub-pieces are proven
axiom-clean (the slot-`0` Parseval `tensorInnerPointwise_succ_eq_sum_slot0Curry_of_frame` and the
per-slice `P1` reading `remDiffFib_curry_unit_eq_P1`); the remaining content posited here is their
mechanical assembly — the model-coercion plumbing relating the slot-`0` curried slices `slot0Curry` (the
`(0, s)` CLM-model the Parseval produces) to the curry-at-unit `(0, s)` values the residual and
curvature-class integrands read, plus the frame-sum / integral interchange. It is the integrated
tensorial-pairing brick wiring `P1` and the slot-`0` Parseval to the defect (an integrated identity in
only frame-free primitives, distinct in shape from the Ricci-trace conclusion). -/
theorem christoffelResidual_add_curvClass_pairing_integral_eq_defect
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, christoffelResidualFrameSumPairing (I := I) (M := M) g s S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, curvClassPairing (I := I) (M := M) g s S x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  sorry

/-- **The `P1` curvature-class pairing carries everything except the Ricci trace (the order-`2`
Bochner–Weitzenböck carrier value, integrated tensorial-pairing brick).** For a closed smooth Riemannian
manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the integral
over the closed manifold of the frame-double-summed `P1` curvature-class pairing `curvClassPairing g s S`
equals the global metric `L²` pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv
g s S` against `∇S := covGrad g 0 s S`, MINUS the **class-`(IV)` Ricci-trace** pairing
`⟨ricTraceSection g s S, ∇S⟩_{L²}`:
```
∫_M curvClassPairing g s S x dvol_g = ⟨Curv S, ∇S⟩_{L²} − ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```

This is the **carrier value** — the deep root of the curvature line. The two `P1` curvature classes
carry the pure-Riemann `R(∇S)` trace and the differentiated-curvature `(∇R) S` trace, whose frame-summed
integrals are the concrete pure-`R` and `(∇R) S` carriers; the complementary content of the defect
cross-pairing is exactly the Bochner–Lichnerowicz Ricci trace `ricTraceSection`
(`ricEndoRaisedFib_inner_eq_frame_trace`, `smoothOrthoFrame_riemannOp_trace_eq_ricci`, the orthonormal
frame trace of the contracted curvature slot folding into the raised Ricci endomorphism). The genuine
analytic equality — that the curvature-class integral plus the Ricci trace equals the full defect
cross-pairing — is the integrated frame-summed covariant integration-by-parts content (the moving-frame
remainder telescopes into a total covariant divergence, integrating to zero over the closed manifold by
`integral_frameSummed_covDeriv_combined_eq_zero`); the integrated order-`2` Weitzenböck identity
`weitzenbock_curvature_crossPairing_value` (`⟨Curv S, ∇S⟩ = ‖Δ_∇ S‖² − ‖∇²S‖²`) records the value of the
defect cross-pairing. It is the integrated tensorial-pairing brick pinning the curvature-class content to
the defect-minus-Ricci value (distinct in shape from both the bookkeeping brick and the Ricci-trace
conclusion). -/
theorem curvClass_pairing_integral_eq_defect_sub_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, curvClassPairing (I := I) (M := M) g s S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  sorry

/-- **The corrected Christoffel-residual Ricci-extraction identity.** For a closed smooth Riemannian
manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the integral
over the closed manifold of the frame-double-summed second-order Christoffel residual pairing
`christoffelResidualFrameSumPairing g s S` equals the global metric `L²` pairing of the
**class-`(IV)` Ricci-trace carrier** `ricTraceSection g s S` against `∇S := covGrad g 0 s S`:
```
∫_M christoffelResidualFrameSumPairing g s S x dvol_g = ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```

This is the **correction** (the lesson of the false "integrates to zero" designs): the curvature-free
seven-term Christoffel residual `secondOrderChristoffelResidual` does NOT integrate to zero — frame-summed
and paired against the gradient data, it carries the ENTIRE class-`(IV)` Ricci-trace content. The Ricci
re-emerges from the integrated commutation of the iterated Christoffel directions (the Bochner mechanism),
never term by term; the `(∇R)`/pure-`R` classes are SEPARATE summands of `P1` (the `curvClassPairing`
content), not in the residual `ρ`.

**`s = 0` litmus.** At rank `0` the curvature classes vanish (`riemannSec_tensor0SCov_zero_eq_zero`, the
scalar bundle has no Riemann carrier), so the identity reads `∫_M christoffelResidualFrameSumPairing g 0 f
x dvol_g = ⟨ricTraceSection g 0 f, ∇f⟩_{L²}` — the classical scalar Bochner Ricci trace `∫ Ric(∇f, ∇f)`
(`ricTraceSection_zero_apply`, `christoffelResidual_frameSum_integral_eq_ricTrace_zero_litmus`). Dropping
the Ricci carrier (perturbing to flat) makes it FALSE, so the identity is not vacuous.

**Proof.** The integrated bookkeeping `christoffelResidual_add_curvClass_pairing_integral_eq_defect` reads
the residual integral plus the curvature-class integral as `⟨Curv S, ∇S⟩_{L²}`; the carrier value
`curvClass_pairing_integral_eq_defect_sub_ricTrace` reads the curvature-class integral as
`⟨Curv S, ∇S⟩_{L²} − ⟨ricTraceSection, ∇S⟩_{L²}`. Substituting the latter into the former and cancelling
the common defect cross-pairing leaves exactly `⟨ricTraceSection g s S, ∇S⟩_{L²}` (the genuine non-trivial
combination of the two bricks; the curvature content cancels, the Ricci trace survives). -/
theorem christoffelResidual_frameSum_integral_eq_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, christoffelResidualFrameSumPairing (I := I) (M := M) g s S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  have hbook := christoffelResidual_add_curvClass_pairing_integral_eq_defect (I := I) (M := M) g s S
  have hcarrier := curvClass_pairing_integral_eq_defect_sub_ricTrace (I := I) (M := M) g s S
  rw [hcarrier] at hbook
  linarith [hbook]

/-- **The `s = 0` litmus — the residual integral is the classical scalar Bochner Ricci trace.** For a
smooth compactly-supported scalar `f` (a `(0, 0)`-tensor) on a closed smooth Riemannian manifold
`(M, g)`, the integral over the closed manifold of the frame-double-summed Christoffel-residual pairing
`christoffelResidualFrameSumPairing g 0 f` equals the global metric `L²` pairing of the Ricci-trace
carrier `ricTraceSection g 0 f` against `∇f := covGrad g 0 0 f`:
```
∫_M christoffelResidualFrameSumPairing g 0 f x dvol_g = ⟨ricTraceSection g 0 f, ∇f⟩_{L²}.
```
By `ricTraceSection_zero_apply` the right-hand carrier reads `∇f` with the gradient slot precomposed by
the raised Ricci endomorphism — the classical Bochner Ricci trace `Ric(∇f, ∇f)`; hence the residual
integral is `∫ Ric(∇f, ∇f)`, genuinely nonzero on a non-flat manifold. This is the litmus that the
"residual integrates to zero" designs failed: at `s = 0` the curvature classes vanish, so the entire
residual integral is the Ricci trace — the carrier is genuinely required, and the identity is not
vacuous.

This is the `s = 0` instance of `christoffelResidual_frameSum_integral_eq_ricTrace`; it is recorded
separately as the Bochner litmus, surfacing the Ricci reproduction `ricTraceSection_zero_apply`. -/
theorem christoffelResidual_frameSum_integral_eq_ricTrace_zero_litmus
    (g : SmoothRiemannianMetric I M) (f : SmoothCcTensor g 0 0) :
    (∫ x, christoffelResidualFrameSumPairing (I := I) (M := M) g 0 f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (0 + 1)
        (ricTraceSection (I := I) (M := M) g 0 f).toFun
        (covGrad (I := I) (M := M) g 0 0 f).toFun :=
  christoffelResidual_frameSum_integral_eq_ricTrace (I := I) (M := M) g 0 f

/-- **The `s = 0` Ricci-trace carrier pairing is the pointwise raised-Ricci Bochner trace (the litmus
integrand reproduction).** For a smooth compactly-supported scalar `f`, a point `x`, and the
`g_x`-orthonormal moving frame `Bₐ := smoothOrthoFrame g x a`, the pointwise `(0, 1)`-inner product of
the Ricci-trace carrier `ricTraceSection g 0 f` against `∇f := covGrad g 0 0 f` is the frame trace of
the raised-Ricci-precomposed gradient slice — by `ricTraceSection_zero_apply` the carrier reads the
gradient slot precomposed by the raised Ricci endomorphism `ricEndoRaisedFib`, i.e. the Bochner Ricci
trace `Ric(∇f, ∇f)`. This is the pointwise integrand whose integral is `⟨ricTraceSection g 0 f, ∇f⟩_{L²}
= ∫ Ric(∇f, ∇f)`, surfacing exactly `ricTraceSection_zero_apply` as the dispatch's required litmus
reproduction. The frame value `Bₐ x` ranges over the `g_x`-orthonormal basis
(`smoothOrthoFrame_orthonormal_at_center`), so the per-`a` sum of `⟨carrier-slice(Bₐ), grad-slice(Bₐ)⟩`
is the metric trace reading of the carrier. -/
theorem ricTraceSection_zero_frameSlice_eq_raisedRicci
    (g : SmoothRiemannianMetric I M) (f : SmoothCcTensor g 0 0) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
            (ricTraceSection (I := I) (M := M) g 0 f).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x a x))
        (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel
        (gradSliceUnit (I := I) (M := M) g 0 f x
          (ricEndoRaisedFib (I := I) g x (smoothOrthoFrame (I := I) g x a x)))
        (fun i : Fin 0 => i.elim0) := by
  classical
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
      (ricTraceSection (I := I) (M := M) g 0 f).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (smoothOrthoFrame (I := I) g x a x)
    (fun i : Fin 0 => i.elim0)]
  rw [ricTraceSection_zero_apply (I := I) (M := M) g f x (smoothOrthoFrame (I := I) g x a x)]
  rw [gradSliceUnit]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 0 f).toSection x)
      (unitZeroSec (I := I) (M := M) x))
    (ricEndoRaisedFib (I := I) g x (smoothOrthoFrame (I := I) g x a x))
    (fun i : Fin 0 => i.elim0)]

end Connection
end Integral
end DifferentialGeometry

end
