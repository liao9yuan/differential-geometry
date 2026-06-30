import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity

/-!
# P1.4 — the pulled-back Ricci-flow solution `Φ^* S`

For a non-endo diffeomorphism `Φ : M ≃ₘ N` and a Ricci-flow solution `S` on `N`, the
fixed-`Φ` pullback `t ↦ Φ^*(S.metric t)` is a Ricci-flow solution on `M`.  The `equation`
field `∂ₜ(Φ^*g) = -2 Ric(Φ^*g)` follows from `S`'s equation by `pullbackMetric_inner`
(metric coeff) + `ricciTensor_pullback` (the `M≃N` Ricci naturality, P1.3).
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

/-- **Pushforward of a `C∞` local frame under a diffeomorphism.**  For `Φ : M ≃ₘ⟮I,I⟯ N` and a
`C∞` local frame `frame` on `u ⊆ M`, the pushed family `y ↦ dΦ_{Φ⁻¹ y}(frame · (Φ⁻¹ y))` is a
`C∞` local frame on `Φ '' u`.  Basis-ness transports through the linear iso
`mfderivToContinuousLinearEquiv`; smoothness is `tangentMap I I Φ ∘ (frame-section ∘ Φ.symm)`. -/
theorem _root_.IsLocalFrameOn.pushforward
    {ι : Type*} {frame : ι → (x : M) → TangentSpace I x} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (Φ : M ≃ₘ⟮I, I⟯ N) :
    IsLocalFrameOn (V := (TangentSpace I : N → Type _)) I E (∞ : WithTop ℕ∞)
      (fun i (y : N) => mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))) (Φ '' u) where
  linearIndependent {y} hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hb : (fun i => mfderiv I I (Φ : M → N) (Φ.symm (Φ x)) (frame i (Φ.symm (Φ x))))
        = ⇑((hframe.toBasisAt hx).map
            (Φ.mfderivToContinuousLinearEquiv infty_ne_zero x).toLinearEquiv) := by
      funext i
      simp only [Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_coe,
        Φ.mfderivToContinuousLinearEquiv_coe, Φ.symm_apply_apply]
    rw [hb]
    exact Module.Basis.linearIndependent _
  generating {y} hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hb : (fun i => mfderiv I I (Φ : M → N) (Φ.symm (Φ x)) (frame i (Φ.symm (Φ x))))
        = ⇑((hframe.toBasisAt hx).map
            (Φ.mfderivToContinuousLinearEquiv infty_ne_zero x).toLinearEquiv) := by
      funext i
      simp only [Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_coe,
        Φ.mfderivToContinuousLinearEquiv_coe, Φ.symm_apply_apply]
    rw [hb]
    exact (Module.Basis.span_eq _).ge
  contMDiffOn i := by
    have hmaps : Set.MapsTo (Φ.symm : N → M) (Φ '' u) u := by
      rintro y ⟨x, hx, rfl⟩; rw [Φ.symm_apply_apply]; exact hx
    have h1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (fun y : N => TotalSpace.mk' E (Φ.symm y) (frame i (Φ.symm y))) (Φ '' u) :=
      (hframe.contMDiffOn i).comp (Φ.symm.contMDiff.contMDiffOn) hmaps
    have h2 := (Φ.contMDiff.contMDiff_tangentMap (by simp)).comp_contMDiffOn h1
    refine h2.congr ?_
    rintro y ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, Φ.symm_apply_apply, tangentMap]

/-- The pulled-back Ricci-flow solution data: `t ↦ Φ^*(S.metric t)`. -/
def solutionOn_pullback [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionOn (I := I) (M := M) D where
  base := { metric := fun t => Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ }

/-- The two fixed-point scalar coefficient functions of the pullback metric
family agree with the original at the pushed-forward point/vectors. -/
private theorem pullback_coeff_eq
    [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (X Y : TangentSpace I x) :
    (fun t : ℝ => ((solutionOn_pullback (I := I) S Φ).family.metric t).inner x X Y)
      = fun t : ℝ => (S.family.metric t).inner (Φ x)
          (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y) := by
  funext t
  exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric t) Φ x X Y

/-- **Smoothness of the pulled-back metric family.**  The scalar coefficient
fields transport by the pointwise rewrite `pullbackMetric_inner` (the point/vectors
are fixed); the bundle joint-continuity/smoothness fields are a `Φ`-pullback of
`hS`'s bundle regularity. -/
theorem metricFamilySmoothOn_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    MetricFamilySmoothOn (I := I) D (solutionOn_pullback (I := I) S Φ).family where
  coeff x X Y := by
    rw [pullback_coeff_eq (I := I) S Φ x X Y]
    exact hS.smoothMetric.coeff (Φ x)
      (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)
  coeff_cont x X Y := by
    rw [pullback_coeff_eq (I := I) S Φ x X Y]
    exact hS.smoothMetric.coeff_cont (Φ x)
      (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)
  metricTensor_cont := by
    apply Tensor0SFamilyContinuousOnSet.congr
      (Tensor0SFamilyContinuousOnSet.pullback (I := I)
        (fun t x => Tensor0SBundle.metricTensorField (I := I) (S.family.metric t) x)
        hS.smoothMetric.metricTensor_cont Φ)
    intro t _ht x
    have hm : (solutionOn_pullback (I := I) S Φ).family.metric t
        = Diffeomorph.pullbackMetric (I := I) (S.family.metric t) Φ := rfl
    ext slots
    rw [hm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Tensor0SBundle.metricTensorField_apply, Tensor0SBundle.metricTensorField_apply,
      Diffeomorph.pullbackMetric_inner]
  frameCompSmooth := by
    intro Idx _ frame u _hframe i j
    have heq : (fun p : ℝ × M =>
          ((solutionOn_pullback (I := I) S Φ).family.metric p.1).inner p.2
            (frame i p.2) (frame j p.2))
        = fun p : ℝ × M => (S.family.metric p.1).inner (Φ p.2)
            (mfderiv I I (Φ : M → N) p.2 (frame i p.2))
            (mfderiv I I (Φ : M → N) p.2 (frame j p.2)) := by
      funext p
      exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric p.1) Φ p.2
        (frame i p.2) (frame j p.2)
    rw [heq]
    -- SMOOTH-TRANSPORT FRONTIER: joint `(t,x)` `ContMDiffOn` of the metric coefficient with the
    -- `dΦ`-pushed frame inputs across `Φ`.  No base-map joint smooth-eval exists (the smooth
    -- `contMDiff_section_apply` is single-manifold/spatial, unlike `eval_continuous`), and there is
    -- no pushforward-`IsLocalFrameOn` under a diffeomorphism to feed `hS.smoothMetric.frameCompSmooth`.
    sorry

/-- **The pulled-back flow satisfies the Ricci-flow metric equation.**
`∂ₜ(Φ^*g) = -2 Ric(Φ^*g)`, from `S`'s equation via `pullbackMetric_inner` and the `M≃N`
Ricci naturality `ricciTensor_pullback`. -/
theorem metricVariationEquation_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    MetricVariationEquationOn (I := I) (solutionOn_pullback (I := I) S Φ) := by
  intro t x X Y
  have hcoeff := pullback_coeff_eq (I := I) S Φ x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (solutionOn_pullback (I := I) S Φ).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := I) S.ricciAt (t : ℝ) (Φ x)
            (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y) := by
    simp only [RicciAtFamily.toTensorField_apply]
    show metricRicciAt (I := I)
          (Diffeomorph.pullbackMetric (I := I) (S.base.metric (t : ℝ)) Φ) x (vec2 X Y)
        = metricRicciAt (I := I) (S.base.metric (t : ℝ)) (Φ x)
            (vec2 (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y))
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact DifferentialGeometry.HCGCompactness.ricciTensor_pullback (I := I)
      (S.base.metric (t : ℝ)) Φ x X Y
  rw [hcoeff, hric]
  exact hS.equation t (Φ x)
    (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)

set_option maxHeartbeats 1000000 in
/-- The pulled-back scalar curvature is the original scalar curvature at `Φ x`
(scalar curvature is an isometry invariant, `metricScalarAt_pullback`). -/
theorem scalar_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (x : M) :
    (solutionOn_pullback (I := I) S Φ).scalar t x = S.scalar t (Φ x) := by
  simp only [SolutionOn.scalar, SolutionFamily.scalar, solutionOn_pullback]
  exact DifferentialGeometry.HCGCompactness.metricScalarAt_pullback (I := I)
    (S.base.metric t) Φ x

/-- **Spacetime continuity of the pulled-back scalar curvature** (the `scalarCont`
field): transport `hS.scalarCont` along `(t,x) ↦ (t, Φ x)` via `scalar_pullback`. -/
theorem scalarCont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    ContinuousOn (fun q : ℝ × M => (solutionOn_pullback (I := I) S Φ).scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)) := by
  have heq : (fun q : ℝ × M => (solutionOn_pullback (I := I) S Φ).scalar q.1 q.2)
      = (fun p : ℝ × N => S.scalar p.1 p.2)
          ∘ (fun q : ℝ × M => ((q.1, Φ q.2) : ℝ × N)) := by
    funext q; exact scalar_pullback (I := I) S Φ q.1 q.2
  rw [heq]
  exact hS.scalarCont.comp
    (continuous_fst.prodMk ((Φ.continuous).comp continuous_snd)).continuousOn
    (fun q hq => ⟨hq.1, Set.mem_univ _⟩)

/-- **Within-time differentiability of the pulled-back scalar curvature** (the
`scalarTime` field): for fixed `x` only the time varies, so it transports from
`hS.scalarTime` at `Φ x` via `scalar_pullback`. -/
theorem scalarTime_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) {K : Set ℝ} {t : ℝ} (htK : t ∈ K) (hKsub : K ⊆ D.carrier)
    (x : M) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => (solutionOn_pullback (I := I) S Φ).scalar s x) K t := by
  have heq : (fun s : ℝ => (solutionOn_pullback (I := I) S Φ).scalar s x)
      = fun s : ℝ => S.scalar s (Φ x) := by
    funext s; exact scalar_pullback (I := I) S Φ s x
  rw [heq]
  exact hS.scalarTime htK hKsub (Φ x)

/-- The bundled Ricci `(0,2)` section transports under pullback (evaluated form):
`metricRicci (Φ^*g) x slots = metricRicci g (Φ x) (dΦ ∘ slots)`.  Mirrors `ricciSection_pullback`
via `metricRicci_apply` (→ `metricRicciAt`) + `metricRicciAt_apply_eq_ricciTensor` + `ricciTensor_pullback`. -/
theorem metricRicci_pullback_eval
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M)
    (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x slots
      = metricRicci (I := I) g (Φ x)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) x (slots q)) := by
  have hLHS : metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x
        (vec2 (slots 0) (slots 1))
      = ricciTensor (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x (slots 0) (slots 1) := by
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  have hRHS : metricRicci (I := I) g (Φ x)
        (vec2 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1)))
      = ricciTensor (I := I) g (Φ x)
          (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1)) := by
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  have hpb := DifferentialGeometry.HCGCompactness.ricciTensor_pullback (I := I) g Φ x
    (slots 0) (slots 1)
  rw [show vec2 (slots 0) (slots 1) = slots from by funext i; fin_cases i <;> rfl] at hLHS
  rw [show vec2 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
        = (fun q : Fin 2 => mfderiv I I (Φ : M → N) x (slots q)) from by
      funext i; fin_cases i <;> rfl] at hRHS
  rw [hLHS, hpb, ← hRHS]

set_option maxHeartbeats 1000000 in
/-- The pulled-back Ricci norm `|Ric|²` equals the original at `Φ x` (`|Ric|²` is an
isometry invariant): `ricciNorm (Φ^*S) t x = ricciNorm S t (Φ x)`.  Via
`normSq0S_pullback_eval_of_orthonormal` with the bundled-Ricci pullback `metricRicci_pullback_eval`. -/
theorem ricciNorm_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (x : M) :
    ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t x = ricciNorm (I := I) S t (Φ x) := by
  obtain ⟨B, hB⟩ :=
    exists_gOrthonormalBasis (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x
  show Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x 2
        (metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x)
      = Tensor0SBundle.normSq0S (I := I) (S.base.metric t) (Φ x) 2
          (metricRicci (I := I) (S.base.metric t) (Φ x))
  exact DifferentialGeometry.HCGCompactness.normSq0S_pullback_eval_of_orthonormal (I := I)
    (g := S.base.metric t) Φ x 2 B hB
    (metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x)
    (metricRicci (I := I) (S.base.metric t) (Φ x))
    (fun slots => metricRicci_pullback_eval (I := I) (S.base.metric t) Φ x slots)

/-- **Fixed-time spatial differentiability of the pulled-back Ricci norm** (the
`ricciNormSpace` field): `ricciNorm (Φ^*S) t = ricciNorm S t ∘ Φ` (`ricciNorm_pullback`),
then the chain rule. -/
theorem ricciNormSpace_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (ht : t ∈ D.carrier) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t) x := by
  have heq : ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t
      = (ricciNorm (I := I) S t) ∘ (Φ : M → N) := by
    funext y; exact ricciNorm_pullback (I := I) S Φ t y
  rw [heq]
  exact (hS.ricciNormSpace t ht (Φ x)).comp x
    (Φ.contMDiff.mdifferentiableAt (by simp))

/-- **Total-space continuity of the pulled-back Ricci tensor family** (the `ricciCont`
field): transport `hS.ricciCont` by `Tensor0SFamilyContinuousOnSet.pullback`, then identify the
pullback section with `(solutionOn_pullback S Φ).ricci` via `metricRicci_pullback_eval`. -/
theorem ricciCont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (solutionOn_pullback (I := I) S Φ).ricci t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.pullback (I := I)
      (fun t x => S.ricci t x) hS.ricciCont Φ)
  intro t _ht x
  ext slots
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact (metricRicci_pullback_eval (I := I) (S.base.metric t) Φ x slots).symm

/-- The bundled lowered Riemann `(0,4)` section transports under pullback (evaluated form):
`metricRm04 (Φ^*g) x slots = metricRm04 g (Φ x) (dΦ ∘ slots)`.  The `(0,4)` analog of
`metricRicci_pullback_eval`: `metricRm04_apply`/`metricRm04StdAt_apply` bridge to `metricRm04StdAt`
on `vec4` slots, then `metricRm04Std_pullback`. -/
theorem metricRm04_pullback_eval
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M)
    (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x slots
      = metricRm04 (I := I) g (Φ x)
          (fun q : Fin 4 => mfderiv I I (Φ : M → N) x (slots q)) := by
  have hLHS : metricRm04 (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x
        (vec4 (slots 0) (slots 1) (slots 2) (slots 3))
      = metricRm04StdAt (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    rw [metricRm04_apply, metricRm04StdAt_apply]
  have hRHS : metricRm04 (I := I) g (Φ x)
        (vec4 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
          (mfderiv I I (Φ : M → N) x (slots 2)) (mfderiv I I (Φ : M → N) x (slots 3)))
      = metricRm04StdAt (I := I) g (Φ x)
          (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
          (mfderiv I I (Φ : M → N) x (slots 2)) (mfderiv I I (Φ : M → N) x (slots 3)) := by
    rw [metricRm04_apply, metricRm04StdAt_apply]
  have hpb := metricRm04Std_pullback (I := I) g Φ x (slots 0) (slots 1) (slots 2) (slots 3)
  rw [show vec4 (slots 0) (slots 1) (slots 2) (slots 3) = slots from by
      funext i; fin_cases i <;> rfl] at hLHS
  rw [show vec4 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
          (mfderiv I I (Φ : M → N) x (slots 2)) (mfderiv I I (Φ : M → N) x (slots 3))
        = (fun q : Fin 4 => mfderiv I I (Φ : M → N) x (slots q)) from by
      funext i; fin_cases i <;> rfl] at hRHS
  rw [hLHS, hpb, ← hRHS]

/-- **Total-space continuity of the pulled-back lowered Riemann tensor family** (the `rm04Cont`
field): transport `hS.rm04Cont` by `Tensor0SFamilyContinuousOnSet.pullback`, then identify with
`(solutionOn_pullback S Φ).base.rm04` via `metricRm04_pullback_eval`. -/
theorem rm04Cont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => (solutionOn_pullback (I := I) S Φ).base.rm04 t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.pullback (I := I)
      (fun t x => S.base.rm04 t x) hS.rm04Cont Φ)
  intro t _ht x
  ext slots
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact (metricRm04_pullback_eval (I := I) (S.base.metric t) Φ x slots).symm

/-- **Smoothness of the pulled-back connection family** (the `smoothConnection` field).  No
transport from `S` is needed: the family connection is the Levi-Civita connection of `Φ^*g_t`,
whose smoothness is the general `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative`. -/
theorem smoothConnection_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) :
    ConnectionFamilySmoothOn (I := I) (solutionOn_pullback (I := I) S Φ).family := by
  intro t
  exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
    ((solutionOn_pullback (I := I) S Φ).base.metric (t : ℝ))

end RicciFlow
end PDE
end DifferentialGeometry

end
