import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldFiberEnergy
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameDifferentiatedCurvatureSection
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge

/-!
# Order bounds and the moving-frame divergence datum for the genuine curvature sections

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
single genuinely-irreducible moving-frame curvature-endomorphism producer underneath the
rank-generic order-`2` rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`), stated over the
*concrete* pure-Riemann genuine curvature section `GcurvSection g s S` of
`MovingFrameCurvatureTraceSmooth` (the slot-`0` assembly of the *tensorial* moving-frame trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction) together with a differentiated-curvature genuine
field and a moving-frame remainder field carried **existentially** — never as per-direction
`smoothExtensionTangent`-curried sections (the differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`
is non-tensorial in the direction, so a concrete per-direction packaging is the unsound object; only
the intrinsic sum is order-controlled).

It packages exactly the genuine moving-frame ingredients that the bracket-free-pairing form of the
genuine third-order Weitzenböck field decomposition consumes but cannot derive from below:

* the section split `Curv S = GcurvSection g s S + Gcd + Grem` with the three **order-separated fibre
  bounds** (`rfns(GcurvSection) ≤ Cper²·rfns(∇S)`, `rfns(Gcd) ≤ Cper²·rfns(S)`,
  `rfns(Grem) ≤ Cper²·rfns(∇²S)`), with a single valence-dependent proportional constant `Cper`; and
* the **integrated moving-frame nullity** — the global metric `L²` pairing `⟨Grem, ∇S⟩_{L²} = 0` of
  the moving-frame remainder against `∇S`. (The pointwise pairing is *not* zero — it carries
  `‖∇²S‖² − ‖Δ_∇S‖²` non-divergence content — so only the global `L²` pairing vanishes; the integrated
  form is the exact datum the sole consumer reduces to.)

The bracket-free `L²` pairing `⟨GcurvSection + Gcd, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` is then *not*
posited: it is recovered from this integrated nullity (after identifying
`Curv S − GcurvSection − Gcd = Grem` via the section split) by the purely-algebraic left-additivity
reduction `tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm`) in
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`.

The producer `exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence` is assembled here from
two precise inputs: the sound pure-Riemann genuine-section fibre bound
`GcurvSection_fiberNormSq_le_covGrad` (`rfns(∇S)`-order, *sorry-free* — the pure-Riemann trace is
tensorial), and the intrinsic genuine moving-frame tri-split with integrated nullity
`exists_pointwiseTensorCurv_genuineTriSplit_divergence` (the existential differentiated-curvature and
remainder fields with their bounds, the section split, and the integrated nullity — the irreducible
genuine content). The producer's only remaining work is the type-level combination of the valence
constants into a single `Cper` (via `max`, with the proportional bounds preserved by monotonicity).

The integrated-nullity tri-split `exists_pointwiseTensorCurv_genuineTriSplit_divergence` is the
**single genuinely-irreducible node** of this file and the deepest moving-frame curvature-endomorphism
primitive of the whole tower — it is posited here (`sorry`, discharged by the orchestrator) in its
**sound integrated form**. It supplies the existential differentiated-curvature and remainder fields
with their two fibre bounds, the section split, and the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0`. The
nullity is stated in its *integrated* form deliberately: the pointwise pairing `⟨Grem, ∇S⟩(x)` is *not*
a total covariant divergence — by the pointwise Bochner divergence identity `divergence_dirichletVFGen_eq`
(`TensorConnLapGreenDivergenceIdentityAnySection`) it carries the pointwise-nonzero non-divergence
content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`, so only its *integral* (equal to the integral of a total covariant
divergence over the closed manifold) vanishes. A *pointwise*-divergence form of this node would be
false-as-stated (unprovable without a Poisson solve pinning the remainder), so the integrated nullity
is the honest primitive — and is exactly the datum the sole consumer
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`
(`MovingFrameGenuineFieldPairing`) reduces to via
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Frame-invariant slot-`0` reconstruction of the fibre norm of a `(0, s + 1)`-tensor section.**
For a smooth compactly-supported `(0, s + 1)`-tensor `Tsec`, any base point `x`, and any
`g_x`-orthonormal frame `e` with `n = Module.finrank ℝ (TangentSpace I x)`, the intrinsic fibre norm
squared of the section value reconstructs as the frame-sum over multi-indices `φ : Fin (s + 1) → Fin n`
of the squared model component of its unit-section value:
```
rfns(Tsec.toSection x)
  = ∑_{φ} (toModel (Tsec.toSection x (unit)) (e ∘ φ))².
```
The right-hand model components are exactly the values the slot-`0` fibre-match suite controls (with
`φ = Fin.cons (φ 0) (Fin.tail φ)` and `e ∘ φ = Fin.cons (e (φ 0)) (e ∘ Fin.tail φ)`). The proof
passes through the fibre-norm/inner-product bridge `riemannianFiberNormSq_eq_tensorInnerPointwise`,
the arbitrary-`g_x`-orthonormal-frame diagonal sum `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`
(applied to the `Module.Basis` built from `e`), and the rank-`0` lowering-evaluation identity
`toModel_liftedTensorSection_zero_eq_apply_unit_reindex`. -/
private lemma riemannianFiberNormSq_succ_section_eq_sum_toModel_unit_sq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (Tsec : SmoothCcTensor g 0 (s + 1)) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Tsec.toSection x) =
      ∑ φ : Fin (s + 1) → Fin n,
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              Tsec.toSection x) (unitZeroSec (I := I) (M := M) x))
            (fun k => e (φ k)) ^ 2 := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  -- Build the `Module.Basis` from the `g_x`-orthonormal frame `e` (linearly independent,
  -- cardinality `finrank`).
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hbse_orth : ∀ i j, g.inner x (bse i) (bse j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hbse_eq i, hbse_eq j]; exact horth i j
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x (Tsec.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (Tsec.toSection x)) (TensorRSSpace.toModel (Tsec.toSection x)) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (Tsec.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (Tsec.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + (s + 1))
    bse hbse_orth _ _]
  -- Re-index the diagonal sum from `Fin (0 + (s + 1)) → Fin n` to `Fin (s + 1) → Fin n` and
  -- resolve each lowered model value as the unit-section evaluation.
  have hkey : ∀ ψ : Fin (0 + (s + 1)) → Fin (Module.finrank ℝ (TangentSpace I x)),
      lowerAllUpperIndices (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (Tsec.toSection x)) (fun k => bse (ψ k)) =
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              Tsec.toSection x) (unitZeroSec (I := I) (M := M) x))
            (fun j : Fin (s + 1) => bse (ψ (Fin.natAdd 0 j))) := by
    intro ψ
    have hlift := toModel_liftedTensorSection_zero_eq_apply_unit_reindex (I := I) (M := M) g (s + 1)
      Tsec.toSection x (fun k => bse (ψ k))
    rw [toModel_liftedTensorSection (I := I) (M := M) g 0 (s + 1) Tsec.toSection x] at hlift
    exact hlift
  -- Resolve each diagonal product `lower(·)(bse∘ψ) * lower(·)(bse∘ψ)` as the squared unit-section
  -- evaluation, then re-index the `Fin (0 + (s + 1)) → Fin n` sum onto `Fin (s + 1) → Fin n`.
  have hstep : ∀ ψ : Fin (0 + (s + 1)) → Fin (Module.finrank ℝ (TangentSpace I x)),
      lowerAllUpperIndices (I := I) (M := M) g 0 (s + 1) x
            (TensorRSSpace.toModel (Tsec.toSection x)) (fun k => bse (ψ k)) *
          lowerAllUpperIndices (I := I) (M := M) g 0 (s + 1) x
            (TensorRSSpace.toModel (Tsec.toSection x)) (fun k => bse (ψ k)) =
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              Tsec.toSection x) (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ (Fin.natAdd 0 k))) ^ 2 := by
    intro ψ
    rw [hkey ψ, ← pow_two]
    congr 2
    funext k
    rw [hbse_eq]
  refine Eq.trans (Finset.sum_congr rfl (fun ψ _ => hstep ψ)) ?_
  refine Fintype.sum_bijective
    (fun ψ : Fin (0 + (s + 1)) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
      fun k : Fin (s + 1) => ψ (Fin.natAdd 0 k))
    ?_ _ _ (fun ψ => rfl)
  refine ⟨fun ψ₁ ψ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add (s + 1)) k), ?_⟩⟩
  · funext k
    have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add (s + 1)) k) := by ext; simp
    rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add (s + 1)) k)
  · funext k
    change φ (Fin.cast (Nat.zero_add (s + 1)) (Fin.natAdd 0 k)) = φ k
    have : Fin.cast (Nat.zero_add (s + 1)) (Fin.natAdd 0 k) = k := by ext; simp
    rw [this]

/-- **Pure-`R` genuine-section fibre bound (`rfns(∇S)`-order).** For a closed smooth Riemannian
manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C₁ : ℕ → ℝ` such that, at every
covariant rank `s`, every smooth compactly-supported `(0, s)`-tensor `S` and every `x`,
```
rfns(GcurvSection g s S)(x) ≤ (C₁ s)² · rfns(∇S)(x),   ∇S := covGrad g 0 s S.
```

**Why this is TRUE.** `GcurvSection g s S` is the slot-`0` assembly of the pure-Riemann genuine
moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` (`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`):
its fibre norm reconstructs through the slot-`0` Parseval split
`riemannianFiberNormSq_succ_eq_sum_slot0Curry` as the frame-sum of the `(0, s)` fibre norms of the
pure-Riemann genuine trace, which is the Ricci identity on the gradient field
(`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) — each summand a bundled curvature operator
`riemannOp (tensorCov g 0 (s + 1)) x Bᵢ (∇S(x))`. The base-point-uniform proportional curvature bound
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`, summed over the `g_x`-orthonormal
frame `Bᵢ` (with `g(Bᵢ, Bᵢ) = 1`) and reassembled, yields the single `(C₁ s)² · rfns(∇S)` envelope,
`C₁ s` independent of `x`. This is genuinely tensorial in the gradient slot (the genuine metric trace
contracts the frame index twice), so it is *not* subject to the `smoothExtensionTangent` term-by-term
obstruction.

**Non-vacuity.** A zero envelope `C₁ s = 0` would force `GcurvSection = 0` pointwise, but its fibre
value carries the pure-Riemann contraction `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, genuinely non-zero when `R ≠ 0`
and `∇S ≠ 0` on a non-flat manifold; so the bound genuinely envelopes the per-point curvature operator
norm. -/
private theorem GcurvSection_fiberNormSq_le_covGrad
    (g : SmoothRiemannianMetric I M) :
    ∃ C₁ : ℕ → ℝ, (∀ s, 0 ≤ C₁ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
          C₁ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  obtain ⟨C₁, hC₁_nn, hbound⟩ := genuineThirdCurvFieldFibPureR_fiberNormEnergy_le (I := I) (M := M) g
  refine ⟨C₁, hC₁_nn, fun s S x => ?_⟩
  -- Read the fibre norm of the pure-`R` genuine section in the slot-`0` fibre-match frame `e`, then
  -- bound the frame-summed fibre-field energy by the per-fibre-field energy primitive.
  obtain ⟨n, e, hn, horth, hmatch⟩ :=
    GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x
  rw [riemannianFiberNormSq_succ_section_eq_sum_toModel_unit_sq (I := I) (M := M) g s
    (GcurvSection (I := I) (M := M) g s S) x e hn horth]
  -- Each squared model component is the squared pure-`R` fibre field at `(e (φ 0), e ∘ Fin.tail φ)`.
  have hcomp : ∀ φ : Fin (s + 1) → Fin n,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (GcurvSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (fun k => e (φ k)) ^ 2 =
        genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e (e (φ 0))
            (fun k => e (Fin.tail φ k)) ^ 2 := by
    intro φ
    have hcons : (fun k => e (φ k)) =
        Fin.cons (e (φ 0)) (fun k => e (Fin.tail φ k)) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j; simp [Fin.tail]
    rw [hcons]
    exact congrArg (· ^ 2) (hmatch (e (φ 0)) (fun k => e (Fin.tail φ k)))
  calc ∑ φ : Fin (s + 1) → Fin n,
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                (GcurvSection (I := I) (M := M) g s S).toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (fun k => e (φ k)) ^ 2
        = ∑ φ : Fin (s + 1) → Fin n,
            genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e (e (φ 0))
                (fun k => e (Fin.tail φ k)) ^ 2 := Finset.sum_congr rfl (fun φ _ => hcomp φ)
    _ ≤ C₁ s ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := hbound s S x e hn horth

/-- **Field-level genuine + bracket split of `Curv S` in an arbitrary `g_x`-orthonormal frame.**
The field-level split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` holds not only in
its own witness frame but in *any* `g_x`-orthonormal frame `e` admitting the metric Parseval
expansion `hv_expand`: the unit-section fibre value of `Curv S := pointwiseTensorCurv g s S`
reconstructs as `genuineThirdCurvFieldFib + bracketThirdCurvFieldFib` evaluated in that very frame.
The proof routes the slot-`0` uncurry through the arbitrary-frame reconstruction
`tensor0S_uncurry_cons_eval_orthonormal`, resolves each slot-`0` slice by the unconditional curried
curvature-defect identity `tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction`, and splits
the resulting frame sum by additivity of the model coercion — the same proof as the witness-frame
form, with the frame supplied externally rather than chosen by the slot-`0` reconstruction. -/
private lemma pointwiseTensorCurv_toModel_unit_eq_genuine_add_bracket_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
        bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) e hv_expand w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

set_option linter.unusedSectionVars false in
/-- **A `g_x`-orthonormal frame of full rank gives the metric Parseval expansion.** For a frame `e`
of `n = Module.finrank ℝ (TangentSpace I x)` vectors with `g(eᵢ, eⱼ) = δᵢⱼ`, every tangent vector at
`x` is its inner-product-weighted frame sum. (The same `basisOfLinearIndependentOfCardEqFinrank`
construction as the in-file fibre-norm reconstruction, exposed for the frame-independence argument.) -/
private lemma orthoFrame_parseval_expand_of_orth
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ a : Fin n, g.inner x (e a) u • e a := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin (Module.finrank ℝ (TangentSpace I x)), bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ (TangentSpace I x)),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Frame-independence of the pure-Riemann genuine fibre field.** The pure-Riemann part
`genuineThirdCurvFieldFibPureR g s S x e w m` is independent of the `g_x`-orthonormal frame `e`
(through which it is reconstructed): it equals the unit-section fibre value of the concrete
pure-Riemann section `GcurvSection g s S` at `(w, m)` for *every* such frame. This is the precise
content of the docstrings' "the pure-Riemann trace is tensorial in the direction": each summand
`R(Bᵢ, W a)(∇_{Bᵢ} S)` is *linear* in the curvature direction `W a` and sees only its value
`W a (x) = e a` at `x` (no extension jet), so the inner-product-weighted frame sum is the metric
Parseval reconstruction of `w`, frame-independent. The proof identifies both sides with
`GcurvSection`'s intrinsic fibre value through the moving-frame match
`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` (whose own witness frame is
`smoothOrthoFrame g x`) and the arbitrary-frame uncurry reconstruction. -/
private lemma genuineThirdCurvFieldFibPureR_frame_indep
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (GcurvSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) := by
  classical
  obtain ⟨n₀, e₀, hn₀, horth₀, hmatch₀⟩ :=
    GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x
  have hexp₀ : ∀ u : TangentSpace I x, u = ∑ a : Fin n₀, g.inner x (e₀ a) u • e₀ a :=
    fun u => orthoFrame_parseval_expand_of_orth (I := I) (M := M) g x e₀ hn₀ horth₀ u
  -- The per-direction pure-Riemann trace value at `m` is a *linear* function `Lφ` of the curvature
  -- direction `u`: each summand `R(Bᵢ, smoothExtensionTangent x u)(∇_{Bᵢ}S)(x)` is the bundled
  -- curvature operator `riemannOp` (linear in its middle slot), evaluated at `(smoothExtensionTangent
  -- x u)(x) = u` (`smoothExtensionTangent_eq`). Hence `genuineThirdCurvFieldFibPureR e w m = Lφ(w)`
  -- for *every* `g_x`-orthonormal frame `e` (metric Parseval), frame-independent.
  have hSt := S.toSection.contMDiff
  set Lφ : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) u
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x))
            (unitZeroSec (I := I) (M := M) x)) m
      map_add' := fun u u' => by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hsplit :
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) (u + u')
                (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                  (fun y : M => S.toSection y) x))
              (unitZeroSec (I := I) (M := M) x) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) u
                (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                  (fun y : M => S.toSection y) x))
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) u'
                (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                  (fun y : M => S.toSection y) x))
              (unitZeroSec (I := I) (M := M) x) := by
          rw [(riemannOp (tensorCov (I := I) g 0 s) x
            (smoothOrthoFrame (I := I) g x i x)).map_add u u']
          rfl
        rw [hsplit, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c u => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hsplit :
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) (c • u)
                (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                  (fun y : M => S.toSection y) x))
              (unitZeroSec (I := I) (M := M) x) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) u
                (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                  (fun y : M => S.toSection y) x))
              (unitZeroSec (I := I) (M := M) x) := by
          rw [(riemannOp (tensorCov (I := I) g 0 s) x
            (smoothOrthoFrame (I := I) g x i x)).map_smul c u]
          rfl
        rw [hsplit, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply] } with hLφ_def
  -- Per-direction identity: each `genuineThirdCurvFieldFibPureR` summand value is `Lφ` at that frame
  -- vector, via the bundled-operator form of the pure-Riemann trace.
  have hsummand : ∀ {nₑ : ℕ} (eₑ : Fin nₑ → TangentSpace I x) (a : Fin nₑ),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          genuineCurvTraceFixedFramePureR (I := I) g s
            (smoothExtensionTangent (I := I) x (eₑ a)) (smoothOrthoFrame (I := I) g x)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m = Lφ (eₑ a) := by
    intro nₑ eₑ a
    rw [hLφ_def]
    show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          genuineCurvTraceFixedFramePureR (I := I) g s
            (smoothExtensionTangent (I := I) x (eₑ a)) (smoothOrthoFrame (I := I) g x)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m = _
    rw [genuineCurvTraceFixedFramePureR_smoothOrthoFrame (I := I) g s
      (smoothExtensionTangent (I := I) x (eₑ a)) (fun y : M => S.toSection y) x]
    have hWa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (smoothExtensionTangent (I := I) x (eₑ a))) :=
      smoothExtensionTangent_contMDiff (I := I) x (eₑ a)
    have hop : ∀ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothExtensionTangent (I := I) x (eₑ a))
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x =
          riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x)
            (eₑ a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x) := by
      intro i
      rw [tensor3rdCurv_pure_R_eq_riemannOp (I := I) g 0 s i hWa hSt,
        smoothExtensionTangent_eq x (eₑ a)]
    -- Push the frame sum through the coerce-apply-`toModel` evaluation: the map
    -- `T ↦ toModel ((T : CLM) unit) m` is additive on `TensorRSSpace 0 s` (via the bundled
    -- `toModelL` linear coercion), so it commutes with the `Finset` sum.
    have hpush : ∀ (T : Fin (Module.finrank ℝ E) → TensorRSSpace 0 s I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              ∑ i : Fin (Module.finrank ℝ E), T i)
              (unitZeroSec (I := I) (M := M) x)) m =
          ∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T i)
                (unitZeroSec (I := I) (M := M) x)) m := by
      intro T
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
      | empty => simp
      | insert i fs hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                T i + ∑ j ∈ fs, T j) =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T i) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ j ∈ fs, T j) from rfl]
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
    have hsec : (∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothExtensionTangent (I := I) x (eₑ a))
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x : TensorRSSpace 0 s I x) =
        ∑ i : Fin (Module.finrank ℝ E),
          (riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x)
            (eₑ a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x) : TensorRSSpace 0 s I x) :=
      Finset.sum_congr rfl (fun i _ => hop i)
    rw [hsec]
    rw [hpush (fun i => riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x)
      (eₑ a)
      (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
        (fun y : M => S.toSection y) x))]
    rfl
  -- `genuineThirdCurvFieldFibPureR e w m = ∑_a ⟨e a, w⟩ • Lφ(e a) = Lφ(∑_a ⟨e a, w⟩ • e a) = Lφ(w)`.
  have hcollapse : ∀ {nₑ : ℕ} (eₑ : Fin nₑ → TangentSpace I x)
      (hexpₑ : ∀ u : TangentSpace I x, u = ∑ a : Fin nₑ, g.inner x (eₑ a) u • eₑ a),
      genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x eₑ w m = Lφ w := by
    intro nₑ eₑ hexpₑ
    rw [genuineThirdCurvFieldFibPureR]
    have : ∀ a : Fin nₑ, g.inner x (eₑ a) w •
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            genuineCurvTraceFixedFramePureR (I := I) g s
              (smoothExtensionTangent (I := I) x (eₑ a)) (smoothOrthoFrame (I := I) g x)
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x)) m =
        Lφ (g.inner x (eₑ a) w • eₑ a) := by
      intro a; rw [hsummand eₑ a, Lφ.map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun a _ => this a), ← map_sum, ← hexpₑ w]
  rw [hcollapse e hv_expand]
  rw [hmatch₀ w m, hcollapse e₀ hexp₀]

/-- **Deepest moving-frame curvature primitive: the intrinsic genuine moving-frame tri-split with the
integrated divergence nullity (sum-shaped order bounds).** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant
rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` splits, over the concrete pure-Riemann genuine section
`GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the *tensorial*
pure-Riemann trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, i.e. the `R(∇S)` contraction), into a differentiated-
curvature field `Gcd` and a moving-frame remainder field `Grem`, both smooth compactly-supported
`(0, s + 1)`-tensors carried **existentially** (never extension-curried):
```
Curv S = GcurvSection g s S + Gcd + Grem,
```
with `⟨Grem, ∇S⟩_{L²} = 0` and the two intrinsic **sum** fibre bounds (`∇S := covGrad g 0 s S`,
`∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`)
* `rfns(Gcd)(x) ≤ (K s)² · (rfns(∇S)(x) + rfns(S)(x))` — the differentiated-curvature contraction
  `(∇R) S`, packaged as the gauge-glued tensorial section; the **sum** order (not the strict
  `rfns(S)`) is genuine, absorbing the Leibniz defect between the gauge-glued tensorial section and
  the non-tensorial moving-frame `(∇R) S` trace;
* `rfns(Grem)(x) ≤ (K s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the moving-frame /
  frame-bracket remainder, `rfns(∇²S)`-order in its leading term after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity, with the lower-order
  Leibniz-defect terms `rfns(∇S) + rfns(S)` carried in the sum (they cancel against the `Gcd`
  packaging at the consumer's two-term fibre merge).

This is the **genuinely-irreducible deepest moving-frame curvature-endomorphism primitive** of the
whole tower (the root that `exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence`,
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`
(`MovingFrameGenuineFieldPairing`), `pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder`
(`MovingFrameWeitzenbockRemainder`), and through them the entire genuine-field tower of
`PointwiseTensorCurvL2Bound.lean` are assembled over). The integrated nullity is the **sound integrated
form**: the moving-frame remainder pairs to zero against `∇S` only *under the integral* — its pointwise
pairing carries the genuine non-divergence content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩` (`divergence_dirichletVFGen_eq`),
vanishing only in the integral by the closed-manifold divergence theorem.

**Why this is TRUE — the gauge-glued genuine-field assembly.** The remainder is the literal subtraction
`Grem := Curv S − GcurvSection g s S − Gcd`, so the section split `Curv S = GcurvSection g s S + Gcd +
Grem` is `abel`. The differentiated-curvature field `Gcd` is the gauge-glued tensorial `(∇R) S`
section (the section-level packaging of `covGradCurvatureContraction` frame-traced and
partition-of-unity-glued, `exists_movingCentreDiffCurvSection_fiberNormSq_bound`,
`MovingFrameDifferentiatedCurvatureSection`), carried with its sum fibre bound; this is the
constructible tensorial pinning, *not* the former per-direction extension-curried fibre match (which
was unsatisfiable on a normal manifold — the per-direction `genuineThirdCurvFieldFibCovDeriv` reads the
`smoothExtensionTangent` jet and is frame-dependent). With `Gcd` the tensorial section, the remainder's
unit fibre value is the bracket field `bracketThirdCurvFieldFib` (the committed sorry-free field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` with
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv` and the pure-Riemann frame-independence
`genuineThirdCurvFieldFibPureR_frame_indep`) *plus* the Leibniz defect between the gauge-glued tensorial
`Gcd` and the genuine non-tensorial `(∇R) S` trace; the bracket part is `rfns(∇²S)`-order after the
`∇³S`-cancellation (the iterated Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) and
the Leibniz defect is `rfns(∇S) + rfns(S)`-order — together the sum bound — with all curvature / frame
coefficients sup-bounded over the compact `M` (the uniform curvature sups). The integrated nullity is
the frame-summed covariant integration by parts: the moving-frame remainder, paired against `∇S` and
summed over the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, telescopes into a total
covariant divergence of an honest smooth `∇S`-order tangent field, whose integral over the closed
manifold vanishes (`integral_divergence_eq_zero_of_hasCompactSupport`) — the gauge-glued `Gcd`'s defect
is itself a total covariant divergence against `∇S`, so the integrated pairing is unchanged from the
genuine field. This `∇³S`-cancellation and divergence-form are *false term-by-term* through
`smoothExtensionTangent`; only the tensorial frame-summed remainder is `∇²S`-order and a total
divergence — the irreducible coupled moving-frame content, posited here as one sharp atom (the
coupling of the existential `Gcd`, `Grem`, the split, the nullity and the two sum bounds cannot be
factored into independent standalone lemmas: the nullity is a property of *the specific* `Gcd`, not of
any bounded field, so it is genuinely irreducible as a coupled existential, exactly the shape of the
order-`m` sibling `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`).

**Non-vacuity.** The zero witness `Gcd = Grem = 0` is rejected: it forces `Curv S = GcurvSection g s S`,
so the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0` would read `⟨Curv S, ∇S⟩_{L²} = ⟨GcurvSection, ∇S⟩_{L²}`,
whereas the genuine Weitzenböck value `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`
(`weitzenbock_integrated_covGrad_l2_normSq`) is not carried by the pure-Riemann field alone on a
non-flat manifold; and the `Grem` fibre bound `rfns(Curv S − GcurvSection − Gcd) ≤ (K s)² · (rfns(∇²S)
+ rfns(∇S) + rfns(S))` is *false* with `Gcd = 0`, since the differentiated-curvature contraction
`(∇R) S` is genuinely `rfns(S)`-order and would not be carried. So the existential fields must carry
the actual third-order Weitzenböck content. Consumers transitively depend on `sorryAx`. -/
theorem exists_pointwiseTensorCurv_genuineTriSplit_divergence
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s S =
              GcurvSection (I := I) (M := M) g s S + Gcd + Grem ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Grem.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) := by
  sorry

/-- **Genuine moving-frame producer: order bounds and the divergence datum for the genuine curvature
fields.** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` admits a
differentiated-curvature genuine field `Gcd` and a moving-frame remainder field `Grem` — smooth
compactly-supported `(0, s + 1)`-tensors — over the concrete pure-Riemann genuine section
`GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`), with the section split, the three
order-separated fibre bounds, and the integrated moving-frame nullity:

* `Curv S = GcurvSection g s S + Gcd + Grem` (the genuine third-order Weitzenböck split);
* `rfns(GcurvSection)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order
  (the sorry-free tensorial trace bound);
* `rfns(Gcd)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))` — the `∇R` field, sum-order (the gauge-glued
  tensorial section, the Leibniz defect absorbed into the wider envelope);
* `rfns(Grem)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the moving-frame /
  frame-bracket remainder, `rfns(∇²S)`-order in its leading term with the lower Leibniz-defect terms
  in the sum;
* `⟨Grem, ∇S⟩_{L²} = 0` — the integrated moving-frame nullity (the moving-frame remainder is a total
  covariant divergence of an `∇S`-order field; the pointwise pairing is *not* zero, carrying
  `‖∇²S‖² − ‖Δ_∇S‖²`).

This is **proved** from the intrinsic genuine moving-frame tri-split
`exists_pointwiseTensorCurv_genuineTriSplit_divergence` (which supplies the existential fields `Gcd`,
`Grem` with the section split, the integrated nullity, and the `Gcd` / `Grem` sum fibre bounds)
together with the sound pure-Riemann genuine-section fibre bound `GcurvSection_fiberNormSq_le_covGrad`
(`rfns(∇S)`-order, *sorry-free*); the valence constants are combined into a single `Cper` by `max`,
the bounds preserved by monotonicity. The downstream bracket-free `L²` pairing
`⟨GcurvSection + Gcd, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` is *not* posited: it is recovered from the
integrated nullity (after identifying `Curv S − GcurvSection − Gcd = Grem` via the section split) by
the purely-algebraic left-additivity reduction
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm`) in
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`. -/
theorem exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s S =
              GcurvSection (I := I) (M := M) g s S + Gcd + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Grem.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  obtain ⟨C₁, hC₁_nn, hbound₁⟩ := GcurvSection_fiberNormSq_le_covGrad (I := I) (M := M) g
  obtain ⟨K, hK_nn, htri⟩ := exists_pointwiseTensorCurv_genuineTriSplit_divergence (I := I) (M := M) g
  refine ⟨fun s => max (C₁ s) (K s), fun s => le_trans (hK_nn s) (le_max_right _ _),
    fun s S => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hnull, hGcd, hGrem⟩ := htri s S
  have hC₁_le : C₁ s ≤ max (C₁ s) (K s) := le_max_left _ _
  have hK_le : K s ≤ max (C₁ s) (K s) := le_max_right _ _
  have hsq₁ : C₁ s ^ 2 ≤ (max (C₁ s) (K s)) ^ 2 := pow_le_pow_left₀ (hC₁_nn s) hC₁_le 2
  have hsqK : K s ^ 2 ≤ (max (C₁ s) (K s)) ^ 2 := pow_le_pow_left₀ (hK_nn s) hK_le 2
  refine ⟨Gcd, Grem, hsplit, fun x => ?_, fun x => ?_, fun x => ?_, hnull⟩
  · exact le_trans (hbound₁ s S x)
      (mul_le_mul_of_nonneg_right hsq₁
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _))
  · refine le_trans (hGcd x) (mul_le_mul_of_nonneg_right hsqK ?_)
    exact add_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)
  · refine le_trans (hGrem x) (mul_le_mul_of_nonneg_right hsqK ?_)
    exact add_nonneg (add_nonneg
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _))
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)

end Connection
end Integral
end DifferentialGeometry

end
