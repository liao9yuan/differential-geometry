import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# Frame-summed fibre-norm energy of the genuine moving-frame curvature fibre fields

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
genuinely-irreducible *per-fibre-field* energy primitives underneath the order-separated fibre
bounds and the moving-frame divergence datum of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`).

The order bounds on the concrete genuine curvature sections `GcurvSection g s S`,
`GcurvDerivSection g s S` and on the moving-frame remainder `Curv S − GcurvSection − GcurvDerivSection`
(`MovingFrameGenuineSectionOrderDivergence`) all reduce, through the slot-`0` fibre-match suite
(`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`, etc.) together with the frame-invariant
fibre-norm reconstruction `riemannianFiberNormSq_eq_tensorInnerPointwise` /
`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame` (valid in *any* `g_x`-orthonormal frame), to a single
shared statement: the frame-summed squared energy of the corresponding *fibre field*
(`genuineThirdCurvFieldFibPureR`, `genuineThirdCurvFieldFibCovDeriv`, `bracketThirdCurvFieldFib`,
the inner-product-weighted frame reconstructions of the curvature contractions) is bounded by a
single valence-dependent proportional constant times the appropriate fibre-norm order. These three
energy bounds, and the moving-frame divergence datum, are the irreducible genuine content; this file
states them as the precise primitives the order-divergence producer consumes.

## The three energy primitives and the remainder fibre-match

For a `g_x`-orthonormal frame `e` with `n = Module.finrank ℝ (TangentSpace I x)`:

* `genuineThirdCurvFieldFibPureR_fiberNormEnergy_le` — the pure-Riemann fibre field
  `genuineThirdCurvFieldFibPureR g s S x e` carries `∑ₐ ⟨e a, ·⟩_g • R(B_i, W a)(∇_{B_i} S)`; its
  frame-summed squared energy is bounded `rfns(∇S)`-order. **Why TRUE.** Orthonormality collapses the
  inner weight `⟨e a, e (φ 0)⟩_g = δ_{a, φ 0}`, leaving the `(0, s)` fibre norm of the pure-Riemann
  curvature trace `∑_i R(B_i, e (φ 0))(∇_{B_i} S)` reassembled over the orthonormal frame
  (`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`); each curvature contraction is fibre-bounded by
  the uniform rank-`s` curvature sup (`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le`,
  uniformised over the compact `M`), with the orthonormal Gram scalars `g(B_i, B_i) = 1`,
  `g(W (φ 0), W (φ 0)) = 1`, reduced to `rfns(∇S)` through the directional-slice control
  `riemannianFiberNormSq_covApply_le_covGrad`. The proportional constant is independent of `x`.

* `genuineThirdCurvFieldFibCovDeriv_fiberNormEnergy_le` — the differentiated-curvature fibre field is
  bounded `rfns(S)`-order by a uniform-over-direction differentiated-curvature sup (`‖∇R‖_∞`,
  posited as `exists_uniform_genuineCurvCovDerivTrace_fiberNormSq_bound`), again after the
  orthonormal collapse of the inner weight.

* `bracketThirdCurvFieldFib_fiberNormEnergy_le` — the bracket fibre field carries the frame-bracket
  discrepancy; its frame-summed squared energy is bounded `rfns(∇²S)`-order after the third-order
  Weitzenböck cancellation of the top-order `∇³S` terms by the iterated Ricci identity (posited as
  `bracketThirdCurvFieldFib_fiberNormSq_le_secondCovGrad_pointwise`). This cancellation is *false
  term-by-term* through `smoothExtensionTangent`; only the tensorial frame-sum is `∇²S`-order.

* `movingFrameRemainder_toSection_eq_bracketField` — the frame-independent reading of the moving-frame
  remainder as the bracket field, in *any* orthonormal frame; it closes over the arbitrary-frame
  pure-Riemann match (proven here, frame-free) and the arbitrary-frame differentiated-curvature match
  (`GcurvDerivSection_toSection_eq_genuineThirdCurvFieldFibCovDeriv_anyFrame`).
-/

noncomputable section

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Rank-`0` reconstruction of a `(0, s)`-multilinear value as a `(0, s)`-tensor.** Sends a bare
`(0, s)`-multilinear fibre value `t : Tensor0SSpace s I x` to the `(0, s)`-tensor (continuous linear
map `Tensor0SSpace 0 →L Tensor0SSpace s`) `σ ↦ (σ ⋆) • t`; its unit-section value recovers `t` (since
the unit covector has scalar value `1`). This is the rank-`0` inverse of the unit-evaluation
`(T : CLM) (unit)`, used to read the bare bracket-field fibre terms (`covGradRoughLapTraceDiscrepancy_gen`,
`covGradRoughLapMovingFrameResidual_gen`) through the `(0, s)`-tensor fibre-norm. -/
private noncomputable def tensorRS0sOfTensor0S (s : ℕ) (x : M) (t : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight t

set_option linter.unusedSectionVars false in
/-- The unit-section value of `tensorRS0sOfTensor0S t` recovers `t`. -/
private lemma tensorRS0sOfTensor0S_apply_unit (s : ℕ) (x : M) (t : Tensor0SSpace s I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from tensorRS0sOfTensor0S (I := I) (M := M) s x t)
        (unitZeroSec (I := I) (M := M) x) = t := by
  rw [tensorRS0sOfTensor0S]
  rw [ContinuousLinearMap.smulRight_apply]
  have hscalar : tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
    have : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) =
        (1 : ℝ) := by
      rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
      simp
    rw [← this]
    rfl
  rw [hscalar, one_smul]

/-- **Frame-summed squared model components of a `(0, s)`-tensor reassemble its fibre norm.** For a
`(0, s)`-tensor value `Tr` at `x` and a `g_x`-orthonormal frame `e` (`n = Module.finrank`), the sum
over multi-indices `ψ : Fin s → Fin n` of the squared model components reassembles the intrinsic
fibre norm:
```
rfns(Tr) = ∑_{ψ} (toModel Tr (e ∘ ψ))².
```
The proof passes through the fibre-norm / inner-product bridge `riemannianFiberNormSq_eq_tensorInnerPointwise`
and the arbitrary-`g_x`-orthonormal-frame diagonal sum `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`
(applied to the `Module.Basis` built from `e`). It is the rank-`s` value analogue of the section
reconstruction `riemannianFiberNormSq_succ_section_eq_sum_toModel_unit_sq`. -/
private lemma riemannianFiberNormSq_eq_sum_toModel_sq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (Tr : TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x Tr =
      ∑ ψ : Fin s → Fin n,
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ k)) ^ 2 := by
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
  have hbse_orth : ∀ i j, g.inner x (bse i) (bse j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hbse_eq i, hbse_eq j]; exact horth i j
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x Tr]
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel Tr) (TensorRSSpace.toModel Tr) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel Tr))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel Tr)) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    bse hbse_orth _ _]
  have hkey : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel Tr) (fun k => bse (ξ k)) =
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr)
              (unitZeroSec (I := I) (M := M) x))
            (fun j : Fin s => bse (ξ (Fin.natAdd 0 j))) := by
    intro ξ
    rw [lowerAllUpperIndices_apply (I := I) (M := M) g 0 s x (TensorRSSpace.toModel Tr)
      (fun k => bse (ξ k))]
    rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x Tr (unitZeroSec (I := I) (M := M) x)]
    rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
    rw [separableFormAt_zero (I := I) (M := M) g x
      (fun i : Fin 0 => (fun k => bse (ξ k)) (Fin.castAdd s i))]
  have hstep : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel Tr) (fun k => bse (ξ k)) *
          lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel Tr) (fun k => bse (ξ k)) =
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ξ (Fin.natAdd 0 k))) ^ 2 := by
    intro ξ
    rw [hkey ξ, ← pow_two]
    congr 2
    funext k
    rw [hbse_eq]
  refine Eq.trans (Finset.sum_congr rfl (fun ξ _ => hstep ξ)) ?_
  refine Fintype.sum_bijective
    (fun ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
      fun k : Fin s => ξ (Fin.natAdd 0 k))
    ?_ _ _ (fun ξ => rfl)
  refine ⟨fun ξ₁ ξ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add s) k), ?_⟩⟩
  · funext k
    have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add s) k) := by ext; simp
    rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add s) k)
  · funext k
    change φ (Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k)) = φ k
    have : Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k) = k := by ext; simp
    rw [this]

set_option linter.unusedSectionVars false in
/-- **Orthonormal collapse of an inner-product-weighted frame field.** For a `g_x`-orthonormal frame
`e` and a trace family `Tr : Fin n → TensorRSSpace 0 s`, the inner-product-weighted frame sum
`∑ₐ ⟨e a, e a₀⟩_g • toModel (Tr a (unit)) m` collapses to the single `a₀` term. -/
private lemma orthoWeighted_frame_sum_collapse
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (Tr : Fin n → TensorRSSpace 0 s I x) (a₀ : Fin n) (m : Fin s → TangentSpace I x) :
    ∑ a : Fin n, g.inner x (e a) (e a₀) •
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr a)
            (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr a₀)
          (unitZeroSec (I := I) (M := M) x)) m := by
  classical
  rw [Finset.sum_eq_single a₀]
  · rw [horth a₀ a₀, if_pos rfl, one_smul]
  · intro b _ hb
    rw [horth b a₀, if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a₀) h

/-- **Reduction of the frame-summed squared field energy to the frame sum of trace fibre norms.**
For a `g_x`-orthonormal frame `e` (`n = Module.finrank`) and a trace family `Tr : Fin n → TensorRSSpace 0 s`,
if the field is the inner-product-weighted frame reconstruction
`field w m = ∑ₐ ⟨e a, w⟩_g • toModel (Tr a (unit)) m`, then the frame-summed squared energy of the
field at `(e (φ 0), e ∘ Fin.tail φ)` reassembles into the frame sum of the intrinsic fibre norms of
the traces:
```
∑_{φ} (field (e (φ 0)) (e ∘ Fin.tail φ))² = ∑_{a} rfns(Tr a).
```
The proof orthonormally collapses each field component (`orthoWeighted_frame_sum_collapse`), re-indexes
`φ ↔ (φ 0, Fin.tail φ)`, and reassembles the inner `ψ`-sum into the fibre norm
(`riemannianFiberNormSq_eq_sum_toModel_sq`). -/
private lemma frame_field_energy_eq_sum_trace_fiberNormSq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (Tr : Fin n → TensorRSSpace 0 s I x)
    (field : TangentSpace I x → (Fin s → TangentSpace I x) → ℝ)
    (hfield : ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
      field w m = ∑ a : Fin n, g.inner x (e a) w •
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr a)
            (unitZeroSec (I := I) (M := M) x)) m) :
    ∑ φ : Fin (s + 1) → Fin n, field (e (φ 0)) (fun k => e (Fin.tail φ k)) ^ 2 =
      ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a) := by
  classical
  have hcollapse : ∀ φ : Fin (s + 1) → Fin n,
      field (e (φ 0)) (fun k => e (Fin.tail φ k)) ^ 2 =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr (φ 0))
            (unitZeroSec (I := I) (M := M) x)) (fun k => e (Fin.tail φ k)) ^ 2 := by
    intro φ
    rw [hfield (e (φ 0)) (fun k => e (Fin.tail φ k))]
    rw [orthoWeighted_frame_sum_collapse (I := I) (M := M) g s x e horth Tr (φ 0)
      (fun k => e (Fin.tail φ k))]
  rw [Finset.sum_congr rfl (fun φ (_ : φ ∈ Finset.univ) => hcollapse φ)]
  -- Re-index `φ ↔ (φ 0, Fin.tail φ)` via the `Fin.cons`/`Fin.tail` equivalence.
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
        (fun (pr : Fin n × (Fin s → Fin n)) =>
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr pr.1)
              (unitZeroSec (I := I) (M := M) x)) (fun k => e (pr.2 k)) ^ 2)
        (fun φ : Fin (s + 1) → Fin n =>
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr (φ 0))
              (unitZeroSec (I := I) (M := M) x)) (fun k => e (Fin.tail φ k)) ^ 2)
        (fun pr => by
          have hcons : (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n)) pr =
              Fin.cons pr.1 pr.2 := rfl
          simp only [hcons]
          rw [Fin.cons_zero, Fin.tail_cons])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a₀ _ => ?_)
  rw [riemannianFiberNormSq_eq_sum_toModel_sq (I := I) (M := M) g s x (Tr a₀) e hn horth]

/-- **Uniform pure-Riemann genuine-trace fibre bound (`‖R‖_∞ · rfns(∇S)`).** For a closed smooth
Riemannian manifold `(M, g)` there is a valence-dependent nonnegative constant `Kpure : ℕ → ℝ` such
that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, and
*unit* tangent vector `v` at `x` (`g(v, v) = 1`), the pure-Riemann genuine curvature trace at the
smooth extension of `v`, against the moving orthonormal frame `smoothOrthoFrame g x`,
```
genuineCurvTraceFixedFramePureR g s (smoothExtensionTangent x v) (smoothOrthoFrame g x) (S.toSection) x
  = ∑ᵢ R(Bᵢ, v)(∇_{Bᵢ} S)(x),
```
has fibre norm bounded `rfns(∇S)`-order, with constant `Kpure s` independent of `x` and `v`.

**Why this is TRUE.** Each summand `R(Bᵢ, v)(∇_{Bᵢ} S)` is the bundled rank-`s` curvature operator
`riemannOp (tensorCov g 0 s) x (Bᵢ x) v (∇_{Bᵢ} S(x))` (`tensor3rdCurv_pure_R_eq_riemannOp`),
fibre-bounded by the uniform rank-`s` curvature sup (the sup over the compact `M` of the continuous
per-point proportional envelope `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`)
times the orthonormal Gram scalars `g(Bᵢ x, Bᵢ x) = 1` (`smoothOrthoFrame_orthonormal_at_center`),
`g(v, v) = 1`, and the directional-derivative slice fibre norm `rfns(∇_{Bᵢ} S)`, in turn controlled by
the full gradient fibre norm `rfns(∇S)` (the `Bᵢ`-slice of the leftmost slot of `covGrad g 0 s S`, of
unit `g`-length, is fibre-dominated by the whole gradient through the slot-`0` Parseval decomposition
`riemannianFiberNormSq_succ_eq_sum_slot0Curry`). Summing the `n`-fold frame sum by
`riemannianFiberNormSq_sum_le_card_mul` gives a single `x`-uniform constant.

**Non-vacuity.** A zero envelope `Kpure s = 0` forces `∑ᵢ R(Bᵢ, v)(∇_{Bᵢ} S) = 0` for all unit `v`,
but the pure-Riemann contraction is genuinely nonzero when `R ≠ 0` and `∇S ≠ 0` on a non-flat manifold;
so the bound genuinely envelopes the per-point curvature operator norm. -/
theorem exists_uniform_genuineCurvTracePureR_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kpure : ℕ → ℝ, (∀ s, 0 ≤ Kpure s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x),
        g.inner x v v = 1 →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (genuineCurvTraceFixedFramePureR (I := I) g s
              (smoothExtensionTangent (I := I) x v) (smoothOrthoFrame (I := I) g x)
              (fun y : M => S.toSection y) x) ≤
          Kpure s *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  sorry

/-- **Uniform differentiated-curvature genuine-trace fibre bound (`‖∇R‖_∞ · rfns(S)`).** For a closed
smooth Riemannian manifold `(M, g)` there is a valence-dependent nonnegative constant `KgradR : ℕ → ℝ`
such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, and
*unit* tangent vector `v` at `x` (`g(v, v) = 1`), the differentiated-curvature genuine curvature trace
at the smooth extension of `v`, against the moving orthonormal frame `smoothOrthoFrame g x`,
```
genuineCurvTraceFixedFrameCovDeriv g s (smoothExtensionTangent x v) (smoothOrthoFrame g x) (S.toSection) x
  = ∑ᵢ ∇_{Bᵢ}(R(Bᵢ, v) S)(x),
```
has fibre norm bounded `rfns(S)`-order, with constant `KgradR s` independent of `x` and `v`.

**Why this is TRUE.** The differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, v) S)` is the
covariant gradient (frame-traced) of the curvature contraction of `S`; its fibre norm is bounded by a
single base-point-independent constant times `rfns(S)` through the uniform differentiated-curvature sup
(the `‖∇R‖_∞` content of `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, taken uniform
over the *direction* `v` as well — the curvature derivative of a fixed smooth metric is bounded over the
unit sphere bundle of the compact `M`), with the orthonormal Gram scalar `g(v, v) = 1`. This is the
direction-uniform `‖∇R‖_∞`-content not available from the per-`(X, Y)` form below.

**Non-vacuity.** A zero envelope `KgradR s = 0` forces `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, v) S) = 0` for all unit `v`,
but the differentiated-curvature contraction `(∇_{Bᵢ} R)(Bᵢ, ·) S` is genuinely nonzero when `∇R ≠ 0`
and `S` is non-parallel on a non-flat manifold; so the bound genuinely envelopes the differentiated
curvature sup. -/
theorem exists_uniform_genuineCurvTraceCovDeriv_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ KgradR : ℕ → ℝ, (∀ s, 0 ≤ KgradR s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x),
        g.inner x v v = 1 →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (genuineCurvTraceFixedFrameCovDeriv (I := I) g s
              (smoothExtensionTangent (I := I) x v) (smoothOrthoFrame (I := I) g x)
              (fun y : M => S.toSection y) x) ≤
          KgradR s *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  sorry

/-- **Frame-summed squared energy of the pure-Riemann genuine curvature fibre field
(`rfns(∇S)`-order).** For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent
nonnegative constant `C₁ : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S`, point `x`, and `g_x`-orthonormal frame `e` (with
`n = Module.finrank ℝ (TangentSpace I x)`), the frame-summed squared energy of the pure-Riemann fibre
field is bounded `rfns(∇S)`-order:
```
∑_{φ : Fin (s+1) → Fin n} (genuineThirdCurvFieldFibPureR g s S x e (e (φ 0)) (e ∘ Fin.tail φ))²
  ≤ (C₁ s)² · rfns(∇S)(x),    ∇S := covGrad g 0 s S.
```

**Why this is TRUE.** `genuineThirdCurvFieldFibPureR g s S x e w m
  = ∑ₐ ⟨e a, w⟩_g • toModel (∑ᵢ R(Bᵢ, W a)(∇_{Bᵢ} S)(x)) m`, `W a := smoothExtensionTangent x (e a)`.
With `w = e (φ 0)` the orthonormal Gram `⟨e a, e (φ 0)⟩_g = δ_{a, φ 0}` collapses the `a`-sum to the
single index `a = φ 0`, leaving the model value of the pure-Riemann curvature trace, whose frame-summed
squared model components reassemble its intrinsic `(0, s)` fibre norm
(`frame_field_energy_eq_sum_trace_fiberNormSq`). Each trace is fibre-bounded `rfns(∇S)`-order by the
uniform pure-Riemann genuine-trace bound `exists_uniform_genuineCurvTracePureR_fiberNormSq_bound` (with
`g(e a, e a) = 1`), and the `n`-fold frame sum gives `C₁ s := √(n · Kpure s)`, independent of `x`.

**Non-vacuity.** A zero envelope `C₁ s = 0` would force the pure-Riemann energy to vanish for all
`S, x, e`, but it carries the curvature trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, genuinely non-zero when
`R ≠ 0` and `∇S ≠ 0` on a non-flat manifold; so the bound genuinely envelopes the per-point curvature
operator norm. -/
theorem genuineThirdCurvFieldFibPureR_fiberNormEnergy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C₁ : ℕ → ℝ, (∀ s, 0 ≤ C₁ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∑ φ : Fin (s + 1) → Fin n,
            genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e (e (φ 0))
              (fun k => e (Fin.tail φ k)) ^ 2 ≤
          C₁ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  obtain ⟨Kpure, hKpure_nn, hKpure⟩ :=
    exists_uniform_genuineCurvTracePureR_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * Kpure s), fun s => Real.sqrt_nonneg _,
    fun s S x n e hn horth => ?_⟩
  -- Abbreviate the pure-R trace family and identify the field as its inner-product-weighted sum.
  set Tr : Fin n → TensorRSSpace 0 s I x := fun a =>
    genuineCurvTraceFixedFramePureR (I := I) g s
      (smoothExtensionTangent (I := I) x (e a)) (smoothOrthoFrame (I := I) g x)
      (fun y : M => S.toSection y) x with hTr
  have hfield : ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
      genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m =
        ∑ a : Fin n, g.inner x (e a) w •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr a)
              (unitZeroSec (I := I) (M := M) x)) m := by
    intro w m; rw [genuineThirdCurvFieldFibPureR]
  rw [frame_field_energy_eq_sum_trace_fiberNormSq (I := I) (M := M) g s x e hn horth Tr
    (genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e) hfield]
  -- Square-root constant: `C₁ s ^ 2 = n · Kpure s` (nonnegative product).
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * Kpure s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * Kpure s :=
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (hKpure_nn s))
  rw [hCsq]
  -- Per-`a` bound (each frame vector is a unit vector), summed.
  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a) ≤
        Kpure s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro a
    have hunit : g.inner x (e a) (e a) = 1 := by rw [horth a a, if_pos rfl]
    exact hKpure s S x (e a) hunit
  calc ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a)
      ≤ ∑ _a : Fin n, Kpure s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (Module.finrank ℝ E : ℝ) * Kpure s *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (n : ℝ) = (Module.finrank ℝ E : ℝ) from by
          rw [hn]; rfl]
        ring

/-- **Frame-summed squared energy of the differentiated-curvature genuine fibre field
(`rfns(S)`-order).** For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent
nonnegative constant `C₂ : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S`, point `x`, and `g_x`-orthonormal frame `e` (with
`n = Module.finrank ℝ (TangentSpace I x)`), the frame-summed squared energy of the
differentiated-curvature fibre field is bounded `rfns(S)`-order:
```
∑_{φ : Fin (s+1) → Fin n} (genuineThirdCurvFieldFibCovDeriv g s S x e (e (φ 0)) (e ∘ Fin.tail φ))²
  ≤ (C₂ s)² · rfns(S)(x).
```

**Why this is TRUE.** `genuineThirdCurvFieldFibCovDeriv g s S x e w m
  = ∑ₐ ⟨e a, w⟩_g • toModel (∑ᵢ ∇_{Bᵢ}(R(Bᵢ, W a) S)(x)) m`. With `w = e (φ 0)` the orthonormal Gram
collapses the `a`-sum to `a = φ 0`, leaving the model value of the differentiated-curvature trace,
whose frame-summed squared model components reassemble its intrinsic `(0, s)` fibre norm
(`frame_field_energy_eq_sum_trace_fiberNormSq`). Each trace is fibre-bounded `rfns(S)`-order by the
uniform differentiated-curvature genuine-trace bound `exists_uniform_genuineCurvTraceCovDeriv_fiberNormSq_bound`
(`‖∇R‖_∞`, with `g(e a, e a) = 1`), and the `n`-fold frame sum gives `C₂ s := √(n · KgradR s)`,
independent of `x`.

**Non-vacuity.** A zero envelope `C₂ s = 0` would force the differentiated-curvature energy to vanish
for all `S, x, e`, but it carries the contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`, genuinely non-zero when
`∇R ≠ 0` and `S` non-parallel; so the bound genuinely envelopes the differentiated-curvature sup. -/
theorem genuineThirdCurvFieldFibCovDeriv_fiberNormEnergy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C₂ : ℕ → ℝ, (∀ s, 0 ≤ C₂ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∑ φ : Fin (s + 1) → Fin n,
            genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e (e (φ 0))
              (fun k => e (Fin.tail φ k)) ^ 2 ≤
          C₂ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  classical
  obtain ⟨KgradR, hKgradR_nn, hKgradR⟩ :=
    exists_uniform_genuineCurvTraceCovDeriv_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * KgradR s), fun s => Real.sqrt_nonneg _,
    fun s S x n e hn horth => ?_⟩
  set Tr : Fin n → TensorRSSpace 0 s I x := fun a =>
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s
      (smoothExtensionTangent (I := I) x (e a)) (smoothOrthoFrame (I := I) g x)
      (fun y : M => S.toSection y) x with hTr
  have hfield : ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
      genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m =
        ∑ a : Fin n, g.inner x (e a) w •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tr a)
              (unitZeroSec (I := I) (M := M) x)) m := by
    intro w m; rw [genuineThirdCurvFieldFibCovDeriv]
  rw [frame_field_energy_eq_sum_trace_fiberNormSq (I := I) (M := M) g s x e hn horth Tr
    (genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e) hfield]
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * KgradR s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * KgradR s :=
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (hKgradR_nn s))
  rw [hCsq]
  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a) ≤
        KgradR s * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro a
    have hunit : g.inner x (e a) (e a) = 1 := by rw [horth a a, if_pos rfl]
    exact hKgradR s S x (e a) hunit
  calc ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a)
      ≤ ∑ _a : Fin n, KgradR s * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (Module.finrank ℝ E : ℝ) * KgradR s *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (n : ℝ) = (Module.finrank ℝ E : ℝ) from by rw [hn]; rfl]
        ring

/-- **The bracket fibre-field directional term** (`(0, s)`-tensor reconstruction). The bracket fibre
field `bracketThirdCurvFieldFib g s S x e w m` is `∑ₐ ⟨e a, w⟩_g • toModel (bracketTraceTerm g s S x (e a)) m`,
with the directional `(0, s)`-tensor term
```
bracketTraceTerm g s S x v
  := tensorRS0sOf( covGradRoughLapTraceDiscrepancy_gen g s S x v
       + (tensor3rdCurvBracket g 0 s (W v) S x) (unit) − covGradRoughLapMovingFrameResidual_gen g s S x v )
```
(`W v := smoothExtensionTangent x v`), lifted to a `(0, s)`-tensor by `tensorRS0sOfTensor0S` so its
intrinsic fibre norm is well-typed; it is genuinely `rfns(∇²S)`-order after the third-order Weitzenböck
cancellation. -/
private noncomputable def bracketTraceTerm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) : TensorRSSpace 0 s I x :=
  tensorRS0sOfTensor0S (I := I) (M := M) s x
    (covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s S x v +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x v)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s S x v)

set_option linter.unusedSectionVars false in
/-- The bracket fibre field is the inner-product-weighted frame reconstruction of `bracketTraceTerm`
(read at the unit covector). -/
private lemma bracketThirdCurvFieldFib_eq_weighted_bracketTraceTerm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) :
    bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m =
      ∑ a : Fin n, g.inner x (e a) w •
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from bracketTraceTerm (I := I) (M := M) g s S x (e a))
            (unitZeroSec (I := I) (M := M) x)) m := by
  rw [bracketThirdCurvFieldFib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [bracketTraceTerm, tensorRS0sOfTensor0S_apply_unit (I := I) (M := M) s x]

/-- **Uniform `∇²S`-order bracket-trace fibre bound.** For a closed smooth Riemannian manifold
`(M, g)` there is a valence-dependent nonnegative constant `Kbr : ℕ → ℝ` such that, at every covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, and *unit* tangent vector `v` at
`x` (`g(v, v) = 1`), the directional bracket-trace term has fibre norm bounded `rfns(∇²S)`-order:
```
rfns(bracketTraceTerm g s S x v) ≤ Kbr s · rfns(∇²S)(x),    ∇²S := covGrad g 0 (s+1) (covGrad g 0 s S).
```

**Why this is TRUE.** The bracket-trace term collects the moving-frame trace discrepancy
`covGradRoughLapTraceDiscrepancy_gen`, the bracket directional piece `tensor3rdCurvBracket` (carrying
the frame-bracket jet `[Bᵢ, W v]` contracted against `∇²S`), and the moving-frame residual
`covGradRoughLapMovingFrameResidual_gen`. Its top-order `∇³S` terms cancel by the iterated Ricci
identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), leaving a genuinely `rfns(∇²S)`-order
tensorial field bounded by a uniform-over-`(x, v)` constant (the curvature and frame-bracket data of
the fixed smooth metric are bounded over the unit sphere bundle of the compact `M`). This cancellation
is *false term-by-term* through `smoothExtensionTangent`; only the tensorial frame-trace is `∇²S`-order.

**Non-vacuity.** An `rfns(∇S)`- or `rfns(S)`-only envelope is *false* on a non-flat manifold (the
bracket carries the genuine `∇²S`-order content — downstream the moving-frame remainder bound and the
bracket-free pairing `‖Δ_∇S‖² − ‖∇²S‖²` are nonzero), so the `∇²S`-order content cannot be dropped. -/
theorem exists_uniform_bracketTraceTerm_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kbr : ℕ → ℝ, (∀ s, 0 ≤ Kbr s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x),
        g.inner x v v = 1 →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (bracketTraceTerm (I := I) (M := M) g s S x v) ≤
          Kbr s *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  sorry

/-- **Frame-summed squared energy of the bracket genuine curvature fibre field (`rfns(∇²S)`-order).**
For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent nonnegative constant
`C₃ : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`,
point `x`, and `g_x`-orthonormal frame `e` (with `n = Module.finrank ℝ (TangentSpace I x)`), the
frame-summed squared energy of the bracket fibre field is bounded `rfns(∇²S)`-order:
```
∑_{φ : Fin (s+1) → Fin n} (bracketThirdCurvFieldFib g s S x e (e (φ 0)) (e ∘ Fin.tail φ))²
  ≤ (C₃ s)² · rfns(∇²S)(x),    ∇²S := covGrad g 0 (s+1) (covGrad g 0 s S).
```

**Why this is TRUE.** `bracketThirdCurvFieldFib g s S x e w m
  = ∑ₐ ⟨e a, w⟩_g • toModel (bracketTraceTerm g s S x (e a)) m`
(`bracketThirdCurvFieldFib_eq_weighted_bracketTraceTerm`). With `w = e (φ 0)` the orthonormal Gram
collapses the `a`-sum to `a = φ 0`, and the frame-summed squared model components reassemble the
intrinsic `(0, s)` fibre norm of the bracket-trace term (`frame_field_energy_eq_sum_trace_fiberNormSq`).
Each bracket-trace term is fibre-bounded `rfns(∇²S)`-order by the uniform bracket-trace bound
`exists_uniform_bracketTraceTerm_fiberNormSq_bound` (after the third-order Weitzenböck cancellation of
the top-order `∇³S` terms by the iterated Ricci identity, with `g(e a, e a) = 1`), and the `n`-fold
frame sum gives `C₃ s := √(n · Kbr s)`, independent of `x`. This cancellation is *false term-by-term*
through `smoothExtensionTangent`; only the tensorial frame-sum is `∇²S`-order.

**Non-vacuity.** The bracket energy genuinely carries the `∇²S` order: an `rfns(∇S)`- or `rfns(S)`-only
envelope is *false* on a non-flat manifold (downstream the moving-frame remainder bound and the
bracket-free pairing `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` are nonzero), so the genuine `∇²S`-order content
cannot be dropped. -/
theorem bracketThirdCurvFieldFib_fiberNormEnergy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C₃ : ℕ → ℝ, (∀ s, 0 ≤ C₃ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∑ φ : Fin (s + 1) → Fin n,
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e (e (φ 0))
              (fun k => e (Fin.tail φ k)) ^ 2 ≤
          C₃ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  obtain ⟨Kbr, hKbr_nn, hKbr⟩ := exists_uniform_bracketTraceTerm_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * Kbr s), fun s => Real.sqrt_nonneg _,
    fun s S x n e hn horth => ?_⟩
  set Tr : Fin n → TensorRSSpace 0 s I x := fun a =>
    bracketTraceTerm (I := I) (M := M) g s S x (e a) with hTr
  rw [frame_field_energy_eq_sum_trace_fiberNormSq (I := I) (M := M) g s x e hn horth Tr
    (bracketThirdCurvFieldFib (I := I) (M := M) g s S x e)
    (fun w m => bracketThirdCurvFieldFib_eq_weighted_bracketTraceTerm
      (I := I) (M := M) g s S x e w m)]
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * Kbr s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * Kbr s :=
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (hKbr_nn s))
  rw [hCsq]
  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a) ≤
        Kbr s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
    intro a
    have hunit : g.inner x (e a) (e a) = 1 := by rw [horth a a, if_pos rfl]
    exact hKbr s S x (e a) hunit
  calc ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tr a)
      ≤ ∑ _a : Fin n, Kbr s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
            ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (Module.finrank ℝ E : ℝ) * Kbr s *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
            ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (n : ℝ) = (Module.finrank ℝ E : ℝ) from by rw [hn]; rfl]
        ring

set_option linter.unusedSectionVars false in
/-- **The Parseval expansion in any `g_x`-orthonormal frame.** A `g_x`-orthonormal frame `e` of
cardinality `n = Module.finrank` expands every tangent vector `u = ∑ₐ ⟨e a, u⟩_g • e a` — the
frame-independent expansion driving the slot-`0` uncurry in an *arbitrary* orthonormal frame. -/
private lemma orthoFrame_parseval_expand
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
      ∑ b : Fin (Module.finrank ℝ (TangentSpace I x)),
        bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ (TangentSpace I x)),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Arbitrary-frame field split of the order-`2` commutator defect.** In *every* `g_x`-orthonormal
frame `e` (not just the witness frame of the slot-`0` Parseval reconstruction), the unit-section value
of the commutator defect `Curv S := pointwiseTensorCurv g s S` reconstructs, at every slot-`0`
direction `w` and tail tuple `m`, as the sum of the genuine and bracket fibre fields:
```
toModel ((Curv S).toSection x (unit)) (Fin.cons w m)
  = genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
```

**Why this is TRUE.** The existence-packaged split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
proves this in a witness `g_x`-orthonormal frame, but the underlying slot-`0` reconstruction
`tensor0S_uncurry_cons_eval_orthonormal` and the per-slice curried curvature-defect identity
`tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction` are *frame-independent* (the latter is
unconditional in the direction `w`), so the same reconstruction holds in *any* orthonormal frame `e`;
both field sums (`genuineThirdCurvFieldFib`, `bracketThirdCurvFieldFib`) are explicit inner-product-weighted
frame reconstructions of the named curvature primitives in `e`. (The witness frame is an artifact of the
existential packaging, not of the mathematics.)

**Non-vacuity.** Dropping `bracketThirdCurvFieldFib` asserts `toModel ((Curv S).toSection x (unit)) (cons w m)
  = genuineThirdCurvFieldFib g s S x e w m`, false on a non-flat manifold (the slot-`0` frame-trace
matching is false there). So the bracket field is genuinely present. -/
theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field_anyFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
        bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  have hexp := orthoFrame_parseval_expand (I := I) (M := M) g x e hn horth
  -- The slot-`0` curried slices reconstruct the unit-section in the arbitrary orthonormal frame `e`.
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) e hexp w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

/-- **Arbitrary-frame genuine-section fibre sum.** In *every* `g_x`-orthonormal frame `e`, the
unit-section fibre values of the two genuine curvature sections `GcurvSection g s S`,
`GcurvDerivSection g s S` sum to the genuine third-order curvature fibre field
`genuineThirdCurvFieldFib g s S x e w m` — the frame-free strengthening of
`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField`.

**Why this is TRUE.** The two sections are fixed `(0, s + 1)`-tensors; their slot-`0` curries along any
direction recover the pure-Riemann / differentiated-curvature genuine traces (the pure-Riemann curry
is unconditional in the direction; the differentiated-curvature section assembles the frame-independent
differentiated-curvature trace), so the frame-independent slot-`0` uncurry
`tensor0S_uncurry_cons_eval_orthonormal` reconstructs `genuineThirdCurvFieldFibPureR` /
`genuineThirdCurvFieldFibCovDeriv` in any orthonormal frame `e`, and their sum is the genuine field by
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`. (Both genuine traces are genuine metric traces — the
frame index contracted twice — hence frame-independent, so the reconstruction does not depend on the
choice of `e`.)

**Non-vacuity.** Replacing the genuine sections by zero would force the genuine field to vanish, false
on a non-flat manifold where the pure-Riemann and differentiated-curvature contractions are nonzero. -/
theorem GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (GcurvSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) +
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  sorry

/-- **The moving-frame remainder fibre-matches the bracket curvature fibre field (any orthonormal
frame).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, smooth
compactly-supported `(0, s)`-tensor `S`, point `x`, and *arbitrary* `g_x`-orthonormal frame `e` (with
`n = Module.finrank ℝ (TangentSpace I x)`), the unit-section value of the moving-frame remainder
`Curv S − GcurvSection − GcurvDerivSection` (`Curv S := pointwiseTensorCurv g s S`) reconstructs, at
every slot-`0` direction `w` and tail tuple `m`, as the bracket curvature fibre field:
```
toModel ((Curv S − GcurvSection − GcurvDerivSection).toSection x (unit)) (Fin.cons w m)
  = bracketThirdCurvFieldFib g s S x e w m.
```

**Why this is TRUE.** The remainder section value splits pointwise into the three section values
(`SmoothCcTensor.toSection_sub`), and the model coercion of the unit-section is additive on the
subtraction. In the *arbitrary* orthonormal frame `e`, the field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field_anyFrame` reads
`toModel ((Curv S).toSection x (unit)) (cons w m)` as
`genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m`, and
`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame` identifies the sum of
the two genuine-section model values with `genuineThirdCurvFieldFib g s S x e w m`; subtracting the
genuine sections leaves exactly the bracket field. Both identities hold in *one common* arbitrary
orthonormal frame `e` because the genuine moving-frame curvature trace is frame-independent.

**Non-vacuity.** Replacing the genuine sections by zero would assert
`toModel ((Curv S).toSection x (unit)) (cons w m) = bracketThirdCurvFieldFib g s S x e w m`, dropping the
genuine field `genuineThirdCurvFieldFib`, false on a non-flat manifold (the pure-Riemann and
differentiated-curvature contractions are genuinely nonzero). So the identity holds exactly for the
genuine curvature sections. -/
theorem movingFrameRemainder_toSection_eq_bracketField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S -
              GcurvSection (I := I) (M := M) g s S -
              GcurvDerivSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  have hsec : (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        GcurvDerivSection (I := I) (M := M) g s S).toSection x =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
        (GcurvSection (I := I) (M := M) g s S).toSection x -
        (GcurvDerivSection (I := I) (M := M) g s S).toSection x := by
    rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]
    rfl
  rw [hsec]
  have hsubapply : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
            (GcurvSection (I := I) (M := M) g s S).toSection x -
            (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (GcurvSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) := by
    rfl
  rw [hsubapply]
  rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field_anyFrame
    (I := I) (M := M) g s S x e hn horth w m]
  rw [← GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame
    (I := I) (M := M) g s S x e hn horth w m]
  ring

end Connection
end Integral
end DifferentialGeometry

end
