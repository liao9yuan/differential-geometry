import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0SliceFiberNormDomination

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

* `movingFrameRemainder_toSection_eq_bracketField` — the reading of the moving-frame remainder as the
  bracket field, in a *single witness* orthonormal frame `e`; it closes over the frame-free field split
  (`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field_anyFrame`, holding in any orthonormal
  frame) and the genuine-section sum match
  (`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame`, holding only in its
  construction witness frame). The match is *existential* in `e`, not universal: the
  differentiated-curvature reconstruction is non-linear in the direction (it sees the covariant
  derivative of `smoothExtensionTangent`), so the genuine-section sum does *not* match
  `genuineThirdCurvFieldFib` in every orthonormal frame.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
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

set_option linter.unusedSectionVars false in
/-- Non-negativity of the metric self-inner product `g(x; v, v)`. -/
private lemma g_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

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
the full gradient fibre norm `rfns(∇S)` (`riemannianFiberNormSq_covApply_le_covGrad`, the slot-`0`
Parseval domination of a unit-direction gradient slice). Summing the `n`-fold frame sum by
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
  classical
  -- Uniformise the rank-`s` continuous proportional curvature envelope over the compact `M`.
  have huniform : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x v w T) ≤
          C * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
    intro s
    obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
      exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
        (I := I) (M := M) g s
    have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
    obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
    refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
    have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
      le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
    have hfactor_nonneg :
        0 ≤ g.inner x v v * g.inner x w w *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
      mul_nonneg
        (mul_nonneg (g_inner_self_nonneg (I := I) (M := M) g x v)
          (g_inner_self_nonneg (I := I) (M := M) g x w))
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T)
    have hstep : Ccurv x * g.inner x v v * g.inner x w w *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T ≤
        max C₀ 0 * g.inner x v v * g.inner x w w *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
      have h := mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
      nlinarith [h]
    exact le_trans (hCcurv_bound x v w T) hstep
  choose C hC_nonneg hC_bound using huniform
  refine ⟨fun s => (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * C s), fun s => ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC_nonneg s))
  intro s S x v hv
  -- Expand the trace as a frame sum of `riemannOp` summands.
  set n : ℕ := Module.finrank ℝ E with hn_def
  set F : Fin n → TensorRSSpace 0 s I x := fun i =>
    riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
      (smoothExtensionTangent (I := I) x v)
      (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
        (fun y : M => S.toSection y)) x with hF_def
  have htrace : genuineCurvTraceFixedFramePureR (I := I) g s
      (smoothExtensionTangent (I := I) x v) (smoothOrthoFrame (I := I) g x)
      (fun y : M => S.toSection y) x = ∑ i : Fin n, F i := by
    rw [genuineCurvTraceFixedFramePureR]
  rw [htrace]
  -- Smoothness inputs for the bundled-operator rewrite of each summand.
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x v)) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  -- Each summand is the bundled curvature operator on the directional slice.
  have hFop : ∀ i : Fin n, F i =
      riemannOp (tensorCov (I := I) g 0 s) x
        (smoothOrthoFrame (I := I) g x i x) (smoothExtensionTangent (I := I) x v x)
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x) := by
    intro i; rw [hF_def]
    exact tensor3rdCurv_pure_R_eq_riemannOp (I := I) g 0 s i hW hS_total
  -- Directional-slice fibre domination: each `∇_{B_i} S(x)` is bounded by the full gradient.
  -- The slot-`0` slice of `(covGrad g 0 s S).toSection x` along `B_i x`, in the moving frame
  -- `e a := B_a x`, has the same unit-section value `(∇_{B_i} S(x))(unit)` as the directional
  -- covariant derivative, so equal fibre norm; the slot-`0` Parseval domination bounds it by `∇S`.
  have hcovApply_le : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro i
    set eF : Fin n → TangentSpace I x := fun a => smoothOrthoFrame (I := I) g x a x with heF_def
    have hnF : n = Module.finrank ℝ (TangentSpace I x) := hn_def
    have horthF : ∀ a b : Fin n, g.inner x (eF a) (eF b) = if a = b then (1 : ℝ) else 0 := by
      intro a b; rw [heF_def]; exact smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
    set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
    -- `fiberNormSqSummand`-form representations of the fibre norm at ranks `s` and `s + 1` in `eF`.
    have hweight : ∀ (m : ℕ),
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (eF (K₀ k))) : Tensor0SSpace 0 I x) =
          unitZeroSec (I := I) (M := M) x := by
      intro _
      have hcf : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (eF (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 eF K₀ := rfl
      rw [hcf]
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro m
      have hL : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 eF K₀) m = 1 := by
        have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 eF K₀) m =
            coframeS (I := I) (M := M) g x 0 eF K₀ (fun k : Fin 0 => k.elim0) := by
          apply congrArg; funext k; exact k.elim0
        rw [h1, coframeS_apply (I := I) (M := M) g x 0 eF K₀ (fun k : Fin 0 => k.elim0)]
        simp
      have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) m = 1 := by
        rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hL, hR]
    have hreprS : ∀ U : TensorRSSpace 0 s I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x U =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 s U n eF K J := by
      intro U
      rw [riemannianFiberNormSq_eq_sum_toModel_sq (I := I) (M := M) g s x U eF hnF horthF]
      rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
      · refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [fiberNormSqSummand, hweight s]; rfl
      · intro K _ hK; exact absurd (Subsingleton.elim K (fun k : Fin 0 => k.elim0)) hK
      · intro h; exact absurd (Finset.mem_univ (fun k : Fin 0 => k.elim0)) h
    have hreprSucc : ∀ U : TensorRSSpace 0 (s + 1) I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x U =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) U n eF K J := by
      intro U
      rw [riemannianFiberNormSq_eq_sum_toModel_sq (I := I) (M := M) g (s + 1) x U eF hnF horthF]
      rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
      · refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [fiberNormSqSummand, hweight (s + 1)]; rfl
      · intro K _ hK; exact absurd (Subsingleton.elim K (fun k : Fin 0 => k.elim0)) hK
      · intro h; exact absurd (Finset.mem_univ (fun k : Fin 0 => k.elim0)) h
    -- The slot-`0` slice in direction `eF i` equals the directional covariant derivative `∇_{B_i} S`.
    have hslice_eq :
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (slot0Curry (I := I) (M := M) g x s eF K₀
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) i) =
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x) := by
      rw [riemannianFiberNormSq_eq_sum_toModel_sq (I := I) (M := M) g s x _ eF hnF horthF,
        riemannianFiberNormSq_eq_sum_toModel_sq (I := I) (M := M) g s x _ eF hnF horthF]
      refine Finset.sum_congr rfl (fun ψ _ => ?_)
      congr 2
      have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              slot0Curry (I := I) (M := M) g x s eF K₀
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) i)
              (unitZeroSec (I := I) (M := M) x) =
            tensor0S_curry (I := I) (M := M) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                (covGrad (I := I) (M := M) g 0 s S).toSection x)
                (unitZeroSec (I := I) (M := M) x)) (eF i) := by
        rw [slot0Curry_apply (I := I) (M := M) g x s eF K₀
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) i
          (unitZeroSec (I := I) (M := M) x)]
        rw [hweight s]
        have hscalar : tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
          rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
          have hone : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
              (fun k : Fin 0 => k.elim0) = (1 : ℝ) := by
            rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
            simp
          rw [← hone]; rfl
        rw [hscalar, one_smul]
      rw [hslot]
      rw [curry_covGrad_unit_eval_genVal (I := I) (M := M) g s S x (eF i)]
      rw [covApply_apply, heF_def]
      rfl
    rw [← hslice_eq]
    exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g s x eF K₀
      hreprS hreprSucc ((covGrad (I := I) (M := M) g 0 s S).toSection x) i
  -- Per-summand fibre bound: uniform curvature sup × unit Gram scalars × directional slice.
  have hgv : g.inner x (smoothExtensionTangent (I := I) x v x) (smoothExtensionTangent (I := I) x v x)
      = 1 := by rw [smoothExtensionTangent_eq x v]; exact hv
  have hper : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (F i) ≤
        C s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro i
    rw [hFop i]
    have hgB : g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) = 1 := by
      have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i; rwa [if_pos rfl] at this
    have hbound := hC_bound s x (smoothOrthoFrame (I := I) g x i x)
      (smoothExtensionTangent (I := I) x v x)
      (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
        (fun y : M => S.toSection y) x)
    rw [hgB, hgv, mul_one, mul_one] at hbound
    refine le_trans hbound ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC_nonneg s)
    exact hcovApply_le i
  -- Sum the per-summand bounds with `n`-subadditivity of the fibre norm.
  calc riemannianFiberNormSq (I := I) (M := M) g 0 s x (∑ i : Fin n, F i)
      ≤ (n : ℝ) * ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (F i) := by
        have := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 s x
          (Finset.univ : Finset (Fin n)) F
        rwa [Finset.card_univ, Fintype.card_fin] at this
    _ ≤ (n : ℝ) * ∑ _i : Fin n, C s *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hper i)) (Nat.cast_nonneg n)
    _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * C s) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn_def]
        ring

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

/-- **Witness-frame genuine-section fibre sum.** At every base point `x` there is a *single*
`g_x`-orthonormal frame `e` in which the unit-section fibre values of the two genuine curvature
sections `GcurvSection g s S`, `GcurvDerivSection g s S` sum to the genuine third-order curvature
fibre field `genuineThirdCurvFieldFib g s S x e w m`. This is the existential-witness-frame fibre
match; it is the same statement as the canonical
`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField`
(`MovingFrameCurvatureTraceSmooth`), re-exported here as the genuine-section input to the moving-frame
remainder fibre match `movingFrameRemainder_toSection_eq_bracketField`.

**Why this is TRUE.** `GcurvSection` is the slot-`0` uncurry of the *direction-linear* pure-Riemann
genuine-trace CLM, so its slot-`0` curry reconstructs `genuineThirdCurvFieldFibPureR` against any
direction; `GcurvDerivSection` is the slot-`0` uncurry of the differentiated-curvature direction CLM,
whose slot-`0` curry recovers the differentiated-curvature trace exactly along the frame vectors of
the construction frame `smoothOrthoFrame g x`, so the reconstruction of `genuineThirdCurvFieldFibCovDeriv`
holds in *that* witness frame `e`. Their sum is the genuine field by
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv` (`GcurvSection_GcurvDerivSection_spec`).

**Frame-dependence warning — the `∀ e` form is FALSE.** This match cannot be strengthened to *every*
`g_x`-orthonormal frame `e`. The LHS is the evaluation of the two *fixed* `(0, s + 1)`-tensors
`GcurvSection`, `GcurvDerivSection` (`e`-independent), but the RHS `genuineThirdCurvFieldFib g s S x e`
collapses (orthonormal Gram) to `toModel (tensor3rdCurvGenuine g 0 s (smoothExtensionTangent x (e (φ 0)))
S x (unit)) (…)`, whose differentiated-curvature summand `∇_{Bᵢ}(R(Bᵢ, ·) S)` is *non-linear* in the
direction — by the Leibniz rule (`riemannSec_smul_right`-style covariant Leibniz) its value at
`smoothExtensionTangent x (e (φ 0))` sees the covariant derivative of the extension (an uncontrolled
`Classical.choose`), so it depends on the choice of `e`. With an `e` whose differentiated-curvature
reconstruction does not match the construction frame `smoothOrthoFrame g x`, the RHS differs from the
fixed LHS; hence the universal-`e` form is unsatisfiable and only the existential witness frame is
correct (cf. the non-tensorial direction dependence documented at `genuineCovDerivFib_contMDiff`).

**Non-vacuity.** Replacing the genuine sections by zero would force the genuine field to vanish, false
on a non-flat manifold where the pure-Riemann and differentiated-curvature contractions are nonzero. -/
theorem GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) +
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m :=
  GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField (I := I) (M := M) g s S x

/-- **The moving-frame remainder fibre-matches the bracket curvature fibre field (witness frame).**
For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S` and point `x`, there is a *single* `g_x`-orthonormal frame `e` (the genuine-section
witness frame, with `n = Module.finrank ℝ (TangentSpace I x)`) in which the unit-section value of the
moving-frame remainder `Curv S − GcurvSection − GcurvDerivSection` (`Curv S := pointwiseTensorCurv g s S`)
reconstructs, at every slot-`0` direction `w` and tail tuple `m`, as the bracket curvature fibre field:
```
toModel ((Curv S − GcurvSection − GcurvDerivSection).toSection x (unit)) (Fin.cons w m)
  = bracketThirdCurvFieldFib g s S x e w m.
```

**Why this is TRUE.** Take `e` to be the genuine-section witness frame of
`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame` (in which the sum of
the two genuine-section unit-section model values equals `genuineThirdCurvFieldFib g s S x e w m`). The
remainder section value splits pointwise into the three section values (`SmoothCcTensor.toSection_sub`),
and the model coercion of the unit-section is additive on the subtraction. The field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field_anyFrame` is *frame-free* (it holds in every
orthonormal frame, in particular in `e`) and reads `toModel ((Curv S).toSection x (unit)) (cons w m)`
as `genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m`; subtracting the
genuine sections (whose sum is the genuine field, in the *same* frame `e`) leaves exactly the bracket
field.

**Frame-dependence warning — the `∀ e` form is FALSE.** The genuine-section sum match holds only in the
construction witness frame, not in *every* orthonormal `e` (the differentiated-curvature reconstruction
is non-linear in the direction via the covariant derivative of `smoothExtensionTangent`; see the
warning on `GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame` and
`genuineCovDerivFib_contMDiff`), so this fibre match is correctly stated only existentially in a single
witness frame `e`, not universally.

**Non-vacuity.** Replacing the genuine sections by zero would assert
`toModel ((Curv S).toSection x (unit)) (cons w m) = bracketThirdCurvFieldFib g s S x e w m`, dropping the
genuine field `genuineThirdCurvFieldFib`, false on a non-flat manifold (the pure-Riemann and
differentiated-curvature contractions are genuinely nonzero). So the identity holds exactly for the
genuine curvature sections. -/
theorem movingFrameRemainder_toSection_eq_bracketField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (pointwiseTensorCurv (I := I) (M := M) g s S -
                  GcurvSection (I := I) (M := M) g s S -
                  GcurvDerivSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hgenuine⟩ :=
    GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField_anyFrame
      (I := I) (M := M) g s S x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
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
  rw [← hgenuine w m]
  ring

end Connection
end Integral
end DifferentialGeometry

end
