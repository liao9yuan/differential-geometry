import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroupIntrinsic
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbeddingCm

/-!
# Parabolic smoothing of the intrinsic tensor heat semigroup into every `Hˢ`

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the
intrinsic tensor heat semigroup `tensorHeatSemigroup_intrinsic g r s t`
(built in `HeatSemigroupIntrinsic.lean` from the chart-locality-free
resolvent eigenbasis) acts diagonally on that eigenbasis, multiplying the
`i`-th Fourier coefficient by `exp(-λᵢ t)` with `λᵢ ≥ 0` the
connection-Laplacian eigenvalue.

Because positive time provides spectral decay that beats every polynomial
weight `(1 + λᵢ)^σ`, the heat semigroup is a **parabolic smoothing**
operator: for `t > 0` the output `e^{tΔ} u₀` lies in the spectral Sobolev
space `Hˢ` for *every* exponent `σ ≥ 0`, even though the initial datum
`u₀` is only `L²`. The witness is the heat-rescaled coordinate family,
whose weighted-`ℓ²` summability at every exponent is the spectral lemma
`tensorHs.heatHs_weighted_summable` (file `SmoothingHs.lean`).

## Main results

* `tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact` — the intrinsic
  eigenbasis coordinate of `e^{tΔ} u₀` is `exp(-λᵢ t)` times the
  coordinate of `u₀`.
* `heat_semigroup_into_tensorHs` — for `0 < t`, `u₀ : L²`, and any
  `σ ≥ 0`, there is an element `v : tensorHs g r s σ` whose
  chart-locality-free `L²` realization `tensorHsToL2_ofCompact` is exactly
  `e^{tΔ} u₀`. Equivalently: `e^{tΔ} u₀ ∈ Hˢ`.
* `heat_semigroup_into_all_tensorHs` — the simultaneous-in-`σ` packaging:
  a single `u₀`-dependent family `σ ↦ vσ` of `Hˢ` witnesses, all
  realizing the *same* `L²` element `e^{tΔ} u₀`. This is the precise
  statement that `e^{tΔ} u₀` lies in the **spectral smooth subspace**
  `⋂_σ Hˢ` for `t > 0`.

## The reduction of the smooth-representative gate

The companion direction — that an element of the spectral smooth subspace
has a genuine `C^∞` (`SmoothCcTensor`) representative — is **not** proved
here; it is the deepest analytic gate of the construction. This file
records its precise reduction in `SpectralSmoothRealizesAsSmooth` and the
documentation lemma `spectral_smooth_realization_reduction`, which spell
out the two analytic ingredients (an *all-orders, unconditional, tensor*
elliptic-regularity bootstrap, and the unconditional `C^m` tensor Sobolev
embedding `iteratedCovGrad_toSobolev_embedding_Cm`) on which it depends.
See the section header below for the exact landscape of which bootstrap
lemmas already exist unconditionally and which remain.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹`, eigenvalues `λᵢ ≥ 0`, heat factor `exp(-λᵢ t) ∈ (0, 1]`
for `t ≥ 0`, and weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The intrinsic eigenbasis coordinate of the heat output

The single fact that turns the diagonal eigenbasis action
(`tensorHeatSemigroup_intrinsic_inner_eigenbasis`) into a statement about
the chart-locality-free coordinate functional `tensorL2Coeff_ofCompact`. -/

/-- **Heat-output coordinate formula.** For `t ≥ 0`, the intrinsic
eigenbasis coordinate of `e^{tΔ} u₀` is `exp(-λᵢ t)` times the coordinate
of `u₀`. Here the coordinate functional `tensorL2Coeff_ofCompact` is taken
against the intrinsic compactness witness
`tensorResolventL2_isCompactOperator_intrinsic g r s`. -/
theorem tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
        (tensorHeatSemigroup_intrinsic (I := I) (M := M) g r s t u₀) i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
          u₀ i := by
  rw [tensorL2Coeff_ofCompact_eq_inner, tensorL2Coeff_ofCompact_eq_inner]
  exact tensorHeatSemigroup_intrinsic_inner_eigenbasis
    (I := I) (M := M) g r s ht u₀ i

/-! ## The `L²` base element as an `H⁰` coordinate family

For a fixed `u₀ : L²`, its intrinsic eigenbasis coordinate family is the
coordinate family of an `H⁰` element, via the chart-locality-free
identification `tensorHsZeroEquivL2_ofCompact`. Applying the spectral
heat rescaling `heatHsFun σ ht` to this `H⁰` element produces, for `0 < t`,
an `Hˢ` element with coordinate `exp(-λᵢ t) · ⟪bᵢ, u₀⟫`. -/

/-- The `H⁰` element carrying the intrinsic eigenbasis coordinate family of
`u₀`: its `i`-th coordinate is `tensorL2Coeff_ofCompact … u₀ i`. -/
private def baseHZero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) :
    tensorHs (I := I) (M := M) g r s 0 :=
  (tensorHsZeroEquivL2_ofCompact (I := I) (M := M)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)).symm u₀

private lemma baseHZero_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (baseHZero (I := I) (M := M) g r s u₀).coeff i =
      tensorL2Coeff_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
        u₀ i :=
  tensorHsZeroEquivL2_ofCompact_symm_coeff (I := I) (M := M) _ u₀ i

/-- The `Hˢ` witness for the heat output: the heat-rescaling
`heatHsFun σ ht` applied to the `H⁰` base coordinate family of `u₀`.
Its `i`-th coordinate is `exp(-λᵢ t) · ⟪bᵢ, u₀⟫`, square-summable against
the weight `(1 + λᵢ)^σ` for every `σ` by `heatHs_weighted_summable`. -/
def heatHsWitness (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHs (I := I) (M := M) g r s σ :=
  tensorHs.heatHsFun (I := I) (M := M) σ ht
    (baseHZero (I := I) (M := M) g r s u₀)

/-- The `i`-th coordinate of the heat witness is `exp(-λᵢ t)` times the
intrinsic eigenbasis coordinate of `u₀`. -/
@[simp] theorem heatHsWitness_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
          u₀ i := by
  unfold heatHsWitness
  rw [tensorHs.heatHsFun_coeff, baseHZero_coeff]

/-! ## The smoothing theorem: `e^{tΔ} u₀ ∈ Hˢ` for every `σ`, `t > 0` -/

/-- **Parabolic smoothing into `Hˢ`.** For `0 < t`, any initial datum
`u₀ : L²`, and any exponent `σ ≥ 0`, the heat output `e^{tΔ} u₀` is the
chart-locality-free `L²` realization of the `Hˢ` element
`heatHsWitness g r s σ ht u₀`:

  `tensorHsToL2_ofCompact h_compact hσ (heatHsWitness … σ ht u₀)
      = tensorHeatSemigroup_intrinsic g r s t u₀`.

Thus `e^{tΔ} u₀` lies in the image of `Hˢ` in `L²` — it is `σ`-smooth —
for *every* `σ ≥ 0`. The proof matches the two `L²` tensors on their
intrinsic eigenbasis coordinates: the witness side equals
`exp(-λᵢ t) · ⟪bᵢ, u₀⟫` by `heatHsWitness_coeff` (after the inclusion's
coordinate-faithfulness `tensorHsToL2_ofCompact_tensorL2Coeff_ofCompact`),
and the heat-output side equals the same by
`tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact`. -/
theorem heat_semigroup_into_tensorHs (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHsToL2_ofCompact (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
        hσ (heatHsWitness (I := I) (M := M) g r s σ ht u₀) =
      tensorHeatSemigroup_intrinsic (I := I) (M := M) g r s t u₀ := by
  set h_compact :=
    tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s
    with hcompact_def
  -- The chart-locality-free eigenbasis representation is injective, so it
  -- suffices to match `tensorL2Coeff_ofCompact` on both sides.
  refine (tensorResolventHilbertEigenbasisSigma_ofCompact
    (I := I) (M := M) h_compact).repr.injective ?_
  ext i
  -- The two coordinates are both `exp(-λᵢ t) · ⟪bᵢ, u₀⟫`.
  have hlhs :
      ((tensorResolventHilbertEigenbasisSigma_ofCompact
          (I := I) (M := M) h_compact).repr
        (tensorHsToL2_ofCompact (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ (heatHsWitness (I := I) (M := M) g r s σ ht u₀))) i =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff_ofCompact (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHsToL2_ofCompact_tensorL2Coeff_ofCompact
      (I := I) (M := M) (h_compact := h_compact) hσ
      (heatHsWitness (I := I) (M := M) g r s σ ht u₀) i
    rw [heatHsWitness_coeff] at h
    simpa only [tensorL2Coeff_ofCompact] using h
  have hrhs :
      ((tensorResolventHilbertEigenbasisSigma_ofCompact
          (I := I) (M := M) h_compact).repr
        (tensorHeatSemigroup_intrinsic (I := I) (M := M) g r s t u₀)) i =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff_ofCompact (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
      (I := I) (M := M) g r s ht.le u₀ i
    simpa only [tensorL2Coeff_ofCompact] using h
  rw [hlhs, hrhs]

/-- **Simultaneous parabolic smoothing into every `Hˢ`.** For `0 < t` and
`u₀ : L²`, there is a family `vσ : Hˢ` (one element per exponent `σ ≥ 0`)
all realizing the *same* `L²` element `e^{tΔ} u₀`. This is the precise
statement that `e^{tΔ} u₀` lies in the spectral smooth subspace
`⋂_σ Hˢ`: every Sobolev order is attained, witnessed coherently by the
single heat output. -/
theorem heat_semigroup_into_all_tensorHs (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2_ofCompact (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator_intrinsic
              (I := I) (M := M) g r s) hσ v =
          tensorHeatSemigroup_intrinsic (I := I) (M := M) g r s t u₀ :=
  fun σ hσ =>
    ⟨heatHsWitness (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩

/-! ## The smooth-representative gate and its reduction

The complementary direction is the deepest analytic content of the whole
spectral programme: an element of the spectral smooth subspace
`⋂_σ Hˢ` — equivalently a tensor in `⋂_k domain((1 - Δ_∇)^k)` — has a
genuine `C^∞` representative as a `SmoothCcTensor`. We do **not** prove it
here; we record the precise predicate `SpectralSmoothRealizesAsSmooth` and
a documentation lemma stating which already-existing unconditional
ingredients it reduces to, and which single ingredient remains.

### Landscape of the all-orders elliptic-regularity infrastructure

The chart-`H^{2k}` regularity needed to convert "lies in every domain
`((1 - Δ)^k)`" into "all chart-partial derivatives exist in `L²` at every
order" is, for the **scalar** Laplacian, available **unconditionally** (no
`HasLocallyConstantChartAt`): the polymorphic-in-`k` bootstrap

  `chartPushed_memWkp_two_k_of_laplacianDomainPow`
    (`Analysis/Laplacian/Regularity/Iterated/BootstrapChartHmAnyK.lean`)

proves, for every `k : ℕ` and every `u_h ∈ laplacianDomainPow g k`, the
chart-`H^{2k}` regularity `MemWkp (2 * k) 2` of the chart-pushed
representative — with no chart-selection hypothesis anywhere in its file
(verified: zero `HasLocallyConstantChartAt` occurrences in
`BootstrapChartHmAnyK`, `BootstrapChartHmStrong`,
`BootstrapChartHmCanonical`, `BootstrapChartHmFinal`, `MixedPartials`,
`BootstrapChartHm`).

The **tensor** analog at arbitrary order is, by contrast, presently
`HasLocallyConstantChartAt`-gated: `eigenvector_chartComponent_memWkp_arbitrary`
(`…/EllipticBridge/EigenvectorWeakSolution/EigenvectorArbitraryKRegularity.lean`)
carries `h_atlas` throughout. The remaining piece of the gate is therefore
an **unconditional tensor all-orders bootstrap** — the
`TensorEigenIdx`-indexed, `(r, s)`-valued analog of
`chartPushed_memWkp_two_k_of_laplacianDomainPow`, obtained by running the
scalar `…AnyK` machinery component-wise on the chart-frame scalar
components `tensorChartComponentScalar` of an
`u ∈ ⋂_k domain((1 - Δ_∇)^k)` element.

### The embedding half is already unconditional

The other half — converting all-orders chart-Sobolev regularity into a
`C^∞` pointwise tensor field — is the unconditional `C^m` tensor Sobolev
embedding

  `iteratedCovGrad_toSobolev_embedding_Cm`
    (`PDE/RicciFlow/SobolevEmbeddingCm.lean`),

which bounds, for `2k > dim M + 2m`, the `C^m` fibre norms of a
`SmoothCcTensor` by its `H^{2(k-j)}` Sobolev norms (no `h_atlas`; it is
built on the Riemannian-fibre `C⁰` embedding
`tensorPouSobolevHilbert_embedding_Ck_gNorm`). Combined over all `m`, this
yields the `C^∞` control; what it does **not** by itself supply is a
*genuine smooth representative of a general `L²`/`Hˢ` class*, which is
exactly what the missing unconditional tensor bootstrap above produces. -/

/-- **The smooth-representative gate (predicate on the data).**

`SpectralSmoothRealizesAsSmooth g r s` holds when every `L²` tensor `u`
that lies (via the chart-locality-free inclusion) in `Hˢ` for *every*
exponent `σ ≥ 0` admits a genuine `C^∞` representative: a
`SmoothCcTensor g r s` whose `L²` class `(↑T : TensorL2 r s g)` equals
`u`.

The hypothesis "`u ∈ Hˢ for every σ`" is phrased as: for each `σ ≥ 0`
there is an `Hˢ` element whose `tensorHsToL2_ofCompact` realization is `u`
(the same shape produced by `heat_semigroup_into_all_tensorHs`). This is
the spectral smooth subspace `⋂_σ Hˢ`.

No term in this file assumes this predicate; it is the precise remaining
analytic content (an unconditional tensor all-orders elliptic-regularity
bootstrap composed with the unconditional `C^m` Sobolev embedding;
see the section header for the landscape). -/
def SpectralSmoothRealizesAsSmooth (g : SmoothRiemannianMetric I M)
    (r s : ℕ) : Prop :=
  ∀ u : TensorL2 r s g,
    (∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2_ofCompact (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator_intrinsic
              (I := I) (M := M) g r s) hσ v = u) →
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u

/-- **Documented reduction of the smooth-representative gate to the heat
output.** Granting the gate predicate `SpectralSmoothRealizesAsSmooth`, the
heat output `e^{tΔ} u₀` (for `0 < t`) — which lies in every `Hˢ` by
`heat_semigroup_into_all_tensorHs` — has a genuine `C^∞`
(`SmoothCcTensor`) representative.

This is *not* an unconditional theorem: it consumes the gate as a
hypothesis. It is recorded to make the reduction explicit — the heat
smoothing supplies the all-orders membership `⋂_σ Hˢ` unconditionally
(`heat_semigroup_into_all_tensorHs`, proved above with axioms exactly
`{propext, Classical.choice, Quot.sound}`); the *only* remaining gap to a
`C^∞` representative is the gate, whose two analytic ingredients are
documented in the section header. -/
theorem spectral_smooth_realization_reduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_gate : SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
        tensorHeatSemigroup_intrinsic (I := I) (M := M) g r s t u₀ :=
  h_gate _ (fun σ hσ =>
    ⟨heatHsWitness (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
