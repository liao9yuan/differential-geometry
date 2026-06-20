import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial

/-!
# The geometric Ricci–DeTurck nonlinearity on the spectral Sobolev scale

The chart-locality-free maximal-regularity strong-existence engine
`deTurckRemainder_strong_shortTime_exists`
(`DeTurck/RemainderShortTimeExistence.lean`) consumes a *locally Lipschitz* first-order
nonlinearity

  `N : tensorHs g_bg 0 2 (a + 1) → tensorHs g_bg 0 2 a`

(`a : ℝ` a non-negative spectral Sobolev exponent), and produces a strong
solution of the quasi-linear tensor heat equation
`∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`.

This file constructs the *geometric* `N` for the Ricci–DeTurck flow.  The
top-order part of the Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg g`
coincides — by the gauge cancellation `deTurckNonlinearitySpectral_principalPart_cancels`
— with the connection Laplacian `Δ_∇`, so the *remainder*

  `N(u) := deTurckRicciRHS g_bg (g_bg + h(u)) − Δ_∇ h(u)`,
  `h(u) := realized metric perturbation of u`,

is genuinely first order in `h(u)`.

## The realization, and well-typedness via the spectral summability of smooth data

`tensorHs g_bg 0 2 σ` is a structure carrying an abstract spectral coordinate
family `coeff : TensorEigenIdx → ℝ` plus a weighted-`ℓ²` summability witness, not
a pointwise tensor field.  To write `N(u)` we realize the finitely-supported `u`
as a genuine smooth compactly-supported `(0,2)`-tensor section
`T_u = tensorHsSmoothRepr u` (the chart-locality-free smooth
representative on the dense finite-support subspace), assemble the smooth metric
`g_bg + h_sym(T_u)` on its validity domain via `tensorSectionRealizeMetric`, and
take the smooth `(0,2)`-tensor section of the geometric remainder
`deTurckRHSSection g_bg (g_bg + h_sym) − Δ_∇ T_u`.

The geometric remainder section is again a `SmoothCcTensor g_bg 0 2`; by the
spectral-scale summability of a smooth compactly-supported tensor
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at *every* real Sobolev
order) its eigenbasis coordinates are weighted square-summable at order `a`,
which is exactly the witness needed to package those coordinates as an element of
`tensorHs g_bg 0 2 a`.  This is the type-level content of the construction.

Off the validity domain — when `u` is not finitely supported, or its
extracted-and-symmetrized form is not `g_bg`-fibre small (so `g_bg + h_sym` is not
an honest metric) — the nonlinearity returns the zero element of
`tensorHs g_bg 0 2 a`.

## Sign convention

Geometer `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; the resolvent is `(1 − Δ_∇)⁻¹`,
weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The validity-domain predicate for realizing `u : H^{a+1}` as a metric
perturbation: `u` is finitely supported and its extracted symmetric bilinear
form is `g_bg`-fibre small with some constant `< 1` (so `g_bg + h_sym` is an
honest, positive-definite smooth metric). -/
def realizableAt (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) : Prop :=
  ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
    gFibreOpBound (I := I) (M := M) g_bg
      (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ'

open scoped Classical in
/-- The smooth metric realized from a finitely-supported, fibre-small order-`σ`
spectral element `u`: the genuine `g_bg + h_sym(u)` on the validity domain
`realizableAt`, and `g_bg` otherwise. -/
def realizeMetricAt (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) :
    SmoothRiemannianMetric I M :=
  if h : realizableAt (I := I) g_bg u then
    tensorSectionRealizeMetric (I := I) g_bg
      (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M) u h.choose)
      h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  else
    g_bg

/-- On the validity domain, the realized metric's inner product is
`g_bg + tensorHsBilinSymm u`. -/
theorem realizeMetricAt_inner_of_realizable (g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg
      (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ')
    (x : M) (v w : TangentSpace I x) :
    (realizeMetricAt (I := I) g_bg u).inner x v w =
      g_bg.inner x v w + tensorHsBilinSymm (I := I) g_bg u hu_fs x v w := by
  classical
  have hex : realizableAt (I := I) g_bg u := ⟨hu_fs, δ', hδ'_lt, hδ'⟩
  rw [realizeMetricAt, dif_pos hex, tensorSectionRealizeMetric_inner]
  rfl

/-- Off the validity domain, the realized metric is the background metric. -/
theorem realizeMetricAt_of_not_realizable (g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu : ¬ realizableAt (I := I) g_bg u) :
    realizeMetricAt (I := I) g_bg u = g_bg := by
  classical
  rw [realizeMetricAt, dif_neg hu]

open scoped Classical in
/-- The geometric Ricci–DeTurck remainder as a smooth compactly-supported
`(0,2)`-tensor section, re-tagged by the background metric `g_bg`.

On the validity domain, with smooth representative `T_u` of `u` and realized
metric `g_u = g_bg + h_sym(u)`, this is

  `deTurckRHSSection g_bg g_u − rawTensorConnLapSmooth g_bg 0 2 T_u`

(the Ricci–DeTurck right-hand side of `g_u`, minus the connection Laplacian of the
perturbation — the gauge-cancelled first-order remainder).  Off the validity
domain it is the zero section. -/
def deTurckRemainderSection (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) :
    SmoothCcTensor g_bg 0 2 :=
  if h : realizableAt (I := I) g_bg u then
    { toSection :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g_bg u)).toSection
      hasCompactSupport :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g_bg u)).hasCompactSupport }
      - rawTensorConnLapSmooth (I := I) g_bg 0 2
          (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
            (I := I) (M := M) u h.choose)
  else
    0

/-- The intrinsic resolvent-compactness witness for the rank-`(0,2)` tensor
resolvent on the closed manifold `(M, g_bg)`. -/
private def hCompact (g_bg : SmoothRiemannianMetric I M) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g_bg 0 2) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2

/-- **The geometric Ricci–DeTurck nonlinearity** as a map of spectral Sobolev
spaces

  `N : tensorHs g_bg 0 2 ((a : ℝ) + 1) → tensorHs g_bg 0 2 (a : ℝ)`.

On a finitely-supported, fibre-small `u`, `N(u)` is the order-`a` spectral
element whose eigenbasis coordinates are the `L²` coordinates of the geometric
remainder section `deTurckRemainderSection g_bg u`
(`= deTurckRHSSection g_bg (g_bg + h_sym(u)) − Δ_∇ T_u`).  The weighted
square-summability witness placing these coordinates in `Hᵃ` is supplied by the
spectral-scale summability of a smooth compactly-supported tensor
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at every real order).
Off the validity domain `N(u) = 0`. -/
def deTurckGeometricN (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1)) :
    tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) g_bg)
      (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g_bg
      (a : ℝ) (deTurckRemainderSection (I := I) g_bg u) (hCompact (I := I) g_bg)

/-- The eigenbasis coordinate of `deTurckGeometricN g_bg a u` is the `L²`
coordinate of the geometric remainder section. -/
@[simp] theorem deTurckGeometricN_coeff (g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g_bg 0 2) :
    (deTurckGeometricN (I := I) g_bg a u).coeff i =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) g_bg)
        (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)) i :=
  rfl

/-- Off the validity domain, the geometric nonlinearity vanishes. -/
theorem deTurckGeometricN_of_not_realizable (g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hu : ¬ realizableAt (I := I) g_bg u) :
    deTurckGeometricN (I := I) g_bg a u = 0 := by
  classical
  have hsec : deTurckRemainderSection (I := I) g_bg u = 0 := by
    rw [deTurckRemainderSection, dif_neg hu]
  apply tensorHs.ext (I := I) (M := M)
  funext i
  rw [deTurckGeometricN_coeff, hsec,
    show SmoothCcTensor.toL2 (g := g_bg) (r := 0) (s := 2)
        (0 : SmoothCcTensor g_bg 0 2) = 0 from map_zero _,
    tensorL2Coeff_eq_inner, inner_zero_right]
  rfl

/-! ## Joint `(x, t)`-smoothness of the geometric Ricci–DeTurck right-hand side along the
realized metric family

The Amann/Picard strong-existence route for the realized nonlinearity needs the geometric
Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg (g₀ + h(F t)) = −2·Ric(g₀ + h(F t)) + 𝓛_{deTurckVF(g₀ + h(F t), g_bg)}(g₀ + h(F t))`
to depend *jointly* `C^∞` on the base point and the time parameter, for the realized metric
family `realizedFam g₀ T T' t` (the convex realization path `t ↦ g₀ + h(convexPerturbation T T' t)`).

This is assembled, chart-locality-free, from the joint chart-Gram smoothness tower of the
realized family (`RicciLinearization.gen_joint_chartDeTurckRicciRHS` over
`realizedFam_genJointGram_free`): the chart-coordinate inverse Gram (Cramer), Christoffel symbols
(first chart partials), Riemann/Ricci curvature (`∂Γ + Γ·Γ`), DeTurck vector field and its Lie
derivative are each finite chart polynomials of the chart-Gram entries, jointly `C^∞` once the
chart-Gram entries are.  The chart scalar `chartDeTurckRicciRHS` is grounded against the intrinsic
operator by `deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS`, and the bundle section is
read off the multilinear-basis coordinates through the chart-center trivialization. -/

section JointSmoothness

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear Tensor0SBundle

/-- The chart-`α`-pushforward frame vector `(triv α).symmL ℝ x (chartModelBasis E i)` equals the
chart-basis fibre `chartBasisVecFiber α i x` (the `symmL`/`symm` agreement on the trivialization). -/
private lemma chartFrameVec_eq_chartBasisVecFiber_helper (α : M)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)
      = chartBasisVecFiber (I := I) α i x := by
  rw [chartBasisVecFiber, Trivialization.symmL_apply]

/-- **Joint `(x, t)`-smoothness of the chart-coordinate DeTurck–Ricci right-hand side along the
realized family.**  On the chart-`α` source × the realized small set, the chart scalar
`(x, t) ↦ chartDeTurckRicciRHS (realizedFam g₀ T T' t) g_bg α i k (ϕ_α x)` is jointly `C^∞`.

The DeTurck-arm mirror of `RicciLinearization.realizedFam_chartRicciTensor_jointContMDiffOn`:
the chart Euclidean joint smoothness `RicciLinearization.gen_joint_chartDeTurckRicciRHS` (over the
δ-free joint Gram `realizedFam_genJointGram_free`), threaded through the smooth moving point
`(x, t) ↦ (t, ϕ_α x)`. -/
theorem realizedFam_chartDeTurckRicciRHS_jointContMDiffOn
    (g_bg g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α i k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_chartDeTurckRicciRHS (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG g_bg i k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α i k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
/-- **C1 — joint `(x, t)`-smoothness of the geometric Ricci–DeTurck right-hand side field along
the realized metric family.**  As a section of the `(0, 2)`-tensor bundle over `M × ℝ`,
`(x, t) ↦ deTurckRHSField g_bg (realizedFam g₀ T T' t) x` is jointly `C^∞` on the slab
`univ ×ˢ realizedSmallSet` (the realized family is junk-extended to `g₀` off the small set, so the
joint smoothness holds on the open parameter set containing the integration interval, not globally
in `t`).

The geometric nonlinearity keystone: it lifts the chart-scalar joint smoothness
`realizedFam_chartDeTurckRicciRHS_jointContMDiffOn` to the intrinsic bundle section.  Worked
pointwise through `Bundle.contMDiffWithinAt_totalSpace` at the moving chart-center trivialization
`α = p₀.1`: the trivialized fibre coordinate is reconstructed from its multilinear-basis
coordinates (`continuousMultilinearMap_basis`/`equivFun.symm`), each coordinate being the chart
scalar `deTurckRicciRHS g_bg (g_t) x (e_{σ 0}, e_{σ 1}) = chartDeTurckRicciRHS (g_t) g_bg α (σ 0)
(σ 1) (ϕ_α x)` (the chart read-off `deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS` on
the Levi-Civita good set), jointly `C^∞` by the chart-scalar lemma. -/
theorem deTurckRHSField_realizeMetric_jointContMDiffOn
    (g_bg g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨_, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hinter]
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set α : M := p₀.1 with hα
  set Bb := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBb
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  have hcoord : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => Bb.repr
          (e ⟨p.1, deTurckRHSField (I := I) g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2 σ)
        ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := by
    intro σ
    have hP1 := realizedFam_chartDeTurckRicciRHS_jointContMDiffOn (I := I) g_bg g₀ T T' hδ hδ'
      α (σ 0) (σ 1)
    have hp₀_in_α : p₀ ∈ (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') := by
      refine ⟨?_, hp₀.2⟩
      rw [hα]; exact mem_chart_source H p₀.1
    have hP1at : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => chartDeTurckRicciRHS (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α (σ 0) (σ 1) (extChartAt I α p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := hP1 p₀ hp₀_in_α
    have hαsrc_nhd : ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∈
        nhdsWithin p₀ ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have h := inter_mem_nhdsWithin
        ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))
        (((chartAt H α).open_source.prod realizedSmallSet_isOpen).mem_nhds hp₀_in_α)
      refine Filter.mem_of_superset h ?_
      intro q hq; exact hq.2
    refine (hP1at.mono_of_mem_nhdsWithin hαsrc_nhd).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hαsrc_nhd] with p hp
      obtain ⟨hpx, hps⟩ := hp
      have hpgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
        rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
        exact hpx
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ p.1
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      rw [chartFrameVec_eq_chartBasisVecFiber_helper,
        chartFrameVec_eq_chartBasisVecFiber_helper]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α (σ 0) (σ 1) hpgood]
    · have hpgood : p₀.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
        rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
        rw [hα]; exact mem_chart_source H p₀.1
      rw [continuousMultilinearMap_basis_repr]
      rw [trivializationAt_tensor0SBundle_succ_fibre]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change Tensor0SBundle.Tensor0SSpace.toModel
          (deTurckRHSField (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) p₀.1)
          (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ p₀.1
            ((chartModelBasis E) (σ i))) = _
      rw [deTurckRHSField_toModel_apply]
      rw [chartFrameVec_eq_chartBasisVecFiber_helper,
        chartFrameVec_eq_chartBasisVecFiber_helper]
      rw [deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) g_bg α (σ 0) (σ 1) hpgood]
  have hpi : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => (Bb.repr
        (e ⟨p.1, deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2 :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ))
      ((chartAt H x₀).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ :=
    contMDiffWithinAt_pi_space.2 (fun σ => hcoord σ)
  have hsymm : ContMDiff 𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ)
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun c : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ => Bb.equivFun.symm c) :=
    (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  refine (hsymm.contMDiffAt.comp_contMDiffWithinAt p₀ hpi).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p _
    simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨p.1, deTurckRHSField (I := I) g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨p.1, deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm
  · simp only [Function.comp_apply]
    rw [show ((Bb.repr (e ⟨p₀.1, deTurckRHSField (I := I) g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) p₀.1⟩).2) :
          (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) =
        Bb.equivFun (e ⟨p₀.1, deTurckRHSField (I := I) g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' p₀.2) p₀.1⟩).2 from
        (Bb.equivFun_apply _).symm]
    exact (Bb.equivFun.symm_apply_apply _).symm

end JointSmoothness

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
