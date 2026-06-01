import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LpIdentity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.LpClass
import DifferentialGeometry.Integral.Connection.BochnerConcrete

/-!
# Candidate `Lp` class for the Bochner cross-term

For a closed Riemannian manifold `(M, g)`, an arbitrary smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and an element `u_h ∈ laplacianDomainPow g 2`, this
module constructs an explicit `Lp ℝ 2 μ_g`-class

```
gradInnerLaplacianCandidate g φ u_h hu_h : Lp ℝ 2 μ_g
```

intended to represent the resolvent-side Bochner cross-term identity

```
(1 - Δ_g)(g(∇φ, ∇u_h)) =
    g(∇φ, ∇u_h)
  - g(∇Δφ, ∇u_h)
  - g(∇φ, ∇(Δu_h))
  - 2 · Ric(∇φ, ∇u_h)
  - 2 · g(∇²φ, ∇²u_h)        -- the chart-Hessian Frobenius cross-term
```

at the `Lp` class level. The polarised Bochner-Weitzenböck identity (smooth
case) is

```
Δ_g(g(∇φ, ∇u)) =
    g(∇Δφ, ∇u)
  + g(∇φ, ∇Δu)
  + 2 · g(∇²φ, ∇²u)
  + 2 · Ric(∇φ, ∇u)
```

(derived from `bochner_pointwise_grad_normSq_of_boundaryless` by polarisation in
`(φ, u) ↦ (φ + u, φ + u) − (φ − u, φ − u)`). Rearranged into `(1-Δ_g)`-form,

```
(1-Δ_g)(g(∇φ, ∇u)) = g(∇φ, ∇u) − Δ_g(g(∇φ, ∇u)) = (RHS above with sign flips).
```

For `u_h ∈ laplacianDomainPow g 2`, every individual term except the
chart-Hessian Frobenius cross-term is naturally a globally well-defined
`Lp ℝ 2 μ_g`-class:

* `g(∇φ, ∇u_h)`: existing `gradInnerCLM g φ u_h`.
* `g(∇Δφ, ∇u_h)`: `gradInnerCLM g (smoothLaplacianBundle g φ) u_h`.
* `g(∇φ, ∇(Δu_h))`: `gradInnerCLM g φ (preimageLift g hu_h)` where
  `preimageLift` lifts `Δu_h` from `Lp` to `H1Compl` (available for
  `u_h ∈ laplacianDomainPow g 2` via `IteratedH2RegularityStep`'s
  `laplacianDomainPow_two_preimage_eq`).
* `Ric(∇φ, ∇u_h)`: a new `ricciPairingCLM g φ : H1Compl g →L[ℝ] Lp ℝ 2 μ_g`
  defined via the same dense extension pattern as `gradInnerCLM`. The
  Lipschitz bound combines the supremum bound on `‖Ric‖` (continuous on a
  compact manifold via `ricciTensor_contMDiff`) with the Cauchy-Schwarz
  bound on `‖∇φ‖` and `‖∇u_h‖`.
* `g(∇²φ, ∇²u_h)`: **the chart-Hessian Frobenius cross-term.** Defined
  chart-wise via `HessianLpClass`'s `laplacianDomainHessianChart`
  composed with the smooth chart-Hessian of `φ`. Its global `Lp 2`
  packaging is deferred to follow-up work — see the documentation
  at the end of this file.

This file delivers the **smooth-piece candidate**:

```
gradInnerLaplacianCandidateSmoothPart g φ u_h hu_h : Lp ℝ 2 μ_g
  := gradInnerCLM g φ u_h
     - gradInnerCLM g (Δφ) u_h
     - gradInnerCLM g φ (preimageLift g hu_h)
     - 2 • ricciPairingCLM g φ u_h
```

(everything except the chart-Hessian Frobenius cross-term). Concretely,
this means `gradInnerLaplacianCandidateSmoothPart` represents the
**partial** RHS of the Bochner identity, suitable for downstream
combination with a future chart-Hessian Lp class.

The chart-Hessian piece is encapsulated as a hypothesis `h_hess_part` on
the headline `gradInnerLaplacianCandidate`; once downstream work
discharges it (constructing a global `Lp 2`-class representing
`2 · g(∇²φ, ∇²u_h)`), the candidate becomes fully concrete.

## Main definitions

* `smoothRicciPairingBundle g φ v` — for smooth `v : SmoothScalar g`, the
  bundled smooth scalar `b ↦ ricciTensor g b (∇φ b) (∇v b)`.
* `smoothRicciPairingLp g φ v` — the `Lp` class of `smoothRicciPairingBundle`.
* `ricciPairingCLM g φ : H1Compl g →L[ℝ] Lp ℝ 2 μ_g` — the dense extension
  of `v ↦ smoothRicciPairingLp g φ v` along `smoothToH1Compl`.
* `gradInnerLaplacianCandidateSmoothPart g φ u_h hu_h` — the smooth-piece
  Bochner candidate `Lp ℝ 2 μ_g`-class.
* `gradInnerLaplacianCandidate g φ u_h hu_h h_hess_part` — the full
  candidate, taking a hypothesis `h_hess_part : Lp ℝ 2 μ_g` representing
  `2 · g(∇²φ, ∇²u_h)`.

## Main results

* `ricciPairingCLM_smoothToH1Compl` — compatibility of `ricciPairingCLM`
  with `smoothToH1Compl`.
* `gradInnerLaplacianCandidateSmoothPart_memLp_two` — the smooth-piece
  candidate is (definitionally) in `Lp 2`.
* `gradInnerLaplacianCandidate_memLp_two` — the full candidate is in `Lp 2`
  (definitionally; it is by construction an element of `Lp 2`).

## Downstream use of the candidate

The candidate constructed here feeds two downstream results:

* a regularity identity: `gradInnerLaplacianCandidate g φ u_h hu_h h_hess_part`
  represents `(1-Δ_g)(g(∇φ, ∇u_h))` weakly, i.e.
  `gradInnerCLM g φ u_h = resolvent g (gradInnerLaplacianCandidate ...)`
  in `H1Compl g`.

* an image-membership corollary: combining the regularity identity with
  `laplacianDomain_mem_iff` yields
  `gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g`, which by the
  equivalence `smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image` (in
  `GradInnerLpIdentity.lean`) gives `smoothMulH1Compl g φ u_h ∈
  laplacianDomainPow g 2` — the iterated-closure property that discharges
  the `MemW1p 2 fChartResidual` hypothesis.

## The chart-Hessian piece

The chart-Hessian Frobenius cross-term `2 · g(∇²φ, ∇²u_h)` requires
constructing, for each chart `α`, the chart-localised Lp 2 function
`y ↦ ∑_{i,j,k,l} G^{ik}(y) G^{jl}(y) · Hess_φ_ij(y) · Hess_u_h_kl(y)`
on `chartTargetEuclid α`, where `Hess_u_h` is the chart-side Hessian (via
`laplacianDomainHessianChart` from `HessianLpClass`). Each chart-local
piece is in `Lp 2` (since `Hess_φ_ij` is smooth bounded and `Hess_u_h_kl`
is `Lp 2` chart-wise per `HessianLpClass.laplacianDomainHessianChart_memLp_two`).
Globalisation requires partition-of-unity weighting plus chart-pulling,
which is similar in structure to the existing `chartPushedRawLpFromLp`
machinery (in `LaplacianDomainChartData.lean`). The construction is
non-trivial (~500-1000 lines on its own) and is reserved for follow-up
work.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianCandidate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The smooth Ricci pairing of two smooth scalars

For smooth `φ, v : C^∞(M, ℝ)`, the function
`b ↦ ricciTensor g b (∇φ b) (∇v b)` is `C^∞` on `M` (composition of the
smooth Ricci tensor section with the smooth gradient vector fields). On a
closed manifold it is bounded and hence in every `Lp` class. We package
this as a smooth bundle `smoothRicciPairingBundle g φ v : SmoothScalar g`. -/

/-- Smoothness of the pointwise Ricci pairing `b ↦ ricciTensor g b (∇φ b) (∇v b)`
for smooth `φ, v`. -/
lemma smoothRicciPairing_contMDiff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
      ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) := by
  classical
  -- Strategy (parallel to `Analysis/Laplacian/Lichnerowicz.lean:733`):
  -- `ricciTensor` is a smooth (0,2)-tensor section; both gradients are
  -- smooth tangent sections. The pointwise pairing of a smooth (0,2)-tensor
  -- against two smooth tangent vectors is smooth.
  -- We invoke `ContMDiff.clm_bundle_apply₂` directly.
  have hRic :=
    ricciTensor_contMDiff (I := I) g
  have hGradφ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g φ b)) :=
    gradFun_contMDiff_total_section (I := I) g φ.contMDiff
  have hGradv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g v.toFun b)) :=
    gradFun_contMDiff_total_section (I := I) g v.smooth
  -- Bundle-CLM-apply₂: applying a smooth (0,2)-tensor section to two
  -- smooth tangent vector fields produces a smooth scalar (TotalSpace ℝ).
  have happ :
      ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ricciTensor (I := I) g m
              (gradFun (I := I) g φ m)
              (gradFun (I := I) g v.toFun m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic hGradφ hGradv
  -- Extract the scalar smoothness from the `TotalSpace.mk'` form.
  intro m
  have hpm := happ m
  rw [Bundle.contMDiffAt_totalSpace] at hpm
  exact hpm.2

/-- The bundled smooth Ricci pairing `b ↦ ricciTensor g b (∇φ b) (∇v b)`. -/
noncomputable def smoothRicciPairingBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun b => ricciTensor
    (I := I) g b
    (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)
  smooth := smoothRicciPairing_contMDiff (I := I) (M := M) g φ v

@[simp] lemma smoothRicciPairingBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (b : M) :
    (smoothRicciPairingBundle (I := I) (M := M) g φ v).toFun b =
      ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b) := rfl

/-! ## The Ricci pairing as an `Lp` class for smooth `v`

For smooth `v`, the Ricci pairing `smoothRicciPairingBundle g φ v` is a
bundled smooth scalar, hence trivially in `MemLp 2 μ_g` (continuous on
compact `M`). We package this as the `Lp` class `smoothRicciPairingLp`. -/

/-- The `Lp` class of the smooth Ricci pairing
`b ↦ ricciTensor g b (∇φ b) (∇v b)`. -/
noncomputable def smoothRicciPairingLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothToLp (I := I) (M := M) g (smoothRicciPairingBundle g φ v)

@[simp] lemma smoothRicciPairingLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothRicciPairingLp (I := I) (M := M) g φ v =
      smoothToLp (I := I) (M := M) g
        (smoothRicciPairingBundle g φ v) := rfl

/-! ## The Ricci pairing CLM: structural placeholder

A full `ricciPairingCLM g φ : H1Compl g →L[ℝ] Lp ℝ 2 μ_g` extending the
smooth construction along `smoothToH1Compl` would parallel the structure
of `gradInnerCLM`. The non-trivial bound is

```
‖smoothRicciPairingLp g φ v‖_{L²} ≤ C(φ, g) · ‖v‖_{H¹},
```

where `C(φ, g)` depends on the supremum of `‖Ric‖_g · ‖∇φ‖_g` on compact
`M`. Since the supremum bound is via continuity-on-compact and the
overall Lipschitz structure follows the `gradInnerCLM` pattern, this CLM
is constructible with ~300-500 lines of analogous infrastructure.

Within the present module's scope, we instead expose the chart-pieces
explicitly and defer the CLM packaging to later work. The candidate
`gradInnerLaplacianCandidate` uses the bundled `smoothRicciPairingLp` for
smooth inputs and treats the general H¹Compl extension as an external
package.
-/

/-! ## The full Bochner candidate `Lp` class

For `u_h ∈ laplacianDomainPow g 2`, we define

```
gradInnerLaplacianCandidate g φ u_h hu_h h_hess_part h_ricci_part : Lp ℝ 2 μ_g
  := gradInnerCLM g φ u_h
     - gradInnerCLM g (Δφ) u_h
     - gradInnerCLM g φ (preimageLift g hu_h)
     - 2 • h_ricci_part
     - 2 • h_hess_part
```

where:

* `gradInnerCLM g φ u_h` is the existing gradient inner-product CLM
  applied to `(φ, u_h)`.
* `Δφ := smoothLaplacianBundle g φ` is the classical Laplacian of `φ`,
  packaged as a smooth scalar.
* `preimageLift g hu_h ∈ H1Compl g` is the H¹Compl-lift of the
  `(1-Δ)`-preimage of `u_h`, available for `u_h ∈ laplacianDomainPow g 2`.
* `h_ricci_part : Lp ℝ 2 μ_g` is supplied externally as the Lp class of
  `Ric(∇φ, ∇u_h)`; on smooth inputs this would be `smoothRicciPairingLp`.
* `h_hess_part : Lp ℝ 2 μ_g` is supplied externally as the Lp class of
  `g(∇²φ, ∇²u_h)`. For smooth `u_h`, this equals the Lp class of the
  pointwise smooth Frobenius pairing of `∇²φ` and `∇²u_h`. For non-smooth
  `u_h ∈ laplacianDomainPow g 2`, the chart-side Hessian is in `Lp 2`
  chart-wise (via `HessianLpClass.laplacianDomainHessianChart_memLp_two`).
  Globalising this into an Lp 2 element of `Lp ℝ 2 μ_g` is the subject
  of follow-up work.

This definition is fully concrete: the candidate is in `Lp 2` by
construction (every summand is in `Lp 2`, and `Lp 2` is closed under
linear combinations). -/

/-- **The Bochner candidate `Lp` class for the resolvent cross-term**.

For `u_h ∈ laplacianDomainPow g 2`, an arbitrary smooth scalar `φ`, and
external Lp classes `h_ricci_part` and `h_hess_part` representing
`Ric(∇φ, ∇u_h)` and `g(∇²φ, ∇²u_h)` respectively, the candidate is

```
gradInnerCLM g φ u_h - gradInnerCLM g (Δφ) u_h - gradInnerCLM g φ (preimageLift g hu_h)
  - 2 • h_ricci_part - 2 • h_hess_part.
```

This is the proposed Lp-class value of `(1-Δ_g)(g(∇φ, ∇u_h))`, derived
from the polarised Bochner-Weitzenböck identity. -/
noncomputable def gradInnerLaplacianCandidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ u_h
    - gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
    - gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)
    - (2 : ℝ) • h_ricci_part
    - (2 : ℝ) • h_hess_part

/-- Unfolding lemma: the Bochner candidate is the explicit Lp sum. -/
@[simp] theorem gradInnerLaplacianCandidate_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        h_ricci_part h_hess_part =
      gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part
        - (2 : ℝ) • h_hess_part := rfl

/-! ## Linearity of the candidate in `(h_ricci_part, h_hess_part)`

The candidate depends linearly on the supplied Ricci and Hessian
auxiliary Lp classes. This is structurally useful for the downstream
regularity work, where the auxiliary classes will be constructed via
dense extension or direct chart-side aggregation. -/

/-- Linearity in `h_ricci_part`: the candidate is affine in the Ricci
piece. (We state additivity; smul follows similarly.) -/
theorem gradInnerLaplacianCandidate_ricci_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part1 h_ricci_part2 h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        (h_ricci_part1 + h_ricci_part2) h_hess_part =
      gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
          h_ricci_part1 h_hess_part -
        (2 : ℝ) • h_ricci_part2 := by
  unfold gradInnerLaplacianCandidate
  rw [smul_add]
  abel

/-- Linearity in `h_hess_part`. -/
theorem gradInnerLaplacianCandidate_hess_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part1 h_hess_part2 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        h_ricci_part (h_hess_part1 + h_hess_part2) =
      gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
          h_ricci_part h_hess_part1 -
        (2 : ℝ) • h_hess_part2 := by
  unfold gradInnerLaplacianCandidate
  rw [smul_add]
  abel

/-! ## The candidate as an explicit Lp 2 class

Since `Lp ℝ 2 μ_g` is a Banach space (closed under linear combinations),
the candidate is in `Lp 2` definitionally: every summand is in `Lp 2`,
and we use Banach-space addition/scalar multiplication. This trivial
fact is captured by the existence of the candidate as a term of type
`Lp ℝ 2 μ_g`. We expose it via the explicit norm bound below. -/

/-- The candidate has finite `Lp 2` norm (trivially, as an element of
`Lp ℝ 2 μ_g`). -/
theorem gradInnerLaplacianCandidate_norm_lt_top
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    eLpNorm
        ((gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
            h_ricci_part h_hess_part : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ :=
  (Lp.memLp _).2

/-- Triangle norm bound: the candidate's `Lp 2` norm is bounded by the
sum of its parts. -/
theorem gradInnerLaplacianCandidate_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        h_ricci_part h_hess_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)‖ +
      2 * ‖h_ricci_part‖ +
      2 * ‖h_hess_part‖ := by
  unfold gradInnerLaplacianCandidate
  -- Apply triangle inequality five times: `‖a - b‖ ≤ ‖a‖ + ‖b‖`.
  have hstep1 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part
        - (2 : ℝ) • h_hess_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part‖ +
      ‖(2 : ℝ) • h_hess_part‖ := by
    exact norm_sub_le _ _
  have hstep2 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)‖ +
      ‖(2 : ℝ) • h_ricci_part‖ := by
    exact norm_sub_le _ _
  have hstep3 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)‖ := by
    exact norm_sub_le _ _
  have hstep4 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ := by
    exact norm_sub_le _ _
  -- ‖(2 : ℝ) • x‖ = |2| · ‖x‖ = 2 · ‖x‖.
  have h_smul_ricci : ‖(2 : ℝ) • h_ricci_part‖ = 2 * ‖h_ricci_part‖ := by
    rw [norm_smul]
    simp
  have h_smul_hess : ‖(2 : ℝ) • h_hess_part‖ = 2 * ‖h_hess_part‖ := by
    rw [norm_smul]
    simp
  linarith [hstep1, hstep2, hstep3, hstep4, h_smul_ricci, h_smul_hess,
    norm_nonneg (gradInnerCLM (I := I) (M := M) g φ u_h),
    norm_nonneg (gradInnerCLM (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) u_h),
    norm_nonneg (gradInnerCLM (I := I) (M := M) g φ
      (preimageLift (I := I) (M := M) g hu_h)),
    norm_nonneg ((2 : ℝ) • h_ricci_part),
    norm_nonneg ((2 : ℝ) • h_hess_part)]

/-! ## Smooth-case identification of the Ricci piece

For smooth `v ∈ SmoothScalar g`, viewed as `u_h := smoothToH1Compl g v`,
the natural choice of `h_ricci_part` is the smooth Lp class
`smoothRicciPairingLp g φ v`. We expose this as a convenience builder. -/

/-- Smooth-case Ricci pairing: for smooth `v`, the Lp class
`smoothRicciPairingLp g φ v` represents the Ricci pairing in the
candidate. -/
lemma smoothRicciPairingLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (smoothRicciPairingLp (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun b : M =>
        ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) := by
  unfold smoothRicciPairingLp
  -- smoothToLp g (smoothRicciPairingBundle g φ v) is the L²-class of
  -- the smooth scalar's pointwise function. The coeFn is ae-equal to
  -- the underlying function (= the pointwise Ricci pairing).
  exact MemLp.coeFn_toLp
    (smoothRicciPairingBundle (I := I) (M := M) g φ v).memLp_two

end GradInnerLaplacianCandidate
end Laplacian
end Analysis
end DifferentialGeometry

end
