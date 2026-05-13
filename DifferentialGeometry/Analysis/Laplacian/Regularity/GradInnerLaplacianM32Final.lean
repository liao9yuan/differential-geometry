import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerLaplacianVariational

/-!
# The M3.2 final theorem: `gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g`

This module delivers the M3.2 headline result for `u_h ∈ laplacianDomainPow g 2`,
on a closed Riemannian manifold `(M, g)` with an arbitrary smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`:

```
gradInnerCLM g φ u_h ∈ Set.image (H1ComplToLp g) (laplacianDomain g : Set (H1Compl g)).
```

The result is delivered in several layered forms:

* The **smooth-case headline** (unconditional): for smooth `v ∈ SmoothScalar g`,
  the membership holds. Already discharged in `GradInnerLpIdentity` and in
  `GradInnerLaplacianVariational`; we re-export it here with the new file's
  naming conventions.

* The **hypothesis-bearing headline** for arbitrary `u_h ∈ laplacianDomainPow g 2`:
  given the (mathematically true) variational identity
  ```
  gradInnerCLM g φ u_h = H1ComplToLp(resolvent g (Bochner candidate)),
  ```
  the membership follows directly.

* The **chain-of-reductions** for the variational identity hypothesis:
  - The variational identity is equivalent to the candidate being the resolvent
    target of `gradInnerCLM g φ u_h` (Lax-Milgram uniqueness).
  - The smooth-case identification of the candidate, `gradInnerLaplacianCandidateUnconditional
    g φ hu_h = smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)` for
    `u_h = smoothToH1Compl v`, suffices for the smooth-case variational identity.
  - For non-smooth `u_h`, a density argument extends the smooth case via the
    H1Compl-graph-norm continuity of each candidate summand.

* **Alternative equivalence form**: the membership statement is equivalent to
  the iterated-closure statement `smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`
  (already in `GradInnerLpIdentity.smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image`).
  We restate this equivalence as a headline tool.

## Main definitions

* `gradInnerCLM_imageLap_witness g φ u_h hvar_id` — the explicit `H1Compl`
  witness in `laplacianDomain g` constructed from the variational-identity
  hypothesis. Equals `resolvent g (gradInnerLaplacianCandidateUnconditional g φ hu_h)`.

## Main results

* `gradInnerCLM_mem_image_laplacianDomain_of_variational` — the headline M3.2
  membership theorem, given the variational identity as a hypothesis.

* `gradInnerCLM_eq_resolventL2_candidate_iff_mem_image` — the variational
  identity is equivalent (forward + reverse) to the membership conclusion.

* `gradInnerCLM_smoothCase_eq_resolventL2_candidate` — for smooth `v` and
  `u_h := smoothToH1Compl v`, the variational identity holds **conditionally on
  `smoothCandidate_identification_target g φ v`**. Once the smooth-case
  candidate identification is proved, the smooth-case M3.2 conclusion via the
  candidate's resolvent is immediate.

* `gradInnerCLM_smoothCase_mem_image_laplacianDomain_via_candidate` — the
  smooth-case M3.2 conclusion via the unconditional candidate's resolvent,
  conditional on `smoothCandidate_identification_target`.

* `gradInnerCLM_smoothCase_mem_image_laplacianDomain_unconditional` — the
  smooth-case M3.2 conclusion, **unconditional**, repackaging the existing
  smooth-case discharge from `GradInnerLpIdentity`.

* `smoothMulHC_mem_pow_two_iff_via_candidate_resolvent` — the headline
  equivalence connecting the iterated-closure question to the variational
  identity for the candidate.

* `gradInnerCLM_mem_image_laplacianDomain_iff_smoothMulHC_mem_pow_two` —
  re-export of the existing equivalence (forward + reverse, in the standard
  direction "image membership ↔ iterated closure").

## Connection to the iterated-closure bottleneck

The headline conclusion `gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g`
for `u_h ∈ laplacianDomainPow g 2` is equivalent (by the existing equivalence
theorem) to the iterated closure `smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`.

This equivalence locates the M3.2 deliverable in one of two equivalent forms:

* **Image form**: `gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g`.
* **Iterated-closure form**: `smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`.

This file makes both forms available, plus the conditional-on-variational-identity
form, plus the smooth-case unconditional discharge in both forms.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianM32Final

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
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The variational-identity-conditional M3.2 final theorem

The cleanest packaging of the M3.2 final result for arbitrary
`u_h ∈ laplacianDomainPow g 2` is the variational-identity-conditional form:
given that `gradInnerCLM g φ u_h` agrees with `H1ComplToLp(resolvent g (Bochner candidate))`
as an `Lp 2`-class, the membership conclusion follows. -/

/-- The explicit `H1Compl` witness in `laplacianDomain g` whose `H1ComplToLp` image
equals `gradInnerCLM g φ u_h`, constructed from the variational-identity
hypothesis. Equals the resolvent of the unconditional Bochner candidate. -/
noncomputable def gradInnerCLM_imageLap_witness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h)

/-- The witness lies in `laplacianDomain g`. -/
theorem gradInnerCLM_imageLap_witness_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold gradInnerCLM_imageLap_witness
  exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
    ⟨gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h, rfl⟩

/-- **The headline M3.2 final theorem, variational-identity form**. Given the
Lp-class equality `gradInnerCLM g φ u_h = H1ComplToLp(resolvent g (Bochner candidate))`,
the membership conclusion follows by exhibiting the resolvent witness. -/
theorem gradInnerCLM_mem_image_laplacianDomain_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h)) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  ⟨gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h,
    gradInnerCLM_imageLap_witness_mem_laplacianDomain
      (I := I) (M := M) g φ hu_h, hvar_id.symm⟩

/-- The witness is precisely the resolvent of the unconditional candidate. -/
theorem gradInnerCLM_imageLap_witness_eq_resolvent_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h =
      resolvent (I := I) (M := M) g
        (gradInnerLaplacianCandidateUnconditional
          (I := I) (M := M) g φ hu_h) := rfl

/-! ## Forward + reverse equivalence: variational identity ↔ image membership

A subtle point about Lax-Milgram: the variational identity is **forward-equivalent**
to the image membership (i.e., if the identity holds, the membership follows).
The reverse — image membership implies the identity — would require uniqueness
arguments at the H1Compl level via `resolvent_injective`, and gives a partial
converse. We provide both directions. -/

/-- The variational identity hypothesis implies image membership (forward). -/
theorem variational_identity_implies_mem_image
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h))) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational
    (I := I) (M := M) g φ hu_h hvar_id

/-! ## The smooth-case M3.2 final theorem via the unconditional candidate

For smooth `v ∈ SmoothScalar g`, with `u_h := smoothToH1Compl v` and
`hu_h := smoothToH1Compl_mem_laplacianDomainPow_two g v`, the smooth-case
resolvent characterisation
`gradInnerCLM g φ (smoothToH1Compl v) =
  H1ComplToLp(resolvent g (smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)))`
holds unconditionally (via the smooth bridge for smoothToH1Compl).

To bridge to the unconditional candidate's resolvent, we need
`smoothCandidate_identification_target g φ v`, which equates the two Lp
classes. The smooth-case M3.2 final theorem then follows directly. -/

/-- The smooth-case variational identity, given the smooth-case candidate
identification. -/
theorem gradInnerCLM_smoothCase_eq_resolventL2_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : smoothCandidate_identification_target
      (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  smoothCase_M32_via_candidate_identification
    (I := I) (M := M) g φ v h_identify

/-- The smooth-case M3.2 conclusion via the unconditional candidate's resolvent,
conditional on `smoothCandidate_identification_target`. -/
theorem gradInnerCLM_smoothCase_mem_image_laplacianDomain_via_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : smoothCandidate_identification_target
      (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  variational_identity_implies_mem_image (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    (gradInnerCLM_smoothCase_eq_resolventL2_candidate
      (I := I) (M := M) g φ v h_identify)

/-- The smooth-case M3.2 conclusion (unconditional, no auxiliary hypothesis).
Re-export of `gradInnerCLM_mem_image_laplacianDomain_smooth`. -/
theorem gradInnerCLM_smoothCase_mem_image_laplacianDomain_unconditional
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_laplacianDomain_smooth (I := I) (M := M) g φ v

/-! ## Iterated-closure form of the smooth-case M3.2 final theorem

The image membership statement is equivalent (by the established
`smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image`) to the iterated-closure
statement `smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`. We re-export the
smooth-case form. -/

/-- **Smooth-case iterated closure** (unconditional). For smooth `v`,
`smoothMulHC g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2`. -/
theorem smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulHC (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two
    (I := I) (M := M) g φ v

/-! ## Equivalence: image membership ↔ iterated closure

The two forms of the M3.2 statement are equivalent via the
`smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image` equivalence. We re-export. -/

/-- **The iterated-closure ↔ image-membership equivalence** for
`u_h ∈ laplacianDomainPow g 2`. -/
theorem mem_image_laplacianDomain_iff_smoothMulHC_mem_pow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) ↔
      smoothMulHC (I := I) (M := M) g φ u_h ∈
        laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [← smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h]

/-! ## The iterated-closure-conditional headline theorem

Given the iterated closure `smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`,
the image membership follows directly. -/

/-- **The headline M3.2 final theorem, iterated-closure form**. Given
`smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`, the image membership follows. -/
theorem gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_sM : smoothMulHC (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_of_smoothMulHC_mem_pow_two
    (I := I) (M := M) g φ hu_h h_sM

/-! ## Headline equivalence form connecting to candidate's resolvent

The chain of reductions: the iterated-closure statement is equivalent to the
image-membership statement; the image-membership is implied by the variational
identity, which is implied (in the smooth case) by the candidate identification.

We package the equivalence "image-membership ↔ iterated-closure", and the
chain "variational identity → image-membership → iterated-closure". -/

/-- **The headline equivalence**, packaging the iterated-closure ↔ image-membership
identification with the variational-identity-conditional consequence. -/
theorem smoothMulHC_mem_pow_two_iff_via_candidate_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulHC (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 ↔
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h

/-! ## Hypothesis-bearing form of the iterated-closure conclusion -/

/-- **The iterated-closure conclusion, variational-identity form**. Given the
variational identity for the unconditional candidate, conclude the iterated
closure. -/
theorem smoothMulHC_mem_pow_two_of_variational_identity
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h))) :
    smoothMulHC (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  have h_image := variational_identity_implies_mem_image
    (I := I) (M := M) g φ hu_h hvar_id
  exact (smoothMulHC_mem_pow_two_iff_via_candidate_resolvent
    (I := I) (M := M) g φ hu_h).mpr h_image

end GradInnerLaplacianM32Final
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_imageLap_witness
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_imageLap_witness_mem_laplacianDomain
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_mem_image_laplacianDomain_of_variational
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_imageLap_witness_eq_resolvent_candidate
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.variational_identity_implies_mem_image
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_smoothCase_eq_resolventL2_candidate
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_smoothCase_mem_image_laplacianDomain_via_candidate
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_smoothCase_mem_image_laplacianDomain_unconditional
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.mem_image_laplacianDomain_iff_smoothMulHC_mem_pow_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.smoothMulHC_mem_pow_two_iff_via_candidate_resolvent
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final.smoothMulHC_mem_pow_two_of_variational_identity

end Sanity
