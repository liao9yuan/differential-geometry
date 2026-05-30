import DifferentialGeometry.Analysis.ODE.FlowCk

/-!
# Parametric `C^k` smoothness of the variational linear map

The previous file `FlowCk.lean` reduced the `C^k` flow problem to the joint `C^j`
smoothness of the *spatial piece* `Lsp(x, t) ∈ E →L[ℝ] E` of the joint Fréchet derivative
`D Φ`.  Pointwise, `Lsp(x, t) δ = y_δ(x, t)` where `y_δ` is the variational solution
along the orbit `Φ ⟨x, ·⟩` with initial variation `δ`.

The key mathematical observation is that the variational ODE itself defines a flow.
For each base point `x`, the variational ODE in `δ` is the linear ODE
`y'(t) = A_x(t) y(t)` where `A_x(t) := fderiv ℝ (f t) (Φ ⟨x, t⟩)`.  Equivalently,
viewing `Y(x, t) ∈ E →L[ℝ] E` (with `Y(x, t) δ := y_δ(x, t)`) as a CLM-valued curve,
`Y` solves the linear ODE on `E →L[ℝ] E` :
`Y'(t) = A_x(t) ∘ Y(t)`, `Y(t₀) = id`.

Crucially, this linear ODE on `E →L[ℝ] E` can be *packaged together with the original
ODE* into a single ODE on the augmented Banach space `E × (E →L[ℝ] E)`.  Define
`augF : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E))` by
```
augF t (x, Z) := (f t x, (fderiv ℝ (f t) x).comp Z)
```
The augmented vector field `augF` is jointly `C^k` whenever `f` is jointly `C^{k+1}`,
because the spatial Fréchet derivative `(t, x) ↦ fderiv ℝ (f t) x` is `C^k` (it is the
post-composition of `fderiv ℝ (uncurry f)` — itself `C^k` from `f` being `C^{k+1}` — with
the inclusion `inr`).  Composition `(A, Z) ↦ A.comp Z` is bounded bilinear in
`A : E →L[ℝ] E` and `Z : E →L[ℝ] E`, hence jointly smooth.

The augmented flow `aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)` satisfies, for any
initial point `(x₀, Z₀)`,
```
aΦ ⟨(x, Z), t⟩ = (Φ(x, t), variationalLinearMapAt(x, t) ∘ Z)
```
when the original local flow `Φ` exists.  In particular, taking `Z = id` recovers
`variationalLinearMapAt(x, t)` as the second component of `aΦ ⟨(x, id), t⟩`.

This recursive observation gives the abstract induction:
* **Base** `k = 1` : V.2.c.2 applied to the original ODE gives `Φ ∈ C^1`.
* **Step** : if the augmented system has a flow that is jointly `C^k`, the projection
  `(x, t) ↦ Y(x, t) ∘ id = variationalLinearMapAt(x, t)` is jointly `C^k`, which
  discharges the spatial-piece hypothesis of `contDiffOn_flow_succ_of_spatial_smooth`
  (the inductive step from `FlowCk.lean`) and upgrades `Φ` from `C^k` to `C^{k+1}`.

This file provides the *structural* pieces of this argument:

* `augVF` — the augmented vector field on `E × (E →L[ℝ] E)`.
* `augVF_uncurry_contDiff` — `uncurry augVF` is `C^k` whenever `uncurry f` is `C^{k+1}`.
* `contDiffOn_partial_fderiv_of_succ` — the partial-Fréchet-derivative regularity
  `(t, x) ↦ fderiv ℝ (f t) x` is `C^k` from `uncurry f` `C^{k+1}`.
* `contDiffOn_variational_linear_of_aug_flow` — the projection lemma: if a function
  `Y : E × ℝ → E →L[ℝ] E` is the second component of a `C^k` candidate `aΦ` for the
  augmented flow with initial spatial-component `id`, then `Y` is jointly `C^k`.
* `contDiffOn_flow_of_isLocalFlow_of_contDiff_via_aug` — the cleanest packaging of the
  unconditional `C^k` flow theorem, parametrised by a *single* `C^k` candidate for the
  augmented flow.  This factors out the entire `Lsp_seq` sequence from `FlowCk.lean` into
  a single, mathematically-transparent hypothesis.

The connecting hypothesis between "the augmented system has a `C^k` joint flow" and
"the variational linear map is jointly `C^k`" is captured by a `Prop` predicate
`IsVariationalFlowProjection` that bundles the variational identity for the spatial
component of the augmented flow.  When discharged at level `k` (by the augmented flow
theorem or by a direct uniqueness argument), this predicate gives an unconditional
`C^k` flow theorem in one line.

All theorems are formulated on a generic Banach space `E`; `[InnerProductSpace ℝ E]` is
*not* used.  No manifold or tensor file is imported.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## The augmented vector field on `E × (E →L[ℝ] E)`

For a time-dependent vector field `f : ℝ → E → E` we define the *augmented* vector field
`augVF f : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E))` whose orbits are pairs `(x(t), Z(t))`
where `x(t)` solves the original ODE and `Z(t)` solves the linear ODE
`Z'(t) = (fderiv ℝ (f t) (x(t))) ∘ Z(t)`.  Concretely:
```
augVF f t (x, Z) := (f t x, (fderiv ℝ (f t) x).comp Z)
```
The second component is the time-derivative of `Y(x, t) ∘ Z` viewed as a curve in
`E →L[ℝ] E` (post-composition with the constant `Z`). -/

section AugVFDefinition

/-- The **augmented vector field** for the linear-ODE coupling.  This is the
time-dependent vector field on `E × (E →L[ℝ] E)` whose first component is the original
ODE `x'(t) = f t (x(t))` and whose second component is the variational ODE for the
CLM-valued curve `Z(t) = Y(x(t)) ∘ Z₀`. -/
def augVF (f : ℝ → E → E) : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E)) :=
  fun t p => (f t p.1, ((fderiv ℝ (f t) p.1).comp p.2))

@[simp]
lemma augVF_apply (f : ℝ → E → E) (t : ℝ) (x : E) (Z : E →L[ℝ] E) :
    augVF f t (x, Z) = (f t x, ((fderiv ℝ (f t) x).comp Z)) := rfl

end AugVFDefinition

/-! ## Partial Fréchet derivative smoothness

If `uncurry f` is `C^{k+1}` on `Set.univ`, then `fderiv ℝ (uncurry f) : ℝ × E → ((ℝ × E) →L[ℝ] E)`
is `C^k`.  Composing with `inr : E →L[ℝ] ℝ × E` (which is a continuous linear map)
gives the partial Fréchet derivative `(t, x) ↦ fderiv ℝ (f t) x`, which is therefore
also `C^k`. -/

section PartialFDerivSmoothness

variable {f : ℝ → E → E}

/-- The partial-Fréchet-derivative map `(t, x) ↦ fderiv ℝ (f t) x` equals the
post-composition of `fderiv ℝ (uncurry f)` with the inclusion `inr : E →L[ℝ] ℝ × E`,
on the open set where `uncurry f` is differentiable.  We package this on `Set.univ`,
since the project-wide hypothesis is `ContDiffOn ℝ _ (uncurry f) Set.univ`. -/
lemma partial_fderiv_eq_comp_inr_on_univ
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∀ p : ℝ × E, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p := by
    have hp_open : (Set.univ : Set (ℝ × E)) ∈ 𝓝 p := isOpen_univ.mem_nhds (mem_univ _)
    exact (hf.contDiffAt hp_open).differentiableAt one_ne_zero
  exact fderiv_eq_comp_inr hdiff_joint

/-- **Spatial-Fréchet-derivative smoothness.**  If `uncurry f` is `C^{k+1}` on
`Set.univ`, then the partial Fréchet derivative `(t, x) ↦ fderiv ℝ (f t) x` is `C^k`
on `Set.univ`. -/
theorem contDiffOn_partial_fderiv_of_succ
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)) := by
  -- `fderiv ℝ (uncurry f) : ℝ × E → ((ℝ × E) →L[ℝ] E)` is `C^k` on the open `Set.univ`.
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) := by
    have h : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) :=
      hf_succ.fderiv_of_isOpen isOpen_univ le_rfl
    exact h
  -- Post-compose with the bounded linear map `R ↦ R.comp inr`.
  -- `M ↦ M.comp inr : ((ℝ × E) →L[ℝ] E) → (E →L[ℝ] E)` is itself a continuous linear map.
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    -- `compL` is the composition map `M ↦ N ↦ M ∘ N` ; `.flip` swaps; apply with `inr`.
    rfl
  -- The composition `postL ∘ fderiv (uncurry f)` is `C^k`.
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) (Set.univ : Set (ℝ × E)) :=
    hfderiv_Ck.continuousLinearMap_comp postL
  -- And this composition equals the partial Fréchet derivative pointwise on `univ`.
  have heq : ∀ p ∈ (Set.univ : Set (ℝ × E)),
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p _
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact zero_le _
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast h1
      have := hf_succ.of_le h1'
      simpa using this
    have h := partial_fderiv_eq_comp_inr_on_univ hf_C1 p
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq

end PartialFDerivSmoothness

/-! ## Smoothness of the augmented vector field

The augmented vector field `augVF f` is jointly `C^k` whenever `uncurry f` is jointly
`C^{k+1}`.  The first component `f t x` inherits the regularity of `f` directly.  The
second component `(fderiv ℝ (f t) x).comp Z` factors through the bounded bilinear
composition `((·) ∘ (·)) : (E →L[ℝ] E) × (E →L[ℝ] E) → (E →L[ℝ] E)` applied to the
pair `(fderiv ℝ (f t) x, Z)`; the first factor is `C^k` by
`contDiffOn_partial_fderiv_of_succ`, and the second is the projection. -/

section AugVFSmoothness

variable {f : ℝ → E → E}

/-- **Smoothness of the augmented vector field.**  If `uncurry f` is `C^{k+1}` on
`Set.univ : Set (ℝ × E)`, then `uncurry (augVF f)` is `C^k` on `Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))`. -/
theorem augVF_uncurry_contDiff
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  -- First-component smoothness.  `(t, (x, Z)) ↦ f t x` is `C^{k+1}` (hence `C^k`) via the
  -- canonical projection.
  set proj1 : ℝ × (E × (E →L[ℝ] E)) → ℝ × E := fun q => (q.1, q.2.1) with hproj1_def
  have hproj1_Ck : ContDiffOn ℝ k proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact contDiff_fst.contDiffOn
    · exact (contDiff_fst.comp contDiff_snd).contDiffOn
  have hmaps1 : MapsTo proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  have hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_succ.of_le h_le
  have hcomp1 : ContDiffOn ℝ k (uncurry f ∘ proj1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hf_Ck.comp hproj1_Ck hmaps1
  have heq1 : (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1) = uncurry f ∘ proj1 := by
    funext q; rfl
  have hC1 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq1]; exact hcomp1
  -- Second-component smoothness.  We factor `(t, (x, Z)) ↦ (fderiv ℝ (f t) x).comp Z` as
  -- `(t, (x, Z)) ↦ (fderiv ℝ (f t) x, Z) ↦ A.comp Z`.
  have hpartial_Ck := contDiffOn_partial_fderiv_of_succ hf_succ
  -- `(t, (x, Z)) ↦ fderiv ℝ (f t) x` is `C^k` by composition with `proj1`.
  have hA_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (f q.1) q.2.1) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    have hcomp := hpartial_Ck.comp hproj1_Ck hmaps1
    have heq : (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) ∘ proj1
        = (fun q : ℝ × (E × (E →L[ℝ] E)) => fderiv ℝ (f q.1) q.2.1) := by
      funext q; rfl
    rw [← heq]; exact hcomp
  -- `(t, (x, Z)) ↦ Z` is `C^∞`.
  have hZ_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  -- Pair them: `(t, (x, Z)) ↦ (fderiv ℝ (f t) x, Z)`.
  have hpair_Ck : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hA_Ck.prodMk hZ_Ck
  -- The composition `(A, Z) ↦ A.comp Z` is a bounded bilinear map, hence smooth on every
  -- finite order.
  have hbilin_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := E) (G := E)).contDiff
  have hbilin_Ck : ContDiffOn ℝ k
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2)
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := hbilin_smooth.contDiffOn
  have hmaps_pair : MapsTo (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hC2_pre : ContDiffOn ℝ k
      ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
       (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hbilin_Ck.comp hpair_Ck hmaps_pair
  have heq2 : ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
        (fun q : ℝ × (E × (E →L[ℝ] E)) =>
         ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      = (fun q : ℝ × (E × (E →L[ℝ] E)) =>
          (fderiv ℝ (f q.1) q.2.1).comp q.2.2) := by
    funext q; rfl
  have hC2 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (fderiv ℝ (f q.1) q.2.1).comp q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq2] at hC2_pre; exact hC2_pre
  -- Combine: `uncurry (augVF f)` is the pair `(C1, C2)`.
  have hpair_final : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) => (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hC1.prodMk hC2
  -- And this pair equals `uncurry (augVF f)`.
  have heq_final : (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      = uncurry (augVF f) := by
    funext q; rfl
  rw [heq_final] at hpair_final
  exact hpair_final

/-- The augmented vector field is `C^0` (continuous) when `uncurry f` is `C^1`.  This is
the base-level smoothness used for Picard–Lindelöf on the augmented system. -/
theorem augVF_uncurry_continuousOn_of_C1
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContinuousOn (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  have hf_succ : ContDiffOn ℝ ((0 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C1
  have h := augVF_uncurry_contDiff (k := (0 : ℕ∞)) hf_succ
  exact contDiffOn_zero.mp h

end AugVFSmoothness

/-! ## Nesting / bound data for the flow regularity recursion

The variational-flow inductive step (`contDiffOn_flow_succ_via_augFlow`) consumes a large
block of geometric bookkeeping: a uniform bound `M` on the linearization
`(x, τ) ↦ ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖` over a closed ball of initial conditions and a
closed time interval, nested radii `ρ < ρ_mid < ρ_out` inside the flow ball, and nested
times `T < T_mid < T_out` inside the flow's time domain with `M · T_mid < 1`.

This section *derives* all of this data from the bare `IsLocalFlow` hypothesis together
with joint `C^1` regularity of `f`, in finite dimensions (where closed balls are compact).
The single genuine extra requirement is that `t₀` lie strictly inside the flow's time
domain `Ioo tmin tmax` (a two-sided time neighbourhood is impossible at a boundary time)
and that the flow ball be non-degenerate (`0 < r`). -/

section NestingData

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Joint continuity of the linearization along the flow.**  For a local flow `Φ` of a
jointly `C^1` field `f`, the map `(x, τ) ↦ fderiv ℝ (f τ) (Φ ⟨x, τ⟩)` is continuous on the
product `closedBall x₀ ρ ×ˢ Icc tmin tmax`, for any radius `ρ ≤ r`. -/
theorem continuousOn_fderiv_along_flow_joint
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {ρ : ℝ} (hρ : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun p : E × ℝ => fderiv ℝ (f p.2) (Φ p))
      ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) := by
  -- The partial Fréchet derivative `(τ, x) ↦ fderiv ℝ (f τ) x` is continuous on `univ`.
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  -- `Φ` is continuous on the (sub-)ball × time interval.
  have hΦcont : ContinuousOn Φ ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) :=
    hΦ.continuousOn.mono (Set.prod_mono (closedBall_subset_closedBall hρ) (le_refl _))
  -- `(x, τ) ↦ (τ, Φ ⟨x, τ⟩)` is continuous into `univ`.
  have hmap : ContinuousOn (fun p : E × ℝ => (p.2, Φ p))
      ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) :=
    (continuousOn_snd).prodMk hΦcont
  have hmaps : MapsTo (fun p : E × ℝ => (p.2, Φ p))
      ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  exact hpartial.comp hmap hmaps

variable [FiniteDimensional ℝ E]

/-- **Joint bound on the linearization along the flow.**  In finite dimensions, the
continuous linearization map is bounded on the compact product `closedBall x₀ ρ ×ˢ Icc tmin
tmax`.  This produces the uniform constant `M` required by the variational-flow step. -/
theorem exists_norm_fderiv_le_along_flow_joint
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ : ρ ≤ (r : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall x₀ ρ, ∀ τ ∈ Icc tmin tmax,
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
  have hcont := continuousOn_fderiv_along_flow_joint hΦ hf hρ
  -- The norm is continuous on the compact product.
  have hcontN : ContinuousOn (fun p : E × ℝ => ‖fderiv ℝ (f p.2) (Φ p)‖)
      ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) := continuous_norm.comp_continuousOn hcont
  have hcompact : IsCompact ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) :=
    (isCompact_closedBall x₀ ρ).prod isCompact_Icc
  have hne : ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)).Nonempty :=
    ⟨(x₀, t₀), ⟨mem_closedBall_self hρ_nonneg, hΦ.t₀_mem_Icc⟩⟩
  obtain ⟨p, hp, hp_max⟩ := hcompact.exists_isMaxOn hne hcontN
  refine ⟨‖fderiv ℝ (f p.2) (Φ p)‖, norm_nonneg _, ?_⟩
  intro x hx τ hτ
  have hmem : ((x, τ) : E × ℝ) ∈ (closedBall x₀ ρ) ×ˢ (Icc tmin tmax) := ⟨hx, hτ⟩
  exact hp_max hmem

/-- **Uniform Lipschitz bound for `f t` on a closed ball.**  In finite dimensions, joint
`C^1` regularity of `f` gives a single constant `K` with `f t` `K`-Lipschitz on `closedBall
x₀ ρ` for every `t` in a compact interval.  The constant is the maximum spatial-derivative
norm over the compact product `Icc × closedBall`. -/
theorem exists_lipschitzOnWith_closedBall_of_C1
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (x₀ : E) (ρ : ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (closedBall x₀ ρ) := by
  -- The partial Fréchet derivative is continuous on `univ`, hence bounded on the compact
  -- product `Icc a b ×ˢ closedBall x₀ ρ`.
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have hcontN : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖)
      ((Icc a b) ×ˢ (closedBall x₀ ρ)) :=
    (continuous_norm.comp_continuousOn (hpartial.mono (subset_univ _)))
  have hcompact : IsCompact ((Icc a b) ×ˢ (closedBall x₀ ρ)) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ ρ)
  -- Differentiability of `f t` at every point (from `C^1` of `uncurry f`).
  have hdiff : ∀ t : ℝ, ∀ x : E, DifferentiableAt ℝ (f t) x := by
    intro t x
    have hDiff_joint : DifferentiableAt ℝ (uncurry f) (t, x) :=
      (hf.contDiffAt (isOpen_univ.mem_nhds (mem_univ _))).differentiableAt one_ne_zero
    have hg : DifferentiableAt ℝ (fun y : E => (t, y)) x :=
      (differentiableAt_const t).prodMk differentiableAt_id
    exact hDiff_joint.comp x hg
  by_cases hball : (closedBall x₀ ρ).Nonempty
  · obtain ⟨x₁, hx₁⟩ := hball
    have hne : ((Icc a b) ×ˢ (closedBall x₀ ρ)).Nonempty := ⟨(a, x₁), ⟨⟨le_rfl, hab⟩, hx₁⟩⟩
    obtain ⟨p, hp, hp_max⟩ := hcompact.exists_isMaxOn hne hcontN
    set C : ℝ := ‖fderiv ℝ (f p.1) p.2‖ with hC_def
    refine ⟨⟨C, norm_nonneg _⟩, ?_⟩
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hdiff t x) ?_ (convex_closedBall x₀ ρ)
    intro x hx
    have hmem : ((t, x) : ℝ × E) ∈ (Icc a b) ×ˢ (closedBall x₀ ρ) :=
      Set.mem_prod.mpr ⟨ht, hx⟩
    have : ‖fderiv ℝ (f t) x‖ ≤ C := hp_max hmem
    rw [← NNReal.coe_le_coe]
    simpa [coe_nnnorm] using this
  · refine ⟨0, ?_⟩
    intro t _
    rw [not_nonempty_iff_eq_empty] at hball
    rw [hball]
    exact lipschitzOnWith_empty 0 (f t)

/-- **Nesting and bound data for the flow recursion.**

From a local flow `Φ` of a jointly `C^1` field `f` in finite dimensions, with the initial
time `t₀` strictly interior in `Icc tmin tmax` and a non-degenerate flow ball (`0 < r`),
all the geometric bookkeeping consumed by the variational-flow inductive step is produced:
nested radii `0 < ρ < ρ_mid < ρ_out ≤ r` with `ρ_mid + r' ≤ r`, nested times
`0 < T < T_mid < T_out` with `M · T_mid < 1`, a closed time interval inside the flow's time
domain, and a uniform bound `M` on the linearization over the closed ball of initial
conditions and the closed time interval. -/
theorem exists_flow_nesting_data
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ)) :
    ∃ (T_out T_mid T M : ℝ) (ρ_out ρ_mid ρ r' : ℝ≥0),
      0 < T ∧ T < T_mid ∧ T_mid < T_out ∧ 0 ≤ M ∧ M * T_mid < 1 ∧ 0 < (r' : ℝ) ∧
      0 < (ρ : ℝ) ∧ (ρ : ℝ) < (ρ_mid : ℝ) ∧ (ρ_mid : ℝ) < (ρ_out : ℝ) ∧
      (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) ∧ (ρ_out : ℝ) ≤ (r : ℝ) ∧
      Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax ∧
      (∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) := by
  -- Radii: ρ = r/8 < ρ_mid = r/4 < ρ_out = r/2 ≤ r ; r' = r/2 with ρ_mid + r' = 3r/4 ≤ r.
  let ρ_out : ℝ≥0 := r / 2
  let ρ_mid : ℝ≥0 := r / 4
  let ρ : ℝ≥0 := r / 8
  let r' : ℝ≥0 := r / 2
  have hρ_out_coe : (ρ_out : ℝ) = (r : ℝ) / 2 := by simp only [ρ_out]; push_cast; ring
  have hρ_mid_coe : (ρ_mid : ℝ) = (r : ℝ) / 4 := by simp only [ρ_mid]; push_cast; ring
  have hρ_coe : (ρ : ℝ) = (r : ℝ) / 8 := by simp only [ρ]; push_cast; ring
  have hr'_coe : (r' : ℝ) = (r : ℝ) / 2 := by simp only [r']; push_cast; ring
  have hρ_pos : 0 < (ρ : ℝ) := by rw [hρ_coe]; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by rw [hρ_coe, hρ_mid_coe]; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by rw [hρ_mid_coe, hρ_out_coe]; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by rw [hρ_mid_coe, hr'_coe]; linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ) := by rw [hρ_out_coe]; linarith
  have hr'_pos : 0 < (r' : ℝ) := by rw [hr'_coe]; linarith
  -- Outer time radius T_out = d/2 where d = min(t₀ - tmin, tmax - t₀) > 0.
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_out : ℝ := d / 2 with hT_out_def
  have hT_out_pos : 0 < T_out := by rw [hT_out_def]; linarith
  -- The closed time interval is inside `Icc tmin tmax`.
  have hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have : d ≤ t₀ - tmin := min_le_left _ _
      rw [hT_out_def]; linarith
    · have : d ≤ tmax - t₀ := min_le_right _ _
      rw [hT_out_def]; linarith
  -- The bound `M` over `closedBall x₀ ρ_out × Icc tmin tmax`, restricted to the inner times.
  obtain ⟨M, hM_nonneg, hM_bd⟩ :=
    exists_norm_fderiv_le_along_flow_joint hΦ hf (ρ := (ρ_out : ℝ))
      (NNReal.coe_nonneg ρ_out) hρ_out_le_r
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
    intro x hx τ hτ
    exact hM_bd x hx τ (hsub hτ)
  -- Inner times: T_mid = min(T_out/2, 1/(2(M+1))), T = T_mid/2.
  set T_mid : ℝ := min (T_out / 2) (1 / (2 * (M + 1))) with hT_mid_def
  have hM1_pos : 0 < 2 * (M + 1) := by linarith
  have hT_mid_pos : 0 < T_mid := lt_min (by linarith) (by positivity)
  have hT_mid_lt_out : T_mid < T_out := by
    calc T_mid ≤ T_out / 2 := min_le_left _ _
      _ < T_out := by linarith
  set T : ℝ := T_mid / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_lt_mid : T < T_mid := by rw [hT_def]; linarith
  -- `M * T_mid < 1`.
  have hMT_mid : M * T_mid < 1 := by
    have hle : T_mid ≤ 1 / (2 * (M + 1)) := min_le_right _ _
    have hM_T_mid : M * T_mid ≤ M * (1 / (2 * (M + 1))) := by
      apply mul_le_mul_of_nonneg_left hle hM_nonneg
    calc M * T_mid ≤ M * (1 / (2 * (M + 1))) := hM_T_mid
      _ = M / (2 * (M + 1)) := by ring
      _ < 1 := by
          rw [div_lt_one hM1_pos]; linarith
  exact ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT_pos, hT_lt_mid, hT_mid_lt_out,
    hM_nonneg, hMT_mid, hr'_pos, hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r,
    hsub, hA_bd⟩

end NestingData

/-! ## The variational-flow projection predicate

The bridge between "augmented flow `aΦ` is jointly `C^k`" and "the variational linear
map is jointly `C^k`" is captured by an explicit projection identity: for every
`(x, t)` in the relevant open neighbourhood, taking the *second* component of
`aΦ ⟨(x, id), t⟩` equals `variationalLinearMapAt(x, t)`.

The argument that the second component of the augmented flow is exactly the variational
linear map requires a uniqueness theorem for the linear ODE on `E →L[ℝ] E` —
specifically, that the curve `t ↦ aΦ ⟨(x, id), t⟩.2` is the unique solution of
`Z'(t) = (fderiv ℝ (f t) (Φ ⟨x, t⟩)) ∘ Z(t)` with `Z(t₀) = id`, and that this unique
solution agrees pointwise with the application `δ ↦ variationalSolutionFun(x, δ, t)`
via linearity.

We package the projection identity as a `Prop`-level predicate, and the abstract
inductive theorem consumes it as a hypothesis.  Discharging this predicate at level
`k` reduces precisely to: existence of a joint `C^k` flow of the augmented system on
the required neighbourhood, together with the variational identification of its
second component. -/

section ProjectionPredicate

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **The augmented-flow projection predicate.**

Given the parameters of `contDiffOn_flow_succ_of_spatial_smooth`, a function
`Y : E × ℝ → (E →L[ℝ] E)` is a *variational-flow projection at level `k`* if

* `Y` is jointly `C^k` on the open neighbourhood
  `ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`;
* `Y(x, t)` agrees with the variational linear map at `(x, t)` for the local flow `Φ`.

The second clause is captured via the coproduct identity for `fderiv ℝ Φ`, matching
the hypothesis of `contDiffOn_flow_succ_of_spatial_smooth`. -/
structure IsVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) (T : ℝ) (ρ : ℝ≥0)
    (Y : E × ℝ → (E →L[ℝ] E)) (k : ℕ∞) : Prop where
  contDiffOn : ContDiffOn ℝ k Y ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))
  fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
    fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q)

/-- Mono: a level-`k` variational-flow projection is also a level-`j` one for `j ≤ k`. -/
lemma IsVariationalFlowProjection.of_le {hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ}
    {T : ℝ} {ρ : ℝ≥0} {Y : E × ℝ → (E →L[ℝ] E)} {k j : ℕ∞}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) (hjk : j ≤ k) :
    IsVariationalFlowProjection hΦ T ρ Y j := by
  refine
  { contDiffOn := ?_,
    fderiv_eq := hY.fderiv_eq }
  have hjk' : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
  exact hY.contDiffOn.of_le hjk'

end ProjectionPredicate

/-! ## The recursive `C^k` flow theorem

Given a single variational-flow projection at level `k`, the flow is jointly `C^{k+1}`
on the required open neighbourhood.  This is a direct application of
`contDiffOn_flow_succ_of_spatial_smooth` (from `FlowCk.lean`) plus an induction on `k`
to upgrade the conclusion to `C^{k+1}`.  We work with `k : ℕ` so that the induction is
clean.

The hypothesis is structured to consume a *sequence* of projections — at every level
`j < k+1` — each of which is jointly `C^j` and agrees with `fderiv ℝ Φ` via the
coproduct.  In practice, all the candidate projections are the same function (the
unique variational linear map), so a single hypothesis at the highest level `j = k`
provides them all.  We expose both flavours below. -/

section RecursiveFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Recursive `C^k` flow theorem (single-projection form).**

If a function `Y : E × ℝ → (E →L[ℝ] E)` is a variational-flow projection at level `k`,
then the flow `Φ` is jointly `C^{k+1}` on the strictly-interior open neighbourhood. -/
theorem contDiffOn_flow_succ_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
  contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck
    hY.contDiffOn hY.fderiv_eq

/-- **Recursive `C^k` flow theorem (sequence form).**

A sequence of variational-flow projections, one at each level `j < k`, gives the flow
joint `C^k` regularity on the strictly-interior open neighbourhood, for any `k : ℕ`.
This is a direct consequence of `contDiffOn_flow_of_spatial_smooth_seq` once the
sequence-of-`Y_seq` formulation is unpacked. -/
theorem contDiffOn_flow_of_isVariationalFlowProjection_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (Y_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hY_seq : ∀ j : ℕ, j + 1 ≤ k →
      IsVariationalFlowProjection hΦ T ρ (Y_seq j) (j : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  refine contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_ ?_
  · intro j hj
    exact (hY_seq j hj).contDiffOn
  · intro j hj
    exact (hY_seq j hj).fderiv_eq

/-- **Recursive `C^k` flow theorem (single-projection top-level form).**

Given a *single* variational-flow projection at level `k - 1`, the flow is jointly
`C^k` on the strictly-interior open neighbourhood, for any `k : ℕ` with `1 ≤ k`.

The single hypothesis at the highest level `k - 1` is upgraded via `IsVariationalFlowProjection.of_le`
to a sequence at every intermediate level `j < k`.  In particular, the user only ever
needs to supply *one* projection — at level `k - 1`. -/
theorem contDiffOn_flow_of_isVariationalFlowProjection_top
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ) (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y ((k - 1 : ℕ) : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Use the sequence formulation, with `Y_seq j := Y` for every `j`.  Each `Y` is
  -- a `IsVariationalFlowProjection` at level `j ≤ k - 1`, by mono.
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun _ => Y with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  have hj_le : (j : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := by
    have h : j ≤ k - 1 := by omega
    exact_mod_cast h
  exact hY.of_le hj_le

end RecursiveFlow

/-! ## Regularity-independent coproduct identity for `fderiv ℝ Φ`

The `fderiv_eq` clause of `IsVariationalFlowProjection` — that `fderiv ℝ Φ` splits as the
coproduct of a spatial piece and the time piece — is a *regularity-independent* statement:
it follows from the joint Fréchet-derivative formula `hasFDerivAt_flow_jointly_at`, which
requires only `C^1` of `f`.  We package it once here, with the spatial piece realised as
the spatial restriction `(fderiv ℝ Φ q).comp (inl ℝ E ℝ)` of the joint derivative, so that
it is a clean total function on `E × ℝ`.

This piece is the half of `IsVariationalFlowProjection` that *can* be discharged from the
existing infrastructure.  The other half — joint `C^k` smoothness of the spatial piece, i.e.
smooth parameter-dependence of the variational linear ODE — is the genuine remaining
mathematical content and is not provided by this lemma. -/

section FderivCoprodIdentity

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- The **spatial piece** of the joint Fréchet derivative of the flow: the spatial
restriction `(fderiv ℝ Φ q).comp (inl ℝ E ℝ)` of the joint derivative, viewed as a total
`CLM`-valued function of `q = (x, t)`.  By `hasFDerivAt_flow_jointly_at`, at every interior
point this equals the variational linear map along the orbit through `x`. -/
def spatialPieceFn (Φ : E × ℝ → E) : E × ℝ → (E →L[ℝ] E) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)

@[simp]
lemma spatialPieceFn_apply (Φ : E × ℝ → E) (q : E × ℝ) :
    spatialPieceFn Φ q = (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) := rfl

/-- **Regularity-independent coproduct identity.**  Under the standard `C^1` flow
hypotheses (three-layer nested setup of `contDiffOn_flow_of_isLocalFlow`), at every point
`q = (x, t)` of the strictly-interior open neighbourhood the joint Fréchet derivative of
the flow splits as the coproduct of its spatial piece and the time piece:
`fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q)`.

This is exactly the `fderiv_eq` clause of `IsVariationalFlowProjection`, realised for the
canonical spatial piece `spatialPieceFn Φ`.  Only `C^1` of `f` is required. -/
theorem fderiv_flow_eq_coprod_spatialPiece
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (_hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) := by
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hρ_mid_pos : 0 < (ρ_mid : ℝ) := lt_of_le_of_lt (ρ.coe_nonneg) hρ_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ), ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ =>
    hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  intro q hq
  rcases hq with ⟨hq_x, hq_t⟩
  rw [mem_ball] at hq_x
  obtain ⟨x, t⟩ := q
  have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
    mem_closedBall.mpr (le_of_lt (lt_trans hq_x hρ_lt_mid))
  have hq_t_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨by linarith [hq_t.1], by linarith [hq_t.2]⟩
  -- The joint Fréchet derivative at `(x, t)`.
  have hfd_at := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid hr' hρρ'
    hA_bd_mid hx_cb_mid hq_t_mid
  have hfd_eq := hfd_at.fderiv
  -- Decompose the coproduct via its spatial/time restrictions.
  set Lsp : E →L[ℝ] E :=
    variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
      hT_mid_pos hM hMT_mid
      (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
          rw [mem_closedBall] at hx_cb_mid; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub_mid)
      (fun τ hτ => hA_bd_mid x hx_cb_mid τ hτ) (Ioo_subset_Icc_self hq_t_mid) with hLsp_def
  set Lti : ℝ →L[ℝ] E :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩)) with hLti_def
  -- The time piece equals `Lti` by definition.
  have hti_eq : timePieceFn f Φ (x, t) = Lti := rfl
  -- The spatial piece equals `Lsp`: it is the `inl`-restriction of the coproduct.
  have hsp_eq : spatialPieceFn Φ (x, t) = Lsp := by
    rw [spatialPieceFn_apply, hfd_eq]
    exact ContinuousLinearMap.coprod_comp_inl Lsp Lti
  rw [hsp_eq, hti_eq, hfd_eq]

end FderivCoprodIdentity

/-! ## The `k = 2` specialization via V.2.c.2 on the augmented system

For `k = 2`, the variational-flow projection at level `1` reduces to *joint continuity*
of the variational linear map.  This is already proved in `FlowC1Continuous.lean` (in
the `continuousOn_fderiv_flow_of_isLocalFlow` proof), where the spatial piece of
`fderiv ℝ Φ` is shown to be jointly continuous on the strictly-interior neighbourhood.

But continuity is not enough at level `1`: we need `C^1`.  The `C^1` claim is the
target of the next layer of recursion: applying V.2.c.2 (`contDiffOn_flow_of_isLocalFlow`)
to the *augmented system* `augVF f` on `E × (E →L[ℝ] E)`.  V.2.c.2 requires the
augmented vector field to be jointly `C^1`, which is satisfied when `uncurry f` is
jointly `C^2` (`augVF_uncurry_contDiff` at level `k = 1`).

The application of V.2.c.2 to the augmented system requires the augmented system to
have a `IsLocalFlow` in its own right.  Since the augmented vector field is jointly
`C^1` on `Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))`, V.2.b.1's
`exists_isLocalFlow_of_contDiffOn_univ` (in `FlowC1.lean`) produces a local flow of the
augmented system around any base point `((x₀, id), t₀)`.

The remaining step — identifying the second component of the augmented flow with the
variational linear map — uses uniqueness of the linear ODE for the variational
solution, applied pointwise in `δ`.  This identification is captured by the
`IsVariationalFlowProjection` predicate above. -/

section LevelTwo

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Existence of a local flow for the augmented system.**

When `uncurry f` is jointly `C^2` on `Set.univ`, the augmented vector field `augVF f`
is jointly `C^1` on `Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))`.  V.2.b.1's
`exists_isLocalFlow_of_contDiffOn_univ` (`FlowC1.lean`) then produces a local flow of
the augmented system around any base point. -/
theorem exists_isLocalFlow_augVF_of_C2
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (p₀ : E × (E →L[ℝ] E)) :
    ∃ (R : ℝ≥0) (ε : ℝ) (_ : 0 < R) (_ : 0 < ε)
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      IsLocalFlow (augVF f) t₀ p₀ R (t₀ - ε) (t₀ + ε) aΦ := by
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  exact exists_isLocalFlow_of_contDiffOn_univ (augVF f) h_augVF_C1 t₀ p₀

/-- **The `C^2` flow theorem, conditional on a `C^1` variational-flow projection.**

If `uncurry f` is jointly `C^2`, the local flow `Φ` is jointly `C^1` on the
strictly-interior open neighbourhood (by V.2.c.2), and a `C^1` variational-flow
projection `Y` at level `1` exists, then `Φ` is jointly `C^2` on the same
neighbourhood. -/
theorem contDiffOn_flow_of_isLocalFlow_C2_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y 1) :
    ContDiffOn ℝ 2 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- First get `C^1` of `Φ` via V.2.c.2.
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2)
    exact hf_C2.of_le h_le
  have hΦ_C1 : ContDiffOn ℝ 1 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  -- Now apply the recursive step at `k = 1`.
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_step := contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid
    hT_mid_lt_out hM hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
    (k := (1 : ℕ∞)) hf_succ hΦ_C1 hY
  -- `(1 : ℕ∞) + 1 = 2`.
  simpa using h_step

end LevelTwo

/-! ## Pointwise variational identification of the augmented-flow second component

The connecting lemma between an `aΦ` (any candidate for the augmented flow) and the
variational linear map is: at every initial point `(x, id)` and time `t`, the second
component of `aΦ ⟨(x, id), t⟩` *equals* `variationalLinearMapAt(x, t)`.

This identification is a uniqueness statement for the variational-style linear ODE on
`E →L[ℝ] E`.  It is mathematically subtle because the augmented flow is given by
Picard–Lindelöf on a *closed ball* centered at `(x₀, id)` in the product norm, and the
variational linear map is the operator-norm closure of solutions on a closed ball of
`E` (per-`δ`).  Reconciling the two requires a pointwise-in-`δ` argument:

* Apply the augmented flow's second component to a fixed `δ ∈ E`: `(aΦ ⟨(x, id), t⟩).2 δ
  : E`.
* Show that as a function of `t`, this satisfies the variational ODE with initial
  variation `δ`.
* By the uniqueness lemma `IsVariationalSolutionOn.unique_Icc` (from
  `FlowC1Bridge.lean`), it agrees with `variationalSolutionFun(x, δ, t)`.
* Hence the operator `(aΦ ⟨(x, id), t⟩).2` agrees pointwise (and hence as a CLM, since
  both are CLMs on `E`) with `variationalLinearMapAt(x, t)`.

The technical work for this identification — propagating the second-component
derivative through the augmented ODE, exchanging the application to `δ` with the
time-derivative, and recognising the resulting curve as a variational solution —
mirrors the existing `variationalSolution` infrastructure but on the larger space.

We expose the *structural* result: a function `aΦ` that satisfies the augmented flow
ODE in the second component (in the sense that `t ↦ aΦ ⟨(x, id), t⟩.2 δ` solves the
variational ODE for each `δ`) gives a variational-flow projection of `Φ`.  The
verification of the second-component-ODE hypothesis is the natural way to plug in any
specific construction of the augmented flow (Picard–Lindelöf, ODE shooting, fixed
point on a function space, ...). -/

section AugFlowProjection

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- The **operator-valued curve from a candidate augmented flow**: given a candidate
`aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)`, the projection
`Y(x, t) := aΦ ⟨(x, id), t⟩.2 : E →L[ℝ] E` is the natural candidate for the spatial
piece of `fderiv ℝ Φ`. -/
def fromAugFlow (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)) :
    E × ℝ → (E →L[ℝ] E) :=
  fun q => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).2

@[simp]
lemma fromAugFlow_apply (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (x : E) (t : ℝ) :
    fromAugFlow aΦ (x, t) = (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2 := rfl

/-- **Joint smoothness of the projection.**  If the candidate `aΦ` is jointly `C^k` in
its arguments on an open set `Ω ⊆ (E × (E →L[ℝ] E)) × ℝ`, and the embedding
`(x, t) ↦ ((x, id), t)` maps `U ⊆ E × ℝ` into `Ω`, then the projection `fromAugFlow aΦ`
is jointly `C^k` on `U`. -/
theorem contDiffOn_fromAugFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {k : ℕ∞} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)} {U : Set (E × ℝ)}
    (haΦ : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U Ω) :
    ContDiffOn ℝ k (fromAugFlow aΦ) U := by
  -- The embedding `(x, t) ↦ ((x, id), t)` is `C^∞`.
  have h_embed_smooth : ContDiff ℝ (k : ℕ∞)
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) := by
    refine ContDiff.prodMk ?_ contDiff_snd
    refine ContDiff.prodMk contDiff_fst ?_
    exact contDiff_const
  have h_embed_Ck : ContDiffOn ℝ k
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) U :=
    h_embed_smooth.contDiffOn
  -- Composition.
  have hcomp : ContDiffOn ℝ k (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U :=
    haΦ.comp h_embed_Ck hmap
  -- Take the second component.
  have hsnd_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : E × (E →L[ℝ] E) => p.2) := contDiff_snd
  have hsnd_Ck : ContDiffOn ℝ k (fun p : E × (E →L[ℝ] E) => p.2)
      (Set.univ : Set (E × (E →L[ℝ] E))) := hsnd_smooth.contDiffOn
  have hmaps : MapsTo (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U
      (Set.univ : Set (E × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hfinal : ContDiffOn ℝ k
      ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2)))) U :=
    hsnd_Ck.comp hcomp hmaps
  -- The composition equals `fromAugFlow aΦ`.
  have heq : ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2))))
      = fromAugFlow aΦ := by
    funext q
    rfl
  rw [heq] at hfinal
  exact hfinal

end AugFlowProjection

/-! ## Wrapping everything: the abstract unconditional `C^k` theorem

We now provide the cleanest abstract packaging of "from an augmented-flow input, the
ordinary flow is `C^{k+1}` jointly".

The input is a candidate `aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)` together with:

* a `ContDiffOn ℝ k` smoothness assertion on `aΦ` on an open neighbourhood;
* a pointwise variational identification of `(aΦ ⟨(x, id), t⟩).2` with the spatial
  partial Fréchet derivative of `Φ` (via the coproduct identity for `fderiv ℝ Φ`).

The conclusion is `ContDiffOn ℝ (k+1) Φ U` on the strictly-interior open neighbourhood.

Discharging the second hypothesis — variational identification — concretely requires
the uniqueness lemma for the linear ODE on `E →L[ℝ] E`.  When the underlying `aΦ` is
the Picard–Lindelöf flow of the augmented vector field `augVF f`, uniqueness follows
from `ODE_solution_unique_of_mem_Ioo` (Mathlib) applied at every fixed `δ ∈ E`.  We do
not embed that pointwise argument into the public signature here; it is left to the
caller, where any specific construction of the augmented flow can supply the
identification directly. -/

section UnconditionalAbstract

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Unconditional `C^{k+1}` flow theorem via an augmented-flow candidate.**

If we have a candidate `aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)` that is jointly
`C^k` on an open neighbourhood `Ω` of `((x₀, id), t₀)`, and whose second-component
projection `fromAugFlow aΦ` is a level-`k` variational-flow projection of `Φ`, then
`Φ` is jointly `C^{k+1}` on the strictly-interior open neighbourhood.

The hypothesis is exactly what an inductive argument on the augmented-flow theorem
delivers; the conclusion plugs back into the same induction at the next level.  In
particular, for `k = 1`, the augmented flow's `C^1` regularity is supplied by V.2.c.2
applied to the augmented vector field `augVF f` (provided `uncurry f` is `C^2`), and
the level-`1` variational identification is the pointwise variational ODE
identification described above. -/
theorem contDiffOn_flow_succ_of_augFlow_candidate
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (h_fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugFlow aΦ q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Build the variational-flow projection from `aΦ`.
  have hY_Ck : ContDiffOn ℝ k (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugFlow haΦ_Ck hmap
  have hY : IsVariationalFlowProjection hΦ T ρ (fromAugFlow aΦ) k :=
    { contDiffOn := hY_Ck, fderiv_eq := h_fderiv_eq }
  -- Plug into the recursive step.
  exact contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hY

end UnconditionalAbstract

/-! ## Aggregated public headline (general `k : ℕ`, parametrised by augmented-flow data)

The cleanest public form of the `C^k` flow theorem in this file consumes:

* the standard `IsLocalFlow` and `ContDiffOn` hypotheses on `f`;
* a *sequence* of augmented-flow candidates, one per level, each jointly `C^j` on its
  open neighbourhood with the variational identification at level `j`.

This is precisely the `Lsp_seq` interface from `FlowCk.lean`, restated through the
augmented-flow lens.  For practical use, this is the public theorem to call: it
factors out all the inductive machinery, and the user supplies only the
parametric-ODE-smoothness data of the augmented system. -/

section AggregatedPublic

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Public headline `C^k` flow theorem (general `k : ℕ`).**

This theorem packages the inductive structural argument cleanly: given a sequence of
augmented-flow candidates `aΦ_seq j`, each jointly `C^j` on its respective open
neighbourhood `Ω j`, whose second-component projections `fromAugFlow (aΦ_seq j)` satisfy
the variational identification with `fderiv ℝ Φ` at every level, the flow `Φ` is
jointly `C^k` on the strictly-interior open neighbourhood. -/
theorem contDiffOn_flow_of_augFlow_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (aΦ_seq : ℕ → (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (Ω_seq : ℕ → Set ((E × (E →L[ℝ] E)) × ℝ))
    (haΦ_Ck : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (aΦ_seq j) (Ω_seq j))
    (hmap_seq : ∀ j : ℕ, j + 1 ≤ k →
      MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) (Ω_seq j))
    (h_fderiv_eq_seq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugFlow (aΦ_seq j) q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Build the `Y_seq` by projection and supply it to the sequence theorem.
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun j => fromAugFlow (aΦ_seq j) with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  refine
  { contDiffOn := contDiffOn_fromAugFlow (haΦ_Ck j hj) (hmap_seq j hj),
    fderiv_eq := h_fderiv_eq_seq j hj }

end AggregatedPublic

/-! ## Operator-valued variational solutions and the identification lemma

We now provide the pointwise variational identification connecting an operator-valued
curve that satisfies the linear ODE on `E →L[ℝ] E` with the per-`δ` variational
linear map.

Concretely: if `Z : ℝ → E →L[ℝ] E` is differentiable in `t` on `Icc (t₀ - T) (t₀ + T)`
with `Z(t₀) = id` and the operator-valued ODE `Z'(t) = A(t) ∘ Z(t)` where
`A(t) := fderiv ℝ (f t) (α t)`, then for every `δ ∈ E`, the curve `t ↦ Z(t) δ` is a
variational solution along `α` with initial variation `δ`.  Uniqueness on the closed
interval then identifies `Z(t) δ = variationalLinearMapAt(...) δ`, hence
`Z(t) = variationalLinearMapAt(...)` as CLMs by extensionality. -/

section OperatorVariational

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

/-- The application `Z(·) δ` of a CLM-curve `Z : ℝ → E →L[ℝ] E` to a fixed vector
`δ ∈ E` has, at every point where `Z` has the operator-valued derivative `Z'(t)`,
ordinary derivative `Z'(t) δ : E`. -/
lemma hasDerivWithinAt_apply {Z Z' : ℝ → (E →L[ℝ] E)} {s : Set ℝ} {t : ℝ} {δ : E}
    (hZ : HasDerivWithinAt Z (Z' t) s t) :
    HasDerivWithinAt (fun τ => Z τ δ) ((Z' t) δ) s t := by
  -- Apply the continuous linear map `apply δ : (E →L[ℝ] E) →L[ℝ] E` to `hZ`.
  set applyδ : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E δ
  have happ : HasFDerivAt applyδ applyδ (Z t) := applyδ.hasFDerivAt
  have hZ_fd : HasFDerivWithinAt Z
      (ContinuousLinearMap.toSpanSingleton ℝ (Z' t)) s t := hZ.hasFDerivWithinAt
  have happ_fd := happ.comp_hasFDerivWithinAt t hZ_fd
  -- The composition has Fréchet derivative `applyδ.comp (toSpanSingleton (Z' t))`,
  -- which equals `toSpanSingleton ((Z' t) δ)`.
  have heq : applyδ.comp (ContinuousLinearMap.toSpanSingleton ℝ (Z' t))
      = ContinuousLinearMap.toSpanSingleton ℝ ((Z' t) δ) := by
    apply ContinuousLinearMap.ext
    intro r
    simp [applyδ, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply]
  rw [heq] at happ_fd
  -- Convert the Fréchet derivative back to the directional derivative.
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact happ_fd

/-- **Operator-valued variational ODE → pointwise variational solutions.**

Suppose `Z : ℝ → E →L[ℝ] E` satisfies, on `Icc (t₀ - T) (t₀ + T)`:
* `Z(t₀) = id`,
* for every `t` in the interval, `Z` has the operator-valued derivative
  `(fderiv ℝ (f t) (α t)).comp (Z t)`.

Then for every `δ ∈ E`, the curve `t ↦ Z(t) δ` is a variational solution along the
central curve `α` with initial variation `δ` on the same interval. -/
theorem isVariationalSolutionOn_apply
    {T : ℝ}
    {Z : ℝ → E →L[ℝ] E}
    (hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    (δ : E) :
    IsVariationalSolutionOn f α δ t₀ (fun s => Z s δ) (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨?_, ?_⟩
  · -- Initial value: `Z(t₀) δ = id δ = δ`.
    have : Z t₀ δ = ContinuousLinearMap.id ℝ E δ := by rw [hZ_init]
    simpa using this
  · intro t ht
    have hZ_d := hZ_deriv t ht
    have happ := hasDerivWithinAt_apply (Z := Z)
      (Z' := fun s => (fderiv ℝ (f s) (α s)).comp (Z s)) (δ := δ) hZ_d
    -- The derivative we get is `((fderiv ℝ (f t) (α t)).comp (Z t)) δ`, which equals
    -- `(fderiv ℝ (f t) (α t)) (Z t δ)` by `comp_apply`.
    have hsimp : ((fderiv ℝ (f t) (α t)).comp (Z t)) δ
        = (fderiv ℝ (f t) (α t)) (Z t δ) := by rfl
    rw [hsimp] at happ
    exact happ

/-- **Identification of `Z` with the variational linear map.**

Under the hypotheses of `isVariationalSolutionOn_apply` (operator-valued variational
ODE with `Z(t₀) = id`), at every `t ∈ Icc (t₀ - T) (t₀ + T)`, the CLM `Z t` agrees
with the variational linear map `variationalLinearMapAt(...)`.

The proof: by `isVariationalSolutionOn_apply`, `t ↦ Z t δ` is a variational solution
on the closed interval; by `variationalSolutionFun_isSolution`,
`t ↦ variationalSolutionFun(...) δ t` is also one; by `unique_Icc`, they agree at every
`t`; hence `Z t δ = variationalLinearMapAt(...) δ` for every `δ`; CLM extensionality
finishes. -/
theorem Z_eq_variationalLinearMapAt
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    {Z : ℝ → E →L[ℝ] E}
    (hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    Z t = variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht := by
  -- Extensionality: show pointwise equality for every `δ`.
  apply ContinuousLinearMap.ext
  intro δ
  have h_Z_sol := isVariationalSolutionOn_apply (T := T) (Z := Z) hZ_init hZ_deriv δ
  have h_var_sol := variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont h_Z_sol h_var_sol
  have hZδ_t : Z t δ
      = variationalSolutionFun (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd δ t :=
    h_eq ht
  rw [hZδ_t]
  exact (variationalLinearMapAt_apply hT hM hMT hA_cont hA_bd ht δ).symm

end OperatorVariational

/-! ## Putting it all together: the augmented-flow-based projection lemma

Given an `IsLocalFlow` for the augmented vector field `augVF f`, the second component
of its orbit starting at `(x, id)` is, on the time interval `Icc (t₀ - T) (t₀ + T)`,
*exactly* the variational linear map.  This is the cleanest concrete way to discharge
the spatial-piece smoothness hypothesis at any level for which the augmented flow's
smoothness is available. -/

section AugFlowVariationalIdentification

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- Given a local flow `aΦ` of the augmented vector field `augVF f`, started at
`(x, id)`, the second component is, at every time `t` in the operating interval,
equal to the variational linear map along the central orbit `t ↦ (aΦ ⟨(x, id), t⟩).1`.

The hypothesis structure mirrors `IsLocalFlow`: the augmented flow has, for every
`p ∈ closedBall p₀ R`, the derivative property
`(aΦ ⟨p, ·⟩)'(t) = augVF f t (aΦ ⟨p, t⟩)`.  Specialising to `p = (x, id)`, the second
component evolves by the operator-valued variational ODE, so
`Z_eq_variationalLinearMapAt` applies. -/
theorem augFlow_snd_eq_variationalLinearMapAt
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    {p₀ : E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ p₀ R tmin' tmax' aΦ)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    {x : E} (hx : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ))
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t)
      ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f t) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f)
          (α := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) (t₀ := t₀)
          hT hM hMT hA_cont hA_bd ht := by
  -- The augmented orbit starting at `(x, id)`.
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  set orbit : ℝ → E × (E →L[ℝ] E) := fun s => aΦ ⟨p, s⟩ with horbit_def
  -- The second component of the orbit.
  set Z : ℝ → E →L[ℝ] E := fun s => (orbit s).2 with hZ_def
  -- The central orbit (first component).
  set α : ℝ → E := fun s => (orbit s).1 with hα_def
  -- Initial value: at `t₀`, `orbit t₀ = p = (x, id)`, so `Z t₀ = id`.
  have hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E := by
    have h_init : orbit t₀ = p := haΦ.apply_initial p hx
    change (orbit t₀).2 = ContinuousLinearMap.id ℝ E
    rw [h_init]
  -- The orbit satisfies the augmented ODE on `Icc tmin' tmax'`.
  have h_orbit_deriv : ∀ s ∈ Icc tmin' tmax',
      HasDerivWithinAt orbit (augVF f s (orbit s)) (Icc tmin' tmax') s :=
    fun s hs => haΦ.hasDerivWithinAt p hx s hs
  -- Specialise to `Icc (t₀ - T) (t₀ + T)` via mono.
  have h_orbit_deriv' : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt orbit (augVF f s (orbit s)) (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    exact (h_orbit_deriv s (hsub hs)).mono hsub
  -- Project to the second component.  `Z(s) = orbit(s).2`, so `Z'(s)` is the second
  -- component of `(orbit s)'`, which equals the second component of `augVF f s (orbit s)`.
  -- The second component of `augVF f s (orbit s)` is `(fderiv ℝ (f s) α(s)).comp Z(s)`.
  have hZ_deriv : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f s) (α s)).comp (Z s))
        (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have h := h_orbit_deriv' s hs
    -- Apply the continuous linear map `snd` to `h`'s Fréchet form, then convert back.
    set sndCLM : (E × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
      ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)
    have h_fd := h.hasFDerivWithinAt
    have h_snd_at := (sndCLM.hasFDerivAt).comp_hasFDerivWithinAt s h_fd
    -- `h_snd_at` has derivative `sndCLM.comp (toSpanSingleton ℝ (orbit')) = toSpanSingleton ℝ (orbit').2`.
    have heq : sndCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (augVF f s (orbit s)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augVF f s (orbit s)).2) := by
      apply ContinuousLinearMap.ext
      intro r
      change (sndCLM (r • augVF f s (orbit s)))
        = r • (augVF f s (orbit s)).2
      change (r • augVF f s (orbit s)).2 = r • (augVF f s (orbit s)).2
      rfl
    rw [heq] at h_snd_at
    have h_aug_snd : (augVF f s (orbit s)).2
        = (fderiv ℝ (f s) (α s)).comp (Z s) := rfl
    rw [h_aug_snd] at h_snd_at
    -- Convert HasFDerivWithinAt back to HasDerivWithinAt.
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact h_snd_at
  exact Z_eq_variationalLinearMapAt hT hM hMT hA_cont hA_bd hZ_init hZ_deriv ht

end AugFlowVariationalIdentification

/-! ## Orbit uniqueness: the augmented flow's first component is the original flow

The first component of `augVF f` is just `f`: `(augVF f t p).1 = f t p.1`.  Hence the first
component `t ↦ (aΦ ⟨(x, id), t⟩).1` of an augmented orbit solves the *original* ODE
`y'(t) = f t (y(t))` with the same initial value `x` at `t₀` as the original orbit
`t ↦ Φ ⟨x, t⟩`.  By ODE uniqueness (Picard–Lindelöf / Grönwall, here through
`ODE_solution_unique_of_mem_Ioo`), the two orbits coincide on the common time interval.

This identification is the analytic content needed to recognise the variational linear map
of the *augmented* flow's central orbit as the variational linear map of the *original*
flow's orbit, so that `augFlow_snd_eq_variationalLinearMapAt` identifies
`(aΦ ⟨(x, id), t⟩).2` with the spatial piece of `fderiv ℝ Φ`. -/

section OrbitUniqueness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Orbit uniqueness for the original ODE.**

Two curves `y₁ y₂ : ℝ → E` that both solve the ODE `y'(t) = f t (y(t))` on an open interval
`Ioo a b ∋ t₀`, agree at `t₀`, and along which `f t` is uniformly `K`-Lipschitz (on the
ambient `univ`), coincide on `Ioo a b`.  This is `ODE_solution_unique_of_mem_Ioo` specialised
to the autonomous-in-form vector field `v t y := f t y`. -/
theorem orbit_unique_Ioo
    {a b : ℝ} {y₁ y₂ : ℝ → E} {K : ℝ≥0}
    (ht₀ : t₀ ∈ Ioo a b)
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (univ : Set E))
    (hy₁ : ∀ t ∈ Ioo a b, HasDerivAt y₁ (f t (y₁ t)) t)
    (hy₂ : ∀ t ∈ Ioo a b, HasDerivAt y₂ (f t (y₂ t)) t)
    (hinit : y₁ t₀ = y₂ t₀) :
    EqOn y₁ y₂ (Ioo a b) := by
  exact ODE_solution_unique_of_mem_Ioo (v := fun t y => f t y) (s := fun _ => univ) (K := K)
    hLip ht₀
    (fun t ht => ⟨hy₁ t ht, mem_univ _⟩)
    (fun t ht => ⟨hy₂ t ht, mem_univ _⟩)
    hinit

/-- **The augmented flow's first component is the original flow's orbit.**

Let `Φ` be a local flow of `f`, and `aΦ` a local flow of the augmented vector field
`augVF f` started at `(x, id)`.  Suppose:
* both flows are operative on a common open time interval `Ioo a b ∋ t₀`, contained in
  the respective closed time domains;
* `f t` is uniformly `K`-Lipschitz on `univ` for `t ∈ Ioo a b`;
* the initial spatial values agree: the augmented orbit starts at `(x, id)` and `x` is in
  the original flow's closed ball, and `(x, id)` is in the augmented flow's closed ball.

Then for every `t ∈ Ioo a b`, the first component of the augmented orbit equals the
original orbit: `(aΦ ⟨(x, id), t⟩).1 = Φ ⟨x, t⟩`. -/
theorem augFlow_fst_eq_flow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {p₀ : E × (E →L[ℝ] E)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augVF f) t₀ p₀ R tmin' tmax' aΦ)
    {a b : ℝ} {K : ℝ≥0} (ht₀ : t₀ ∈ Ioo a b)
    (ha_sub : Ioo a b ⊆ Icc tmin tmax) (ha_sub' : Ioo a b ⊆ Icc tmin' tmax')
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (univ : Set E))
    {x : E} (hx : x ∈ closedBall x₀ (r : ℝ))
    (hxp : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ)) :
    ∀ t ∈ Ioo a b, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 = Φ ⟨x, t⟩ := by
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  -- The two candidate orbits for the original ODE.
  set y₁ : ℝ → E := fun s => (aΦ ⟨p, s⟩).1 with hy₁_def
  set y₂ : ℝ → E := fun s => Φ ⟨x, s⟩ with hy₂_def
  -- `y₁` solves `y' = f t y`: it is the first component of the augmented orbit.
  have hy₁_deriv : ∀ t ∈ Ioo a b, HasDerivAt y₁ (f t (y₁ t)) t := by
    intro t ht
    -- The augmented orbit has the augmented-ODE derivative on `Icc tmin' tmax'`.
    have h_orbit := haΦ.hasDerivWithinAt p hxp t (ha_sub' ht)
    -- Project to the first component via the CLM `fst`.
    set fstCLM : (E × (E →L[ℝ] E)) →L[ℝ] E := ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)
    have h_fd := h_orbit.hasFDerivWithinAt
    have h_fst_at := (fstCLM.hasFDerivAt).comp_hasFDerivWithinAt t h_fd
    have heq : fstCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (augVF f t (aΦ ⟨p, t⟩)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augVF f t (aΦ ⟨p, t⟩)).1) := by
      apply ContinuousLinearMap.ext
      intro s
      change fstCLM (s • augVF f t (aΦ ⟨p, t⟩)) = s • (augVF f t (aΦ ⟨p, t⟩)).1
      change (s • augVF f t (aΦ ⟨p, t⟩)).1 = s • (augVF f t (aΦ ⟨p, t⟩)).1
      rfl
    rw [heq] at h_fst_at
    have h_aug_fst : (augVF f t (aΦ ⟨p, t⟩)).1 = f t (y₁ t) := rfl
    rw [h_aug_fst] at h_fst_at
    -- `h_fst_at : HasFDerivWithinAt (fstCLM ∘ fun s => aΦ ⟨p, s⟩) (toSpanSingleton (f t (y₁ t))) …`.
    -- The composed function is definitionally `y₁`, so this is `HasDerivWithinAt y₁ …`.
    have h_within : HasDerivWithinAt y₁ (f t (y₁ t)) (Icc tmin' tmax') t := by
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      exact h_fst_at
    exact (h_within.mono ha_sub').hasDerivAt (isOpen_Ioo.mem_nhds ht)
  -- `y₂` solves `y' = f t y`: it is the original orbit.
  have hy₂_deriv : ∀ t ∈ Ioo a b, HasDerivAt y₂ (f t (y₂ t)) t := by
    intro t ht
    have h_within := hΦ.hasDerivWithinAt x hx t (ha_sub ht)
    exact (h_within.mono ha_sub).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  -- Initial values agree at `t₀`: both equal `x`.
  have hinit : y₁ t₀ = y₂ t₀ := by
    have h1 : y₁ t₀ = x := by
      change (aΦ ⟨p, t₀⟩).1 = x
      rw [haΦ.apply_initial p hxp]
    have h2 : y₂ t₀ = x := by
      change Φ ⟨x, t₀⟩ = x
      exact hΦ.apply_initial x hx
    rw [h1, h2]
  exact orbit_unique_Ioo ht₀ hLip hy₁_deriv hy₂_deriv hinit

end OrbitUniqueness

/-! ## Invariance of the variational linear map under agreement of the central orbit

`variationalLinearMapAt` along a central orbit `α` depends on `α` only through the values
`α t` for `t ∈ Icc (t₀ - T) (t₀ + T)` (through the linearization `fderiv ℝ (f t) (α t)`).
Two orbits that agree on the closed interval therefore give the *same* variational linear
map at every interior time.  This is the bridge that lets `augFlow_fst_eq_flow` transport
the augmented flow's variational identification onto the original flow's orbit. -/

section VariationalLinearMapCongr

variable {f : ℝ → E → E} {α₁ α₂ : ℝ → E} {t₀ : ℝ}

/-- If two central orbits agree on `Icc (t₀ - T) (t₀ + T)`, an `IsVariationalSolutionOn`
along the first is an `IsVariationalSolutionOn` along the second. -/
theorem IsVariationalSolutionOn.congr_central
    {T : ℝ} {δ : E} {y : ℝ → E}
    (hαeq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    (hy : IsVariationalSolutionOn f α₁ δ t₀ y (Icc (t₀ - T) (t₀ + T))) :
    IsVariationalSolutionOn f α₂ δ t₀ y (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨hy.1, ?_⟩
  intro t ht
  have hd := hy.2 t ht
  rwa [hαeq ht] at hd

/-- **Congruence of the variational linear map under agreement of the central orbit.**

If `α₁ = α₂` on `Icc (t₀ - T) (t₀ + T)`, then the variational linear maps along the two
orbits agree at every `t` in the interval (with the bound/continuity data transported
across the agreement). -/
theorem variationalLinearMapAt_congr_central
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hαeq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    (hA_cont₁ : ContinuousOn (fun t => fderiv ℝ (f t) (α₁ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd₁ : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₁ t)‖ ≤ M)
    (hA_cont₂ : ContinuousOn (fun t => fderiv ℝ (f t) (α₂ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd₂ : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₂ t)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA_cont₁ hA_bd₁ ht
      = variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA_cont₂ hA_bd₂ ht := by
  -- Pointwise equality for every `δ`.
  apply ContinuousLinearMap.ext
  intro δ
  -- The two variational solutions agree by uniqueness along `α₂` (after transporting the
  -- `α₁`-solution).
  have h₁ := variationalSolutionFun_isSolution hT hM hMT hA_cont₁ hA_bd₁ δ
  have h₂ := variationalSolutionFun_isSolution hT hM hMT hA_cont₂ hA_bd₂ δ
  -- Transport `h₁` (a solution along `α₁`) to a solution along `α₂`.
  have h₁' : IsVariationalSolutionOn f α₂ δ t₀
      (variationalSolutionFun hT hM hMT hA_cont₁ hA_bd₁ δ) (Icc (t₀ - T) (t₀ + T)) :=
    IsVariationalSolutionOn.congr_central hαeq h₁
  -- Both are solutions along `α₂`; uniqueness gives agreement.
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont₂ h₁' h₂
  rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
  exact h_eq ht

end VariationalLinearMapCongr

/-! ## The spatial piece is the variational linear map along the orbit

Refining `fderiv_flow_eq_coprod_spatialPiece`, we expose directly that, at every interior
point `(x, t)`, the spatial piece of `fderiv ℝ Φ` *equals* the variational linear map along
the orbit `Φ ⟨x, ·⟩`, evaluated at time `t`.  This is the half-step needed to match it with
the augmented flow's second component. -/

section SpatialPieceVariational

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **The spatial piece is the variational linear map.**  Under the standard `C^1` flow
hypotheses, at every interior point `(x, t)`, `spatialPieceFn Φ (x, t)` equals the
variational linear map along the orbit `Φ ⟨x, ·⟩` evaluated at `t`. -/
theorem spatialPieceFn_eq_variationalLinearMapAt
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    spatialPieceFn Φ (x, t)
      = variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀) hT hM hMT
          (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
              rw [mem_closedBall] at hx; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
            (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub)
          (fun τ hτ => hA_bd x hx τ hτ) (Ioo_subset_Icc_self ht) := by
  have hfd_at := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx ht
  have hfd_eq := hfd_at.fderiv
  rw [spatialPieceFn_apply, hfd_eq]
  exact ContinuousLinearMap.coprod_comp_inl _ _

end SpatialPieceVariational

/-! ## Pointwise identification: spatial piece equals the augmented-flow projection

Combining the four analytic pieces — the spatial-piece/variational-map equality, the
augmented-flow second-component identification, the orbit-uniqueness, and the
variational-map congruence — we obtain, at every interior point `(x, t)`,
`spatialPieceFn Φ (x, t) = fromAugFlow aΦ (x, t)`, provided `aΦ` is a local flow of the
augmented vector field `augVF f` whose closed domain covers the orbit data.

The augmented flow `aΦ` is a *genuine* datum (constructed by Picard–Lindelöf via
`exists_isLocalFlow_of_contDiffOn_univ` for the `C^k` field `augVF f`); supplying it is not
a packaging of the conclusion — its type `IsLocalFlow (augVF f) …` is unrelated to the
`ContDiffOn` conclusion. -/

section SpatialPieceAugFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Pointwise identification of the spatial piece with the augmented-flow projection.**

Let `Φ` be a local flow of `f` and `aΦ` a local flow of `augVF f` centred at `(x₀, id)`.
On a strictly-interior open time interval `Ioo (t₀ - T) (t₀ + T)` and spatial ball
`closedBall x₀ ρ`, where:
* `f` is `C^1`, `f t` is uniformly `K`-Lipschitz on a slightly larger open time interval;
* the closed time interval is covered by both flow domains and the original `Icc tmin tmax`;
* the spatial ball is inside both the flow's `closedBall x₀ r` (with the recentring slack
  `r'`) and the augmented flow's `closedBall (x₀, id) R`;
* a uniform linearization bound `M` holds along the orbits,

then at every `(x, t)` with `x ∈ closedBall x₀ ρ` and `t ∈ Ioo (t₀ - T) (t₀ + T)`,
`spatialPieceFn Φ (x, t) = fromAugFlow aΦ (x, t)`. -/
theorem spatialPieceFn_eq_fromAugFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax' aΦ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T T' M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hTT' : T < T')
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax)
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (univ : Set E))
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    spatialPieceFn Φ (x, t) = fromAugFlow aΦ (x, t) := by
  -- Auxiliary memberships.
  have hx_le : dist x x₀ ≤ (ρ : ℝ) := by rw [mem_closedBall] at hx; exact hx
  have hx_r : x ∈ closedBall x₀ (r : ℝ) :=
    mem_closedBall.mpr (by linarith [r'.coe_nonneg])
  -- `(x, id) ∈ closedBall (x₀, id) R`.
  have hxp : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall (x₀, ContinuousLinearMap.id ℝ E) (R : ℝ) := by
    rw [mem_closedBall, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist x x₀ ≤ (ρ : ℝ) := hx_le
      _ ≤ (R : ℝ) := hρR
  -- Central orbits.
  set α₁ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα₁_def
  set α₂ : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 with hα₂_def
  -- Orbit uniqueness on the larger open interval, restricted to the closed interval.
  have ht₀_O : t₀ ∈ Ioo (t₀ - T') (t₀ + T') := ⟨by linarith, by linarith⟩
  have h_orbit_eq : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'), α₂ s = α₁ s :=
    augFlow_fst_eq_flow hΦ haΦ ht₀_O hsubO hsubO' hLip hx_r hxp
  have hαeq : EqOn α₂ α₁ (Icc (t₀ - T) (t₀ + T)) := by
    intro s hs
    have hs_O : s ∈ Ioo (t₀ - T') (t₀ + T') :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact h_orbit_eq s hs_O
  -- Step 1: spatial piece equals variational map along `α₁`.
  have h_sp := spatialPieceFn_eq_variationalLinearMapAt hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx ht
  -- Continuity / bound data along `α₁` (= the recentred-orbit data).
  set hA_cont₁ : ContinuousOn (fun s => fderiv ℝ (f s) (α₁ s)) (Icc (t₀ - T) (t₀ + T)) :=
    (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
        rw [mem_closedBall] at hx; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
      (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub) with hA_cont₁_def
  set hA_bd₁ : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f s) (α₁ s)‖ ≤ M :=
    (fun τ hτ => hA_bd x hx τ hτ) with hA_bd₁_def
  -- Continuity / bound data along `α₂` (transported from `α₁` via `hαeq`).
  have hA_cont₂ : ContinuousOn (fun s => fderiv ℝ (f s) (α₂ s)) (Icc (t₀ - T) (t₀ + T)) := by
    apply hA_cont₁.congr
    intro s hs
    change fderiv ℝ (f s) (α₂ s) = fderiv ℝ (f s) (α₁ s)
    rw [hαeq hs]
  have hA_bd₂ : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f s) (α₂ s)‖ ≤ M := by
    intro s hs
    change ‖fderiv ℝ (f s) (α₂ s)‖ ≤ M
    rw [hαeq hs]
    exact hA_bd₁ s hs
  -- Step 2: augmented-flow second component equals variational map along `α₂`.
  have h_aug := augFlow_snd_eq_variationalLinearMapAt haΦ hT hM hMT hsub'
    hxp hA_cont₂ hA_bd₂ (Ioo_subset_Icc_self ht)
  -- Step 3: the two variational maps agree (same orbit on the interval).
  have h_congr := variationalLinearMapAt_congr_central hT hM hMT hαeq
    hA_cont₂ hA_bd₂ hA_cont₁ hA_bd₁ (Ioo_subset_Icc_self ht)
  -- Assemble.
  rw [fromAugFlow_apply]
  rw [h_sp]
  -- `h_sp` rewrote `spatialPieceFn Φ (x, t)` to the variational map along `α₁`.
  -- `h_aug` says `(aΦ ⟨(x, id), t⟩).2 = variationalLinearMapAt(α₂)`.
  -- `h_congr` says `variationalLinearMapAt(α₂) = variationalLinearMapAt(α₁)`.
  rw [h_aug, h_congr]

end SpatialPieceAugFlow

/-! ## Joint `C^k` smoothness of the variational linear map

Putting the pointwise identification together with `contDiffOn_fromAugFlow`, we obtain the
headline: the spatial piece `spatialPieceFn Φ` (the variational linear map) is jointly `C^k`
on the strictly-interior open neighbourhood, provided a *jointly `C^k`* local flow `aΦ` of
the augmented vector field `augVF f` is available on a neighbourhood covering the orbit data.

The augmented flow `aΦ` and its `C^k` regularity are the genuine datum delivered by the
strong induction: `augVF f` is `C^k` whenever `f` is `C^{k+1}` (`augVF_uncurry_contDiff`),
and the inductive hypothesis — the flow of a `C^k` field is `C^k` — applied to `augVF f`
produces a `C^k` flow `aΦ`. -/

section VariationalLinearMapSmooth

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Joint `C^k` smoothness of the variational linear map (augmented-flow form).**

Let `Φ` be a local flow of `f`, and `aΦ` a *jointly `C^k`* local flow of the augmented
vector field `augVF f` centred at `(x₀, id)`, on an open neighbourhood `Ω` covering the
embedded orbit data.  Then `spatialPieceFn Φ` — the spatial piece of `fderiv ℝ Φ`, i.e. the
variational linear map — is jointly `C^k` on the strictly-interior open neighbourhood
`ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem contDiffOn_variationalLinearMap
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax' aΦ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    {T T' M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hTT' : T < T')
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax)
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (univ : Set E))
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ k (spatialPieceFn Φ) ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- `fromAugFlow aΦ` is `C^k` on the neighbourhood.
  have h_fromAug_Ck : ContDiffOn ℝ k (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugFlow haΦ_Ck hmap
  -- `spatialPieceFn Φ` agrees with `fromAugFlow aΦ` on the neighbourhood.
  have h_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      spatialPieceFn Φ q = fromAugFlow aΦ q := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    rw [mem_ball] at hq_x
    obtain ⟨x, t⟩ := q
    have hx_cb : x ∈ closedBall x₀ (ρ : ℝ) := mem_closedBall.mpr (le_of_lt hq_x)
    exact spatialPieceFn_eq_fromAugFlow hΦ haΦ hf_C1 hT hM hMT hTT' hsub hsub' hsubO hsubO'
      hLip hr' hρρ' hρR hA_bd hx_cb hq_t
  exact h_fromAug_Ck.congr h_eq

/-- **The inductive step, driven by a `C^k` augmented flow.**

If `Φ` is the local flow of a `C^{k+1}` field `f`, is already jointly `C^k` on the
strictly-interior neighbourhood, and a *jointly `C^k`* augmented flow `aΦ` of `augVF f`
covering the orbit data is available, then `Φ` is jointly `C^{k+1}`.

This is the `n → n + 1` step of the strong induction: it converts the inductive hypothesis
applied to `augVF f` (giving the `C^k` augmented flow `aΦ`) into the next regularity level
for `Φ`.  The variational-flow projection is built from `spatialPieceFn Φ`, whose
smoothness is `contDiffOn_variationalLinearMap` and whose coproduct identity is
`fderiv_flow_eq_coprod_spatialPiece`. -/
theorem contDiffOn_flow_succ_via_augFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax' aΦ)
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T T' M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1) (hT_lt' : T < T') (hTT'_out : T' ≤ T_out)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (univ : Set E))
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- `f` is `C^1`.
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact zero_le _
      exact_mod_cast this
    have h := hf_succ.of_le h_le
    simpa using h
  -- Inner-interval facts.
  have hT_pos : 0 < T := hT
  have hsub_T : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_T_tmax : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax := hsub_T.trans hsub
  have hsubO_tmax : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax := by
    intro s hs
    exact hsub (Icc_subset_Icc (by linarith [hs.1]) (by linarith [hs.2]) (Ioo_subset_Icc_self hs))
  -- `M * T < 1`.
  have hMT : M * T < 1 := lt_of_le_of_lt (by nlinarith [hM, le_of_lt hT_lt_mid]) hMT_mid
  -- `hA_bd` restricted to the inner ball / inner interval (along orbits of `Φ`).
  have hA_bd_inner : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
    intro x hx τ hτ
    refine hA_bd x ?_ τ (hsub_T hτ)
    exact closedBall_subset_closedBall
      (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hx
  -- `ρ + r' ≤ r` (from `ρ < ρ_mid` and `ρ_mid + r' ≤ r`).
  have hρρ'_inner : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by
    have := hρ_lt_mid; linarith
  -- Spatial-piece smoothness via the augmented flow.
  have hLsp_Ck : ContDiffOn ℝ k (spatialPieceFn Φ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_variationalLinearMap hΦ haΦ hf_C1 haΦ_Ck hT hM hMT hT_lt' hsub_T_tmax hsub'
      hsubO_tmax hsubO' hLip hr' hρρ'_inner hρR hmap hA_bd_inner
  -- Coproduct identity for the spatial piece.
  have hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) :=
    fderiv_flow_eq_coprod_spatialPiece hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  -- Plug into the recursive flow step.
  exact contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hLsp_Ck hLsp_eq

end VariationalLinearMapSmooth

/-! ## Unconditional `C^1` flow regularity (existence form)

Combining the nesting/bound-data derivation (`exists_flow_nesting_data`) with the
unconditional `C^1` flow theorem (`exists_contDiffOn_flow_of_contDiff`), we obtain the
fully unconditional `C^1` local-flow regularity statement in finite dimensions: from a bare
local flow `Φ` of a jointly `C^1` field, with `t₀` strictly interior in the flow's time
domain and a non-degenerate flow ball, the flow is jointly `C^1` on an open neighbourhood of
`(x₀, t₀)`.  No bound, nesting, or Lipschitz data is required as input — it is all produced
internally from compactness of closed balls. -/

section UnconditionalC1

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Unconditional `C^1` flow regularity (existence form).**

In finite dimensions, a local flow `Φ` of a jointly `C^1` field `f` is jointly `C^1` on an
open neighbourhood of `(x₀, t₀)`, with all bound/nesting data derived internally.  The two
genuine non-degeneracy requirements are that `t₀` lie strictly interior in `Icc tmin tmax`
(a two-sided time neighbourhood is impossible at a boundary time) and that the flow ball be
non-degenerate (`0 < r`). -/
theorem exists_contDiffOn_flow_C1 [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ 1 Φ U := by
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r',
    hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid, hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out,
    hρρ', hρ_out_le_r, hsub, hA_bd⟩ := exists_flow_nesting_data hΦ hf ht₀ hr_pos
  exact exists_contDiffOn_flow_of_contDiff hΦ (le_refl 1) hf hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

end UnconditionalC1

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
