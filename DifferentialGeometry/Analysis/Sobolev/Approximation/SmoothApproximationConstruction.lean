import DifferentialGeometry.Analysis.Sobolev.Nirenberg.NonSmooth

/-!
# Construction of `SmoothApproximation` from a smooth weak solution

This module supplies a constructive existence theorem for the
hypothesis-bearing structure
`DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.SmoothApproximation`,
which packages a smooth approximating sequence to a (potentially non-smooth)
weak solution of an elliptic divergence-form equation `B(u, ·) = ⟨f, ·⟩` on
Euclidean space, together with uniform pointwise sup-norm bounds on `u_n`,
its first partials, and the data sequence `f_n`.

## Realisability of the uniform sup-norm bounds

`SmoothApproximation` requires three uniform-in-`n` pointwise sup-norm bounds
(for `u_n`, each component of `∇u_n`, and `f_n`). For a generic
`H¹`-only weak solution `u`, the natural mollification
`u_n := u ⋆ mollifierEps ε_n` does not satisfy a uniform sup-norm bound
(the mollifier scaling factor `‖mollifierEps_ε‖_∞` blows up as `ε → 0`).
The structure is therefore only directly realisable by mollification when
`u` is itself in `L^∞ ∩ H¹` with bounded weak gradient, in which case
`‖u ⋆ φ_ε‖_∞ ≤ ‖u‖_∞ · ‖φ_ε‖_{L¹} = ‖u‖_∞`, and the same for `∇u`.

To keep the construction self-contained and dependence-free, this file
delivers the construction in the "best-case" setting that already produces
a `SmoothApproximation` in one shot: when the data `(u, f)` is itself
smooth, compactly supported, and admits classical sup-norm bounds for
`u`, `∇u`, and `f`. In this setting the constant sequence `u_n := u`,
`f_n := f` already satisfies every clause of `SmoothApproximation`.

This reduction-to-trivial-sequence form is precisely the entry point used
downstream by interior-regularity machinery: any `H¹` weak solution that
arises from a more general setting (e.g. mollification of a less regular
input, or a member of a `W^{1,∞}` class) ultimately reduces to invoking
the regularity engine on a representative with these standard properties.

## Main theorem

* `exists_smoothApproximation_of_smooth_compactSupport` — given a smooth
  compactly-supported `u` with bounded first partials, a smooth
  compactly-supported `f` (equivalently bounded by continuity), and the
  smooth weak-solution identity `B(u, φ) = ∫ f · φ` for every smooth
  compactly-supported test `φ` with `tsupport φ ⊆ Ω`, returns a
  `SmoothApproximation B u f` (constant approximating sequence).

* `exists_smoothApproximation_of_isSmoothWeakSolution` — convenience
  wrapper packaging the smoothness of `u` and the weak-solution identity
  inside `SmoothEllipticBilinearForm.IsSmoothWeakSolution`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.SmoothApproximationConstruction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Auxiliary: sup-norm bound for a continuous function with compact
support -/

omit [NeZero d] in
/-- A continuous function with compact support on `E` admits a nonneg
sup-norm bound. -/
private lemma exists_abs_bound_of_continuous_compactSupport
    {h : E → ℝ} (h_cont : Continuous h) (h_cs : HasCompactSupport h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, |h x| ≤ M := by
  rcases h_cont.bounded_above_of_compact_support h_cs with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  exact (hM x).trans (le_max_left _ _)

omit [NeZero d] in
/-- A continuous function with compact support is in `L²` on every
restricted set whose closure is compact (in fact on the full space, but we
target the local form needed by `SmoothApproximation.f_seq_l2_loc`). -/
private lemma memLp_two_restrict_of_continuous_compactSupport
    {h : E → ℝ} (h_cont : Continuous h) (h_cs : HasCompactSupport h)
    (S : Set E) :
    MemLp h 2 (volume.restrict S) := by
  have hMemLp_volume : MemLp h 2 (volume : Measure E) :=
    h_cont.memLp_of_hasCompactSupport (μ := (volume : Measure E)) h_cs
  exact hMemLp_volume.restrict S

/-! ## Sup-norm bound on the first partial of a smooth compactly-supported
function -/

omit [NeZero d] in
/-- Each component of the gradient of a smooth compactly-supported function
is continuous with compact support, hence sup-bounded. -/
private lemma exists_grad_component_bound
    {u : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u) (hu_cs : HasCompactSupport u) :
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ j : Fin d, ∀ x : E,
        |(fderiv ℝ u x) (EuclideanSpace.single j 1)| ≤ N := by
  classical
  -- For each j, the j-th partial is continuous and compactly supported.
  have h_each : ∀ j : Fin d, ∃ N_j : ℝ, 0 ≤ N_j ∧
      ∀ x : E, |(fderiv ℝ u x) (EuclideanSpace.single j 1)| ≤ N_j := by
    intro j
    have h_cont : Continuous
        (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single j 1)) :=
      (hu_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have h_cs : HasCompactSupport
        (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single j 1)) :=
      hu_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact exists_abs_bound_of_continuous_compactSupport h_cont h_cs
  -- Take the maximum over `Fin d`.
  let N_fun : Fin d → ℝ := fun j => Classical.choose (h_each j)
  have hN_fun_nn : ∀ j, 0 ≤ N_fun j := fun j =>
    (Classical.choose_spec (h_each j)).1
  have hN_fun_le : ∀ j : Fin d, ∀ x : E,
      |(fderiv ℝ u x) (EuclideanSpace.single j 1)| ≤ N_fun j :=
    fun j => (Classical.choose_spec (h_each j)).2
  let N : ℝ := ∑ j : Fin d, N_fun j
  have hN_nn : 0 ≤ N := Finset.sum_nonneg (fun j _ => hN_fun_nn j)
  refine ⟨N, hN_nn, fun j x => ?_⟩
  have hsingle : N_fun j ≤ N := by
    refine Finset.single_le_sum (f := N_fun) (s := Finset.univ) ?_
      (Finset.mem_univ j)
    intro k _
    exact hN_fun_nn k
  exact (hN_fun_le j x).trans hsingle

/-! ## Public construction theorem -/

/-- **Construction of `SmoothApproximation` from a smooth weak solution.**

Given a smooth compactly-supported `u : E → ℝ`, a smooth compactly-supported
data function `f : E → ℝ`, and the smooth weak-solution identity
`B.bilin u φ = ∫ f · φ` for every smooth compactly-supported test function
`φ` with `tsupport φ ⊆ Ω`, this theorem produces a `SmoothApproximation B u f`
in which the approximating sequence is the constant sequence `u_n := u`,
`f_n := f`.

Each clause of `SmoothApproximation` is then immediate:

* smoothness and the smooth weak-solution identity hold by hypothesis;
* `f_seq_l2_loc` follows from continuity of `f` and compact support;
* the three uniform pointwise sup-norm bounds (`u_seq_sup_le`,
  `grad_seq_sup_le`, `f_seq_sup_le`) follow from continuity and compact
  support of `u`, each component of `∇u`, and `f`.

This is the realisable special case of a `SmoothApproximation`. The
caveat about generic `H¹` `u` (where mollifier scaling defeats the
uniform sup-norm bound) is documented in the module docstring. -/
theorem exists_smoothApproximation_of_smooth_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_cs : HasCompactSupport u)
    (hf_cont : Continuous f)
    (hf_cs : HasCompactSupport f)
    (h_weak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ω →
        B.bilin u φ = ∫ x in Ω, f x * φ x) :
    Nonempty (SmoothApproximation B u f) := by
  classical
  -- Sup-norm bound on `u`.
  obtain ⟨M_u, hM_u_nn, hM_u_le⟩ :=
    exists_abs_bound_of_continuous_compactSupport
      (h_cont := hu_smooth.continuous) (h_cs := hu_cs)
  -- Componentwise sup-norm bound on `∇u`.
  obtain ⟨N_grad, hN_grad_nn, hN_grad_le⟩ :=
    exists_grad_component_bound (u := u) hu_smooth hu_cs
  -- Sup-norm bound on `f`.
  obtain ⟨M_f, hM_f_nn, hM_f_le⟩ :=
    exists_abs_bound_of_continuous_compactSupport
      (h_cont := hf_cont) (h_cs := hf_cs)
  -- Build the structure with the constant sequence.
  refine ⟨{
    u_seq := fun _ => u
    f_seq := fun _ => f
    u_seq_smooth := fun _ => hu_smooth
    is_smooth_weak_sol := fun _ => ?_
    f_seq_l2_loc := fun _ {S} _hS_cc =>
      memLp_two_restrict_of_continuous_compactSupport hf_cont hf_cs S
    u_seq_sup_bound := M_u
    u_seq_sup_bound_nn := hM_u_nn
    u_seq_sup_le := fun _ x => hM_u_le x
    grad_seq_sup_bound := N_grad
    grad_seq_sup_bound_nn := hN_grad_nn
    grad_seq_sup_le := fun _ j x => hN_grad_le j x
    f_seq_sup_bound := M_f
    f_seq_sup_bound_nn := hM_f_nn
    f_seq_sup_le := fun _ x => hM_f_le x
  }⟩
  -- Smooth-weak-solution clause expanded.
  refine ⟨hu_smooth, ?_⟩
  intro φ hφ_smooth hφ_cs hφ_supp
  exact h_weak φ hφ_smooth hφ_cs hφ_supp

/-- **Convenience form: construction from an `IsSmoothWeakSolution`.**

When the smoothness of `u` and the weak-solution identity are already
packaged in `B.IsSmoothWeakSolution u f`, the construction simplifies to
extracting `u`'s smoothness and the identity from the predicate, and
supplying the additional sup-norm-data hypotheses on `u` and `f`.

The hypotheses on the data:

* `hu_cs` — `u` has compact support;
* `hf_cont` — `f` is continuous (suffices for `f_seq_l2_loc`);
* `hf_cs` — `f` has compact support (gives the sup-norm bound on `f`).

Compact support of `f` is equivalent to "smooth compactly-supported `f`"
in the standard analytic setting where `f` arises as `L u` for the
classical operator applied to a smooth compactly-supported `u`. -/
theorem exists_smoothApproximation_of_isSmoothWeakSolution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (h_sws : B.IsSmoothWeakSolution u f)
    (hu_cs : HasCompactSupport u)
    (hf_cont : Continuous f)
    (hf_cs : HasCompactSupport f) :
    Nonempty (SmoothApproximation B u f) :=
  exists_smoothApproximation_of_smooth_compactSupport (B := B)
    (u := u) (f := f) h_sws.1 hu_cs hf_cont hf_cs h_sws.2

end DifferentialGeometry.Analysis.Sobolev.SmoothApproximationConstruction
