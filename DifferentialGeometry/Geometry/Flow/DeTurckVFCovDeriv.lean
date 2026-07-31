import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace

/-!
# The covariant derivative of the DeTurck vector field

The DeTurck vector field `W = deTurckVF g g_bg` is the `g`-cometric trace of the
connection-difference tensor `A = connDiff g g_bg`.  Because `∇^{g} g = 0`, and hence
`∇^{g} g^{-1} = 0`, differentiating the trace with `∇^{g}` commutes with the contraction:
$$
  \nabla^{g}_v W \;=\; \operatorname{tr}_g \bigl(\nabla^{g}_v A\bigr).
$$

This file proves that identity, in the frame currency the rest of the tree uses, and the
frame linear algebra it rests on.

## Main results

* `orthoFrame_expand` — Parseval expansion `u = ∑ᵢ g(u, Bᵢ) • Bᵢ` of a tangent vector in a
  `g_x`-orthonormal frame.
* `frameDiag_indep` — the diagonal frame trace `∑ᵢ A(Bᵢ, Bᵢ)` of a vector-valued bilinear map
  is independent of the `g_x`-orthonormal frame.
* `deTurckVF_frame_trace` — consequently the DeTurck vector field is the diagonal trace of
  `connDiff g g_bg` against *any* `g_x`-orthonormal frame, not only the `x`-centred
  `smoothOrthoFrame g x`.
* `frameCorr_vanish` — the moving-frame correction `∑ᵢ A(∇_v Bᵢ, Bᵢ)` vanishes, by the
  skew-symmetry of the connection one-form on a `g`-orthonormal frame
  (`smoothOrthoFrame_cov_skew`) paired with the symmetry of `A` (`connDiff_symm`).
* `deTurckVF_covDeriv_eq` — the identity above, with the right-hand side already converted by
  `connDiff_outerCovDeriv_eq` into the *background* covariant derivative
  `covDerivConnDiff g_bg g` plus a quadratic `A · A` remainder.  Both pieces are exactly the
  objects the `Λ`-class jet-envelope bounds control.

## Convention

`connDiff g g' x w v = ∇^{g}_v w - ∇^{g'}_v w` — first argument the differentiated section
value, second the direction (the project's `connDiff` argument order).  The frame
`Bᵢ = smoothOrthoFrame g x i` is a *smooth section*, `g_y`-orthonormal for every `y` in its
orthonormality neighbourhood `smoothOrthoFrameNbhd x`, so it can be differentiated.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Frame linear algebra -/

set_option linter.unusedSectionVars false in
/-- **Parseval expansion in a `g_x`-orthonormal frame.**  A tangent vector is recovered from
its `g_x`-inner products against a `g_x`-orthonormal frame `B`. -/
theorem orthoFrame_expand (g : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E), g.inner x u (B i) • B i := by
  classical
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i => g.inner x u (B i) with hc
  set S : TangentSpace I x := ∑ i, c i • B i with hS
  have hsecond : ∀ w : TangentSpace I x,
      g.inner x w S = ∑ i, c i * g.inner x w (B i) := by
    intro w
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have hfirst : ∀ w : TangentSpace I x,
      g.inner x S w = ∑ i, c i * g.inner x (B i) w := by
    intro w
    rw [hS, map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have huu : g.inner x u u = ∑ i, c i * c i := by
    rw [g_inner_eq_orthonormal_parseval_sum (I := I) g x u u B hB]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]; rw [g.symm x (B i) u]
  have huS : g.inner x u S = ∑ i, c i * c i := by
    rw [hsecond u]
  have hSu : g.inner x S u = ∑ i, c i * c i := by
    rw [hfirst u]
    exact Finset.sum_congr rfl fun i _ => by rw [g.symm x (B i) u]
  have hBS : ∀ i, g.inner x (B i) S = c i := by
    intro i
    rw [hsecond (B i)]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hB i j]; split_ifs <;> simp :
      ∀ j ∈ Finset.univ, c j * g.inner x (B i) (B j) =
        if i = j then c j else 0)]
    simp
  have hSS : g.inner x S S = ∑ i, c i * c i := by
    rw [hfirst S]
    exact Finset.sum_congr rfl fun i _ => by rw [hBS i]
  have hlin : ∀ w : TangentSpace I x,
      g.inner x (u - S) w = g.inner x u w - g.inner x S w := by
    intro w
    rw [map_sub (g.inner x) u S, ContinuousLinearMap.sub_apply]
  have hzero : g.inner x (u - S) (u - S) = 0 := by
    rw [map_sub (g.inner x (u - S)) u S, hlin u, hlin S, huu, huS, hSu, hSS]
    ring
  by_contra hne
  have hsub : u - S ≠ 0 := sub_ne_zero.mpr hne
  have := g.pos x (u - S) hsub
  rw [hzero] at this
  exact lt_irrefl 0 this

set_option linter.unusedSectionVars false in
/-- **Frame-independence of the diagonal trace.**  For a vector-valued continuous bilinear map
`A` on `T_x M`, the diagonal sum `∑ᵢ A(Bᵢ, Bᵢ)` over a `g_x`-orthonormal frame is the
`g`-cometric contraction of `A`, hence independent of the chosen frame. -/
theorem frameDiag_indep (g : SmoothRiemannianMetric I M) (x : M)
    (B B' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hB' : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B' i) (B' j) = if i = j then (1 : ℝ) else 0)
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E), A (B i) (B i) =
      ∑ j : Fin (Module.finrank ℝ E), A (B' j) (B' j) := by
  classical
  have key : ∀ u₁ u₂ : TangentSpace I x, A u₁ u₂ =
      ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (g.inner x u₁ (B' j) * g.inner x u₂ (B' k)) • A (B' j) (B' k) := by
    intro u₁ u₂
    conv_lhs => rw [orthoFrame_expand (I := I) g x B' hB' u₁,
      orthoFrame_expand (I := I) g x B' hB' u₂]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_sum, ContinuousLinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_smul, mul_comm]
  have hcoef : ∀ j k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        g.inner x (B i) (B' j) * g.inner x (B i) (B' k)) =
      (if j = k then (1 : ℝ) else 0) := by
    intro j k
    rw [← hB' j k, g_inner_eq_orthonormal_parseval_sum (I := I) g x (B' j) (B' k) B hB]
    exact Finset.sum_congr rfl fun i _ => by
      rw [g.symm x (B' j) (B i), g.symm x (B i) (B' k)]
  rw [Finset.sum_congr rfl (fun i _ => key (B i) (B i)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (B i) (B' j) * g.inner x (B i) (B' k)) • A (B' j) (B' k)) =
      (if j = k then (1 : ℝ) else 0) • A (B' j) (B' k) := by
    intro j
    rw [← Finset.sum_smul, hcoef j k]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  simp

set_option linter.unusedSectionVars false in
/-- **The DeTurck vector field as the diagonal trace against an arbitrary orthonormal frame.**

Generalisation of `deTurckVF_eq_orthoFrame_trace` from the `x`-centred smooth orthonormal
frame to any `g_x`-orthonormal family: `W(x) = ∑ᵢ A(Bᵢ, Bᵢ)` with `A = connDiff g g_bg x`.
This is what makes the *frozen* (`x`-centred) frame usable at nearby points. -/
theorem deTurckVF_frame_trace (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    (deTurckVF (I := I) g g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i : Fin (Module.finrank ℝ E), connDiff (I := I) g g_bg x (B i) (B i) := by
  rw [deTurckVF_eq_orthoFrame_trace (I := I) g g_bg x]
  exact frameDiag_indep (I := I) g x
    (fun i => smoothOrthoFrame (I := I) g x i x) B
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j) hB
    (connDiff (I := I) g g_bg x)

/-! ## The moving-frame correction -/

set_option linter.unusedSectionVars false in
/-- **A skew family paired diagonally against a symmetric bilinear map vanishes.**

If `D` pairs skew-symmetrically with a `g_x`-orthonormal frame `B`
(`g(Dᵢ, Bⱼ) = − g(Dⱼ, Bᵢ)`) and `A` is symmetric, then `∑ᵢ A(Dᵢ, Bᵢ) = 0`: expanding `Dᵢ`
in the frame turns the sum into a skew ⊗ symmetric contraction. -/
private theorem skewDiag_zero (g : SmoothRiemannianMetric I M) (x : M)
    (B D : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hskew : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (D i) (B j) = - g.inner x (D j) (B i))
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hA : ∀ u w : TangentSpace I x, A u w = A w u) :
    ∑ i : Fin (Module.finrank ℝ E), A (D i) (B i) = 0 := by
  classical
  have hexp : ∑ i : Fin (Module.finrank ℝ E), A (D i) (B i)
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          g.inner x (D i) (B j) • A (B j) (B i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [orthoFrame_expand (I := I) g x B hB (D i)]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, ContinuousLinearMap.smul_apply]
  have hflip : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (D i) (B j) • A (B j) (B i))
      = - ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          g.inner x (D i) (B j) • A (B j) (B i) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          g.inner x (D b) (B a) • A (B a) (B b))
        = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (- g.inner x (D a) (B b)) • A (B b) (B a) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hskew b a, hA (B a) (B b)]]
    simp only [neg_smul, Finset.sum_neg_distrib]
  rw [hexp]
  have h2 : (2 : ℝ) • (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g.inner x (D i) (B j) • A (B j) (B i)) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hflip]
    exact add_neg_cancel _
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact h

set_option linter.unusedSectionVars false in
/-- **The moving-frame correction vanishes.**

For the smooth `g`-orthonormal frame `Bᵢ = smoothOrthoFrame g x i`, the diagonal contraction
of the connection-difference tensor against the frame's own covariant derivative vanishes:
```
∑ᵢ A(∇^{g}_v Bᵢ, Bᵢ) = 0,   A = connDiff g g_bg.
```
The frame one-form `g(∇_v Bᵢ, Bⱼ)` is skew (`smoothOrthoFrame_cov_skew`, i.e. `∇^{g} g = 0`
read on the frame) while `A` is symmetric (`connDiff_symm`, torsion-freeness of both
Levi-Civita connections).  This is what makes `∇^{g}` commute with the `g`-trace. -/
theorem frameCorr_vanish (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        connDiff (I := I) g g_bg x
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x i x) = 0 :=
  skewDiag_zero (I := I) g x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
    (fun i j => by
      rw [smoothOrthoFrame_cov_skew (I := I) g x i j v]
      exact congrArg Neg.neg (g.symm x _ _))
    (connDiff (I := I) g g_bg x)
    (fun u w => connDiff_symm (I := I) g g_bg x u w)

/-! ## Covariant differentiation through a finite sum of sections -/

set_option linter.unusedSectionVars false in
/-- A covariant derivative distributes over a finite sum of smooth sections. -/
private theorem cov_sum (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {ι : Type*} (σ : ι → Π b : M, TangentSpace I b)
    (hσ : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (σ i))) (s : Finset ι) (x : M) :
    cov.toFun (fun b : M => ∑ i ∈ s, σ i b) x = ∑ i ∈ s, cov.toFun (σ i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact congrFun (CovariantDerivative.zero cov) x
  · intro a t ha ih
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => ∑ i ∈ t, σ i b)) :=
      ContMDiff.sum_section (fun i _ => hσ i)
    have hstep : (fun b : M => ∑ i ∈ insert a t, σ i b)
        = σ a + (fun b : M => ∑ i ∈ t, σ i b) := by
      funext b
      rw [Finset.sum_insert ha]
      rfl
    rw [hstep, cov.isCovariantDerivativeOnUniv.add ((hσ a x).mdifferentiableAt (by simp))
      ((hsm x).mdifferentiableAt (by simp)) (Set.mem_univ x), ih, Finset.sum_insert ha]

/-! ## The covariant derivative of the DeTurck vector field -/

set_option linter.unusedSectionVars false in
/-- **`∇^{g}` commutes with the `g`-trace defining the DeTurck vector field.**

Write `A = connDiff g g_bg`, `W = deTurckVF g g_bg` and `Bᵢ = smoothOrthoFrame g x i`.  Since
`W = tr_g A` and `∇^{g} g^{-1} = 0`, the `g`-covariant derivative of `W` is the `g`-trace of
`∇^{g} A`; and `connDiff_outerCovDeriv_eq` rewrites `∇^{g}A` as the *background* derivative
`∇^{g_bg} A = covDerivConnDiff g_bg g` plus the quadratic `A · A` action.  Hence
$$
  \nabla^{g}_v W \;=\; \sum_i \Bigl[(\nabla^{g_{bg}}_v A)(B_i, B_i)
    + A(A(B_i,B_i), v) - A(B_i, A(B_i, v)) - A(A(B_i, v), B_i)\Bigr].
$$
The moving-frame correction produced by differentiating the frame is discharged by
`frameCorr_vanish`.

Both right-hand-side ingredients are exactly what the `Λ`-class jet-envelope bounds
`unifCovConnDiffSup` and `unifConnDiffSup` control, so this is the identity that closes the
Lie half of the static Ricci–DeTurck field. -/
theorem deTurckVF_covDeriv_eq (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (covDerivConnDiff (I := I) g_bg g (smoothExtensionTangent (I := I) x v)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) x
          + (connDiff (I := I) g g_bg x
                (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x i x)) v
              - connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
              - connDiff (I := I) g g_bg x
                  (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
                  (smoothOrthoFrame (I := I) g x i x))) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hXx : smoothExtensionTangent (I := I) x v x = v :=
    smoothExtensionTangent_eq (I := I) x v
  have hBsm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hσsm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))) := fun i =>
    diffSec_contMDiff (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g) (hBsm i)
      (by simpa using hBsm i)
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b)) :=
    (deTurckVF (I := I) g g_bg).contMDiff
  have hSsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
        diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) b)) :=
    ContMDiff.sum_section (fun i _ => hσsm i)
  have hev : ∀ᶠ b in nhds x,
      (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b =
        ∑ i : Fin (Module.finrank ℝ E),
          diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) b := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with b hb
    rw [deTurckVF_frame_trace (I := I) g g_bg b
      (fun i => smoothOrthoFrame (I := I) g x i b)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hb i j)]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hcongr := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := fun b : M => (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b)
    (σ' := fun b : M => ∑ i : Fin (Module.finrank ℝ E),
      diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) b)
    ((hW x).mdifferentiableAt (by simp)) ((hSsm x).mdifferentiableAt (by simp))
    Filter.univ_mem hev
  rw [hcongr, cov_sum (I := I) (LeviCivita (I := I) g)
    (fun i : Fin (Module.finrank ℝ E) =>
      diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
    hσsm Finset.univ x, ContinuousLinearMap.sum_apply]
  have hper : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g).toFun
          (diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)) x v =
        (covDerivConnDiff (I := I) g_bg g (smoothExtensionTangent (I := I) x v)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) x
          + (connDiff (I := I) g g_bg x
                (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x i x)) v
              - connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
              - connDiff (I := I) g g_bg x
                  (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
                  (smoothOrthoFrame (I := I) g x i x)))
        + (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
              ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
            + connDiff (I := I) g g_bg x
                ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
                (smoothOrthoFrame (I := I) g x i x)) := by
    intro i
    have hkey := connDiff_outerCovDeriv_eq (I := I) g g_bg
      (X := smoothExtensionTangent (I := I) x v)
      (Y := smoothOrthoFrame (I := I) g x i) (Z := smoothOrthoFrame (I := I) g x i)
      (hBsm i) (hBsm i) x
    rw [hXx] at hkey
    have hcov : covApply (LeviCivita (I := I) g) (smoothExtensionTangent (I := I) x v)
        (smoothOrthoFrame (I := I) g x i) x =
        (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v := by
      rw [covApply_apply, hXx]
    rw [hcov] at hkey
    linear_combination (norm := abel) hkey
  have hcorr2 : ∑ i : Fin (Module.finrank ℝ E),
      connDiff (I := I) g g_bg x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
        (smoothOrthoFrame (I := I) g x i x) = 0 :=
    frameCorr_vanish (I := I) g g_bg x v
  have hcorr1 : ∑ i : Fin (Module.finrank ℝ E),
      connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v) = 0 := by
    rw [Finset.sum_congr rfl
      (fun i _ => connDiff_symm (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v))]
    exact hcorr2
  have hcorr : ∑ i : Fin (Module.finrank ℝ E),
      (connDiff (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
          + connDiff (I := I) g g_bg x
              ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x i x)) = 0 := by
    rw [Finset.sum_add_distrib, hcorr1, hcorr2, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_add_distrib,
    Finset.sum_add_distrib, hcorr, add_zero]

end DeTurck
end PDE
end DifferentialGeometry

end
