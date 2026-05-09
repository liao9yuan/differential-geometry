import DifferentialGeometry.Integral.Connection.Bochner

/-!
# Concrete pointwise Bochner-Weitzenböck identity, unconditional form

The companion `Connection.Bochner` derives the **fully unconditional** abstract pointwise
Bochner-Weitzenböck identity for a smooth scalar function on a smooth boundaryless
Riemannian manifold:
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$

This file produces the **concrete** pointwise Bochner-Weitzenböck identity in the
right-hand-side form expected by the Integral / Analysis / PDE layer, multiplying by `2`:
$$
  \Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    2\,|\nabla^2 f|_g^2(x) +
    2\,\mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    2\,g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr).
$$

The Frobenius norm squared is realised in two equivalent forms:

* `frobeniusSq_grad_vector g (∇f) x` — the orthonormal-frame trace produced by the
  abstract Bochner identity, summing `g(LC^∇(∇f) B_i, LC^∇(∇f) B_i)` over a
  `g_x`-orthonormal frame at `x`. This is the form natively output by
  `bochner_pointwise_abstract_unconditional`.
* `chartHessFrobeniusSq g f x` — the chart-coordinate metric Frobenius squared, which is
  the geometer's basis-independent expression `∑_{ijkl} G^{ik} G^{jl} H_{ij} H_{kl}`.

We prove these two are equal pointwise (`frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`)
by combining the orthonormal-frame trace identity `orthonormal_basis_bilin_trace`
applied to the bilinear form `(z, w) ↦ g(LC z, LC w)` with the chart-Hessian-matrix
identity `chartHessianMatrixIdentity_holds` and a model-basis decomposition for the
Hessian carrier `LC e_l = ∑_n (b.repr (LC e_l) n) • e_n`.

The Ricci pairing is left in its abstract form `ricciTensor g x (∇f) (∇f)`. Identifying
this with the chart-coordinate metric Ricci pairing `chartRicciOnGradF g f x` requires a
basis-coordinate identification of the abstract Riemann CLM with the chart Riemann
tensor — itself a separate chart-Christoffel computation; in this file we keep
`ricciTensor` as the abstract carrier.

## Main results

* `frobeniusSq_grad_vector_eq_chartHessFrobeniusSq` — unconditional identity bridging the
  orthonormal-frame Frobenius squared `frobeniusSq_grad_vector g (∇f) x` to the
  chart-coordinate metric Frobenius squared `chartHessFrobeniusSq g f x`.
* `bochner_pointwise_concrete_unconditional` — unconditional pointwise Bochner identity,
  using the orthonormal-frame Frobenius squared and the abstract Ricci tensor.
* `bochner_pointwise_concrete_metric_unconditional` — unconditional metric form, using
  the chart-coordinate metric Frobenius squared and the abstract Ricci tensor.

Both unconditional theorems carry no hypotheses beyond `[I.Boundaryless]`,
`[T2Space M]`, and `[SigmaCompactSpace M]` (the closed-manifold standard package).
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Helper: Hilbert-Schmidt-type contraction in the model basis

Apply `orthonormal_basis_bilin_trace` to the bilinear form `(z, w) ↦ g(T(z), T(w))`. -/

/-- For a continuous linear self-map `T : T_x M →L T_x M` and any `g_x`-orthonormal
frame `B`, the orthonormal-frame Hilbert-Schmidt norm squared equals the inverse Gram
contraction of `g(T(e_k), T(e_l))`:
$$
  \sum_i g_x(T(B_i), T(B_i)) =
    \sum_{kl} G^{kl}(x, x)\, g_x(T(e_k), T(e_l)).
$$
-/
private theorem sum_g_inner_T_self_eq_invGram_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TangentSpace I x →L[ℝ] TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (T (B i)) (T (B i)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T ((Module.finBasis ℝ E) k))
              (T ((Module.finBasis ℝ E) l)) := by
  classical
  -- Define Hb(z, w) := g.inner x (T z) (T w) as a continuous bilinear form.
  set Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    (((g.inner x).comp T).flip.comp T).flip with hHb_def
  -- Application formula.
  have hHb_apply : ∀ z w : TangentSpace I x,
      Hb z w = g.inner x (T z) (T w) := by
    intro z w
    change (((g.inner x).comp T).flip.comp T).flip z w =
      g.inner x (T z) (T w)
    rw [ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_apply]
  -- Apply orthonormal_basis_bilin_trace.
  have htrace := orthonormal_basis_bilin_trace (I := I) g x Hb B hB
  -- htrace : ∑ i, Hb (B i) (B i) = ∑ k l, G^{kl} * Hb e_k e_l.
  -- Rewrite both sides via hHb_apply.
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g.inner x (T (B i)) (T (B i))) =
        ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (B i) (B i)).symm)]
  rw [htrace]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [hHb_apply]

/-! ## Helper: model-basis decomposition for `g.inner x v`

For any tangent vector `v` and model-basis index `n`, the inner product
`g.inner x v (b n)` decomposes as a sum of model-basis components weighted by the Gram
matrix. From this we derive that the model-basis component of `v` (i.e., `b.repr v n`)
admits an inverse-Gram-weighted formula: `b.repr v n = ∑_m G^{nm} g.inner x v (b m)`. -/

/-- The metric inner product on the model basis equals the chart Gram matrix entry. -/
private lemma g_inner_modelBasis_eq_chartGram
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j) =
      chartGramMatrix (I := I) g x x i j := by
  classical
  rw [chartGramMatrix_apply]
  rw [chartBasisVecFiber_self (I := I) x i]
  rw [chartBasisVecFiber_self (I := I) x j]

/-- For any tangent vector `v ∈ T_x M`, decomposed in the model basis as
`v = ∑_p (b.repr v) p • b p`, the inner product `g.inner x v (b n)` equals
`∑_p (b.repr v) p * G_{pn}`. -/
private lemma g_inner_modelBasis_first_decomp
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (n : Fin (Module.finrank ℝ E)) :
    g.inner x v ((Module.finBasis ℝ E) n) =
      ∑ p : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr v p *
          chartGramMatrix (I := I) g x x p n := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  -- Decompose v in the model basis.
  have hv_eq : v = ∑ p : Fin (Module.finrank ℝ E), b.repr v p • b p :=
    (Module.Basis.sum_repr b v).symm
  -- Apply g.inner x · (b n) to both sides.
  rw [show g.inner x v =
      g.inner x (∑ p : Fin (Module.finrank ℝ E), b.repr v p • b p) from
    congrArg (g.inner x) hv_eq]
  rw [map_sum]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [show g.inner x (b.repr v p • b p) =
      b.repr v p • g.inner x (b p) from
    (g.inner x).map_smul (b.repr v p) (b p)]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_inner_modelBasis_eq_chartGram (I := I) g x p n]

/-- **Inverse-Gram formula for the model-basis component.** For any tangent vector
`v ∈ T_x M`, the model-basis component `b.repr v n` is recovered from inner products
against the model basis via the inverse Gram matrix:
$$
  (b.repr\,v)\,n = \sum_m G^{nm}(x, x)\, g_x(v, e_m).
$$
-/
private lemma modelBasis_repr_eq_invGram_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (n : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).repr v n =
      ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          g.inner x v ((Module.finBasis ℝ E) m) := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  -- ∑ m G^{nm} g(v, b_m) = ∑ m G^{nm} (∑ p (b.repr v p) G_{pm})
  --                     = ∑ p (b.repr v p) (∑ m G^{nm} G_{pm})
  -- Using G^{-1}: ∑ m G^{nm} G_{pm} = δ^n_p, so the result is (b.repr v n).
  -- Substitute the inner sum.
  have h_inner : ∀ m : Fin (Module.finrank ℝ E),
      g.inner x v (b m) =
        ∑ p : Fin (Module.finrank ℝ E),
          b.repr v p *
            chartGramMatrix (I := I) g x x p m :=
    g_inner_modelBasis_first_decomp (I := I) g x v
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          g.inner x v (b m)) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          (∑ p : Fin (Module.finrank ℝ E),
            b.repr v p * chartGramMatrix (I := I) g x x p m) from by
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [h_inner m]]
  -- Distribute and reorder.
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          (∑ p : Fin (Module.finrank ℝ E),
            b.repr v p * chartGramMatrix (I := I) g x x p m)) =
      ∑ p : Fin (Module.finrank ℝ E),
        b.repr v p *
          (∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              chartGramMatrix (I := I) g x x p m) from by
    -- ∑ m c * (∑ p A_p * B_m) = ∑ m ∑ p c * A_p * B_m = ∑ p A_p * (∑ m c * B_m).
    rw [show (∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              (∑ p : Fin (Module.finrank ℝ E),
                b.repr v p * chartGramMatrix (I := I) g x x p m)) =
        ∑ m : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              (b.repr v p * chartGramMatrix (I := I) g x x p m) from by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring]
  -- Inner sum: ∑ m G^{nm} G_{pm} = (G G^{-1})^n_p (after reordering) = δ^n_p?
  -- Actually: (G^{-1} G)_{n p} = ∑ m G^{-1}_{nm} G_{m p} = δ_{n p}.
  -- But we have G^{nm} G_{pm} — note G_{pm} (not G_{mp}), and G is symmetric.
  -- So ∑ m G^{nm} G_{pm} = ∑ m G^{nm} G_{mp} (by G symmetry) = (G^{-1} G)_{n p} = δ_{n p}.
  -- For matrix products, this is precisely (chartInvGram * chartGram) n p.
  have h_inner_collapse : ∀ p : Fin (Module.finrank ℝ E),
      (∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x n m *
          chartGramMatrix (I := I) g x x p m) =
        (if n = p then (1 : ℝ) else 0) := by
    intro p
    -- chartGramMatrix is symmetric: G_{pm} = G_{mp}.
    have hsymm : ∀ m : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x p m =
          chartGramMatrix (I := I) g x x m p := by
      intro m
      rw [chartGramMatrix_apply, chartGramMatrix_apply]
      exact g.symm x _ _
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartGramMatrix (I := I) g x x p m) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartGramMatrix (I := I) g x x m p from by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [hsymm m]]
    -- Now this is exactly (chartInvGram * chartGram) n p.
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x
    have hidentity := chartInvGramMatrix_mul_chartGramMatrix
      (I := I) g x hxbase
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartGramMatrix (I := I) g x x m p) =
        (chartInvGramMatrix (I := I) g x x *
          chartGramMatrix (I := I) g x x) n p from by
      rw [Matrix.mul_apply]]
    rw [hidentity]
    rw [Matrix.one_apply]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        b.repr v p *
          (∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x n m *
              chartGramMatrix (I := I) g x x p m)) =
      ∑ p : Fin (Module.finrank ℝ E),
        b.repr v p * (if n = p then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [h_inner_collapse p]]
  -- Collapse the sum to the term `p = n`.
  rw [Finset.sum_eq_single n]
  · rw [if_pos rfl, mul_one]
  · intro p _ hpn
    rw [if_neg (fun h => hpn h.symm), mul_zero]
  · intro hn
    exact absurd (Finset.mem_univ n) hn

/-! ## Main bridge: orthonormal-frame Frobenius equals chart-coordinate metric
Frobenius. -/

/-- **Unconditional bridge: orthonormal-frame Frobenius equals chart-coordinate metric
Frobenius.** For a smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian
manifold, the orthonormal-frame Frobenius squared `frobeniusSq_grad_vector g (∇f) x`
equals the chart-coordinate metric Frobenius squared `chartHessFrobeniusSq g f x`. -/
theorem frobeniusSq_grad_vector_eq_chartHessFrobeniusSq
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    frobeniusSq_grad_vector (I := I) g
        (fun b : M => gradFun (I := I) g f b) x =
      chartHessFrobeniusSq (I := I) g f x := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  -- Define T : T_x M →L T_x M via T(v) := (LeviCivita g) (∇f) x v.
  set T : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (LeviCivita (I := I) g).toFun
      (fun b => gradFun (I := I) g f b) x with hT_def
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  -- Step 1: frobeniusSq_grad_vector g (∇f) x = ∑_i g(T(B_i), T(B_i)).
  have hStep1 : frobeniusSq_grad_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (T (B i)) (T (B i)) := by
    rw [frobeniusSq_grad_vector_def]
  rw [hStep1]
  -- Step 2: ∑_i g(T(B_i), T(B_i)) = ∑_{kl} G^{kl} g(T(e_k), T(e_l)).
  rw [sum_g_inner_T_self_eq_invGram_sum (I := I) g x T B hB_orth]
  -- Step 3: Decompose g(T(e_k), T(e_l)) in the model basis.
  -- g(T(e_k), T(e_l)) = ∑_n (b.repr (T e_l) n) * g(T(e_k), e_n).
  -- And (b.repr (T e_l) n) = ∑_m G^{nm} g(T(e_l), e_m).
  -- And g(T(e_k), e_n) = abstractHessian g f x e_k e_n = chartHessianTensor g x f k n x.
  -- And g(T(e_l), e_m) = chartHessianTensor g x f l m x.
  -- So g(T(e_k), T(e_l)) = ∑_n (∑_m G^{nm} chartHessianTensor l m x) chartHessianTensor k n x
  --                     = ∑_{mn} G^{nm} chartHessianTensor l m x chartHessianTensor k n x.
  -- Substitute this expansion.
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  -- Helper: g(T(e_k), e_n) = chartHessianTensor g x f k n x.
  have h_TE_eq : ∀ k n : Fin (Module.finrank ℝ E),
      g.inner x (T (b k)) (b n) =
        chartHessianTensor (I := I) g x f k n x := by
    intro k n
    -- T(e_k) = (LC g)(∇f) x e_k. By abstractHessian_eq_inner_cov_gradFun_extend,
    -- g(T(e_k), b_n) = abstractHessian g f x e_k b_n.
    -- Then by hM, abstractHessian g f x e_k e_n = chartHessianTensor g x f k n x.
    have h1 : g.inner x (T (b k)) (b n) =
        g.inner x ((LeviCivita (I := I) g).toFun
            (fun b => gradFun (I := I) g f b) x (b k)) (b n) := rfl
    rw [h1]
    rw [abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x (b k) (b n)]
    exact hM k n
  -- Decompose T(e_l) in model basis: T(e_l) = ∑_n (b.repr (T e_l) n) • b n.
  -- Hence g(T(e_k), T(e_l)) = ∑_n (b.repr (T e_l) n) * g(T(e_k), b_n) =
  --   ∑_n (b.repr (T e_l) n) * chartHessianTensor g x f k n x.
  have h_g_TT : ∀ k l : Fin (Module.finrank ℝ E),
      g.inner x (T (b k)) (T (b l)) =
        ∑ n : Fin (Module.finrank ℝ E),
          b.repr (T (b l)) n *
            chartHessianTensor (I := I) g x f k n x := by
    intro k l
    -- Apply g.inner x (T (b k)) to T (b l) = ∑ n (b.repr (T (b l)) n) • b n.
    have hTl_eq : T (b l) = ∑ n : Fin (Module.finrank ℝ E),
        b.repr (T (b l)) n • b n :=
      (Module.Basis.sum_repr b (T (b l))).symm
    rw [show g.inner x (T (b k)) (T (b l)) =
        g.inner x (T (b k))
          (∑ n : Fin (Module.finrank ℝ E),
            b.repr (T (b l)) n • b n) from
      congrArg (g.inner x (T (b k))) hTl_eq]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [show g.inner x (T (b k)) (b.repr (T (b l)) n • b n) =
        b.repr (T (b l)) n • g.inner x (T (b k)) (b n) from
      (g.inner x (T (b k))).map_smul (b.repr (T (b l)) n) (b n)]
    rw [smul_eq_mul]
    rw [h_TE_eq k n]
  -- Substitute h_g_TT into the LHS.
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T (b k)) (T (b l))) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              b.repr (T (b l)) n *
                chartHessianTensor (I := I) g x f k n x) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [h_g_TT k l]]
  -- Now expand b.repr (T (b l)) n via modelBasis_repr_eq_invGram_sum.
  have h_repr_T_eq : ∀ l n : Fin (Module.finrank ℝ E),
      b.repr (T (b l)) n =
        ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            g.inner x (T (b l)) (b m) :=
    fun l n => modelBasis_repr_eq_invGram_sum (I := I) g x (T (b l)) n
  -- Substitute and use h_TE_eq for g(T(b l)) (b m) = chartHessianTensor g x f l m x.
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              b.repr (T (b l)) n *
                chartHessianTensor (I := I) g x f k n x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              (∑ m : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x n m *
                  chartHessianTensor (I := I) g x f l m x) *
                  chartHessianTensor (I := I) g x f k n x) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    refine congrArg (fun y => chartInvGramMatrix (I := I) g x x k l * y) ?_
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [h_repr_T_eq l n]
    -- Substitute g(T(b l)) (b m) = chartHessianTensor g x f l m x.
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            g.inner x (T (b l)) (b m)) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x n m *
            chartHessianTensor (I := I) g x f l m x from by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [h_TE_eq l m]]]
  -- Now we have a quadruple sum. Distribute and reorganize to match
  -- chartHessFrobeniusSq g f x.
  -- LHS at this point:
  -- ∑_k ∑_l G^{kl} ∑_n (∑_m G^{nm} H_{lm}) * H_{kn}
  -- = ∑_{klmn} G^{kl} * G^{nm} * H_{lm} * H_{kn}
  -- chartHessFrobeniusSq:
  -- ∑_{i j k l} G^{ik} G^{jl} H_{ij} H_{kl}
  -- We need to match: relabel LHS variables (k_LHS, l_LHS, m_LHS, n_LHS) to RHS
  -- (i_RHS, k_RHS, l_RHS, j_RHS):
  -- (k_LHS = i, l_LHS = k, m_LHS = l, n_LHS = j)
  -- ⇒ G^{kl} → G^{ik}, G^{nm} → G^{jl}, H_{lm} → H_{kl}, H_{kn} → H_{ij}
  -- ⇒ G^{ik} G^{jl} H_{kl} H_{ij} = G^{ik} G^{jl} H_{ij} H_{kl} ✓.
  -- After distribution and Finset.sum_comm shuffles, we get the RHS.
  rw [chartHessFrobeniusSq_def]
  -- LHS: ∑ k l G^{kl} (∑ n (∑ m G^{nm} H_{lm}) * H_{kn})
  --    = ∑ k l ∑ n ∑ m G^{kl} * G^{nm} * H_{lm} * H_{kn}
  -- RHS: ∑ i j k l G^{ik} G^{jl} H_{ij} H_{kl}
  -- Rewrite LHS as a quadruple sum.
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            (∑ n : Fin (Module.finrank ℝ E),
              (∑ m : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x n m *
                  chartHessianTensor (I := I) g x f l m x) *
                  chartHessianTensor (I := I) g x f k n x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                chartInvGramMatrix (I := I) g x x n m *
                chartHessianTensor (I := I) g x f l m x *
                chartHessianTensor (I := I) g x f k n x from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring]
  -- LHS now: ∑ k l n m G^{kl} G^{nm} H_{lm} H_{kn}.
  -- RHS: ∑ i j k l G^{ik} G^{jl} H_{ij} H_{kl}.
  -- Reorder LHS to match: rename (k → i, l → k, n → j, m → l):
  -- ∑ i k j l G^{ik} G^{jl} H_{kl} H_{ij}.
  -- Then commute multiplications: G^{ik} G^{jl} H_{kl} H_{ij} = G^{ik} G^{jl} H_{ij} H_{kl}.
  -- Use Finset.sum_comm to rearrange the order of summation.
  -- Goal LHS: ∑ k l n m ... → want ∑ i j k l = ∑ k_LHS n_LHS l_LHS m_LHS (with i=k_LHS,
  -- j=n_LHS, k_RHS = l_LHS, l_RHS = m_LHS).
  -- The order on LHS is (k, l, n, m); we want order (k, n, l, m) (i.e., swap middle two).
  have h_swap : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                chartInvGramMatrix (I := I) g x x n m *
                chartHessianTensor (I := I) g x f l m x *
                chartHessianTensor (I := I) g x f k n x) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                chartInvGramMatrix (I := I) g x x n m *
                chartHessianTensor (I := I) g x f l m x *
                chartHessianTensor (I := I) g x f k n x := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]
  rw [h_swap]
  -- Now the order is (k, n, l, m). Compare to RHS (i, j, k, l):
  -- (k_LHS = i_RHS, n_LHS = j_RHS, l_LHS = k_RHS, m_LHS = l_RHS).
  -- The inner expression: G^{kl} G^{nm} H_{lm} H_{kn} with l = k_RHS, m = l_RHS, k = i,
  -- n = j becomes G^{i k_RHS} G^{j l_RHS} H_{k_RHS l_RHS} H_{ij}. After commuting H's,
  -- this is G^{ik} G^{jl} H_{ij} H_{kl} = the RHS summand.
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro n _
  refine Finset.sum_congr rfl ?_
  intro l _
  refine Finset.sum_congr rfl ?_
  intro m _
  ring

/-! ## Step 5: unconditional pointwise Bochner-Weitzenböck identity (concrete form). -/

/-- **Truly unconditional pointwise Bochner-Weitzenböck identity in concrete form.**
For any smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian manifold, the
pointwise identity
$$
  \Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    2\,|\nabla^2 f|_g^2(x) +
    2\,\mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr) +
    2\,g_x\bigl(\nabla f(x), \nabla(\Delta_g f)(x)\bigr)
$$
holds at every point `x : M`, with `|\nabla^2 f|_g^2(x)` realised as the
orthonormal-frame Frobenius squared `frobeniusSq_grad_vector g (∇f) x` and
`\mathrm{Ric}_x(\nabla f, \nabla f)` as the abstract Ricci pairing
`ricciTensor g x (∇f x) (∇f x)`. -/
theorem bochner_pointwise_concrete_unconditional
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      2 * frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g (Δ_g (I := I) g hf) x) := by
  -- The abstract identity gives `(1/2) Δ_g (norm²grad) = ... + ricciTensor + frob`.
  have h := bochner_pointwise_abstract_unconditional (I := I) g hf x
  -- `normGradSq_contMDiff = normGradSqFun_contMDiff` as smoothness witnesses (re-export).
  have hLHS_eq : Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x := rfl
  rw [hLHS_eq] at h
  -- Multiply by 2.
  have h' : Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      2 * (g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
            (gradFun (I := I) g f x) +
          ricciTensor (I := I) g x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x) +
          frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x) := by
    linarith [h]
  rw [h']
  -- Reorder to match the standard RHS order. Use `g.symm` on the cross term.
  rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
          (gradFun (I := I) g f x) =
        g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g (Δ_g (I := I) g hf) x) from
    g.symm x _ _]
  ring

/-- **Truly unconditional pointwise Bochner-Weitzenböck identity in concrete form
(metric-Frobenius variant).** Same identity as `bochner_pointwise_concrete_unconditional`
but with the orthonormal-frame Frobenius squared replaced by the chart-coordinate metric
Frobenius squared `chartHessFrobeniusSq g f x`. The two are equal by
`frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`. -/
theorem bochner_pointwise_concrete_metric_unconditional
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x =
      2 * chartHessFrobeniusSq (I := I) g f x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g (Δ_g (I := I) g hf) x) := by
  rw [bochner_pointwise_concrete_unconditional (I := I) g hf x]
  rw [frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x]

end Connection
end Integral
end DifferentialGeometry
