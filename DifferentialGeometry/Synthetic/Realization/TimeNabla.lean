import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Synthetic.Realization.TimeDeriv
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction

/-!
# P28: Concrete `NablaTimeProductRule`

This file realizes the Synthetic-level `NablaTimeProductRule` predicate for the
canonical concrete realization `concreteTimeDerivativeData` of
`Synthetic/Realization/TimeDeriv.lean` (the jointly-smooth algebra on `ℝ × M`).

## Approach: localised discrete Leibniz identities

Given the 8 smoothness hypotheses of `NablaTimeProductRule`, the equation
asserted by the rule reduces to two *discrete Leibniz identities* — one for
each per-slot connection substitution — after applying `t_nabla_eval`,
`conn_var_tensor_eval`, and `nabla_tensor_eval` to the two sides. These
identities have the shape

```
dt_apply (fun τ => T τ (…(conn_fam τ X (vs i))…) αs) t =
  dt_apply (fun τ => T t (…(conn_fam τ X (vs i))…) αs) t
+ dt_apply (fun τ => T τ (…(conn_fam t X (vs i))…) αs) t
```

and are genuinely "jointly-smooth Leibniz" facts about partial differentiation
on `ℝ × M`. Rather than axiomatising them globally, we localise them to two
*local hypotheses* `h_leibniz_v` / `h_leibniz_c` on this theorem — downstream
Ricci-flow users can supply them using concrete calculus on joint-smooth
families.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle BigOperators
open SyntheticTensor

-- ============================================================
-- P28: the product rule for the canonical concrete time-derivative model.
-- ============================================================

section ConcreteProductRule

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Concrete realisation of `NablaTimeProductRule` for the canonical
jointly-smooth time-derivative model of `TimeDeriv.lean`.

After unfolding both sides pointwise via `t_nabla_eval`, `conn_var_tensor_eval`,
and `nabla_tensor_eval`, the equality reduces to a pair of discrete-Leibniz
identities — one per vector/covector slot — which are supplied as local
hypotheses `h_leibniz_v` / `h_leibniz_c`. -/
theorem concrete_nabla_time_product_rule
    (conn_fam : ℝ →
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (ha_fam : ∀ τ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ X (f : C^∞⟮I, M; ℝ⟯) Y,
        conn_fam τ X (f • Y) =
          (concreteDerivationEmbedding I M).embed X f • Y + f • conn_fam τ X Y)
    (h_leibniz_v : ∀ {r s : ℕ}
        (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (T : ℝ → TensorData C^∞⟮I, M; ℝ⟯
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ r s)
        (t : ℝ) (i : Fin s)
        (vs : Fin s → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (αs : Fin r →
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
        (concreteTimeDerivativeData I M).dt_apply
            (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) t
          = (concreteTimeDerivativeData I M).dt_apply
              (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) t
            + (concreteTimeDerivativeData I M).dt_apply
                (fun τ => T τ (Function.update vs i (conn_fam t X (vs i))) αs) t)
    (h_leibniz_c : ∀ {r s : ℕ}
        (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (T : ℝ → TensorData C^∞⟮I, M; ℝ⟯
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ r s)
        (t : ℝ) (j : Fin r)
        (vs : Fin s → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (αs : Fin r →
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
        (concreteTimeDerivativeData I M).dt_apply
            (fun τ => T τ vs (Function.update αs j
              (nabla_dual (concreteDerivationEmbedding I M) (conn_fam τ)
                (ha_fam τ) (hl_fam τ) X (αs j)))) t
          = (concreteTimeDerivativeData I M).dt_apply
              (fun τ => T t vs (Function.update αs j
                (nabla_dual (concreteDerivationEmbedding I M) (conn_fam τ)
                  (ha_fam τ) (hl_fam τ) X (αs j)))) t
            + (concreteTimeDerivativeData I M).dt_apply
                (fun τ => T τ vs (Function.update αs j
                  (nabla_dual (concreteDerivationEmbedding I M) (conn_fam t)
                    (ha_fam t) (hl_fam t) X (αs j)))) t) :
    NablaTimeProductRule (concreteDerivationEmbedding I M)
      (concreteTimeDerivativeData I M) conn_fam ha_fam hl_fam := by
  -- Bind the 8 hypotheses of `NablaTimeProductRule`.
  intro X r s T t hT hXT h_conn_smooth_v_var h_conn_smooth_c_var hT_nabla
    h_conn_smooth_v_at h_conn_smooth_c_at h_nabla_t
  -- Short-hands.
  set emb := concreteDerivationEmbedding I M with hemb
  set td := concreteTimeDerivativeData I M with htd
  set h_st := concrete_spatial_temporal_comm_general I M
  -- Reduce the tensor equality to a pointwise MultilinearMap equality in `R`.
  -- Use `MultilinearMap.ext` twice to avoid auto-extension into `C^∞⟮I,M;ℝ⟯`'s
  -- pointwise `M → ℝ` level.
  refine MultilinearMap.ext (fun vs => ?_)
  refine MultilinearMap.ext (fun αs => ?_)
  -- Evaluate LHS via `t_nabla_eval` (uses `h_st`).
  rw [t_nabla_eval emb td h_st conn_fam ha_fam hl_fam X T t hT hXT
      h_conn_smooth_v_var h_conn_smooth_c_var hT_nabla vs αs]
  -- Evaluate RHS: push `MultilinearMap.add_apply` and then unfold each piece.
  simp only [MultilinearMap.add_apply]
  rw [conn_var_tensor_eval emb td conn_fam ha_fam hl_fam t X (T t) h_nabla_t
      h_conn_smooth_v_at h_conn_smooth_c_at vs αs]
  rw [nabla_tensor_eval emb (conn_fam t) (ha_fam t) (hl_fam t) X
      (dt_tensor td t T hT) vs αs]
  -- The inner `dt_tensor … vs αs` and its update-shifted siblings reduce to
  -- `dt_apply (fun τ => T τ · ·) t`.
  simp only [dt_tensor_eval]
  -- Smoothness of the per-i vector slices at `conn_fam t` — pulled from
  -- the `h_conn_smooth_v_var` hypothesis at the special time `τ = t`.
  -- These are the families under the outer `Σᵢ dt_apply` on the RHS.
  -- Pull the `Σᵢ` out of `dt_apply` on the RHS's vector piece.
  have hS_vec_var : ∀ i : Fin s, td.isSmoothFam
      (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) :=
    fun i => h_conn_smooth_v_var i vs αs
  have hS_cov_var : ∀ j : Fin r, td.isSmoothFam
      (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) :=
    fun j => h_conn_smooth_c_var j vs αs
  have hS_vec_at : ∀ i : Fin s, td.isSmoothFam
      (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) :=
    fun i => h_conn_smooth_v_at i vs αs
  have hS_cov_at : ∀ j : Fin r, td.isSmoothFam
      (fun τ => T t vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) :=
    fun j => h_conn_smooth_c_at j vs αs
  have hS_vec_tfix : ∀ i : Fin s, td.isSmoothFam
      (fun τ => T τ (Function.update vs i (conn_fam t X (vs i))) αs) :=
    fun i => hT _ _
  have hS_cov_tfix : ∀ j : Fin r, td.isSmoothFam
      (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam t) (ha_fam t) (hl_fam t) X (αs j)))) :=
    fun j => hT _ _
  -- Pull the sums outside of `dt_apply` on both sides.
  -- LHS vector sum:
  have h_vec_sum_fn_var : (fun τ => ∑ i : Fin s,
        T τ (Function.update vs i (conn_fam τ X (vs i))) αs) =
      ∑ i : Fin s,
        (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    funext τ; simp only [Finset.sum_apply]
  have h_cov_sum_fn_var : (fun τ => ∑ j : Fin r,
        T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      ∑ j : Fin r,
        (fun τ => T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp only [Finset.sum_apply]
  have h_vec_sum_fn_at : (fun τ => ∑ i : Fin s,
        T t (Function.update vs i (conn_fam τ X (vs i))) αs) =
      ∑ i : Fin s,
        (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    funext τ; simp only [Finset.sum_apply]
  have h_cov_sum_fn_at : (fun τ => ∑ j : Fin r,
        T t vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      ∑ j : Fin r,
        (fun τ => T t vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp only [Finset.sum_apply]
  -- Distribute `dt_apply` over the LHS sum (vector) and over the RHS sums (at, tfix).
  rw [h_vec_sum_fn_var,
      td.dt_apply_sum Finset.univ _ t
        (fun i _ => hS_vec_var i),
      h_cov_sum_fn_var,
      td.dt_apply_sum Finset.univ _ t
        (fun j _ => hS_cov_var j),
      h_vec_sum_fn_at,
      td.dt_apply_sum Finset.univ _ t
        (fun i _ => hS_vec_at i),
      h_cov_sum_fn_at,
      td.dt_apply_sum Finset.univ _ t
        (fun j _ => hS_cov_at j)]
  -- On the RHS of `nabla_tensor_eval`, the per-i/per-j terms
  -- `dt_apply (fun τ => T τ (update vs i (conn_fam t X (vs i))) αs) t` (resp. cov)
  -- are already in the "tfix" shape — they go as the second summand of the Leibniz.
  -- Apply the discrete Leibniz identity per-i/per-j on the LHS.
  have h_leibniz_sum_v : ∑ i : Fin s,
        td.dt_apply (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) t =
      (∑ i : Fin s, td.dt_apply
          (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) t)
      + ∑ i : Fin s, td.dt_apply
          (fun τ => T τ (Function.update vs i (conn_fam t X (vs i))) αs) t := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_leibniz_v X T t i vs αs
  have h_leibniz_sum_c : ∑ j : Fin r,
        td.dt_apply (fun τ => T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t =
      (∑ j : Fin r, td.dt_apply
          (fun τ => T t vs (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t)
      + ∑ j : Fin r, td.dt_apply
          (fun τ => T τ vs (Function.update αs j
            (nabla_dual emb (conn_fam t) (ha_fam t) (hl_fam t) X (αs j)))) t := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_leibniz_c X T t j vs αs
  rw [h_leibniz_sum_v, h_leibniz_sum_c]
  -- Rearrange: goal is now purely algebraic in the RHS split forms.
  ring

end ConcreteProductRule

end
