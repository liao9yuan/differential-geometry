import DifferentialGeometry.Synthetic.Realization.TensorContract
import DifferentialGeometry.Synthetic.Algebra.MetricTrace
import DifferentialGeometry.Synthetic.Geometry.CurvatureContractions
import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.CurvatureAlgebra

/-!
# Concrete Trace Fubini

This file lives in the realization layer. It connects the concrete
`concreteAbstractTrace` implementation to the synthetic Fubini interfaces.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped Manifold ContDiff Topology
open BigOperators
open SyntheticTensor
open TensorContractRealization

namespace TensorContractRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev R_ := C^∞⟮I, M; ℝ⟯

private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯

private lemma R_evalAt_sum {ι : Type*} (s : Finset ι) (f : ι → R_ I M) (x₀ : M) :
    (∑ i ∈ s, f i) x₀ = ∑ i ∈ s, (f i) x₀ := by
  let evalAt : C^∞⟮I, M; ℝ⟯ →+* ℝ := ContMDiffMap.evalRingHom x₀
  change evalAt (∑ i ∈ s, f i) = ∑ i ∈ s, evalAt (f i)
  exact map_sum evalAt f s

/-- Char-≠-2 cancellation in the smooth-function ring `C^∞⟮I, M; ℝ⟯`. Discharges
the `h2` coherence input used by the slot-audit obligations and the P2 finite
component fallback. -/
theorem concreteSmooth_two_cancel
    (a : R_ I M) (h : (2 : R_ I M) * a = 0) : a = 0 := by
  apply ContMDiffMap.ext
  intro x
  have hx := DFunLike.congr_fun h x
  have h2x : (2 : R_ I M) x = (2 : ℝ) := by
    have h_two_eq : (2 : R_ I M) = (1 : R_ I M) + (1 : R_ I M) := by norm_num
    have := DFunLike.congr_fun h_two_eq x
    simp only [ContMDiffMap.coe_add, Pi.add_apply,
      ContMDiffMap.coe_one, Pi.one_apply] at this
    rw [this]; norm_num
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply,
    ContMDiffMap.coe_zero, Pi.zero_apply, h2x] at hx
  change a x = (0 : ℝ)
  linarith

/-- Pointwise metric expansion of a covector component in the chosen local
frame.

This is the finite-frame identity that converts the concrete trace
`∑ᵢ θᵢ(L σᵢ)` of an endomorphism into the inverse-metric contraction form
`∑ᵢⱼ g^{ij} g(L σᵢ, σⱼ)`. It is independent of curvature and is intended as
the basic tensor-calculus bridge used by the P1 contracted-Bianchi traces. -/
theorem chooseLocalFrames_metric_covector_component_at
    (met : MetricDuality (R_ I M) (V_ I M))
    (α : V_ I M →ₗ[R_ I M] R_ I M) (X : V_ I M) (x₀ : M) :
    (α X) x₀ =
      (let σ := (chooseLocalFrames I M x₀).1
       let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
       ∑ j, (((met.g_inv ![]) ![α, θ j]) x₀) * (met.g X (σ j) x₀)) := by
  classical
  set σ := (chooseLocalFrames I M x₀).1 with hσ
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q) with hθ
  let c : Fin (Module.finrank ℝ E) → R_ I M := fun j => met.g X (σ j)
  let β : V_ I M →ₗ[R_ I M] R_ I M := ∑ j, c j • θ j
  have hβ_eval : ∀ Y : V_ I M, (β Y) x₀ = (met.flat X Y) x₀ := by
    intro Y
    have hflat :=
      chooseLocalFrames_covector_expand_at I M (met.flat X) Y x₀
    rw [← hσ] at hflat
    change (met.flat X Y) x₀ =
      ∑ i, (θ i Y) x₀ * (met.flat X (σ i)) x₀ at hflat
    change ((∑ j, c j • θ j) Y) x₀ = (met.flat X Y) x₀
    rw [LinearMap.sum_apply, R_evalAt_sum]
    rw [hflat]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change ((c j) • (θ j Y)) x₀ =
      (θ j Y) x₀ * (met.flat X (σ j)) x₀
    change (c j) x₀ * (θ j Y) x₀ =
      (θ j Y) x₀ * (met.g X (σ j)) x₀
    ring
  have hpoint :
      ((met.g_inv ![]) ![α, met.flat X]) x₀ =
        ((met.g_inv ![]) ![α, β]) x₀ := by
    apply tensorData_eval_pointwise I M 2 0 met.g_inv ![] ![]
      ![α, met.flat X] ![α, β] x₀
    · intro i
      exact i.elim0
    · intro j Y
      fin_cases j
      · rfl
      · exact (hβ_eval Y).symm
  have hlin :
      (met.g_inv ![]) ![α, β] =
        ∑ j, c j * ((met.g_inv ![]) ![α, θ j]) := by
    change (met.g_inv ![])
        (Fin.cons α (Fin.cons β ![])) =
      ∑ j, c j * (met.g_inv ![])
        (Fin.cons α (Fin.cons (θ j) ![]))
    have harg :
        (Fin.cons α (Fin.cons β ![]) :
          Fin 2 → V_ I M →ₗ[R_ I M] R_ I M) =
        Function.update
          (Fin.cons α (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) ![])) 1 β := by
      ext q
      fin_cases q <;> simp [Function.update]
    rw [harg]
    change (met.g_inv ![])
        (Function.update
          (Fin.cons α (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) ![])) 1
          (∑ j, c j • θ j)) = _
    rw [(met.g_inv ![]).map_update_sum (t := Finset.univ)
      (g := fun j => c j • θ j)
      (m := Fin.cons α (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) ![])) (i := 1)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [(met.g_inv ![]).map_update_smul
      (Fin.cons α (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) ![])) 1
      (c j) (θ j)]
    rw [smul_eq_mul]
    have hupdate :
        Function.update
          (Fin.cons α (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) ![])) 1 (θ j) =
        (Fin.cons α (Fin.cons (θ j) ![]) :
          Fin 2 → V_ I M →ₗ[R_ I M] R_ I M) := by
      ext q
      fin_cases q <;> simp [Function.update]
    rw [hupdate]
  have hinv := congrArg (fun f : R_ I M => f x₀) (met.inverse_eval' X α)
  calc
    (α X) x₀ = ((met.g_inv ![]) ![α, met.flat X]) x₀ := hinv.symm
    _ = ((met.g_inv ![]) ![α, β]) x₀ := hpoint
    _ = (∑ j, c j * ((met.g_inv ![]) ![α, θ j])) x₀ := by rw [hlin]
    _ = ∑ j, (((met.g_inv ![]) ![α, θ j]) x₀) * (met.g X (σ j) x₀) := by
      rw [R_evalAt_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      change (c j) x₀ * (((met.g_inv ![]) ![α, θ j]) x₀) =
        (((met.g_inv ![]) ![α, θ j]) x₀) * (met.g X (σ j) x₀)
      ring

/-- Concrete trace of an endomorphism as the inverse-metric contraction of its
metric pairing in the chosen local frame.

This is the general trace-to-metric-trace bridge needed by the P1
contracted-Bianchi `h_div` and `h_grad` calculations. The curvature-specific
step after this theorem is only to rewrite `met.g (L σᵢ) σⱼ` using the relevant
Ricci/Riemann contraction lemma. -/
theorem concreteTr_metric_pairing_unfold
    (met : MetricDuality (R_ I M) (V_ I M))
    (L : V_ I M →ₗ[R_ I M] V_ I M) (x₀ : M) :
    (concreteTr I M L) x₀ =
      (let σ := (chooseLocalFrames I M x₀).1
       let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
       ∑ i, ∑ j,
         (((met.g_inv ![]) ![θ i, θ j]) x₀) * (met.g (L (σ i)) (σ j) x₀)) := by
  classical
  set σ := (chooseLocalFrames I M x₀).1 with hσ
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q) with hθ
  have htrace :=
    congrArg (fun f : R_ I M => f x₀) (concreteTensorContract_endo I M L)
  change (((concreteTensorContract I M 0 0 (endo_to_tensor L)) ![]) ![]) x₀ =
    (concreteTr I M L) x₀ at htrace
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply] at htrace
  change (∑ i, (endo_to_tensor L (Fin.cons ((chooseLocalFrames I M x₀).1 i) ![])
      (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)) ![])) x₀) =
    (concreteTr I M L) x₀ at htrace
  rw [← htrace]
  rw [← hσ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hcomponent := chooseLocalFrames_metric_covector_component_at I M met
    (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)) (L (σ i)) x₀
  rw [← hσ] at hcomponent
  change ((covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)) (L (σ i))) x₀ =
    ∑ j,
      (((met.g_inv ![]) ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i),
          covectorToFunctional I M ((chooseLocalFrames I M x₀).2 j)]) x₀) *
        (met.g (L (σ i)) (σ j) x₀)
    at hcomponent
  rw [← hcomponent]
  change (endo_to_tensor L ![σ i]
      ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)]) x₀ =
    ((covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)) (L (σ i))) x₀
  rw [endo_to_tensor_eval]

/-- Concrete trace is invariant under metric adjoints.

This is the realization-layer proof of the abstract
`HasMetricAdjointTraceInvariant` bridge. It uses the metric-pairing trace
expansion, the supplied adjoint relation, symmetry of the metric, symmetry of
the inverse metric, and a finite-sum swap. -/
theorem concreteTr_eq_of_metric_adjoint
    (met : MetricDuality (R_ I M) (V_ I M))
    (A B : V_ I M →ₗ[R_ I M] V_ I M)
    (h_adj : ∀ X Y, met.g (A X) Y = met.g X (B Y)) :
    concreteTr I M A = concreteTr I M B := by
  classical
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteTr_metric_pairing_unfold I M met A x₀,
    concreteTr_metric_pairing_unfold I M met B x₀]
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  calc
    (∑ i, ∑ j,
        (((met.g_inv ![]) ![θ i, θ j]) x₀) * (met.g (A (σ i)) (σ j) x₀))
        =
      (∑ i, ∑ j,
        (((met.g_inv ![]) ![θ i, θ j]) x₀) * (met.g (σ i) (B (σ j)) x₀)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h := congrArg (fun f : R_ I M => f x₀) (h_adj (σ i) (σ j))
        simpa using congrArg
          (fun r => (((met.g_inv ![]) ![θ i, θ j]) x₀) * r) h
    _ =
      (∑ i, ∑ j,
        (((met.g_inv ![]) ![θ i, θ j]) x₀) * (met.g (B (σ j)) (σ i) x₀)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h := congrArg (fun f : R_ I M => f x₀)
          (met.g_symm (σ i) (B (σ j)))
        simpa using congrArg
          (fun r => (((met.g_inv ![]) ![θ i, θ j]) x₀) * r) h
    _ =
      (∑ i, ∑ j,
        (((met.g_inv ![]) ![θ i, θ j]) x₀) * (met.g (B (σ i)) (σ j) x₀)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h := congrArg (fun f : R_ I M => f x₀)
          (met.g_inv_symm (θ j) (θ i))
        simpa using congrArg
          (fun r => r * (met.g (B (σ i)) (σ j) x₀)) h

/-- The concrete standard trace satisfies trace invariance under metric
adjoints, for any synthetic metric duality over smooth tangent sections. -/
instance concreteHasMetricAdjointTraceInvariant
    (met : MetricDuality (R_ I M) (V_ I M)) :
    HasMetricAdjointTraceInvariant (concreteAbstractTrace I M) met where
  trace_eq_of_metric_adjoint A B h_adj := by
    simpa [concreteAbstractTrace_tr] using
      concreteTr_eq_of_metric_adjoint I M met A B h_adj

@[simp] private theorem fin_zero_fun_eq_empty {α : Type*} (f : Fin 0 → α) :
    f = ![] := by
  ext i
  exact i.elim0

private theorem Finset.sum_four_contract_bianchi_perm
    {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (F : ι → ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ i, ∑ j, ∑ a, ∑ b, F b a i j := by
  classical
  have hpack : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) := {
    toFun p := (p.2.2.2, p.2.2.1, p.1, p.2.1)
    invFun p := (p.2.2.1, p.2.2.2, p.2.1, p.1)
    left_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl
    right_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl }
  have hunpack : (∑ p : ι × ι × ι × ι, F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2) =
      ∑ i, ∑ j, ∑ a, ∑ b, F b a i j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  calc
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
        = ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := hpack
    _ = ∑ p : ι × ι × ι × ι, F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2 := by
            exact (Equiv.sum_comp e (fun p : ι × ι × ι × ι =>
              F p.1 p.2.1 p.2.2.1 p.2.2.2)).symm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F b a i j := hunpack

private theorem Finset.sum_four_contract_bianchi_cycle_perm
    {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (F : ι -> ι -> ι -> ι -> R) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ i, ∑ j, ∑ a, ∑ b, F a b j i := by
  classical
  have hpack : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) := {
    toFun p := (p.2.2.1, p.2.2.2, p.2.1, p.1)
    invFun p := (p.2.2.2, p.2.2.1, p.1, p.2.1)
    left_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl
    right_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl }
  have hunpack :
      (∑ p : ι × ι × ι × ι,
          F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2) =
        ∑ i, ∑ j, ∑ a, ∑ b, F a b j i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  calc
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
        = ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := hpack
    _ = ∑ p : ι × ι × ι × ι, F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2 := by
            exact (Equiv.sum_comp e (fun p : ι × ι × ι × ι =>
              F p.1 p.2.1 p.2.2.1 p.2.2.2)).symm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F a b j i := hunpack

private theorem Finset.sum_four_reorder_ijab_to_abij
    {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (F : ι -> ι -> ι -> ι -> R) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
  classical
  have hpack : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) := {
    toFun p := (p.2.2.1, p.2.2.2, p.1, p.2.1)
    invFun p := (p.2.2.1, p.2.2.2, p.1, p.2.1)
    left_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl
    right_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl }
  have hunpack :
      (∑ p : ι × ι × ι × ι,
          F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2) =
        ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  calc
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
        = ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := hpack
    _ = ∑ p : ι × ι × ι × ι, F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2 := by
            exact (Equiv.sum_comp e (fun p : ι × ι × ι × ι =>
              F p.1 p.2.1 p.2.2.1 p.2.2.2)).symm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := hunpack

private theorem Finset.sum_pair_symm_mul_antisymm_eq_zero
    {ι R : Type*} [Fintype ι] [CommRing R]
    (h2 : forall a : R, (2 : R) * a = 0 -> a = 0)
    (A F : ι -> ι -> R)
    (hA : forall i j, A i j = A j i)
    (hF : forall i j, F i j = -F j i) :
    (∑ i, ∑ j, A i j * F i j) = 0 := by
  classical
  let S : R := ∑ i, ∑ j, A i j * F i j
  have hSneg : S = -S := by
    calc
      S = ∑ j, ∑ i, A i j * F i j := by
          unfold S
          rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, A j i * F j i := by
          rfl
      _ = ∑ i, ∑ j, A i j * (-F i j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hA j i, hF j i]
      _ = -S := by
          unfold S
          simp only [mul_neg, Finset.sum_neg_distrib]
  apply h2 S
  have hsum : S + S = 0 := by
    have hsum' : S + S = -S + S := by
      nth_rewrite 1 [hSneg]
      rfl
    simpa using hsum'
  calc
    (2 : R) * S = S + S := by ring
    _ = 0 := hsum

/-- The concrete `AbstractTrace` satisfies the raw double-contraction Fubini
law. At each point this is the finite-sum identity obtained by swapping the two
local-frame summation indices. -/
theorem concreteTensorContractFubini :
    TensorContractFubini (concreteAbstractTrace I M) := by
  intro r s T
  unfold tensor_contract_twice
  rw [concreteAbstractTrace_tensor_contract, concreteAbstractTrace_tensor_contract]
  rw [concreteAbstractTrace_tensor_contract, concreteAbstractTrace_tensor_contract]
  refine MultilinearMap.ext (fun m => ?_)
  refine MultilinearMap.ext (fun n => ?_)
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteTensorContract_apply, concreteTensorContract_apply]
  rw [concreteTensorContract_fun_apply, concreteTensorContract_fun_apply]
  try (simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply])
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 2
  · congr 1
    funext k
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
        induction k using Fin.cases with
        | zero => rfl
        | succ k => rfl
  · funext k
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
        induction k using Fin.cases with
        | zero => rfl
        | succ k => rfl

/-- Typeclass form of `concreteTensorContractFubini`. -/
instance concreteHasTensorContractFubini :
    HasTensorContractFubini (concreteAbstractTrace I M) where
  tensor_contract_fubini := concreteTensorContractFubini I M

/-!
## Metric-trace Fubini lift

The concrete instance below proves

```lean
HasDoubleMetricTrace05PatternFubini
  DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
  DoubleMetricTrace05Pattern.contractedBianchiDivPattern
  (concreteMetricDuality I M g) (concreteAbstractTrace I M)
```

for a concrete Riemannian metric `g`. Expanding the two sides reduces this to a
four-index finite-sum reindexing: two raw concrete traces plus two inserted
`g_inv` tensors. The public `chooseLocalFrames` API in `TensorContract.lean`
is now exposed so that this proof can be written against the actual canonical
local frame instead of inaccessible private names.
-/

/-- Concrete pointwise expansion of the contracted-Bianchi divergence pattern.

For a lowered `(0,5)` tensor `T(A, X, Y, Z, W)`, the named divergence pattern
contracts original slots `(0, 3)` and `(1, 4)`, leaving slot `2`. This lemma is
the raw local-frame sum used by the later `h_div` probe: the remaining task is
to identify this four-index sum with the concrete trace defining
`ricciDivergenceAt`. -/
theorem concreteContractedBianchiDivPattern_tensor_apply_unfold
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5)
    (m : Fin 1 -> V_ I M) (x₀ : M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.tensor met
      (concreteAbstractTrace I M) T m ![]) x₀ =
    (let σ := (chooseLocalFrames I M x₀).1
     let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
     ∑ i, ∑ j, ∑ a, ∑ b,
       (((met.g_inv ![]) ![θ b, θ a]) x₀) *
       (((met.g_inv ![]) ![θ j, θ i]) x₀) *
       (T ![σ a, σ i, m 0, σ b, σ j] ![]) x₀) := by
  unfold DoubleMetricTrace05Pattern.tensor
  unfold doubleMetricTrace05
  simp only [metric_trace, raise_index, contract_general]
  simp only [concreteAbstractTrace_tensor_contract]
  repeat' rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  conv_lhs =>
    congr
    · skip
    · intro i
      rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp_rw [Finset.mul_sum]
  simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp only [DoubleMetricTrace05Pattern.contractedBianchiDivPattern]
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  simp only [Nat.reduceAdd, Fin.isValue, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Equiv.swap_self, Equiv.coe_refl, CompTriple.comp_eq, fin_zero_fun_eq_empty,
    Nat.add_zero, Matrix.Fin.cons_vecEmpty, Fin.mk_one, Matrix.cons_cons_comp_swap_zero_one,
    Fin.castAdd_zero, Fin.cast_refl, Fin.natAdd_zero]
  simp_rw [Finset.mul_sum]
  try simp only [Nat.reduceAdd, Fin.isValue, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Equiv.swap_self, Equiv.coe_refl, CompTriple.comp_eq, fin_zero_fun_eq_empty,
    Nat.add_zero, Matrix.Fin.cons_vecEmpty, Fin.mk_one, Matrix.cons_cons_comp_swap_zero_one,
    Fin.castAdd_zero, Fin.cast_refl, Fin.natAdd_zero]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun x_1 _ => ?_)
  refine Finset.sum_congr rfl (fun x_2 _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hvec :
      (Fin.cons (σ i)
          (Fin.cons (σ x_2) (Fin.cons (σ x_1) (Fin.cons (σ x) m) ∘ ⇑(Equiv.swap 0 2)) ∘
            ⇑(Equiv.swap 0 2)) ∘
        ⇑(Equiv.swap 0 3)) = ![σ x_2, σ x, m 0, σ i, σ x_1] := by
    ext k
    fin_cases k <;> rfl
  rw [hvec]
  have hsym1 :
      (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_1)]) x₀) =
        (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_1),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x)]) x₀) := by
    exact congrArg (fun f : R_ I M => f x₀)
      (met.g_inv_symm
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x))
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_1)))
  have hsym2 :
      (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_2),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)]) x₀) =
        (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_2)]) x₀) := by
    exact congrArg (fun f : R_ I M => f x₀)
      (met.g_inv_symm
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_2))
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)))
  rw [hsym1, hsym2]
  ring

/-- Pointwise vector-argument form of
`concreteContractedBianchiDivPattern_tensor_apply_unfold`. -/
theorem concreteContractedBianchiDivPattern_apply_unfold
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5)
    (Y : V_ I M) (x₀ : M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M) T Y) x₀ =
    (let σ := (chooseLocalFrames I M x₀).1
     let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
     ∑ i, ∑ j, ∑ a, ∑ b,
       (((met.g_inv ![]) ![θ b, θ a]) x₀) *
       (((met.g_inv ![]) ![θ j, θ i]) x₀) *
       (T ![σ a, σ i, Y, σ b, σ j] ![]) x₀) := by
  simpa [DoubleMetricTrace05Pattern.apply]
    using concreteContractedBianchiDivPattern_tensor_apply_unfold I M met T ![Y] x₀

/-- Concrete slot expansion for the left cyclic term in the traced second
Bianchi identity. This is the pure slot audit before applying Riemann
curvature symmetries to identify the result with the reversed divergence
trace. -/
theorem concreteContractedBianchiDivPattern_apply_cycle_left_unfold
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5)
    (Y : V_ I M) (x₀ : M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M) (covariantCycle012Left05 T) Y) x₀ =
    (let σ := (chooseLocalFrames I M x₀).1
     let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
     ∑ i, ∑ j, ∑ a, ∑ b,
       (((met.g_inv ![]) ![θ b, θ a]) x₀) *
       (((met.g_inv ![]) ![θ j, θ i]) x₀) *
       (T ![σ i, Y, σ a, σ b, σ j] ![]) x₀) := by
  rw [concreteContractedBianchiDivPattern_apply_unfold I M met
    (covariantCycle012Left05 T) Y x₀]
  simp only [covariantCycle012Left05_eval]

/-- Concrete pointwise expansion of the contracted-Bianchi scalar-gradient
pattern. The pattern contracts original slots `(1, 3)` and `(2, 4)`, leaving
slot `0`. -/
theorem concreteContractedBianchiGradPattern_apply_unfold
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5)
    (Y : V_ I M) (x₀ : M) :
    (DoubleMetricTrace05Pattern.contractedBianchiGradPattern.apply met
      (concreteAbstractTrace I M) T Y) x₀ =
    (let σ := (chooseLocalFrames I M x₀).1
     let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
     ∑ i, ∑ j, ∑ a, ∑ b,
       (((met.g_inv ![]) ![θ b, θ a]) x₀) *
       (((met.g_inv ![]) ![θ j, θ i]) x₀) *
       (T ![Y, σ a, σ i, σ b, σ j] ![]) x₀) := by
  unfold DoubleMetricTrace05Pattern.apply
  unfold DoubleMetricTrace05Pattern.tensor
  unfold doubleMetricTrace05
  simp only [metric_trace, raise_index, contract_general]
  simp only [concreteAbstractTrace_tensor_contract]
  repeat' rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  conv_lhs =>
    congr
    · skip
    · intro i
      rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp_rw [Finset.mul_sum]
  simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  try simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp only [DoubleMetricTrace05Pattern.contractedBianchiGradPattern]
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  simp only [Nat.reduceAdd, Fin.isValue, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Equiv.swap_self, Equiv.coe_refl, CompTriple.comp_eq, fin_zero_fun_eq_empty,
    Nat.add_zero, Matrix.Fin.cons_vecEmpty, Fin.mk_one, Matrix.cons_cons_comp_swap_zero_one,
    Fin.castAdd_zero, Fin.cast_refl, Fin.natAdd_zero]
  simp_rw [Finset.mul_sum]
  try simp only [Nat.reduceAdd, Fin.isValue, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Equiv.swap_self, Equiv.coe_refl, CompTriple.comp_eq, fin_zero_fun_eq_empty,
    Nat.add_zero, Matrix.Fin.cons_vecEmpty, Fin.mk_one, Matrix.cons_cons_comp_swap_zero_one,
    Fin.castAdd_zero, Fin.cast_refl, Fin.natAdd_zero]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun x_1 _ => ?_)
  refine Finset.sum_congr rfl (fun x_2 _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hvec :
      (Fin.cons (σ i) (Fin.cons (σ x_2) (![σ x_1, Y, σ x] ∘ ⇑(Equiv.swap 0 2))) ∘
          ⇑(Equiv.swap 0 3)) =
        ![Y, σ x_2, σ x, σ i, σ x_1] := by
    ext k
    fin_cases k <;> rfl
  have hT :
      ((T
          (Fin.cons (σ i)
            (Fin.cons (σ x_2) (![σ x_1, Y, σ x] ∘ ⇑(Equiv.swap 0 2))) ∘
              ⇑(Equiv.swap 0 3))) ![]) x₀ =
        ((T ![Y, σ x_2, σ x, σ i, σ x_1]) ![]) x₀ := by
    rw [hvec]
  rw [hT]
  have hsym1 :
      (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_1)]) x₀) =
        (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_1),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x)]) x₀) := by
    exact congrArg (fun f : R_ I M => f x₀)
      (met.g_inv_symm
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x))
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_1)))
  have hsym2 :
      (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_2),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)]) x₀) =
        (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_2)]) x₀) := by
    exact congrArg (fun f : R_ I M => f x₀)
      (met.g_inv_symm
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 x_2))
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)))
  rw [hsym1, hsym2]
  ring

/-- Concrete slot audit for the right cyclic term.

With the current `contractedBianchiGradPattern` slot convention, tracing the
right cyclic permutation by the divergence pattern gives the scalar-gradient
pattern with the same sign. This theorem is intentionally stated for an
arbitrary `(0,5)` tensor, so any later negative sign must come from a changed
gradient convention or an additional curvature-symmetry bridge, not from pure
slot bookkeeping. -/
theorem concreteContractedBianchiDivPattern_apply_cycle_right_eq_gradPattern
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5)
    (Y : V_ I M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M) (covariantCycle012Right05 T) Y) =
    (DoubleMetricTrace05Pattern.contractedBianchiGradPattern.apply met
      (concreteAbstractTrace I M) T Y) := by
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteContractedBianchiDivPattern_apply_unfold I M met
    (covariantCycle012Right05 T) Y x₀]
  rw [concreteContractedBianchiGradPattern_apply_unfold I M met T Y x₀]
  simp only [covariantCycle012Right05_eval]

/-- Concrete left-cycle trace audit for the lowered `nabla Rm` tensor.

After expanding the two metric traces, this is the classical calculation

```text
sum g^{ba} g^{ji} (nabla_i R)_{Y a b j}
  = sum g^{ba} g^{ji} (nabla_a R)_{i Y b j}.
```

The proof uses differentiated block symmetry to put the left cyclic term in
Ricci-trace position, then uses the differentiated first Bianchi identity. The
middle first-Bianchi term vanishes because it is antisymmetric in the pair
contracted against the symmetric inverse metric. -/
theorem concreteContractedBianchiDivPattern_apply_cycle_left_eq_divPattern_lowered
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M))
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (Y : V_ I M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M)
      (covariantCycle012Left05
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y) =
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M)
      (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y) := by
  classical
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteContractedBianchiDivPattern_apply_cycle_left_unfold I M met
    (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y x₀]
  rw [concreteContractedBianchiDivPattern_apply_unfold I M met
    (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y x₀]
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  let c : Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) ->
      Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) -> ℝ :=
    fun i j a b =>
      (((met.g_inv ![]) ![θ b, θ a]) x₀) *
        (((met.g_inv ![]) ![θ j, θ i]) x₀)
  let Tval :
      V_ I M -> V_ I M -> V_ I M -> V_ I M -> V_ I M -> ℝ :=
    fun A X Z W U => (covDerivRm_lowered emb conn met A X Z W U) x₀
  simp only [LoweredCovDerivRmTensorData.eval_apply]
  change
    (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ i) Y (σ a) (σ b) (σ j)) =
      ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j)
  have hblock :
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ i) Y (σ a) (σ b) (σ j)) =
        ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ i) (σ b) (σ j) Y (σ a) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    unfold Tval
    rw [show (covDerivRm_lowered emb conn met (σ i) Y (σ a) (σ b) (σ j)) x₀ =
        (covDerivRm_lowered emb conn met (σ i) (σ b) (σ j) Y (σ a)) x₀ from
      congrArg (fun f : R_ I M => f x₀)
        (covDerivRm_lowered_block_symm emb conn ha hal met h_mc h_tf
          (concreteSmooth_two_cancel I M)
          (σ i) Y (σ a) (σ b) (σ j))]
  have hperm :
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ i) (σ b) (σ j) Y (σ a)) =
        ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) (σ b) Y (σ j) := by
    conv_lhs =>
      rw [Finset.sum_four_contract_bianchi_cycle_perm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    unfold c
    have hsym1 :
        (((met.g_inv ![]) ![θ i, θ j]) x₀) =
          (((met.g_inv ![]) ![θ j, θ i]) x₀) := by
      exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ i) (θ j))
    have hsym2 :
        (((met.g_inv ![]) ![θ b, θ a]) x₀) =
          (((met.g_inv ![]) ![θ a, θ b]) x₀) := by
      exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ b) (θ a))
    rw [hsym1, hsym2]
    ring
  have hmiddle_zero :
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ b) Y (σ i) (σ j)) = 0 := by
    calc
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ b) Y (σ i) (σ j))
          = ∑ a, ∑ b, ∑ i, ∑ j, c i j a b * Tval (σ a) (σ b) Y (σ i) (σ j) := by
              rw [Finset.sum_four_reorder_ijab_to_abij]
      _ = 0 := by
          refine Finset.sum_eq_zero (fun a _ => ?_)
          refine Finset.sum_eq_zero (fun b _ => ?_)
          let A : Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) -> ℝ :=
            fun i j => (((met.g_inv ![]) ![θ j, θ i]) x₀)
          let F : Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) -> ℝ :=
            fun i j =>
              (((met.g_inv ![]) ![θ b, θ a]) x₀) *
                Tval (σ a) (σ b) Y (σ i) (σ j)
          have h2real : forall a : ℝ, (2 : ℝ) * a = 0 -> a = 0 := by
            intro a h
            exact (mul_eq_zero.mp h).resolve_left (by norm_num)
          have hA : forall i j, A i j = A j i := by
            intro i j
            unfold A
            exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ j) (θ i))
          have hF : forall i j, F i j = -F j i := by
            intro i j
            unfold F Tval
            rw [show (covDerivRm_lowered emb conn met (σ a) (σ b) Y (σ i) (σ j)) x₀ =
                - (covDerivRm_lowered emb conn met (σ a) (σ b) Y (σ j) (σ i)) x₀ from
              congrArg (fun f : R_ I M => f x₀)
                (covDerivRm_lowered_antisymm_second_pair emb conn met h_mc
                  (σ a) (σ b) Y (σ i) (σ j))]
            ring
          have hzero := Finset.sum_pair_symm_mul_antisymm_eq_zero h2real A F hA hF
          calc
            (∑ i, ∑ j, c i j a b * Tval (σ a) (σ b) Y (σ i) (σ j))
                = ∑ i, ∑ j, A i j * F i j := by
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    refine Finset.sum_congr rfl (fun j _ => ?_)
                    unfold A F c
                    ring
            _ = 0 := hzero
  have hfirstBianchi_sum :
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) (σ b) Y (σ j)) +
          (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ b) Y (σ i) (σ j)) +
            (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) Y (σ i) (σ b) (σ j)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    have hb := congrArg (fun f : R_ I M => f x₀)
      (covDerivRm_lowered_first_bianchi emb conn ha hal met h_tf
        (σ a) (σ i) (σ b) Y (σ j))
    have hb0 :
        Tval (σ a) (σ i) (σ b) Y (σ j) +
            Tval (σ a) (σ b) Y (σ i) (σ j) +
              Tval (σ a) Y (σ i) (σ b) (σ j) = 0 := by
      unfold Tval
      simpa only [Pi.add_apply, Pi.zero_apply] using hb
    linear_combination c i j a b * hb0
  have hthird :
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) Y (σ i) (σ b) (σ j)) =
        -∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j) := by
    calc
      (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) Y (σ i) (σ b) (σ j))
          = ∑ i, ∑ j, ∑ a, ∑ b,
              -(c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              refine Finset.sum_congr rfl (fun a _ => ?_)
              refine Finset.sum_congr rfl (fun b _ => ?_)
              unfold Tval
              rw [show (covDerivRm_lowered emb conn met (σ a) Y (σ i) (σ b) (σ j)) x₀ =
                  - (covDerivRm_lowered emb conn met (σ a) (σ i) Y (σ b) (σ j)) x₀ from
                congrArg (fun f : R_ I M => f x₀)
                  (covDerivRm_lowered_antisymm_first_pair emb conn ha hal met
                    (σ a) Y (σ i) (σ b) (σ j))]
              ring
      _ = -∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j) := by
          simp only [Finset.sum_neg_distrib]
  calc
    (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ i) Y (σ a) (σ b) (σ j))
        = ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ i) (σ b) (σ j) Y (σ a) := hblock
    _ = ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) (σ b) Y (σ j) := hperm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j) := by
      have h := hfirstBianchi_sum
      rw [hmiddle_zero, hthird] at h
      have h' :
          (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) (σ b) Y (σ j)) =
            ∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j) := by
        have hsub :
            (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) (σ b) Y (σ j)) -
              (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j)) = 0 := by
          simpa [sub_eq_add_neg, add_assoc] using h
        exact sub_eq_zero.mp hsub
      exact h'

/-- Tensor-level form of
`concreteContractedBianchiDivPattern_apply_cycle_right_eq_gradPattern`. The
right cyclic term is pure slot bookkeeping: tracing the right cycle by the
divergence pattern is exactly the named gradient pattern on the original
tensor. -/
theorem concreteContractedBianchiDivPattern_tensor_cycle_right_eq_gradPattern
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5) :
    DoubleMetricTrace05Pattern.contractedBianchiDivPattern.tensor met
        (concreteAbstractTrace I M) (covariantCycle012Right05 T) =
      DoubleMetricTrace05Pattern.contractedBianchiGradPattern.tensor met
        (concreteAbstractTrace I M) T := by
  ext m n x₀
  have hm : m = ![m 0] := by
    ext i
    fin_cases i
    rfl
  have hn : n = ![] := by
    ext i
    exact i.elim0
  rw [hm, hn]
  exact congrArg (fun f : R_ I M => f x₀)
    (concreteContractedBianchiDivPattern_apply_cycle_right_eq_gradPattern
      I M met T (m 0))

theorem concreteContractedBianchiDivMetricTraceFubini
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5) :
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern.Fubini
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met
        (concreteAbstractTrace I M) T := by
  unfold DoubleMetricTrace05Pattern.Fubini DoubleMetricTrace05Fubini
  unfold doubleMetricTrace05
  ext m n x₀
  have hm : m = ![m 0] := by
    ext i
    fin_cases i
    rfl
  have hn : n = ![] := by
    ext i
    exact i.elim0
  rw [hm, hn]
  simp only [metric_trace, raise_index, contract_general]
  simp only [concreteAbstractTrace_tensor_contract]
  repeat' rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval]
  conv_lhs =>
    congr
    · skip
    · intro i
      rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  conv_rhs =>
    congr
    · skip
    · intro i
      rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval]
  simp_rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  simp only [swap_covariant_eval, swap_contravariant_eval, tensor_prod_eval]
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  simp only [DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern,
    DoubleMetricTrace05Pattern.contractedBianchiDivPattern]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_four_contract_bianchi_perm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  simp only [Nat.reduceAdd, Fin.isValue, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Equiv.swap_self, Equiv.coe_refl, CompTriple.comp_eq, fin_zero_fun_eq_empty,
    Nat.add_zero, Matrix.Fin.cons_vecEmpty, Fin.mk_one, Matrix.cons_cons_comp_swap_zero_one,
    Fin.castAdd_zero, Fin.cast_refl, Fin.natAdd_zero]
  have hvec :
      (Fin.cons (σ j) (Fin.cons (σ i) (![σ a, σ b, m 0] ∘ ⇑(Equiv.swap 0 2))) ∘
          ⇑(Equiv.swap 0 4)) =
        (Fin.cons (σ b)
            (Fin.cons (σ a) (![σ j, σ i, m 0] ∘ ⇑(Equiv.swap 0 2)) ∘ ⇑(Equiv.swap 0 2)) ∘
          ⇑(Equiv.swap 0 3)) := by
    ext k
    fin_cases k <;> rfl
  rw [hvec]
  have hsym_ab :
      (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 b),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 a)]) x₀) =
        (((met.g_inv ![])
          ![covectorToFunctional I M ((chooseLocalFrames I M x₀).2 a),
            covectorToFunctional I M ((chooseLocalFrames I M x₀).2 b)]) x₀) := by
    exact congrArg (fun f : R_ I M => f x₀)
      (met.g_inv_symm
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 b))
        (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 a)))
  rw [hsym_ab]
  ring

/-- Direct tensor equality form of the concrete contracted-Bianchi double
`metric_trace` Fubini theorem. This is the API downstream proofs should prefer
when they do not need a typeclass instance. -/
theorem concreteContractedBianchiDivMetricTraceFubini_tensor
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5) :
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern.tensor met
        (concreteAbstractTrace I M) T =
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern.tensor met
        (concreteAbstractTrace I M) T := by
  exact DoubleMetricTrace05Pattern.tensor_eq_of_fubini
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
    DoubleMetricTrace05Pattern.contractedBianchiDivPattern met
    (concreteAbstractTrace I M) T
    (concreteContractedBianchiDivMetricTraceFubini I M met T)

/-- Direct evaluated form of the concrete contracted-Bianchi double
`metric_trace` Fubini theorem. -/
theorem concreteContractedBianchiDivMetricTraceFubini_apply
    (met : MetricDuality (R_ I M) (V_ I M))
    (T : TensorData (R_ I M) (V_ I M) 0 5) (X : V_ I M) :
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern.apply met
        (concreteAbstractTrace I M) T X =
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
        (concreteAbstractTrace I M) T X := by
  exact DoubleMetricTrace05Pattern.apply_eq_of_fubini
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
    DoubleMetricTrace05Pattern.contractedBianchiDivPattern met
    (concreteAbstractTrace I M) T
    (concreteContractedBianchiDivMetricTraceFubini I M met T) X

/-- Concrete left-cycle trace audit in the exact named-pattern form used by
the contracted second Bianchi package. The proof combines the curvature
symmetry calculation
`concreteContractedBianchiDivPattern_apply_cycle_left_eq_divPattern_lowered`
with concrete double metric-trace Fubini, which identifies the two divergence
trace orders. -/
theorem concreteContractedBianchiDivPattern_apply_cycle_left_eq_divFubini_lowered
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M))
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (Y : V_ I M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M)
      (covariantCycle012Left05
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y) =
    (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern.apply met
      (concreteAbstractTrace I M)
      (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y) := by
  calc
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
      (concreteAbstractTrace I M)
      (covariantCycle012Left05
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y)
        =
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern.apply met
        (concreteAbstractTrace I M)
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y) := by
        exact concreteContractedBianchiDivPattern_apply_cycle_left_eq_divPattern_lowered
          I M emb conn ha hal hsl hl met h_mc h_tf Y
    _ =
      (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern.apply met
        (concreteAbstractTrace I M)
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y) := by
        exact (concreteContractedBianchiDivMetricTraceFubini_apply I M met
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y).symm

/-- Concrete standard traces satisfy metric double-trace Fubini for the
contracted-Bianchi divergence patterns, for any synthetic metric duality over
the concrete smooth-section module. -/
instance concreteHasContractedBianchiDivMetricTraceFubini
    (met : MetricDuality (R_ I M) (V_ I M)) :
    HasDoubleMetricTrace05PatternFubini
      DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met
      (concreteAbstractTrace I M) where
  tensor_contract_fubini := concreteTensorContractFubini I M
  metric_trace_fubini := concreteContractedBianchiDivMetricTraceFubini I M met

private theorem Finset.sum_four_swap_pairs
    {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (F : ι -> ι -> ι -> ι -> R) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := by
  classical
  have hpack : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) =
      ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) := {
    toFun p := (p.2.2.1, p.2.2.2, p.1, p.2.1)
    invFun p := (p.2.2.1, p.2.2.2, p.1, p.2.1)
    left_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl
    right_inv p := by
      rcases p with ⟨i, j, a, b⟩
      rfl }
  have hunpack :
      (∑ p : ι × ι × ι × ι,
          F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2) =
        ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  calc
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
        = ∑ p : ι × ι × ι × ι, F p.1 p.2.1 p.2.2.1 p.2.2.2 := hpack
    _ = ∑ p : ι × ι × ι × ι,
          F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2 := by
            exact (Equiv.sum_comp e (fun p : ι × ι × ι × ι =>
              F p.1 p.2.1 p.2.2.1 p.2.2.2)).symm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := hunpack

/-- Concrete traces discharge the cyclic slot-audit obligations in P1.

The right cyclic term is pure slot bookkeeping. The left cyclic term is the
general tensor-calculus contraction proved in `MetricTraceFubini.lean`: expand
the metric traces, use differentiated block symmetry, first Bianchi, and the
fact that a symmetric inverse-metric trace kills an antisymmetric pair, then
fold back through metric-trace Fubini. -/
theorem concreteContractedBianchiSlotAuditObligations
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M))
    (h_tf : IsTorsionFree emb conn) :
    ContractedBianchiSlotAuditObligations emb conn ha hal hsl hl
      (concreteAbstractTrace I M) met where
  cycle_left_apply_eq_divFubiniPattern := by
    intro h_mc Y
    exact concreteContractedBianchiDivPattern_apply_cycle_left_eq_divFubini_lowered
      I M emb conn ha hal hsl hl met h_mc h_tf Y
  cycle_right_apply_eq_gradPattern := by
    intro h_mc Y
    exact concreteContractedBianchiDivPattern_apply_cycle_right_eq_gradPattern I M met
      (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y

/-- Concrete local-frame calculation for the divergence named pattern.

This proves the raw trace form expected by `CurvatureAlgebra.lean`: the named
double trace is the trace of the swapped-Ricci divergence endomorphism. The
remaining conversion from this swapped Ricci slot to the public
`ricciDivergenceAt` accessor is handled in the synthetic wrapper using Ricci
symmetry. -/
theorem concreteContractedBianchiDivPattern_apply_eq_neg_trace_swap_ricci_divergence_endomorphism
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M))
    (h_mc : IsMetricCompatible emb conn met)
    (h_ntr : NablaTrComm emb (concreteAbstractTrace I M) conn ha hl)
    (Y : V_ I M) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met
        (concreteAbstractTrace I M)
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
      - (concreteAbstractTrace I M).tr
        (covDivergence02Endomorphism emb met conn ha hal hsl hl
          (swap_covariant (0 : Fin 2) 1
            (ricciForm_tensor emb conn ha hal hsl hl (concreteAbstractTrace I M))) Y) := by
  classical
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteContractedBianchiDivPattern_apply_unfold I M met
    (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y x₀]
  rw [concreteAbstractTrace_tr]
  simp only [ContMDiffMap.coe_neg, Pi.neg_apply]
  rw [concreteTr_metric_pairing_unfold I M met
    (covDivergence02Endomorphism emb met conn ha hal hsl hl
      (swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl (concreteAbstractTrace I M))) Y) x₀]
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  let c : Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) ->
      Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) -> ℝ :=
    fun i j a b =>
      (((met.g_inv ![]) ![θ b, θ a]) x₀) *
        (((met.g_inv ![]) ![θ j, θ i]) x₀)
  let Tval :
      V_ I M -> V_ I M -> V_ I M -> V_ I M -> V_ I M -> ℝ :=
    fun A X Z W U => (covDerivRm_lowered emb conn met A X Z W U) x₀
  simp only [LoweredCovDerivRmTensorData.eval_apply]
  change
    (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval (σ a) (σ i) Y (σ b) (σ j)) =
      - (∑ i, ∑ j,
        (((met.g_inv ![]) ![θ i, θ j]) x₀) *
          (met.g
            (covDivergence02Endomorphism emb met conn ha hal hsl hl
              (swap_covariant (0 : Fin 2) 1
                (ricciForm_tensor emb conn ha hal hsl hl (concreteAbstractTrace I M))) Y (σ i))
            (σ j) x₀))
  have htrace :
      (∑ i, ∑ j,
        (((met.g_inv ![]) ![θ i, θ j]) x₀) *
          (met.g
            (covDivergence02Endomorphism emb met conn ha hal hsl hl
              (swap_covariant (0 : Fin 2) 1
                (ricciForm_tensor emb conn ha hal hsl hl (concreteAbstractTrace I M))) Y (σ i))
            (σ j) x₀)) =
        - ((∑ i, ∑ j, ∑ a, ∑ b,
          c i j a b * Tval (σ i) (σ a) Y (σ j) (σ b)) : ℝ) := by
    rw [show
        - ((∑ i, ∑ j, ∑ a, ∑ b,
          c i j a b * Tval (σ i) (σ a) Y (σ j) (σ b)) : ℝ) =
          ∑ i, ∑ j, ∑ a, ∑ b,
            -(c i j a b * Tval (σ i) (σ a) Y (σ j) (σ b)) by
      simp only [Finset.sum_neg_distrib]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [covDivergence02Endomorphism_swap_ricciForm_metric_apply emb conn ha hal hsl hl
      (concreteAbstractTrace I M) met (σ i) Y (σ j)]
    rw [covDerivRc_eq_trace_covDerivRmEndomorphism emb conn ha hal hsl hl
      (concreteAbstractTrace I M) h_ntr (σ i) Y (σ j)]
    rw [concreteAbstractTrace_tr]
    rw [concreteTr_metric_pairing_unfold I M met
      (covDerivRmEndomorphism emb conn ha hal hsl hl (σ i) Y (σ j)) x₀]
    change
      (((met.g_inv ![]) ![θ i, θ j]) x₀) *
          (∑ a, ∑ b,
            (((met.g_inv ![]) ![θ a, θ b]) x₀) *
              (met.g
                (covDerivRmEndomorphism emb conn ha hal hsl hl (σ i) Y (σ j) (σ a))
                (σ b) x₀)) =
        ∑ a, ∑ b, -(c i j a b * Tval (σ i) (σ a) Y (σ j) (σ b))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [covDerivRmEndomorphism_apply emb conn ha hal hsl hl (σ i) Y (σ j) (σ a)]
    unfold c Tval
    have hanti := congrArg (fun f : R_ I M => f x₀)
      (covDerivRm_lowered_antisymm_first_pair emb conn ha hal met
        (σ i) Y (σ a) (σ j) (σ b))
    have hanti' :
        (covDerivRm_lowered emb conn met (σ i) Y (σ a) (σ j) (σ b)) x₀ =
          - (covDerivRm_lowered emb conn met (σ i) (σ a) Y (σ j) (σ b)) x₀ := by
      simpa only [Pi.neg_apply] using hanti
    have hsym_ab :
        (((met.g_inv ![]) ![θ a, θ b]) x₀) =
          (((met.g_inv ![]) ![θ b, θ a]) x₀) := by
      exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ a) (θ b))
    have hsym_ij :
        (((met.g_inv ![]) ![θ i, θ j]) x₀) =
          (((met.g_inv ![]) ![θ j, θ i]) x₀) := by
      exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ i) (θ j))
    change
      ((met.g_inv ![]) ![θ i, θ j]) x₀ * (((met.g_inv ![]) ![θ a, θ b]) x₀ *
          (covDerivRm_lowered emb conn met (σ i) Y (σ a) (σ j) (σ b)) x₀) =
        - (c i j a b * Tval (σ i) (σ a) Y (σ j) (σ b))
    rw [hanti', hsym_ab, hsym_ij]
    ring
  rw [htrace]
  simp only [neg_neg]
  conv_lhs =>
    rw [Finset.sum_four_swap_pairs]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold c
  ring

/-- Concrete local-frame calculation for the scalar-gradient named pattern.

The synthetic wrappers in `CurvatureAlgebra.lean` reduce the public
`gradPattern = -grad_R` statement to this raw trace identity. The calculation
expands both traces in the same chosen frame and uses the last-pair
antisymmetry of the lowered covariant Riemann tensor to account for the sign. -/
theorem concreteContractedBianchiGradPattern_apply_eq_trace_covDerivRicciEndomorphism
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M))
    (h_mc : IsMetricCompatible emb conn met)
    (h_ntr : NablaTrComm emb (concreteAbstractTrace I M) conn ha hl)
    (Y : V_ I M) :
    (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met
        (concreteAbstractTrace I M)
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
      (concreteAbstractTrace I M).tr
          (covDerivRicciEndomorphism emb conn ha hal hsl hl
            (concreteAbstractTrace I M) met Y) := by
  classical
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteContractedBianchiGradPattern_apply_unfold I M met
    (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y x₀]
  rw [concreteAbstractTrace_tr]
  change
    (let σ := (chooseLocalFrames I M x₀).1
     let θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
     ∑ i, ∑ j, ∑ a, ∑ b,
       (((met.g_inv ![]) ![θ b, θ a]) x₀) *
       (((met.g_inv ![]) ![θ j, θ i]) x₀) *
       (((loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor
          ![Y, σ a, σ i, σ b, σ j]) ![]) x₀) =
      ((concreteTr I M)
          (covDerivRicciEndomorphism emb conn ha hal hsl hl
            (concreteAbstractTrace I M) met Y) x₀)
  rw [concreteTr_metric_pairing_unfold I M met
    (covDerivRicciEndomorphism emb conn ha hal hsl hl
      (concreteAbstractTrace I M) met Y) x₀]
  set σ := (chooseLocalFrames I M x₀).1
  set θ := fun q => covectorToFunctional I M ((chooseLocalFrames I M x₀).2 q)
  let c : Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) ->
      Fin (Module.finrank ℝ E) -> Fin (Module.finrank ℝ E) -> ℝ :=
    fun i j a b =>
      (((met.g_inv ![]) ![θ b, θ a]) x₀) *
        (((met.g_inv ![]) ![θ j, θ i]) x₀)
  let Tval :
      V_ I M -> V_ I M -> V_ I M -> V_ I M -> V_ I M -> ℝ :=
    fun A X Z W U => (covDerivRm_lowered emb conn met A X Z W U) x₀
  simp only [LoweredCovDerivRmTensorData.eval_apply]
  change
    (∑ i, ∑ j, ∑ a, ∑ b, c i j a b * Tval Y (σ a) (σ i) (σ b) (σ j)) =
      (∑ i, ∑ j,
          (((met.g_inv ![]) ![θ i, θ j]) x₀) *
            (met.g
              (covDerivRicciEndomorphism emb conn ha hal hsl hl
                (concreteAbstractTrace I M) met Y (σ i)) (σ j) x₀))
  have htrace :
      (∑ i, ∑ j,
          (((met.g_inv ![]) ![θ i, θ j]) x₀) *
            (met.g
              (covDerivRicciEndomorphism emb conn ha hal hsl hl
                (concreteAbstractTrace I M) met Y (σ i)) (σ j) x₀)) =
        - ((∑ i, ∑ j, ∑ a, ∑ b,
          c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b)) : ℝ) := by
    rw [show
        - ((∑ i, ∑ j, ∑ a, ∑ b,
          c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b)) : ℝ) =
          ∑ i, ∑ j, ∑ a, ∑ b,
            -(c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b)) by
      simp only [Finset.sum_neg_distrib]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [covDerivRicciEndomorphism_metric_apply emb conn ha hal hsl hl
      (concreteAbstractTrace I M) met h_mc Y (σ i) (σ j)]
    rw [covDerivRc_eq_trace_covDerivRmEndomorphism emb conn ha hal hsl hl
      (concreteAbstractTrace I M) h_ntr Y (σ i) (σ j)]
    rw [concreteAbstractTrace_tr]
    rw [concreteTr_metric_pairing_unfold I M met
      (covDerivRmEndomorphism emb conn ha hal hsl hl Y (σ i) (σ j)) x₀]
    change
      (((met.g_inv ![]) ![θ i, θ j]) x₀) *
          (∑ a, ∑ b,
            (((met.g_inv ![]) ![θ a, θ b]) x₀) *
              (met.g
                (covDerivRmEndomorphism emb conn ha hal hsl hl Y (σ i) (σ j) (σ a))
                (σ b) x₀)) =
        ∑ a, ∑ b, -(c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [covDerivRmEndomorphism_apply emb conn ha hal hsl hl Y (σ i) (σ j) (σ a)]
    unfold c Tval
    have hanti_first := congrArg (fun f : R_ I M => f x₀)
      (covDerivRm_lowered_antisymm_first_pair emb conn ha hal met
        Y (σ i) (σ a) (σ j) (σ b))
    have hanti_first' :
        (covDerivRm_lowered emb conn met Y (σ i) (σ a) (σ j) (σ b)) x₀ =
          - (covDerivRm_lowered emb conn met Y (σ a) (σ i) (σ j) (σ b)) x₀ := by
      simpa only [Pi.neg_apply] using hanti_first
    have hsym_ab :
        (((met.g_inv ![]) ![θ a, θ b]) x₀) =
          (((met.g_inv ![]) ![θ b, θ a]) x₀) := by
      exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ a) (θ b))
    have hsym_ij :
        (((met.g_inv ![]) ![θ i, θ j]) x₀) =
          (((met.g_inv ![]) ![θ j, θ i]) x₀) := by
      exact congrArg (fun f : R_ I M => f x₀) (met.g_inv_symm (θ i) (θ j))
    change
      ((met.g_inv ![]) ![θ i, θ j]) x₀ * (((met.g_inv ![]) ![θ a, θ b]) x₀ *
          (covDerivRm_lowered emb conn met Y (σ i) (σ a) (σ j) (σ b)) x₀) =
        - (c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b))
    rw [hanti_first', hsym_ab, hsym_ij]
    ring
  rw [htrace]
  rw [show
      - (∑ i, ∑ j, ∑ a, ∑ b,
          c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b)) =
        (∑ i, ∑ j, ∑ a, ∑ b,
          -(c i j a b * Tval Y (σ a) (σ i) (σ j) (σ b))) by
    simp only [Finset.sum_neg_distrib]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold c Tval
  have hanti := congrArg (fun f : R_ I M => f x₀)
    (covDerivRm_lowered_antisymm_second_pair emb conn met h_mc
      Y (σ a) (σ i) (σ b) (σ j))
  have hanti' :
      (covDerivRm_lowered emb conn met Y (σ a) (σ i) (σ b) (σ j)) x₀ =
        - (covDerivRm_lowered emb conn met Y (σ a) (σ i) (σ j) (σ b)) x₀ := by
    simpa only [Pi.neg_apply] using hanti
  rw [hanti']
  ring

/-- Concrete standard-trace named-pattern calculus for P1.

This packages the concrete slot audit plus the two raw double-trace
identifications into the public synthetic class consumed by the Hamilton-level
P1 wrapper. Trace-adjoint invariance and `NablaTrComm` remain external
coherence inputs of the class methods; the theorem only registers that the
concrete standard trace has the required named-pattern calculations. -/
theorem concreteHasContractedSecondBianchiNamedPatternCalculus
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M))
    [HasMetricAdjointTraceInvariant (concreteAbstractTrace I M) met]
    (h_tf : IsTorsionFree emb conn) :
    HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl
      (concreteAbstractTrace I M) met :=
  hasContractedSecondBianchiNamedPatternCalculus_of_trace_divergence_trace_adjoint_and_grad_trace
    emb conn ha hal hsl hl (concreteAbstractTrace I M) met
    (concreteContractedBianchiSlotAuditObligations
      I M emb conn ha hal hsl hl met h_tf)
    h_tf (concreteSmooth_two_cancel I M)
    (fun h_mc h_ntr Y =>
      concreteContractedBianchiDivPattern_apply_eq_neg_trace_swap_ricci_divergence_endomorphism
        I M emb conn ha hal hsl hl met h_mc h_ntr Y)
    (fun h_mc h_ntr Y =>
      concreteContractedBianchiGradPattern_apply_eq_trace_covDerivRicciEndomorphism
        I M emb conn ha hal hsl hl met h_mc h_ntr Y)

/-- Concrete P1 contraction theorem.

This is the realization-side closure of the remaining named-pattern
calculation for `concreteAbstractTrace`. The synthetic file
`CurvatureAlgebra.lean` supplies the algebraic wrappers; this theorem supplies
the concrete raw trace identities:

* `divPattern = tr(swapped Ricci divergence endomorphism)`;
* `gradPattern = -tr(∇ Ric♯)`;
* the cyclic slot audit and double-trace Fubini from
  `MetricTraceFubini.lean`.

Trace-commutation and trace-invariance under metric adjoints remain explicit
coherence inputs, because this file works with an arbitrary synthetic
connection and metric duality over the concrete smooth-section module. -/
theorem concreteContractedSecondBianchiIdentity
    (emb : DerivationEmbedding ℝ (R_ I M) (V_ I M))
    (conn : V_ I M -> V_ I M -> V_ I M)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R_ I M) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R_ I M) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality (R_ I M) (V_ I M)) (half : R_ I M)
    (h_half : IsHalfCoefficient half)
    [HasMetricAdjointTraceInvariant (concreteAbstractTrace I M) met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (h_ntr : NablaTrComm emb (concreteAbstractTrace I M) conn ha hl) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl
      (concreteAbstractTrace I M) met half := by
  haveI :
      HasDoubleMetricTrace05PatternFubini
        DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
        DoubleMetricTrace05Pattern.contractedBianchiDivPattern met
        (concreteAbstractTrace I M) :=
    concreteHasContractedBianchiDivMetricTraceFubini I M met
  haveI :
      HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl
        (concreteAbstractTrace I M) met :=
    concreteHasContractedSecondBianchiNamedPatternCalculus
      I M emb conn ha hal hsl hl met h_tf
  exact
    contractedSecondBianchiIdentity_from_second_bianchi_named_patterns
      emb conn ha hal hsl hl (concreteAbstractTrace I M) met half h_half
      h_mc h_tf h_ntr

end TensorContractRealization

end
