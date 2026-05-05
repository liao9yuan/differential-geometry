import DifferentialGeometry.Synthetic.Realization.TensorContract
import DifferentialGeometry.Synthetic.Realization.LeviCivita
import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.RiemannFromRicci3D

/-!
# Concrete Orthonormal Trace Formula

This file is the realization-layer entry point for the P2 trace hypothesis
`HasOrthonormalBasisTraceFormula3`.

The concrete trace `concreteAbstractTrace I M` is already defined fiberwise by
`LinearMap.trace` and has a local-frame expansion in `Trace.lean`.  What P2
needs is a stronger global-section statement:

```lean
tr L = sum_i g(e_i, L e_i)
```

for every synthetic `Fin 3` orthonormal basis of smooth tangent sections.  That
does not follow merely from the local-frame trace formula: one still has to
prove that evaluating such a global section basis at each point gives a
pointwise real basis of the tangent fiber, then compare the abstract metric
pairing with the fiber trace formula.

The theorem below therefore exposes the exact remaining concrete obligation and
turns it into the synthetic P2 class.  This keeps the P2 package honest while
giving later coordinate/orthonormal-frame work a stable target.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology BigOperators
open Bundle SyntheticTensor

section OrthonormalTraceRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
private abbrev R_ := C^∞⟮I, M; ℝ⟯

/-- Concrete P2 trace obligation for a chosen Riemannian metric.

This is intentionally a proposition rather than an instance.  A future
coordinate proof should discharge it from the fiberwise trace formula for
`concreteTr`, the pointwise basis obtained by evaluating `basis`, and the
orthonormality condition against `concreteMetricDuality I M g`. -/
def ConcreteOrthonormalBasisTraceFormula3
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    Prop :=
  ∀ (basis : Module.Basis (Fin 3) (R_ I M) (V_ I M)),
    IsMetricOrthonormalBasis3 (concreteMetricDuality I M g) basis →
      ∀ L : V_ I M →ₗ[R_ I M] V_ I M,
        (TensorContractRealization.concreteAbstractTrace I M).tr L =
          ∑ i : Fin 3, (concreteMetricDuality I M g).g (basis i) (L (basis i))

private theorem eval_metric_orthonormal
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (basis : Module.Basis (Fin 3) (R_ I M) (V_ I M))
    (hortho : IsMetricOrthonormalBasis3 (concreteMetricDuality I M g) basis)
    (x : M) (i j : Fin 3) :
    g.inner x ((basis i) x) ((basis j) x) = if i = j then (1 : ℝ) else 0 := by
  have hfun := hortho i j
  have hx := congrArg (fun f : R_ I M => f x) hfun
  change ((concreteMetricDuality I M g).g (basis i) (basis j)) x =
    ((if i = j then (1 : R_ I M) else 0) x) at hx
  rw [concreteMetricDuality_g_eval] at hx
  by_cases hij : i = j
  · simp only [hij, if_true] at hx ⊢
    simpa only [ContMDiffMap.coe_one, Pi.one_apply] using hx
  · simp only [hij, if_false] at hx ⊢
    simpa only [ContMDiffMap.coe_zero, Pi.zero_apply] using hx

private theorem eval_section_basis_span
    (basis : Module.Basis (Fin 3) (R_ I M) (V_ I M)) (x : M) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i : Fin 3 => (basis i) x)) := by
  intro v _
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hsum := congrArg (fun τ : V_ I M => τ x) (basis.sum_repr σ)
  change (∑ i : Fin 3, ((basis.repr σ) i x) • (basis i x)) = σ x at hsum
  rw [← hσ, ← hsum]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))

private theorem eval_orthonormal_section_basis_linearIndependent
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (basis : Module.Basis (Fin 3) (R_ I M) (V_ I M))
    (hortho : IsMetricOrthonormalBasis3 (concreteMetricDuality I M g) basis)
    (x : M) :
    LinearIndependent ℝ (fun i : Fin 3 => (basis i) x) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum j
  have hpair := congrArg (fun v : TangentSpace I x => g.inner x ((basis j) x) v) hsum
  change g.inner x ((basis j) x) (∑ i : Fin 3, c i • ((basis i) x)) =
    g.inner x ((basis j) x) (0 : TangentSpace I x) at hpair
  rw [(g.inner x ((basis j) x)).map_zero] at hpair
  have hsum_pair :
      g.inner x ((basis j) x) (∑ i : Fin 3, c i • ((basis i) x)) =
        ∑ i : Fin 3, c i * g.inner x ((basis j) x) ((basis i) x) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  rw [hsum_pair] at hpair
  rw [show (∑ i : Fin 3, c i * g.inner x ((basis j) x) ((basis i) x)) = c j by
    simp only [eval_metric_orthonormal I M g basis hortho x]
    simp] at hpair
  exact hpair

private theorem eval_section_basis_coord_eq_metric
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (basis : Module.Basis (Fin 3) (R_ I M) (V_ I M))
    (hortho : IsMetricOrthonormalBasis3 (concreteMetricDuality I M g) basis)
    (x : M)
    (fiberBasis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hb_apply : ∀ j : Fin 3, fiberBasis j = (basis j) x)
    (i : Fin 3) (v : TangentSpace I x) :
    fiberBasis.coord i v = g.inner x ((basis i) x) v := by
  have hpair_sum :
      g.inner x ((basis i) x) (∑ j : Fin 3, fiberBasis.repr v j • fiberBasis j) =
        ∑ j : Fin 3, fiberBasis.repr v j * g.inner x ((basis i) x) (fiberBasis j) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    rfl
  calc
    fiberBasis.coord i v = fiberBasis.repr v i := rfl
    _ = ∑ j : Fin 3, fiberBasis.repr v j * g.inner x ((basis i) x) (fiberBasis j) := by
      rw [show (∑ j : Fin 3,
          fiberBasis.repr v j * g.inner x ((basis i) x) (fiberBasis j)) =
            fiberBasis.repr v i by
        simp only [hb_apply, eval_metric_orthonormal I M g basis hortho x]
        simp]
    _ = g.inner x ((basis i) x) (∑ j : Fin 3, fiberBasis.repr v j • fiberBasis j) :=
      hpair_sum.symm
    _ = g.inner x ((basis i) x) v := by rw [fiberBasis.sum_repr]

/-- Concrete proof of the P2 orthonormal trace formula.

At each point, evaluating a global `C∞(M)`-basis of sections gives a real
basis of the tangent fiber: spanning follows by extending a tangent vector to
a smooth section, and linear independence follows from the evaluated
orthonormality equations.  The fiberwise trace is then the ordinary matrix
trace in that basis. -/
theorem concreteOrthonormalBasisTraceFormula3
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    ConcreteOrthonormalBasisTraceFormula3 I M g := by
  intro basis hortho L
  rw [TensorContractRealization.concreteAbstractTrace_tr]
  apply ContMDiffMap.ext
  intro x
  change concreteTr_fun I M L x =
    (∑ i : Fin 3, (concreteMetricDuality I M g).g (basis i) (L (basis i))) x
  change concreteTr_fun I M L x =
    ∑ i : Fin 3, g.inner x ((basis i) x) ((L (basis i)) x)
  let hli := eval_orthonormal_section_basis_linearIndependent I M g basis hortho x
  let hsp := eval_section_basis_span I M basis x
  let fiberBasis : Module.Basis (Fin 3) ℝ (TangentSpace I x) := Module.Basis.mk hli hsp
  have hb_apply : ∀ i : Fin 3, fiberBasis i = (basis i) x := fun i =>
    Module.Basis.mk_apply _ _ _
  change LinearMap.trace ℝ (TangentSpace I x) (vbcFiber I M L x) =
    ∑ i : Fin 3, g.inner x ((basis i) x) ((L (basis i)) x)
  rw [LinearMap.trace_eq_matrix_trace ℝ fiberBasis]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change fiberBasis.coord i ((vbcFiber I M L x) (fiberBasis i)) =
    g.inner x ((basis i) x) ((L (basis i)) x)
  rw [eval_section_basis_coord_eq_metric I M g basis hortho x fiberBasis hb_apply]
  rw [hb_apply]
  rw [vbcFiber_spec I M L (basis i) x]

/-- Turn the concrete trace formula into the synthetic P2 typeclass.

This is the missing `concreteHasOrthonormalBasisTraceFormula3` entry point. -/
theorem concreteHasOrthonormalBasisTraceFormula3
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    HasOrthonormalBasisTraceFormula3
      (TensorContractRealization.concreteAbstractTrace I M) (concreteMetricDuality I M g) where
  tr_eq_sum_orthonormal3 := concreteOrthonormalBasisTraceFormula3 I M g

end OrthonormalTraceRealization

end
