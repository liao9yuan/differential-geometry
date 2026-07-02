import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotExtendCovariantParallelism
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RankRReadingDominationUniformSup

/-! # Operator-field fibre-norm jet estimates for the valence-dropping drop tower

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the foundational intrinsic fibre-norm (`rfns`) estimates that
bound the `covGrad`/`slotExtend` covariant jets `dropTowerPsi g b₀ s₀ C p w k` of a fixed coefficient
operator field `C : SmoothCcTensor g b₀ s₀` by the section-level iterated covariant gradients
`iteratedCovGrad g b₀ s₀ j C` of `C` itself, with a polynomial factor that is *independent* of `C`
(depending only on `Module.finrank ℝ E` and the indices).

## The foundational fibre-norm estimates

* `rfns_rs_eq_sum_componentSq_of_basis` — the valence-generic frame Parseval: the intrinsic fibre norm
  squared is the double-multi-index sum of squared `g_x`-orthonormal-frame components, for an arbitrary
  caller-supplied frame at *any* tensor valence (the `(r, s)` lift of
  `rfns_eq_sum_fiberNormSqSummand_of_orthoFrame`).
* `rfns_slotExtendFib_eq` / `rfns_slotExtend_eq` — the **passenger-slot scaling**: inserting one leading
  covariant passenger slot scales the intrinsic fibre norm by the dimension factor `n = finrank ℝ E`:
  `rfns(slotExtend g r s Φ) x = n · rfns(Φ) x`.
* `rfns_slotExtendIter_eq` — the iterated form: `rfns(slotExtendIter g r s w Φ) x = n^w · rfns(Φ) x`.
* `rfns_covGrad_slotExtend_eq` / `rfns_covGrad_slotExtend_scale` — the **gradient/slot-extension
  fibre-norm commutation**: `covGrad (slotExtend Φ)` and `slotExtend (covGrad Φ)` differ by a
  transposition of the two leading covariant output slots (the gradient slot and the passenger slot are
  read in the opposite order), so they have *equal* intrinsic fibre norm; combined with the passenger
  scaling, `rfns(covGrad (slotExtend Φ)) x = n · rfns(covGrad Φ) x`.  This is the slot-insertion ×
  differentiation fibre-norm interaction at the heart of the valence-dropping `dropTowerPsi` jet bound.

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` (`rfns`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## A single `g_x`-orthonormal frame representing the fibre norm at every valence -/

/-- **A single `g_x`-orthonormal frame (as a `Module.Basis`), usable at every tensor valence.**  The
`stdOrthonormalBasis` of the metric-induced inner product on `TangentSpace I x`, packaged as a
`Module.Basis bse` with `n = Module.finrank ℝ E` directions and the δ-form Gram.  Unlike
`exists_orthonormal_frame_riemannianFiberNormSq` (which bundles a per-valence representation), this
exposes the underlying frame and its `Module.Basis` witness, so the valence-generic Parseval
`rfns_rs_eq_sum_componentSq_of_basis` can be applied at *two different valences with the same frame*. -/
private lemma exists_orthoFrame_basis (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  classical
  obtain ⟨n, e0, hn, horth0, _hpars, _hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g 0 0 x
  subst hn
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := e0 with he_def
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth0
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  refine ⟨e, basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_, horth⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **The intrinsic `(r, s)` fibre norm is the frame component-square sum in any `g_x`-orthonormal
frame (valence-generic, public).**  For any `g_x`-orthonormal frame `e` packaged as a `Module.Basis
bse` with `n = Module.finrank ℝ E`, the intrinsic fibre norm squared is the double-multi-index sum of
squared frame components.  The valence-generic Parseval (the rank-`(r, s)` lift of
`rfns_eq_sum_fiberNormSqSummand_of_orthoFrame`), obtained from the bilinear frame inner-product bridge
`tensorInnerPointwise_eq_sum_componentS_mul` (diagonal) through
`riemannianFiberNormSq_eq_tensorInnerPointwise`. -/
theorem rfns_rs_eq_sum_componentSq_of_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x S]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g r s x e bse hn hbse horth S S]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  rw [pow_two]

/-! ## The passenger-slot scaling of the fibre norm -/

/-- **The slot-`0` reading frame component of a slot-extended fibre operator.**  For a `g_x`-orthonormal
frame `e`, the `(K', J')`-frame component of the slot-extended fibre operator `slotExtendFib g r s x A`
(an `(r + 1, s + 1)`-tensor) factors as the Kronecker delta `[K' 0 = J' 0]` times the `(K' ∘ succ,
J' ∘ succ)` frame component of the rank-`(r, s)` operator `A`: the leading passenger slot is read
identically on source and target (`slotExtendFib_apply_eval`), and orthonormality of `e` selects the
diagonal `K' 0 = J' 0`. -/
private lemma fiberNormSqComponent_slotExtendFib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
        n e K' J' =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) *
        fiberNormSqComponent (I := I) (M := M) g x r s
          (show TensorRSSpace r s I x from A) n e
          (fun k => K' (Fin.succ k)) (fun k => J' (Fin.succ k)) := by
  classical
  -- The component is `toModel (slotExtendFib A (ω^{K'})) (e ∘ J')`; read off the leading slot.
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
        n e K' J' =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g r s x A
          (coframeS (I := I) (M := M) g x (r + 1) e K'))
        (Fin.cons (show E from e (J' 0)) (fun k : Fin s => (show E from e (J' (Fin.succ k))))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
          (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
          n e K' J' =
        Tensor0SSpace.toModel
          (slotExtendFib (I := I) (M := M) g r s x A
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => (show E from e (J' k))) from rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
  rw [hcomp]
  -- Read the leading slot off `J'` via `slotExtendFib_apply_eval`.
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x A
    (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0))
    (fun k : Fin s => (show E from e (J' (Fin.succ k))))]
  -- The curried passenger reading of the coframe covector picks out the `K' 0 = J' 0` delta.
  have hcurry : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
        (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0)) =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) •
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := r)
      (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0)) u]
    have hcf : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x (r + 1) e K')
          (Fin.cons (show E from e (J' 0)) u) =
        coframeS (I := I) (M := M) g x (r + 1) e K' (Fin.cons (show E from e (J' 0)) u) := rfl
    rw [hcf, coframeS_apply (I := I) (M := M) g x (r + 1) e K' (Fin.cons (show E from e (J' 0)) u)]
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [horth (K' 0) (J' 0)]
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hcf2 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x r e
          (fun k => K' (Fin.succ k))) u =
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u := rfl
    rw [hcf2, coframeS_apply (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u]
    by_cases h : K' 0 = J' 0
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [hcurry, map_smul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  -- The remaining factor is the `(K' ∘ succ, J' ∘ succ)` component of `A`.
  congr 1

/-- **The passenger-slot scaling of the fibre norm (fibre level).**  Inserting one leading covariant
passenger slot scales the intrinsic fibre norm by the dimension factor `n = Module.finrank ℝ E`:
```
rfns(slotExtendFib g r s x A) = n · rfns(A).
```
Parseval-expand both fibre norms in any `g_x`-orthonormal frame `e`; the slot-extended component factors
as `[K' 0 = J' 0] · A_{K' ∘ succ, J' ∘ succ}` (`fiberNormSqComponent_slotExtendFib_eq`), so squaring and
summing collapses the Kronecker delta (`∑_{K' 0} [K' 0 = J' 0] = 1` against the leading `J'`-index, and
the residual leading `J'`-index ranges over `n` values, contributing the factor `n`). -/
private lemma rfns_slotExtendFib_eq_frame
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A) =
      (n : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r s x (show TensorRSSpace r s I x from A) := by
  classical
  -- Parseval-expand both fibre norms in the SAME frame `e`.
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g (r + 1) (s + 1) x
    (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
    e bse hn hbse horth]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x
    (show TensorRSSpace r s I x from A) e bse hn hbse horth]
  -- Rewrite each slot-extended component by the Kronecker factorisation.
  have hcompsq : ∀ (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1) → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
          (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
          n e K' J') ^ 2 =
        (if J' 0 = K' 0 then (1 : ℝ) else 0) *
          (fiberNormSqComponent (I := I) (M := M) g x r s (show TensorRSSpace r s I x from A) n e
            (fun k => K' (Fin.succ k)) (fun k => J' (Fin.succ k))) ^ 2 := by
    intro K' J'
    rw [fiberNormSqComponent_slotExtendFib_eq (I := I) (M := M) g r s x A e horth K' J']
    by_cases h : J' 0 = K' 0
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun K' _ => Finset.sum_congr rfl (fun J' _ => hcompsq K' J'))]
  set comp : (Fin r → Fin n) → (Fin s → Fin n) → ℝ := fun K J =>
    (fiberNormSqComponent (I := I) (M := M) g x r s (show TensorRSSpace r s I x from A) n e K J) ^ 2
    with hcomp_def
  -- Reindex `K' = cons k0 K` over the outer sum.
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
        (fun pr : Fin n × (Fin r → Fin n) =>
          ∑ J' : Fin (s + 1) → Fin n,
            (if J' 0 = pr.1 then (1 : ℝ) else 0) * comp pr.2 (fun k => J' (Fin.succ k)))
        (fun K' : Fin (r + 1) → Fin n =>
          ∑ J' : Fin (s + 1) → Fin n,
            (if J' 0 = K' 0 then (1 : ℝ) else 0) * comp (fun k => K' (Fin.succ k))
              (fun k => J' (Fin.succ k)))
        (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  -- For each `k0`, reindex `J' = cons j0 J` over the inner sum and collapse the delta.
  rw [show (∑ k0 : Fin n, ∑ K : Fin r → Fin n, ∑ J' : Fin (s + 1) → Fin n,
        (if J' 0 = k0 then (1 : ℝ) else 0) * comp K (fun k => J' (Fin.succ k))) =
      ∑ k0 : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, comp K J from by
    refine Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun K _ => ?_))
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun pr : Fin n × (Fin s → Fin n) =>
            (if pr.1 = k0 then (1 : ℝ) else 0) * comp K pr.2)
          (fun J' : Fin (s + 1) → Fin n =>
            (if J' 0 = k0 then (1 : ℝ) else 0) * comp K (fun k => J' (Fin.succ k)))
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    rw [show (∑ j0 : Fin n, ∑ J : Fin s → Fin n, (if j0 = k0 then (1 : ℝ) else 0) * comp K J) =
        ∑ J : Fin s → Fin n, comp K J from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ k0 (fun _ => (1 : ℝ)),
        if_pos (Finset.mem_univ k0), one_mul]]]
  -- `∑_{k0} = n`.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The passenger-slot scaling of the fibre norm (fibre level).**  Inserting one leading covariant
passenger slot scales the intrinsic fibre norm by the dimension factor `n = Module.finrank ℝ E`:
```
rfns(slotExtendFib g r s x A) = n · rfns(A).
```
Parseval-expand both fibre norms in any `g_x`-orthonormal frame `e`; the slot-extended component factors
as `[K' 0 = J' 0] · A_{K' ∘ succ, J' ∘ succ}` (`fiberNormSqComponent_slotExtendFib_eq`), so squaring and
summing collapses the Kronecker delta (`∑_{K' 0} [K' 0 = J' 0] = 1` against the leading `J'`-index, and
the residual leading `J'`-index ranges over `n` values, contributing the factor `n`). -/
theorem rfns_slotExtendFib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r s x (show TensorRSSpace r s I x from A) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  exact rfns_slotExtendFib_eq_frame (I := I) (M := M) g r s x A e bse rfl hbse horth

/-- **The passenger-slot scaling of the fibre norm of the slot-extended section.**  At every base point
`x`, the intrinsic fibre norm of the slot-extension `slotExtend g r s Φ` of an operator field `Φ` is
`n = Module.finrank ℝ E` times the fibre norm of `Φ`:
```
rfns(slotExtend g r s Φ)(x) = n · rfns(Φ)(x).
```
The section value of `slotExtend Φ` at `x` is `slotExtendFib g r s x (Φ x)` (`slotExtend_toSection`), so
this is the section-level reading of `rfns_slotExtendFib_eq`. -/
theorem rfns_slotExtend_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
        ((slotExtend (I := I) (M := M) g r s Φ).toSection x) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) := by
  rw [slotExtend_toSection (I := I) (M := M) g r s Φ x]
  exact rfns_slotExtendFib_eq (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)

/-! ## The gradient/slot-extension fibre-norm commutation

The covariant gradient does NOT commute with the leading-passenger-slot extension on the nose: both
`covGrad (slotExtend Φ)` and `slotExtend (covGrad Φ)` are `(r + 1, s + 2)`-tensor fields, but they read
the new gradient slot and the new passenger slot in the OPPOSITE order — they differ by a transposition
of the two leading covariant (output) slots.  The intrinsic fibre norm is invariant under any
permutation of the covariant slots, so they have the SAME fibre norm; combined with the passenger-slot
scaling, `rfns(covGrad (slotExtend Φ)) = n · rfns(covGrad Φ)`. -/

/-- **The leading-output-slot frame component of `covGrad (slotExtend Φ)` is the slot-`0,1`-swapped
component of `slotExtend (covGrad Φ)`.**  For a `g_x`-orthonormal frame `e`, the `(K', J')`-frame
component of `covGrad (slotExtend Φ)` at `x` equals the `(K', J' ∘ swap 0 1)`-frame component of
`slotExtend (covGrad Φ)`: both read the same underlying directional data, with the gradient and
passenger output slots transposed (`covGrad_toSection_apply_eval`, `slotExtendFib_apply_eval`,
`tensorCovDerivAt_slotExtend_eq`). -/
private lemma fiberNormSqComponent_covGrad_slotExtend_eq_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (Φ : SmoothCcTensor g r s)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1 + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) n e K' J' =
      fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) n e K'
          (J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  -- Both components are `toModel (... ω^{K'}) (e ∘ J')`; expand each side via the slot evals.
  have hLHS : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) n e K' J' =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x (e (J' 0)))
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
            (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1))))
        (fun k : Fin s => (show E from e (J' (Fin.succ (Fin.succ k))))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
          ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)).toSection x) n e K' J' =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            (covGrad (I := I) (M := M) g (r + 1) (s + 1)
              (slotExtend (I := I) (M := M) g r s Φ)).toSection x)
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => (show E from e (J' k))) from rfl]
    rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ) x (coframeS (I := I) (M := M) g x (r + 1) e K')
      (fun k => (show E from e (J' k)))]
    rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensorCovDerivAt_slotExtend_eq
      (I := I) (M := M) g r s Φ x ((fun k => (show E from e (J' k))) 0)]
    rw [show Matrix.vecTail (fun k => (show E from e (J' k))) =
        Fin.cons (show E from e (J' 1)) (fun k : Fin s => (show E from e (J' (Fin.succ (Fin.succ k)))))
        from by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · change (show E from e (J' (Fin.succ 0))) = _
        rw [Fin.cons_zero]; rfl
      · change (show E from e (J' (Fin.succ (Fin.succ i)))) = _
        rw [Fin.cons_succ]]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g r s Φ x ((fun k => (show E from e (J' k))) 0))
      (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1))
      (fun k : Fin s => (show E from e (J' (Fin.succ (Fin.succ k)))))]
  have hRHS : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) n e K'
          (J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x (e (J' 0)))
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
            (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1))))
        (fun k : Fin s => (show E from e (J' (Fin.succ (Fin.succ k))))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
          ((slotExtend (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ)).toSection x) n e K'
            (J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            (slotExtend (I := I) (M := M) g r (s + 1)
              (covGrad (I := I) (M := M) g r s Φ)).toSection x)
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) k))) from rfl]
    rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
    rw [show (fun k => (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) k))) =
        Fin.cons (show E from e (J' 1))
          (fun k : Fin (s + 1) => (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Fin.succ k)))) from by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero, Function.comp_apply]
        rw [Equiv.swap_apply_left]
      · rw [Fin.cons_succ]]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g r s Φ).toSection x)
      (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1))
      (fun k : Fin (s + 1) => (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k))))]
    rw [show ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
          (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1)) :
          Tensor0SSpace r I x) =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
          (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1)) from rfl]
    rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
        (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 1)))
      (fun k : Fin (s + 1) => (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k))))]
    -- Simplify the swap on the read-off direction and the tail tuple.
    have hdir : (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ 0))) =
        (show E from e (J' 0)) := by
      change e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ 0)) = e (J' 0)
      simp only [Function.comp_apply]
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
    have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
          (show E from e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k))))) =
        (fun k : Fin s => (show E from e (J' (Fin.succ (Fin.succ k))))) := by
      funext k
      change e ((J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
        e (J' (Fin.succ (Fin.succ k)))
      simp only [Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · exact (Fin.succ_ne_zero _)
      · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    rw [hdir, htail]
  rw [hLHS, hRHS]

/-- **The covariant gradient and the leading-passenger-slot extension commute up to fibre norm.**  At
every base point `x`, `covGrad (slotExtend Φ)` and `slotExtend (covGrad Φ)` — which differ by a
transposition of the two leading covariant output slots — have equal intrinsic fibre norm:
```
rfns(covGrad (slotExtend g r s Φ))(x) = rfns(slotExtend g r (s + 1) (covGrad g r s Φ))(x).
```
Parseval-expand both in a `g_x`-orthonormal frame; each component of the left side is the slot-`0,1`-
swapped component of the right (`fiberNormSqComponent_covGrad_slotExtend_eq_swap`), and the swap is a
bijective reindexing of the `J'`-sum, hence leaves the component-square sum unchanged. -/
theorem rfns_covGrad_slotExtend_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1 + 1) x
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g (r + 1) (s + 1 + 1) x _ e bse rfl
    hbse horth]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g (r + 1) (s + 1 + 1) x _ e bse rfl
    hbse horth]
  refine Finset.sum_congr rfl (fun K' _ => ?_)
  -- Reindex the inner `J'`-sum by precomposition with the swap, then rewrite each component.
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.refl (Fin (Module.finrank ℝ E))))
    (fun J' : Fin (s + 1 + 1) → Fin (Module.finrank ℝ E) =>
      (fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) (Module.finrank ℝ E) e K' J') ^ 2)
    (fun J' : Fin (s + 1 + 1) → Fin (Module.finrank ℝ E) =>
      (fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1 + 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) (Module.finrank ℝ E) e K' J') ^ 2)
    (fun J' => ?_)
  simp only []
  have heqv : (Equiv.arrowCongr (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (Equiv.refl (Fin (Module.finrank ℝ E)))) J' =
      J' ∘ Equiv.swap (0 : Fin (s + 1 + 1)) 1 := by
    funext a; simp [Equiv.arrowCongr]
  rw [heqv]
  rw [fiberNormSqComponent_covGrad_slotExtend_eq_swap (I := I) (M := M) g r s x Φ e K' J']

/-- **The covariant gradient of a slot-extension scales the fibre norm by `n` over the gradient.**  At
every base point `x`,
```
rfns(covGrad (slotExtend g r s Φ))(x) = n · rfns(covGrad g r s Φ)(x),   n = Module.finrank ℝ E.
```
Compose `rfns_covGrad_slotExtend_eq` (the fibre norm is insensitive to the slot transposition between
`covGrad (slotExtend Φ)` and `slotExtend (covGrad Φ)`) with the passenger-slot scaling
`rfns_slotExtend_eq` applied to `covGrad Φ`. -/
theorem rfns_covGrad_slotExtend_scale (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s Φ).toSection x) := by
  rw [rfns_covGrad_slotExtend_eq (I := I) (M := M) g r s Φ x]
  exact rfns_slotExtend_eq (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x

/-- **The `w`-fold passenger-slot extension scales the fibre norm by `n^w`.**  At every base point `x`,
```
rfns(slotExtendIter g r s w Φ)(x) = n^w · rfns(Φ)(x),   n = Module.finrank ℝ E.
```
Induction on `w`, each step applying the single passenger-slot scaling `rfns_slotExtend_eq`. -/
theorem rfns_slotExtendIter_eq (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ (w : ℕ) (Φ : SmoothCcTensor g r s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g (r + w) (s + w) x
          ((slotExtendIter (I := I) (M := M) g r s w Φ).toSection x) =
        (Module.finrank ℝ E : ℝ) ^ w *
          riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) := by
  intro w
  induction w with
  | zero => intro Φ x; simp [slotExtendIter]
  | succ w ih =>
      intro Φ x
      -- `slotExtendIter (w + 1) Φ = slotExtend (slotExtendIter w Φ)`.
      have hrec : slotExtendIter (I := I) (M := M) g r s (w + 1) Φ =
          slotExtend (I := I) (M := M) g (r + w) (s + w)
            (slotExtendIter (I := I) (M := M) g r s w Φ) := rfl
      change riemannianFiberNormSq (I := I) (M := M) g ((r + w) + 1) ((s + w) + 1) x
          ((slotExtendIter (I := I) (M := M) g r s (w + 1) Φ).toSection x) = _
      rw [hrec, rfns_slotExtend_eq (I := I) (M := M) g (r + w) (s + w)
        (slotExtendIter (I := I) (M := M) g r s w Φ) x, ih Φ x]
      rw [pow_succ]
      ring

/-! ## General-valence covariant-slot permutation invariance of the fibre norm

The intrinsic fibre norm of an `(r, s)`-tensor is invariant under any permutation of its `s` covariant
output slots.  This is the general-valence `(r, s)` lift of the rank-`0` slot-permutation invariance
`riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr`; here the contravariant rank `r` is
arbitrary (untouched by the output-slot permutation), which is exactly what the iterated
slot-extension fibre-norm scaling needs when it must commute an inner covariant gradient past the
slot-extension's covariant-output-slot transposition at positive contravariant rank. -/

/-- **The covariant-slot permutation of an `(r, s)`-tensor fibre.**  Post-compose the output
`(0, s)`-fibre `Tensor0SSpace s I x` of the `(r, s)`-tensor `T` (a continuous linear map from
`(0, r)`-fibres) with the isometric slot reindexing `domDomCongr σ`.  The result is the `(r, s)`-tensor
whose `(K, J)`-frame component is the `(K, J ∘ σ)`-component of `T`. -/
def rsDomDomCongr {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) : TensorRSSpace r s I x :=
  TensorRSSpace.ofCLM
    ((((tensor0SSpace_continuousLinearEquiv s x).symm.toContinuousLinearMap).comp
        (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ).toContinuousLinearEquiv
            : Tensor0SModel s ℝ E ≃L[ℝ] Tensor0SModel s ℝ E).toContinuousLinearMap.comp
          ((tensor0SSpace_continuousLinearEquiv s x).toContinuousLinearMap))).comp
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T))

/-- **The model form of `rsDomDomCongr σ T` on a `(0, r)`-tensor `d` is the slot-reindexing of the
model form of `T d`.** -/
lemma toModel_rsDomDomCongr_apply {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) (d : Tensor0SSpace r I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from rsDomDomCongr σ T) d) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)) := by
  rw [rsDomDomCongr, TensorRSSpace.ofCLM]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [Tensor0SSpace.toModel]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

/-- **Evaluation of the slot-permuted tensor.**  On a `(0, r)`-tensor `d` and a tangent tuple `v`,
`rsDomDomCongr σ T` reads `T d` on the slot-reindexed tuple `v ∘ σ`. -/
lemma rsDomDomCongr_apply_eval {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) (d : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from rsDomDomCongr σ T) d v =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d (fun k => v (σ k)) := by
  classical
  have hL := toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      (y : Tensor0SSpace s I x) w = Tensor0SSpace.toModel y w := fun y w => rfl
  rw [hfib, hL, ContinuousMultilinearMap.domDomCongr_apply, ← hfib]

/-- **Composition of two covariant-slot permutations.**  `rsDomDomCongr σ (rsDomDomCongr τ T) =
rsDomDomCongr (τ.trans σ) T`. -/
lemma rsDomDomCongr_rsDomDomCongr {r s : ℕ} {x : M} (σ τ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) :
    rsDomDomCongr (I := I) (M := M) σ (rsDomDomCongr (I := I) (M := M) τ T) =
      rsDomDomCongr (I := I) (M := M) (τ.trans σ) T := by
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace s I x) w := fun y w => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (rsDomDomCongr (I := I) (M := M) τ T) d v,
    rsDomDomCongr_apply_eval (I := I) (M := M) τ T d (fun k => v (σ k)),
    rsDomDomCongr_apply_eval (I := I) (M := M) (τ.trans σ) T d v]
  rfl

/-- **The frame component of a slot-permuted tensor reindexes the output multi-index.**  For a
`g_x`-orthonormal frame `e`, the `(K, J)`-frame component of `rsDomDomCongr σ T` is the
`(K, J ∘ σ)`-frame component of `T` (the slot reindexing acts on the output-slot reading). -/
lemma fiberNormSqComponent_rsDomDomCongr {r s : ℕ} (g : SmoothRiemannianMetric I M) (x : M)
    (σ : Equiv.Perm (Fin s)) (T : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s (rsDomDomCongr σ T) n e K J =
      fiberNormSqComponent (I := I) (M := M) g x r s T n e K (fun k => J (σ k)) := by
  rw [fiberNormSqComponent, fiberNormSqComponent]
  exact rsDomDomCongr_apply_eval (I := I) (M := M) σ T _ (fun k => e (J k))

/-- **General-valence covariant-slot permutation invariance of the intrinsic fibre norm.**  For any
permutation `σ : Equiv.Perm (Fin s)` of the `s` covariant output slots and any `(r, s)`-tensor `T`,
```
rfns(rsDomDomCongr σ T)(x) = rfns(T)(x).
```
Parseval-expand both fibre norms in a `g_x`-orthonormal frame (`rfns_rs_eq_sum_componentSq_of_basis`);
the `(K, J)`-component of `rsDomDomCongr σ T` is the `(K, J ∘ σ)`-component of `T`
(`fiberNormSqComponent_rsDomDomCongr`), and `J ↦ J ∘ σ` is a bijective reindexing of the inner
`J`-sum, hence leaves the component-square sum unchanged.  The contravariant index `K` is untouched. -/
theorem riemannianFiberNormSq_domDomCongr_covariant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (σ : Equiv.Perm (Fin s)) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (rsDomDomCongr σ T) =
      riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x (rsDomDomCongr σ T)
    e bse rfl hbse horth]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x T e bse rfl hbse horth]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  refine Fintype.sum_equiv
    (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ E))))
    (fun J => (fiberNormSqComponent (I := I) (M := M) g x r s (rsDomDomCongr σ T)
      (Module.finrank ℝ E) e K J) ^ 2)
    (fun J => (fiberNormSqComponent (I := I) (M := M) g x r s T
      (Module.finrank ℝ E) e K J) ^ 2)
    (fun J => ?_)
  simp only []
  have heqv : (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ E)))) J =
      (fun k => J (σ k)) := by
    funext a; simp [Equiv.arrowCongr]
  rw [heqv]
  rw [fiberNormSqComponent_rsDomDomCongr (I := I) (M := M) g x σ T e K J]

/-! ## Cast / commute bookkeeping for the diagonal product grid (generic contravariant rank) -/

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast (heterogeneous form, generic
contravariant rank `r`).** -/
private theorem rfns_toSection_heq_congr_rs (g : SmoothRiemannianMetric I M)
    {r a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

set_option linter.unusedSectionVars false in
/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form, generic
contravariant rank `r`).**  `rfns(∇^m(∇Φ))` at valence `(r, (s + 1) + m)` equals `rfns(∇^{m+1}Φ)` at
valence `(r, s + (m + 1))`; the generic-rank instance of `rfns_iteratedCovGrad_covGrad_comm`. -/
theorem rfns_iteratedCovGrad_covGrad_comm_rs (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad (I := I) (M := M) g r s Φ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) Φ).toSection x) :=
  rfns_toSection_heq_congr_rs g (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g r s m Φ) x

/-! ## The iterated slot-extension fibre-norm bound

Iterating the single-step gradient/slot-extension fibre-norm scaling `rfns_covGrad_slotExtend_scale`
over the gradient order, the covariant slot permutation invariance `riemannianFiberNormSq_domDomCongr_covariant`
absorbs the order-dependent transposition of the passenger slot through the accumulated gradient slots
(needed because the contravariant rank `r + 1 > 0` makes the rank-`0` naturality inapplicable). -/

/-- **Covariant gradient commutes with the leading-passenger-slot extension up to a leading-slot
transposition (section level).**  At every base point `x`, the section value of `covGrad (slotExtend
g r s Φ)` is the slot-`0,1`-transposition (`rsDomDomCongr (Equiv.swap 0 1)`) of the section value of
`slotExtend g r (s + 1) (covGrad g r s Φ)`:
```
(covGrad (slotExtend Φ)).toSection x = rsDomDomCongr (swap 0 1) ((slotExtend (covGrad Φ)).toSection x).
```
Both sides are `(r + 1, (s + 1) + 1)`-tensors reading the gradient slot and the new passenger slot in
the opposite order; the section identity is the `toModel`-level reading of `covGrad_toSection_apply_eval`,
`tensorCovDerivAt_slotExtend_eq` and `slotExtendFib_apply_eval`. -/
private lemma covGrad_slotExtend_toSection_rsDomDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      rsDomDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  -- RHS: the slot-reindexing reads `m ∘ swap` (coe-application form).
  conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m]
  conv_rhs => rw [← hfib]
  -- LHS: read the leading (gradient) slot via `covGrad_toSection_apply_eval`.
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x (m 0)]
  -- The slot-extended fibre operator reads the new passenger slot first.
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x (m 0))
    d (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k)))]
  -- RHS continued: `slotExtend (covGrad Φ)` reads the passenger slot first, then `covGrad`.
  rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
  rw [show (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))
      from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero]
      rw [Equiv.swap_apply_left]
    · rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
    (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  -- The read-off direction and the tail tuple after the swap.
  have hdir : m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1)))) = m 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
      (fun k : Fin s => m (Fin.succ (Fin.succ k))) := by
    funext k
    change m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
      m (Fin.succ (Fin.succ k))
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.succ_ne_zero _)
    · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
      exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  rw [hdir, htail]

/-- **The covariant gradient commutes with the covariant-rank cast `castRankCc_db`.** -/
private lemma covGrad_castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r b
        (DifferentialGeometry.Integral.Connection.castRankCc_db g r h W) =
      DifferentialGeometry.Integral.Connection.castRankCc_db g r (by rw [h] : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g r a W) := by
  subst h; rfl

/-- **A leading-slot transposition is heterogeneously equal across a covariant-rank cast.** -/
private lemma heq_swap_zero_one_of_eq {p q : ℕ} (h : p = q) :
    HEq (Equiv.swap (0 : Fin (p + 1)) 1) (Equiv.swap (0 : Fin (q + 1)) 1) := by
  subst h; rfl

/-- **Succ-step cast/transposition bookkeeping.**  Given two `(r + 1, a)`-tensors `P, Q` related at
the section level by the leading-slot transposition `rsDomDomCongr swapA` (helper 1), casting both up
along `h : a = b` and reindexing by `σ̂` on the cast valence composes the transposition into
`swapB.trans σ̂`.  Proven by `subst h` (collapsing the cast and identifying `swapA = swapB`), then the
permutation composition `rsDomDomCongr_rsDomDomCongr`. -/
private lemma succ_step_cast_transposition_eq {r a b : ℕ} (h : a = b)
    (g : SmoothRiemannianMetric I M)
    (P Q : SmoothCcTensor g (r + 1) a) (x : M)
    (sigmaHat swapB : Equiv.Perm (Fin b)) (swapA : Equiv.Perm (Fin a)) (hswap : HEq swapA swapB)
    (hPQ : P.toSection x = rsDomDomCongr (I := I) (M := M) swapA (Q.toSection x)) :
    rsDomDomCongr (I := I) (M := M) sigmaHat
        ((DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1) h P).toSection x) =
      rsDomDomCongr (I := I) (M := M) (swapB.trans sigmaHat)
        ((DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1) h Q).toSection x) := by
  subst h
  rw [eq_of_heq hswap] at hPQ
  simp only [DifferentialGeometry.Integral.Connection.castRankCc_db]
  rw [hPQ, rsDomDomCongr_rsDomDomCongr]

/-- **The structural slot-extension naturality invariant for the iterated covariant gradient.**  At
every gradient order `i`, the iterated covariant gradient `∇^i (slotExtend Φ)` is a covariant-output-
slot reindexing of (the covariant-rank cast of) `slotExtend (∇^i Φ)`:
```
∃ σ, (∇^i (slotExtend g r s Φ)).toSection x =
  rsDomDomCongr σ ((castRankCc_db g (r+1) h (slotExtend g r (s+i) (∇^i Φ))).toSection x).
```
Induction on `i`: order `0` is the identity; the step pushes one covariant gradient through the inner
reindexing by the general-rank `covGrad`-naturality `covGrad_rs_toModel_domDomCongr` (the positive
contravariant rank `r + 1` makes the rank-`0` naturality inapplicable), then absorbs the leading
gradient/passenger transposition of `covGrad (slotExtend (∇^i Φ))` via
`covGrad_slotExtend_toSection_rsDomDomCongr`. -/
private lemma exists_iteratedCovGrad_slotExtend_rsDomDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + 1) + i)),
      ∀ x : M,
        (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
          rsDomDomCongr (I := I) (M := M) σ
            ((DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1)
              (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g r (s + i)
                (iteratedCovGrad (I := I) g r s i Φ))).toSection x) := by
  classical
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, fun x => ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      apply ContinuousLinearMap.ext
      intro d
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro m
      have hfib : ∀ (y : Tensor0SSpace ((s + 1) + 0) I x)
          (w : Fin ((s + 1) + 0) → TangentSpace I x),
          Tensor0SSpace.toModel y w = (y : Tensor0SSpace ((s + 1) + 0) I x) w := fun _ _ => rfl
      conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
        (Equiv.refl (Fin ((s + 1) + 0)))
        ((DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1)
          (by omega : (s + 0) + 1 = (s + 1) + 0)
          (slotExtend (I := I) (M := M) g r (s + 0) Φ)).toSection x) d m]
      simp only [Equiv.refl_apply]
      -- `castRankCc_db` with `s + 0 + 1 = s + 1 + 0` is a transport over a defeq cast; both `Fin`
      -- cardinalities reduce to `s + 1`.
      rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      -- The new permutation: shift `σ` past the new leading gradient slot, then absorb the
      -- gradient/passenger transposition.
      refine ⟨(Equiv.swap (0 : Fin (((s + 1) + i) + 1)) 1).trans
        (Equiv.Perm.decomposeFin.symm (0, σ)), fun x => ?_⟩
      -- `∇^{i+1}(slotExtend Φ) = covGrad (∇^i(slotExtend Φ))`.
      rw [iteratedCovGrad_succ (I := I) g (r + 1) (s + 1) i (slotExtend (I := I) (M := M) g r s Φ)]
      -- Push `covGrad` through the IH reindexing by the general-rank naturality.
      have hcov : (covGrad (I := I) (M := M) g (r + 1) ((s + 1) + i)
            (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
              (slotExtend (I := I) (M := M) g r s Φ))).toSection x =
          rsDomDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
            ((covGrad (I := I) (M := M) g (r + 1) ((s + 1) + i)
              (DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1)
                (by omega : (s + i) + 1 = (s + 1) + i)
                (slotExtend (I := I) (M := M) g r (s + i)
                  (iteratedCovGrad (I := I) g r s i Φ)))).toSection x) := by
        apply ContinuousLinearMap.ext
        intro d
        apply Tensor0SSpace.toModel_injective
        apply ContinuousMultilinearMap.ext
        intro v
        rw [covGrad_rs_toModel_domDomCongr (I := I) (M := M) g (r + 1) ((s + 1) + i) σ
          (DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1)
            (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ)))
          (iteratedCovGrad (I := I) g (r + 1) (s + 1) i (slotExtend (I := I) (M := M) g r s Φ))
          (fun y d' => by
            have := hσ y
            rw [this]
            exact toModel_rsDomDomCongr_apply (I := I) (M := M) σ _ d') x d v]
        rw [ContinuousMultilinearMap.domDomCongr_apply]
        have hfib : ∀ (y : Tensor0SSpace (((s + 1) + i) + 1) I x)
            (w : Fin (((s + 1) + i) + 1) → TangentSpace I x),
            Tensor0SSpace.toModel y w = (y : Tensor0SSpace (((s + 1) + i) + 1) I x) w := fun _ _ => rfl
        conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
          (Equiv.Perm.decomposeFin.symm (0, σ))
          ((covGrad (I := I) (M := M) g (r + 1) ((s + 1) + i)
            (DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1)
              (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g r (s + i)
                (iteratedCovGrad (I := I) g r s i Φ)))).toSection x) d v]
        rfl
      rw [hcov]
      -- The inner `covGrad (castRankCc_db ... (slotExtend (∇^iΦ)))`: commute the cast, then absorb
      -- the gradient/passenger transposition.
      rw [covGrad_castRankCc_db (I := I) (M := M) g (r + 1)
        (by omega : (s + i) + 1 = (s + 1) + i)
        (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ))]
      -- `iteratedCovGrad_succ` on the inner `∇^{i+1}Φ` and `slotExtend`'s gradient commutation.
      rw [iteratedCovGrad_succ (I := I) g r s i Φ]
      exact succ_step_cast_transposition_eq (I := I) (M := M)
        (by omega : (s + i) + 1 + 1 = (s + 1) + i + 1) g
        (covGrad (I := I) (M := M) g (r + 1) (s + i + 1)
          (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ)))
        (slotExtend (I := I) (M := M) g r (s + (i + 1))
          (covGrad (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ)))
        x (Equiv.Perm.decomposeFin.symm (0, σ))
        (Equiv.swap (0 : Fin (((s + 1) + i) + 1)) 1)
        (Equiv.swap (0 : Fin (((s + i) + 1) + 1)) 1)
        (heq_swap_zero_one_of_eq (by omega : (s + i) + 1 = (s + 1) + i))
        (covGrad_slotExtend_toSection_rsDomDomCongr (I := I) (M := M) g r (s + i)
          (iteratedCovGrad (I := I) g r s i Φ) x)

/-- **The iterated slot-extension fibre-norm bound.**  At every base point `x` and gradient order `i`,
inserting one leading covariant passenger slot scales the iterated covariant-gradient fibre norm by at
most the dimension factor `n = Module.finrank ℝ E`:
```
rfns(∇^i (slotExtend g r s Φ))(x) ≤ n · rfns(∇^i Φ)(x).
```
The single-step `i = 0`/`i = 1` instances are `rfns_slotExtend_eq` / `rfns_covGrad_slotExtend_scale`;
the iterate commutes the inner covariant gradient `∇^i` past the slot-extension's covariant-output-slot
transposition, whose fibre norm is invariant by `riemannianFiberNormSq_domDomCongr_covariant` (the
general-valence slot-permutation invariance, applicable at the positive contravariant rank `r + 1`),
then applies the passenger scaling `rfns_slotExtend_eq` to `∇^i Φ`.

This is the section-level slot-extension jet scaling consumed by the `appCc` diagonal product grid; it
is the general-valence analogue of the rank-`0` slot-permutation jet invariance
`riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr`, lifted to positive contravariant
rank through `riemannianFiberNormSq_domDomCongr_covariant` and the general-rank covariant-gradient
slot-permutation naturality `covGrad_rs_toModel_domDomCongr`. -/
theorem rfns_iteratedCovGrad_slotExtend_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  obtain ⟨σ, hσ⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M) g r s Φ i
  -- The structural invariant: `∇^i(slotExtend Φ)` is the `σ`-reindexing of the cast `slotExtend(∇^iΦ)`.
  rw [hσ x]
  -- The slot reindexing preserves the fibre norm.
  rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g (r + 1) ((s + 1) + i) x σ
    ((DifferentialGeometry.Integral.Connection.castRankCc_db g (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g r (s + i)
        (iteratedCovGrad (I := I) g r s i Φ))).toSection x)]
  -- The cast preserves the fibre norm (heterogeneous-section congruence); `rfns_slotExtend_eq`
  -- scales it by `n`.
  rw [← rfns_toSection_heq_congr_rs g (by omega : (s + i) + 1 = (s + 1) + i)
    (DifferentialGeometry.Integral.Connection.castRankCc_db_heq g (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ))).symm x]
  rw [rfns_slotExtend_eq (I := I) (M := M) g r (s + i) (iteratedCovGrad (I := I) g r s i Φ) x]

/-! ## The `appCc` diagonal product grid

The covariant Leibniz diagonal product grid for the operator-field action: the iterated covariant
gradient `∇^j (appCc C W)` of the contracted action of a coefficient field `C` on a section `W` is
bounded, fibrewise, by the diagonal product of the `C`-jets and the `W`-jets,
```
rfns(∇^j (appCc C W))(x) ≤ Gdiag j · ∑_{i ≤ j} rfns(∇^i C)(x) · ∑_{l ≤ j − i} rfns(∇^l W)(x),
```
with `Gdiag j = (2 (n + 1))^j`, `n = Module.finrank ℝ E`.  This is the chart-jet-free Moser-tame grid
fed to the integrated Gagliardo–Nirenberg two-arm engine. -/

/-- **The per-order diagonal product-grid constant `Gdiag j = (2 (n + 1))^j`.** -/
def appCcGdiag (j : ℕ) : ℝ := (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ j

set_option linter.unusedSectionVars false in
/-- `appCcGdiag` is nonnegative. -/
theorem appCcGdiag_nonneg (j : ℕ) : 0 ≤ appCcGdiag (E := E) j := by
  rw [appCcGdiag]; positivity

/-- **The pure combinatorial diagonal-grid step inequality.**  For nonnegative jet-coefficient
families `cΦ, cW : ℕ → ℝ` and dimension factor `n ≥ 0`, the gradient-step combination of the
`Φ`-shifted and `W`-shifted diagonal grids is dominated by `(n + 1)` times the order-`(j + 1)`
diagonal grid:
```
∑_{i≤j} cΦ(i+1)·(∑_{l≤j-i} cW l) + n · ∑_{i≤j} cΦ(i)·(∑_{l≤j-i} cW(l+1))
  ≤ (n + 1) · ∑_{i≤j+1} cΦ(i)·(∑_{l≤j+1-i} cW l).
``` -/
private lemma diagonalGrid_step_le (n : ℝ) (hn : 0 ≤ n) (j : ℕ) (cΦ cW : ℕ → ℝ)
    (hcΦ : ∀ i, 0 ≤ cΦ i) (hcW : ∀ l, 0 ≤ cW l) :
    (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
        n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) ≤
      (n + 1) * ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
  classical
  set D : ℝ := ∑ i ∈ Finset.range (j + 1 + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l
    with hD_def
  have hcell_nn : ∀ i, 0 ≤ cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
    intro i; exact mul_nonneg (hcΦ i) (Finset.sum_nonneg (fun l _ => hcW l))
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun i _ => hcell_nn i)
  -- A shift bound: `∑_{l<m} cW(l+1) ≤ ∑_{l<m+1} cW l`.
  have hWshift : ∀ m : ℕ, (∑ l ∈ Finset.range m, cW (l + 1)) ≤ ∑ l ∈ Finset.range (m + 1), cW l := by
    intro m
    rw [Finset.sum_range_succ' (fun l => cW l) m]
    exact le_add_of_nonneg_right (hcW 0)
  -- First sum: reindex `i ↦ i + 1`, each term ≤ the `(i+1)`-cell of `D`.
  have hA : (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ' (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn 0))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hcΦ (i + 1))
    rw [show j + 1 + 1 - (i + 1) = j + 1 - i from by omega]
  -- Second sum: each `W`-shifted inner sum ≤ the full inner sum of the `i`-cell of `D`.
  have hB : (∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn (j + 1)))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left ?_ (hcΦ i)
    refine le_trans (hWshift (j + 1 - i)) (le_of_eq ?_)
    rw [show j + 1 - i + 1 = j + 1 + 1 - i from by omega]
  calc (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
          n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
      ≤ D + n * D := by
        refine add_le_add hA ?_
        exact mul_le_mul_of_nonneg_left hB hn
    _ = (n + 1) * D := by ring

set_option maxHeartbeats 6400000 in
/-- **The generic-rank diagonal product grid for the operator-field action `appCcRS`.**  For an
operator field `Φ : SmoothCcTensor g a b` and a contracted section `W : SmoothCcTensor g 0 a`, the
iterated covariant gradient of `appCcRS g 0 a b Φ W` is bounded fibrewise by the diagonal product of the
`Φ`-jets (at contravariant valence `a`) and the `W`-jets:
```
rfns(∇^j (appCcRS Φ W))(x) ≤ Gdiag j · ∑_{i ≤ j} rfns(∇^i Φ)(x) · ∑_{l ≤ j − i} rfns(∇^l W)(x).
```
Induction on `j`: the single-step operator-field covariant product rule `covGrad_appCcRS_eq` splits the
gradient into the `Φ`-differentiated arm `appCcRS (∇Φ) W` and the `slotExtend`-passenger arm
`appCcRS (slotExtend Φ) (∇W)`; `riemannianFiberNormSq_add_le` separates them, the inductive hypothesis
(at `(a, b + 1)` and `(a + 1, b + 1)`) bounds each, the front-commute `rfns_iteratedCovGrad_covGrad_comm_rs`
reindexes the differentiated jets, and the slot-extension scaling `rfns_iteratedCovGrad_slotExtend_le`
collapses the passenger arm's `Φ`-jets back to the `∇^i Φ` jets with the dimension factor `n`. -/
theorem rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le (g : SmoothRiemannianMetric I M) :
    ∀ (j a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g 0 a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (b + j) x
          ((iteratedCovGrad (I := I) g 0 b j
            (appCcRS (I := I) (M := M) g 0 a b Φ W)).toSection x) ≤
        appCcGdiag (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
                ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g 0 (a + l) x
                  ((iteratedCovGrad (I := I) g 0 a l W).toSection x) := by
  intro j
  induction j with
  | zero =>
      intro a b Φ W x
      rw [iteratedCovGrad_zero, appCcGdiag, pow_zero, one_mul]
      rw [Finset.sum_range_one, Finset.sum_range_one, iteratedCovGrad_zero, iteratedCovGrad_zero]
      -- `rfns(appCcRS Φ W) ≤ rfns Φ · rfns W` by the partial-contraction Cauchy–Schwarz.
      rw [appCcRS_toSection (I := I) (M := M) g 0 a b Φ W x]
      have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g 0 a b x
        (show TensorRSSpace a b I x from Φ.toSection x)
        (show TensorRSSpace 0 a I x from W.toSection x)
      simpa using h
  | succ j ih =>
      intro a b Φ W x
      classical
      -- Front-commute one gradient: `∇^{j+1}(appCcRS Φ W)` has the same `rfns` as `∇^j(∇(appCcRS Φ W))`.
      rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g 0 b j
        (appCcRS (I := I) (M := M) g 0 a b Φ W) x]
      -- Split the inner gradient by the operator-field covariant product rule.
      rw [covGrad_appCcRS_eq (I := I) (M := M) g 0 a b Φ W]
      rw [iteratedCovGrad_add]
      -- Separate the two arms.
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((b + 1) + j) x
        ((iteratedCovGrad (I := I) g 0 (b + 1) j
          (appCcRS (I := I) (M := M) g 0 a (b + 1)
            (covGrad (I := I) (M := M) g a b Φ) W)).toSection x)
        ((iteratedCovGrad (I := I) g 0 (b + 1) j
          (appCcRS (I := I) (M := M) g 0 (a + 1) (b + 1)
            (slotExtend (I := I) (M := M) g a b Φ)
            (covGrad (I := I) (M := M) g 0 a W))).toSection x)) ?_
      -- Abbreviations for the jet coefficient families and the diagonal grids.
      set cΦ : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i Φ).toSection x) with hcΦ_def
      set cW : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (a + l) x
        ((iteratedCovGrad (I := I) g 0 a l W).toSection x) with hcW_def
      have hcΦ_nn : ∀ i, 0 ≤ cΦ i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (b + i) x _
      have hcW_nn : ∀ l, 0 ≤ cW l := fun l =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (a + l) x _
      have hGj_nn : (0 : ℝ) ≤ appCcGdiag (E := E) j := appCcGdiag_nonneg (E := E) j
      have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      -- Arm A: bound by the IH at `(a, b + 1)` on `∇Φ`, then reindex `Φ`-jets.
      have hArmA : riemannianFiberNormSq (I := I) (M := M) g 0 ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g 0 (b + 1) j
              (appCcRS (I := I) (M := M) g 0 a (b + 1)
                (covGrad (I := I) (M := M) g a b Φ) W)).toSection x) ≤
          appCcGdiag (E := E) j *
            ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l := by
        refine le_trans (ih a (b + 1) (covGrad (I := I) (M := M) g a b Φ) W x) ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hGj_nn
        rw [hcΦ_def]
        dsimp only
        rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g a b i Φ x]
      -- Arm B: bound by the IH at `(a + 1, b + 1)` on `slotExtend Φ`, `∇W`; slot-extension + comm.
      have hArmB : riemannianFiberNormSq (I := I) (M := M) g 0 ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g 0 (b + 1) j
              (appCcRS (I := I) (M := M) g 0 (a + 1) (b + 1)
                (slotExtend (I := I) (M := M) g a b Φ)
                (covGrad (I := I) (M := M) g 0 a W))).toSection x) ≤
          appCcGdiag (E := E) j *
            ((Module.finrank ℝ E : ℝ) *
              ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
        refine le_trans (ih (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b Φ)
          (covGrad (I := I) (M := M) g 0 a W) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ hGj_nn
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        -- `rfns(∇^i(slotExtend Φ)) ≤ n·rfns(∇^iΦ)`, and `rfns(∇^l(∇W)) = rfns(∇^{l+1}W)`.
        have hWinner : (∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((a + 1) + l) x
                ((iteratedCovGrad (I := I) g 0 (a + 1) l
                  (covGrad (I := I) (M := M) g 0 a W)).toSection x)) =
            ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcW_def]
          dsimp only
          rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g 0 a l W x]
        rw [hWinner]
        have hΦle : riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
              ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                (slotExtend (I := I) (M := M) g a b Φ)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) * cΦ i := by
          rw [hcΦ_def]
          dsimp only
          exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g a b Φ i x
        calc riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
                ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                  (slotExtend (I := I) (M := M) g a b Φ)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
            ≤ ((Module.finrank ℝ E : ℝ) * cΦ i) * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) :=
                mul_le_mul_of_nonneg_right hΦle
                  (Finset.sum_nonneg (fun l _ => hcW_nn (l + 1)))
          _ = (Module.finrank ℝ E : ℝ) * (cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
                ring
      -- Combine the two arms (each with the factor `2` from `rfns_add_le`) with the combinatorial step.
      refine le_trans (add_le_add
        (mul_le_mul_of_nonneg_left hArmA (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hArmB (by norm_num : (0:ℝ) ≤ 2))) ?_
      -- Pull `appCcGdiag j` and the dimension factor out; reduce to the pure combinatorial step.
      set Gj : ℝ := appCcGdiag (E := E) j with hGj_def
      set SA : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l
        with hSA_def
      set SB : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
        with hSB_def
      set DG : ℝ := ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l with hDG_def
      have hstep : SA + (Module.finrank ℝ E : ℝ) * SB ≤ ((Module.finrank ℝ E : ℝ) + 1) * DG := by
        rw [hSA_def, hSB_def, hDG_def]
        exact diagonalGrid_step_le (Module.finrank ℝ E : ℝ) hn_nn j cΦ cW hcΦ_nn hcW_nn
      have hGdiag_succ : appCcGdiag (E := E) (j + 1) = (2 * ((Module.finrank ℝ E : ℝ) + 1)) * Gj := by
        rw [hGj_def, appCcGdiag, appCcGdiag, pow_succ]; ring
      rw [hGdiag_succ]
      -- `2·(Gj·SA) + 2·(Gj·(n·SB)) = 2 Gj (SA + n SB) ≤ 2 Gj (n+1) DG`.
      have hGj_nn' : (0 : ℝ) ≤ Gj := hGj_nn
      nlinarith [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * Gj), hGj_nn',
        hstep]

/-- **The `appCc` diagonal product grid (the headline pointwise Moser-tame grid).**

For a fixed coefficient operator field `C : SmoothCcTensor g b₀ s₀` (covariant source width `b₀`,
target `s₀`) acting on a section `W : SmoothCcTensor g 0 b₀`, at every base point `x` and gradient
order `j` the iterated covariant gradient of the contracted action `appCc C W` is bounded by the
**diagonal product** of the `C`-jets (at contravariant valence `b₀`) and the `W`-jets:
```
rfns(∇^j (appCc C W))(x) ≤ Gdiag j · ∑_{i ≤ j} rfns(∇^i C)(x) · ∑_{l ≤ j − i} rfns(∇^l W)(x),
```
with `Gdiag j = (2 (n + 1))^j`, `n = Module.finrank ℝ E`.  This is the diagonal companion of the
single-sum drop bound `appCc_iteratedCovGrad_drop_singleSum_le`: there the coefficient is collapsed
into an `L^∞` window envelope, here it carries its own covariant-`L²` jets, so the apex top-order
Ricci–DeTurck-arm leaf can feed it into the integrated Gagliardo–Nirenberg two-arm EXTREMES engine
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` with each arm carrying one factor's
full covariant-`L²` jet scale against the other factor's order-`0` `C⁰` sup.

The rank-`0` reading of the generic-valence diagonal grid
`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le` through `appCcRS_zero_eq_appCc`. -/
theorem appCc_iteratedCovGrad_diagonalProductGrid_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (W : SmoothCcTensor g 0 b₀) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
        ((iteratedCovGrad (I := I) g 0 s₀ j (appCc (I := I) (M := M) g b₀ s₀ C W)).toSection x) ≤
      appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g b₀ (s₀ + i) x
              ((iteratedCovGrad (I := I) g b₀ s₀ i C).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ + l) x
                ((iteratedCovGrad (I := I) g 0 b₀ l W).toSection x) := by
  rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g b₀ s₀ C W]
  exact rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le (I := I) (M := M) g j b₀ s₀ C W x

private lemma sum_finZeroFun_eq {N : ℕ} (f : (Fin 0 → Fin N) → ℝ) :
    ∑ K : Fin 0 → Fin N, f K = f (fun k : Fin 0 => k.elim0) := by
  refine Finset.sum_eq_single (fun k : Fin 0 => k.elim0) ?_ ?_
  · exact fun K _ hK => absurd (funext (fun k : Fin 0 => k.elim0)) hK
  · exact fun h => absurd (Finset.mem_univ _) h

private lemma sum_consEquiv {N t : ℕ} (F : (Fin (t + 1) → Fin N) → ℝ) :
    ∑ J : Fin (t + 1) → Fin N, F J =
      ∑ j0 : Fin N, ∑ J' : Fin t → Fin N, F (Fin.cons j0 J') := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (t + 1) => Fin N))
      (fun pr : Fin N × (Fin t → Fin N) => F (Fin.cons pr.1 pr.2)) F
      (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]

set_option linter.unusedSectionVars false in

private lemma tensor00Scalar_coframe0_eq_one (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (e : Fin N → TangentSpace I x) (K : Fin 0 → Fin N) :
    tensor00Scalar (I := I) (M := M) x (coframeS (I := I) (M := M) g x 0 e K) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
    coframeS_apply (I := I) (M := M) g x 0 e K (fun k : Fin 0 => k.elim0)]
  simp

set_option linter.unusedSectionVars false in

private lemma rfns_zero_eq_sum_componentSq
    (g : SmoothRiemannianMetric I M) (x : M) (m : ℕ) (S : TensorRSSpace 0 m I x)
    {N : ℕ} (e : Fin N → TangentSpace I x)
    (bse : Module.Basis (Fin N) ℝ (TangentSpace I x))
    (hn : N = Module.finrank ℝ E) (hbse : ∀ i : Fin N, bse i = e i)
    (horth : ∀ a b : Fin N, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
      ∑ J : Fin m → Fin N,
        (fiberNormSqComponent (I := I) (M := M) g x 0 m S N e (fun k : Fin 0 => k.elim0) J) ^ 2 := by
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 0 m x S e bse hn hbse horth]
  rw [sum_finZeroFun_eq]

private noncomputable def appCcSlice (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M)
    {N : ℕ} (e : Fin N → TangentSpace I x) (W : SmoothCcTensor g 0 (r + 1))
    (j0 : Fin N) : TensorRSSpace 0 r I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
        (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
      (show E from e j0))

set_option linter.unusedSectionVars false in

private lemma appCcSlice_apply_coframe0 (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M)
    {N : ℕ} (e : Fin N → TangentSpace I x) (W : SmoothCcTensor g 0 (r + 1))
    (j0 : Fin N) (K : Fin 0 → Fin N) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from appCcSlice (I := I) (M := M) g r x e W j0)
        (coframeS (I := I) (M := M) g x 0 e K) =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
          (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
        (show E from e j0) := by
  rw [appCcSlice, ContinuousLinearMap.smulRight_apply,
    tensor00Scalar_coframe0_eq_one (I := I) (M := M) g x e K, one_smul]

set_option linter.unusedSectionVars false in

private lemma fiberNormSqComponent_zero_eq_toModel
    (g : SmoothRiemannianMetric I M) (x : M) (m : ℕ) (S : TensorRSSpace 0 m I x)
    {N : ℕ} (e : Fin N → TangentSpace I x) (K : Fin 0 → Fin N) (J : Fin m → Fin N) :
    fiberNormSqComponent (I := I) (M := M) g x 0 m S N e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from S)
          (coframeS (I := I) (M := M) g x 0 e K))
        (fun k => (show E from e (J k))) := rfl

set_option maxHeartbeats 6400000 in

theorem riemannianFiberNormSq_appCc_slotExtend_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 (r + 1)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((appCc (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1) x (W.toSection x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis (I := I) (M := M) g x
  have hdiamond : ∀ (j0 : Fin (Module.finrank ℝ E))
      (J' : Fin s → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1)
          ((appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ) W).toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 J') =
        fiberNormSqComponent (I := I) (M := M) g x 0 s
          (show TensorRSSpace 0 s I x from
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                appCcSlice (I := I) (M := M) g r x e W j0))
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) J' := by
    intro j0 J'
    have hL : fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1)
          ((appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ) W).toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 J') =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
                (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
              (show E from e j0)))
          (fun k : Fin s => (show E from e (J' k))) := by
      rw [fiberNormSqComponent_zero_eq_toModel (I := I) (M := M) g x (s + 1)
        ((appCc (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) e (fun k : Fin 0 => k.elim0)
        (Fin.cons j0 J')]
      rw [appCc_toSection, slotExtend_toSection, ContinuousLinearMap.comp_apply]
      rw [show (fun k => (show E from
            e ((Fin.cons j0 J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k))) =
          Fin.cons (show E from e j0) (fun k : Fin s => (show E from e (J' k))) from by
        funext k
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
        · simp only [Fin.cons_zero]
        · simp only [Fin.cons_succ]]
      rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
          (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
        (show E from e j0) (fun k : Fin s => (show E from e (J' k)))]
    have hR : fiberNormSqComponent (I := I) (M := M) g x 0 s
          (show TensorRSSpace 0 s I x from
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                appCcSlice (I := I) (M := M) g r x e W j0))
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) J' =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
                (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
              (show E from e j0)))
          (fun k : Fin s => (show E from e (J' k))) := by
      rw [fiberNormSqComponent_zero_eq_toModel (I := I) (M := M) g x s
        (show TensorRSSpace 0 s I x from
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
              appCcSlice (I := I) (M := M) g r x e W j0)) e (fun k : Fin 0 => k.elim0) J']
      rw [ContinuousLinearMap.comp_apply,
        appCcSlice_apply_coframe0 (I := I) (M := M) g r x e W j0 (fun k : Fin 0 => k.elim0)]
    rw [hL, hR]
  have hVW : ∀ (j0 : Fin (Module.finrank ℝ E))
      (P : Fin r → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 r
          (appCcSlice (I := I) (M := M) g r x e W j0)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) P =
        fiberNormSqComponent (I := I) (M := M) g x 0 (r + 1) (W.toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 P) := by
    intro j0 P
    have hL : fiberNormSqComponent (I := I) (M := M) g x 0 r
          (appCcSlice (I := I) (M := M) g r x e W j0)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) P =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
            (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
          (Fin.cons (show E from e j0) (fun k : Fin r => (show E from e (P k)))) := by
      rw [fiberNormSqComponent_zero_eq_toModel (I := I) (M := M) g x r
        (appCcSlice (I := I) (M := M) g r x e W j0) e (fun k : Fin 0 => k.elim0) P]
      rw [appCcSlice_apply_coframe0 (I := I) (M := M) g r x e W j0 (fun k : Fin 0 => k.elim0)]
      rw [tensor0S_curry_apply_eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
          (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
        (show E from e j0) (fun k : Fin r => (show E from e (P k)))]
    have hR : fiberNormSqComponent (I := I) (M := M) g x 0 (r + 1) (W.toSection x)
          (Module.finrank ℝ E) e (fun k : Fin 0 => k.elim0) (Fin.cons j0 P) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from W.toSection x)
            (coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)))
          (fun k => (show E from
            e ((Fin.cons j0 P : Fin (r + 1) → Fin (Module.finrank ℝ E)) k))) :=
      fiberNormSqComponent_zero_eq_toModel (I := I) (M := M) g x (r + 1) (W.toSection x)
        e (fun k : Fin 0 => k.elim0) (Fin.cons j0 P)
    rw [hL, hR]
    congr 1
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  have hLHS : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) =
        ∑ j0 : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (show TensorRSSpace 0 s I x from
              (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                  appCcSlice (I := I) (M := M) g r x e W j0)) := by
    rw [rfns_zero_eq_sum_componentSq (I := I) (M := M) g x (s + 1)
      ((appCc (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ) W).toSection x) e bse rfl hbse horth]
    rw [sum_consEquiv]
    refine Finset.sum_congr rfl (fun j0 _ => ?_)
    rw [rfns_zero_eq_sum_componentSq (I := I) (M := M) g x s
      (show TensorRSSpace 0 s I x from
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            appCcSlice (I := I) (M := M) g r x e W j0)) e bse rfl hbse horth]
    refine Finset.sum_congr rfl (fun J' _ => ?_)
    rw [hdiamond j0 J']
  have hsum : ∑ j0 : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 r x
          (appCcSlice (I := I) (M := M) g r x e W j0) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1) x (W.toSection x) := by
    rw [rfns_zero_eq_sum_componentSq (I := I) (M := M) g x (r + 1) (W.toSection x)
      e bse rfl hbse horth]
    rw [sum_consEquiv]
    refine Finset.sum_congr rfl (fun j0 _ => ?_)
    rw [rfns_zero_eq_sum_componentSq (I := I) (M := M) g x r
      (appCcSlice (I := I) (M := M) g r x e W j0) e bse rfl hbse horth]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hVW j0 P]
  rw [hLHS]
  calc ∑ j0 : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (show TensorRSSpace 0 s I x from
              (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
                  appCcSlice (I := I) (M := M) g r x e W j0))
      ≤ ∑ j0 : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 r x
              (appCcSlice (I := I) (M := M) g r x e W j0) :=
        Finset.sum_le_sum (fun j0 _ => riemannianFiberNormSq_compRS_le_mul (I := I) (M := M)
          g 0 r s x (Φ.toSection x) (appCcSlice (I := I) (M := M) g r x e W j0))
    _ = riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
          ∑ j0 : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 r x
              (appCcSlice (I := I) (M := M) g r x e W j0) := by
        rw [Finset.mul_sum]
    _ = riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1) x (W.toSection x) := by
        rw [hsum]

end Connection
end Integral
end DifferentialGeometry

end
