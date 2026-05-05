import DifferentialGeometry.Analysis.Laplacian.Operator

/-!
# Symmetry of the variational Laplacian

For a closed Riemannian manifold `(M, g)`, the variational Laplacian
`laplacianOp : laplacianDomain g →ₗ[ℝ] Lp ℝ 2 μ_g` is symmetric in the
`Lp` inner product:

  `⟨H1ComplToLp u, Δ_g v⟩_{L²} = ⟨Δ_g u, H1ComplToLp v⟩_{L²}`
  for all `u, v ∈ laplacianDomain g`.

The proof is direct from symmetry of the H¹ inner product on `H1Compl g`.
Specifically, for `u = resolvent g f` and `v = resolvent g h`, the variational
identity gives
  `⟨resolvent g f, w⟩_{H¹} = ⟨H1ComplToLp w, f⟩_{L²}` for every `w`,
in particular for `w = resolvent g h`. Then symmetry of the H¹ inner product
swaps the two sides.

## Main result

* `laplacianOp_symmetric`: the symmetry identity above.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Auxiliary identities -/

/-- For `u, v ∈ laplacianDomain g`, the H¹ inner product expands via the
variational identity into an `Lp` inner product against the preimage. -/
private lemma h1Inner_eq_lpInner_with_preimage
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ := by
  -- `u = resolvent (preimage u)`. Apply the variational identity.
  have h_u_eq : (u : H1Compl g) = resolvent (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g u) :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g u).symm
  rw [h_u_eq]
  exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g
    (laplacianDomain.preimage (I := I) (M := M) g u) (v : H1Compl g)

/-- The L² inner product `⟨H1ComplToLp v, preimage u⟩` equals
`⟨H1ComplToLp u, preimage v⟩` (a key consequence of H¹ symmetry). -/
private lemma lpInner_preimage_swap
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ := by
  -- Both sides equal `⟨u, v⟩_{H¹}` (and `⟨v, u⟩_{H¹}` by symmetry).
  -- LHS = ⟨v, u⟩_{H¹} via h1Inner_eq_lpInner_with_preimage applied to (u, v).
  -- RHS = ⟨u, v⟩_{H¹} via h1Inner_eq_lpInner_with_preimage applied to (v, u).
  -- ⟨v, u⟩ = ⟨u, v⟩ by symmetry of real inner product.
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g u v]
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g v u]
  exact real_inner_comm _ _

/-! ## Main symmetry theorem -/

/-- **Symmetry of the variational Laplacian.** For `u, v ∈ laplacianDomain g`,

  `⟨H1ComplToLp u, Δ_g v⟩_{L²} = ⟨Δ_g u, H1ComplToLp v⟩_{L²}`. -/
theorem laplacianOp_symmetric (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianOp (I := I) (M := M) g v⟫_ℝ =
      ⟪laplacianOp (I := I) (M := M) g u,
        H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
  -- LHS = ⟨H1ComplToLp u, H1ComplToLp v - preimage v⟩
  --     = ⟨H1ComplToLp u, H1ComplToLp v⟩ - ⟨H1ComplToLp u, preimage v⟩.
  -- RHS = ⟨H1ComplToLp u - preimage u, H1ComplToLp v⟩
  --     = ⟨H1ComplToLp u, H1ComplToLp v⟩ - ⟨preimage u, H1ComplToLp v⟩.
  -- The first parts cancel; the second parts equal each other by `lpInner_preimage_swap`
  -- (after using symmetry of the real inner product to swap arguments).
  rw [laplacianOp_apply, laplacianOp_apply]
  rw [inner_sub_right, inner_sub_left]
  -- LHS - RHS = -⟨H1ComplToLp u, preimage v⟩ - (-⟨preimage u, H1ComplToLp v⟩)
  --          = -⟨H1ComplToLp u, preimage v⟩ + ⟨preimage u, H1ComplToLp v⟩
  --          = -⟨H1ComplToLp u, preimage v⟩ + ⟨H1ComplToLp v, preimage u⟩  (real_inner_comm)
  --          = 0  (lpInner_preimage_swap with u, v swapped)
  have h_swap := lpInner_preimage_swap (I := I) (M := M) g v u
  -- h_swap : ⟨H1ComplToLp u, preimage v⟩ = ⟨H1ComplToLp v, preimage u⟩.
  -- Apply symmetry to align with the proof goal.
  have h_swap_inner :
      ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
          laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ =
        ⟪laplacianDomain.preimage (I := I) (M := M) g u,
          H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
    rw [h_swap, real_inner_comm]
  linarith [h_swap_inner]

/-! ## Symmetry of the variational form

A useful corollary: the variational form `⟨u, v⟩_{H¹}` is symmetric in
`u, v ∈ laplacianDomain g`. (This follows trivially from symmetry of the
H¹ inner product, but is worth recording.) -/

/-- For `u, v ∈ laplacianDomain g`, the H¹ inner product is symmetric.
This follows trivially from the symmetry of `⟨·, ·⟩_{H1Compl}`. -/
theorem h1Inner_symmetric_on_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪(v : H1Compl g), (u : H1Compl g)⟫_ℝ :=
  real_inner_comm _ _

/-! ## Sanity tests -/

example (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪H1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianOp (I := I) (M := M) g v⟫_ℝ =
      ⟪laplacianOp (I := I) (M := M) g u,
        H1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ :=
  laplacianOp_symmetric (I := I) (M := M) g u v

end Laplacian
end Analysis
end DifferentialGeometry

end
