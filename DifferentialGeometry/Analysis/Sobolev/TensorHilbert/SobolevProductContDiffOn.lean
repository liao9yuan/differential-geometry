import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SupercriticalSobolevAlgebra

/-! # `C^∞`-in-the-input of a supercritical chart-Sobolev bare-tensor product of two smooth maps

A small reusable bridge between the supercritical chart-Sobolev Banach-algebra product
(`SupercriticalSobolevAlgebra.lean`) and the `ContDiffOn` calculus: if two maps
`f : Dom → H^{k}(0, s₁)` and `h : Dom → H^{k}(0, s₂)` into the chart-Sobolev Hilbert completions are
`ContDiffOn ℝ n` on a set `s`, then their pointwise bare tensor product, read at the output order
`s'`,

  `x ↦ (f x) ⊗ (h x) : Dom → H^{s'}(0, s₁ + s₂)` ,

is `ContDiffOn ℝ n` on `s`, for any supercritical input order `k = N + 2 s'` (`dim M < 2 N`).

## Why a dedicated lemma (the heterogeneous diagonal)

The on-disk diagonal brick `BanachAlgebraSmoothness.contDiffOn_bilinDiag` is stated for a bilinear
map `B : A × A → G` with the **same** carrier `A` in both slots (the Banach-algebra self-product).
The chart-Sobolev bare product is genuinely **heterogeneous** — its two factors live in different
valence completions `H^{k}(0, s₁)`, `H^{k}(0, s₂)` and its value in a third, `H^{s'}(0, s₁ + s₂)`.
Mathlib's `IsBoundedBilinearMap.contDiff` is already fully heterogeneous (`b : E × F → G`), so the
diagonal of a heterogeneous bounded bilinear map applied to two `C^∞` maps is `C^∞`; this file packages
that heterogeneous diagonal once (`contDiffOn_isBoundedBilinearMap_diag`) and instantiates it on the
supercritical bare-product `IsBoundedBilinearMap` witness
(`exists_isBoundedBilinearMap_bareTensorProd_supercritical`), so a consumer building a chart-Sobolev
rational-polynomial Nemytskii functional cites a single product-smoothness lemma in the exact `toHs`
currency rather than re-threading the `prodMk` / `comp_contDiffOn` bookkeeping.

This is the polynomial-numerator product brick of a chart-rational DeTurck functional, in the
`H^k → H^{s'}` chart-Sobolev currency.  It is **not** the rational/inverse part (that is the
inverse-Gram Neumann spine on the fibre-operator algebra, `FibreOperatorAlgebra.lean`); the two
together are the algebra operations a quasilinear chart-Sobolev Nemytskii map composes.

All inputs are sorry-free, so the bridge is sorry-free. -/

noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **`C^∞` of the diagonal of a heterogeneous bounded bilinear map applied to two `C^∞` maps.**

For a bounded bilinear map `B : F₁ × F₂ → G` (the two slots living in *different* normed spaces) and
`ContDiffOn ℝ n` maps `f : Dom → F₁`, `h : Dom → F₂` on `s`, the diagonal `x ↦ B (f x, h x)` is
`ContDiffOn ℝ n` on `s`.  A bounded bilinear map is `C^∞` (`IsBoundedBilinearMap.contDiff`, fully
heterogeneous), composed with the `C^∞` pairing `x ↦ (f x, h x)` (`ContDiffOn.prodMk`).  This is the
heterogeneous companion of `BanachAlgebraSmoothness.contDiffOn_bilinDiag`, needed because the
chart-Sobolev bare product has distinct valence completions in its two slots and its value. -/
theorem contDiffOn_isBoundedBilinearMap_diag
    {Dom : Type*} [NormedAddCommGroup Dom] [NormedSpace ℝ Dom]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set Dom} {B : F₁ × F₂ → G} {f : Dom → F₁} {h : Dom → F₂} {n : WithTop ℕ∞}
    (hB : IsBoundedBilinearMap ℝ B) (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s) :
    ContDiffOn ℝ n (fun x => B (f x, h x)) s :=
  hB.contDiff.comp_contDiffOn (hf.prodMk hh)

/-- **`C^∞`-in-the-input of the supercritical chart-Sobolev bare tensor product of two `C^∞` maps.**

For a closed Riemannian manifold, a supercritical Sobolev floor `N` (`dim M < 2 N`), a fixed domain
`Dom`, and two `ContDiffOn ℝ n` maps `f : Dom → H^{N+2s'}(0, s₁)`, `h : Dom → H^{N+2s'}(0, s₂)` on a
set `s`, there is a bounded bilinear bare-product map `B` on the chart-Sobolev Hilbert completions
`H^{N+2s'}(0, s₁) × H^{N+2s'}(0, s₂) → H^{s'}(0, s₁ + s₂)` such that the diagonal `x ↦ B (f x, h x)`
is `ContDiffOn ℝ n` on `s`, and on the dense smooth sections `B` reads the bare tensor product:
`B (S.toHs (N+2s'), T.toHs (N+2s')) = (S ⊗ T).toHs s'`.

This packages the supercritical Banach-algebra product
(`exists_isBoundedBilinearMap_bareTensorProd_supercritical`) into the `ContDiffOn` diagonal form a
quasilinear chart-Sobolev Nemytskii functional consumes: the bare product of two `C^∞` Sobolev-valued
maps is `C^∞`, the multiplicative (polynomial-numerator) structure of a chart-rational DeTurck
quantity in the `toHs` currency.  Both arms are sorry-free. -/
theorem exists_contDiffOn_bareTensorProd_supercritical
    {Dom : Type*} [NormedAddCommGroup Dom] [NormedSpace ℝ Dom]
    (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ s' N : ℕ)
    (h_super : Module.finrank ℝ E < 2 * N) {s : Set Dom}
    {f : Dom → TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 s₁ (N + 2 * s')}
    {h : Dom → TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 s₂ (N + 2 * s')}
    {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s) :
    ∃ (B : TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 s₁ (N + 2 * s') ×
          TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 s₂ (N + 2 * s') →
        TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 (s₁ + s₂) s'),
      (∀ (S : Integral.L2.SmoothCcTensor g₀ 0 s₁) (T : Integral.L2.SmoothCcTensor g₀ 0 s₂),
          B (SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + 2 * s') S,
              SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₂) (N + 2 * s') T)
            = SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁ + s₂) s'
                (bareTensorProdSection (I := I) g₀ S T)) ∧
      ContDiffOn ℝ n (fun x => B (f x, h x)) s := by
  obtain ⟨B, hBilin, hval⟩ :=
    exists_isBoundedBilinearMap_bareTensorProd_supercritical (I := I) (M := M) g₀ s₁ s₂ s' N h_super
  exact ⟨B, hval, contDiffOn_isBoundedBilinearMap_diag hBilin hf hh⟩

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
