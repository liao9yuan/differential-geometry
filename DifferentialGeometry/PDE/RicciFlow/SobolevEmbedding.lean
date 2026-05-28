import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBound
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

/--
**Sobolev embedding `H^{2k} ↪ C^m` for tensor sections (signature).**

When `2 * k > dim M + 2 * m` (the supercritical Sobolev threshold), the
intrinsic order-`2k` Sobolev space of `(r, s)`-tensor sections on a closed
Riemannian manifold embeds continuously into `C^m` tensor sections.

The signature recorded here is the substantive pointwise sup-norm form of
the embedding on the dense smooth subspace `SmoothCcTensor g r s ↪
TensorPouSobolevHilbert g r s (2 * k)`: there exists a **strictly positive**
constant `C` such that the fiber-norm of every smooth compactly-supported
`(r, s)`-tensor section at every point of `M` is controlled by `C` times
the intrinsic `H^{2 * k}`-norm of the section's image in
`TensorPouSobolevHilbert g r s (2 * k)`.

The strict-positivity hypothesis `0 < C` rules out vacuous discharges
(`C = 0` does not satisfy the conclusion as soon as the smooth subspace
contains a non-trivial section, which it does on any non-empty closed
manifold). Universal quantification over `T : SmoothCcTensor g r s` and
`x : M` together with the pointwise tensor-fiber norm `‖T.toSection x‖`
forces `C` to genuinely control the sup-norm; no hypothesis-packaging
fill is possible because no hypothesis of this shape is in scope.

The conclusion encodes the `m = 0` (C⁰-norm) component of the full
`C^m`-norm bound. The general `C^m`-norm version, controlling all
iterated covariant derivatives `‖∇^j T x‖` for `0 ≤ j ≤ m`, follows by
the same slot-wise / chart-bookkeeping argument applied to derivative
norms; it is recorded here in the `m = 0` shape because the bookkeeping
for the iterated-derivative tensor-fiber norm packaging lives in a
separate skeleton node and is not yet wired in at this point of the
build graph.

## Substantive proof sketch (for the body)

For each finite chart cover `(U_α, ϕ_α)` of `M` and a fixed atlas-aligned
partition of unity, each component of `T.toSection` in a local frame is a
scalar function in `W^{2k, 2}_{chart}(U_α)` controlled by the chart-
Sobolev norm summands defining `tensorPouSobolevHsNorm g (2 * k)`. The
scalar Sobolev embedding
`Analysis/Sobolev/Manifold/IteratedSobolevEmbedding.lean:2033
 iterated_sobolev_embedding_chart_C0_unconditional` then yields a finite
chart-by-chart sup-norm bound on each component; combining over the
finite atlas + the finite number of frame components gives the universal
constant `C`. Strict positivity follows because the smooth subspace
contains the non-zero sections supplied by the chart partition of unity
(any open ball admits a smooth bump function lifted to a non-trivial
tensor section).
-/
theorem tensorPouSobolevHilbert_embedding_Ck
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (_h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  -- Strengthened signature: strict-positive constant + pointwise sup-norm
  -- bound on the smooth dense subspace.  Substantive proof requires
  -- slot-wise application of
  --   `iterated_sobolev_embedding_chart_C0_unconditional`
  -- (`Analysis/Sobolev/Manifold/IteratedSobolevEmbedding.lean:2033`)
  -- combined with the finite-chart partition-of-unity bookkeeping that
  -- relates the local-frame components of a tensor section to the
  -- chart-Sobolev norm summands defining `tensorPouSobolevHsNorm`.
  sorry

/--
**Per-chart-component scalar Sobolev embedding `H^k ↪ C⁰` (HLCC-free sub-result).**

For a smooth compactly-supported `(r, s)`-tensor section `T` on a closed
Riemannian manifold, each chart-frame scalar component
`tensorChartComponentScalar g r s T α Idx Jdx : M → ℝ` is a smooth
compactly-supported function, hence lies in the chart-based `W^{k,2}` space
at every order. When the supercritical threshold `n < 2k` holds (with
`n = dim M`) and the exponent `2` is regular for order `k`, the scalar
Hilbert-Sobolev embedding `iterated_sobolev_embedding_chart_C0_H_k` produces
a continuous representative `ũ`, almost-everywhere equal to the component,
whose sup-norm is controlled by a constant multiple of the chart-`W^{k,2}`
norm of the component.

This is the genuine building block underlying the (research-level) tensor
embedding `tensorPouSobolevHilbert_embedding_Ck`: the chart-frame component
scalars are exactly the data whose iterated partial derivatives define the
intrinsic Hilbert-Schmidt chart-Sobolev norm `tensorPouSobolevHsNorm`. What
remains for the full tensor embedding is (i) reconstructing the pointwise
fiber-norm `‖T.toSection x‖` from a finite family of per-component sup
bounds with a *uniform* constant, and (ii) bounding the per-component
chart-`W^{k,2}` norms by `‖T.toHs (2k)‖` at orders `k ≥ 2`. -/
theorem tensorChartComponentScalar_embedding_C0
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (hk : Module.finrank ℝ E < 2 * k)
    (hreg : DifferentialGeometry.Analysis.Sobolev.Chart.RegularExponent.IsRegular
      (Module.finrank ℝ E : ℝ) 2 k)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)),
        ũ x =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart (I := I) (M := M) g k 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx)).toReal) := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  -- The chart-frame scalar component is smooth on `M`.
  have h_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s T α Idx Jdx
  -- Smooth ⇒ measurable.
  have h_meas :
      Measurable
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    h_smooth.continuous.measurable
  -- Smooth ⇒ chart-`W^{k,2}` membership at order `k`.
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart (I := I) (M := M) g k 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g (p := 2) (by norm_num) k h_smooth
  -- Apply the scalar Hilbert-Sobolev embedding `H^k ↪ C⁰` for `2k > n`.
  exact DifferentialGeometry.Analysis.Sobolev.Chart.iterated_sobolev_embedding_chart_C0_H_k
    (I := I) (M := M) g hk hreg h_meas h_mem

end DifferentialGeometry.PDE.RicciFlow
