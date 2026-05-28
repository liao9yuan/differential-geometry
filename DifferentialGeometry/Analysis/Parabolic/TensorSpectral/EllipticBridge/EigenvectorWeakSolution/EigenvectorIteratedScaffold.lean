import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData

/-!
# Standalone iterated divergence-form datum for the eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the chart
`P₀`-component of a resolvent eigenvector of the connection Laplacian `Δ_∇`
satisfies a scalar divergence-form weak-elliptic identity with principal symbol
`weightedInvGramOnEuclid g α`. The arbitrary-order interior-regularity bootstrap
iterates the elliptic Leibniz-commutator step, raising the Sobolev order by one
each time it differentiates the identity.

The plain per-component datum `TensorChartBilinearH1ComplData g r s α P₀` does
not compose under iteration: it carries no level index and its principal block
is the *first* weak partial. This module ships the **standalone iterated
divergence-form datum** that does compose — the eigenvector/tensor mirror of the
scalar campaign's `IteratedDiffChartBilinearData`.

## Schematic form

The packaged identity reads, at level `m`,
```
∫_{chartTarget} ∑_{a, b} weightedInvGramOnEuclid · ∂^{m}_dir(u_chart)_{cons a dir} · ∂_bψ
  + ∫_{chartTarget} densityOnEuclid · ∂^{m}_dir(u_chart)_dir · ψ
  = ∫_{chartTarget} densityOnEuclid · fChartEff · ψ
```
where `dir : Fin m → Fin n` is the direction multi-index, `cons a dir` is the
direction multi-index used by the inner principal LHS (with the additional
direction `a` prepended innermost), and `fChartEff : EuclN → ℝ` is the effective
`L²` source at level `m`. The `m`-fold mixed weak partials are the recursive
`eigenvectorChartIteratedPartial` — chosen weak partials taken via
`chosenWeakPartial'` — which composes definitionally under `Fin.snoc`/`Fin.cons`.

## Why the standalone structure composes

The principal factor is `eigenvectorChartIteratedPartial g r s h_atlas i α P₀
(m+1) (Fin.cons a dir)`. Its `Fin.snoc`/`Fin.cons` composition is definitional:
the level-`(m+1)` mixed partial along `Fin.snoc dir l` peels — by the recursive
definition together with `Fin.snoc_last` and `Fin.init_snoc` — to the chosen
weak `l`-partial of the level-`m` mixed partial along `dir`. This is exactly the
composition that the inductive step (part 2) needs in order to build a
level-`(m+1)` datum from a level-`m` one.

## Main definitions

* `eigenvectorIteratedTensorChartBilinearData` — the standalone iterated
  divergence-form datum (a `Type`), the eigenvector/tensor mirror of
  `IteratedDiffChartBilinearData`.
* `eigenvectorChartIteratedStepNumerator` — the explicit five-layer differentiated
  numerator with `dir`/`l` separated (the standalone-step shape).
* `eigenvectorChartIteratedStep` — the indicator-of-`chartPouKernel` of the
  numerator divided by `densityOnEuclid g α`.

## Main theorems

* `eigenvectorChartIteratedPartial_memW1p_of_memWkp` — global `MemW1p 2` of every
  `m`-fold mixed weak partial from global `MemWkp (m+1) 2` of the chart
  component (the tensor analogue of `chosenMthMixedPartialChartPushedU_memW1p_two`).
* `eigenvector_per_pair_ibp` — the per-pair integration by parts at level `m`
  applied to the `m`-fold mixed weak partial (the tensor analogue of
  `per_pair_ibp_chosenMthMixed`).
* `eigenvectorChartIteratedStep_memLp_two_weighted` — the weighted-`L²`
  regularity of `eigenvectorChartIteratedStep`, *unconditional*.
* `eigenvectorIteratedTensorChartBilinearData.ofBase` — the `m = 0` instance.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The standalone iterated divergence-form datum

The structure `eigenvectorIteratedTensorChartBilinearData` packages the
level-`m` differentiated divergence-form variational identity satisfied by the
eigenvector chart component. It is the eigenvector/tensor mirror of the scalar
campaign's `IteratedDiffChartBilinearData`: it carries the level index `m`, the
`m`-direction multi-index, the effective `L²` source, its weighted-`L²`
regularity, and the variational identity itself, whose principal factor is the
recursive `m`-fold mixed weak partial `eigenvectorChartIteratedPartial`. -/

/-- **Standalone iterated divergence-form datum for the eigenvector chart
component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, and a
component multi-index `P₀`, this is the `m`-times-differentiated divergence-form
data on `chartTargetEuclid α` for the chart `P₀`-component of the resolvent
eigenvector. The structure captures the polymorphic shape of the variational
identity at level `m`:
```
∫ ∑_{a, b} weightedInvGramOnEuclid · (m+1)-mixed-partial_{cons a dir} · ∂_bψ
  + ∫ densityOnEuclid · m-mixed-partial_dir · ψ
  = ∫ densityOnEuclid · fChartEff · ψ
```
where `dir : Fin m → Fin n` is the direction multi-index, the `m+1`-mixed and
`m`-mixed partials are `eigenvectorChartIteratedPartial g r s h_atlas i α P₀`
at levels `m+1`/`m`, and the LHS principal uses `Fin.cons a dir` to prepend the
additional direction `a` innermost.

This is the eigenvector/tensor mirror of the scalar `IteratedDiffChartBilinearData`.
The plain per-component datum `TensorChartBilinearH1ComplData g r s α P₀` does not
compose under iteration; this standalone structure — carrying the level index
`m`, with the `m`-fold mixed weak partial `eigenvectorChartIteratedPartial` as
principal factor — is the campaign's iteration carrier, composing definitionally
under `Fin.snoc`/`Fin.cons`. -/
structure eigenvectorIteratedTensorChartBilinearData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) where
  /-- The `m`-direction multi-index. -/
  directions : Fin m → Fin (Module.finrank ℝ E)
  /-- The effective `L²` source at level `m`. -/
  fChartEff : EuclN → ℝ
  /-- The effective source is `MemLp 2` with respect to the chart-pulled weighted
  measure restricted to `chartTargetEuclid α`. This is the regularity field the
  inductive step consumes. -/
  fChartEff_memLp_weighted :
    MemLp fChartEff 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  /-- The level-`m` differentiated divergence-form variational identity, in the
  `c · fChartEff · ψ` form. Its principal factor is the level-`(m+1)` mixed weak
  partial `eigenvectorChartIteratedPartial … (m+1) (Fin.cons a directions)`,
  which composes definitionally under `Fin.snoc`/`Fin.cons`. -/
  m_diff_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α a b y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m directions y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * fChartEff y * ψ y
        ∂(volume : Measure EuclN)

namespace eigenvectorIteratedTensorChartBilinearData

/-! ## Hypothesis-bearing abstract constructor

The constructor `mk_from_hypotheses` takes the variational identity as an
explicit hypothesis, together with the effective source and its weighted-`L²`
regularity. This is the engine of inductive proofs: the inductive step (part 2)
constructs an instance at level `m + 1` from the instance at level `m` plus one
more directional integration by parts. -/

/-- Hypothesis-bearing abstract constructor for
`eigenvectorIteratedTensorChartBilinearData`. Takes the direction multi-index,
the effective `L²` source, its weighted-`L²` regularity, and the variational
identity as explicit hypotheses. -/
def mk_from_hypotheses
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {i : TensorEigenIdx (I := I) (M := M) g r s}
    {α : M} {P₀ : TensorCompIdx (E := E) r s} {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (fChartEff : EuclN → ℝ)
    (fChartEff_memLp_weighted :
      MemLp fChartEff 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
    (m_diff_variational_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m directions y * ψ y
          ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * fChartEff y * ψ y
          ∂(volume : Measure EuclN)) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m :=
  { directions := directions
    fChartEff := fChartEff
    fChartEff_memLp_weighted := fChartEff_memLp_weighted
    m_diff_variational_identity := m_diff_variational_identity }

end eigenvectorIteratedTensorChartBilinearData

/-! ## Polymorphic regularity bridge for the iterated mixed weak partial

The recursive `m`-fold mixed weak partial `eigenvectorChartIteratedPartial`
peels its **last** entry — the outermost differentiation direction — via
`chosenWeakPartial'`. The structural lemma below mirrors the scalar campaign's
`chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp`: chart-`H^{k+m}`
of the chart component implies chart-`H^k` of every `m`-fold mixed weak partial,
for arbitrary `m, k : ℕ`. The proof is induction on `m`, repeatedly applying
`MemWkp.chosenWeakPartial_mem` to peel off one weak derivative per step. -/

omit [CompleteSpace E] in
/-- **Polymorphic regularity bridge for the eigenvector iterated mixed partial.**
From chart-`H^{k+m}` of the eigenvector chart component on the chart target,
every `m`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s
h_atlas i α P₀ m dirs` lies in chart-`H^k` on the chart target, for arbitrary
`m, k : ℕ` and arbitrary multi-index `dirs : Fin m → Fin n`.

This is the eigenvector/tensor mirror of the scalar campaign's
`chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp`. -/
theorem eigenvectorChartIteratedPartial_memWkp_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      -- `k + 0 = k`, and the `m = 0` mixed partial is the chart component.
      intro k h_parent _dirs
      simpa [eigenvectorChartIteratedPartial_zero] using h_parent
  | succ m ih =>
      intro k h_parent dirs
      -- Rewrite `k + (m + 1)` as `(k + 1) + m` on the parent hypothesis.
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      -- Inductive hypothesis with one fewer derivative on the level-`m` partial.
      have h_inner :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (k + 1) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init dirs))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (k + 1) h_parent' (Fin.init dirs)
      -- Peel off one weak partial in the outermost direction `dirs (Fin.last m)`.
      have h_step := h_inner.chosenWeakPartial_mem (dirs (Fin.last m))
      -- Rewrite via the recursive definition.
      rw [eigenvectorChartIteratedPartial_succ]
      exact h_step

omit [CompleteSpace E] in
/-- **Global `MemW1p 2` of the eigenvector iterated mixed weak partial.**

From global `MemWkp (m + 1) 2` of the eigenvector chart component on the chart
target, every `m`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s
h_atlas i α P₀ m dirs` lies in `DeGiorgi.MemW1p 2` of the chart target. This is
the headline `H¹` regularity the inductive step (part 2) consumes for its
once-more integration by parts.

This is the eigenvector/tensor analogue of the scalar campaign's
`chosenMthMixedPartialChartPushedU_memW1p_two`. -/
theorem eigenvectorChartIteratedPartial_memW1p_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  -- Apply the polymorphic bridge with `k = 1`.
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  have h_memWkp_1 :=
    eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s h_atlas i α P₀ m 1 h_parent' dirs
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_memWkp_1
  exact h_memWkp_1

/-! ## Per-pair integration by parts for the eigenvector iterated mixed partial

The per-pair integration-by-parts identity, applied to the eigenvector `m`-fold
mixed weak partial. It is the eigenvector/tensor analogue of the scalar
campaign's `per_pair_ibp_chosenMthMixed`: there the weakly differentiable factor
was `chosenMthMixedPartialChartPushedU`; here it is `eigenvectorChartIteratedPartial`.

The natural IBP-derived index is `Fin.snoc dirs l : Fin (m+1) → Fin n`. By the
recursive definition the weak `l`-partial of the `m`-fold mixed partial is
precisely the `(m+1)`-fold mixed partial along `Fin.snoc dirs l`. -/

omit [CompleteSpace E] in
/-- **Per-pair polymorphic integration by parts for the eigenvector iterated
mixed partial.** Given global chart-`H^{m+1}` regularity of the eigenvector chart
component, the `m`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s
h_atlas i α P₀ m dirs` lies in `MemW1p 2` on the chart target, and its weak
`l`-partial is, by the recursive definition, `eigenvectorChartIteratedPartial g
r s h_atlas i α P₀ (m+1) (Fin.snoc dirs l)`.

Combined with a smooth chart-target coefficient `φ` and a smooth compactly
supported test function `ψ`, integrating `φ · (m-mixed partial) · ∂_l ψ` by parts
in direction `l` yields
```
∫ φ · (m-mixed partial) · ∂_l ψ
  = -((∫ (∂_l φ) · (m-mixed partial) · ψ)
     + (∫ φ · ((m+1)-mixed partial, index `Fin.snoc dirs l`) · ψ)).
```

This is the eigenvector/tensor analogue of the scalar
`per_pair_ibp_chosenMthMixed`. -/
theorem eigenvector_per_pair_ibp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (l : Fin (Module.finrank ℝ E)) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        φ y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m dirs y *
          ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.snoc dirs l) y *
          ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  -- The `m`-fold mixed weak partial lies in `MemW1p 2` of the chart target.
  have h_v_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartIteratedPartial_memW1p_of_memWkp
      (I := I) (M := M) g r s h_atlas i α P₀ m h_parent dirs
  -- The weak `l`-partial is the `(m+1)`-fold mixed partial along `Fin.snoc dirs l`.
  have h_w_eq :
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.snoc dirs l) =
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
    rw [eigenvectorChartIteratedPartial_succ]
    have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs l
        (Fin.last m) = l := by simp
    have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
        dirs l) = dirs := by simp
    rw [h_last, h_init]
  -- Apply the generic per-pair integration-by-parts primitive (over the chart
  -- target) and rewrite the principal weak partial via `h_w_eq`.
  have h_ibp :=
    generic_per_pair_ibp (I := I) (M := M) (α := α) h_v_memW1p hφ_chart
      hψ_smooth hψ_cs hψ_supp l
  rw [h_w_eq]
  exact h_ibp

/-! ## The five-layer differentiated numerator (standalone-step shape)

`eigenvectorChartIteratedStepNumerator` records the explicit five-layer Leibniz
combination produced by integrating the level-`m` variational identity by parts
once more in the new direction `l`. It is the eigenvector/tensor mirror of the
scalar campaign's `fChartEffStepNumerator`: the level-`m` direction multi-index
`dirs` and the new direction `l` are kept separate (the standalone-step shape),
with the chart-component data instantiated by the recursive `m`-fold mixed weak
partials `eigenvectorChartIteratedPartial`.

It is definitionally equal to `eigenvectorChartRHSDiffNumerator … m (Fin.snoc
dirs l)` — the level-`(m+1)`-indexed numerator built in
`EigenvectorDifferentiatedRHS` — because `Fin.snoc dirs l (Fin.last m) = l` and
`Fin.init (Fin.snoc dirs l) = dirs`. -/

/-- The five-layer differentiated numerator at the inductive step, in the new
direction `l` with level-`m` direction multi-index `dirs : Fin m → Fin n`.

`fChartEffPrev` is the level-`m` effective source. The layers are (mirroring the
scalar campaign's `fChartEffStepNumerator`):

* `A` — `∑_{a,b} (∂_b weightedInvGramDerivOnEuclid g α a b l) ·
  ((m+1)-fold mixed weak partial in `Fin.cons a dirs`)`;
* `B` — `∑_{a,b} weightedInvGramDerivOnEuclid g α a b l ·
  (∂_b-weak-partial of that `(m+1)`-fold mixed weak partial)`;
* `C` — `-(densityDerivOnEuclid g α l) · (m-fold mixed weak partial in `dirs`)`;
* `D` — `(densityDerivOnEuclid g α l) · fChartEffPrev`;
* `E` — `densityOnEuclid g α · (∂_l-weak-partial of fChartEffPrev)`. -/
def eigenvectorChartIteratedStepNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN) : ℝ :=
  -- Layer A: (∂_b ∂_l a_ab) · ((m+1)-fold mixed partial, index `Fin.cons a dirs`).
  (∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b l) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
          (m + 1) (Fin.cons a dirs) y)
  -- Layer B: (∂_l a_ab) · (∂_b of the (m+1)-fold mixed partial, `Fin.cons a dirs`).
  + (∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b l y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a dirs))
            (chartTargetEuclid (I := I) (M := M) α) y)
  -- Layer C: -(∂_l c) · (m-fold mixed partial, index `dirs`).
  - densityDerivOnEuclid (I := I) g α l y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
        m dirs y
  -- Layer D: (∂_l c) · fChartEffPrev.
  + densityDerivOnEuclid (I := I) g α l y * fChartEffPrev y
  -- Layer E: c · (∂_l-weak-partial of fChartEffPrev).
  + densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y

omit [CompleteSpace E] in
/-- The standalone-step numerator coincides definitionally with the
level-`(m+1)`-indexed differentiated numerator `eigenvectorChartRHSDiffNumerator`
built in `EigenvectorDifferentiatedRHS`, evaluated at the snoc-extended index
`Fin.snoc dirs l`. This is the bridge that lets the standalone-step weighted-`L²`
regularity reuse the (unconditional) regularity of the level-`(m+1)` numerator. -/
theorem eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStepNumerator (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs fChartEffPrev l =
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.snoc dirs l) fChartEffPrev := by
  classical
  funext y
  -- `Fin.snoc dirs l (Fin.last m) = l` and `Fin.init (Fin.snoc dirs l) = dirs`.
  have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs l
      (Fin.last m) = l := by simp
  have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
      dirs l) = dirs := by simp
  unfold eigenvectorChartIteratedStepNumerator eigenvectorChartRHSDiffNumerator
  rw [h_last, h_init]

/-! ## The reciprocal chart density

The differentiated numerator is divided by the chart density; the reciprocal
`1 / densityOnEuclid g α` is `C^∞` on the open chart target because the chart
density is `C^∞` and strictly positive there. -/

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there. -/
private lemma one_div_densityOnEuclid_contDiffOn_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-! ## The effective chart-pulled `L²` source at the inductive step

`eigenvectorChartIteratedStep` is the indicator, of the compact partition-of-unity
kernel `chartPouKernel α`, of the chart-density-divided differentiated numerator.
It is the eigenvector/tensor mirror of the scalar campaign's `fChartEffStep`. -/

/-- The effective chart-pulled `L²` source at the inductive step:
`eigenvectorChartIteratedStep g r s h_atlas i α P₀ m dirs fChartEffPrev l`.
Defined as the indicator of the compact partition-of-unity kernel
`chartPouKernel α` applied to
`eigenvectorChartIteratedStepNumerator / densityOnEuclid g α`.

This is the eigenvector/tensor mirror of the scalar campaign's `fChartEffStep`;
it coincides definitionally with `eigenvectorChartRHSDiff … (m+1) (Fin.snoc dirs
l)` (the level-`(m+1)` differentiated right-hand side built in
`EigenvectorDifferentiatedRHS`). -/
def eigenvectorChartIteratedStep
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Set.indicator (chartPouKernel (I := I) (M := M) α)
    (fun y => eigenvectorChartIteratedStepNumerator
        (I := I) (M := M) g r s h_atlas i α P₀ m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y)

omit [CompleteSpace E] in
/-- The standalone-step effective source coincides definitionally with the
level-`(m+1)` differentiated right-hand side `eigenvectorChartRHSDiff` evaluated
at the snoc-extended index `Fin.snoc dirs l`, when the level-`m` effective source
is itself the level-`m` differentiated right-hand side. -/
theorem eigenvectorChartIteratedStep_eq_rhsDiff_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs
        (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs) l =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.snoc dirs l) := by
  classical
  rw [eigenvectorChartRHSDiff_succ]
  unfold eigenvectorChartIteratedStep
  -- The numerator coincides; the recursive `fChartEffPrev` is `Fin.init`-indexed.
  have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
      dirs l) = dirs := by simp
  have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
    (I := I) (M := M) g r s h_atlas i α P₀ m dirs
    (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m dirs) l
  rw [h_num, h_init]

/-! ## Support of the standalone-step effective source

The standalone-step effective source is, by construction, an indicator of the
compact partition-of-unity kernel `chartPouKernel α`; it therefore vanishes
pointwise off that kernel. -/

omit [CompleteSpace E] in
/-- The standalone-step effective source vanishes pointwise off the compact
partition-of-unity kernel `chartPouKernel α` — it is the indicator of that
kernel. -/
theorem eigenvectorChartIteratedStep_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs fChartEffPrev l y = 0 := by
  rw [eigenvectorChartIteratedStep, Set.indicator_of_notMem hy]

omit [CompleteSpace E] in
/-- The support of the standalone-step effective source is contained in the
compact partition-of-unity kernel `chartPouKernel α`. -/
theorem eigenvectorChartIteratedStep_support_subset_chartPouKernel
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {i : TensorEigenIdx (I := I) (M := M) g r s}
    {α : M} {P₀ : TensorCompIdx (E := E) r s} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    {fChartEffPrev : EuclN → ℝ}
    {l : Fin (Module.finrank ℝ E)} :
    Function.support
        (eigenvectorChartIteratedStep (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs fChartEffPrev l) ⊆
      chartPouKernel (I := I) (M := M) α := by
  unfold eigenvectorChartIteratedStep
  exact Set.support_indicator_subset

/-! ## Weighted-`L²` regularity of the standalone-step effective source

The standalone-step effective source is `MemLp 2` with respect to the chart-pulled
weighted measure restricted to the chart target. The membership is
**unconditional** — it carries no regularity hypothesis on the eigenvector beyond
the uniform-Sobolev hypothesis `h_atlas` already needed to name the
eigenvector.

The mechanism is the unconditionality already established in
`EigenvectorDifferentiatedRHS`: the recursive `m`-fold mixed weak partials and
the canonical chosen weak partials are *total* functions and hence
unconditionally `MemLp 2` of the restricted volume; the `W^{1,2}`-regularity of
the eigenvector never enters. The standalone-step numerator coincides
definitionally with the level-`(m+1)`-indexed differentiated numerator, whose
weighted-`L²` regularity is established unconditionally. -/

/-- **Weighted-`L²` regularity of the standalone-step effective source,
unconditional.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level-`m` direction
multi-index `dirs`, a new direction `l`, and a level-`m` effective source
`fChartEffPrev` that is itself `MemLp 2` of the chart-pulled weighted measure on
the chart target, the standalone-step effective source
`eigenvectorChartIteratedStep g r s h_atlas i α P₀ m dirs fChartEffPrev l` is
`MemLp 2` with respect to the chart-pulled weighted measure restricted to
`chartTargetEuclid α`.

The membership carries no regularity hypothesis on the eigenvector: every
constituent of the differentiated numerator is unconditionally `MemLp 2` of the
plain Lebesgue volume restricted to the compact partition-of-unity kernel; the
indicator construction then upgrades the plain-volume membership to the
chart-pulled weighted measure.

This is the eigenvector/tensor analogue of the scalar campaign's
`fChartEffStep_memLp_two_weighted` — but, unlike the scalar version, it requires
no chart-`H^{m+1}` / chart-`H^{m+2}` hypotheses, because the eigenvector iterated
mixed partials are unconditionally `L²`. -/
theorem eigenvectorChartIteratedStep_memLp_two_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemLp fChartEffPrev 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs fChartEffPrev l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The standalone-step effective source coincides definitionally with the
  -- level-`(m+1)` differentiated right-hand side at the snoc-extended index when
  -- `fChartEffPrev` is the level-`m` differentiated right-hand side. For a
  -- *general* `fChartEffPrev` we re-run the proof directly: the numerator
  -- coincides with the level-`(m+1)` differentiated numerator (whose
  -- unconditional `MemLp 2 (volume.restrict K)` is established in
  -- `EigenvectorDifferentiatedRHS`).
  have h_num : MemLp (fun y => eigenvectorChartRHSDiffNumerator
      (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.snoc dirs l)
      fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict K) :=
    eigenvectorChartRHSDiffNumerator_memLp_volume_compact
      (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.snoc dirs l) h_prev
  -- Dividing by the chart density is a `C^∞`-coefficient multiplication on `K`.
  have h_div : MemLp (fun y => eigenvectorChartIteratedStepNumerator
      (I := I) (M := M) g r s h_atlas i α P₀ m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y) 2
      ((volume : Measure EuclN).restrict K) := by
    have h_eq : (fun y => eigenvectorChartIteratedStepNumerator
        (I := I) (M := M) g r s h_atlas i α P₀ m dirs fChartEffPrev l y /
        densityOnEuclid (I := I) g α y) =
        fun y => (1 / densityOnEuclid (I := I) g α y) *
          eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.snoc dirs l) fChartEffPrev y := by
      funext y
      rw [eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator]
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [h_eq]
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (one_div_densityOnEuclid_contDiffOn_chartTarget (I := I) (M := M) g α)
      hK_compact hK_meas hK_in h_num
  -- The standalone-step effective source is the indicator of `K` of the
  -- chart-density-divided numerator; it is `MemLp 2 (volume.restrict
  -- (chartTarget))` and vanishes pointwise off `K`.
  have h_plain : MemLp (eigenvectorChartIteratedStep (I := I) (M := M)
      g r s h_atlas i α P₀ m dirs fChartEffPrev l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [eigenvectorChartIteratedStep, memLp_indicator_iff_restrict hK_meas]
    have h_double : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_double]
    exact h_div
  -- Upgrade the plain-volume membership to the chart-pulled weighted measure.
  refine memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α hK_compact hK_meas hK_in
    (Filter.Eventually.of_forall (fun y hy =>
      eigenvectorChartIteratedStep_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ m dirs fChartEffPrev l hy))
    h_plain

/-! ## The `m = 0` instance — the level-0 chart variational identity

At level `m = 0` the differentiated divergence-form datum is the eigenvector
chart variational identity itself, repackaged into the standalone iterated
shape. The principal block uses the level-`1` mixed weak partial along
`Fin.cons a Fin.elim0`, which is the chosen weak `a`-partial of the chart
component and so agrees a.e. with the candidate weak chart partial
`eigenvectorChartWeakPartial`. -/

omit [CompleteSpace E] in
/-- The level-`1` mixed weak partial along `Fin.cons a Fin.elim0` coincides with
the chosen weak `a`-partial of the chart component. -/
private lemma eigenvectorChartIteratedPartial_one_cons_elim0_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (a : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ 1 (Fin.cons a Fin.elim0) =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
  rw [eigenvectorChartIteratedPartial_succ, eigenvectorChartIteratedPartial_zero]
  -- `Fin.cons a Fin.elim0 (Fin.last 0) = a` and `Fin.init (...) = Fin.elim0`.
  rfl

/-- The candidate weak chart partial `eigenvectorChartWeakPartial g r s h_atlas
i α P₀ a` agrees a.e. on the chart target with the level-`1` mixed weak partial
along `Fin.cons a Fin.elim0` (the chosen weak `a`-partial of the chart
component). Both are genuine weak `a`-partials of the chart component, so they
agree a.e. by uniqueness of weak partials. -/
private lemma eigenvectorChartWeakPartial_ae_eq_iteratedPartial_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (a : Fin (Module.finrank ℝ E)) :
    eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P₀ a
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ 1 (Fin.cons a Fin.elim0) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The chart component lies in `W^{1,2}(Ω)`: `eigenvectorChartWeakPartial` is a
  -- genuine weak partial of it in every direction, and is itself `L²(Ω)`.
  have h_wp_isWeak : ∀ k : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P₀ k)
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        Ω :=
    fun k => eigenvectorChartWeakPartial_hasWeakPartialDeriv
      (I := I) (M := M) g r s h_atlas i α P₀ k
  have h_wp_memLp : ∀ k : Fin (Module.finrank ℝ E),
      MemLp (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s h_atlas i α P₀ k) 2 ((volume : Measure EuclN).restrict Ω) :=
    fun k => Lp.memLp (eigenvectorChartPartialLp (I := I) (M := M)
      g r s h_atlas i α P₀ k)
  have h_comp_memLp :
      MemLp (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P₀) 2 ((volume : Measure EuclN).restrict Ω) :=
    Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀)
  have h_comp_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀) Ω :=
    ⟨h_comp_memLp, fun k => ⟨_, h_wp_memLp k, h_wp_isWeak k⟩⟩
  -- The level-`1` mixed partial along `Fin.cons a Fin.elim0` is the chosen weak
  -- `a`-partial of the chart component; it is a genuine weak `a`-partial of it.
  have h_iter_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) a
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ 1 (Fin.cons a Fin.elim0))
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀) Ω := by
    rw [eigenvectorChartIteratedPartial_one_cons_elim0_eq]
    exact chosenWeakPartial'_isWeakPartial_of_mem h_comp_memW1p a
  -- Local integrability of both weak partials.
  have h_wp_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P₀ a)
      ((volume : Measure EuclN).restrict Ω) :=
    (h_wp_memLp a).locallyIntegrable (by norm_num)
  have h_iter_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ 1 (Fin.cons a Fin.elim0))
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartIteratedPartial_one_cons_elim0_eq]
    exact (chosenWeakPartial'_memLp_of_mem h_comp_memW1p a).locallyIntegrable
      (by norm_num)
  -- Uniqueness of weak partials identifies the two a.e.
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open
    (h_wp_isWeak a) h_iter_isWeak h_wp_loc h_iter_loc

namespace eigenvectorIteratedTensorChartBilinearData

/-- **The `m = 0` instance of `eigenvectorIteratedTensorChartBilinearData`.**

The level-`0` differentiated divergence-form datum for the eigenvector chart
component is the eigenvector chart variational identity itself, repackaged into
the standalone iterated shape. The effective `L²` source at level `0` is the
seven-term `eigenvectorChartRHS`. -/
def ofBase
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ 0 where
  directions := Fin.elim0
  fChartEff := eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀
  fChartEff_memLp_weighted :=
    eigenvectorChartRHS_memLp_weighted (I := I) (M := M) g r s h_atlas i α P₀
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_supp
    -- The level-0 eigenvector chart variational identity.
    have h_id := eigenvectorChartVariationalIdentity (I := I) (M := M)
      g r s h_atlas i α P₀ hψ_smooth hψ_cs hψ_supp
    -- Rewrite the LHS principal: at `m = 0` the level-`1` mixed partial along
    -- `Fin.cons a Fin.elim0` agrees a.e. with `eigenvectorChartWeakPartial a`.
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ 1 (Fin.cons a Fin.elim0) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ a y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      -- ae-equality of the candidate and chosen weak partials in every direction.
      have h_all_ae :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartWeakPartial (I := I) (M := M)
                g r s h_atlas i α P₀ a y =
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ 1 (Fin.cons a Fin.elim0) y := by
        rw [Filter.eventually_all]
        intro a
        exact eigenvectorChartWeakPartial_ae_eq_iteratedPartial_one
          (I := I) (M := M) g r s h_atlas i α P₀ a
      filter_upwards [h_all_ae] with y hy
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hy a]
    -- The LHS mass uses the `m = 0` mixed partial, definitionally the chart
    -- component `= tensorL2ChartComponent` coercion.
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ 0 Fin.elim0 y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
              α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y * ψ y
          ∂(volume : Measure EuclN) := rfl
    rw [h_principal_eq, h_mass_eq]
    exact h_id

end eigenvectorIteratedTensorChartBilinearData

/-! ## Chart-locality-free twins

The remainder of this file ships the chart-locality-free twins of the iterated
carrier structure and step, re-keyed onto the intrinsic-compactness eigenvector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`
via the committed chart-locality-free iterated partials
(`eigenvectorChartIteratedPartial_unconditional`), differentiated right-hand side
(`eigenvectorChartRHSDiff_unconditional`), and differentiated numerator
(`eigenvectorChartRHSDiffNumerator_unconditional`). Each twin carries no
chart-locality hypothesis: the index `i : TensorEigenIdx g r s` enters directly,
and the proof bodies transfer verbatim from the chart-locality-bearing
originals. -/

/-- **Chart-locality-free standalone iterated divergence-form datum for the
eigenvector chart component.** Chart-locality-free twin of
`eigenvectorIteratedTensorChartBilinearData`, re-keyed onto the
intrinsic-compactness eigenvector. The principal factor is the chart-locality-
free recursive `m`-fold mixed weak partial
`eigenvectorChartIteratedPartial_unconditional`. -/
structure eigenvectorIteratedTensorChartBilinearData_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) where
  /-- The `m`-direction multi-index. -/
  directions : Fin m → Fin (Module.finrank ℝ E)
  /-- The effective `L²` source at level `m`. -/
  fChartEff : EuclN → ℝ
  /-- The effective source is `MemLp 2` with respect to the chart-pulled weighted
  measure restricted to `chartTargetEuclid α`. -/
  fChartEff_memLp_weighted :
    MemLp fChartEff 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  /-- The level-`m` differentiated divergence-form variational identity, in the
  `c · fChartEff · ψ` form, with principal factor the chart-locality-free
  level-`(m+1)` mixed weak partial. -/
  m_diff_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α a b y *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m directions y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * fChartEff y * ψ y
        ∂(volume : Measure EuclN)

namespace eigenvectorIteratedTensorChartBilinearData_unconditional

/-- Hypothesis-bearing abstract constructor for
`eigenvectorIteratedTensorChartBilinearData_unconditional`. Chart-locality-free
twin of `eigenvectorIteratedTensorChartBilinearData.mk_from_hypotheses`. -/
def mk_from_hypotheses
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {i : TensorEigenIdx (I := I) (M := M) g r s}
    {α : M} {P₀ : TensorCompIdx (E := E) r s} {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (fChartEff : EuclN → ℝ)
    (fChartEff_memLp_weighted :
      MemLp fChartEff 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
    (m_diff_variational_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m directions y * ψ y
          ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * fChartEff y * ψ y
          ∂(volume : Measure EuclN)) :
    eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ m :=
  { directions := directions
    fChartEff := fChartEff
    fChartEff_memLp_weighted := fChartEff_memLp_weighted
    m_diff_variational_identity := m_diff_variational_identity }

end eigenvectorIteratedTensorChartBilinearData_unconditional

/-- **Chart-locality-free polymorphic regularity bridge for the eigenvector
iterated mixed partial.** Chart-locality-free twin of
`eigenvectorChartIteratedPartial_memWkp_of_memWkp`: from chart-`H^{k+m}` of the
chart-locality-free eigenvector chart component, every `m`-fold mixed weak
partial `eigenvectorChartIteratedPartial_unconditional g r s i α P₀ m dirs` lies
in chart-`H^k`. -/
theorem eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _dirs
      simpa [eigenvectorChartIteratedPartial_unconditional_zero] using h_parent
  | succ m ih =>
      intro k h_parent dirs
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      have h_inner :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (k + 1) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init dirs))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (k + 1) h_parent' (Fin.init dirs)
      have h_step := h_inner.chosenWeakPartial_mem (dirs (Fin.last m))
      rw [eigenvectorChartIteratedPartial_unconditional_succ]
      exact h_step

/-- **Chart-locality-free global `MemW1p 2` of the eigenvector iterated mixed weak
partial.** Chart-locality-free twin of
`eigenvectorChartIteratedPartial_memW1p_of_memWkp`. -/
theorem eigenvectorChartIteratedPartial_unconditional_memW1p_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  have h_memWkp_1 :=
    eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ m 1 h_parent' dirs
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_memWkp_1
  exact h_memWkp_1

/-- **Chart-locality-free per-pair polymorphic integration by parts for the
eigenvector iterated mixed partial.** Chart-locality-free twin of
`eigenvector_per_pair_ibp`. -/
theorem eigenvector_per_pair_ibp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (l : Fin (Module.finrank ℝ E)) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        φ y *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l 1) *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m dirs y *
          ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.snoc dirs l) y *
          ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  have h_v_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartIteratedPartial_unconditional_memW1p_of_memWkp
      (I := I) (M := M) g r s i α P₀ m h_parent dirs
  have h_w_eq :
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.snoc dirs l) =
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
    rw [eigenvectorChartIteratedPartial_unconditional_succ]
    have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs l
        (Fin.last m) = l := by simp
    have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
        dirs l) = dirs := by simp
    rw [h_last, h_init]
  have h_ibp :=
    generic_per_pair_ibp (I := I) (M := M) (α := α) h_v_memW1p hφ_chart
      hψ_smooth hψ_cs hψ_supp l
  rw [h_w_eq]
  exact h_ibp

/-- **Chart-locality-free five-layer differentiated numerator at the inductive
step.** Chart-locality-free twin of `eigenvectorChartIteratedStepNumerator`, with
the recursive mixed weak partials re-keyed onto
`eigenvectorChartIteratedPartial_unconditional`. -/
def eigenvectorChartIteratedStepNumerator_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN) : ℝ :=
  -- Layer A: (∂_b ∂_l a_ab) · ((m+1)-fold mixed partial, index `Fin.cons a dirs`).
  (∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b l) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a dirs) y)
  -- Layer B: (∂_l a_ab) · (∂_b of the (m+1)-fold mixed partial, `Fin.cons a dirs`).
  + (∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b l y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a dirs))
            (chartTargetEuclid (I := I) (M := M) α) y)
  -- Layer C: -(∂_l c) · (m-fold mixed partial, index `dirs`).
  - densityDerivOnEuclid (I := I) g α l y *
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs y
  -- Layer D: (∂_l c) · fChartEffPrev.
  + densityDerivOnEuclid (I := I) g α l y * fChartEffPrev y
  -- Layer E: c · (∂_l-weak-partial of fChartEffPrev).
  + densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y

/-- Chart-locality-free twin of
`eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator`. -/
theorem eigenvectorChartIteratedStepNumerator_unconditional_eq_rhsDiffNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStepNumerator_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l =
      eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev := by
  classical
  funext y
  have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs l
      (Fin.last m) = l := by simp
  have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
      dirs l) = dirs := by simp
  unfold eigenvectorChartIteratedStepNumerator_unconditional
    eigenvectorChartRHSDiffNumerator_unconditional
  rw [h_last, h_init]

/-- **Chart-locality-free effective chart-pulled `L²` source at the inductive
step.** Chart-locality-free twin of `eigenvectorChartIteratedStep`. -/
def eigenvectorChartIteratedStep_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Set.indicator (chartPouKernel (I := I) (M := M) α)
    (fun y => eigenvectorChartIteratedStepNumerator_unconditional
        (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y)

/-- Chart-locality-free twin of `eigenvectorChartIteratedStep_eq_rhsDiff_succ`. -/
theorem eigenvectorChartIteratedStep_unconditional_eq_rhsDiff_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs
        (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs) l =
      eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.snoc dirs l) := by
  classical
  rw [eigenvectorChartRHSDiff_unconditional_succ]
  unfold eigenvectorChartIteratedStep_unconditional
  have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
      dirs l) = dirs := by simp
  have h_num := eigenvectorChartIteratedStepNumerator_unconditional_eq_rhsDiffNumerator
    (I := I) (M := M) g r s i α P₀ m dirs
    (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m dirs) l
  rw [h_num, h_init]

/-- Chart-locality-free twin of
`eigenvectorChartIteratedStep_eq_zero_off_chartPouKernel`. -/
theorem eigenvectorChartIteratedStep_unconditional_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l y = 0 := by
  rw [eigenvectorChartIteratedStep_unconditional, Set.indicator_of_notMem hy]

/-- Chart-locality-free twin of
`eigenvectorChartIteratedStep_support_subset_chartPouKernel`. -/
theorem eigenvectorChartIteratedStep_unconditional_support_subset_chartPouKernel
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {i : TensorEigenIdx (I := I) (M := M) g r s}
    {α : M} {P₀ : TensorCompIdx (E := E) r s} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    {fChartEffPrev : EuclN → ℝ}
    {l : Fin (Module.finrank ℝ E)} :
    Function.support
        (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs fChartEffPrev l) ⊆
      chartPouKernel (I := I) (M := M) α := by
  unfold eigenvectorChartIteratedStep_unconditional
  exact Set.support_indicator_subset

/-- **Chart-locality-free weighted-`L²` regularity of the standalone-step
effective source, unconditional.** Chart-locality-free twin of
`eigenvectorChartIteratedStep_memLp_two_weighted`. -/
theorem eigenvectorChartIteratedStep_unconditional_memLp_two_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemLp fChartEffPrev 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_num : MemLp (fun y => eigenvectorChartRHSDiffNumerator_unconditional
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l)
      fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict K) :=
    eigenvectorChartRHSDiffNumerator_unconditional_memLp_volume_compact
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l) h_prev
  have h_div : MemLp (fun y => eigenvectorChartIteratedStepNumerator_unconditional
      (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y) 2
      ((volume : Measure EuclN).restrict K) := by
    have h_eq : (fun y => eigenvectorChartIteratedStepNumerator_unconditional
        (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l y /
        densityOnEuclid (I := I) g α y) =
        fun y => (1 / densityOnEuclid (I := I) g α y) *
          eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev y := by
      funext y
      rw [eigenvectorChartIteratedStepNumerator_unconditional_eq_rhsDiffNumerator]
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [h_eq]
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (one_div_densityOnEuclid_contDiffOn_chartTarget (I := I) (M := M) g α)
      hK_compact hK_meas hK_in h_num
  have h_plain : MemLp (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
      g r s i α P₀ m dirs fChartEffPrev l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [eigenvectorChartIteratedStep_unconditional, memLp_indicator_iff_restrict hK_meas]
    have h_double : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_double]
    exact h_div
  refine memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α hK_compact hK_meas hK_in
    (Filter.Eventually.of_forall (fun y hy =>
      eigenvectorChartIteratedStep_unconditional_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l hy))
    h_plain

/-- Chart-locality-free twin of
`eigenvectorChartIteratedPartial_one_cons_elim0_eq`. -/
private lemma eigenvectorChartIteratedPartial_unconditional_one_cons_elim0_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (a : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ 1 (Fin.cons a Fin.elim0) =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
  rw [eigenvectorChartIteratedPartial_unconditional_succ,
    eigenvectorChartIteratedPartial_unconditional_zero]
  rfl

/-- Chart-locality-free twin of
`eigenvectorChartWeakPartial_ae_eq_iteratedPartial_one`: the chart-locality-free
candidate weak chart partial `eigenvectorChartWeakPartial_unconditional` agrees
a.e. on the chart target with the chart-locality-free level-`1` mixed weak
partial along `Fin.cons a Fin.elim0`. -/
private lemma eigenvectorChartWeakPartial_ae_eq_iteratedPartial_unconditional_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (a : Fin (Module.finrank ℝ E)) :
    eigenvectorChartWeakPartial_unconditional (I := I) (M := M) g r s i α P₀ a
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ 1 (Fin.cons a Fin.elim0) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The chart component lies in `W^{1,2}(Ω)`: `eigenvectorChartWeakPartial_unconditional`
  -- is a genuine weak partial of it in every direction, and is itself `L²(Ω)`.
  have h_wp_isWeak : ∀ k : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P₀ k)
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i α P₀)
        Ω :=
    fun k => eigenvectorChartWeakPartial_hasWeakPartialDeriv_unconditional
      (I := I) (M := M) g r s i α P₀ k
  have h_wp_memLp : ∀ k : Fin (Module.finrank ℝ E),
      MemLp (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P₀ k) 2 ((volume : Measure EuclN).restrict Ω) :=
    fun k => Lp.memLp (eigenvectorChartPartialLp_unconditional (I := I) (M := M)
      g r s i α P₀ k)
  have h_comp_memLp :
      MemLp (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i α P₀) 2 ((volume : Measure EuclN).restrict Ω) :=
    eigenvectorChartComponentFun_ofCompact_memLp_volume
      (I := I) (M := M) g r s i α P₀
  have h_comp_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i α P₀) Ω :=
    ⟨h_comp_memLp, fun k => ⟨_, h_wp_memLp k, h_wp_isWeak k⟩⟩
  have h_iter_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) a
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ 1 (Fin.cons a Fin.elim0))
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i α P₀) Ω := by
    rw [eigenvectorChartIteratedPartial_unconditional_one_cons_elim0_eq]
    exact chosenWeakPartial'_isWeakPartial_of_mem h_comp_memW1p a
  have h_wp_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P₀ a)
      ((volume : Measure EuclN).restrict Ω) :=
    (h_wp_memLp a).locallyIntegrable (by norm_num)
  have h_iter_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ 1 (Fin.cons a Fin.elim0))
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartIteratedPartial_unconditional_one_cons_elim0_eq]
    exact (chosenWeakPartial'_memLp_of_mem h_comp_memW1p a).locallyIntegrable
      (by norm_num)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open
    (h_wp_isWeak a) h_iter_isWeak h_wp_loc h_iter_loc

namespace eigenvectorIteratedTensorChartBilinearData_unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The `m = 0` instance of
`eigenvectorIteratedTensorChartBilinearData_unconditional`.**
Chart-locality-free twin of `eigenvectorIteratedTensorChartBilinearData.ofBase`.
The effective `L²` source at level `0` is the chart-locality-free seven-term
`eigenvectorChartRHS_unconditional`. -/
def ofBase
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ 0 where
  directions := Fin.elim0
  fChartEff := eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀
  fChartEff_memLp_weighted :=
    eigenvectorChartRHS_memLp_weighted_unconditional (I := I) (M := M)
      g r s i α P₀
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_supp
    have h_id := eigenvectorChartVariationalIdentity_unconditional (I := I) (M := M)
      g r s i α P₀ hψ_smooth hψ_cs hψ_supp
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ 1 (Fin.cons a Fin.elim0) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ a y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_all_ae :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
                g r s i α P₀ a y =
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ 1 (Fin.cons a Fin.elim0) y := by
        rw [Filter.eventually_all]
        intro a
        exact eigenvectorChartWeakPartial_ae_eq_iteratedPartial_unconditional_one
          (I := I) (M := M) g r s i α P₀ a
      filter_upwards [h_all_ae] with y hy
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hy a]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ 0 Fin.elim0 y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i)
              α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y * ψ y
          ∂(volume : Measure EuclN) := rfl
    rw [h_principal_eq, h_mass_eq]
    exact h_id

end eigenvectorIteratedTensorChartBilinearData_unconditional

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The standalone iterated divergence-form datum is a `Type`. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : Type _ :=
  eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
    g r s h_atlas i α P₀ m

/-- The `m = 0` instance produces a level-0 datum. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ 0 :=
  eigenvectorIteratedTensorChartBilinearData.ofBase
    (I := I) (M := M) g r s h_atlas i α P₀

/-- The standalone-step effective source coincides definitionally with the
level-`(m+1)` differentiated right-hand side at the snoc-extended index. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs
        (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs) l =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.snoc dirs l) :=
  eigenvectorChartIteratedStep_eq_rhsDiff_succ
    (I := I) (M := M) g r s h_atlas i α P₀ m dirs l

/-- The chart-locality-free standalone iterated divergence-form datum is a `Type`. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : Type _ :=
  eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
    g r s i α P₀ m

/-- The chart-locality-free `m = 0` instance produces a level-0 datum. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ 0 :=
  eigenvectorIteratedTensorChartBilinearData_unconditional.ofBase
    (I := I) (M := M) g r s i α P₀

/-- The chart-locality-free standalone-step effective source coincides
definitionally with the chart-locality-free level-`(m+1)` differentiated
right-hand side at the snoc-extended index. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs
        (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs) l =
      eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.snoc dirs l) :=
  eigenvectorChartIteratedStep_unconditional_eq_rhsDiff_succ
    (I := I) (M := M) g r s i α P₀ m dirs l

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
