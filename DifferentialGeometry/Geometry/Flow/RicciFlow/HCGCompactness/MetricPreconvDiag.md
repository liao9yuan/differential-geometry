# MetricPreconvDiag.lean — P3 Brick C-I (countable diagonal + global limit)

**Status (2026-06-12): C0 DONE + verified (focused check + targeted build green,
`#print axioms` clean = `[propext, Classical.choice, Quot.sound]`).  C1a/C1b
STOPPED and reported to the planner — the `gInf : SmoothRiemannianMetric`
packaging needs a foundational bridge that does not exist (see below).**

## C0 — `exists_diag_subseq` (DONE)

The abstract countable common-subsequence diagonal, proved exactly as the planner
fixed it:

```
exists_diag_subseq
  (P : ℕ → (ℕ → ℕ) → Prop)
  (hstep   : ∀ n φ, StrictMono φ → ∃ ψ, StrictMono ψ ∧ P n (φ ∘ ψ))
  (hsub    : ∀ n φ ψ, StrictMono ψ → P n φ → P n (φ ∘ ψ))
  (hextend : ∀ n φ m, P n (fun k => φ (k + m)) → P n φ) :
  ∃ φ, StrictMono φ ∧ ∀ n, P n φ
```

Construction (as the planner specified): nested extractors carried with their
strict-monotonicity proofs in a subtype `{φ // StrictMono φ}` (`Nat.rec`),
`G 0 = id`, `G (n+1) = G n ∘ ρ n` with `ρ n := (hstep n (G n) _).choose`; diagonal
`φ n := G (n+1) n`.  For each `n` the `n`-tail `fun m => φ (n+m)` equals
`G (n+1) ∘ τ` with `τ m := Q m (n+m)`, where `Q` is the partial composition of the
`ρ`'s past step `n+1` (`Q 0 = id`, `Q (m+1) = Q m ∘ ρ (n+1+m)`); `hGcomp :
G (n+1+m) = G (n+1) ∘ Q m` (induction).  `hsub` gives `P n` on the tail, `hextend`
lifts to all of `φ`.

Verified usable for the eventual C1b instantiation with `MapCInfConvOnCompacts`:
`hstep := exists_chart_cInfConv` (its `(B_r)` bound `∀k …` restricts to any
subsequence `∀k, … (φ k)`), `hsub := MapCInfConvOnCompacts.comp_subseq`, `hextend`
= the asymptotic `∃ k₀` shape of `MapCPConvOn`.

### Lean gotchas (C0)
- The recursion equations `G (n+1) = G n ∘ ρ n` and `Q (m+1) = Q m ∘ ρ (n+1+m)`
  are `rfl`; `rw` with them often auto-closes via its trailing `rfl` (drop the
  explicit `rfl`), EXCEPT the final comp-associativity `(f∘g)∘h = f∘(g∘h)` which
  is defeq but NOT syntactic after `rw` — needs an explicit trailing `rfl`.
- `StrictMono.le_apply : n ≤ f n` (implicit `n`) is the `ℕ→ℕ` ≥-id lemma;
  `strictMono_nat_of_lt_succ` builds `StrictMono` from `f n < f (n+1)`.
- `n + 1 + (j + 1)` is defeq `(n + 1 + j) + 1` (Nat succ), so the `Gf`-step at the
  shifted index closes by `show … ; rfl`-style without a `ring` rewrite.

## C1a / C1b — STOPPED, planner decision required

### What was checked FIRST (per the prompt)

`SmoothRiemannianMetric I M = Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`
(`Geometry/Metric/Basic.lean`).  The Mathlib constructor
(`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:244`) has FIVE fields:
1. `inner (b : M) : T_b M →L[ℝ] T_b M →L[ℝ] ℝ` — the **intrinsic** fibrewise
   bilinear form (a CLM), NOT chart-component scalars;
2. `symm`, 3. `pos`, 4. `isVonNBounded (b) : IsVonNBounded ℝ {v | inner b v v < 1}`;
5. `contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L F →L ℝ)) ∞ (fun b => TotalSpace.mk'
   … (inner b))` — smoothness of the metric as a section of the **bilinear-forms
   bundle**.

### Why C1b is blocked (the foundational gap)

The Brick-B engine delivers limits as **chart-coordinate scalar functions**
`Φinf : E → ℝ` (one per chart × component), `ContDiff ⊤`.  Packaging them into
`gInf : SmoothRiemannianMetric` requires the **inverse of the entire `componentize`
layer**: reconstruct an intrinsic, globally smooth `(0,2)` field (fields 1 + 5)
from a chart-compatible family of `ContDiff` component functions, with overlap
consistency.  This bridge DOES NOT EXIST in the project:
- No constructor `Tensor0SField`/`SmoothRiemannianMetric` from real component
  functions (grep: only the forward `metricTensorField`).
- The project explicitly documents the general gate as unavailable:
  `Analysis/Spectral/.../DeTurck/NonlinearitySpectral.lean:53` —
  "`TensorL2 → SmoothRiemannianMetric` — *the gate, NOT available*".
- The ONLY metric-realization that exists,
  `TensorHsRealize.exists_smooth_metric_of_smooth_tensor_small`, builds `g + h`
  from a **`SmoothCcTensor`** (intrinsic, compactly-supported, `gFibreOpBound`
  fibre-small, `δ' < 1`).  It is inapplicable here twice over: (i) it consumes an
  intrinsic smooth section, not chart components — so it still needs the inverse-
  componentize bridge to even produce its input; (ii) it is a small/compactly-
  supported PERTURBATION of a fixed `g`, whereas `gInf` is a GLOBAL `C^∞` limit
  that need not be a `C⁰`-small perturbation of `gRef`.

Building the inverse-componentize / "smooth intrinsic metric from chart-compatible
component family" layer is a multi-lemma foundational addition (local-frame
coefficient smoothness `contMDiffOn_iff_localFrame_coeff` for the bilinear-forms
bundle + overlap gluing + `isVonNBounded`/`pos` from the lower bound).  The
planner's own Brick-B note flags Frontier 2 (σ-compact atlas, = C1a) and the
limit-object (C1b) as "one design unit," and the planner ruling reserved that
unit for Brick C-I.  Per the prompt's explicit instruction ("if the
SmoothRiemannianMetric packaging needs new foundational structure, STOP and
report — a planner decision, not yours"), C1a/C1b are NOT built in a vacuum.

### Building blocks located for the planner (when C1b is unblocked)
- Atlas (C1a): `compactCovering X : ℕ → Set X` + `isCompact_compactCovering`,
  `iUnion_compactCovering`, `exists_mem_compactCovering`
  (`Mathlib/Topology/Compactness/SigmaCompact.lean`); combine with per-compact
  finite chart subcovers (manifold local compactness) → countable
  (chart, inner-compact) family covering `M`.
- Per-item extractor (hstep for C0): `exists_chart_cInfConv` (MetricPreconv.lean).
- Diagonal: `exists_diag_subseq` (this file, DONE).
- Closest-but-insufficient realization gate:
  `TensorHsRealize.exists_smooth_metric_of_smooth_tensor_small`.

### Options for the planner
1. Build the inverse-componentize bridge ("smooth intrinsic `(0,2)` field /
   `SmoothRiemannianMetric` from a chart-compatible family of `ContDiff`
   components") as a dedicated foundational brick, then resume C1a/C1b.
2. Reformulate the P3 limit object to carry the limit as **chart-component data +
   intrinsic pointwise limit** (avoiding the smooth-metric packaging) if a
   downstream consumer can accept that — but `metricPreconvInf` / the P4
   `SourceDomainMetricData.limitMetric` both require a `SmoothRiemannianMetric`,
   so this likely needs a consumer-side change too.
3. Supply `gInf` as a hypothesis to the P3 endpoint (as Brick D's `windowPreconv`
   already does with its `gInf` argument), deferring the construction.
