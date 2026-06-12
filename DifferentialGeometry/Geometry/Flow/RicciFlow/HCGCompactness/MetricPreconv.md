# MetricPreconv — MSM135 Corollary lbl351 (metrics with bounded derivatives preconverge)

**Status: PLAN (2026-06-11). Nothing implemented yet.**

## Where this sits

P3 of the Lemma 3.11/Theorem 3.10 chain (and a SHARED engine: the Ch4
Thm 3.9 (`metricCompactness`) proof cites the same corollary).  Book source:
MSM135 ch3, Corollary `lbl351` (proof sketch at lines ~788-813 of
`RicciFlow/RicciFlowBooksLatex/MSM135/tex/chapters/chapter3.tex`), consumed by
the Thm 3.10 assembly (`lbl352` subsection).

## Statement (target form, C^∞/global version — what both consumers want)

```
theorem metricPreconvInf
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ α : ℕ, ∀ K, IsCompact K → ∃ C, ∀ k,
      MetricCovDerivOrderBoundOn (I := I) K α (gSeq k) gRef C)
    (hlow : ∀ K, IsCompact K → ∃ δ > 0, ∀ k, ∀ x ∈ K, ∀ v,
      δ * gRef.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      MetricCInfConvOnCompacts (I := I) (fun k => gSeq (φ k)) gInf gRef
```

(The per-`p`, per-`K` book statement lbl351 is the engine inside; the
diagonal over a countable chart cover + orders gives the global C^∞ form,
which is what `MetricCInfConvData` / the 3.10 assembly and Thm 3.9 need.
The lower bound makes the limit positive-definite.)

## Deviation from the book recorded (3.10 application)

The book gets SPACETIME C^∞ convergence by applying lbl351 to `g∞ + dt²` on
`M × (α,ω)` — which needs the FULL mixed `(p,q)` bounds of Lemma 3.11
(lbl341, q ≥ 1, via the curvature evolution equation).  The project's
consumer (`SourceMetricCPConvOnWindow`, PointedConvergence.lean:777) only
requires SPATIAL C^p sup-norms uniformly in t — so P3 takes the lighter
route: per-t spatial preconvergence (this file) + time-equicontinuity from
the q = 1 bound only (`∂ₜ∇ᵖg = -2∇ᵖRc`, bounded by `ric_bound` + (B_r) —
all P2 machinery, NO curvature-evolution recursion needed).  The q ≥ 1
mixed bounds of lbl341 are NOT formalized (not consumed).

## Proof route (per book sketch + project reuse)

1. **Componentize** on a countable atlas: in a chart, the scalar components
   `(g_k)_{bc}(y)` (coordinate frame / `extChartAt`-pullback to an open ball
   of ℝⁿ).
2. **Covariant→coordinate derivative conversion** (the genuinely new layer):
   `∇^α_gRef`-bounds (α ≤ A) ⇒ chart-component `iteratedFDeriv` bounds
   (orders ≤ A) on compact sub-balls.  Induction:
   `∂(comp) = ∇-comp + Γ·comp` (book lbl345-form); gRef's Christoffel +
   derivatives bounded on compacts (smooth fixed background).  REUSE
   candidates: `AkMFold.iterCovCompU` / `covDerivStepCompU` (component
   covariant tower = ∂-step − chr-corrections; invert the recursion),
   `Claim1Wiring` producers (lcChrist_e_mdiffOn etc.),
   `Geometry/Coordinates/NablaComponents/`.
3. **Euclidean engine**: bump-extend the components from a compact sub-ball
   to all of ℝⁿ and feed `exists_cInf_subseq` (MapConvergence.lean — the
   other session's sorry-free AA-diagonal engine; E := ℝⁿ, F := ℝ); OR add
   an On-version of the engine.  Output: subsequence + C^∞ limit components
   + C^∞_loc convergence per chart.
4. **Diagonal** over (countable charts) × (n² components) → one subsequence;
   reassemble the limit tensor field; positive-definiteness from `hlow`;
   smoothness of the limit from the engine's `ContDiff ⊤` output.
5. **Norm bridge**: chart-component C^p convergence ⇒ the project's
   `metricDerivNorm`-form `MetricCPConvOn` (the two-sided component↔normSq0S
   bounds of `RicBoundGoodFrame` / `Comparison.lean` — already built for
   ric_bound — convert sup-component differences to `normSq0S` differences
   of `metricDiffCovDerivAt`; this also needs the covariant tower of the
   DIFFERENCE, i.e. linearity `covDerivOfField` of `g_k − g∞`:
   `metricCovDeriv` is linear in the field (`MetricCovDerivLinear`)).

## Brick order

- **Brick A** (conversion layer, step 2): coordinate-partial bounds from
  covariant bounds.  Self-contained; sizeable.
- **Brick B** (steps 3-4): chart-local extraction + diagonal; mostly plumbing
  around `exists_cInf_subseq` + the scalar AA file.
- **Brick C** (step 5): norm-form bridge back to `MetricCPConvOn`.
- **Brick D** (time direction, separate file): window-uniform upgrade via
  q = 1 equicontinuity (consumes P2's `hevComp_of_solutions` + `ric_bound`).

## Brick A refined design (scouted 2026-06-11)

The single-step coordinate↔covariant bridge exists but only at chart CENTERS
(`covariantDerivative_modelInChart_center_eq_fderiv_plus_connection`,
`Geometry/Coordinates/NablaComponents/Tensor0S.lean:185`) — not directly
iterable over a ball.  The iterable decomposition is instead the one ALREADY
USED by the P2 tower-regularity inductions
(`MetricCovDerivTimeDeriv.lean`, `covDerivOfField_eval_smoothAt`):

  `extDerivFun (s_p^{V-tail}) (V 0) = s_{p+1}^V + Σ_a s_p^{update_a V}`
  (from `totalNabla0SFun_apply_section` + `nabla0SFun_eval_smooth_slots`),

where `s_p^V(y) := (covDerivOfField gRef A0 p) y (V·y)` and the updated slots
insert `∇_{V0}(V a)` (smooth sections; for coordinate-frame slots these are
Christoffel combinations of the FIXED gRef — bounded with all derivatives on
compacts).  So the directional derivative of the level-p scalar along any
smooth field is (level-(p+1) scalar) − (level-p scalars at modified tuples).

Induction invariant for Brick A: P(m): for every p and every slot tuple from
a fixed finite family closed under the Christoffel updates, the m-th chart
`iteratedFDeriv` of `s_p` is bounded by C⁰ bounds of `{s_q : q ≤ p + m}` at
(finitely many) tuples + chart-frame/Christoffel data.  Then `hbdd` at orders
≤ A gives chart-component `iteratedFDeriv` bounds at orders ≤ A.
Technical care: closing the slot-tuple family under updates (the update
inserts `∇_{V0} V_a`, not a coordinate frame element — either prove tuples
stay in the span with bounded coefficients (multilinearity expands them), or
phrase P(m) for ALL ∞-section tuples with bounds depending on the tuples'
own C^m data on K — the latter is cleaner: the bound constant is a function
of `sup_K ‖iteratedFDeriv^{≤m}(slot coords)‖`).

C⁰ bounds of `s_q` from `hbdd`: `|s_q(y)| ≤ ‖∇^q g_k‖_{gRef}(y) · Π‖V_a‖` —
Cauchy-Schwarz for `normSq0S` against slot vectors (exists in the
Tensor0SRiemannian layer / `Comparison.lean` two-sided machinery).

## Open design questions

- Whether to add an `On`-version of `exists_cInf_subseq` vs bump-extension
  (bump route keeps the other session's file untouched — preferred while
  they are active in MapConvergence.lean's neighborhood).
- The limit's global assembly: chart-local C^∞ limits glue by uniqueness of
  limits (overlaps agree pointwise); the global smooth metric is built chart
  by chart — check whether `SmoothRiemannianMetric` has a local-construction
  constructor or whether to build the `(0,2)`-field first and add
  positivity/symmetry.
