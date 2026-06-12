# MetricPreconv — MSM135 Corollary lbl351 (metrics with bounded derivatives preconverge)

**Status: Brick A1 IMPLEMENTED + read-only verified (2026-06-11).**

## Brick A1 DONE — `fderiv_comp_le_tower` (MetricPreconv.lean)

The order-1 covariant→coordinate conversion is proved sorry-free.  File
`HCGCompactness/MetricPreconv.lean` exports (all public, reused by A2/B):

- `fderiv_comp_le_tower` — the endpoint.  `‖fderiv (chart rep of s_p^V)‖ ≤
  CV·(Cp1+Cp)` on an inner compact `Kc ⊆ chart source`, with `CV` collecting
  gRef/chart/slot/basis data only (A0-independent — so k-independent on a metric
  SEQUENCE; the load-bearing quantifier discipline `∃CV … ∀y∀Cp,Cp1`).
- `opNorm_le_sum_coord` — generic finite-dim `‖L‖ ≤ Σ‖coordᵢ‖·|L(bEᵢ)|`.
- `exists_ON_tangentBasis` — general-dim gRef-orthonormal tangent basis at a
  point (repackages `exists_trivONBasis` via `IsLocalFrameOn.toBasisAt`).
- `exists_section_eqOn_compact` — bump-globalizes `tangentConstInChart x₀ v` to a
  genuine `ContMDiffSection` agreeing on `Kc`.
- `exists_sqrtInner_bound` / `exists_family_bound` — compact sup of the
  gRef-norm of a (family of) smooth section(s).

### Route as implemented (one simplification vs the plan)

Plan's per-slot product bookkeeping was replaced by a **uniform bound `D`**: one
constant bounding `√gRef(s·,s·)` on `Kc` for every direction `σ i`, slot `V a`,
and correction `W i a = ∇_{σ i}(V a)`.  Then each Cauchy–Schwarz slot product is
`≤ D^(p+3)` / `≤ D^(p+2)`, so `|fderiv·(bEᵢ)| ≤ Cp1·D^(p+3)+(p+2)·Cp·D^(p+2)`,
and `opNorm_le_sum_coord` + `CV := max(Ccoord·D^(p+3), Ccoord·(p+2)·D^(p+2))`
closes it.  Crude constant, but k-independent and far less bookkeeping.

Otherwise as scouted: chart bridge `extDerivFun_tangentConstInChart_eq_fderiv`
(per-direction), step decomposition `covDerivOfField_succ` +
`metricCovDerivStep_apply` + `totalNabla0SFun_apply_section` +
`nabla0SFun_eval_smooth_slots` (no `Fin.cons` `hv`/`hupd` needed — the cons is
formed directly), CS `abs_apply_le_sqrt_normSq0S`.

### Lean gotchas hit (record for A2/B)

- `metricInner_mdiffAt` and `cotangentCov_pairing_contMDiff` carry an
  `[InnerProductSpace ℝ E]` section var the HCG block lacks → **inline** the
  `g.contMDiff` + `ContMDiff.clm_bundle_apply` (×2) + `contMDiffAt_section`
  chain instead (no inner product needed; that var is unused in their proofs).
- Bump `exists_contMDiffMap_one_nhds_of_subset_interior` wants `n : ℕ∞`; pass
  `(⊤ : ℕ∞)` so `χ.contMDiff` lands at `(∞ : WithTop ℕ∞)` matching the section.
- `NormalSpace M` is not directly inferred: add
  `LocallyCompactSpace H := I.locallyCompactSpace`,
  `LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M`, then
  `NormalSpace M := inferInstance` (PouThickening pattern).
- `abs_add` → `abs_add_le`.
- `Fin.cons x f a` inside `gRef.inner y (…)` cannot infer its motive → ascribe
  `(Fin.cons … : Fin (p+3) → TangentSpace I y)`.
- `Finset.prod_le_prod` cannot infer the upper-bound function `g` under
  `le_trans` → pass `(g := fun _ => D)` and finish with `le_of_eq`.
- `Function.update_of_ne` (not `update_noteq`); `Function.update_self`.

**Status: PLAN below (the rest, Bricks A2/B/C/D, 2026-06-11). Brick A1 done.**

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

## Design decision: Euclidean engine vs equicontinuity-only (2026-06-11)

Considered and REJECTED: skipping the iteratedFDeriv conversion by proving
manifold-level equicontinuity directly (directional-derivative bounds from the
step decomposition + CS lemma give C¹ bounds per order; "C¹ bound ⇒ Lipschitz
on compacts" needs only one chart/MVT lemma) and using the scalar AA per order
+ diagonal.  REJECTED because the limit's smoothness and the
derivative↔limit interchange (`L_p = ∇ᵖ(g∞)`) would then have to be proved by
hand on the manifold tower — strictly worse than the iteratedFDeriv
conversion, which is finite-dimensional scalar calculus and after which
`exists_cInf_subseq` delivers the smooth limit + all interchanges for free.
Stick with Brick A as planned.

Brick A progress: first lemma DONE (commit e4e8db5a) —
`Tensor0SBundle.abs_apply_le_sqrt_normSq0S` (Comparison.lean): pointwise
tensor Cauchy–Schwarz `|T(v)| ≤ √normSq0S(T)·∏√g(vₐ,vₐ)` at a g-ON basis.
Proof pattern: `T.map_sum` + `T.map_smul_univ` basis expansion, discrete CS
`Finset.sum_mul_sq_le_sq_mul_sq`, slot Parseval (simp with `map_sum, map_smul,
ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_apply, hON` + `sum_comm`
+ `sum_ite_eq`), `Finset.prod_univ_sum`, private `sqrt_prod`.

## Brick A base bridges (located, 2026-06-11)

- `extDerivFun_real_eq_mfderiv` (Bundle/PartialMfderiv/FixedBase.lean:22) and
  `extDerivFun_eq_fderiv` (FixedBase.lean:199, the chart-fderiv form used by
  the swap constructors) — the scalar directional-derivative ↔ chart-partial
  bridges for the conversion induction.
- Step decomposition: `totalNabla0SFun_apply_section` +
  `nabla0SFun_eval_smooth_slots` (the P2 tower-regularity pattern in
  `MetricCovDerivTimeDeriv.lean`).
- C⁰ input: `abs_apply_le_sqrt_normSq0S` (Comparison.lean, e4e8db5a).
- Euclidean endgame: `exists_cInf_subseq` (MapConvergence.lean).

NEXT concrete step: create `MetricPreconv.lean`; first theorem = the
order-1 conversion (chart-partials of the component scalars bounded by
`(B_{p+1})`, `(B_p)` + chart-frame data via the step decomposition + CS),
then the iteratedFDeriv induction.

Order-1 route in detail:
- THE pointwise bridge is `extDerivFun_tangentConstInChart_eq_fderiv`
  (FixedBase.lean:69): for EVERY `p` in the chart source (not only the
  center), `fderiv ℝ (writtenInExtChartAt I 𝓘 x₀ f) (extChartAt x₀ p) v =
  extDerivFun f p (tangentConstInChart x₀ v p)`.
- So `‖fderiv F z‖ ≤ sup over a basis of v's` of `|extDerivFun (s_p^V)
  along the chart-constant field|`, and the step decomposition + the CS
  lemma bound that by `(B_{p+1})`/`(B_p)` times `gRef`-norms of the slot
  fields and the chart-constant direction field on the compact — finite
  sup of continuous functions.
- ⚠ SLOT GLOBALIZATION: the step decomposition (`nabla0SFun_eval_smooth_slots`)
  takes GLOBAL `ContMDiffSection` slots, but `tangentConstInChart` fields are
  only chart-smooth.  Globalize by bump-truncation (the
  `SmoothSectionsLocal.lean` bump pattern: `SmoothBumpFunction` supported in
  the chart, = 1 on the inner compact); on the inner set the truncated
  section agrees with the chart-constant field, and `extDerivFun` only
  depends on the germ (`extDerivFun_congr_nhds`).
- Higher orders: iterate `fderiv` of the chart representative; each step
  re-enters the same family `s_q` at slot tuples extended by bump-globalized
  chart-constant fields and Christoffel-update fields — the bound constants
  pick up sup-norms of those fields' derivatives on the inner compact
  (finite, gRef/chart data only, k-independent ✓).

## Open design questions

- Whether to add an `On`-version of `exists_cInf_subseq` vs bump-extension
  (bump route keeps the other session's file untouched — preferred while
  they are active in MapConvergence.lean's neighborhood).
- The limit's global assembly: chart-local C^∞ limits glue by uniqueness of
  limits (overlaps agree pointwise); the global smooth metric is built chart
  by chart — check whether `SmoothRiemannianMetric` has a local-construction
  constructor or whether to build the `(0,2)`-field first and add
  positivity/symmetry.
