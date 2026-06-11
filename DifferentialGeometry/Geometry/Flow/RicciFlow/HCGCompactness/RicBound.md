# RicBound.lean — THE `ric_bound` endpoint (MSM135 Lemma 3.11, Step 4 (A_N))

## Status (2026-06-10): STATED, verified to elaborate; proof = ONE precise `sorry`

`theorem ric_bound` is the intrinsic (A_N) endpoint, stated per the user's
"state ric_bound first" directive.  Focused check passes (single expected
`sorry` warning).

## Statement design (load-bearing choices)

- **Conclusion** matches the `MetricCovOrderEvolutionInput.ric_bound` field
  (AllTimesBounds.lean:4365) verbatim in shape, with the abstract `nablaRic`
  data REALIZED by the genuine geometric object
  `ricCovTower g gRef s := iterCov gRef 2 (ricciSection (LC g) …) s`
  (defined in this file): `√(normSq0S gRef x (2+N) (ricCovTower (gSeq i t) gRef N x))
  ≤ Cpp · metricCovDerivNorm N (gSeq i t) gRef x + Cppp`.
  NOTE the arity is `2 + N` (iterCov-native), not `N + 2` (the Grönwall field's
  `p + 2`); the consumption adapter will need a slot-arity cast/reindex
  (norm-invariant).
- **Hypotheses** are the honest stage-`N` inputs of the book's induction:
  `hKc : IsCompact K` (the frame-covering/uniformization needs it),
  `hequiv` = eq (3.3) (`MetricUniformEquivalentOnWindow`),
  `hBprev` = (B_r) for `1 ≤ r < N` (`MetricCovDerivOrderBoundOnWindow`),
  `hShi` = moving-metric Shi bounds on the Ricci towers up to order `N`
  (`ricCovTower (gSeq i t) (gSeq i t) s`, moving norm).  (A_r) for `r < N` is
  NOT needed (the book uses it only to produce (B_r)).
- Namespace/variables mirror AllTimesBounds' FixedDomain section (no
  `I.Boundaryless`, no extra IsManifold instances — instances derived in
  bodies where needed, as in `metricCovDeriv`).

## Discharge chain (what the `sorry` stands for)

Component core PROVEN in RicBoundClaims.lean (all sorry-free, checked):
`claim1_LC` → `hDlow` + the pointwise top factor; `claim2_component` → `hmix`;
`mixed_descent` → `|∇_H^N T| ≤ C(1+|∇_{H,U}^{N-1}D|)` pointwise per frame
domain.  Remaining assembly bricks:
1. smooth local-frame covering of compact `K` + per-domain frame constants;
2. component ↔ intrinsic bridge (`iterCovComp_eq_iterCov` +
   `normSq0S_identity_eq_sum_sq` at a `gRef`-ON frame — Parseval EXISTS at
   `Tensor0SRiemannian/Comparison.lean:220` — or bounded-gram equivalence);
3. moving ↔ fixed norm conversion of the Shi inputs through `hequiv`;
4. Ricci-component identification (`iterCovComp_eq_iterCov` at
   `ricciSection`), giving the `hT` smoothness and the tower match;
5. instantiate `mixed_descent` + `claim1_LC` per domain, take maxima over the
   finite cover.

The missing-API frontier list: a smooth `gRef`-orthonormal local-frame
producer (Gram–Schmidt on a trivialization; pointwise `OrthonormalBasisAt`
exists but carries no smoothness), and the slot-arity reindex adapter
`2 + N ↔ N + 2` for the Grönwall consumption.

## Why this file (and not RicBoundClaims/AllTimesBounds)

Final assembly above all producers: AllTimesBounds is the (huge) predicate +
Grönwall skeleton, RicBoundClaims is the component engine; this file imports
the former for vocabulary and will import the latter when the discharge
begins.  Keeping the endpoint in its own small file avoids coupling the
engine layer to the 4.7k-line skeleton.
