# RicBound.lean — THE `ric_bound` endpoint (MSM135 Lemma 3.11, Step 4 (A_N))

## ⚡ ASSEMBLY DESIGN (2026-06-11, ACTIVE — the /goal "finish ric_bound" run)

**Uniformization wave DONE (commit af9eeb83, all green):** claim1_abstract/claim1
(AkMFold), claim1_LC/claim2_component/mixed_descent/aN_component (RicBoundClaims)
are now CONSTANTS-FIRST (∃C before the varying field data: metric, moving
Christoffels, T, gComp, Ginv + their bound hypotheses; frame/chrH(gRef)/numerics
stay before ∃).  This was REQUIRED: ric_bound's Cpp/Cppp must be uniform over
(i,t), and the old per-invocation ∃ hid the (numeric-only) constant formulas.
claim1_geom call site updated.  Each proof = same script, intros moved past the
refine ⟨formula,…⟩.

**Route change: BYPASS aN_intrinsic_point (U7 skipped).** Its hinvON-at-the-
eval-point only holds at cover centers.  Instead assemble at COMPONENT level
with aN_component-uniform per cover domain, converting both sides with the
TWO-SIDED goodFrame bounds valid at EVERY z ∈ u′:
- forward (done): `exists_goodFrame_compBound` + `compL2_tower_le`
  (compL2 tower ≤ 2^{r+j}·√normSq0S).
- reverse (W1–W3 below): √normSq0S ≤ ((1+ε)·card)^{s}-ish · compL2.

**Statement fix: hypotheses on open U ⊇ K** (book's nested sets).  The engine
needs bounds on open frame domains; hBprev/hequiv/hShi only on K is not enough
when K has empty interior.  Change ric_bound: add (U : Set M) (hU : IsOpen U)
(hKU : K ⊆ U), state hequiv/hBprev/hShi over U, conclude on K.  Stage-N
induction wrapper will thread U (record in AllTimesBounds consumer later).

**Remaining work list:**
- W1 `quad_ub_of_near_id` (KroneckerQuadForm): |Q−δ|≤ε entrywise ⟹
  ∑∑(∏Q)c_Ic_J ≤ ((1+ε)·card)^s·∑c² (abs-triangle + ∏|Q| ≤ (1+ε)^s +
  (∑|c|)² ≤ card^s·∑c² via sq_sum_le_card_mul_sum_sq over (Fin s → Idx)).
- W2 Comparison upper adapter: normSq0S g x s A = coordInner0S Q ≤ … ∑comp²
  (via normSq0S_eq_coord + W1).
- W3 RicBoundGoodFrame: (a) extend `gramInv_near_id` to also return Gram-entry
  closeness |gramE z i j − δ| ≤ ε (same hentry continuity, trivial); (b) reverse
  tower bound √normSq0S(iterCov tower) ≤ Cu^{r+j}·compL2(tower) at goodFrame
  points (mirror of compL2_tower_le via W2); (c) extend exists_goodFrame_compBound
  to return BOTH directions + the Gram closeness; (d) moving-metric C0 bound:
  vᵀGram_{g}v = g(W,W) ≥ Beq⁻¹·gRef(W,W) = Beq⁻¹·vᵀGramRef v ≥ (1/(2Beq))‖v‖²
  (quad_lb_of_near_id on GramRef-entries + hequiv pointwise) → B4
  `ginv_compL2_le` ⟹ compL2(ginvCompField e₀ g basisE) ≤ √card·2Beq on u′.
- W4 hgB producer: hBprev (MetricCovDerivOrderBoundOn U) + R4f
  `metricCovDerivNorm_eq_iterCov` (check signature; needs pointwise ON basis —
  available pointwise everywhere) + `compL2_tower_le` ⟹ compL2(gRef-tower of
  g-comps, j ≤ N−1) ≤ Kg uniform.
- W5 hShi producer: hShi (moving norm of ricCovTower g g s) +
  `normSq0S_le_of_metric_equiv` (Comparison:614, pointwise hequiv from
  MetricUniformEquivalentOn) + moving-Christoffel `iterCovComp_eq_iterCov` +
  goodFrame forward bound ⟹ compL2(moving Ricci tower) ≤ KShi uniform.
  ALSO Ricci-component smoothness producer (B2 pattern for ricciSection (LC g))
  — check for a generic frameComp0S-smoothness lemma first.
- W6 assembly in RicBound.lean: per x ∈ K goodFrame u′_x ∩ U; finite subcover;
  per domain aN_component-uniform constants; max over the cover; per (i,t,x)
  apply component conclusion + reverse bound (LHS) + compL2_tower_le + R4f (RHS).
  LHS defeq: ricCovTower g gRef N = iterCov gRef 2 (ricciSection (LC g)) N.

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

## KEYSTONE FOUND — the smooth gRef-ON frame producer already exists (2026-06-10)

The "missing-API frontier" (a *smooth* `gRef`-orthonormal local frame) is NOT
missing.  **`exists_trivFrame_orthonormal_basis`** (`ApproximateIsometry.lean:4846`,
sorry-free) delivers exactly it: `∃ basisE`, with `frame := e₀.localFrame basisE`
on `u := e₀.baseSet`, `hframe : IsLocalFrameOn I E ∞ frame u`, `x ∈ u`, and
`∀ i j, gRef.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) = δᵢⱼ`
(gRef-ON AT the centre `x`).  (`exists_orthoFrameAt`/`exists_orthoBasisFrameAt` in
Evolution are pointwise-only — constant `fun i _x => e i`, no smoothness — do NOT
use them here.)  Downgrade `∞→1` for `aN_intrinsic_point` (mono).  The instances
it needs (`VectorBundle`, `ContMDiffVectorBundle 1`) are already in
RicBoundAssembly's variable block.

## Refined remaining decomposition (3 bricks; the frontier is brick 2)

`aN_intrinsic_point` (RicBoundAssembly.lean, DONE) consumes, over a frame domain
`u`: smoothness inputs (frame/Christoffel/metric/Ricci — Claim1Wiring patterns),
`Ginv`/`hinv`/`hGinv` (Claim1Wiring `gramE`/`ginvCompField`), and the COMPONENT
(`compL2`) bounds `hgB` (= (B_r), `1≤j≤N-1`) and `hShi` (Shi, `s≤N`) over all of
`u`, plus `hinvON` at the eval point.  From the keystone + `exists_trivFrame`,
the gap to ric_bound's intrinsic-over-K hypotheses is:

1. **`boundedGram`** (standard continuity): from the keystone frame, shrink to a
   small open `u' ∋ x ⊆ baseSet` with the frame Gram `G(z)=gRef.inner z(frame i z)
   (frame j z)` and its inverse bounded by a constant `CG≥1` on `u'` (continuity,
   `G(x)=Id`).  Feeds both the `Ginv`/`hGinv` data and brick 2's factor.
2. **`towerBridge`** (THE analytic frontier): generalize B5's *equality*
   `compL2_tower_eq` (which holds only at ON points) to a bounded-Gram *inequality*
   over `u'`: `compL2 (iterCovComp frame chr (frameComp0S T) j z) ≤ CG^? ·
   √normSq0S gRef z (iterCov gRef 2 T j z)` (+ reverse).  Apply with `T :=
   metricTensorField g` (intrinsic (B_r) → `hgB`) and `T := ricciSection (LC g)`
   (intrinsic moving Shi → `hShi`, routed through `normSq0S_le_of_metric_equiv`
   (Comparison.lean:520) for the moving↔fixed norm via eq 3.3 + `iterCovComp_eq_iterCov`).
3. **`uniformize`** (compactness bookkeeping): apply `aN_intrinsic_point` at each
   `x∈K` on its `u'_x`; finite subcover of compact `K`; `max` the `Cpp/Cppp`;
   assemble in RicBound.lean — RHS via `metricCovDerivNorm_eq_iterCov` (R4f), LHS
   via the `ricCovTower g gRef N = iterCov gRef 2 (ricciSection (LC g)) N` defeq.

Brick 1 = continuity; brick 2 = the genuine remaining math (component↔intrinsic
tower norm under a varying Gram); brick 3 = finite-cover maxima.  Build order:
1 → 2 → 3, each a named lemma (likely a new `RicBoundGoodFrame.lean` between
RicBoundAssembly and RicBound).

### Brick 2 is NOT from scratch — MSM135 Lemma 3.13 machinery exists

`Tensor0SRiemannian/Comparison.lean` already has the bounded-inverse-metric norm
comparison: `coordInner0S_diagonal_le_pow_identity` (`coordInner0S(diagInv μ) ≤
C^s·coordInner0S(Id)` for `μ ≤ C`), `normSq0S_diag_le` (the invariant form
`normSq0S h ≤ C^s·normSq0S g` given `g`-ON basis + `h`-diagonal-inverse `≤ C` =
Lemma 3.13), and `exists_diagInv_of_equiv` (from two-sided `C⁻¹g ≤ h ≤ Cg`, a
`g`-ON eigenbasis with `h`-inverse diagonal and `≤ C`).  For brick 2: `compL2²` in
the fixed frame `= coordInner0S identityInvMetric (tower)`, and `normSq0S gRef =
coordInner0S (Gram⁻¹) (tower)` (via `normSq0S_eq_coord`); so the bound is
`coordInner0S(Id) ≤ (λ_max Gram)^s · coordInner0S(Gram⁻¹)`, i.e. the same
quadratic-form-power estimate in the direction `Id ≤ C^s·Q` for symmetric posdef
`Q = Gram⁻¹` with `λ_min Q ≥ 1/CG`.  Route: either generalize
`coordInner0S_diagonal_le_pow_identity` to non-diagonal `Q` (operator-norm bound),
or diagonalize `Gram(z)` per `z` (its eigenbasis) and reuse the diagonal lemma —
the diagonal lemma + `exists_diagInv_of_equiv` are the templates.  This shrinks
brick 2 from "new analytic frontier" to "adapt Lemma 3.13 to the compL2 tower."

### Progress 2026-06-10 (verified)

- **`coordInner0S_identity_le_pow_diagonal`** (Comparison.lean, sorry-free, focus-
  checked): the REVERSE of `coordInner0S_diagonal_le_pow_identity` — raw
  component-ℓ² `coordInner0S Id A A ≤ (1/m)^s · coordInner0S (diagInv μ) A A` when
  `μ ≥ m > 0`.  First brick-2 building block (the diagonal case).
- Brick-2 general-`Q` (non-diagonal) core route CONFIRMED: slot-peel induction on
  `s`, peeling the last index via `Fin (s+1) → Idx ≃ Idx × (Fin s → Idx)`; the
  per-step PSD-pairing `Σ (Q-(1/C)Id)_{kl} B(v_k,v_l) ≥ 0` reuses the existing
  **`sum_posSemidef_mul_neg_semidef_le_zero`** (Analysis/Heat/MaximumPrinciple.lean)
  + `Matrix.PosSemidef.eigenvalues_nonneg`.  Fiddly part = the `tensor0SComponent`
  slice reindex under `Fin.cons`/`Fin.snoc`.  Alternative: bridge `coordInner0S` to
  a `Matrix` Kronecker-power quadratic form and use Mathlib PSD-Kronecker (if it
  exists) — heavier bridge, maybe shorter proof.  ~150 lines, slow (1–2 min) checks.
- HONEST: ric_bound theorem 0% proved (sorry); machinery ~75%; this lemma is a
  small slice of brick 2 (one of ~5 remaining pieces: general-Q core, brick 1
  continuity, brick 3 uniformize, Ricci-smoothness producer, final assembly).
  Multi-session.
