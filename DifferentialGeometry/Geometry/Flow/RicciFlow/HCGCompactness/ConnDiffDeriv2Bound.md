# ConnDiffDeriv2Bound — the `hAcc` (m ≥ 2) frontier: recon + state-before-prove

Companion to `ConnDiffDeriv2Bound.lean`.  Sibling of `ConnDiffDerivBound.md` (the a=1 / B2 note) and
`UNIF_ITEM6_RECON.md` (the B2 route).  This note RULES the a ≥ 2 route, records the single stated
lemma, and gives the honest size estimate for the campaign.  **This was a RECON brick: the deliverable
is the route + a stated frontier lemma, not a proof.**

## 0. STATUS (2026-07-25)

- Ruling: **route (i) — iterate the differentiated Koszul identity** — RULED IN.  Routes (ii) and (iii)
  ruled OUT (reasons in §2).
- Stated: `covStepDiff2_exists_const` (the a=2 base-Leibniz jet atom) — elaborates GREEN, one `sorry`,
  `[NormedSpace ℝ E]`-only (standing ruling honoured).  Focused check: no errors, only the intended
  `declaration uses sorry`.
- a=2 NOT proved: it is **not** a direct extension of committed pieces — it needs a genuinely new
  differential-geometric identity (`connDiff_koszul_deriv2`, §4).  Per the brick's task 3, machinery
  NOT built; exactly what is missing is recorded (§3, §4).
- Files: created `ConnDiffDeriv2Bound.lean` + this note.  UNTOUCHED: `UnifCovSumCross.lean`,
  `AllTimesBounds.lean`, `ConnDiffDerivBound.lean`, `Evolution/*`.

## 1. THE REDUCTION — `hAcc m` forces `∇₂^a A`, unavoidably

`hAcc m` (`UnifCovSumCross.lean`, `iterCovG1_le`) bounds the **base** covariant derivative of the
telescoping accumulator:
```
√normSq0S(g₂, r+m+1, covStep g₂ (r+m) (telescAccum g₁ g₂ r T m))  ≤  Racc m · ∑_{k≤m+1} |iterCov g₂ r T k|_{g₂}.
```
Tower vocabulary (`MetricCovDerivLinear.lean`): `covStep g₂ = ∇₂`, `covStep g₁ = ∇₁`,
`diffStep g₁ g₂ = ∇₁ − ∇₂ = A ⋆ ·` (algebraic, `A = Γ₁ − Γ₂`), and
`telescAccum (m+1) = ∇₁(telescAccum m) + (∇₁ − ∇₂)(∇₂ᵐ T)`, `telescAccum 0 = 0`,
`telescAccum 1 = A ⋆ T`.

Expanding `∇₂(telescAccum(m+1))` with `∇₁ = ∇₂ + A⋆`:
```
∇₂(telescAccum(m+1)) = ∇₂²(telescAccum m) + ∇₂(A ⋆ telescAccum m) + ∇₂(A ⋆ ∇₂ᵐT).
```
The `∇₂²(telescAccum m)` term forces a **second** base derivative; iterating pushes the derivative
order up while the accumulator level comes down, so the honest object is the whole family
`∇₂^j(telescAccum m)`.  The `∇₂^j(A ⋆ S)` terms that appear are the **base-Leibniz jets of a single
connection-difference step**, and

  `∇₂^j(A ⋆ S) = Σ_{i≤j} (binom j i) (∇₂^i A) ⋆ (∇₂^{j−i} S)`   (Leibniz / Faà-di-Bruno),

so `∇₂^a A` appears with an S-independent coefficient.  **The star-product structure means `∇₂^a A`
cannot be avoided**: any recursion on `A ⋆ S`-shaped objects spawns `(∇₂A)⋆S`, `(∇₂²A)⋆S`, …, i.e. the
individual connection-difference jets.  This is why route (iii) (recurse on the accumulator, never
isolate `∇₂^a A`) does NOT dissolve the frontier (§2).

### The concrete m = 2 decomposition (what the next brick assembles)

`telescAccum 2 = ∇₁(A ⋆ T) + (A ⋆ ∇₂T)`, and `∇₂(telescAccum 2)` splits into three pieces:
```
∇₂(telescAccum 2) = ∇₂²(A ⋆ T)            -- I.a  a=2  ← THE NEW ATOM (covStepDiff2_exists_const)
                  + ∇₂(A ⋆ (A ⋆ T))        -- I.b  a=1, S = A⋆T   (covStepDiff_of_jets, committed)
                  + ∇₂(A ⋆ ∇₂T).           -- II   a=1, S = ∇₂T    (covStepDiff_of_jets, committed)
```
Derivation: `∇₂(telescAccum 2) = ∇₂(∇₁(A⋆T)) + ∇₂(A ⋆ ∇₂T)`; expand `∇₁ = ∇₂ + A⋆` inside the first:
`∇₂(∇₁(A⋆T)) = ∇₂²(A⋆T) + ∇₂(A ⋆ (A⋆T))`.  Only **I.a** is new.  I.b needs `|A⋆T|_{g₂}` (a=0 norm of
`diffStep`, available/derivable) and `|∇₂(A⋆T)|_{g₂}` (= `covStepDiff_of_jets` at S = T); II needs
`|∇₂T|, |∇₂²T|` (= `iterCov g₂` jets).  So **the sole new mathematics at m = 2 is `∇₂²(A ⋆ S)`**, which
this file's `covStepDiff2_exists_const` isolates (with S = T, s = r it is exactly term I.a).

## 2. ROUTE RULING (≤ a page)

**Route (i) — iterate the differentiated Koszul identity. RULED IN.**
B2 landed the a=1 identity `connDiff_koszul_deriv` (`ChristoffelDiffKoszulDeriv.lean:227`):
```
2 g₁(∇₂A(W,X,Y), Z) = [∇₂²g₁ combos] − 2 (∇₂_W g₁)(A(X,Y), Z),
```
with `∇₂²g₁ = nabla0SFun 3 (LC g₂) W (totalNabla0S 2 (LC g₂)(mtf g₁))` = `metricCovDeriv g₁ g₂ 2`.
**Key check (the recon's central question): does the Koszul RHS stay in `metricCovDeriv` currency at
order a+1?  YES.**  Differentiating once more along `V` (metric-compat Leibniz):
- the `∇₂²g₁`-combo terms become `∇₂³g₁`-combo terms = `metricCovDeriv g₁ g₂ 3` (order 3 = a+1); and
- the quadratic `(∇₂g₁)·A` term becomes `(∇₂²g₁)·A + (∇₂g₁)·(∇₂A)` (order-2 jet × a=0 atom + order-1
  jet × a=1 atom).
So route (i) is a clean **recursion in the metric-jet currency**:
`|∇₂^a A| ≲ |∇₂^{a+1}g₁| + Σ_{j<a} |∇₂^{a−j}g₁|·|∇₂^j A|`, base a=0 = `lcDiff_norm_le`, a=1 =
`covDerivConnDiff_gJet_le` (both committed).  This is why the stated lemma's metric jets reach **order 3**
and carry the **role asymmetry** (∇g₁ w.r.t. g₂ in `hJet1/2/3`; ∇g₂ w.r.t. g₁ in `hJet1'`, sharing Λ').
Shortest correct route; reuses the committed a=1 machinery verbatim; the general-`s` comparability
`sqrt_normSq0S_comp` already covers the higher orders.

**Route (ii) — bundle A as a tensor field, run generic `tensorRSCovariantDerivative`/`covGrad` Leibniz.
RULED OUT.**  `∇₂^a A` would be iterated `covGrad g₂` of `connDiffSection g₁ g₂`.  But A is not a product
of g-jets *as a bundled object*; to bound `covGrad^a (connDiffSection)` you still need the Koszul formula
`A ~ g₁⁻¹∇₂g₁` and to differentiate it — i.e. route (i)'s content — packaged through the bundled
covariant derivative.  This is exactly the bundled-`covGrad connDiffSection` fibre bound (P2.d) that B2
**deliberately bypassed** via the dual/eval route (see `ConnDiffDerivBound.md` §"ROUTE DECISION").
Resurrecting it is strictly more work, not less.

**Route (iii) — recurse on the accumulator re-expansion, bounding whole products.  RULED OUT.**  As §1
shows, `∇₂(telescAccum(m+1))` needs `∇₂²(telescAccum m)` (the full derivative tower), and each
`∇₂^j(A ⋆ S)` term spawns `∇₂^a A` via the Leibniz expansion.  Route (iii) therefore needs the SAME
`∇₂^a A` content as route (i) **plus** a two-index induction on `(j, m)`.  Strictly more work; it
reorganises the frontier without dissolving it.

## 3. THE STATED LEMMA (the interface)

`covStepDiff2_exists_const` (`ConnDiffDeriv2Bound.lean`, namespace `DifferentialGeometry.HCGCompactness`):
```
(hEq  : MetricUniformEquivalentOn K g₂ g₁ Λ)
(hJet1 : MetricCovDerivOrderBoundOn K 1 g₁ g₂ Λ')     -- ∇g₁ / g₂
(hJet2 : MetricCovDerivOrderBoundOn K 2 g₁ g₂ Λ'')    -- ∇²g₁ / g₂
(hJet3 : MetricCovDerivOrderBoundOn K 3 g₁ g₂ Λ''')   -- ∇³g₁ / g₂   (order a+1 = 3, the new jet)
(hJet1': MetricCovDerivOrderBoundOn K 1 g₂ g₁ Λ')     -- ∇g₂ / g₁   (role asymmetry)
⊢ ∃ C₂ ≥ 0, ∀ (S : Tensor0SField … s) (x ∈ K),
    √normSq0S(g₂, s+3, ∇₂²(A ⋆ S) x)
      ≤ C₂ · (|S x| + |∇₂S x| + |∇₂²S x|)     [ ∇₂²(A⋆S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S)) ]
```
Constant is **existential** (honest state-before-prove): C₂ depends only on `Λ,Λ',Λ'',Λ''',finrank E,s`,
uniform in `S` and `x∈K` — the a≥2 campaign has not pinned its explicit polynomial, only its structure
(order-3 metric jets, order-2 S-jets, role asymmetry).  A downstream `hAcc`-facing consumer reads
`Racc 2 := C₂` and `hRnn 2 := ·.1` (this matches `iterCovG1_le`'s abstract `Racc : ℕ → ℝ`, `hRnn`).
Placement: NEW sibling leaf, not `ConnDiffDerivBound.lean`, so the committed sorry-free B2 file stays
pristine and its axiom audit stays meaningful; the a≥2 campaign gets a dedicated home.  `[NormedSpace ℝ E]`
only — the atom uses only fibre data, and both dependency layers (`MetricCovDerivLinear:42`,
`AllTimesBounds:560`) are NormedSpace-only, so the InnerProductSpace consumer can still use it.

### What discharges the `sorry` (two ingredients, one genuinely new)

1. **THE FRONTIER — `connDiff_koszul_deriv2` (does NOT exist; grep-confirmed).**  The a=2 differentiated
   Koszul identity of §2, plus its a=2 dual core (analogue of `ConnDiffDerivBound`'s private
   `covDerivConnDiff_g1_le`) yielding `|∇₂²A|` in metric-jet currency.  This is a new
   differential-geometric identity of the same character/size as `connDiff_koszul_deriv` (B2 session 5,
   ~150–300 lines, needed the differentiation engines `metric_leibniz_extDeriv`,
   `nablaMetric_combo_extDeriv`, `nabla0SFun_eval_smooth_slots`).  Canonical home upstream:
   `Geometry/Connection/LeviCivita/` next to `connDiff_koszul_deriv`.
2. **MECHANICAL — the a=2 base-Leibniz operator identity** `∇₂²(A⋆S) = (∇₂²A)⋆S + 2(∇₂A)⋆∇₂S + A⋆∇₂²S`
   (a=2 analogue of `diffStep_leibniz`, `MetricCovDerivLinear.lean:516`, pure `covStep`/`diffStep`
   algebra), then the fibre Cauchy–Schwarz product bound composing the a=0 atom `|A| ≲ √(Λ³)Λ'`
   (`lcDiff_norm_le`), the a=1 atom `|∇₂A| ≲ Λ⁴(Λ''+ΛΛ'²)` (`covDerivConnDiff_gJet_le`), and the a=2 atom
   from (1).

## 4. a = 2 VERDICT — not a direct extension

Task 3 asked to prove a=2 **iff** it is a direct extension of committed pieces.  It is NOT: the only new
atom (§1, term I.a) is `∇₂²(A ⋆ S)`, whose bound needs `|∇₂²A|`, whose only route needs the new identity
`connDiff_koszul_deriv2` (§3.1).  That identity is genuinely new machinery (grep confirms no
`covDerivConnDiff2` / `koszul_deriv2` / iterated-connection-difference-jet exists in the tree).  Per the
brick's instruction, machinery NOT built; the `sorry` in `covStepDiff2_exists_const` is the single
remaining visible frontier.

## 5. HONEST SIZE ESTIMATE

- `hAcc` is the LAST mathematical piece of **UNIF item 6**; item 6 is one lane of the multi-week HCG
  compactness project.  So `hAcc a≥2` is a small fraction (~1–2%) of the whole HCG project, but it gates
  item 6's completion.
- **a=2 alone (this atom):** the `connDiff_koszul_deriv2` identity + dual core dominate; mirrors B2
  session 5. Estimate ~2–4 focused sessions.  The base-Leibniz assembly (§3.2) and the `hAcc m=2`
  glue (in `UnifCovSumCross.lean`, the NEXT brick, out of scope here) are each ~1 session of bookkeeping.
- **General a ≥ 2 (all orders / uniform-in-a):** substantially more.  Cleanest is a general-`a`
  `covDerivConnDiffN` object + a Faà-di-Bruno schematic + the per-order Koszul recursion (§2).  This is a
  genuine multi-session-to-multi-week infrastructure project.  Reaching order 2 (this atom) is the first,
  gating step and validates the recursion currency.
- **Theorem vs machinery (per CLAUDE.md honest split):** the `hAcc a≥2` frontier is **0% proved**; its
  dedicated machinery for a=2 is **~0% built** (the differentiated-Koszul-2 identity does not exist).
  The RECON + interface (route ruled, atom stated green, reduction pinned) is complete — but that is the
  scaffolding, not the theorem.

## 6. INFRA-MAP CROSS-CHECK — no false wall

`ConnDiffDerivBound.md`'s "Infra map verdict" flagged as genuinely missing "∇ of `connDiff` as a tensor
field fed through `tensorRSCovariantDerivative`/`covGrad`" — i.e. route (ii)'s bundled object.  This recon
**agrees** it is missing AND shows route (ii) is the wrong route (B2 bypassed it).  **No existing engine
was found that the map missed**: the a=2 atom `∇₂²A` (route i's object) is genuinely absent
(grep-confirmed).  The useful nuance the recon adds: the missing piece is SMALLER/cleaner than route (ii)
implied — a per-order Koszul-differentiation identity that reuses the committed a=1 engines and stays in
`metricCovDeriv` currency, **not** a bundled-tensor covariant-derivative Leibniz theory.  Route (i) makes
`∇₂^a A` a clean recursion rather than a new fibre-norm bundle project.

## 7. ENV / Lean lessons

- **Working-checkout cwd trap (cost 3 tool calls).**  `E:\testdifferential-geometry` (the DEFAULT cwd of
  both the Bash and PowerShell tools) is STALE; the primary tree is `E:\testdifferential-geometry-ste-align`.
  File ops must use absolute ste-align paths; Bash needs `cd /e/testdifferential-geometry-ste-align`;
  **PowerShell/lake needs `Set-Location E:\testdifferential-geometry-ste-align` first** or `lake env lean`
  reports "no such file" and `lake-locked.ps1 check` reports "No existing Lean files to check" (its
  Test-Path guard fails in the stale tree).  The `lake-locked claim` succeeds even in the wrong tree (it
  does not Test-Path), which masks the mistake — always `Set-Location` before lake.
- The atom statement elaborates `[NormedSpace ℝ E]`-only.  Confirms `covStep`/`diffStep`/`normSq0S`/
  `MetricCovDerivOrderBoundOn` are all InnerProductSpace-free; `ConnDiffDerivBound.lean` carries
  `[InnerProductSpace ℝ E]` only for its `covGrad`/`connDiffSection` P1 machinery, which the atom avoids.
- Existential-constant (`∃ C₂ ≥ 0, ∀ S x∈K, …`) is the right honest interface for a state-before-prove
  frontier whose constant is not yet derived: it asserts uniformity (C₂ independent of S, x) without
  committing to a wrong polynomial, and still supplies the consumer's `Racc`/`hRnn`.  An
  existential-at-a-fixed-point would be vacuous — the `∀ S x∈K` inside is load-bearing.
