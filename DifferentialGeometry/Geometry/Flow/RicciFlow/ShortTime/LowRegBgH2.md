# `LowRegBgH2.lean`

## Role

This module packages the fixed-order `H²` estimates needed to compare the
zero-order Ricci--DeTurck coefficient at a fixed background metric with the
same-background low-base coefficient.  It is part of the analytic machinery
for uniform low-regularity existence; it does not state or prove
`ricci_flow_unif_existence`.

## Verified bricks

- `dlaDiff_h2` packages the public DLa background-difference grid into an
  `H²` bound whose state window ends at `H³`.
- `dlbDiff_h2` packages the public DLb background-difference grid into an
  `H²` bound.
- `insert_h2` proves the insertion-field `H²` estimate from the existing trace,
  connection-difference, and bounded-product estimates.  Its state window ends
  at the `H³` jet.
- `amixDiff_h2` proves the AMix background-difference `H²` estimate.  The proof
  first controls the exact refolded AMix form and then subtracts the two fixed
  backgrounds.
- The private `bgCorrFam`/`bgCorrInt` layer now proves the exact four-way
  background telescope and its path-integral identity.  The general-background
  `C0` coefficient is exactly the same-background `C0`, plus this integral,
  plus one fixed smooth curvature-coefficient difference.
- `bgCorr_h2` aggregates all four component bounds along `realizedFam` and
  transfers the result through the canonical path integral.
- `bgCorrInt_h2` transfers any uniform integrand `H²` bound through the canonical
  path integral, and `fixedBg_h2` closes the state-independent fixed term.
- `lowC0_bg_h2` combines the exact background telescope with the public
  same-background coefficient endpoint.  It gives the complete fixed-background
  `C0` two-jet bound with a state window ending at `H³`.
- `lowC1_bg_h2` packages the public intrinsic order-one path estimate at the
  fixed perturbation radius `δ₀ = 1/3`.  Its state window also ends at `H³`.
  An input bound with `δ ≤ 1/3` is promoted to this common radius before the
  producer is called; this avoids comparing proof-indexed realized paths at two
  different radius witnesses.
- `lowData_bg_coeff` gives one envelope for the complete general-background
  `C0` and `C1` pair.
- `lowA1_bg_bounds` applies the generic action estimates to that same pair and
  proves compatible smooth-core `H3 → H2` and `H2 → H1` bounds.  No `H4` state
  jet or high-Sobolev smallness enters either estimate.

The enlarged file passes persistent-LSP elaboration, the focused Lean check,
and its targeted module refresh.  It contains no `sorry`, `admit`, `axiom`,
`whnf`, or trace option.

## Remaining frontier

The general-background coefficient and first-order action estimates are closed.
The next smallest producer is the exact zero-based remainder split with a fixed
DeTurck background.  The intrinsic action module already proves the needed
identity privately for arbitrary `g_bg`, while its public endpoint specializes
to `g_bg = g`.  The remaining task is therefore a thin canonical exposure of
that exact general-background split, followed by the background-parameterized
time-level data; it is not another coefficient estimate or Ricci algebra
frontier.

## `c0_bg_aff` feasibility gate: FAILED — the C0 arm is not affine in the `H³` jet

Brick BG-1 (ledger №195) asked whether

```
lowJetSq g 2 (lowBaseData g gB T …).C0  ≤  (B0 R + B1 R * A)²
```

with `R` an `H²` radius and `A` the independent `H³` size, i.e. the exact
`c1_bg_aff` shape one order down.  The paper gate was run first, and it **fails**.
No Lean was written.  This is a negative result about the claim, not about the
route to it.

### The decisive term

`.C0 = selfLowInt g gB T … + phiMetCurvCoeff g gB g` (`c0_eq`,
`DeTurck/DeTurckRemainderLowBaseAction.lean:3807`).  The second summand takes no
`T` argument at all (`PhiMetSymmetry.lean:232`), so it is a pure `B0` constant —
that half of the gate is fine.  The first summand is the path integral of
`rhsSelfLow` (`…Action.lean:3750`), whose exact five-arm form is
`selfBase_decomp` (`…Action.lean:11165`):

```
rhsSelfLow g g T … s
  = (-2) • ricciGoodLow g gm (s•T)
    + (deTurckLieCovDerivArmField g gm g − edgeLiePairFam …)
    + lc0VB g gm  +  lc0AMix g gm g  +  lc0Riem g gm ,      gm = g + s·T̂ .
```

Three of these five arms are **quadratic in the connection difference**, i.e.
schematically `(algebraic in gm⁻¹) ⋆ ∇P ⋆ ∇P` with `P = s·T`:

- `lc0VB` is literally `2 • trace( connDiff(g₁,g₁,g₀) ⊗ ι_{W(g₁,g₀)} )`
  (`DeTurckCoefficients/LieCorr0Core.lean:144`) — a connection difference times
  the DeTurck vector field, which is itself a trace of the same connection
  difference.  Both factors carry exactly one derivative of `P`.
- `lc0AMix` is the "mixed connection-difference term" (`LieCorr0Core.lean:173`).
- `ricciGoodLow` splits into `ricciAA` + `ricciDA` (`ricciGood_act_tame`,
  `…Action.lean:7072`); `ricciAAArm` is described in the tree itself as "the
  connection-difference-quadratic Ricci arm … each piece is
  `permCoeff ⋆ (insertion ⋆ innerInsertion)` with both insertions carrying
  exactly one derivative of the state"
  (`Analysis/Sobolev/TensorHilbert/SelfLowCapWindows.lean:277`).

Taking two covariant derivatives of such an arm (which is what `lowJetSq … 2`
requires) produces, by Leibniz,

```
∇²(∇P ⋆ ∇P)  ⊃  ∇³P ⋆ ∇P   and   ∇²P ⋆ ∇²P .
```

**These are the quadratic witnesses, and neither factor is absorbable.**  In
dimension three the only way to price one factor of such a product cheaply is to
put it in `L^∞`, and the tree's own sup-norm producer is `gradCapLin`
(`Analysis/Sobolev/TensorHilbert/TameGridProd.lean:492`):
`‖∇P‖²_{L^∞} ≤ c · ‖P‖²_{H³}` — the first derivative's sup norm costs the **full
`H³` jet, i.e. `A`, never `R`** (`H¹ ⊄ L^∞` at `n = 3`), and `‖∇²P‖_{L^∞}` would
cost `H⁴`, which class three does not have.  The fibre certificate `hδ` bounds
`‖P‖_{L^∞} ≤ δ` only, no derivative, so δ-smallness does not absorb either
factor.  Hence every route leaves both factors priced by `A`.

### Why this is sharp, not a bookkeeping artifact

Two independent confirmations:

1. *The tree's own sharpest bound is already quadratic.*  The `R`-priced
   coefficient producers are `lc0VB_h2_tame` and `lc0AMix_h2_tame`
   (`…Action.lean:8136`, `:8506`), both `≤ (D R · A²)²`, and `lieCov_h2_tame`
   (`:10965`), `≤ (D R · (A + A²))²`.  `ricciAAJet`
   (`TensorHilbert/TameArmJets.lean:298`) is the deliberately sharpened window —
   its docstring advertises "exactly ONE power of `‖P‖²_{H³}`", against the older
   `ricciAACap` route's degree `6(i+1)` — and at `i = 2` it still reads
   `(K₀ + K₂A²)(1 + A²)`, i.e. `A²` in the norm.  The only arm with an honestly
   affine coefficient is `lc0Riem` (`lc0Riem_h2_rf`, `:7472`, `≤ K(1+A²)`), the
   fixed-curvature arm whose metric dependence is algebraic.
2. *A scaling witness refutes the affine claim outright.*  Take a bump family in
   one chart, `P_λ = ε φ(x/λ)`, `φ` a fixed smooth symmetric `2`-tensor.  In
   `n = 3`: `‖P‖_{L^∞} = ε`, `‖P‖_{H²} ≍ ελ^{-1/2}`, `‖P‖_{H³} ≍ ελ^{-3/2}`,
   `‖∇²P ⋆ ∇²P‖_{L²} ≍ ε²λ^{-5/2}`.  Fix `R` and let `A → ∞`: then
   `λ = R/A` and `ε = R^{3/2}A^{-1/2} → 0` — so the δ-fibre certificate is
   satisfied with room to spare — while

   ```
   ‖∇²P ⋆ ∇²P‖_{L²}  ≍  R^{1/2} · A^{3/2} .
   ```

   `A^{3/2}` outgrows `B0(R) + B1(R)·A` for any fixed `R > 0`.  (Equivalently:
   `‖∇²P‖_{L⁴}² ≍ R^{1/2}A^{3/2}` is the sharp Gagliardo–Nirenberg value and is
   attained, so no better product estimate exists.)  The claim is therefore
   **false**, not merely unproved.  The spectral currency does not rescue it:
   the hypotheses are upper bounds on spectral `H²`/`H³` norms, which the easy
   comparison direction supplies from the covariant ones, while the conclusion is
   covariant.

### Why `c1_bg_aff` is affine and `c0` cannot be

`c1_bg_aff` (`LowRegBgC1Time.lean:157`) is not a Leibniz computation at all: it
specialises the existing pair producer `rhs1_path_tame`
(`LowRegRhsOne.lean:203`) at `T' = 0` after `c1_eq`.  The mechanism underneath is
that the order-**one** coefficient carries exactly **one** connection-difference
factor: `C1 ~ f(gm⁻¹) ⋆ ∇P`, so `∇²C1` yields `∇³P` (linear in `A`),
`∇²P ⋆ ∇P` (priced `R · A` by `gradCapLin`) and `(∇P)³` — every product has at
most one factor priced by `A`, the rest by `R` or by δ through `f`.  `C0` is the
order-**zero** coefficient of the same operator and necessarily contains the
`Γ⋆Γ` half of `Ric = ∂Γ + Γ⋆Γ`; the DeTurck trick removes the second-derivative
gauge terms, not the first-derivative-squared ones.  That is the whole
difference, and it is structural.

### Menu for the design decision (reserved for the user, per №195)

- **(a) Accept a quadratic envelope** `‖C0‖_{H²} ≤ B0(R) + B1(R)·A²` and adapt the
  consumer.  This is nearly assemblable from what exists: four of the five arms
  already have `R`-priced coefficient producers of exactly this shape
  (`lc0VB_h2_tame`, `lc0AMix_h2_tame`, `lieCov_h2_tame`, `lc0Riem_h2_rf`); the
  one gap is a coefficient-level `ricciGood_h2_tame` (only the polynomial
  `ricciGood_h2_rf` and the action-level `ricciGood_act_tame` exist), which
  `ricciAA_act_tame`/`ricciDA_act_tame` should give in the same `(D R·(A+A²))`
  shape.  Cost: one arm plus an assembly.
- **(b) Buy affineness with one more jet** — `A` bounding `H⁴` — which silently
  promotes the lane from class three to class four and is explicitly forbidden by
  №195.
- **(c) The refold route** named in №195: restate `IsBgLiftAt`'s core fields
  against a background-refolded bundle and prove the arbitrary-background
  `refold_low_split` analogue.

Note that the same obstruction is visible in the already-landed
`lowA1_act_tame` (`…Action.lean:11893`), whose action bound is
`D R · (A + A²)` = (affine coefficient) × (linear argument) for `C1` but whose
`C0` half `lowC0_act_tame` (`:11584`) inherits the quadratic from
`selfInt_act_tame`.  Any consumer already tolerating `A + A²` there can tolerate
option (a).

## Progress accounting

- `ricci_flow_unif_existence`: theorem remains unstated here and unproved at its
  endpoint, therefore **0%**.
- Fixed-background low-base action: the exact `C0` correction, complete `C0/C1`
  coefficient envelope, and both required smooth-core A1 estimates are verified.
- `c0_bg_aff`: **not implementable as specified** — the claim is false (gate
  section above).  `0%`, and it should not be re-attempted in that shape.
- `IsBgA1At` / `IsBgLiftAt` producer: **0%**.  The `bgA1_aff` chain toward its two
  affine bound fields is blocked at this arm until the user rules between options
  (a), (b), (c).
- Dedicated uniform-existence machinery: approximately **80%** (aligned with
  ledger №194/№195; the gate landed no code, so the number is unchanged).  This
  is infrastructure progress, not theorem completion.
- Whole HCG compactness theorem closure: approximately **3%**.

## 2026-08-07 — MISSING PRODUCER identified here (B2 part (a), ledger №205)

`c0bg_pack` (the affine packet for the ΔC0 passenger of `refoldCoreBg`) needs
a TAME `H²` envelope for the background correction, and this file is its home:

> `c0Bg_diff_tame`: ∃ `B0 B1 : ℝ → ℝ` ≥ 0, ∀ `T` with
> `∑_{j<3}‖∇^j T‖² ≤ R²` and `‖∇³T‖ ≤ A`,
> `lowJetSq g₀ 2 ((lowBaseData g₀ gB T …).C0 − (lowBaseData g₀ g₀ T …).C0)
>   ≤ (B0 R + B1 R · A)²`.

State it on the BARE DIFFERENCE: `lowC0_bg_eq` (`:893`) and `bgCorrInt`
(`:816`) then stay `private` (the smaller honest surface — un-privatizing a
path-integral internal would make it permanent public API and would not fix
the shape).  Note `bgCorr_h2` (`:950`) and `bg0_pair_h2`
(`LowRegBgA1Pair.lean:462`) are `public` in keyword only: their conclusions
name private definitions, so no other module can apply them.  `lowC0_bg_h2`
(`:997`) IS applicable but its `B` is opaque (degree six internally), so it
cannot serve the affine half.

**The `c0_bg_aff` FAILED gate above does NOT apply to the difference.**  Its
three decisive quadratic arms — `ricciGoodLow g gm`, `lc0VB g gm`,
`lc0Riem g gm` — carry no background argument (`selfBase_decomp`), so they
cancel in `bgCorrFam`.  Only DLa/DLb/Insert/AMix survive (`bgCorr_eq`), and
all four are affine-shaped already; see ledger №205 for the arm-by-arm
verification and the engines (`h2_grid_tame`, `connLow_tame`,
`trace_h2`/`kappaBg_h2` being H²-jet-only).  Route: tame siblings of
`dlaDiff_h2`/`dlbDiff_h2` (one-call swap), `insert_h2` (use `connLow_tame`),
`amixForm_h2`+`amixDiff_h2` (pure restatement — the envelope is already
`const(R)·A`), then `bgCorrFam_tame`, `bgCorrInt_tame`, and the assembly with
`fixedBg_h2`.  ~400 lines; file goes 1270 → ~1670, under the 3000 cap.

## 2026-08-07 — B2a LANDED: `c0Bg_diff_tame` (ledger №207)

**Verified.**  Focused check green; targeted builds
`+…ShortTime.LowRegBgH2` and `+…ShortTime.LowRegBgTime` (the only downstream
importer) both completed successfully; `c0Bg_diff_tame`, `amixDiff_tame`,
`insert_tame`, `dlaDiff_tame`, `dlbDiff_tame` and the untouched
`lowC0_bg_h2` each depend on `[propext, Classical.choice, Quot.sound]` only.
No `sorry`, no new `set_option maxHeartbeats`, no linter warning left.
File 1270 → 1579 lines.

### The cancellation was already proved in this file

`bgCorr_eq` (`:692` pre-edit) *is* the definition-level verification the
dispatch asked for: `bgCorrFam = rhsSelfLow g gB T − rhsSelfLow g g T` reduces
to DLa + DLb + Insert + AMix, with no `ricciGoodLow` / `lc0VB` / `lc0Riem`
term left.  Nothing had to be re-derived from `selfBase_decomp`; the three
quadratic arms take no background argument, exactly as №205 claimed.

### Final statement (hypothesis convention corrected)

The ledger's spelling (`∑_{j<3}‖∇ʲT‖² ≤ R²`, `‖∇³T‖ ≤ A`) was replaced by the
sibling convention of `c0Coeff_aff` (`LowRegBgC0Core.lean:340`), i.e.
`lowJetSq g 2 T ≤ R²` and `lowJetSq g 3 T ≤ A²`, because `c0_core_affine`
(`LowRegBgC0Time.lean:122`) — the template B2b must mirror — consumes exactly
that pair via `jet2_le_hs` / `jet3_le_hs`.  `lowJetSq g 3 T ≤ A²` is strictly
stronger than `‖∇³T‖ ≤ A`, so the theorem is (harmlessly) weaker and drops
straight into the `c0_core_affine` bookkeeping with `R := C2·ρ`,
`A := C3·‖ccToHsLin g 2 3 T‖`.  No symmetry hypothesis `hT` is needed — the
arms that consume symmetry are exactly the ones that cancel.

### Arm ledger

| arm | tame producer used | shape |
| --- | --- | --- |
| DLa | `dlaBg_grid` + `h2_grid_tame` (one-call swap for `h2_of_grid`) | `B0 R + B1 R·A` |
| DLb | `dlbDiff_grid` + `h2_grid_tame` | `B0 R + B1 R·A` |
| Insert | `trace_h2` at `R` + `connLow_tame` (replaces `connLow_h2`) | `B0 R + B1 R·A` |
| AMix | `kappaDiff_h2` + `kappaSelf_h2` + `trace_h2` at `R` | `0 + B1 R·A` |

### The one place №205's route note was WRONG (and the repair)

№205 said AMix was "already affine, a pure restatement".  It is not:
`amixForm_h2`'s envelope is `const(R) · BK(A) · A`, where the `BK` factor is
`kappaBg_h2`, and `kappaBg_tame` (`LowRegCoeffJets.lean:1700`) is
`√(3(16A² + SF + BP(R)²))` — it does **not** drop to the range-3 sum, because
`kappa_bg = kappa_self + kappa(g₀,gB) + pbLow` and `kappa_self` genuinely needs
`∇³P` at `H²`.  Bounding the two AMix forms separately therefore gives `A²`,
not `A`.

The affineness comes from a SECOND cancellation, one level below the arm split:
`gB` enters `lc0AMixHalfRF` only through the single slot
`slotExtendIter (lc0Kappa g₀ g₁ gB)`, and that occurrence is linear, so the
background difference replaces it by
`bgKappa = lc0Kappa g₀ g₁ gB − lc0Kappa g₀ g₁ g₀`, in which the Koszul
self-arm cancels.  `kappaDiff_h2` (`LowRegInsertH1.lean:194`, public and
already imported) bounds precisely that difference by `BK R` — **R-only**.
So the surviving product carries exactly one top derivative, from the
`kappaSelf_h2` factor in the inner `Qf` slot.

Implementation: `bgKappa`, `bgAmixHalf`, `amixHalf_bg`, `bgAmix_eq` (all
private).  These are byte-for-byte the same lemmas as the private ones in
`LowRegBgC0PairH2.lean:47–140`; that file could not be reused (private, and it
sits above this one in the import order).  **Dedup candidate**: promote
`bgKappa`/`bgAmixHalf`/`amixHalf_bg`/`bgAmix_eq` and `slotIter_sub` into
`LowRegInsertH1.lean`, which both files already import, and delete both private
copies.  Deliberately NOT done here: adding a public `bgAmix_eq` while the
private one still exists in `LowRegBgC0PairH2` would make the name ambiguous
there, so the promotion and the two deletions must land in one commit.

### API collapse performed (one canonical tame layer)

`dlaDiff_h2`, `dlbDiff_h2`, `insert_h2`, `amixForm_h2`, `amixDiff_h2` had
**zero consumers outside this file** (census re-run before touching them; the
`insert_h2` hits in `DeTurckRemainderLowBaseC1Lip.lean` are a different,
private theorem).  Their only in-file consumer was `bgCorrFam_h2`, which is now
a five-line wrapper around the new `bgCorrFam_tame`.  So the non-tame arm
lemmas were replaced outright rather than duplicated — the file grew by 309
lines, not the ~400 estimated, and `amixForm_h2`'s 154-line normal-form bound
disappeared entirely (the difference route never needs it).

Untouched and still the diagonal (quadratic) statement: `bgCorr_h2`,
`lowC0_bg_h2`, `lowC1_bg_h2`, `lowData_bg_coeff`, `lowA1_bg_bounds`.
`bgCorrInt` and `lowC0_bg_eq` stayed private, as specified.

### Lean lessons from this pass

- `slotIter_sub` is public in `LieCorr0LowJet.lean:1306` but that module is
  **not** in this file's import closure (`slotExtendIter` arrives from
  `AppCcDropIteratedGrid`, `slotExtend_sub` from
  `OperatorFieldCovariantCalculus`).  A private local copy is required; this is
  presumably why `LowRegBgC0PairH2` also carries one.
- `omit [CompactSpace M] …` on that copy fails with *"cannot omit referenced
  section variable"* — `SmoothCcTensor`'s own elaboration references them.
  Only `topNorm_le` could be slimmed (`omit [BoundarylessManifold I M]`).
- `bgCorrFam_tame` first blew the default heartbeat budget at `whnf`.  The
  cause was eight `nlinarith` calls discharging goals of the shape
  `Ba0 R ≤ Ba0 R + Bb0 R + Bi0 R + Bm0 R`; swapping them for `linarith` brought
  the declaration well inside the default budget.  No `set_option
  maxHeartbeats` was added.
- Assembly pattern that keeps the arithmetic cheap: bound every arm by the
  SAME `V := ΣB0ᵢ R + (ΣB1ᵢ R)·A` (one `pow_le_pow_left₀` per arm), then
  `h2Jet_sum4 … V V V V` and close `4·(4V²) = (4V)²` by `ring`.  Trying to feed
  four distinct affine bounds into one `nlinarith` is what makes this step
  expensive.
- The endpoint's proof-term mismatch (`hδ_lt` versus the statement's inline
  `lt_of_le_of_lt hδ_le (by norm_num)`) is crossed by `change`, not `rw`; and
  the style linter rejects `show` for that, so `change` is also the required
  spelling.

### B2b entry point

`c0bg_pack` must emit `BgDeltaPack g gB` (`LowRegBgA1Refold.lean:902`, seven
clauses).  Mirror `c0_core_affine` (`LowRegBgC0Time.lean:122`) line for line:
`S := lowRadial g ρ T`, `R2 := C2·ρ` from `jet2_le_hs` + `lowRadial_norm`,
`A3 := C3·‖ccToHsLin g 2 3 T‖` from `jet3_le_hs` + `lowRadialH3_le` /
`lowRadialH3_core`, feed `c0Bg_diff_tame`, then `a1_diff` against the zero
bundle gives `Z := Ca·B0 R2`, `L := Ca·B1 R2·C3`.  Because
`deltaCoreBg.C1 = 0` and `.C2 = 0`, the `a1_diff` input is
`lowJetSq g 2 ΔC0 + lowJetSq g 2 0`, so a `lowJet_zero` mirror
(`LowRegBgC0Time.lean:81`) is needed.  The continuity clauses ride
`c0_bg_pair_h2` (`LowRegBgA1Pair.lean:759`) and the square clause rides an
`a1_comm_any` mirror (`LowRegBgC0Time.lean:237`) — per №206, `a1_comm` itself
does NOT suffice, it only lands at smooth states.
