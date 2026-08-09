# DeTurckRemainderLowBaseH2Cov — status, findings, lessons

**Class 2** of the `H²` five-class capstone `selfLow_pair_h2`: the DeTurck--Lie
covariant-derivative edge against its refolded pair-trace partner.

Import order: `…LowBaseLip` → `…H2VB` → `…H2Cov` → `…H2Pair`.  Everything lives
in `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral`, and the capstone is
named `lieCovH2Pair` — the same name the `sorry` stub had inside `…H2Pair.lean`,
so the master telescope's call site was not touched, only the stub deleted.

## Status — sorry-free, axiom-clean

`#print axioms` on `lieCovH2Pair`, `covXBddH2`, `covXPairH2`, `r4PairH2`:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

| declaration | role |
|---|---|
| `domH2` / `domSub` | input-slot permutation is an `H²` jet isometry, and is additive |
| `armSuccEq` / `armSub` / `armSuccH2` / `arm2H2` | the connection-arm slot tower at `H²` |
| `hatBddH2` / `hatPairH2` | the public `lieOmega_bdd_h2` / `lieOmega_pair_h2` restated on `lrOmegaHat` |
| `jetSix` / `quadSixH2` | the six-block `lrQuadF` splitting, hoisted |
| `envSq` / `envQuart` / `envOne` | scalar quartic-envelope facts |
| `armBddH2` / `armPairH2` | `H²` moduli for `armSlotEndoCc g 2 (bdConnPair g gm)` |
| `curvSub` / `curvBddH2` | the curvature head is linear in the state |
| `quadTelB` / `quadTelA` / `quadBddH2` / `quadPairH2` | `H²` moduli for `lrQuadF` |
| `r4BddH2` / `r4PairH2` | `H²` moduli for `lieCovR4` |
| `covXBddH2` / `covXPairH2` | the `X` slot after `Ext²` and the output-slot permutation |
| `edgeEq` | `edgeLiePairFam = deTurckLieCovDerivRefoldPairTraceFamily …` (`rfl`) |
| `lieCovH2Pair` | **class 2, proved** |

## The route as executed

`lieCov_residual` (Palatini, public) collapses the whole edge to a *single*
product

```
(deTurckLieCovDerivArmField g gm g − edgeLiePairFam g T … s)
  = (−1) • app₂₆₂( lieCovPair gm , X ),
X = rsPerm(lieCovSigma)( Ext²( lieCovR4 T ) ).
```

So there are only two telescope levels, both read at `J2`:

| level | bounded | difference |
|---|---|---|
| `lieCovPair gm` | `LowBaseInternal.pairTrace_bdd_h2` (`A`-free, `Bp²`) | `pairTrace_pair_h2` (pure `N`-currency) |
| `X` | `covXBddH2` (`Dx R · (1+A)⁴`) | `covXPairH2` (`Cx R · (1+A)⁴·D3²`) |

and `appH2 2 6 2` multiplies them.

The `X` slot is where the work is.  `lieCovR4_eq` gives
`lieCovR4 = −(s/2)·CurvF(T) − QuadF(gm)`:

* **CurvF is linear in `T`** — `lrCurvF g T = app(lrRiemW1 g, T) + app(lrRiemW2 g, T)`
  with both kernels frozen `g`-objects, so `curvBddH2` gives
  `J2 (CurvF T) ≤ Cc · J2 T` with an `A`-free constant, and the pair case is
  *the same lemma* applied to `T − U` after `curvSub`.  No separate
  `curvF_pair_h2` is needed.
* **QuadF is six permuted `arm ⊗ hat` blocks.**  Bounded: `armBddH2`
  (`(fr·Bs R·A)²`, sharp — the arm is a pure connection difference, reached
  through `bdConnDiffSection_eq_armSlotEndoCc_zero` + `connSec_self_h2` +
  `wXiSelfTame`) times `hatBddH2` (`(Bt R·A)²`).  Difference: `armPairH2` (from
  the public `connSec_sub_tame`) and `hatPairH2` (from the public
  `lieOmega_pair_h2`), both of the two-arm shape
  `(B0·D3 + B1·D2 + B1·A·D2)²`.

Both connection-difference pair moduli are fed with `D2 := D3` (legitimate by
`jetMono`), so `pairFold3` — already in `…H2VB.lean` — folds them into
`M·((1+A)²·D3²)` in one step.  With `A² ≤ (1+A)²` the whole quadratic head lands
on `Cq·Kq R·((1+A)⁴·D3²)`.

The `X` slot therefore carries an `A²` passenger (arm ~ `A` against hat ~ `A`),
inadmissible against a difference.  Exactly as in classes 3 and 4, **both**
states are re-read at the interpolated third-jet size

```
a := √(Cip · R · A4)      (jetInterp3, applied to T and to U directly)
```

so `covXBddH2` contributes `pl2·pl2 = (1+a)⁴` and `covXPairH2` contributes
`(1+a)⁴·D3²`, and the same hoisted scalar lemma `amixScalar` closes with
`u := D3² + N²`:

```
(B0 R · (1+A) · (D4 + D3 + D2 + N) + B1 R · A4 · (D3 + N))²,
B0 R = √(8·Bh R),   B1 R = √(8·Bh R)·Cip·R,
Bh R = 2·(Ca·Cp²·Dx R + Ca·Bp²·Cx R).
```

`D2` and `D4` are absorbed as slack only; the proof uses neither `A` nor
`D2`/`D4` quantitatively.

## What was found while routing this

* **`jetInterp3` is applied to `T` and `U` themselves, not to `P = s·T`.**
  Unlike classes 3 and 4, the `X`-slot producers take the *original* state
  (because `lieCovR4 g T hδT hδZ s` mentions `T`), and they build `P = s·T`
  internally.  So `hT3i : J3 T ≤ a²` is fed straight in as the `A`-slot.
* **The recipe's "`ΔlieCovPair ⊗ covX` gives `N·(A+A²)`" is right, but the
  `covX` bound is cleaner stated in the `(1+A)⁴` envelope** than in the `H¹`
  sibling's `(A + A²)²` shape: `(a+a²)² = a²(1+a)² ≤ (1+a)⁴`, and the extra
  `a²` is never needed, so the envelope form removes an algebra step from the
  capstone and matches the `pl2·pl2` currency of `amixScalar` verbatim.
* **`lipOmega` is `private` to `…LowBaseLip.lean`**, so `hat_eq_lip`
  (`lrOmegaHat = lipOmega`, `rfl`) cannot be *stated* here.  It does not need
  to be: the public `lieOmega_bdd_h2` / `lieOmega_pair_h2` are consumed by
  `exact`, and the definitional equality is discharged by the elaborator
  without ever naming the private constant.  `hatBddH2` / `hatPairH2` are those
  two facts restated on the public `lrOmegaHat`.
* **The arm slot tower needed only `armSlot_succ_lip`** (cloned as `armSuccEq`).
  The `H¹` lane's `rfns_arm_le_lip` / `arm_l2_lip` pointwise induction is *not*
  needed: `armSuccEq` + the already-public `reindexJet`, `rspermH2`, `slotH2`
  from `…H2VB.lean` give `armSuccH2` in four lines, and `arm2H2` is two steps.
  This saved ~100 lines of clone.
* **`connSec_sub_tame` (C1Lip, public) is already the `H²` arm difference.**
  The `H¹` lane's `armD_pair_h1` route through `connSec_pair_h1` has no `H²`
  analogue and is not needed.
* **No publicization was required** for class 2 either — the third class in a
  row where the "minimal publicization list" in `…H2Pair.md` turned out to be
  unnecessary.

## Canonical-home note for the next class

`domH2`, `domSub`, `jetSix`, `envSq`, `envQuart`, `envOne` and the arm tower
(`armSuccEq`, `armSub`, `armSuccH2`, `arm2H2`) carry no class-2 content — they
are generic `H²` jet algebra and belong in `…H2VB.lean` alongside `slotH2` /
`reindexJet` / `rspermH2` **once they have a second consumer**.  They are kept
here for now because class 2 is the only one, matching the rule already
recorded in `…H2VB.md` for the interpolation block.  Class 1 (`ricciAAKer`,
which also has permuted blocks and connection arms) is the likely second
consumer: lift them then rather than duplicating.

## Lean lessons banked

* A theorem whose *statement* mentions neither `I` nor `M` (here `envSq`,
  `envQuart`, `envOne`, all pure scalar facts) drops the section variables
  entirely, so call sites must **not** pass `(I := I) (M := M)`; the error is
  `Invalid argument name 'I' for function …`.  Contrast the tensor-valued
  helpers, which need them.
* When a needed bridge is an equation between a public and a `private`
  constant, do not try to state it.  Consume the public fact about the private
  constant by `exact`/`refine … .trans` at the public constant's type and let
  definitional unfolding do the work; `set_option backward.isDefEq.respectTransparency
  false` (already on in this tree) keeps that cheap.
* `jetSix` (six-term `jetAdd` cascade, constant `94`) and `quadSixH2` (its
  `lrQuadF`-shaped instance) exist only to keep the six-block bookkeeping out
  of the big proofs; the `H¹` sibling `quad_pair_h1` spends ~110 lines on the
  same thing inline.
* The file was developed inside `…H2VB.lean` and split out once that file
  reached 3252 lines (over the 3000-line project limit).  The split is by
  abstraction boundary — shared jet algebra + class 3 stay in `…H2VB.lean`,
  the covariant-arm class moves here — and it also halves the iteration cost of
  the class-2 loop.

## Verification

Targeted `lake build` of this module: **sorry-free, no errors**.
`…H2Pair.lean` rebuilds on top of it with exactly **one** remaining `sorry`
(class 1, `goodH2Pair`).
