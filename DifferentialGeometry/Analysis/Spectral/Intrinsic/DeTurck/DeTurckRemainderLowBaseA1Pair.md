# DeTurckRemainderLowBaseA1Pair

## Role

The first-order sibling of `c2_pair_lip` / `a2_pair_lip`
(`DeTurckRemainderLowBaseC2Lip`): the pairwise (two-state) estimate for the
canonical low-base **first-order** coefficient and for both adjacent-scale
completions of its action.

Written for Lane B of the `(N)` `ricci_flow_unif_existence` endgame, whose
consumer `lowA1_lip`
(`Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/LowRegOperatorTime.lean`)
asked for exactly this object.

## What is in the file

* `a1PairArith`, `sqSumLe` (private) — pure real bookkeeping that merges the two
  producers' differently-shaped moduli into one envelope and turns
  `J₀ ≤ X²`, `J₁ ≤ Y²`, `X + Y ≤ Z` into `J₀ + J₁ ≤ Z²`.
* `c1_pair_lip` — the two-jet `H²` bound
  `lowJetSq g 2 (A_T.C0 - A_U.C0) + lowJetSq g 2 (A_T.C1 - A_U.C1) ≤
   (K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N))²`
  on a common spectral `H²` ball.  This is precisely the input shape of
  `a1_diff` (`DeTurckRemainderLowBasePair`).
* `a1_pair_lip` — the operator-norm consequence:
  `‖A_T.a1Hi - A_U.a1Hi‖`, `‖A_T.a1Lo - A_U.a1Lo‖ ≤
   K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N)`.

## Reuse (nothing new was proved about the geometry)

Everything geometric was already in tree; this module is pure packaging.

* `c0Diff_h2_tame` (`DeTurckRemainderLowBaseH2Pair`) — the `H²` jet of the
  `C0` difference, modulus `(B₀R·(1+A)·(D₄+D₃+D₂+N) + B₁R·A₄·(D₃+N))²`.
* `c1Diff_tame` (`DeTurckRemainderLowBaseLip`) — the `H²` jet of the `C1`
  difference, modulus `(B₀·D₃ + B₁·N + B₁·A·N)²`.
* `lowC0_sub` / `lowC1_sub` (`DeTurckRemainderLowBaseLip`) — identify the field
  differences of `lowBaseData` with the path integrals `lowC0Diff` / `lowC1Diff`
  that the two producers actually bound.
* `a1_diff` (`DeTurckRemainderLowBasePair`) — two-jet coefficient bound ⟹ both
  completed actions.

Placement: `DeTurckRemainderLowBaseC1Lip` would be the natural home by name, but
it sits *below* `DeTurckRemainderLowBaseLip` in the import order and therefore
cannot see `c1Diff_tame`.  The lowest module that sees both halves plus
`a1_diff` is one above `DeTurckRemainderLowBaseH2Pair`, hence this file.

## The mathematics: why the modulus is not uniform

`a2_pair_lip` gets `C · ‖T - U‖_{H²}` with **no** dependence on higher jets,
because the second-order coefficient is *algebraic* in the state (metric
inverses).  The first-order coefficient is `∇`-linear in the state with
metric-inverse coefficients, so the difference telescopes as

```
C₁(T) - C₁(U) = (P(g_T⁻¹) - P(g_U⁻¹)) ∗ ∇T  +  P(g_U⁻¹) ∗ ∇(T - U)
```

and the **first** summand costs `‖T - U‖ · ‖T‖_{H³}`.  That is the `B₁ · A · D₂`
slot of `c1Diff_tame`, and it is sharp — not a lossy artefact.

### Consequence: `lowA1_lip`'s `hHiPair` is unsatisfiable

`lowA1_lip` asks for `‖a1Hi(T) - a1Hi(U)‖ ≤ C‖T - U‖_{H³}` with **one** `C`
valid for all `T, U`.  `lowCoreData` cuts off only in the spectral `H²` norm
(`lowRadial`), so the third jet of the state is unbounded on that ball.  Take
`T` oscillatory with `‖T‖_{H²} ≤ ρ/2` and `‖T‖_{H³} = A → ∞`, and `U = T + εV`
with `V` a fixed low-frequency bump.  Then

* `‖T - U‖_{H³} ≍ ε`;
* the cross term gives `‖a1Hi(T) - a1Hi(U)‖ ≳ ε·A` (no cancellation: the two
  summands are `εV ∗ ∇T` and `g⁻¹ ∗ ε∇V`, of sizes `εA` and `ε`).

So the ratio is `≍ A`, unbounded.  `lowA1_lip`, `lowA1_square` and
`lowRegA1_square` are therefore *vacuously* conditional; warnings were added to
their docstrings.

`hLoPair` is different: `a1Lo` is `H² → H¹`, so its coefficient is read at the
`H¹` jet, which costs only the *second* jet of the state — and that **is**
controlled by the `H²` cutoff.  `hLoPair` is plausibly true; it is simply not
derivable from the current `c0Diff_tame` / `c1Diff_tame`, whose moduli carry a
lossy `(1 + A + A²)⁴` / `B₁·A·N`.

### What the square actually needs next

Two separate items, in this order:

1. **An `A₄`/`D₄`-free pair estimate.**  The one-state bound
   `lowData_a1_coeff` controls `lowJetSq g 2 (C0) + lowJetSq g 2 (C1)` by
   `K₀(1 + J₃S)⁶` — the *third* jet only.  A sharp pair estimate should
   therefore also need only `J₃`, i.e.
   `‖a1Hi(T) - a1Hi(U)‖ ≤ K A · ‖T - U‖_{H³}` on `{J₃ ≤ A²}`.  The `A₄`, `D₄`
   in `c0Diff_h2_tame` are a lossy artefact of that lane's telescope, not
   intrinsic.
2. **A dense-extension lemma for locally Lipschitz core maps.**  Even with (1),
   the conclusion of `lowA1_lip` can only be `Continuous (lowA1Hi …)`, never
   `LipschitzWith`.  `dense_lipschitz` does not apply.  The needed lemma: a map
   on a dense subspace of a normed space that is Lipschitz on every bounded
   set extends continuously to a complete codomain (Cauchy filter ↦ Cauchy
   image, then `DenseInducing.continuous_extend`).  With that, the `∀ v` square
   follows from `radialA1_pair`'s core square by `DenseRange.induction_on`
   exactly as it does today.

## Verification

Focused check green; targeted module build green.  `#print axioms` on both
public theorems: `propext, sorryAx, Classical.choice, Quot.sound`.

The `sorryAx` is **inherited, not new**: this file contains no `sorry`.  It
comes from `goodH2Pair` and `lieCovH2Pair`
(`DeTurckRemainderLowBaseH2Pair.lean:215` and `:275`), the two declared
frontiers of the sibling `H²`-pair lane, which feed
`selfLow_pair_h2 → c0Diff_h2_tame`.  Discharging those two makes
`c1_pair_lip` / `a1_pair_lip` axiom-clean with no change here.

## Lessons

* `c0Diff_h2_tame` and `c1Diff_tame` deliver moduli in *different* shapes
  (`(1+A)·(D₄+D₃+D₂+N) + A₄·(D₃+N)` versus `D₃ + N + A·N`).  Merging them by a
  single scalar lemma (`a1PairArith`) taking every coefficient as an explicit
  real, proved with `mul_le_mul` chains and a final `nlinarith`, is far more
  robust than trying to `nlinarith` the whole degree-3 inequality in place.
* When feeding `a1PairArith` from `c1Diff_tame`, pass `nrm := N` (with
  `le_rfl`) rather than the literal norm: bounding the literal-norm version and
  *then* trying to compare with the `N` version goes the wrong way round and
  `linarith` cannot recover it.  Monotonise `c1Diff_tame`'s conclusion first
  (`pow_le_pow_left₀`), then do all arithmetic in `N`.
* Proof irrelevance carries the `δ < 1` witness across `lowC0_sub` / `lowC1_sub`
  and `c0Diff_h2_tame`'s internal `lt_of_le_of_lt hδ_le (by norm_num)`: `rw`
  followed by `exact` closes it, no transport lemma needed.
* Structuring the endgame as `sqSumLe X Y Z _ _ … ?_ ?_` lets Lean unify the two
  giant `lowJetSq (… .C0 - … .C0)` atoms from the goal instead of forcing them
  to be retyped by hand.

## Project accounting

### 2026-07-30 update: the low pair frontier is closed

The public theorem `a1Lo_pair_lip` now gives the completed `H2 -> H1`
operator difference estimate using only `R`, the two state `H3` jet
envelopes, and the `H2`/`H3` difference envelopes.  Its conclusion has
the scalar modulus

`K * R * (1 + A + A^2)^2 * (D3 + D2 + N)`.

In particular, neither an `A4` state envelope nor a `D4` difference
envelope occurs.  The proof combines the now-unconditional
`c0Diff_tame`, `c1Diff_tame`, and the completed `a1Lo_diff` transfer.
The older discussion above remains useful as the record of why the high
`a1Hi` global-Lipschitz route is false, but its claim that the low
D4-free estimate is still open is superseded by this update.

Focused verification and the exact module refresh are GREEN.  The source
contains no `sorry`, `admit`, `axiom`, or `whnf`.

Project accounting remains separated: `ricci_flow_unif_existence` is
still at 0% with its existing endpoint placeholder; the dedicated
uniform-existence machinery is approximately 77%; the whole HCG
compactness project remains in the low single digits.

* `ricci_flow_unif_existence` (the `(N)` endpoint): still one `sorry`, **0%**.
* The Lane-B first-order square that this estimate was supposed to unlock:
  **not unlocked**, and now known to be unlockable only after items (1) and (2)
  above.  What this file delivers is the honest form of the estimate — the
  first-order sibling of `a2_pair_lip` — which is roughly the packaging half of
  item (1); the sharpening (dropping `A₄`/`D₄` and absorbing `D₂`/`N` into
  `‖T - U‖_{H³}`) is the remaining analytic half.
