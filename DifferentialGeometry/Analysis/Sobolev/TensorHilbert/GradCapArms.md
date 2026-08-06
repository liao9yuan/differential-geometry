# `GradCapArms.lean` — the arm calculus of the `∇P`-capped currency

Created 2026-08-04, brick A1-CUR-2 session 2.  Landed sorry-free on the first
focused check.

## Why it exists

Session 1 built the `Λ₁` cap (`gradCapOfBall`), the base shift
(`atgwShift`/`armShift`) and the capped integration step (`atgwCapToJet`), and
smoke-tested them on `lc0VB` through the hand-rolled two-arm workhorse
`atgwCapArm`/`atgwCapFold`.  The assembly session then had to run the same
manoeuvre on ~20 further arms across five summands, with product trees of depth
up to four (`lc0AMix` is a five-factor nest).  Doing that with the raw
`atgwFold`/`armShift` calls means repeating a six-line bound shape at every
node.

`HasCapWin g₀ P X K` names that shape once:

```
∀ i x, |∇ⁱX|²(x) ≤ K i · atgw (gridBase g₀ (∇P) x) (i + 1)
```

## The one fact that makes it work

**The capped level `i + 1` is closed under `appCcRS`.**  `atgwFold` at offsets
`(u, v) = (0, 0)` sends windows at `i' + 1` and `l + 1` to a window at
`n + 0 + 0 + 1`.  So an arbitrary product tree of once-differentiated arms stays
at level `n + 1`, and `capJet` (= `atgwCapToJet` at `w = 1`) turns that into the
`range (n + 2)` budget.  There is no accumulation with depth — only the
constants grow.

Contrast: in the UNSHIFTED base a product of two offset-`+2` arms lands at
`n + 3`, and shifting the FOLDED window afterwards only gets back to `n + 2`,
which still integrates to `range (n + 3)`.  The gain is strictly per-arm: each
arm's shift drops one level, two arms drop two, and the fold gives one back.
That is why `capOfArm` must be applied at the leaves, never at the root.

## The API

| name | role |
| --- | --- |
| `capOfArm` | leaf-in: a `bP`-offset-`+2` window becomes capped, price `shiftConst Λ (i+1)` |
| `capOfBnd` | leaf-in: a state-free arm enters for free (`1 ≤ atgw`) |
| `capApp` | `appCcRS`; the closure property above |
| `capAdd`/`capSub`/`capSmul`/`capNeg` | linear algebra (2-subadditivity, `t²`) |
| `capReindex`/`capDdc` | source- and target-slot permutations: isometries |
| `capSlotExt`/`capIter` | slot extension: one/`w` dimension factors |
| `capMono`/`capCongr` | weaken the constant / transport along an equality |
| `capJet` | leaf-out: `‖∇ⁿX‖² ≤ K n · (∑Kint) · (1 + ∑_{j<n+2}‖∇ʲP‖²)` |

An arm whose radius-free window is at offset `+1` (traces, cometric casts,
`P` itself) is weakened to `+2` by `antidiagonalTupleGridWindow_mono` before
`capOfArm`; there is deliberately no separate `+1` entry point, because
`atgwShift` needs `k ≥ 1` and the level-`0` window is empty.

## Traps

* `capIter`'s induction needs `slotExtendIter g r s (w+1) X = slotExtend g (r+w)
  (s+w) (slotExtendIter g r s w X)`, which holds by `rfl`; the valence indices
  `r + (w+1)` vs `(r+w) + 1` are defeq, so the `rw [← hrec]` goes through.
* `capOfBnd` is the right entry for `permCoeff`: a uniform bound per order from
  `exists_bound_riemannianFiberNormSq_smoothCcTensor`.  When several
  permutations occur, take the constant to be `∑ ρ : Equiv.Perm (Fin d), S ρ i`
  — `Equiv.Perm (Fin d)` is a `Fintype`, so `Finset.single_le_sum` gives a
  permutation-uniform bound in one line instead of a case split.
* The `simpa using armShift …`/`simpa using atgwFold …` pattern is what
  normalizes `i + 0 + 1` to `i + 1`; writing the offsets as literals instead
  produces goals that `exact` will not close.

## Verification

Focused check passed, first attempt, ~19 s.  No sorries, no new
`maxHeartbeats` beyond the file-level `1600000` this layer already uses.

---

## 2026-08-04 (A1-CUR-2 session 3): three more calculus lemmas

* `capOfP` — the perturbation itself is capped, at constant `Λ`.  `|∇ⁱP|²` is
  `|∇P|`'s grid entry of weight `i−1` for `i ≥ 2`, and the two pointwise caps
  cover `i = 0, 1` (the window is `≥ 1`, so a constant is a legal bound there).
  This is what lets an arm **linear in `P` itself** — the curvature head
  `lrCurvF g₀ P` of the Palatini residual — enter the currency at all.
* `capOfDP` — `covGrad g₀ 0 2 P` is capped, on the order-one cap alone.  Its
  jets ARE the base, so only `i = 0` is exceptional.
* `capDdc0` — `domDomCongrSection` at valence `(0,s)` is a capped-window
  isometry, from the public
  `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection`.  This is the
  `(0,s)` sibling of `capDdc`: the Palatini normal forms (`lrQuadF`, the
  `refoldKernel` identity) permute output slots with `domDomCongrSection`,
  the pair traces with `rsDomDomCongrSection`, and both occur in the same
  proof.

Private helper `capBaseLe` (a single grid entry of the shifted base sits inside
its own window) backs `capOfP`/`capOfDP`.

Trap: its hypothesis is `j ≤ i`, not `j ≤ i + 1` —
`antidiagonalTupleGrid_le_window` wants a STRICT `k < w`, and `omega` reports
the failure with the bound variable already generalized away, which reads as a
context-free goal.

Verification: focused check green; used by `SelfLowArmCaps.lean`, and the
targeted build of `…DeTurck.LowRegC01JetTower` (9610 jobs) is green with all
three axiom-clean.
