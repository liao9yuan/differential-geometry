# DeTurckRemainderLowBaseH2VB — status, findings, lessons

Sibling of `DeTurckRemainderLowBaseH2Pair.lean` in Lane A of the `(N)` endgame.
Two jobs:

1. the **shared `H²` jet-algebra layer** (moved verbatim out of `…H2Pair.lean`,
   which was about to breach the 3000-line limit);
2. **class 3** of the second-order five-class telescope: the vector–bundle zero
   head `lc0VB`.

A third sibling, `DeTurckRemainderLowBaseH2Cov.lean`, was later split off to
carry **class 2** (`lieCovH2Pair`, the `lieCovR4` covariant arm); it imports
this module and reuses its jet algebra unchanged — in particular `jetInterp3`,
`pairFold3`, `amixScalar`, `appH2`, `slotH2`, `reindexJet`, `rspermH2`,
`rspermSub` and `wXiSelfTame` all found a second consumer there.

Import order: `…LowBaseLip` → `…H2VB` → `…H2Cov` → `…H2Pair`.  Everything lives in
`DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral` under the same names it
had when it was `private` in `…H2Pair.lean`, so no call site changed.

## Status — `lake build` GREEN, sorry-free

| declaration | role |
|---|---|
| `jetNn / jetSmul / jetAdd / sqAdd2 / jetMono` | local jet algebra (moved) |
| `prodOfParam / wgtAmgm / specInterp3 / jetSumSq / jetSumLe / jetInterp3` | exact spectral interpolation `J3 ≤ C·R·A4` (moved) |
| `sqTwo / quadFour / amixScalar` | scalar re-pairing endgame (moved) |
| `slotL2 / slotH2 / reindexJet / reindexSub / trSub / trJet / appH2` | slot / reindex / trace / product transfer at `H²` (moved) |
| `pairFold3` | **new** — folds `(b0·D3 + b1·D3 + b1·a·D3)²` into `(2(b0+b1)² + 2b1²)·(pl2·u)`; used twice (mcd and wXi) |
| `icgZero / jetZero / wXiZero / wXiSelfTame` | **new here** — single-state `H²` bound `J2 (wXi g gT g) ≤ (Bs R · A)²`, recovered from the public `wXi_sub_tame` at `U := 0`, `gU := g` |
| `rspermL2 / rspermH2 / rspermSub` | output-slot permutation is a jet isometry and is additive |
| `ipHead / ipForm / ipSub` | `ipLowCc om = app₂₃₁(ipHead, Ext²om)`, and it is additive |
| `vbRank0Smul / vbMcdUnit / vbPKSlot / vbmcdRel / vbmcdPerm` | the head identity `vbMcdArm g gm = rsPerm(VBPerm)(Ext(mcd g gm g))` |
| `vbmcdH2 / vbmcdSub` | its `H²` jet transfer, bounded **and** difference, at one factor of `finrank` |
| `riemLiveEq` | `lc0RiemLive g gm = pureTrace g gm 2` |
| `vbH2Pair` | **class 3, proved** |

## The class-3 route as executed

`vb_refold_rf` + `lc0VBFormRF` give

```
lc0VB g gm = 2 • app₂₄₂( lc0RiemLive g gm ,
                          app₂₁₄( vbMcdArm g gm , ipLowCc (wOmega g gm g) ) )
```

and `wOmega_refold` gives `wOmega g gm g = app₀₃₁(Tr₁ , connDiffLoweredCc g gm)`
with `Tr₁ = lc0TraceRF g gm 1 (Equiv.refl (Fin 3))`.  So the telescope has five
levels, all read at `J2`:

| level | bounded | difference |
|---|---|---|
| `Tr₁` | `trace1_h2_bdd` | `trace1_pair_h2` (`N`-currency) |
| `cd = connDiffLoweredCc = wXi g gm g` | `wXiSelfTame` → `(Bs R · a)²` | `wXi_sub_tame` with `D2 := D3` |
| `W = wOmega` | `appH2 0 3 1` | Leibniz split |
| `Ip = ipLowCc W` | `appH2 2 3 1` + two `slotH2` | ditto |
| `Vm = vbMcdArm` | `vbmcdH2` + `mcd_h2_bdd` | `vbmcdSub` + `mcd_pair_h2` with `D2 := D3` |
| `Lv = lc0RiemLive` | `trace2_h2_bdd` | `trace2_pair_h2` |

The inner arm carries `mcd ~ (1+A)` against `wOmega ~ A`, i.e. an `A²`
passenger, inadmissible against a difference.  Exactly as in class 4, **both**
`A`-carrying producers are instantiated at the interpolated third-jet size

```
a := √(Cip · R · A4)      (jetInterp3, applied to P and to Q)
```

so the envelope `pl2 := (1+a)²` appears squared, and the same hoisted scalar
lemma `amixScalar` closes: `(1+a)⁴ ≤ 8(1 + (Cip R A4)²)` lands the whole excess
in the single `A4`-linear arm of

```
(B0 R · (1+A) · (D4 + D3 + D2 + N) + B1 R · A4 · (D3 + N))²,
B0 R = √(8·Bh R),   B1 R = √(8·Bh R)·Cip·R.
```

`D2 := D3` is fed to both connection-difference pair moduli, legitimate because
`J2 (T−U) ≤ J3 (T−U)` (`jetMono`).

## What was found while routing this

* **The planned shortcut does not exist.**  The recipe suggested re-deriving the
  `vbMcdArm` jet transfer from the *public* `vbMcdArm_rfns_le` /
  `vbMcdArm_l2_le` by integrating per order, "avoiding the section equation".
  That works only for the **single-state** bound.  The telescope also needs
  `J2 (vbMcdArm g gT − vbMcdArm g gU)`, and a per-state norm bound says nothing
  about a difference: the difference needs *linearity*, i.e. the section-level
  identity `vbMcdArm g gm = rsPerm(VBPerm)(slotExtend (mcd g gm g))`.  Both
  routes to that identity (`vbPK_eq_slotExt` in `LieCorr0CoeffL2JetBound`,
  `vbPK_slotExt_lip` in `…LowBaseLip`) are `private`, so the ~120-line fibre
  chain `vbRank0Smul → vbMcdUnit → vbPKSlot → vbmcdRel → vbmcdPerm` had to be
  re-established here.  It transfers verbatim; the `rfl`-`show` step that
  unfolds the private `vbMcdArmFib` works from another module because privacy is
  name resolution, not a definitional barrier — only public constants are named.
* **`wXi_h2_low` is private** (C1Lip:1809), so the single-state `H²` bound for
  `connDiffLoweredCc` is not directly available.  Recovered instead from the
  public `wXi_sub_tame` at `U := 0`, `gU := g`, which needs `wXi g g g = 0`
  (`wXiZero`, from `PDE.DeTurck.connDiff_self`) and `jetZero`.
* **No upstream publicization was needed** for class 3 either — but for a
  different reason than class 4: not because the shortcut worked, but because
  cloning the fibre chain into this module was cheaper than rebuilding the
  10 000-line `…LowBaseLip` after dropping a `private`.
* **`positivity` was avoided** for the constant ladder: the constants (`Cw`,
  `Cin`, `Cout`, `Cipp`, `Bt1`, …) are opaque locals, so explicit
  `mul_nonneg`/`sq_nonneg` chains are used, matching class 4.

## Lean lessons banked

* `set_option linter.unusedSectionVars` is off project-wide in `lakefile.toml`
  but `lake env lean` still reports it; the fix is the `omit …` line the linter
  prints (needed on `vbRank0Smul`).
* Cloned Lip proofs that use `show` to *change* the goal trip
  `linter.style.show`; mechanical `show` → `change`.
* `simp only [X]` zeta-delta-unfolds tactic-`let` constants (`M5`, `Wb`, `Bh`,
  `B0`, …) reliably in this toolchain; `set … with h` + `rw [h]` re-exposes the
  definition at the point of use.  Both patterns carry the whole ladder.
* Splitting the algebra layer out was worth it purely for iteration speed:
  this module builds in ≈ 150–200 s, `…H2Pair.lean` in ≈ 450 s.

## Verification

Targeted `lake build` of this module: **sorry-free, no errors, no warnings**.
`…H2Pair.lean` rebuilds green on top of it with exactly its two remaining
`sorry`s (classes 1 and 2).
