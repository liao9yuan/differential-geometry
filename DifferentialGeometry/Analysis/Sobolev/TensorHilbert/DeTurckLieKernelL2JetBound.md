# DeTurckLieKernelL2JetBound.lean — DLa top-separated field bound (in-flight)

## Goal (this dispatch)

Field-level **summed top-separated jetL2** bound for the DLa half of the deTurckLie coefficient,
mirroring `connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated`
(`ConnDiffJetL2Summed.lean`):

```
∑_{i≤a} ‖∇^i (deTurckLieDLaCoeffField g₀ (realizedFam g₀ T T' hδ hδ' s) g_bg)‖²
   ≤ Ktop · (∑_{j<a+3}(‖∇^jT‖²+‖∇^jT'‖²))      -- top window a+2 (= arm0), R-INDEPENDENT Ktop
   +  Kc  · (1 + ∑_{j<a+2 or a+3}(‖∇^jT‖²+‖∇^jT'‖²))
```

`g_bg` is a fixed background metric (T-independent ⟹ Kc). Only the `g₁ = realizedFam` part carries
the top window.

## Route (VALIDATED — no math frontier, but a multi-level structural build)

The field factors (`deTurckLieDLaCoeffField_eq_pairTrace`, ~line 4298) as
`field = (-1)·appCcRS(PT)(X)`, `PT = pairTraceOpDla g₀ g₁ : (6,2)` (g₁-orthonormal-frame
bicontraction), `X = rsDomDomCongr(slotExtendIter(dLaSymCc)) : (2,6)`.
`dLaSymCc = domDomCongr(dLaLoweredG1) + dLaLoweredG1`;
`dLaLoweredG1 = dLaLoweredCc + dLaLoweredPerturbCc`;
`dLaLoweredPerturbCc = appCcRS(slotInsert(perturbSharp))(dLaLoweredCc)`;
`raise(dLaLoweredCc) = dLaKernelRaisedCc` (8-summand, A1 = covGrad(connDiffSection g₁ g₀) the top).

**The only summand reaching the protected top window `∇^{i+2}T` is A1**, appearing at:
- the kernel triangle (A1 slot),
- the perturb `appCcRS`'s `(i'=0, l=i)` cell (perturbSharp undiff · ∇^i dLaLoweredCc),
- the field `appCcRS`'s `(i'=0, l=i)` cell (PT undiff · ∇^i X).

### R-independence linchpin (CONFIRMED)

Both appCcRS frame operators have **R-independent order-0 pointwise `rfns`**:
- `rfns(∇⁰ pairTraceOpDla) ≤ CPT 0` because `exists_rfns_pairTraceOpDla_tgrid` gives
  `≤ CPT 0 · dLaGridWin b 1` and `dLaGridWin b 1 = antidiagonalTupleGrid b 0 = 1`; `CPT` is chosen
  before `T`, so R-independent.
- `rfns(∇⁰ slotInsert(perturbSharp)) ≤ finrank⁵·δ₀²` via `rfns_iCG_slotInsert3_dLaPerturb_le` at 0
  + `rfns_symmS_zero_le_dla` (`≤ finrank²·δ²`, δ≤δ₀). R-independent.

So each `(i'=0,l=i)` top cell = `appCcGdiag i · (R-indep frame const) · (Wt top-sep)`, keeping Ktop
R-independent; every other Leibniz cell reaches ≤ `∇^{i+1}T` (sub-top) ⟹ Kc.

## Pieces (status)

- **PIECE 1** `engineRem_le_dLaGridWin` — reshape the connDiffSection topSeparated engine remainder
  `∑_{k<j} b(j-k)·antidiagonalTupleGrid b (k+1)` into `Cj·dLaGridWin b (j+2)` (pure combinatorial:
  `single_le_grid_dla` + `antidiagonalTupleGrid_mul_le_dla` + `grid_le_dLaGridWin`).  WRITTEN, in file
  before `end DLaGridBrick`.
- **PIECE 2** `exists_rfns_connDiffSection_topsep_dla` — connDiffSection topSeparated jet in
  `dLaGridWin` currency: `rfns(∇^j connDiff) ≤ 2·Kt0·rfns(∇^{j+1}T) + 2·Kc0 j·Cj·dLaGridWin b (j+2)`.
  Consumes `rfns_iteratedCovGrad_connDiffSection_topSeparated_le` (engine, in import cone via
  `CurvatureCoefficientDifferenceJetTower`) + PIECE 1.  WRITTEN, in file.
- **PIECE 3** `exists_rfns_dLaKernelRaised_topsep` — 8-summand kernel triangle twin of
  `exists_rfns_dLaKernelRaised_tgrid`, with `hA1` swapped for PIECE 2 (top-separated) and the other 7
  summands' grid bounds unchanged.  `Ktop_kernel = 128·(2·Kt0)` (2⁷ triangle doubling, R-indep).
  DRAFTED (scratchpad `dla_kernel_twin.lean`); apply after PIECE 1-2 verify.
  This is the dispatched "DLa Step 2" (acceptance №10).

## Remaining field assembly (DESIGN — piece 4, next)

1. **Generic appCcRS (0,i)-cell extractor** `rfns_iCG_appCcRS_topsep_of`: given a Wt top-sep
   `rfns(∇^i Wt) ≤ Wtop·τ + Wrem`, an R-indep order-0 `rfns(∇⁰ Φ) ≤ cΦ0`, and the full grid bound
   `appCcGdiag i·fullsum ≤ gridB`, conclude
   `rfns(∇^i appCcRS Φ Wt) ≤ appCcGdiag i·cΦ0·Wtop·τ + (appCcGdiag i·cΦ0·Wrem + gridB)`.
   Proof: Leibniz → split `fullsum = pΦ0·q_i + (fullsum − pΦ0·q_i)`; `pΦ0·q_i ≤ fullsum` (single
   term ≤ sum); cell ≤ cΦ0·(Wtop·τ+Wrem); rest ≤ fullsum ≤ gridB.
2. Lowered→kernel: `rfns(∇^i dLaLoweredCc) = rfns(∇^i dLaKernelRaisedCc)` via
   `rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq` + `dLaLoweredCc_raise_repr` ⟹ PIECE 3 top-sep.
3. Perturb: apply the generic extractor with Φ=slotInsert(perturbSharp), Wt=dLaLoweredCc,
   Wt top-sep from (2); `hfull` = the `hLT` derivation inside `exists_rfns_dLaSym_tgrid` (re-derive).
4. dLaLoweredG1 top-sep = `2·(2)+2·(3)`; dLaSymCc = `4·dLaLoweredG1` (add + domDomCongr rfns eq);
   X = `fr²·dLaSymCc` (two `rfns_iteratedCovGrad_slotExtend_le` + perm eq).
5. Field: generic extractor with Φ=PT, Wt=X, `hfull` = field-grid `hcell` derivation (re-derive
   from `exists_rfns_pairTraceOpDla_tgrid` + the X-tower bound, mirroring lines 4529-4602).
6. Integrate (mirror `deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_ballUniform`, 4606-4746):
   top → `Ktop·‖∇^{i+2}P‖²`; remainder is a SINGLE `dLaGridWin b (i+3)` currency (piece 2 was built
   in `dLaGridWin` currency, not `boundedFactorGridWindow`, so the whole tower stays one currency).
   `∫ dLaGridWin b (i+3) = ∑_{k<i+3} ∫ antidiagonalTupleGrid b k`, each ball-uniform via
   `antidiagonalTupleGrid_integral_ballUniform_tameWindow` (exactly the 4606 pattern) — no
   `boundedFactorGridWindow` integrator needed.
7. realizedFam wrapper + `jetL2_sum_lowShift a 2 2` (top offset p=2, matching arm0 window a+2), mirror
   `DLaTopSeparated.lean` / `ConnDiffJetL2Summed.lean`.

Estimated field assembly ≈ 450 lines (two `hfull` re-derivations + the sym/X tower dominate). Ktop
shape: `Ktop(i) = appCcGdiag i·CPT0·(fr²·4·(2·1 + 2·appCcGdiag i·Cperturb0))·(128·2·Kt0)` — all
R-independent.

**Wrinkle + resolution (appCcGdiag i is i-dependent in the top coefficient).**  The appCcRS Leibniz
puts `appCcGdiag i` (= `(2·(finrank+1))^i`, `OperatorFieldFibreNormJet.lean:737`) in front of the top
cell, so the per-order top coefficient `Ktop(i)` grows with i.  `jetL2_sum_lowShift` needs a single
`Ktop`.  Resolution: `appCcGdiag` is monotone (base `2·(finrank+1) ≥ 1`), so for `i ≤ a`,
`appCcGdiag i ≤ appCcGdiag a` (`pow_le_pow_right` with `1 ≤ 2·(finrank+1)`); bound `Ktop(i)·w ≤
Ktop_a·w` at the per-order→summed step, `Ktop_a` = the `i:=a` fixed value (still R-independent:
finrank, δ₀, CPT0, Kt0 only).  Do this bounding inside the realizedFam per-order lemma before feeding
`jetL2_sum_lowShift`.

Scratchpad drafts for piece 4 (session-temp, fold into file next session):
`dla_generic_appccrs.lean` (4.1 extractor), `dla_zero_order.lean` (4.2 CPT0/Cperturb0),
`dla_field_pointwise_PLAN.md` (full 4.1–4.7 recipe with exact copy-block line refs).

## Verification status

**PIECES 1-3 VERIFIED GREEN** — focused `lake env lean DeTurckLieKernelL2JetBound.lean` (whole file,
`LEAN_NUM_THREADS=4`, quiet-window waiter) EXIT=0, **zero errors, zero warnings**.  Two fixes were
applied after the first check flagged the kernel-twin tail: (i) restored `have hW_ge1 : 1 ≤ W`
(dropped in the copy; needed by `hA2`'s `nlinarith`); (ii) added a `mul_assoc (128:ℝ) KtopA <τ>`
regrouping hint to the final `linarith` (it treated `KtopA·τ` in `hA1` and `(128·KtopA)·τ` in the
goal as unrelated opaque nonlinear atoms; the hint bridges them as `128·(KtopA·τ)`).  Axiom audit:
`#print axioms` on all three ⇒ `[propext, Classical.choice, Quot.sound]` (audit lines then stripped).

Piece 4 (field lift) NOT built — designed + drafted only (see above + scratchpad).
`(N) ricci_flow_unif_existence` remains **0%**; pieces 1-3 are the kernel top-separation ("DLa Step 2")
of the field-level lift of the 1st of 2 genuinely-missing C₀ constituents (`deTurckLieCoeffField`).
