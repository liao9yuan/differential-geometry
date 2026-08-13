# Route C Rung-3 collaborator handoff

## 1. Repository checkpoint

- Authoritative checkout: `E:\\testdifferential-geometry-ste-align`
- Branch: `codex/short-time-existence-align`
- Remote-visible HEAD: `4b1cc723d694e87ee9a112b3d71e0892773d632c`
- Commit subject: `Handoff`
- The working tree was clean when this document was written.
- All Route-C subagents were interrupted and all Route-C file claims were
  released. No Lean or Lake process was left running.

Important verification boundary: commit `4b1cc723d` contains both verified
declarations and two source-complete but **unverified** declarations. Do not
infer GREEN merely because a file is committed.

The running source of truth remains `ROUTE_C_PLAN.md`; this document is a
self-contained technical request for an external collaborator.

## 2. End goal and quantifier order

Write

```text
L := 1 - Delta_nabla
r := ||T||_{H2_g}
y := ||T||_{H3_g}
z := ||T||_{H4_g}
V := L^2 T
```

The Route-C Rung-3 target has the quantifier order

```text
for every eta > 0,
  choose delta_2 and R_2 before the class metric g varies;
  for every g in the prescribed C3(gBase,Lambda) class,
    choose G_g >= 0 after g is known;
  for every admissible symmetric T with delta <= delta_2 and r <= R_2,
    2 |<V, centered-edge(T)>| <= eta z^2 + G_g y^2.
```

The placement of `G_g` is essential. It may depend on the full fixed smooth
metric `g`, including fixed higher metric jets. Such dependence is harmless
only for terms with at most one factor `z` and at least one actual lower state
norm (`r` or `y`). It may not multiply a naked `z^2`, because then the radius
would have to be selected after `g`.

The intended final theorem `edge_center_h4_unif` is not yet stated and remains
theorem-level **0%**.

## 3. Exact algebra already closed

The public theorem

```text
Analysis/Spectral/Intrinsic/DeTurck/EdgeCenterCommutator.lean
  edge_center_peel
```

is focused-verified, directly refreshed, and directly axiom-audited. Its axiom
audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

For fixed path parameter `s`, it defines

```text
C := Phi_s - Phi_0
A := rhsSelfLow_s + K_0
B := lieRefold2_s + C - 2 s ricciTop_s
G := nabla(pointwiseTensorCurv_g(T))
     + pointwiseTensorCurv_g(nabla T)
HLT := nabla^2(LT)
```

and three transparent product-rule corners

```text
P20  := Tr_g ((nabla^2 B) (nabla^2 T))
P11L := Tr_g ((slotExtend nabla B) (nabla^3 T))
P11R := Tr_g ((nabla slotExtend B) (nabla^3 T)).
```

`Cross` is the sum of the two complete raw top-pair orientations

```text
Q_s(LT) T + Q_s(T) LT.
```

The exact identity is

```text
J_s
  = L(A T)
    + (B-C) HLT
    - B G
    - P20 - P11L - P11R
    - Cross.
```

This is a non-Green peel. It does not differentiate the test `V`, introduces
no H5 norm, and asserts no false arbitrary-passenger low-base refold.

## 4. Paired faces already verified

The following source theorems are GREEN and directly refreshed. Direct axiom
status is stated separately so that refresh status is not mistaken for an
axiom audit.

1. Complete cross sum:

   ```text
   ShortTime/UnifEdgeSwapPair.lean
     edge_swap_h4_unif
   ```

   It bounds the sum of both raw top-pair orientations by

   ```text
   C R z^2.
   ```

   The proof uses the non-Green formal partner identity, with the two products
   `LT in L6, nabla^2 T in L3, V in L2` and
   `T in Linfinity, nabla^2 LT in L2, V in L2`.

   No separate direct axiom audit is recorded in its same-name note.

2. Principal face `(B-C) HLT`:

   ```text
   ShortTime/UnifTopKerPair.lean
     bcD2_pair_h4_unif
     bcD2_pair_abs_unif
   ```

   Here

   ```text
   B-C = lieRefold2_s - 2 s ricciTop_s.
   ```

   The pointwise class-first coefficient cap is supplied by
   `RicciTopFibreBound.lean` (`dagTop_cap_unif`, `ricciTop_cap_unif`, and
   `topKer_cap_unif`).

   A direct axiom audit reports only `propext`, `Classical.choice`, and
   `Quot.sound`.

3. Curvature-defect face `B G`:

   ```text
   ShortTime/UnifEdgeDefectPair.lean
     bg_pair_abs_unif
   ```

   This gives

   ```text
   2 |<V, B G>| <= eta z^2 + G_g y^2.
   ```

   It is important that this theorem does not claim that the
   `nabla^2 Rm` coefficient vanishes.

   A direct axiom audit reports only `propext`, `Classical.choice`, and
   `Quot.sound`.

## 5. Correction to the earlier coefficient-level STOP diagnosis

The earlier remote note in `pasted-text.txt` was right that a q-only
calculation cannot decide cancellation of the complete block, but two later
points change the route:

1. `pointwiseTensorCurv g 2 T` already contains

   ```text
   (nabla Rm_g) T + Rm_g nabla T.
   ```

   Therefore the outer covariant derivative in `G` really can contain
   `(nabla^2 Rm_g) T`. The expression is not uniformly controlled by the C3
   class.

2. Complete cancellation of that term is nevertheless unnecessary for the
   target quantifiers. The coefficient `B` vanishes at `T=0`, so the resulting
   pairing has at least one actual lower state factor and only one H4 factor;
   schematically it is `C_g r^2 z` (or a coarser `C_g r z`), not `C_g z^2`.
   Young's inequality puts it into

   ```text
   eta z^2 + G_g y^2,
   ```

   with `G_g` chosen after the fixed smooth metric `g` is known.

Thus the selected route does **not** need a theorem saying that the complete
`nabla^2 Rm` coefficient is zero. It needs homogeneous state estimates that
keep the lower state factor visible.

## 6. Verified H3 infrastructure

The following reusable producers are verified and directly axiom-audited:

```text
ShortTime/UnifInvCoeffH3.lean
  inv_coeff_h3_unif

HCGCompactness/UnifGridRS.lean
  grid_rs_const_le

ShortTime/UnifAppH3.lean
  appRS_h3_sup_unif
```

`appRS_h3_sup_unif` is the class-first tame product estimate with supplied
pointwise caps:

```text
sum_{j<4} ||nabla^j appCcRS(Phi,W)||_2^2
 <= C [ B0^2 sum_{j<4} ||nabla^j Phi||_2^2
      + A0^2 sum_{j<4} ||nabla^j W||_2^2 ],
```

where `A0` and `B0` are pointwise fibre caps for `Phi` and `W`.

This is the correct product currency for the remaining algebraic coefficient
chain. A pure `H3 x H3` estimate is too coarse because it loses homogeneity.

## 7. Source written but not verified at the pause

### 7.1 `fullRaised_h3_unif`

```text
ShortTime/UnifAlgCoeffH3.lean
```

The source is complete and contains no deliberate `sorry`, but **no focused
verification was run** before the pause. Its same-name note correctly records
the theorem as 0% until checked.

The intended statement gives a class-first H2 radius and an affine H3 bound
for

```text
slotInsertEndoCc g 1 (fullRaisedEndoField g gm),
```

using `fullRaisedEndoField_diff_split`, `inv_coeff_h3_unif`, and the parallel
identity part.

### 7.2 `phi_dev_h3_unif`

```text
ShortTime/UnifPhiDevH3.lean
```

The source is complete and contains no deliberate `sorry`, but its first
focused check was interrupted almost immediately to reduce memory pressure.
There is no Lean diagnostic to report. It is **not GREEN**.

Its intended output preserves the H2 realization radius and pointwise
`(C R)^2` deviation cap while proving

```text
sum_{j<4} ||nabla^j(Phi_s-Phi_0)||_2^2
 <= [C (||T||_{H3}+||T'||_{H3})]^2.
```

The proof uses `inv_coeff_h3_unif` and the order-generic `trace_l2_le` and
`ricci_l2_le` APIs.

## 8. Missing H3 coefficient producers

No source was completed for the following declarations before the pause:

```text
lieRefold_h3_unif
ricciTop_h3_unif
edgeCoeff_h3_unif
```

The desired final fixed-s coefficient theorem is, schematically,

```text
theorem edgeCoeff_h3_unif :
  exists rho C > 0, forall g in C3(gBase,Lambda),
    forall admissible symmetric T with ||T||H2 <= rho and s in [0,1],
      let B := lieRefold2_s + (Phi_s-Phi_0) - 2 s ricciTop_s
      (pointwise fibre cap for B)
      and
      sum_{j<4} ||nabla^j B||_2^2 <= (C ||T||H3)^2.
```

The pointwise cap may honestly retain the supplied fibre radius `delta`; the
range-four jet estimate must be homogeneous in the actual state norm.

The planned algebraic routes are:

```text
lieRefold2:
  moving inverse pair coefficient x symm(T)

ricciTop:
  fullRaised -> dagTop
  fullRaised x T -> daWeight -> daTrans
  daTrans x dagTop -> ricciTop.
```

All arrows are algebraic operator-field applications. They should use
`appRS_h3_sup_unif`, the verified inverse coefficient estimate, pointwise
Morrey control of the actual `T`, and structural slot/permutation jet
identities. Do not route through connection difference; that introduces the
wrong derivative budget.

## 9. First remaining genuine paired inequality: the corners

Once `edgeCoeff_h3_unif` is available, the next theorem should be

```text
ShortTime/UnifEdgeCornerPair.lean
  edge_corner_h4_unif
```

with conclusion of the form

```text
2 |<V, P20 + P11L + P11R>| <= C r z^2
```

or the harmless variant `C (r+r^2) z^2` on `r <= 1`.

The intended three-dimensional estimates are:

```text
P20:
  ||nabla^2 B||_L6 * ||nabla^2 T||_L3 * ||V||_L2

P11L/P11R:
  ||nabla B||_Linfinity * ||nabla^3 T||_L2 * ||V||_L2.
```

The H3 coefficient/state bounds give `C y^2 z`; spectral log convexity gives

```text
y^2 <= r z,
```

and hence the required `C r z^2`.

This route deliberately avoids both unavailable alternatives:

- estimating `nabla^2 T` in `Linfinity`, or
- estimating `nabla^3 T` in `H1`.

Either alternative asks for a class-uniform spectral-H4 to raw-four-jet bridge,
which is not available under a C3 metric class.

## 10. Second remaining genuine inequality: the self-low carrier

The remaining term is

```text
2 |<V, L(A T)>|,
where A = rhsSelfLow_s + K_0.
```

The desired endpoint is

```text
ShortTime/UnifSelfLowPair.lean
  self0_pair_abs_unif

2 |<V, L(A T)>| <= eta z^2 + G_g y^2.
```

The required quantitative split is:

- state-independent/fixed-carrier higher metric jets may enter a coefficient
  `C_g` selected after `g` and multiply only a lower shape such as `y z`;
- nonlinear top heads must have a class-first coefficient and retain an actual
  H2 factor, giving `C r z^2` after interpolation;
- no term may leave `C_g z^2`.

Nearby metricwise/affine tower theorems are not enough: they lose the
homogeneous state factor and would force the H2 cap to depend on `g`.

## 11. Requested collaborator verdict

Please inspect the remote-visible commit above and answer these questions in
order.

1. Do `fullRaised_h3_unif` and `phi_dev_h3_unif` have mathematically correct
   statements and proof architecture? If not, identify the first exact false
   inequality or Lean API mismatch.
2. Give the shortest project-native proof chain for `lieRefold_h3_unif` and
   `ricciTop_h3_unif`, including the exact existing declarations to reuse.
3. Confirm or refute the `(6,3,2)` / `(infinity,2,2)` corner route above. Check
   the tensor valences and the precise derivative count; do not replace it by a
   generic H4-to-four-jet comparison.
4. Propose the weakest honest statement for the self-low carrier estimate,
   preserving the quantifier order `caps before g`, `G_g after g`.
5. Classify the result as `CONTINUE`, `CONTINUE-WITH-CORRECTIONS`, or
   `STOP-AND-REDESIGN`. A STOP verdict should name the first unavoidable term
   of one of these forbidden forms:

   ```text
   H5(test),
   class-uniform fourth metric jet,
   cap selected after g,
   C_g z^2 with no actual lower state factor.
   ```

Please distinguish:

- a theorem already verified in Lean;
- source present but unverified;
- a routine missing API;
- a genuinely new analytic inequality;
- a mathematical obstruction.

## 12. Suggested verification order on a larger-memory machine

Run one Lean process at a time with four threads and 6144 MB:

1. focused check `UnifAlgCoeffH3.lean`;
2. if GREEN, directly refresh only `UnifAlgCoeffH3`;
3. focused check `UnifPhiDevH3.lean`;
4. if GREEN, directly refresh only `UnifPhiDevH3`;
5. perform direct axiom audits for the two declarations;
6. only then implement and check the Lie and Ricci-top H3 producers.

Read the full diagnostic set from each failed run before changing the source.
Do not run a broad project build at this stage.

## 13. Honest project accounting at handoff

- Exact fixed-s peel `edge_center_peel`: 100%.
- Cross, principal face, and curvature-defect paired estimates: 100% each.
- Reusable inverse/application H3 infrastructure: 100%.
- `fullRaised_h3_unif`: source written, theorem verification 0%.
- `phi_dev_h3_unif`: source written, theorem verification 0%.
- Complete coefficient theorem `edgeCoeff_h3_unif`: unstated, 0%.
- Corner theorem `edge_corner_h4_unif`: unstated, 0%.
- Self-low carrier theorem `self0_pair_abs_unif`: unstated, 0%.
- `edge_center_h4_unif`: unstated, 0%.
- Downstream full low-base Rung-3 theorem: 0%.
- Dedicated Route-C infrastructure: approximately 96%.
- Whole HCG compactness program: approximately 3%.

The current mathematical verdict is **CONTINUE-WITH-CORRECTIONS**. The exact
algebra frontier is closed; the live frontier is homogeneous H3 coefficient
control followed by the two paired estimates above.
