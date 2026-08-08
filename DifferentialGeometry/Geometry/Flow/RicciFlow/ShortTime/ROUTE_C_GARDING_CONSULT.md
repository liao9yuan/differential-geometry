# Route-(c) full-slope Rung-3 Gårding consult

## Result: CONTINUE-WITH-CORRECTIONS at the sharp post-peel estimates

The 2026-08-08 source audit refuted the prompt's proposed arbitrary-acted-field
pointwise extension.  `ricciDA_refold`, `ricciConn_refold`, and the public
kernel identity place `nabla^2 P` on the coefficient/path state and put the
independent passenger `U` into the rank-four coefficient.  The private
`rhsSelf_refold` closes only after specializing `P` and `U` to the same tensor.
The reversed expression `C2(P) (nabla^2 U)` has a nonzero second-order
principal symbol in `U`, whereas the original Riemann coefficient action is
zeroth order in `U`.

Existing `edgeRiem_cancel` is already arbitrary in its acted field, but only
after receiving a correctly oriented `hrefold`; the diagonal Palatini producer
does not produce the reversed one.  Consequently this prompt is retained as a
historical audit input.  The route has since adopted the honest diagonal
alternative: keep state=acted=`T`, use an exact path normal form, and estimate
the resulting pairing directly.  No `_bi` wrapper or higher-radius hypothesis
was added.

The exact diagonal layer and principal form are now focused-green:

- `lowBase_path_nf` identifies the actual `AB.a2 T + AB.a1 T` with its complete
  order-zero/order-one/top-deviation path action;
- `appD2_pair_h2` and `appD2_pair_h4` prove the rank-two principal form bound;
- `top_pair_h2_unif`, `top_pair_h4_unif`, and `top_pair_abs_unif` select a
  class-first `H2` cap and absorb the top form into `eta * H4^2` using only the
  `C3` metric class;
- `galArmPair3_diag` and `galRepHs_scale` retain the exact radial factor.  The
  eventual consumer needs a `theta = 0` / `0 < theta` split, but never an
  inverse.

The remaining theorem is not the principal estimate: it is the homogeneous
diagonal residual commutator/Gårding bound after subtracting the absorbed
`<L^2 T, Phi(T) nabla^2(LT)>` form.

The corrected diagonal route has now been pushed through its exact path and
centered algebra.  Focused-green `low0_path_refold`, `b02_raw_nf`, and
`b02_center_nf` perform the diagonal refold without asserting an off-diagonal
low-base identity.  `edgePath_inner_bi`, `edge_swap_h4_unif`, and
`edge_diag_h4_unif` close the raw Cross and diagonal pair estimates.
`edge_center_s_nf` gives the fixed-parameter identity

```text
J_s = L(E0_s T) + (L(D_s T) - D_s(LT))
        - (K_s-K_0)(LT) - Cross_s.
```

At the principal-symbol level the canonical raw top family reduces to six
monomials, and its two fourth-order orientations agree exactly with
`Cross_s`.  Covariantly, the exact argument corner is
`Delta(nabla^2 T)`.  Rewriting it as `nabla^2(Delta T)` produces

```text
nabla(pointwiseTensorCurv g 2 T)
  + pointwiseTensorCurv g 3 (nabla T),
```

and hence an `(nabla^2 Rm(g)) * T` cell.  The externally supplied Pro response
incorrectly simplified this derivative to `(nabla Rm) * T`; the first-order
commutator already contains one curvature derivative.  A complete
normal-frame symbol check also indicates that the transparent
`q/Phi/ricciTop` action on this cell is generally nonzero.  Thus a pointwise
zero theorem is the wrong target.

This does not trigger the binding STOP condition.  The target order is

```text
eta -> exists delta2,R2 -> forall g in C3 -> exists G_g.
```

Only the small caps and coefficients of `H4^2` must be class-uniform.  A
fourth jet of the already fixed smooth `g` may enter the lower constant `G_g`.
The dangerous `(nabla^2 Rm(g)) * T` cell is zeroth order in state derivatives;
the full curvature defect is linear in `T` and uses state jets through order
two.  Its complete coefficient vanishes at `T=0`; paired with `L^2 T` it has the lower shape
`C_g * H2(T)^2 * H4(T)` (or at worst
`C_g * H2(T) * H4(T)`), which Young absorbs into
`eta * H4^2 + G_g * H3^2` without changing `delta2` or `R2`.

The exact non-Green normal form `edge_center_peel` is now focused-verified and
directly refreshed.  It exposes the explicit `2+0` and `1+1` Leibniz corners,
the existing Cross term, and the curvature defect without hiding them in an
opaque remainder or differentiating the test.  The class-first top-kernel
fibre bound, principal-face pairing, and nonzero curvature-defect pairing are
now focused-verified and directly refreshed.  The next substantive estimates
are the sharp `P20`, `P11L/P11R`, and self-low carrier pairing bounds.  The Cross term in the
peel cancels exactly with the Cross added by `b02_center_nf`; it must not be
charged twice.  The route stops only if those estimates leave a naked or
metricwise coefficient in front of `H4^2`, require an `H4/H5` state radius, or
force a cap to be chosen after `g`.

## Fixed audit boundary

The original supplied consult was written against remote commit
`94a94eeebe4b6cb24963423761b2d1a43627cdfe`.  The later Pro response audited
remote snapshot `cda17d2ecb951945c9f0a6bfb60faf6b3ca36d11`; the current live
branch head is `70cbba6385ec0a70804236e7731c71ce116971a4`, which contains the
public diagonal self-refold and the documentation correction.  The untracked
peel source is therefore not attributed to either remote snapshot.  The false
arbitrary-passenger refold remains rejected.  The correction here concerns the
derivative ledger and the quantifier order of the lower Gårding constant; it
does not claim the final analytic theorem is proved.

## Historical consult prompt (refuted at Gate A)

You are auditing and solving Route B for the uniform short-time Ricci-flow
existence lane.  The target is a homogeneous, class-first theorem, tentatively
named `lowbase_full3_unif`, in a future
`ShortTime/LowRegBgC2Pair.lean`.  Its quantifier order must be

```text
forall eta > 0,
  exists delta2 R2,
    0 < delta2 < 1/3 and 0 < R2 <= 1 and
    forall g in the C3 metric class,
      exists G >= 0,
        forall symmetric T with ||T||H2 <= R2 and fibreBound T delta2,
          2 * <L^2 T, L (AB.a2 T + AB.a1 T)>
            <= eta * ||T||H4^2 + G * ||T||H3^2,
```

where `L = 1 - Delta_nabla` and
`AB = lowBaseData g gBase T ...`.  The lower term must remain homogeneous
`G * H3^2`.  Only the later Galerkin/rest consumer may weaken it to
`G * (1 + E3)^2`.

First verify, term by term, two viability gates rather than assuming them.

1. **AUDIT RESULT: FAILED off the diagonal.**  The prompt asked to recombine
   the complete `C0+C2` whole slope using
   `LowBaseInternal.topKernel_eq`, `LowBaseInternal.c2_eq`, the exact
   `rhsSelf_refold` identity (currently private), `lowData_split`,
   `exists_edgePairRef`, and `edgeRiem_cancel`.  Check every sign and
   permutation.  The full low-base `C2` is not definitionally `edgeTopPair`:
   `ricciTop` has two moving traces and must not be forced into
   `edgePairMono`.  Do not create a separate `ricciTop` formal partner unless
   this whole-slope route is proved impossible.
   The diagonal recombination remains valid; the requested arbitrary acted
   field extension reverses the coefficient/passenger roles described above.
2. **AUDIT RESULT: the supplied scaling adapter remains valid.**  Put
   `X = finiteEigenCombo g F c`,
   `theta = min 1 (R / ||galLowView ...||)`, and
   `T = theta * symmS X`.  The supplied finite spectral split gives, at
   `a = 1`, `b = 2`,
   `sum_F weight3*c_i*coeff(A)_i = <L^2 X, L A>`.
   Transport `theta` and `symmS` by exact linearity/self-adjointness, using
   `symmS_smul`, `symmS_remSymmS`, `symmS_sub`,
   `rawTensorConnLapSmooth_domDomCongrSection`, and
   `inner_domDomCongrSection_swap`.  Never divide by `theta`; in particular,
   no `1/theta` may enter the lower coefficient.

The local supplied exact APIs are `finite_pair_split`, `finite_symm_scale`,
and the monomial
polarized identities `edgePair_l2_bi`, `edgePair_inner_bi`, and
`edgePair_green_bi`.  In the latter, the raised coefficient slots contain
`P`, the unraised test slots contain `V`, and the acted field `U` appears only
through `nabla^2 U`, then `nabla U` after one Green identity.  These lemmas do
not provide a complete polarized low-base top family.

The central analytic task is to pass `L` through the complete closed slope,
show every commutator is genuinely lower order and bounded by `G * H3^2`, and
make every coefficient multiplying `H4^2` uniformly small using only the
class-first caps `delta2,R2`.  Existing `edgePair_pair_le` is only the Rung-0
diagonal estimate and cannot be quoted as Rung 3.  Existing high-order tame
commutator estimates that require an `H4/H5` state ball are not admissible.

Forbidden dependencies are: `galRepJet_le g 4`, an `H4/H5` state radius, a cap
chosen after `g`, or any metricwise non-small coefficient in front of `H4^2`.
A fourth jet of the fixed smooth `g` is permitted only inside the lower
constant `G_g`, where it multiplies at most one `H4` factor and at least one
actual lower state norm before Young.

Return `STOP-AND-REDESIGN` with the exact failed identity and smallest genuine
obstruction if any of the following is unavoidable: the C0+C2 refold fails;
the test/state scaling fails; a common cap must depend on `g`; a fourth metric
jet is required in a class-uniform cap or `H4^2` coefficient; a high state
radius is required; or a metricwise non-small coefficient remains in front of
`H4^2`.  Otherwise give the exact Lean statement,
dependency order, smallest new lemmas, and focused verification evidence.

## Current accounting

- `lowbase_full3_unif`: unstated, **0%**.
- Rest-only Rung-3 theorem: unstated, **0%**.
- Complementary finite spectral split: **100% verified**.
- Polarized monomial formal-partner/Green API: **100% verified as stated**.
- Exact diagonal path normal form: **100% verified**.
- Class-first principal-form absorption: **100% verified**.
- Exact centered path/refold algebra and raw Cross estimates: **100% verified**.
- Exact complete-edge peel `edge_center_peel`: **100% verified**.
- Class-first centred top-kernel fibre bound and principal-face pairing:
  **100% verified**.
- Nonzero `B * G` curvature-defect pairing: **100% verified**.
- Dedicated fixed-background Route-(c) machinery: approximately **96%**; the
  remaining denominator is the sharp post-peel corner/carrier
  estimates and the diagonal residual Gårding theorem.
- `ricci_flow_unif_existence`: **0%**.
- Whole HCG project: approximately **3%**.
