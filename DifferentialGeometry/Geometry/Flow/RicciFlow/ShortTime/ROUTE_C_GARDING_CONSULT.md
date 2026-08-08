# Route-(c) full-slope Rung-3 Gårding consult

## Fixed audit boundary

Audit the RicciFlower Route-(c) redesign from remote commit
`94a94eeebe4b6cb24963423761b2d1a43627cdfe`.  The current local worktree also
contains focused-verified but not yet remote-visible spectral and monomial
pairing adapters; treat their statements below as supplied lemmas, not as
evidence that the analytic theorem is already closed.

## Consult prompt

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

1. Recombine the complete `C0+C2` whole slope using
   `LowBaseInternal.topKernel_eq`, `LowBaseInternal.c2_eq`, the exact
   `rhsSelf_refold` identity (currently private), `lowData_split`,
   `exists_edgePairRef`, and `edgeRiem_cancel`.  Check every sign and
   permutation.  The full low-base `C2` is not definitionally `edgeTopPair`:
   `ricciTop` has two moving traces and must not be forced into
   `edgePairMono`.  Do not create a separate `ricciTop` formal partner unless
   this whole-slope route is proved impossible.
2. Verify the Galerkin scaling.  Put
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

Forbidden dependencies are: `galRepJet_le g 4`, a fourth varying-metric jet,
an `H4/H5` state radius, a cap chosen after `g`, or any metricwise coefficient
in front of `H4^2`.  `H4` may occur only as the energy absorbed by `eta`.

Return `STOP-AND-REDESIGN` with the exact failed identity and smallest genuine
obstruction if any of the following is unavoidable: the C0+C2 refold fails;
the test/state scaling fails; a common cap must depend on `g`; a fourth metric
jet or high state radius is required; or a metricwise non-small coefficient
remains in front of `H4^2`.  Otherwise give the exact Lean statement,
dependency order, smallest new lemmas, and focused verification evidence.

## Current accounting

- `lowbase_full3_unif`: unstated, **0%**.
- Rest-only Rung-3 theorem: unstated, **0%**.
- Complementary finite spectral split: **100% verified**.
- Polarized monomial formal-partner/Green API: **100% verified as stated**.
- Dedicated fixed-background Route-(c) machinery: approximately **92%**.
- `ricci_flow_unif_existence`: **0%**.
- Whole HCG project: approximately **3%**.
