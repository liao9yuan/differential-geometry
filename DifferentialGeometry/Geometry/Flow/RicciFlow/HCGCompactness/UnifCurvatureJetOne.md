# UnifCurvatureJetOne

## Role

This module assembles the intrinsic pointwise first-curvature-jet split from
the connection-insertion term, the differentiated Palatini term, and the fixed
background curvature derivative.

## Current state

`nablaRm_split` proves the intrinsic `(1,3)` identity

`∇Rm(g₀) = connection insertion + differentiated Palatini + ∇Rm(gBase)`.

`unifRmJetOne` then gives the complete class-uniform first curvature-jet
envelope in `iterCov`/`normSq0S` currency, and `unifRmSecOne` transports it to
the `iteratedCovGrad`/`riemannianFiberNormSq` currency used by the short-time
consumers. Both theorems now hold for every `Λ ≥ 1`; their former `Λ < 2`
arguments were removed by routing through the arbitrary-`Λ` A0 connection,
order-zero curvature, and differentiated Palatini producers. The class input
stops at metric-jet order three. No lowering defect or fourth metric derivative
appears.

`unifRmOpOne_of` is also public.  It retains the sharper covariant
Riemann-operator estimate with both fixed-background caps supplied, which is
the exact first-jet input needed by the rank-two curvature-action package; no
all-rank or all-order curvature envelope is introduced.  Its closed coefficient
has the reusable sign lemma `rmOneOpC_nonneg`.

Focused verification and the exact targeted module refresh pass. Direct axiom
audits of `unifRmJetOne` and `unifRmSecOne` report only `propext`,
`Classical.choice`, and `Quot.sound`. The file has no placeholders; the exact
build reported only pre-existing warnings in imported modules.

## Proof route

The connection-insertion term is estimated in the `g₀` norm from the banked
connection-difference and order-zero curvature bounds. The differentiated
Palatini term comes from `unifPalatini1`, and compactness controls the fixed
background derivative. Metric comparability transfers the latter two from
`gBase` to `g₀`; the pointwise operator estimate is finally converted to the
rank-five tensor norm and then to smooth-section currency.

## Next consumer

Use `unifRmSecOne` to close the `j = 1` static-field `Ksup` packet.  Use the
supplied-cap operator face `unifRmOpOne_of` in the separate rank-two
curvature-action producer for the finite `H²` realization radius.

## Project accounting

`ricci_flow_unif_existence` remains 0%. This is dedicated machinery for the
now-closed `a = 1` curvature envelope. The class-uniform `Ksup` consumer and E6
assembly remain separate downstream work.
