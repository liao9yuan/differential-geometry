# Busemann line product

## Scope

This module adds the smallest algebraic product producer after the verified
complete Busemann-gradient flow.  It uses the universe-polymorphic native
subtype `{x : M // b x = 0}`, introduces no manifold structure on that subtype,
and adds no metric structure on the product.

The forward map uses the sign convention

`(z, t) |-> busemannFlow (-t) z`,

and its inverse sends `y` to the zero-level point obtained by flowing for time
`-b(y)`, together with the coordinate `-b(y)`.  The two inverse laws use only
`busemannFlow_add`, `busemannFlow_value`, and `busemannFlow_zero`.

`busemannProdHomeo` promotes this exact equivalence to a homeomorphism without
putting a manifold structure on the zero level.  Forward continuity is the
joint continuity supplied by `busemannFlow_smooth`, composed with
`(z, t) |-> (-t, z)`.  Inverse continuity combines continuity of the smooth
Busemann function with the same joint flow map; `Continuous.subtype_mk` records
that the flowed point lies in the raw zero-level subtype.

The same file also records `busemann_deriv_ne`: the unit-gradient identity rules
out a zero manifold derivative at every point, with no level-set hypothesis.

`busemannProdDiffeo` is the smooth promotion.  It takes one explicit continuous
linear equivalence from the generic ambient model to `MorseModel (m + 1)` and
uses `I.transContinuousLinearEquiv e` only locally.  Boundarylessness and the
ambient manifold instance are transported to that model; `isCrit_trans_iff`
then transfers the already proved noncriticality of the Busemann function.
The canonical regular-level charted space and manifold instance are local
`letI`s in the result type, so this construction introduces no global instance.

For the forward map, the regular-level inclusion is first transported from the
Morse model back to `I`, then paired with smooth negated time and composed with
the joint smooth Busemann flow.  For the inverse, the map
`y |-> flow (-b(y)) y` is transported from `I` to the Morse ambient model and
factored smoothly through the zero level by `contMDiff_levelSet_factor`; its
second component is the smooth function `-b`.

## Public source exports

- `busemannProdEquiv`
- `busemannProdHomeo`
- `busemann_deriv_ne`
- `busemannProdDiffeo`

All four names are at most twenty characters.  No `sorry`, `admit`, axiom,
wrapper predicate, global charted-space instance, metric structure, or extra
hypothesis was introduced.

## Verification state

The first focused checks failed at two local type boundaries.  The algebraic
equivalence needed the standard local removal of the conflicting tangent-space
instances, and the Morse level/critical APIs exposed the universe issue
described above.  Replacing the restricted Morse carrier with the raw subtype
and stating regularity as nonvanishing of the native `mfderiv` removed both
boundaries without changing the product map or adding assumptions.  The final
focused check and the downstream-required named refresh are warning-free GREEN.

The homeomorphism promotion subsequently passed a warning-free focused check
and its downstream-required named refresh.  It reuses the checked equivalence
and joint flow smoothness exactly as planned; no definitional-equality or
subtype-continuity gap remained.

The smooth promotion is source-written against the finalized universe-generic
regular-level API.  Its first focused check stopped before the map proofs at
three local setup errors: the transported boundaryless range goal remained
`range (e ∘ I) = univ`; the local transported `IsManifold J` instance did not
reduce through the `let J`; and the unindexed smooth-diffeomorphism notation
failed to elaborate its `∞` grade in this dependent `letI` result type.  The
repair was correspondingly narrow: the range equality now uses the explicit
transported-range formula, `I.range_eq_univ`, and surjectivity of the linear
equivalence; the transported manifold instance is inferred after unfolding
`J`; and the diffeomorphism grade is written explicitly.  The second focused
check accepted all three repairs but isolated a grade mismatch in the native
regular-level API: the ambient Busemann hypotheses provide
`IsManifold I ((top : N-infinity) : WithTop N-infinity) M`, while
`manifoldLevelSetChartedSpace`, `manifoldLevelSetIsManifold`, and the two
smooth level-set maps currently demand `IsManifold I (top : WithTop
N-infinity) M`.  Transporting the model preserves the former grade but cannot
strengthen it to the latter.  Consequently the canonical level-set calls and
both smooth-map calls fail to synthesize `IsManifold J top M` before their
actual proof bodies are checked.  This was a precise upstream assumption-grade
API blocker, not a failure of the product-map route.  The four regular-level
declarations and their needed internal producers were subsequently lowered to
the genuinely used smooth grade and refreshed.  Against that repaired API,
the complete `busemannProdDiffeo` now passes a warning-free focused check and
its downstream-required named refresh; this verifies both model transports,
both canonical local instances, the forward/inverse smoothness proofs, and a
fresh importable artifact for the unified axiom audit.

## Project accounting

The formal Cheeger--Gromoll splitting theorem remains unstated and is **0%**.
Its dedicated P1c machinery is approximately **92--94% verified**: the
algebraic product bijection, regularity producer, raw product homeomorphism,
regular-level manifold structure, and smooth product diffeomorphism are
focused GREEN, while the product-metric/isometry assembly still remains.  The
smooth product substage is verified and refreshed; it does not by itself
establish the final isometric product endpoint.
