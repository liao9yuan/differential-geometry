# CGTWhiteheadBigon

## State — 2026-07-28

`intrCore_short_inj` is the localized Klingenberg/Whitehead hard producer.  It
proves that two controlled minimizing launches from the same core point to the
same endpoint coincide.

The proof minimizes the bad-pair relation on a compact set, uses endpoint first
variation at both corners to obtain the opposite-velocity matching needed for
a smooth closed geodesic, and uses the exact ratio of the two segment lengths
to form its period.  The contradiction is strict convexity of the explicit
origin energy

```text
z ↦ (1 / 2) * ‖z‖ ^ 2.
```

All geometry remains inside the agreement region.  The proof derives one
strict scale with `L > 2*a`, `a + L < 3*R/4`, and the required curvature slack;
it never replaces the assumed `2*a` curvature scale by `3*a` or `4*a`.

The monodromy, proper-local-diffeomorphism, global cut-locus, and fake
completeness routes were rejected because each would either require a new
unproved global premise or conceal the same short-bigon step.  The implemented
route introduces no new geometric assumption.

The already proved edge-core bridge `intrExt_edge_core` is now exported from
this module for the strict-Jensen consumer; its statement and proof are
unchanged.

Focused verification and the exact targeted refresh passed.  A direct axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`.

Accounting:

- `intrCore_short_inj`: theorem 100%, dedicated machinery 100%;
- localized Whitehead bigon producer: 100%;
- `intrCore_jensen`: theorem 100%, dedicated machinery 100%;
- paper CGT Lemma 4.6: theorem 0%; dedicated machinery is about 90%;
- pointwise CGT producer: theorem 0%; dedicated machinery is about 80%;
- whole HCG supporting machinery: about 63%.

The Whitehead/Jensen lane is closed.  The next frontier is the paper Lemma 4.6
propeller assembly: canonical loop transport, invariant finite-center energy,
and distinct loop iterates.
