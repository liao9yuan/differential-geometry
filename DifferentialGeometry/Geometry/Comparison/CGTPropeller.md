# CGTPropeller

## State - 2026-07-28

This module now proves the intrinsic finite-family form of
Cheeger--Gromov--Taylor Lemma 4.6.

The canonical transport is the endpoint of the selected lift of a based loop
followed by the radial path to the input.  `loopTransport_curve` proves
transported controlled curves remain `C1` with the same length, and
`loopTransport_nonexp` turns the Whitehead core minimizing join into the
distance inequality required by the center argument.

The first attempted center route incorrectly asked transport to preserve one
fixed radius-`a` core.  Canonical transport only has the radius estimate
`a -> L + a`.  The corrected route puts a finite alleged orbit in a smaller
radius-`r` ball, uses `intrCore_center` to obtain a unique global center via
the outside-energy barrier, and applies `CenterOfMass.fixed_of_nonexp`.
`loopTransport_ne` then rules out the fixed center.

The orbit chain is complete:

- `intrOrbit_not_finite` excludes a finite permuted inner orbit;
- `intrIter_ne` excludes a positive controlled period;
- `intrIter_ne_of_lt` gives pairwise distinct controlled iterates;
- `loopTransport_norm` and `intrIter_norm` supply the sharp incremental
  `i * L` norm bound;
- `loopIter_exp` and `intrIter_exp` keep every endpoint in the fibre over the
  basepoint;
- `intrIter_family` packages injectivity, fibre membership, and norm control
  for `Fin (N + 1)`;
- `intrFiber_encard_ge` gives base-fibre cardinality at least `N + 1`;
- `intrFiber_count_ge` combines Lemma 4.5 transport with Lemma 4.6 to give the
  same lower bound over every point of the short target ball.

Focused verification passed, and the exact module refresh completed with
3975 jobs.  Direct axiom audits of `intrIter_family`,
`intrFiber_encard_ge`, and `intrFiber_count_ge` report only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Honest accounting:

- paper CGT Lemma 4.6, native finite-family endpoint: theorem 100%,
  dedicated machinery 100%;
- `intrLoop_ge_cgt`: theorem 0%, dedicated machinery about 90%;
- pointwise CGT injectivity producer: theorem 0%, dedicated machinery about
  85%;
- sequence `InjRadiusDecayInput` producer: theorem 0%;
- unconditional Theorem 3.9: theorem 0%;
- whole HCG supporting machinery: about 64%.

The exact remaining frontier for `intrLoop_ge_cgt` is a
multiplicity-sensitive area theorem.  In schematic form it must turn

```text
forall y in S, (m : ENat) <= encard {v in U | exp(v) = y}
```

into

```text
(m : ENNReal) * riemVol(S)
  <= integral over U of the intrinsic exponential Jacobian density.
```

The existing `riemVol_exp_image_le` counts only the image once, and
`riemVol_exp_image_eq` assumes injectivity on its source.  Neither consumes a
pointwise fibre-cardinality lower bound.  The smallest honest implementation
is a countable measurable injective partition for a local diffeomorphism, or
an equivalent local-sheet area formula followed by exhaustion.  No new
geometric assumption is needed.
