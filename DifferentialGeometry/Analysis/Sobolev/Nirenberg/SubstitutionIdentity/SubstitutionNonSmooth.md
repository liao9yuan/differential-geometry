# SubstitutionNonSmooth

## Raw master producer

`master_raw_nonsmooth` is the canonical pre-Young producer. It contains the
coercivity and triangle-inequality part formerly nested inside
`nirenberg_master_inequality_nonsmooth` and assumes only the data that proof
uses: global L2 data for `u` and its weak partials, the weak-partial identities,
the cutoff and translation room, the compact outer domain, and the exact
four-term substitution identity.

The existing after-Young theorem now calls this producer, so there is one proof
of the raw inequality. Forcing integrability, the cutoff derivative bound, the
Friedrichs-Korn bound, and the test-square bound remain only on the after-Young
consumer.

Focused verification and the required named module refresh both passed without
warnings. Downstream files may now consume the refreshed raw producer.
