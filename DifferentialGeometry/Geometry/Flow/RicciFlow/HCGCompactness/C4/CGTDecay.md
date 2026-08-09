# CGTDecay

## State - 2026-07-28

This module is the native sequence-level Cheeger--Gromov--Taylor producer.
From `SeqMetricComplete`, connected sequence members, `SeqBoundedGeometry`, and
`BaseInjBound`, `injDecay_of_bg` constructs the actual
`InjRadiusDecayInput`.  `injDecay_realizes` proves that its stored real
distance realizes the member Riemannian emetric, and `exists_injDecay` is the
small consumer-facing existence theorem returning both pieces.

The proof uses:

- the uniform intrinsic metric/local-diffeomorphism radius from
  `exists_intr_control`;
- `intrBall_vol_ge` for a uniform basepoint small-ball lower bound;
- center shift plus relative Bishop--Gromov comparison for exponential decay
  of arbitrary-center small-ball volume;
- absolute Bishop and intrinsic pullback-volume upper bounds for the CGT
  denominator;
- the pointwise `intrInj_ge_cgt` theorem at the safe scale
  `r0 = s`, `R = 5 * s`.

The existential control radius is selected with classical choice because the
producer returns data; no existential proposition is eliminated directly into
`Type`.  The assembled proof is one large declaration, so only that
declaration carries an increased heartbeat budget.  This is a verification
resource setting, not an extra mathematical assumption.

Focused verification and the exact module refresh passed.  Direct axiom audits
of `injDecay_of_bg`, `injDecay_realizes`, and `exists_injDecay` contain only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.

Honest accounting:

- pointwise CGT injectivity theorem: 100%, dedicated machinery 100%;
- sequence `InjRadiusDecayInput` producer: 100%, dedicated machinery 100%;
- A0/CGT lane: 100%;
- unconditional Theorem 3.9: theorem 0%; the remaining work is the final
  native-input/provider assembly and any separate connectedness obligation;
- whole HCG supporting machinery: about 67%.
