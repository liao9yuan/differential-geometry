# Exact spectral H1 jet identity

`cc_h1_jet_sq` is the public rank-two bridge between the generic
`ccTensorToHs` embedding and the exact order-one spectral identity already
proved for `smoothCcToTensorHs`.

It states that the rank-two spectral `H¹` norm squared is exactly the sum of
the intrinsic tensor `L²` norm squared and the first covariant-derivative
`L²` norm squared.  This avoids introducing a metric-dependent output
comparison constant in class-first low-regularity product estimates.

Focused verification passed with four Lean threads and no warnings.  A
temporary axiom census for `cc_h1_jet_sq` reported only `propext`,
`Classical.choice`, and `Quot.sound`; the temporary print was removed.
