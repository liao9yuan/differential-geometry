# CGTRadialPath

## 2026-07-27 canonical radial lift

`radialFlat` is the intrinsic framed radial segment with a fixed smooth
monotone reparameterization that is constant near both endpoints.
`radialFlat_flat` proves the resulting path is globally `C¹` with endpoint
collars.  `radialFlat_len` proves its Riemannian length is exactly the model
norm of the defining vector.

`radialFlatLift` is the explicit zero-start lift, and `radialLift_one`
identifies its endpoint with the original model vector.  The construction
uses no raw exponential radius and no global covering hypothesis.

Focused verification and the targeted artifact refresh are green.  This brick
is theorem/API 100% and dedicated machinery 100%.  Its next consumer is the
actual inverse-fiber injection in `CGTEvenCover.lean`.  Paper Lemma 4.5 remains
theorem 0% with dedicated machinery about 60%; `intrLoop_ge_cgt`, the
sequence-level injectivity-decay producer, and unconditional metric compactness
remain theorem 0%.
