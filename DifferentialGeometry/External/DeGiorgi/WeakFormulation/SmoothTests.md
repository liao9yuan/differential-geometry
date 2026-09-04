# SmoothTests

## Signed smooth-test bridge

- `IsSolution.bilin_eq_zero_smooth` shifts a signed smooth compactly supported
  test by `C * η`, where `η` is one on its support and valued in `[0,1]`.
- Both shifted tests are nonnegative, so the subsolution and supersolution
  inequalities give equality; witness independence and bilinear additivity
  recover the original signed test.
- No positive-part `H₀¹` closure, new assumption, or classical derivative of
  the weak solution is used.
- The first check exposed only a final equality-orientation mismatch after the
  two zero identities were rewritten.  Closing that scalar equality directly
  fixed it; focused verification and the required named refresh then passed
  without warnings.
