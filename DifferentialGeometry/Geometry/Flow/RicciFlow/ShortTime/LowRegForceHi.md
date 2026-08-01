# LowRegForceHi

## Result

`force_hi_smooth` identifies the lifted `H²` forcing almost everywhere with
the genuine order-two smooth Ricci--DeTurck nonlinearity along any smooth
family realizing the lower solution field.  The fixed DeTurck background is
kept as the independent parameter `g_bg`.

The proof is the injectivity bridge suggested by the spectral scale:

1. `lowReg_force_smooth` identifies the lower `H¹` forcing with the order-one
   smooth nonlinearity;
2. the supplied high-to-low forcing identity identifies the inclusion of the
   `H²` forcing with that same lower forcing;
3. `deTurckSmoothN_incl` identifies the inclusion of the order-two smooth
   nonlinearity with the order-one value;
4. injectivity of `tensorHsInclusion` lifts the equality back to `H²`.

This route does not assert a global map from every `H³` state to an `H²`
nonlinearity.  Such a map would be too strong for the second-order passenger
term.  The conclusion is instead the correct time-field identity along a
smooth representative, and it naturally uses `symmS F`.

## Verification

The persistent LSP worker reported no diagnostics after the final small edit.
The focused check and the targeted module refresh passed.  Direct axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`; the file contains
no `sorry`, `admit`, `axiom`, `whnf`, or `trace` marker.

Opening this new file in the persistent LSP initially caused its worker to run
an implicit setup-file refresh because part of the dirty import closure lacked
current artifacts.  The server was kept alive and no second server was
started.  Future new-file LSP sessions should first verify that the import
closure has current `.olean` files; already-open files remain suitable for the
fast saved-edit loop.

## Remaining frontier

This closes the high forcing identity only under the existing smooth-family
realization hypotheses `F`, `hpin`, and `hball`.  It does not yet construct that
representative from the low-regularity solution packet or assemble the final
uniform-existence endpoint.

Honest accounting: `ricci_flow_unif_existence` remains unstated here and its
existing endpoint proof still has a placeholder, so the theorem itself is 0%.
Its dedicated uniform-existence machinery is approximately 70% complete.  The
whole HCG compactness project remains in the low single digits.
