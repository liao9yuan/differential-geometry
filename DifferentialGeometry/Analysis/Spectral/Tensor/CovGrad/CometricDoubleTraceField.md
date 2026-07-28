# CometricDoubleTraceField

## 2026-07-27 metric pairing API

The public theorem `cometricLmodel_inner` now records that the model cometric
raise inverts metric lowering on an arbitrary model covector.  The proof is the
existing exact inverse-metric-sharp calculation, moved to the module that owns
`cometricLmodel`; the old parabolic theorem remains a compatibility wrapper.

The source check is currently blocked before elaboration by a temporarily
missing `LeviCivita.Torsion` object file while another lane rebuilds the shared
geometry dependency tree.  No proof error has been observed.

