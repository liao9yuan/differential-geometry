# LengthBound

## Signature migration

The unique call to `indexForm_nonneg_of_minimising_geodesic` now uses its
weakened interface.  The metric-norm witness and separate global smoothness
hypothesis are no longer passed; all geometric data, variation regularity,
minimizing hypothesis, and endpoint conditions are unchanged.

This is only a call-site migration.  It does not alter the Bonnet--Myers
argument, any public declaration in this file, or the mathematical content of
the length bound.  The retained metric-norm parameter keeps its original public
binder name and position for named-argument compatibility.  Its proof now
records one local compatibility use because the weakened index-form producer
no longer consumes that witness.

## Verification

Static source inspection confirms that this file contains exactly one call to
the migrated theorem and that the two obsolete arguments were removed there.
After the upstream compiled artifact was refreshed, focused verification passed
without warnings.

Local source migration and verification: 100%.  The Bonnet--Myers endpoint and
the wider project receive no completion percentage increase from this
compatibility-only edit.
