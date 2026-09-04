# Morse level sets: universe-polymorphic carrier

## Purpose

`LevelSetSpace` should preserve the universe of its manifold carrier instead of forcing that carrier
into universe zero. This is the minimal bridge needed by generic finite-dimensional manifold users.

## Source change

- Generalized the explicit carrier binder of `LevelSetSpace` from `Type` to `Type*`.
- Made its result universe-inferred with `Type _`.
- Preserved the declaration name and mathematical definition; no other level-set API was changed.
- The remaining explicit `Type` in `MorseHalfSpace` was intentionally retained because it is a fixed
  real finite-dimensional model, not a generic manifold carrier.

## Verification status

The generalized `LevelSetSpace` passed a warning-free focused check and explicit
named module refresh.  No level-set chart declaration or mathematical proof was
changed; downstream manifold-instance modules may consume the refreshed type.
