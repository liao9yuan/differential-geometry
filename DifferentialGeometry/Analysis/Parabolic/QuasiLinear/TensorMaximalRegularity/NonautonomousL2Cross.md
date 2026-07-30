# NonautonomousL2Cross

## Role

This sibling module supplies the finite-time `L²` coefficient estimate and
adjacent-scale compatibility facts needed to lift the non-autonomous
maximal-regularity fixed point.

## Current state

- `memLp_clm_affine` packages an affine pointwise operator bound into `MemLp`
  and gives the radius-free norm estimate
  `L * ‖u‖ + Real.sqrt T * Z₀`.
- The proof uses the scalar `L²` majorant formed from the constant field and
  the pointwise norm of `u`; it does not require time differentiability.
- `duhamel_incl` identifies the included `H^(a+2)` Duhamel field with its
  canonical `H^(a+1)` realization for arbitrary tensor valence and a supplied
  resolvent compactness witness.

## Verification

Focused verification passed for the complete module. The initial check exposed
only a missing object file for the higher `NonautonomousL2` import; narrowing
the module to its actual lower-layer dependencies removed that artifact
dependency. No exact refresh was used.

## Project status

The two declarations targeted in this generic brick are complete (100%).
The planned `nonautL2_lift` theorem itself remains unstated here (0%); these
affine-integrability and Duhamel-inclusion prerequisites are roughly half of
its generic cross-scale setup, with coefficient compatibility and fixed-point
identification still separate. The uniform low-regularity existence theorem
remains unstated and unproved (0%); its dedicated machinery is still only
approximately 88--90% and the geometric coefficient/nonlinear bootstrap
frontiers remain independent of this module.
