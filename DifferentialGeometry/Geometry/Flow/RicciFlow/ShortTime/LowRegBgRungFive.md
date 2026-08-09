# LowRegBgRungFive.lean

## Role

This sibling ports the complete rung-five Galerkin arm estimate and energy
closure from `LowRegRungFive.lean` to an arbitrary fixed DeTurck background
`g_bg`.  The spectral basis, Sobolev scale, trajectory, and energy remain based
at the state metric `g₀`.

## Source state

The file provides the five intended public declarations:

* `armOrder4Bg`;
* `galArmMass5OrdBg`;
* `lowregRung5OrdBg`;
* `IsRung5OrdBg`;
* `lowregRung5PackBg`.

The scalar binder order and the diagonal proof bodies are preserved.  The only
mathematical substitutions are the second metric slot in `lowBaseData`,
`coreN`, `lowregNfun`, `lowData_split`, and `lowRegSeedMass`, together with the
already verified background versions of the order-three/order-four arms,
Galerkin arm vector, and force split.  The private scalar helper `mul3Le5` is
duplicated locally because its diagonal counterpart is private.  No parallel
analytic API or new hypothesis was introduced, and the diagonal rung-five file
was not edited by this port.

## Verification

Focused verification passed without local diagnostics after the rung-four
export became fresh.  The targeted module refresh also passed, and the
resulting `LowRegBgRungFive.olean` is newer than the source.  Static review
found no `sorry`, `admit`, added axiom, heartbeat override, inferred theorem
result, or residual diagonal background slot.

Accordingly this isolated fixed-background rung-five brick is 100% complete,
and the conditional rung-three/four/five porting subphase is 100% complete.
This is still bootstrap infrastructure: `lowreg_loMassBg` is unstated and
unproved (0%), while the headline `ricci_flow_unif_existence` theorem remains
0%.  The broader route-(c) background/adapted machinery is approximately 60%;
the next frontier is the background gate/adapted package and higher-rung mass
driver, not another pointwise coefficient estimate.
