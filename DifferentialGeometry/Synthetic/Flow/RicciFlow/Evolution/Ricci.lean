import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciFromRiemann

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Evolution of Ricci Curvature

Compatibility facade for the Ricci evolution API. The implementation is split
across:

* `RicciCore.lean` for the public evolution interfaces;
* `RicciTrace.lean` for Ricci-slot trace and reaction algebra;
* `RicciTraceCoordinate.lean` for finite-basis time-trace commutation;
* `RicciFromRiemann.lean` for constructors from Riemann evolution.

New code should import the narrow file it actually needs when possible.
-/
