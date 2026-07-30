import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# Legacy low-base pair import

This module path is retained as an import compatibility shim.  The former
pair-reduced API depended on the obsolete `extraA2Act` decomposition and had no
downstream declaration consumers.  New code should use
`DeTurckRemainderLowBaseAction`, whose `LowBaseActionData.a2` is the canonical
complete second-order action.
-/
