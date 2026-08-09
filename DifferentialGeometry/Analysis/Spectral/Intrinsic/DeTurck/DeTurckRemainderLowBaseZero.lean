import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# Legacy low-base zero import

This module path is retained as an import compatibility shim.  The former
zero-path API used the obsolete `rhsRefold2Int` decomposition and had no
downstream declaration consumers.  The canonical exact zero-based identity is
now `remainder_low_split` in `DeTurckRemainderLowBaseAction`.
-/
