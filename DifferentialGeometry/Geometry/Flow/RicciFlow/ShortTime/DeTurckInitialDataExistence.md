# DeTurckInitialDataExistence

## 2026-08-05 - reuse the intrinsic representation bridge

`deTurckRicci_solution_with_jointReg` now imports and applies
`deTurck_rem_repr` from the intrinsic DeTurck layer.  The former local
slot-symmetry helper and the duplicated realized-RHS proof were removed; the
public theorem and its hypotheses are unchanged.

Focused verification and the targeted module build passed.  The extracted
bridge is also covered by the ShortTime axiom census and uses only the standard
three axioms.
