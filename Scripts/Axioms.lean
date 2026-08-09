import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Leibniz
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Tensor.Exterior.Pullback
import DifferentialGeometry.Tensor.Exterior.Basic

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let heads : Array String := #[
    "ContinuousAlternatingMap.wedge_mul_assoc",
    "ContinuousAlternatingMap.wedge_antisymm",
    "ContinuousAlternatingMap.factorial_nsmul_wedge_product_eq_alternatization",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_sq",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_wedge",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_pullback",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_comp"
  ]
  let mut failed := false
  for s in heads do
    let parts := s.splitOn "."
    let nm := parts.foldl (fun acc p => Name.str acc p) Name.anonymous
    if !env.contains nm then
      throwError m!"missing declaration {s}"
    let axioms ← liftCoreM <| Lean.collectAxioms nm
    if axioms.contains ``sorryAx then
      failed := true
      logError m!"{s} depends on sorryAx"
    let bad := axioms.filter fun a =>
      a != ``propext && a != ``Classical.choice && a != ``Quot.sound
    if !bad.isEmpty then
      failed := true
      for a in bad do
        logError m!"{s} depends on unapproved axiom {a}"
  if failed then
    throwError "axiom closure check failed"
  logInfo "axiom closures OK"
