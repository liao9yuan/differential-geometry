import DifferentialGeometry.Tensor.Auxiliary.Perm
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Pullback
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Tensor.Exterior.Leibniz
import DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm
import DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
import DifferentialGeometry.Tensor.Alternating.Comp

open Batteries.Tactic.Lint Lean Elab Command

run_cmd do
  let env ← getEnv
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let excluded := #[`docBlame, `docBlameThm]
  let prefixes := ["Equiv.Perm", "ContinuousAlternatingMap", "DifferentialForm",
    "ModelDifferentialForm", "DifferentialGeometry.AnalyticTransfer",
    "DifferentialGeometry.DifferentialForm"]
  let mut found := false
  for (decl, _) in env.constants.toList do
    let n := decl.toString
    if prefixes.any (fun p => n.startsWith p) then
      for linter in checks do
        if excluded.contains linter.name then
          continue
        if ← liftCoreM <| shouldBeLinted linter.name decl then
          let msg ← liftTermElabM <| linter.test decl
          if let some m := msg then
            found := true
            logInfo m!"LINT_FAIL {decl}\n{m}"
  if found then
    throwError "linter failures found in de Rham foundation modules"
  logInfo "linters passed on de Rham foundation modules"
