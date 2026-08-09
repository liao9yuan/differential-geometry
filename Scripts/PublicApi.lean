import DifferentialGeometry.Tensor.Auxiliary.Perm
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Placement
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Tensor.Exterior.Basic
import DifferentialGeometry.Tensor.Exterior.Pullback
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Tensor.Exterior.Leibniz
import DifferentialGeometry.Tensor.Exterior.ModelDifferentialForm
import DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
import DifferentialGeometry.Tensor.Alternating.Comp

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let api : Array String := #[
    "Equiv.Perm.TwoShuffle", "Equiv.Perm.TwoShuffle.toPerm", "Equiv.Perm.TwoShuffle.ofPerm",
    "Equiv.Perm.TwoShuffle.modSumCongrTwoShuffle", "Equiv.Perm.ThreeShuffle",
    "Equiv.Perm.ThreeShuffle.leftShuffle", "Equiv.Perm.ThreeShuffle.rightShuffle",
    "Equiv.Perm.ThreeShuffle.leftAssocShuffle", "Equiv.Perm.ThreeShuffle.rightAssocShuffle",
    "Equiv.Perm.ThreeShuffle.canonicalLeft", "Equiv.Perm.ThreeShuffle.canonicalRight",
    "Equiv.Perm.ThreeShuffle.sign_canonicalLeft_canonicalRight",
    "Equiv.Perm.ThreeShuffle.nBlock", "Equiv.Perm.ThreeShuffle.pBlock",
    "Equiv.Perm.ThreeShuffle.mBlock", "Equiv.Perm.ThreeShuffle.mnBlock",
    "Equiv.Perm.ThreeShuffle.leftInner", "Equiv.Perm.ThreeShuffle.leftOuter",
    "Equiv.Perm.ThreeShuffle.rightInner", "Equiv.Perm.ThreeShuffle.rightOuter",
    "Equiv.Perm.addAssocPerm", "Equiv.Perm.addAssocPerm_symm_addAssocPerm",
    "Equiv.Perm.sign_addAssocPerm",
    "ContinuousAlternatingMap.wedge_product", "ContinuousAlternatingMap.wedge_mul_assoc",
    "ContinuousAlternatingMap.wedge_antisymm", "ContinuousAlternatingMap.wedge_self_odd_zero",
    "ContinuousAlternatingMap.domDomCongr_finAddFlip_wedge_self",
    "ContinuousAlternatingMap.factorial_nsmul_wedge_product_eq_alternatization",
    "ContinuousAlternatingMap.wedge_product_eq_alternatization",
    "ContinuousAlternatingMap.elementaryCovector_wedge",
    "ContinuousAlternatingMap.uncurrySum", "ContinuousAlternatingMap.curryFin",
    "ContinuousAlternatingMap.uncurryFin", "ContinuousAlternatingMap.uncurryFinAdd",
    "DifferentialGeometry.AnalyticTransfer.multilinearValues",
    "DifferentialGeometry.AnalyticTransfer.linearIsometryEquivRange",
    "DifferentialGeometry.AnalyticTransfer.isClosed_range_comp",
    "DifferentialGeometry.ModelDifferentialForm", "DifferentialGeometry.ModelDifferentialForm.pullback", "DifferentialGeometry.ModelDifferentialForm.extDeriv",
    "DifferentialGeometry.ModelDifferentialForm.extDeriv_extDeriv", "DifferentialGeometry.ModelDifferentialForm.extDeriv_pullback",
    "DifferentialGeometry.DifferentialForm",
    "DifferentialGeometry.DifferentialForm.exteriorDerivativeAtInterior",
    "DifferentialGeometry.DifferentialForm.exteriorDerivativeAt",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_sq",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_add",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_smul",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_wedge",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_pullback",
    "DifferentialGeometry.DifferentialForm.pullback", "DifferentialGeometry.DifferentialForm.pullbackMap",
    "DifferentialGeometry.DifferentialForm.pullback_id", "DifferentialGeometry.DifferentialForm.pullback_comp",
    "DifferentialGeometry.DifferentialForm.pullback_wedge", "DifferentialGeometry.DifferentialForm.pullback_add",
    "DifferentialGeometry.DifferentialForm.pullback_smul", "DifferentialGeometry.DifferentialForm.pullbackLinearMap",
    "DifferentialGeometry.DifferentialForm.pullbackMap_id", "DifferentialGeometry.DifferentialForm.pullbackMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMap_wedge", "DifferentialGeometry.DifferentialForm.pullbackMap_add",
    "DifferentialGeometry.DifferentialForm.pullbackMap_smul", "DifferentialGeometry.DifferentialForm.pullbackMapLinear",
    "DifferentialGeometry.DifferentialForm.deRhamCochainComplex",
    "DifferentialGeometry.DifferentialForm.deRhamCohomology",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackMapCochainMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_comp",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap_id",
    "DifferentialGeometry.DifferentialForm.pullbackMapCohomologyMap_comp"
  ]
  let mut missing : Array String := #[]
  for n in api do
    let parts := n.splitOn "."
    let nm := parts.foldl (fun acc p => Name.str acc p) Name.anonymous
    if !env.contains nm then
      missing := missing.push n
  if !missing.isEmpty then
    for n in missing do
      logError m!"MISSING PUBLIC API: {n}"
    throwError "public API manifest mismatch"
  let charZeroFree : Array String := #[
    "ContinuousAlternatingMap.wedge_mul_assoc",
    "ContinuousAlternatingMap.wedge_antisymm",
    "ContinuousAlternatingMap.wedge_self_odd_zero",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_wedge",
    "DifferentialGeometry.DifferentialForm.exteriorDerivative_pullback"
  ]
  let mut signatureFail := false
  for s in charZeroFree do
    let parts := s.splitOn "."
    let nm := parts.foldl (fun acc p => Name.str acc p) Name.anonymous
    let some c := env.find? nm | throwError m!"missing declaration {s}"
    let ty := toString (← liftTermElabM <| Meta.inferType
      (.const nm (c.levelParams.map mkLevelParam)))
    if ty.contains "CharZero" then
      signatureFail := true
      logError m!"SIGNATURE REGRESSION: {s} must not depend on CharZero"
  if signatureFail then
    throwError "public signature regression detected"
  logInfo s!"public API manifest OK ({api.size} declarations)"
