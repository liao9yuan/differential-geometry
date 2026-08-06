import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace DifferentialGeometry.Topology.Homotopy

universe u v w

open ContinuousMap

structure HomotopyEquivUnder {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    {Z : Type w} [TopologicalSpace Z] (toBase : C(X, Y)) (fromBase : C(X, Z)) where
  toFun : C(Y, Z)
  invFun : C(Z, Y)
  map_toBase : toFun.comp toBase = fromBase
  map_fromBase : invFun.comp fromBase = toBase
  left_inv : ContinuousMap.HomotopyRel (invFun.comp toFun) (ContinuousMap.id Y) (Set.range toBase)
  right_inv : ContinuousMap.HomotopyRel (toFun.comp invFun) (ContinuousMap.id Z) (Set.range fromBase)

namespace HomotopyEquivUnder

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z] {toBase : C(X, Y)} {fromBase : C(X, Z)}

theorem map_toBase_apply (e : HomotopyEquivUnder toBase fromBase) (x : X) :
    e.toFun (toBase x) = fromBase x :=
  congrArg (fun f : C(X, Z) => f x) e.map_toBase

theorem map_fromBase_apply (e : HomotopyEquivUnder toBase fromBase) (x : X) :
    e.invFun (fromBase x) = toBase x :=
  congrArg (fun f : C(X, Y) => f x) e.map_fromBase

end HomotopyEquivUnder

end DifferentialGeometry.Topology.Homotopy
