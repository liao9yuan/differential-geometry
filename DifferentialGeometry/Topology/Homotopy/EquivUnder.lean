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

structure BaseCommutingHomotopyEquiv {B : Type u} [TopologicalSpace B] {X : Type v}
    [TopologicalSpace X] {Y : Type w} [TopologicalSpace Y] where
  toBase : C(B, X)
  fromBase : C(B, Y)
  toHomotopyEquiv : ContinuousMap.HomotopyEquiv X Y
  left_comm : ContinuousMap.Homotopy (toHomotopyEquiv.toFun.comp toBase) fromBase
  right_comm : ContinuousMap.Homotopy (toHomotopyEquiv.invFun.comp fromBase) toBase

namespace BaseCommutingHomotopyEquiv

variable {B : Type u} [TopologicalSpace B] {X : Type v} [TopologicalSpace X]
variable {Y : Type w} [TopologicalSpace Y]

def refl (i : C(B, X)) : BaseCommutingHomotopyEquiv (B := B) (X := X) (Y := X) where
  toBase := i
  fromBase := i
  toHomotopyEquiv := ContinuousMap.HomotopyEquiv.refl X
  left_comm := ContinuousMap.Homotopy.refl i
  right_comm := ContinuousMap.Homotopy.refl i

def symm (e : BaseCommutingHomotopyEquiv (B := B) (X := X) (Y := Y)) :
    BaseCommutingHomotopyEquiv (B := B) (X := Y) (Y := X) where
  toBase := e.fromBase
  fromBase := e.toBase
  toHomotopyEquiv := e.toHomotopyEquiv.symm
  left_comm := e.right_comm
  right_comm := e.left_comm

end BaseCommutingHomotopyEquiv

end DifferentialGeometry.Topology.Homotopy
