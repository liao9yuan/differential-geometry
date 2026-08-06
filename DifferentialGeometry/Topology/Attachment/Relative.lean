import Mathlib.Topology.Homotopy.Equiv

namespace DifferentialGeometry.Topology

universe u v w

noncomputable section

variable {B : Type u} {X : Type v} {Y : Type w}
variable [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]

structure HomotopyEquivUnder {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X]
    [TopologicalSpace Y] where
  toBase : C(B, X)
  fromBase : C(B, Y)
  toHomotopyEquiv : ContinuousMap.HomotopyEquiv X Y
  left_comm : ContinuousMap.Homotopy (toHomotopyEquiv.toFun.comp toBase) fromBase
  right_comm : ContinuousMap.Homotopy (toHomotopyEquiv.invFun.comp fromBase) toBase

namespace HomotopyEquivUnder

def refl (i : C(B, X)) : HomotopyEquivUnder (B := B) (X := X) (Y := X) where
  toBase := i
  fromBase := i
  toHomotopyEquiv := ContinuousMap.HomotopyEquiv.refl X
  left_comm := ContinuousMap.Homotopy.refl i
  right_comm := ContinuousMap.Homotopy.refl i

def symm (e : HomotopyEquivUnder (B := B) (X := X) (Y := Y)) :
    HomotopyEquivUnder (B := B) (X := Y) (Y := X) where
  toBase := e.fromBase
  fromBase := e.toBase
  toHomotopyEquiv := e.toHomotopyEquiv.symm
  left_comm := e.right_comm
  right_comm := e.left_comm

end HomotopyEquivUnder

end

end DifferentialGeometry.Topology
