import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Normed.Module.Dual

set_option autoImplicit false

abbrev TensorData (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (r s : ℕ) :=
  MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)

def evalLinear {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) : (V →ₗ[R] R) →ₗ[R] R where
  toFun w := w v
  map_add' w1 w2 := rfl
  map_smul' c w := rfl

def vectorToData {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) : TensorData R V 1 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.ofSubsingleton R _ 0 (evalLinear v))

def scalarToData {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (f : R) : TensorData R V 0 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) f)
