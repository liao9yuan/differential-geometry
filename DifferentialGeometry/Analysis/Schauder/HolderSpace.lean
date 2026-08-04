import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

section Elliptic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

namespace IsContDiffHolderOn

theorem zero (k : Nat) (alpha : NNReal) (s : Set V) :
    IsContDiffHolderOn k alpha s (0 : V → F) := by
  constructor
  · intro x _
    exact contDiffAt_const
  · have hjet :
        s.restrict (iteratedFDeriv Real k (0 : V → F)) = 0 := by
      funext x
      rw [iteratedFDeriv_zero]
      rfl
    rw [hjet]
    exact memHolder_zero

theorem add {k : Nat} {alpha : NNReal} {s : Set V} {f g : V → F}
    (hf : IsContDiffHolderOn k alpha s f)
    (hg : IsContDiffHolderOn k alpha s g) :
    IsContDiffHolderOn k alpha s (f + g) := by
  constructor
  · intro x hx
    exact (hf.1 x hx).add (hg.1 x hx)
  · have hjet :
        s.restrict (iteratedFDeriv Real k (f + g)) =
          s.restrict (iteratedFDeriv Real k f) +
            s.restrict (iteratedFDeriv Real k g) := by
      funext x
      exact iteratedFDeriv_add_apply (hf.1 x x.2) (hg.1 x x.2)
    rw [hjet]
    exact hf.2.add hg.2

theorem smul {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (hf : IsContDiffHolderOn k alpha s f) (c : Real) :
    IsContDiffHolderOn k alpha s (c • f) := by
  constructor
  · intro x hx
    simpa only [Pi.smul_apply] using (hf.1 x hx).const_smul c
  · have hjet :
        s.restrict (iteratedFDeriv Real k (c • f)) =
          c • s.restrict (iteratedFDeriv Real k f) := by
      funext x
      exact iteratedFDeriv_const_smul_apply (hf.1 x x.2)
    rw [hjet]
    exact hf.2.smul

theorem neg {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (hf : IsContDiffHolderOn k alpha s f) :
    IsContDiffHolderOn k alpha s (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1)

theorem sub {k : Nat} {alpha : NNReal} {s : Set V} {f g : V → F}
    (hf : IsContDiffHolderOn k alpha s f)
    (hg : IsContDiffHolderOn k alpha s g) :
    IsContDiffHolderOn k alpha s (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end IsContDiffHolderOn

def contDiffHolderOnSubmodule (k : Nat) (alpha : NNReal) (s : Set V) :
    Submodule Real (V → F) where
  carrier := {f | IsContDiffHolderOn k alpha s f}
  zero_mem' := IsContDiffHolderOn.zero k alpha s
  add_mem' := IsContDiffHolderOn.add
  smul_mem' := fun c _ hf ↦ hf.smul c

@[simp]
theorem mem_contDiffHolderOnSubmodule {k : Nat} {alpha : NNReal}
    {s : Set V} {f : V → F} :
    f ∈ contDiffHolderOnSubmodule k alpha s ↔
      IsContDiffHolderOn k alpha s f :=
  Iff.rfl

end Elliptic

section Parabolic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem parabolicSpatialJet_const_smul
    (j : Nat) (u : Real → V → F) (p : ParabolicPoint V) (c : Real)
    (hu : ContDiffAt Real j (u p.time) p.space) :
    parabolicSpatialJet j (c • u) p = c • parabolicSpatialJet j u p := by
  unfold parabolicSpatialJet
  exact iteratedFDeriv_const_smul_apply hu

omit [NormedAddCommGroup V] [NormedSpace Real V] in
theorem parabolicTimeDerivative_const_smul
    (u : Real → V → F) (p : ParabolicPoint V) (c : Real)
    (hu : DifferentiableAt Real (fun t ↦ u t p.space) p.time) :
    parabolicTimeDerivative (c • u) p =
      c • parabolicTimeDerivative u p := by
  unfold parabolicTimeDerivative
  change (fderiv Real (c • fun t ↦ u t p.space) p.time) 1 = _
  rw [fderiv_const_smul hu c]
  exact ContinuousLinearMap.smul_apply _ _ _

namespace IsParabolicC2On

theorem zero (Q : Set (ParabolicPoint V)) :
    IsParabolicC2On Q (0 : Real → V → F) := by
  constructor
  · intro p _
    exact contDiffAt_const
  · intro p _
    exact differentiableAt_const _

theorem add {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hu : IsParabolicC2On Q u) (hv : IsParabolicC2On Q v) :
    IsParabolicC2On Q (u + v) := by
  constructor
  · intro p hp
    exact (hu.1 p hp).add (hv.1 p hp)
  · intro p hp
    exact (hu.2 p hp).add (hv.2 p hp)

theorem smul {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (hu : IsParabolicC2On Q u) (c : Real) :
    IsParabolicC2On Q (c • u) := by
  constructor
  · intro p hp
    simpa only [Pi.smul_apply] using (hu.1 p hp).const_smul c
  · intro p hp
    simpa only [Pi.smul_apply] using (hu.2 p hp).const_smul c

theorem neg {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (hu : IsParabolicC2On Q u) :
    IsParabolicC2On Q (-u) := by
  simpa only [neg_one_smul] using hu.smul (-1)

theorem sub {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hu : IsParabolicC2On Q u) (hv : IsParabolicC2On Q v) :
    IsParabolicC2On Q (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

end IsParabolicC2On

namespace IsParabolicC2HolderOn

theorem zero (alpha : NNReal) (Q : Set (ParabolicPoint V)) :
    IsParabolicC2HolderOn alpha Q (0 : Real → V → F) := by
  refine ⟨IsParabolicC2On.zero Q, ?_, ?_⟩
  · have hjet :
        Q.restrict (parabolicSpatialJet 2 (0 : Real → V → F)) = 0 := by
      funext p
      unfold parabolicSpatialJet
      change iteratedFDeriv Real 2 (0 : V → F) p.1.space = 0
      rw [iteratedFDeriv_zero]
      rfl
    rw [hjet]
    exact memHolder_zero
  · have htime :
        Q.restrict (parabolicTimeDerivative (0 : Real → V → F)) = 0 := by
      funext p
      unfold parabolicTimeDerivative
      change (fderiv Real (0 : Real → F) p.1.time) 1 = 0
      rw [fderiv_zero]
      rfl
    rw [htime]
    exact memHolder_zero

theorem add {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u v : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u)
    (hv : IsParabolicC2HolderOn alpha Q v) :
    IsParabolicC2HolderOn alpha Q (u + v) := by
  refine ⟨hu.1.add hv.1, ?_, ?_⟩
  · have hjet :
        Q.restrict (parabolicSpatialJet 2 (u + v)) =
          Q.restrict (parabolicSpatialJet 2 u) +
            Q.restrict (parabolicSpatialJet 2 v) := by
      funext p
      exact parabolicSpatialJet_add 2 u v p (hu.1.1 p p.2) (hv.1.1 p p.2)
    rw [hjet]
    exact hu.2.1.add hv.2.1
  · have htime :
        Q.restrict (parabolicTimeDerivative (u + v)) =
          Q.restrict (parabolicTimeDerivative u) +
            Q.restrict (parabolicTimeDerivative v) := by
      funext p
      exact parabolicTimeDerivative_add u v p (hu.1.2 p p.2) (hv.1.2 p p.2)
    rw [htime]
    exact hu.2.2.add hv.2.2

theorem smul {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u) (c : Real) :
    IsParabolicC2HolderOn alpha Q (c • u) := by
  refine ⟨hu.1.smul c, ?_, ?_⟩
  · have hjet :
        Q.restrict (parabolicSpatialJet 2 (c • u)) =
          c • Q.restrict (parabolicSpatialJet 2 u) := by
      funext p
      exact parabolicSpatialJet_const_smul 2 u p c (hu.1.1 p p.2)
    rw [hjet]
    exact hu.2.1.smul
  · have htime :
        Q.restrict (parabolicTimeDerivative (c • u)) =
          c • Q.restrict (parabolicTimeDerivative u) := by
      funext p
      exact parabolicTimeDerivative_const_smul u p c (hu.1.2 p p.2)
    rw [htime]
    exact hu.2.2.smul

theorem neg {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u) :
    IsParabolicC2HolderOn alpha Q (-u) := by
  simpa only [neg_one_smul] using hu.smul (-1)

theorem sub {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u v : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u)
    (hv : IsParabolicC2HolderOn alpha Q v) :
    IsParabolicC2HolderOn alpha Q (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

end IsParabolicC2HolderOn

def parabolicC2HolderOnSubmodule (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) : Submodule Real (Real → V → F) where
  carrier := {u | IsParabolicC2HolderOn alpha Q u}
  zero_mem' := IsParabolicC2HolderOn.zero alpha Q
  add_mem' := IsParabolicC2HolderOn.add
  smul_mem' := fun c _ hu ↦ hu.smul c

@[simp]
theorem mem_parabolicC2HolderOnSubmodule {alpha : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F} :
    u ∈ parabolicC2HolderOnSubmodule alpha Q ↔
      IsParabolicC2HolderOn alpha Q u :=
  Iff.rfl

end Parabolic

end DifferentialGeometry.Analysis.Schauder
