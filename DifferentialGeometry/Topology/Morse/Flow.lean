import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Morse.LocalNormalForm
import Mathlib.Geometry.Manifold.Diffeomorph

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable {f : M → ℝ} {a b : ℝ}

structure GradientLikeFlow (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) where
  flow : ℝ → M → M
  flow_zero : ∀ x : M, flow 0 x = x
  flow_add : ∀ s t : ℝ, flow (s + t) = flow s ∘ flow t
  contMDiffAt : ∀ t : ℝ, ∀ x : M, ContMDiffAt I I (⊤ : WithTop ℕ∞) (fun x : M => flow t x) x
  contMDiffAt_t : ∀ x : M, ContMDiffAt 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) (fun t : ℝ => flow t x) (0 : ℝ)
  strip_eq_sub : ∀ x : M, ∀ t : ℝ, 0 ≤ t → a ≤ f x - t → f (flow t x) = f x - t
  strip_eq_add_back : ∀ x : M, ∀ t : ℝ, 0 ≤ t → a ≤ f x → f x + t ≤ b →
    f (flow (-t) x) = f x + t
  rate_bound : ∀ x : M, ∀ t : ℝ, 0 ≤ t → f x - t ≤ f (flow t x) ∧ f (flow t x) ≤ f x

def GradientLikeFlow.toDiffeomorph (Φ : GradientLikeFlow I f a b) (t : ℝ) :
    Diffeomorph I I M M (⊤ : WithTop ℕ∞) where
  toEquiv :=
    { toFun := Φ.flow t
      invFun := Φ.flow (-t)
      left_inv := by
        intro x
        have h := congrFun (Φ.flow_add (-t) t) x
        change Φ.flow (-t) (Φ.flow t x) = x
        calc
          Φ.flow (-t) (Φ.flow t x) = (Φ.flow (-t) ∘ Φ.flow t) x := rfl
          _ = Φ.flow (-t + t) x := h.symm
          _ = Φ.flow 0 x := by simp
          _ = x := Φ.flow_zero x
      right_inv := by
        intro x
        have h := congrFun (Φ.flow_add t (-t)) x
        change Φ.flow t (Φ.flow (-t) x) = x
        calc
          Φ.flow t (Φ.flow (-t) x) = (Φ.flow t ∘ Φ.flow (-t)) x := rfl
          _ = Φ.flow (t + -t) x := h.symm
          _ = Φ.flow 0 x := by simp
          _ = x := Φ.flow_zero x }
  contMDiff_toFun := Φ.contMDiffAt t
  contMDiff_invFun := Φ.contMDiffAt (-t)

theorem GradientLikeFlow.flow_sublevel (Φ : GradientLikeFlow I f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) {x : M} (hx : x ∈ sublevel f b) :
    Φ.flow t x ∈ sublevel f (b - t) := by
  change f (Φ.flow t x) ≤ b - t
  by_cases hst : a ≤ f x - t
  · have hEq := Φ.strip_eq_sub x t ht.1 hst
    calc
      f (Φ.flow t x) = f x - t := hEq
      _ ≤ b - t := by
        have hfx : f x ≤ b := by simpa [sublevel] using hx
        linarith
  · by_cases hbelow : f x ≤ a
    · have hb := (Φ.rate_bound x t ht.1).2
      calc
        f (Φ.flow t x) ≤ f x := hb
        _ ≤ a := hbelow
        _ ≤ b - t := by linarith [ht.2]
    · have hax : a < f x := lt_of_not_ge hbelow
      let t₀ : ℝ := f x - a
      have ht₀ : 0 ≤ t₀ := by
        dsimp [t₀]
        linarith
      have ht₀t : t₀ < t := by
        have hnot : f x - t < a := lt_of_not_ge hst
        dsimp [t₀]
        linarith
      have hEq₀ := Φ.strip_eq_sub x t₀ ht₀ (by dsimp [t₀]; linarith)
      have hflow : Φ.flow t x = Φ.flow (t - t₀) (Φ.flow t₀ x) := by
        have h := congrFun (Φ.flow_add (t - t₀) t₀) x
        change Φ.flow ((t - t₀) + t₀) x = Φ.flow (t - t₀) (Φ.flow t₀ x) at h
        rw [sub_add_cancel] at h
        exact h
      have hb := (Φ.rate_bound (Φ.flow t₀ x) (t - t₀) (by linarith)).2
      calc
        f (Φ.flow t x) = f (Φ.flow (t - t₀) (Φ.flow t₀ x)) := by rw [hflow]
        _ ≤ f (Φ.flow t₀ x) := hb
        _ = a := by
          have hE : f (Φ.flow t₀ x) = f x - t₀ := hEq₀
          dsimp [t₀] at hE
          linarith
        _ ≤ b - t := by linarith [ht.2]

theorem GradientLikeFlow.flow_sublevel_back (Φ : GradientLikeFlow I f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) {y : M} (hy : y ∈ sublevel f (b - t)) :
    Φ.flow (-t) y ∈ sublevel f b := by
  change f (Φ.flow (-t) y) ≤ b
  by_cases hst : a ≤ f y
  · have hEq := Φ.strip_eq_add_back y t ht.1 hst (by
      have hfy : f y ≤ b - t := by simpa [sublevel] using hy
      linarith)
    calc
      f (Φ.flow (-t) y) = f y + t := hEq
      _ ≤ b := by
        have hfy : f y ≤ b - t := by simpa [sublevel] using hy
        linarith
  · have hfy : f y ≤ b - t := by simpa [sublevel] using hy
    let z : M := Φ.flow (-t) y
    have hmain : f z - t ≤ f y := by
      have hle := (Φ.rate_bound z t ht.1).1
      have hzy : Φ.flow t z = y := by
        dsimp [z]
        have h := congrFun (Φ.flow_add t (-t)) y
        change Φ.flow (t + -t) y = Φ.flow t (Φ.flow (-t) y) at h
        rw [add_neg_cancel] at h
        simpa [Φ.flow_zero] using h.symm
      calc
        f z - t ≤ f (Φ.flow t z) := hle
        _ = f y := by rw [hzy]
    calc
      f (Φ.flow (-t) y) = f z := by rfl
      _ ≤ f y + t := by linarith
      _ ≤ b := by linarith

noncomputable def GradientLikeFlow.sublevelEquiv (Φ : GradientLikeFlow I f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) :
    SublevelSpace f b ≃ SublevelSpace f (b - t) where
  toFun := fun x => ⟨Φ.flow t (x : M), Φ.flow_sublevel (t := t) ht (x := (x : M)) x.2⟩
  invFun := fun y => ⟨Φ.flow (-t) (y : M), Φ.flow_sublevel_back (t := t) ht (y := (y : M)) y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have h := congrFun (Φ.flow_add (-t) t) (x : M)
    change Φ.flow (-t) (Φ.flow t (x : M)) = x.1
    calc
      Φ.flow (-t) (Φ.flow t (x : M)) = (Φ.flow (-t) ∘ Φ.flow t) (x : M) := rfl
      _ = Φ.flow (-t + t) (x : M) := h.symm
      _ = Φ.flow 0 (x : M) := by simp
      _ = (x : M) := Φ.flow_zero (x : M)
  right_inv := by
    intro y
    apply Subtype.ext
    have h := congrFun (Φ.flow_add t (-t)) (y : M)
    change Φ.flow t (Φ.flow (-t) (y : M)) = y.1
    calc
      Φ.flow t (Φ.flow (-t) (y : M)) = (Φ.flow t ∘ Φ.flow (-t)) (y : M) := rfl
      _ = Φ.flow (t + -t) (y : M) := h.symm
      _ = Φ.flow 0 (y : M) := by simp
      _ = (y : M) := Φ.flow_zero (y : M)

theorem GradientLikeFlow.flow_image_sublevel (Φ : GradientLikeFlow I f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) :
    (fun x : M => Φ.flow t x) '' sublevel f b = sublevel f (b - t) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    exact Φ.flow_sublevel (t := t) ht (x := x) hx
  · intro hy
    refine ⟨Φ.flow (-t) y, Φ.flow_sublevel_back (t := t) ht (y := y) hy, ?_⟩
    have h := congrFun (Φ.flow_add t (-t)) y
    change Φ.flow (t + -t) y = Φ.flow t (Φ.flow (-t) y) at h
    rw [add_neg_cancel] at h
    simpa [Φ.flow_zero] using h.symm

theorem GradientLikeFlow.toDiffeomorph_image_sublevel (Φ : GradientLikeFlow I f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) :
    Φ.toDiffeomorph t '' sublevel f b = sublevel f (b - t) := by
  simpa [toDiffeomorph] using Φ.flow_image_sublevel ht

theorem noCriticalValues (Φ : GradientLikeFlow I f a b) (hab : a ≤ b) :
    (fun x : M => Φ.flow (a - b) x) '' sublevel f a = sublevel f b := by
  have ht : b - a ∈ Set.Icc (0 : ℝ) (b - a) := ⟨sub_nonneg.mpr hab, le_rfl⟩
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    have hb : b - (b - a) = a := by ring
    have hx' : x ∈ sublevel f (b - (b - a)) := by
      simpa [hb] using hx
    have hback := Φ.flow_sublevel_back (t := b - a) ht (y := x) hx'
    have hneg : -(b - a) = a - b := by ring
    simpa [hneg] using hback
  · intro hy
    refine ⟨Φ.flow (b - a) y, ?_, ?_⟩
    · have hsub := Φ.flow_sublevel (t := b - a) ht (x := y) hy
      have hb : b - (b - a) = a := by ring
      simpa [hb] using hsub
    · have h := congrFun (Φ.flow_add (a - b) (b - a)) y
      have hz : (a - b) + (b - a) = 0 := by ring
      calc
        Φ.flow (a - b) (Φ.flow (b - a) y) = (Φ.flow (a - b) ∘ Φ.flow (b - a)) y := rfl
        _ = Φ.flow ((a - b) + (b - a)) y := h.symm
        _ = Φ.flow 0 y := by rw [hz]
        _ = y := Φ.flow_zero y

theorem noCriticalValues_toDiffeomorph (Φ : GradientLikeFlow I f a b) (hab : a ≤ b) :
    Φ.toDiffeomorph (a - b) '' sublevel f a = sublevel f b := by
  simpa [GradientLikeFlow.toDiffeomorph] using (noCriticalValues Φ hab)

noncomputable def linearModelFlow (a b : ℝ) (_hab : a ≤ b) :
    GradientLikeFlow 𝓘(ℝ, MorseModel 1) (fun y : MorseModel 1 => y 0) a b where
  flow := fun t y => (fun _ : Fin 1 => y 0 - t)
  flow_zero := by
    intro y
    funext i
    fin_cases i; simp
  flow_add := by
    intro s t
    funext y
    funext i
    fin_cases i
    change y 0 - (s + t) = (y 0 - t) - s
    ring
  contMDiffAt := by
    intro t x
    exact ContDiffAt.contMDiffAt (f := fun y : MorseModel 1 => (fun _ : Fin 1 => y 0 - t))
      ((contDiff_pi' (fun i : Fin 1 => by fun_prop) :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : MorseModel 1 => (fun _ : Fin 1 => y 0 - t))).contDiffAt)
  contMDiffAt_t := by
    intro x
    exact ContDiffAt.contMDiffAt (f := fun t : ℝ => (fun _ : Fin 1 => x 0 - t))
      ((contDiff_pi' (fun i : Fin 1 => by fun_prop) :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun t : ℝ => (fun _ : Fin 1 => x 0 - t))).contDiffAt)
  strip_eq_sub := by
    intro x t ht hst
    rfl
  strip_eq_add_back := by
    intro x t ht h1 h2
    simp [sub_eq_add_neg]
  rate_bound := by
    intro x t ht
    constructor
    · rfl
    · simp [sub_eq_add_neg]
      linarith

theorem linearModelNoCriticalValues (a b : ℝ) (hab : a ≤ b) :
    (fun y : MorseModel 1 => (linearModelFlow a b hab).flow (a - b) y) ''
        sublevel (fun y : MorseModel 1 => y 0) a =
      sublevel (fun y : MorseModel 1 => y 0) b :=
  noCriticalValues (linearModelFlow a b hab) hab

end

end DifferentialGeometry.Topology.Morse
