import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoLift
import DifferentialGeometry.Geometry.Exponential.RawLiftLength

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

/-- A smooth path shorter than the raw local-diffeomorphism radius lifts from
the origin through the raw framed exponential.  Radial raw-domain coverage is
used only to fence every partial lift inside the compact model-space ball. -/
theorem exists_raw_lift
    [(x : M) → NormedAddCommGroup (TangentSpace I x)]
    [(x : M) → NormedSpace Real (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {γ : Real → M} {a b R : Real}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hγa : γ a = p)
    (hR : 0 < R)
    (hlen : Manifold.pathELength I γ a b < ENNReal.ofReal R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    ∃ η : Real → E,
      IsLiftOn (framedExpMap (I := I) g p) γ
        (Metric.ball (0 : E) R) 0 a b η := by
  let ell : Real := (Manifold.pathELength I γ a b).toReal
  have hfin : Manifold.pathELength I γ a b ≠ ⊤ := hlen.ne_top
  have hellR : ell < R :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hlen
  have hK : IsCompact (Metric.closedBall (0 : E) ell) :=
    isCompact_closedBall _ _
  have hKU :
      Metric.closedBall (0 : E) ell ⊆ Metric.ball (0 : E) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hellR
  have hzero : (0 : E) ∈ Metric.ball (0 : E) R := by
    simpa only [Metric.mem_ball, dist_self] using hR
  have hstart : framedExpMap (I := I) g p 0 = γ a := by
    rw [framedExpMap_apply, map_zero, expMap_zero, hγa]
  have hfence :
      ∀ {t : Real}, t ∈ Set.Icc a b →
        ∀ {η : Real → E},
          IsLiftOn (framedExpMap (I := I) g p) γ
              (Metric.ball (0 : E) R) 0 a t η →
            η t ∈ Metric.closedBall (0 : E) ell := by
    intro t ht η hη
    have hsub : Set.Icc a t ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc le_rfl ht.2
    have hηcd : ContDiffOn Real 1 η (Set.Icc a t) :=
      hη.contDiffOn hloc (hγ.mono hsub)
    have hrad :
        ENNReal.ofReal ‖η t‖ ≤
          Manifold.pathELength I
            ((framedExpMap (I := I) g p) ∘ η) a t := by
      apply rawLift_norm_le (I := I) g hEnorm p ht.1 hη.2.1 hηcd
      intro x hx s hs
      exact hdom (η x) (hη.mapsTo hx) s hs
    have hlift :
        Manifold.pathELength I
            ((framedExpMap (I := I) g p) ∘ η) a t =
          Manifold.pathELength I γ a t := by
      apply Manifold.pathELength_congr
      intro s hs
      exact (hη.2.2 s hs).2
    have hmono :
        Manifold.pathELength I γ a t ≤
          Manifold.pathELength I γ a b :=
      Manifold.pathELength_mono le_rfl ht.2
    have hchain :
        ENNReal.ofReal ‖η t‖ ≤
          Manifold.pathELength I γ a b := by
      calc
        ENNReal.ofReal ‖η t‖
            ≤ Manifold.pathELength I
                ((framedExpMap (I := I) g p) ∘ η) a t := hrad
        _ = Manifold.pathELength I γ a t := hlift
        _ ≤ Manifold.pathELength I γ a b := hmono
    have hreal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hchain
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa only [ell, ENNReal.toReal_ofReal (norm_nonneg _)] using hreal
  exact
    IsLiftOn.exists_of_compact hab Metric.isOpen_ball hloc hγ.continuousOn
      hzero hstart hK hKU hfence

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
