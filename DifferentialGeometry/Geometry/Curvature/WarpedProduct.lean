import DifferentialGeometry.Geometry.Connection.LeviCivita.MetricKoszul

open Set

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

/-- The block-diagonal inner product with radial coefficient one and fiber
coefficient `f ^ 2`. -/
def warpInner {F : Type*} [AddCommGroup F] [Module Real F]
    (f : Real) (h : F -> F -> Real) (X Y : Real × F) : Real :=
  X.1 * Y.1 + f ^ 2 * h X.2 Y.2

/-- Radial sectional-curvature coefficient of a warped product. -/
def warpRadCurv (f fpp : Real) : Real :=
  -fpp / f

/-- Fiber-tangential sectional-curvature coefficient for a unit-curvature
fiber. -/
def warpTanCurv (f fp : Real) : Real :=
  (1 - fp ^ 2) / f ^ 2

/-- The numerator in the warped-product curvature formula.  The arguments
`a, b` are radial components and `u, v` are fiber components. -/
def warpRmVal {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F -> F -> Real)
    (fiberRm : F -> F -> F -> F -> Real)
    (a b : Real) (u v : F) : Real :=
  -(f * fpp) * h (a • v - b • u) (a • v - b • u)
    + f ^ 2 * fiberRm u v v u
    - f ^ 2 * fp ^ 2 * (h u u * h v v - h u v * h u v)

/-- The difference between the warped Levi-Civita connection and the product
connection at a point. -/
def warpConnDiff {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp : Real) (h : F -> F -> Real) (X Y : Real × F) : Real × F :=
  (-(f * fp * h X.2 Y.2),
    (fp / f) • (X.1 • Y.2 + Y.1 • X.2))

/-- The standard warped connection term is the Koszul vector determined by
the radial derivative of the warped Gram field. -/
theorem warp_koszul {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f fp : Real) (hf : f ≠ 0)
    (h : F →L[Real] F →L[Real] Real)
    (D : (Real × F) →L[Real] (Real × F) →L[Real]
      (Real × F) →L[Real] Real)
    (hD : ∀ X Y Z, D X Y Z =
      2 * f * fp * X.1 * h Y.2 Z.2)
    (X Y Z : Real × F) :
    MetricKoszul.koszulCov D X Y Z =
      warpInner f (fun x y => h x y) (warpConnDiff f fp
        (fun x y => h x y) X Y) Z := by
  rw [MetricKoszul.koszulCov_apply, hD X Y Z, hD Y X Z, hD Z X Y]
  rcases X with ⟨a, u⟩
  rcases Y with ⟨b, v⟩
  rcases Z with ⟨c, w⟩
  simp [warpInner, warpConnDiff]
  field_simp [hf]
  ring

/-- The product-covariant derivative of `warpConnDiff`, evaluated on vectors
that are parallel for the product connection at the chosen point. -/
def warpDiffDeriv {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F -> F -> Real)
    (X Y Z : Real × F) : Real × F :=
  (-X.1 * (fp ^ 2 + f * fpp) * h Y.2 Z.2,
    (X.1 * ((f * fpp - fp ^ 2) / f ^ 2)) •
      (Y.1 • Z.2 + Z.1 • Y.2))

/-- Curvature of the standard warped connection, assembled from the product
curvature, the covariant derivative of the connection difference, and its
quadratic term. -/
def warpCurvOp {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F -> F -> Real)
    (fiberR : F -> F -> F -> F) (X Y Z : Real × F) : Real × F :=
  (0, fiberR X.2 Y.2 Z.2)
    + warpDiffDeriv f fp fpp h X Y Z
    - warpDiffDeriv f fp fpp h Y X Z
    + warpConnDiff f fp h X (warpConnDiff f fp h Y Z)
    - warpConnDiff f fp h Y (warpConnDiff f fp h X Z)

/-- The standard warped connection has the classical radial/fiber curvature
numerator. -/
theorem warpRm_formula {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f fp fpp : Real) (hf : f ≠ 0)
    (h : F →L[Real] F →L[Real] Real)
    (hsymm : ∀ u v, h u v = h v u)
    (fiberR : F -> F -> F -> F) (a b : Real) (u v : F) :
    warpInner f (fun x y => h x y) (a, u)
        (warpCurvOp f fp fpp (fun x y => h x y) fiberR
          (a, u) (b, v) (b, v)) =
      warpRmVal f fp fpp (fun x y => h x y)
        (fun x y z w => h w (fiberR x y z)) a b u v := by
  have hvu : h v u = h u v := hsymm v u
  simp [warpInner, warpCurvOp, warpDiffDeriv, warpConnDiff, warpRmVal,
    hvu]
  field_simp [hf]
  ring

/-- For a unit-curvature fiber, the warped-product curvature numerator splits
into its radial and tangential parts. -/
theorem warpRm_round {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F -> F -> Real)
    (fiberRm : F -> F -> F -> F -> Real)
    (a b : Real) (u v : F)
    (hround : fiberRm u v v u = h u u * h v v - h u v * h u v) :
    warpRmVal f fp fpp h fiberRm a b u v =
      -(f * fpp) * h (a • v - b • u) (a • v - b • u)
        + f ^ 2 * (1 - fp ^ 2) *
          (h u u * h v v - h u v * h u v) := by
  rw [warpRmVal, hround]
  ring

/-- For a unit-curvature fiber, the curvature numerator of the standard warped
connection is the sum of the radial and tangential sectional-curvature
coefficients times their corresponding squared areas. -/
theorem warpRm_coeffs {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f fp fpp : Real) (hf : f ≠ 0)
    (h : F →L[Real] F →L[Real] Real)
    (hsymm : ∀ u v, h u v = h v u)
    (fiberR : F -> F -> F -> F) (a b : Real) (u v : F)
    (hround : h u (fiberR u v v) =
      h u u * h v v - h u v * h u v) :
    warpInner f (fun x y => h x y) (a, u)
        (warpCurvOp f fp fpp (fun x y => h x y) fiberR
          (a, u) (b, v) (b, v)) =
      warpRadCurv f fpp *
          (f ^ 2 * h (a • v - b • u) (a • v - b • u))
        + warpTanCurv f fp *
          (f ^ 4 * (h u u * h v v - h u v * h u v)) := by
  calc
    _ = warpRmVal f fp fpp (fun x y => h x y)
        (fun x y z w => h w (fiberR x y z)) a b u v :=
      warpRm_formula f fp fpp hf h hsymm fiberR a b u v
    _ = -(f * fpp) * h (a • v - b • u) (a • v - b • u)
        + f ^ 2 * (1 - fp ^ 2) *
          (h u u * h v v - h u v * h u v) :=
      warpRm_round f fp fpp (fun x y => h x y)
        (fun x y z w => h w (fiberR x y z)) a b u v hround
    _ = _ := by
      simp only [warpRadCurv, warpTanCurv]
      field_simp [hf]

end Curvature
end Geometry
end DifferentialGeometry
