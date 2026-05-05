/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The differential-geometry contributors
-/

import DifferentialGeometry.ForMathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import DifferentialGeometry.ForMathlib.Geometry.Manifold.VectorBundle.OrthonormalFrame
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Levi-Civita connection interface

This file contains the stable interface from the Mathlib PR
`Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` that is
useful to the synthetic realization layer.

The PR also sketches a concrete construction of `LeviCivitaConnection` using
Koszul's formula and local orthonormal frames. That construction currently has
unfinished local-candidate, compatibility, and Christoffel-symbol obligations,
so this file deliberately does **not** copy it. Instead it records the part that
is already mathematically and API-wise stable: a covariant derivative is
Levi-Civita when it is metric compatible and torsion-free.

The `OrthonormalFrame` import is routed through `DifferentialGeometry.ForMathlib`
rather than `Mathlib`, since that PR file is not yet available in the pinned
mathlib checkout.
-/

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The scalar product of two vector fields, using the Riemannian bundle
inner-product instances. -/
noncomputable abbrev product (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun x => inner ℝ (X x) (Y x)

local notation "⟪" X ", " Y "⟫" => product X Y

/-- Product-rule metric compatibility for a tangent-bundle covariant derivative.

This is the PR-style predicate, stated directly in terms of an existing
`cov : CovariantDerivative I E (TangentSpace I)`. It avoids the instance-package
problem currently encountered when trying to use
`CovariantDerivative.IsCompatible` from `Metric.lean` on a `cov` built with the
pre-existing tangent-bundle module/norm instances. -/
def IsCompatibleConnection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ X Y Z : Π x : M, TangentSpace I x,
  ∀ x : M,
    mfderiv I 𝓘(ℝ, ℝ) ⟪Y, Z⟫ x (X x) =
      ⟪fun y => cov Y y (X y), Z⟫ x + ⟪Y, fun y => cov Z y (X y)⟫ x

/-- A covariant derivative on the tangent bundle is Levi-Civita when it is
metric-compatible and torsion-free.

The metric is the one supplied by the local `RiemannianBundle` instance. -/
def IsLeviCivitaConnection
    [FiniteDimensional ℝ E] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  cov.IsCompatibleConnection ∧ cov.torsion = 0

/-- Metric compatibility projection from `IsLeviCivitaConnection`. -/
theorem IsLeviCivitaConnection.isCompatible
    [FiniteDimensional ℝ E] [IsManifold I 2 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (h : cov.IsLeviCivitaConnection) :
    cov.IsCompatibleConnection :=
  h.1

/-- Torsion-free projection from `IsLeviCivitaConnection`. -/
theorem IsLeviCivitaConnection.torsion_eq_zero
    [FiniteDimensional ℝ E] [IsManifold I 2 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (h : cov.IsLeviCivitaConnection) :
    cov.torsion = 0 :=
  h.2

end CovariantDerivative
