/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import PhysLean.FluidMechanics.IdealFluid.Basic
public import PhysLean.Mathematics.Calculus.Divergence
public import PhysLean.SpaceAndTime.Time.Derivatives
public import PhysLean.SpaceAndTime.Space.Derivatives.Grad
public import PhysLean.SpaceAndTime.Space.Derivatives.Div

/-!
This module introduces the Euler's equation.
-/

open scoped InnerProductSpace
open Time
open Space

/-- Defines the property of satisfying Euler's equation. -/
public def IdealFluid.satisfiesEuler (F: IdealFluid) (g: Space → ℝ):
    Prop :=
      ∀ (t : Time) (pos : Space),
        let v := F.velocity t pos
        ∂ₜ (fun t'=> F.velocity t' pos) t +
        (fun i => ⟪v, Space.grad (fun pos' => F.velocity t pos' i) pos⟫_ℝ)
        = -(1/F.density t pos) • Space.grad (fun pos' => F.pressure t pos') pos + Space.grad g pos
