/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import PhysLean.FluidMechanics.IdealFluid.Basic
public import PhysLean.Mathematics.Calculus.Divergence
public import PhysLean.SpaceAndTime.Time.Derivatives

/-!
This module introduces:
steady flow,
... (still under construction)
-/

open scoped InnerProductSpace
open Time
open Space

/-- Determines whether a flow is steady -/
def IdealFluid.isSteady (F: IdealFluid) :
    Prop :=
      ∀ (t : Time) (pos : Space), ∂ₜ (fun t' => F.velocity t' pos) t = (0 : EuclideanSpace ℝ (Fin 3))

/-- Determines whether a flow is isentropic -/
def IdealFluid.isIsentropic (F: IdealFluid):
    Prop :=
      ∀ (t: Time) (pos: Space), ∂ₜ (fun t' => F.entropy t' pos) t = (0 : ℝ)

-- TODO: Provide the Bernoulli's equation (after fun derivatoins)
