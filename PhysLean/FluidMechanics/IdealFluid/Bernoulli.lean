/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import PhysLean.FluidMechanics.IdealFluid.Basic
public import PhysLean.FluidMechanics.IdealFluid.Euler
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
      ∀ (t : Time) (pos : Space),
      ∂ₜ (fun t' => F.velocity t' pos) t = (0 : EuclideanSpace ℝ (Fin 3))

/-- Determines whether a flow is isentropic -/
def IdealFluid.isIsentropic (F: IdealFluid):
    Prop :=
      ∀ (t: Time) (pos: Space),
      ∂ₜ (fun t' => F.entropy t' pos) t = (0 : ℝ)

/-- The Bernoulli function (1/2)v^2 + w -/
noncomputable def IdealFluid.bernoulliEquation (F: IdealFluid)
(t: Time) (pos: Space) (g: Space → ℝ):
    ℝ :=
      let v := F.velocity t pos
      0.5 * ⟪v, v⟫_ℝ + F.enthalpy t pos + g pos

/-- Derivation:
  If the flow is steady and isentropic, the bernoulli equation is constant
-/
theorem bernoulli_derivation (F: IdealFluid) (Eul: F.satisfiesEuler g) (Stdy: F.isSteady)
(Istrpc: F.isIsentropic) (g: Space → ℝ) (t: Time) (pos: Space):
    let v := F.velocity t pos
    ⟪v, Space.grad (fun pos' => F.bernoulliEquation t pos' g) pos⟫_ℝ = 0
    := by
      sorry

--TODO: Complete the proofs
