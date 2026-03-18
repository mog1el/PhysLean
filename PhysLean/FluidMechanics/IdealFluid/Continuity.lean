/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import PhysLean.FluidMechanics.IdealFluid.Basic
public import PhysLean.Mathematics.Calculus.Divergence
public import PhysLean.SpaceAndTime.Time.Derivatives
public import PhysLean.SpaceAndTime.Space.Derivatives.Div

/-!
This module introduces the continuity criterium.
There is potential to add various different lemmas expanding on this.
-/

open scoped InnerProductSpace
open Time
open Space

/-- defining satisfying the equation of continuity -/
public def IdealFluid.satisfiesContinuity (F : IdealFluid):
    Prop :=
      ∀ (t : Time) (pos : Space),
      ∂ₜ (fun t' => F.density t' pos) t +
      Space.div (fun pos' => F.massFluxDensity t pos') pos = (0 : ℝ)

/-- Criterion for incompressibility -/
public def IdealFluid.isIncompressible (F : IdealFluid):
    Prop :=
      ∀ (t : Time) (pos : Space), ∂ₜ (fun t' => F.density t' pos) t = 0


/-- Theorem: If constant density and incompressible div(v)=0-/
theorem incompress_const_density_implies_div_v_eq_zero (F : IdealFluid)
    (Cont      : F.satisfiesContinuity)
    (Incomp    : F.isIncompressible)
    (ConstDens : ∀ (t : Time) (pos : Space), Space.grad (fun pos' => F.density t pos') pos = 0) :
    ∀ (t : Time) (pos : Space), Space.div (fun pos' => F.velocity t pos') pos = 0 := by
      sorry
