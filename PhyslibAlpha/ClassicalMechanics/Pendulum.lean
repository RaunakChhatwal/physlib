/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import PhyslibAlpha.ClassicalMechanics.Pendulum.Defs
public import Mathlib.Topology.EMetricSpace.Weak
import all PhyslibAlpha.ClassicalMechanics.Pendulum.Proofs
/-!
# The simple pendulum

This file states the public results of the pendulum model while keeping the construction proofs
internal. A pendulum exists for every admissible choice of physical parameters and initial angular
state. Its angle, derived from the bob's position, obeys the nonlinear pendulum equation. The
familiar elementary period appears only as a limit near the downward equilibrium.
-/

@[expose] public noncomputable section

open scoped Topology

namespace ClassicalMechanics.Pendulum

/-!
## A. Equation of motion

The angular equation follows from the particle-level assumptions: Newton's second law for the bob,
central tension, fixed length, and uniform gravity. It is derived rather than separately assumed in
the definition of a pendulum.
-/

/-- θ'' = -(g/L) sin θ -/
theorem differential_equation (self : Pendulum) (t : Time) :
    Time.deriv self.ω t = -self.g / self.L * Real.Angle.sin (self.θ t) :=
  Internal.differential_equation self t

/-!
## B. Uniqueness and construction

`Specs` identifies which particles and forces in a fixed system serve as the pivot, bob, tension,
and support, and records the required properties. It does not add independently variable state.
Once a system has one such specification, there is no distinct second one. Conversely, `make`
selects a pendulum with the requested physical parameters and initial state.
-/

/-- A fixed particle system admits no pendulum specification distinct from `self`. -/
lemma Specs.uniqueness (system : PointParticle.System 2) (self : Specs system) :
    Set.univ = {self} :=
  Internal.specs_uniqueness system self

/-- At least one pendulum exists for every positive choice of masses, length, and gravity and every
initial angular state. -/
lemma Params.surjective : Function.Surjective params :=
  Internal.params_surjective

/-- Create a pendulum from physical parameters and initial state. -/
def make (params : Params) : Pendulum :=
  Classical.choose params.surjective

/-!
## C. Small-angle period

The period is optional because not every complete trajectory repeats. The topology below places
the absence of a period infinitely far from every real period. Therefore, convergence to a real
period also guarantees the converging periods exist.
-/

/-- Compare real periods by their usual distance and place `none` infinitely far from all of
them. -/
local instance : EMetricSpace (Option ℝ) :=
  { PseudoEMetricSpace.ofEDist edist (Option.edist_self' _) (Option.edist_comm' _) (Option.edist_triangle' _)
    with eq_of_edist_eq_zero {x y} _ := by cases x <;> cases y <;> simp_all }

/-- For release from rest, the exact period approaches `2π √(L/g)` as the nonzero initial angle
approaches the downward equilibrium.

The punctured neighborhood excludes the equilibrium solution itself, whose constant bob position
does not have a least positive period. -/
theorem small_angle_period (params : Params) (from_rest : params.ω0 = 0) :
    Filter.Tendsto
      (fun θ0 => (make { params with θ0 }).period)
      (𝓝[≠] 0)
      (𝓝 <| some <| 2 * Real.pi * √(params.L / params.g)) :=
  Internal.small_angle_period (by simp) params from_rest
