/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Physlib.ClassicalMechanics.ParticleMechanics.System
/-!
# The simple pendulum

The usual sketch of a pendulum shows a bob hanging from a rigid, massless rod. This model contains
exactly two physical objects, both point particles: a pivot and a bob. It does not add a rod as
a third object. The effects normally attributed to the rod are expressed by two conditions:
the bob stays a fixed distance from the pivot, and the pivot exerts a central force on the bob.

The pivot is also a particle, rather than a fixed point of space. An external support force keeps it
at the frame origin, and gravity acts on both particles. Representing these forces explicitly makes
the environment assumed by the textbook model visible while keeping the pendulum a
`ParticleMechanics.System` that satisfies Newton's laws.

The model can be described in two directions. `Params` supplies masses, length, gravity, and an
initial angular state from which a pendulum can be built. `Specs system` states that an existing
Newtonian particle system has exactly the particles, forces, and geometric constraints required of
a simple pendulum.
-/

@[expose] public noncomputable section

open scoped Classical Finset Manifold

namespace ClassicalMechanics.Pendulum

/-!
## A. Parameters and specifications

The pendulum is built from ordinary particle-mechanics data. Gravity is one external force on each
particle. The remaining fields of `Specs` identify the pivot, bob, tension, and support force among
the objects already in the system, then state the conditions that make them a simple pendulum.
-/

/-- Uniform downward gravity on one system particle.

The vector is constant in time and points along the frame's negative second axis, so a pendulum
specification separately requires the frame basis to be orthonormal. -/
def gravity {system : ParticleMechanics.System 2} (particle : system.Particle) (g : ℝ+) :
    system.frame.Force where
  value _ := .mk ![0, -particle.mass * g]
  target := particle

/-- Physical parameters and initial data from which to construct a pendulum. -/
structure Params where
  /-- The inertial mass assigned to the supported pivot particle. -/
  pivotMass : ℝ+
  /-- The inertial mass assigned to the moving bob particle. -/
  bobMass : ℝ+
  /-- The fixed pivot-to-bob distance. -/
  L : ℝ+
  /-- The positive magnitude of uniform downward gravitational acceleration. -/
  g : ℝ+
  /-- The bob's initial direction from the pivot, measured from downward vertical. -/
  θ0 : Real.Angle
  /-- The initial rate of change of that direction. -/
  ω0 : ℝ

/-- Data and evidence showing that a two-dimensional Newtonian particle system is a simple
pendulum.

This structure adds no physical objects to `system`. It identifies two existing particles and
existing forces as the pivot, bob, tension, and support, then states that these are all the relevant
objects and that they satisfy the defining relations of a simple pendulum. -/
structure Specs (system : ParticleMechanics.System 2) where
  /-- The frame coordinates preserve Euclidean lengths and perpendicular directions. -/
  orthonormal : system.frame.Orthonormal
  /-- The system particle that serves as the pivot. -/
  pivot : system.Particle
  /-- The pivot's whole trajectory is the frame origin. -/
  pivot_at_origin : pivot.pos = 0
  /-- The positive separation imposed between pivot and bob. -/
  L : ℝ+
  /-- The system particle that serves as the bob. -/
  bob : system.Particle
  /-- The bob remains on the circle of radius `L` centered at the fixed pivot. -/
  length_constant : ∀ t, ‖bob.pos t‖ = L
  /-- The pivot and bob are the only particles in the system. -/
  no_other_particles : Set.univ = {pivot, bob}
  /-- The internal force that represents the pivot's pull on the bob. -/
  tension : system.frame.InternalForce
  /-- The tension force acts on the bob. -/
  tension_targets_bob : tension.target = bob
  /-- Tension has no tangential component: it lies along the pivot-bob line. -/
  tension_central : tension.Central
  /-- The only internal interaction is tension and its equal-and-opposite reaction on the pivot. -/
  no_other_internal_forces : system.internalForces = {tension, tension.reverse}
  /-- The external force that keeps the pivot on its prescribed trajectory. -/
  pivotSupportForce : system.frame.Force
  /-- The support force acts on the pivot. -/
  support_targets_pivot : pivotSupportForce.target = pivot
  /-- The positive gravitational acceleration shared by both particles. -/
  g : ℝ+
  /-- The environment contributes exactly gravity on each mass and support at the pivot. -/
  no_other_external_forces :
    system.externalForces = {gravity bob g, gravity pivot g, pivotSupportForce}

end Pendulum

/-!
## B. Pendulums
-/

/-- A Newtonian particle system together with evidence that it is a simple pendulum. -/
structure Pendulum extends ParticleMechanics.System 2, Pendulum.Specs toSystem

namespace Pendulum

/-!
## C. Angular variables and period

The angle is derived from the bob's position rather than stored as independent data, so the angle
cannot disagree with the particle trajectory. The period is likewise derived from the bob's
motion, not supplied as a separate parameter.
-/

/-- The period of a pendulum if the pendulum is periodic. -/
def period (self : Pendulum) : Option ℝ :=
  let periods : Set ℝ := {T > 0 | Function.Periodic self.bob.pos T}
  if fundamentalPeriodExists : ∃ T, IsLeast periods T then
    some (Classical.choose fundamentalPeriodExists)
  else
    none

/-- The bob's direction from the pivot, measured counterclockwise from downward vertical. -/
def θ (self : Pendulum) (t : Time) : Real.Angle :=
  let x := (self.bob.pos t).components 0
  let y := (self.bob.pos t).components 1
  Complex.arg ⟨-y, x⟩

/-- Cancellation for the action that identifies real numbers differing by whole turns.

This allows angles to be differentiated without choosing one preferred real-valued representative
for each angle. -/
instance : IsCancelVAdd (AddSubgroup.zmultiples <| 2 * Real.pi).op ℝ where
  left_cancel' _ _ _ equality := add_right_cancel equality
  right_cancel' _ _ _ equality :=
    Subtype.ext <| AddOpposite.unop_injective <| add_left_cancel equality

/-- Regard the circle of angles as locally one-dimensional real space. -/
instance : ChartedSpace ℝ Real.Angle := AddAction.instChartedSpaceQuotient

/-- The time derivative of the angle trajectory, taken directly on the circle of angles. -/
def ω (self : Pendulum) (t : Time) : ℝ :=
  Time.manifoldDeriv 𝓘(ℝ) self.θ t

/-- Extract the pendulum's masses, constants, and angular state at time zero. -/
def params (self : Pendulum) : Params where
  pivotMass := self.pivot.mass
  bobMass := self.bob.mass
  L := self.L
  g := self.g
  θ0 := self.θ 0
  ω0 := self.ω 0
