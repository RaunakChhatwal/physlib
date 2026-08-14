/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Data.Multiset.Fintype
public import Physlib.SpaceAndTime.Time.Derivatives
public import Physlib.SpaceAndTime.ReferenceFrame
/-!
# Particle mechanics

This module describes particles and individual forces. A `Particle` has an inertial mass and a
position at every time, expressed in one reference frame. Velocity and acceleration are derived from
that position. A `Force` gives the value of one force over time and names the particle on which it
acts.

These definitions specify the objects in the model, but do not yet say that the forces produce the
recorded motion. `ParticleMechanics.System` adds that dynamical relation by requiring Newton's
laws. Thus particles and forces are introduced first, and the equations relating them are imposed
separately.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d}

/-- Values of `T` carrying evidence that they are strictly greater than zero. -/
-- abbrev Type.Pos (T : Type) [LT T] [Zero T] := {x : T // 0 < x}

notation "ℝ+" => {x : ℝ // 0 < x}

/-- Use a positive real as a scalar without discarding its positivity witness. -/
instance {α : Type*} [SMul ℝ α] : SMul ℝ+ α where
  smul c x := c.val • x

/-!
## A. Particles

In this model, a Newtonian point particle has mass but no orientation, shape, or internal degrees of
freedom. It occupies one point in space at each time. The definition stores its position as
coordinates relative to a chosen reference frame.
-/

/-- A Newtonian point particle described relative to `frame`. -/
structure Particle (frame : ReferenceFrame d) where
  /-- The particle's positive, time-independent inertial mass. -/
  mass : ℝ+
  /-- Its displacement from the frame origin, given in frame coordinates at every time. -/
  pos : Time → frame.Vector
  /-- In an inertial frame, the position and its derivative are differentiable. -/
  pos_twice_differentiable [Fact frame.IsInertial] :
    Differentiable ℝ pos ∧ Differentiable ℝ (Time.deriv pos)

namespace Particle

variable (particle : frame.Particle)

/-- A particle observed in an inertial frame has differentiable position. -/
instance [Fact frame.IsInertial] : Fact (Differentiable ℝ particle.pos) :=
  ⟨particle.pos_twice_differentiable.left⟩

/-- The first time derivative of the particle's coordinate position. -/
def vel [Fact (Differentiable ℝ particle.pos)] :
    Time → frame.Vector :=
  Time.deriv particle.pos

/-- A particle observed in an inertial frame has differentiable velocity. -/
instance [Fact frame.IsInertial] :  Fact (Differentiable ℝ particle.vel) :=
  ⟨particle.pos_twice_differentiable.right⟩

/-- The second time derivative of the particle's coordinate position. -/
def acc [Fact (Differentiable ℝ particle.pos)] [Fact (Differentiable ℝ particle.vel)] :
    Time → frame.Vector :=
  Time.deriv particle.vel

/-- Convert the particle's coordinate position at `t` into a point of affine space. -/
def pointInSpace (t : Time) : Space d :=
  Vector.dispEquiv t (particle.pos t) +ᵥ frame.origin t

/-- m * v -/
def momentum [Fact (Differentiable ℝ particle.pos)] (t : Time) : frame.Vector :=
  particle.mass • particle.vel t

/-- m * |v|^2 / 2 -/
def kineticEnergy [Fact frame.IsMetricConserved] [Fact (Differentiable ℝ particle.pos)]
    (t : Time) : ℝ :=
  particle.mass * ‖particle.vel t‖ ^ 2 / 2

end Particle

/-!
## B. Forces

A `Force` represents one particular force, not the sum of all forces on a particle.
An external force names only the particle it acts on, because its source lies outside the
chosen system. An internal force also names its source particle within the system.
-/

/-- A time-dependent force together with the particle on which it acts. -/
structure Force (frame : ReferenceFrame d) where
  /-- The force vector at each time. -/
  value : Time → frame.Vector
  /-- The particle on which the force acts. -/
  target : frame.Particle

instance : CoeFun frame.Force (fun _ => Time → frame.Vector) where
  coe := Force.value

/-- A force whose source and target are both explicit particles. -/
structure InternalForce (frame : ReferenceFrame d) extends frame.Force where
  /-- The particle that exerts the force. -/
  source : frame.Particle
  /-- An internal force must connect two distinct particles. -/
  source_ne_target : source ≠ target

instance : CoeFun frame.InternalForce (fun _ => Time → frame.Vector) where
  coe force := force.value

namespace InternalForce

/-- Whether the force always lies along the line from its target to its source.

The scalar may have either sign, so this includes attraction and repulsion. -/
def Central (force : frame.InternalForce) : Prop :=
  ∀ t, ∃ c : ℝ, force t = c • (force.source.pos t - force.target.pos t)

/-- The equal-and-opposite force obtained by exchanging source and target. -/
def reverse (force : frame.InternalForce) : frame.InternalForce where
  value := -force.value
  target := force.source
  source := force.target
  source_ne_target := force.source_ne_target.symm

end InternalForce

/-!
## C. Resultant forces

Forces are collected in multisets so that two separately recorded forces are still counted twice,
even when their values, sources, and targets agree. The resultant force on a particle is found by
selecting the forces that act on it and adding their vectors.
-/

/-- Every particle named as a source or target by the given forces. -/
def particlesInvolved
    (internalForces : Multiset frame.InternalForce)
    (externalForces : Multiset frame.Force) : Finset frame.Particle :=
  (internalForces.map InternalForce.source).toFinset ∪
    (internalForces.map (fun force => force.target)).toFinset ∪
      (externalForces.map Force.target).toFinset

/-- Add exactly the external forces whose target is `particle`. -/
def Particle.netExternalForce
    (particle : frame.Particle)
    (externalForces : Multiset frame.Force)
    (t : Time) : frame.Vector :=
  ∑ force : externalForces.filter fun force => force.target = particle, force.1 t

/-- The resultant of every recorded internal and external force targeting `particle`. -/
def Particle.netForce
    (particle : frame.Particle)
    (internalForces : Multiset frame.InternalForce)
    (externalForces : Multiset frame.Force)
    (t : Time) : frame.Vector :=
  (∑ force : internalForces.filter fun force => force.target = particle, force.1 t) +
    particle.netExternalForce externalForces t
