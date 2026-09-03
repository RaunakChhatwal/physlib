/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Algebra.Order.Positive.Field
public import Physlib.ClassicalMechanics.Force
public import Physlib.SpaceAndTime.Time.Derivatives
/-!
# Point-particle mechanics

This module defines Newtonian point particles and finite systems of particles.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d}

/-- Positive real numbers. -/
notation "ℝ+" => {x : ℝ // 0 < x}

/-- Scalar multiplication by a positive real. -/
instance {α : Type*} [SMul ℝ α] : SMul ℝ+ α where
  smul c x := c.val • x

/-!
## A. Point particles

A point particle has a positive mass and a trajectory relative to a reference frame.
-/

/-- A point particle in `frame`. -/
structure Particle (frame : ReferenceFrame d) where
  /-- The particle's mass. -/
  mass : ℝ+
  /-- The particle's position in frame coordinates. -/
  pos : Time → frame.Vector
  pos_twice_differentiable :
    frame.IsInertial → Differentiable ℝ pos ∧ Differentiable ℝ (Time.deriv pos)

namespace Particle

variable (particle : frame.Particle)

/-- Position is differentiable in an inertial frame. -/
instance [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.pos) :=
  ⟨particle.pos_twice_differentiable h.out |>.left⟩

/-- The particle's velocity. -/
def vel [_h : Fact (Differentiable ℝ particle.pos)] : Time → frame.Vector :=
  Time.deriv particle.pos

/-- Velocity is differentiable in an inertial frame. -/
instance [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.vel) :=
  ⟨particle.pos_twice_differentiable h.out |>.right⟩

/-- The particle's acceleration. -/
def acc [Fact (Differentiable ℝ particle.pos)] [_h : Fact (Differentiable ℝ particle.vel)] :
    Time → frame.Vector :=
  Time.deriv particle.vel

/-- The particle's position in affine space. -/
def pointInSpace (t : Time) : Space d :=
  Vector.dispEquiv t (particle.pos t) +ᵥ frame.origin t

end Particle

end ClassicalMechanics.ReferenceFrame

namespace ClassicalMechanics.PointParticle

open ReferenceFrame

variable {d : ℕ}

/-!
## B. Systems
-/

/-- A finite system of point particles satisfying Newton's laws. -/
structure System (d : ℕ) where
  /-- The system's reference frame. -/
  frame : ReferenceFrame d
  [isInertial : Fact frame.IsInertial]

  /-- The particles in the system. -/
  particles : Multiset frame.Particle

  /-- Forces between particles in the system. -/
  internalForces : Multiset (frame.InternalForce particles)
  /-- Forces on the system from external sources. -/
  externalForces : Multiset (frame.Force particles)

  newton_second_law : ∀ particle : particles,
    netForce particle internalForces externalForces = particle.1.mass • particle.1.acc

  newton_third_law : internalForces.map .reverse = internalForces

namespace System

variable (system : System d)

instance : Fact system.frame.IsInertial :=
  system.isInertial

/-!
## C. System particles
-/

/-- Vectors in the system's frame. -/
abbrev Vector := system.frame.Vector

/-- A particle in `system`. -/
abbrev Particle : Type := system.particles

namespace Particle

variable {system : System d} (particle : system.Particle) (t : Time)

/-- The particle's mass. -/
def mass : ℝ+ := particle.1.mass

/-- The particle's position at `t`. -/
def pos : system.Vector := particle.1.pos t

/-- The particle's velocity at `t`. -/
def vel : system.Vector := particle.1.vel t

/-- The particle's acceleration at `t`. -/
def acc : system.Vector := particle.1.acc t

/-- The particle's momentum at `t`. -/
def momentum : system.Vector := particle.mass • particle.vel t

/-- The particle's kinetic energy at `t`. -/
def kineticEnergy : ℝ := particle.mass * ‖particle.vel t‖ ^ 2 / 2

end Particle

/-!
## D. System forces
-/

/-- A force in `system`. -/
abbrev Force : Type :=
  system.internalForces ⊕ system.externalForces

namespace Force

variable {system : System d} (force : system.Force)

/-- The underlying force. -/
@[coe] def inner : system.frame.Force system.Particle :=
  match force with | .inl force => force | .inr force => force

instance : Coe system.Force (system.frame.Force system.Particle) := Coe.mk inner

/-- The force at `t`. -/
def value (t : Time) : system.Vector := force.inner.value t

instance : CoeFun system.Force (fun _ => Time → system.Vector) where
  coe := value

/-- The force's target. -/
def target : system.Particle := force.inner.target

/-- Whether `force` is internal. -/
def Internal : Prop := force.isLeft

/-- Whether `force` is external. -/
def External : Prop := force.isRight

end Force

/-- An internal force in `system`. -/
abbrev InternalForce : Type := system.internalForces

namespace InternalForce

variable {system : System d} (force : system.InternalForce)

/-- View an internal force as a system force. -/
instance : Coe system.InternalForce system.Force := Coe.mk .inl

/-- The force at `t`. -/
def value (t : Time) : system.Vector := force.1.value t

/-- The force's target. -/
def target : system.Particle := force.1.target

/-- The force's source. -/
def source : system.Particle := force.1.source

/-- A force and its reverse have the same multiplicity. -/
lemma reverse_count_eq :
    system.internalForces.count force.1.reverse = system.internalForces.count force.1 := by
  rw [← congrArg (Multiset.count force.1.reverse) system.newton_third_law]
  refine Multiset.count_map_eq_count' _ _ (Function.Involutive.injective ?_) _
  intro internalForce
  rcases internalForce with ⟨⟨value, target⟩, source, source_ne_target⟩
  simp [ReferenceFrame.InternalForce.reverse]

/-- The reverse force. -/
def reverse : system.InternalForce :=
  ⟨force.1.reverse, (finCongr force.reverse_count_eq).symm force.2⟩

/-- Whether the force lies along the line joining its source and target. -/
def Central : Prop :=
  ∀ t, ∃ c : ℝ, force.value t = c • (force.target.pos t - force.source.pos t)

end InternalForce

/-!
## E. Aggregate quantities
-/

variable (t : Time)

/-- Total mass. -/
def mass : ℝ :=
  ∑ particle : system.Particle, particle.mass

/-- Total momentum at `t`. -/
def momentum : system.Vector :=
  ∑ particle : system.Particle, particle.momentum t

/-- Net external force at `t`. -/
def netExternalForce : system.Vector :=
  ∑ force : system.Force with force.External, force t

/-- Total kinetic energy at `t`. -/
def kineticEnergy : ℝ :=
  ∑ particle : system.Particle, particle.kineticEnergy t

end ClassicalMechanics.PointParticle.System
