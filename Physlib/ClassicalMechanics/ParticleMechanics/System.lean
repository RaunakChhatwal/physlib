/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Physlib.ClassicalMechanics.ParticleMechanics.Basic
/-!
# Systems of particles

A `System` selects finitely many particles to study together. A force between two selected
particles is internal, while a force exerted from outside the selection is external. This
classification depends on the chosen system boundary: changing the selection changes which causes
are represented explicitly, not the physical interaction itself.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ParticleMechanics

variable {d : ℕ}

/-!
## A. Particle systems
-/

/-- A finite collection of particles and forces satisfying Newton's laws. -/
structure System (d : ℕ) where
  /-- The inertial frame in which all positions and force vectors are represented. -/
  frame : InertialReferenceFrame d
  /-- All particles included in the system. -/
  particles : Finset frame.Particle
  /-- The forces whose source and target are both particles in the system. -/
  internalForces : Multiset frame.InternalForce
  /-- The forces exerted on system particles by sources outside the system. -/
  externalForces : Multiset frame.Force
  /-- Every force target, and every internal-force source, belongs to `particles`. -/
  forces_involve_self : frame.particlesInvolved internalForces externalForces ⊆ particles
  /-- The net force on a particle equals its mass times its acceleration -/
  newton_second_law :
    ∀ particle ∈ particles, ∀ t,
      particle.netForce internalForces externalForces t = particle.mass • particle.acc t
  /-- For every force, there is an equal and opposite force -/
  newton_third_law : internalForces.map .reverse = internalForces

namespace System

/-!
## B. System particles

Once a system has fixed its particles, later definitions should range only over those particles.
`System.Particle` pairs a particle with evidence that it belongs to the system.
-/

/-- Coordinate vectors interpreted in the system's chosen frame. -/
abbrev Vector (system : System d) := system.frame.Vector

/-- A particle together with evidence that it belongs to `system`. -/
structure Particle (system : System d) extends system.frame.Particle where
  /-- Evidence that the underlying particle belongs to the system. -/
  membership : toParticle ∈ system.particles

namespace Particle

instance (system : System d) : Coe system.Particle system.frame.Particle where
  coe := Particle.toParticle

instance (system : System d) : Fintype system.Particle :=
  Fintype.ofSurjective (fun particle : system.particles => ⟨particle, particle.property⟩)
    fun ⟨particle, membership⟩ => ⟨⟨particle, membership⟩, rfl⟩

end Particle

/-!
## C. Aggregate quantities

The following quantities add contributions from all particles in the system. The sums describe the
system as a whole, but they do not introduce an additional composite particle.
-/

/-- The sum of all external forces acting on the system. -/
def netExternalForce (system : System d) (t : Time) : system.Vector :=
  ∑ externalForce : system.externalForces, externalForce.1 t

/-- The sum of the masses of all particles in the system. -/
def mass (system : System d) : ℝ :=
  ∑ particle : system.Particle, particle.mass

/-- The mass-weighted mean of the particles' positions. -/
def centerOfMass (system : System d) (t : Time) : system.Vector :=
  system.mass⁻¹ • ∑ particle : system.Particle, particle.mass • particle.pos t

/-- The vector sum of the momenta of all particles in the system. -/
def momentum (system : System d) (t : Time) : system.Vector :=
  ∑ particle : system.Particle, particle.momentum t

/-- The sum of the frame-relative kinetic energies of all particles in the system. -/
def kineticEnergy (system : System d) (t : Time) : ℝ :=
  ∑ particle : system.Particle, particle.kineticEnergy t

end System

end ClassicalMechanics.ParticleMechanics
