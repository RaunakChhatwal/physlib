/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Physlib.SpaceAndTime.ReferenceFrame
/-!
# Forces

This module defines time-dependent forces in a reference frame.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d} {Object : Type}

/-!
## A. Individual forces
-/

/-- A time-dependent force acting on an object. -/
structure Force (frame : ReferenceFrame d) (Object : Type) where
  /-- The force vector. -/
  value : Time → frame.Vector
  /-- The target object. -/
  target : Object

instance : CoeFun (frame.Force Object) (fun _ => Time → frame.Vector) where
  coe := Force.value

/-- A force between two objects. -/
structure InternalForce (frame : ReferenceFrame d) (Object : Type) extends frame.Force Object where
  /-- The source object. -/
  source : Object
  source_ne_target : source ≠ target

instance : CoeFun (frame.InternalForce Object) (fun _ => Time → frame.Vector) where
  coe force := force.value

instance : Coe (frame.InternalForce Object) (frame.Force Object) where
  coe := InternalForce.toForce

/-- The equal-and-opposite force with source and target exchanged. -/
def InternalForce.reverse (force : frame.InternalForce Object) : frame.InternalForce Object where
  value := -force.value
  target := force.source
  source := force.target
  source_ne_target := force.source_ne_target.symm

/-!
## B. Resultant force
-/

/-- The net force on `object`. -/
def netForce
    (object : Object)
    (internalForces : Multiset (frame.InternalForce Object))
    (externalForces : Multiset (frame.Force Object))
    (t : Time) : frame.Vector :=
  let forces := internalForces.map InternalForce.toForce + externalForces
  ∑ force : forces with force.1.target = object, force.1 t
