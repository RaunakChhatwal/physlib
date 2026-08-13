/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.Basic
/-!
# Reference frames

A point in space and a list of coordinates are different kinds of data. Assigning coordinates to a
point requires an origin and a basis for measuring displacements from that origin. A
`ReferenceFrame` records those choices at every time.

This distinction is built into `Space d`, which is an affine space. Two points determine a
displacement, but no point is automatically the zero point. The chosen origin therefore belongs to
the frame, not to space itself. Similarly, a displacement has coordinate components only after a
basis has been chosen.

A general frame may accelerate, rotate, or deform. An `InertialReferenceFrame` allows only uniform
translation. The units and the choice of time zero are already fixed by `Time`.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics

variable {d : ℕ}

/-!
## A. Reference frames

A reference frame can be pictured as a coordinate grid carried through time. It is part of how
motion is described, not an additional physical object moving with the particles.
-/

/-- A time-indexed choice of affine origin and displacement basis in `d`-dimensional space. -/
structure ReferenceFrame (d : ℕ) where
  /-- The point assigned coordinate zero at each time. -/
  origin : Time → Space d
  /-- The basis used to turn displacement vectors into coordinate components at each time. -/
  basis : Time → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))

/-- Build a reference frame from the trajectories of a collection of reference points.

At each time, the reference points must form an affine basis: none is redundant, and together they
span the whole space. One reference point is chosen as the origin, and the displacements from it to
the remaining points form the coordinate basis. The resulting frame need not be inertial or
orthonormal. -/
def ReferenceFrame.fromReferencePoints
    (referencePoints : Finset (Time → Space d))
    (independence : ∀ t, AffineIndependent ℝ fun point : referencePoints => point.val t)
    (spans_space : ∀ t, affineSpan ℝ {point.val t | point : referencePoints} = ⊤) :
    ReferenceFrame d :=
  let affineBasis (t : Time) : AffineBasis referencePoints ℝ (Space d) :=
    ⟨fun point => point.val t, independence t, spans_space t⟩
  let reference_points_not_empty := (affineBasis 0).nonempty
  let origin := Classical.choice reference_points_not_empty
  letI := Fintype.ofFinite {point : referencePoints // point ≠ origin}
  let basis t := (affineBasis t).basisOf origin
  let other_reference_points_size_eq_dim : Fintype.card {point : referencePoints // point ≠ origin} = d :=
    by simpa using (Module.finrank_eq_card_basis <| basis 0).symm
  let basisReindexed t := (basis t).reindex (Fintype.equivFinOfCardEq other_reference_points_size_eq_dim)
  { origin := origin, basis := basisReindexed }

/-!
## B. Inertial reference frames

In Newtonian mechanics, an inertial coordinate grid does not rotate or change scale, and its origin
moves in a straight line at constant velocity. These conditions restrict the frame, not the
particles described in that frame.
-/

/-- A reference frame related to its initial grid by uniform translation alone. -/
structure InertialReferenceFrame (d : ℕ) extends ReferenceFrame d where
  /-- The time-independent velocity of the coordinate origin. -/
  velocity : EuclideanSpace ℝ (Fin d)
  /-- Elapsed time times `velocity` is exactly the origin's displacement. -/
  origin_moves_uniformly :
    ∀ t₁ t₂, toReferenceFrame.origin t₂ -ᵥ toReferenceFrame.origin t₁ = (t₂ - t₁).val • velocity
  /-- The coordinate axes neither rotate nor change scale with time. -/
  basis_conserved : ∀ t₁ t₂, toReferenceFrame.basis t₁ = toReferenceFrame.basis t₂

namespace InertialReferenceFrame

/-- Whether the frame's coordinate basis is orthonormal. -/
def Orthonormal (frame : InertialReferenceFrame d) : Prop :=
  _root_.Orthonormal ℝ (frame.basis 0)

/-!
## C. Vectors in an inertial reference frame

`Vector frame` stores the coordinates of a displacement; it is not a second kind of geometric
displacement. Its dependence on `frame` records which basis gives those coordinates their meaning.
The map `linearEquiv` converts the coordinates back into the displacement they represent.
-/

/-- The `d` real components used to represent a displacement in `frame`. -/
structure Vector (frame : InertialReferenceFrame d) where
  /-- One scalar coefficient for each axis of the frame. -/
  components : Fin d → ℝ

namespace Vector

variable {frame : InertialReferenceFrame d}

instance : AddCommGroup frame.Vector :=
  (Equiv.mk components mk Eq.refl Eq.refl).addCommGroup

instance : Module ℝ frame.Vector :=
  (Equiv.mk components mk Eq.refl Eq.refl).module ℝ

/-- Convert a frame vector to its tuple of coordinate components. -/
def componentLinearEquiv (frame : InertialReferenceFrame d) : frame.Vector ≃ₗ[ℝ] (Fin d → ℝ) where
  toFun := components
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Interpret coordinate components as a geometric displacement using the frame's basis. -/
def linearEquiv (frame : InertialReferenceFrame d) : frame.Vector ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  -- The basis at time zero suffices because an inertial frame conserves its basis
  (componentLinearEquiv frame).trans (frame.basis 0).equivFun.symm

/-- The coordinate-free displacement represented by `v`. -/
def asDisplacement (v : frame.Vector) : EuclideanSpace ℝ (Fin d) :=
  linearEquiv frame v

instance : NormedAddCommGroup frame.Vector :=
  NormedAddCommGroup.induced _ _ (linearEquiv frame).toLinearMap (linearEquiv frame).injective

instance : NormedSpace ℝ frame.Vector :=
  NormedSpace.induced ℝ _ _ (linearEquiv frame).toLinearMap
