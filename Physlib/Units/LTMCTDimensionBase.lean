/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.Dimension
/-!

# PhysLib's default dimension basis

`LTMCTDimensionBase` is PhysLib's default basis of base dimensions — length, time,
mass, charge and temperature. `Dimension LTMCTDimensionBase` is the familiar
five-exponent dimension, and this module provides the concrete API on top of the
generic `Dimension B`:

* the `.length`, `.time`, `.mass`, `.charge`, `.temperature` exponent projections;
* the `ofLTMCTDimensionBase` constructor from five exponents; and
* the named generators `L𝓭`, `T𝓭`, `M𝓭`, `C𝓭`, `Θ𝓭`, shown to be the generic
  `single` base vectors.

This basis is *charge*-based with five generators, so it is deliberately **not** the
SI/ISQ base-quantity set (which takes electric current as base and adds amount of
substance and luminous intensity); see `ISQDimensionBase`.

-/

@[expose] public section

/-- PhysLib's default basis of base dimensions — `length`, `time`, `mass`,
  `charge`, `temperature`. Note this is *charge*-based, so it is not the SI/ISQ
  base-quantity set; see `Dimension`. -/
inductive LTMCTDimensionBase where
  /-- The length base dimension. -/
  | length
  /-- The time base dimension. -/
  | time
  /-- The mass base dimension. -/
  | mass
  /-- The charge base dimension. -/
  | charge
  /-- The temperature base dimension. -/
  | temperature
deriving DecidableEq

namespace LTMCTDimensionBase

instance : Fintype LTMCTDimensionBase where
  elems := {.length, .time, .mass, .charge, .temperature}
  complete := fun x => by cases x <;> decide

open Dimension in
/-- The fixed five-component exponent tuple for PhysLib's default dimension basis. -/
abbrev Exponents := Exponent × Exponent × Exponent × Exponent × Exponent

instance : DimensionBasis LTMCTDimensionBase where
  Exponents := Exponents
  addCommGroup := inferInstance
  exponentEquiv :=
    { toFun := fun ⟨l, t, m, c, temp⟩ => fun
        | .length => l | .time => t | .mass => m | .charge => c | .temperature => temp
      invFun f := ⟨f .length, f .time, f .mass, f .charge, f .temperature⟩
      left_inv e := by rcases e; rfl
      right_inv f := by funext b; cases b <;> rfl
      map_add' _ _ := by funext b; cases b <;> rfl }

end LTMCTDimensionBase

namespace Dimension

/-!

## The LTMCTDimensionBase projections

The five base-dimension exponents of a `Dimension LTMCTDimensionBase`, provided so that
the familiar `.length`, `.time`, `.mass`, `.charge`, `.temperature` API is available.

-/

/-- The length exponent of a `LTMCTDimensionBase` dimension. -/
def length (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.1
/-- The time exponent of a `LTMCTDimensionBase` dimension. -/
def time (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.1
/-- The mass exponent of a `LTMCTDimensionBase` dimension. -/
def mass (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.2.1
/-- The charge exponent of a `LTMCTDimensionBase` dimension. -/
def charge (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.2.2.1
/-- The temperature exponent of a `LTMCTDimensionBase` dimension. -/
def temperature (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.2.2.2

@[simp]
lemma exponent_length (d : Dimension LTMCTDimensionBase) : d.exponent .length = d.length := rfl

@[simp]
lemma exponent_time (d : Dimension LTMCTDimensionBase) : d.exponent .time = d.time := rfl

@[simp]
lemma exponent_mass (d : Dimension LTMCTDimensionBase) : d.exponent .mass = d.mass := rfl

@[simp]
lemma exponent_charge (d : Dimension LTMCTDimensionBase) : d.exponent .charge = d.charge := rfl

@[simp]
lemma exponent_temperature (d : Dimension LTMCTDimensionBase) :
    d.exponent .temperature = d.temperature := rfl

/-- Build a `LTMCTDimensionBase` dimension from its five exponents, in the order
  `⟨length, time, mass, charge, temperature⟩`. -/
def ofLTMCTDimensionBase (length time mass charge temperature : Exponent) :
    Dimension LTMCTDimensionBase :=
  ⟨(length, time, mass, charge, temperature)⟩

@[simp]
lemma ofLTMCTDimensionBase_length (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).length = l := rfl

@[simp]
lemma ofLTMCTDimensionBase_time (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).time = t := rfl

@[simp]
lemma ofLTMCTDimensionBase_mass (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).mass = m := rfl

@[simp]
lemma ofLTMCTDimensionBase_charge (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).charge = c := rfl

@[simp]
lemma ofLTMCTDimensionBase_temperature (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).temperature = θ := rfl

@[simp]
lemma time_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

@[simp]
lemma one_length : (1 : Dimension LTMCTDimensionBase).length = 0 := rfl
@[simp]
lemma one_time : (1 : Dimension LTMCTDimensionBase).time = 0 := rfl

@[simp]
lemma one_mass : (1 : Dimension LTMCTDimensionBase).mass = 0 := rfl

@[simp]
lemma one_charge : (1 : Dimension LTMCTDimensionBase).charge = 0 := rfl

@[simp]
lemma one_temperature : (1 : Dimension LTMCTDimensionBase).temperature = 0 := rfl

@[simp]
lemma inv_length (d : Dimension LTMCTDimensionBase) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension LTMCTDimensionBase) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension LTMCTDimensionBase) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension LTMCTDimensionBase) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension LTMCTDimensionBase) : d⁻¹.temperature = -d.temperature := rfl

@[simp]
lemma div_length (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 / d2).length = d1.length - d2.length := by
  simpa only [exponent_length] using div_exponent d1 d2 .length

@[simp]
lemma div_time (d1 d2 : Dimension LTMCTDimensionBase) : (d1 / d2).time = d1.time - d2.time := by
  simpa only [exponent_time] using div_exponent d1 d2 .time

@[simp]
lemma div_mass (d1 d2 : Dimension LTMCTDimensionBase) : (d1 / d2).mass = d1.mass - d2.mass := by
  simpa only [exponent_mass] using div_exponent d1 d2 .mass

@[simp]
lemma div_charge (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 / d2).charge = d1.charge - d2.charge := by
  simpa only [exponent_charge] using div_exponent d1 d2 .charge

@[simp]
lemma div_temperature (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 / d2).temperature = d1.temperature - d2.temperature := by
  simpa only [exponent_temperature] using div_exponent d1 d2 .temperature

@[simp]
lemma npow_length (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).length = n • d.length := by
  simpa only [exponent_length] using npow_exponent d n .length

@[simp]
lemma npow_time (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).time = n • d.time := by
  simpa only [exponent_time] using npow_exponent d n .time

@[simp]
lemma npow_mass (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).mass = n • d.mass := by
  simpa only [exponent_mass] using npow_exponent d n .mass

@[simp]
lemma npow_charge (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).charge = n • d.charge := by
  simpa only [exponent_charge] using npow_exponent d n .charge

@[simp]
lemma npow_temperature (d : Dimension LTMCTDimensionBase) (n : ℕ) :
    (d ^ n).temperature = n • d.temperature := by
  simpa only [exponent_temperature] using npow_exponent d n .temperature

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 1 0 0 0 0

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 1 0 0 0

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 0 1 0 0

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 0 0 1 0

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 0 0 0 1

/-!

## The named generators are the base vectors

Each named generator `L𝓭`, `T𝓭`, … is the generic `single` base vector at the
corresponding base dimension, exhibiting them as instances of the basis-generic API.

-/

lemma L𝓭_eq_single : L𝓭 = single .length := by
  ext b; cases b <;> simp [L𝓭, ofLTMCTDimensionBase, length, time, mass, charge, temperature]

lemma T𝓭_eq_single : T𝓭 = single .time := by
  ext b; cases b <;> simp [T𝓭, ofLTMCTDimensionBase, length, time, mass, charge, temperature]

lemma M𝓭_eq_single : M𝓭 = single .mass := by
  ext b; cases b <;> simp [M𝓭, ofLTMCTDimensionBase, length, time, mass, charge, temperature]

lemma C𝓭_eq_single : C𝓭 = single .charge := by
  ext b; cases b <;> simp [C𝓭, ofLTMCTDimensionBase, length, time, mass, charge, temperature]

lemma Θ𝓭_eq_single : Θ𝓭 = single .temperature := by
  ext b; cases b <;> simp [Θ𝓭, ofLTMCTDimensionBase, length, time, mass, charge, temperature]

end Dimension
