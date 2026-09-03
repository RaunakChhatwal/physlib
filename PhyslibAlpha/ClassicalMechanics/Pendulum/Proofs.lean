module

import PhyslibAlpha.ClassicalMechanics.Pendulum.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.EMetricSpace.Weak

namespace ClassicalMechanics.Pendulum.Internal

noncomputable section
open scoped Classical
open scoped Finset
open scoped Manifold
open scoped Topology

lemma vector_norm_l2_if_orthonormal {d : ℕ} {frame : ReferenceFrame d}
    [Fact frame.IsMetricConserved]
    (frame_orthonormal : frame.Orthonormal) (x : frame.Vector) :
    ‖x‖ = √(∑ i, (x.components i) ^ 2) := by
  let basis := frame.basis 0
  let orthonormalBasis := basis.toOrthonormalBasis (frame_orthonormal 0)
  change ‖basis.equivFun.symm x.components‖ = _
  calc
    _ = ‖orthonormalBasis.repr.symm (WithLp.toLp 2 x.components)‖ := by rfl
    _ = ‖WithLp.toLp 2 x.components‖ := orthonormalBasis.repr.symm.norm_map _
    _ = √(∑ i, (x.components i) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]

lemma periodOption_edist_self (x : Option ℝ) :
    @edist (Option ℝ) Option.toEDist x x = 0 :=
  Option.edist_self' inferInstance x

lemma periodOption_edist_comm (x y : Option ℝ) :
    @edist (Option ℝ) Option.toEDist x y = @edist (Option ℝ) Option.toEDist y x :=
  Option.edist_comm' inferInstance x y

lemma periodOption_edist_triangle (x y z : Option ℝ) :
    @edist (Option ℝ) Option.toEDist x z ≤
      @edist (Option ℝ) Option.toEDist x y + @edist (Option ℝ) Option.toEDist y z :=
  Option.edist_triangle' inferInstance x y z

lemma periodOption_eq_of_edist_eq_zero {x y : Option ℝ}
    (distance_zero : @edist (Option ℝ) Option.toEDist x y = 0) :
    x = y := by
  cases x <;> cases y <;> simp_all

noncomputable def paramsFrame : ReferenceFrame 2 where
  origin := fun _ ↦ Classical.choice inferInstance
  basis := fun _ ↦ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

lemma paramsFrame_isInertial : paramsFrame.IsInertial where
  origin_moves_uniformly := ⟨0, by intro t₁ t₂; simp [paramsFrame]⟩
  basis_conserved := by intro _ _; rfl

local instance : Fact paramsFrame.IsInertial := ⟨paramsFrame_isInertial⟩

lemma paramsFrame_orthonormal : paramsFrame.Orthonormal :=
  fun _ ↦ (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal

def phaseField (params : Params) (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.2, -params.g / params.L * Real.sin state.1)

lemma phaseField_lipschitz (params : Params) :
    LipschitzWith (max 1 ‖(-params.g / params.L : ℝ)‖₊) (phaseField params) := by
  have first : LipschitzWith 1 (fun state : ℝ × ℝ ↦ state.2) :=
    LipschitzWith.prod_snd
  have second : LipschitzWith ‖(-params.g / params.L : ℝ)‖₊
      (fun state : ℝ × ℝ ↦ -params.g / params.L * Real.sin state.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    rw [← mul_sub, abs_mul, coe_nnnorm, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      |Real.sin x.1 - Real.sin y.1| ≤ |x.1 - y.1| :=
        Real.abs_sin_sub_sin_le _ _
      _ ≤ dist x y := by rw [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  exact first.prodMk second

def truncatedPhaseField (params : Params) (B : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  (max (-B) (min state.2 B), -params.g / params.L * Real.sin state.1)

lemma truncatedPhaseField_lipschitz (params : Params) (B : ℝ) :
    LipschitzWith (max 1 ‖(-params.g / params.L : ℝ)‖₊)
      (truncatedPhaseField params B) := by
  have first : LipschitzWith 1
      (fun state : ℝ × ℝ ↦ max (-B) (min state.2 B)) := by
    simpa only [one_mul, Function.comp_apply] using
      ((LipschitzWith.prod_snd (α := ℝ) (β := ℝ)).min_const B).const_max (-B)
  have second : LipschitzWith ‖(-params.g / params.L : ℝ)‖₊
      (fun state : ℝ × ℝ ↦ -params.g / params.L * Real.sin state.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    rw [← mul_sub, abs_mul, coe_nnnorm, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      |Real.sin x.1 - Real.sin y.1| ≤ |x.1 - y.1| :=
        Real.abs_sin_sub_sin_le _ _
      _ ≤ dist x y := by rw [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  exact first.prodMk second

lemma phase_solution_on (params : Params) {R : ℝ} (R_pos : 0 < R) :
    ∃ phase : ℝ → ℝ × ℝ,
      phase 0 = (params.θ0.toReal, params.ω0) ∧
      ∀ t ∈ Set.Ioo (-R) R,
        HasDerivAt phase (phaseField params (phase t)) t := by
  let c := params.g.val / params.L.val
  have c_pos : 0 < c := div_pos params.g.property params.L.property
  have coefficient_abs : |(-params.g.val) / params.L.val| = c := by
    rw [abs_div, abs_neg, abs_of_pos params.g.property, abs_of_pos params.L.property]
  let B := |params.ω0| + c * R + 1
  have B_pos : 0 < B := by positivity
  let M : NNReal := ⟨max B c, B_pos.le.trans (le_max_left _ _)⟩
  let a : NNReal := ⟨M * R, mul_nonneg M.property R_pos.le⟩
  let t0 : Set.Icc (-R) R := ⟨0, by constructor <;> linarith⟩
  let initial := (params.θ0.toReal, params.ω0)
  have field_bound (state : ℝ × ℝ) :
      ‖truncatedPhaseField params B state‖ ≤ M := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs]
      simp only [truncatedPhaseField]
      apply (abs_le.2 ⟨le_max_left _ _, max_le (neg_le_self B_pos.le) (min_le_right _ _)⟩).trans
      exact le_max_left _ _
    · rw [Real.norm_eq_abs]
      simp only [truncatedPhaseField]
      rw [abs_mul, coefficient_abs]
      calc
        c * |Real.sin state.1| ≤ c * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one state.1) c_pos.le
        _ = c := mul_one c
        _ ≤ M := le_max_right _ _
  have picard : IsPicardLindelof
      (fun _ ↦ truncatedPhaseField params B) t0 initial a 0 M
        (max 1 ‖(-params.g / params.L : ℝ)‖₊) := by
    apply IsPicardLindelof.of_time_independent
    · exact fun state _ ↦ field_bound state
    · exact (truncatedPhaseField_lipschitz params B).lipschitzOnWith
    · change M * max (R - 0) (0 - -R) ≤ M * R - 0
      simp
  obtain ⟨phase, phase_zero, phase_deriv⟩ :=
    picard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  change phase 0 = initial at phase_zero
  refine ⟨phase, phase_zero, ?_⟩
  intro t t_mem
  have truncated_deriv :=
    (phase_deriv t (Set.Ioo_subset_Icc_self t_mem)).hasDerivAt
      (Icc_mem_nhds t_mem.1 t_mem.2)
  have angular_velocity_deriv :
      HasDerivAt (fun s ↦ (phase s).2)
        (truncatedPhaseField params B (phase t)).2 t := by
    convert (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
      truncated_deriv using 1 <;> rfl
  have angular_velocity_bound : ‖(phase t).2 - params.ω0‖ ≤ c * ‖t - 0‖ := by
    have bound := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun s ↦ (phase s).2) (s := Set.Ioo (-R) R) (x := 0) (y := t) (C := c)
      (fun s s_mem ↦ by
        have derivative :=
          (phase_deriv s (Set.Ioo_subset_Icc_self s_mem)).hasDerivAt
            (Icc_mem_nhds s_mem.1 s_mem.2)
        exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s derivative).differentiableAt)
      (fun s s_mem ↦ by
        have derivative :=
          (phase_deriv s (Set.Ioo_subset_Icc_self s_mem)).hasDerivAt
            (Icc_mem_nhds s_mem.1 s_mem.2)
        have velocity_derivative :
            HasDerivAt (fun u ↦ (phase u).2)
              (truncatedPhaseField params B (phase s)).2 s := by
          convert (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s derivative using 1 <;>
            rfl
        rw [velocity_derivative.deriv, truncatedPhaseField, Real.norm_eq_abs, abs_mul]
        rw [coefficient_abs]
        exact mul_le_of_le_one_right c_pos.le (Real.abs_sin_le_one _))
      (convex_Ioo _ _) (by constructor <;> linarith) t_mem
    simpa only [phase_zero] using bound
  have velocity_lt_B : |(phase t).2| < B := by
    rw [Real.norm_eq_abs, sub_zero] at angular_velocity_bound
    calc
      |(phase t).2| = |((phase t).2 - params.ω0) + params.ω0| := by ring_nf
      _ ≤ |(phase t).2 - params.ω0| + |params.ω0| := abs_add_le _ _
      _ ≤ c * |t| + |params.ω0| := by
        rw [Real.norm_eq_abs] at angular_velocity_bound
        linarith
      _ < B := by
        dsimp only [B]
        have t_abs_lt : |t| < R := (abs_lt.2 t_mem)
        nlinarith
  have field_eq : truncatedPhaseField params B (phase t) = phaseField params (phase t) := by
    apply Prod.ext
    · simp only [truncatedPhaseField, phaseField]
      rw [min_eq_left (abs_lt.mp velocity_lt_B).2.le,
        max_eq_right (abs_lt.mp velocity_lt_B).1.le]
    · rfl
  rwa [field_eq] at truncated_deriv

lemma phase_exists (params : Params) :
    ∃ phase : ℝ → ℝ × ℝ,
      phase 0 = (params.θ0.toReal, params.ω0) ∧
      ∀ t, HasDerivAt phase (phaseField params (phase t)) t := by
  let radius := fun n : ℕ ↦ (n : ℝ) + 1
  have local_solution (n : ℕ) :
      ∃ phase : ℝ → ℝ × ℝ,
        phase 0 = (params.θ0.toReal, params.ω0) ∧
        ∀ t ∈ Set.Ioo (-(radius n)) (radius n),
          HasDerivAt phase (phaseField params (phase t)) t := by
    apply phase_solution_on
    dsimp only [radius]
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  choose phases phases_zero phases_deriv using local_solution
  have consistency (m n : ℕ) :
      Set.EqOn (phases m) (phases n)
        (Set.Ioo (-(min (radius m) (radius n))) (min (radius m) (radius n))) := by
    apply ODE_solution_unique_of_mem_Ioo
        (v := fun _ ↦ phaseField params) (s := fun _ ↦ Set.univ)
        (K := max 1 ‖(-params.g / params.L : ℝ)‖₊) (t₀ := 0)
    · intro _ _
      exact (phaseField_lipschitz params).lipschitzOnWith
    · have radius_pos : 0 < min (radius m) (radius n) := by
        apply lt_min <;> dsimp only [radius]
        · linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
        · linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      exact ⟨neg_lt_zero.mpr radius_pos, radius_pos⟩
    · intro t t_mem
      refine ⟨phases_deriv m t ?_, Set.mem_univ _⟩
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) t_mem.1,
        t_mem.2.trans_le (min_le_left _ _)⟩
    · intro t t_mem
      refine ⟨phases_deriv n t ?_, Set.mem_univ _⟩
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) t_mem.1,
        t_mem.2.trans_le (min_le_right _ _)⟩
    · rw [phases_zero m, phases_zero n]
  let index := fun t : ℝ ↦ ⌈|t|⌉₊ + 1
  have index_mem (t : ℝ) : t ∈ Set.Ioo (-(radius (index t))) (radius (index t)) := by
    rw [Set.mem_Ioo, ← abs_lt]
    dsimp only [radius, index]
    push_cast
    have := Nat.le_ceil |t|
    linarith
  let phase := fun t ↦ phases (index t) t
  have phase_eq (n : ℕ) {t : ℝ}
      (t_mem : t ∈ Set.Ioo (-(radius n)) (radius n)) :
      phase t = phases n t := by
    apply consistency (index t) n
    constructor
    · rcases le_total (radius (index t)) (radius n) with radius_le | radius_le
      · rw [min_eq_left radius_le]
        exact (index_mem t).1
      · rw [min_eq_right radius_le]
        exact t_mem.1
    · exact lt_min (index_mem t).2 t_mem.2
  refine ⟨phase, ?_, ?_⟩
  · rw [phase_eq 0 (by simp [radius]), phases_zero]
  · intro t
    let n := index t
    have t_mem : t ∈ Set.Ioo (-(radius n)) (radius n) := index_mem t
    have phase_eventually_eq : phase =ᶠ[𝓝 t] phases n := by
      filter_upwards [Ioo_mem_nhds t_mem.1 t_mem.2] with s s_mem
      exact phase_eq n s_mem
    have derivative := (phases_deriv n t t_mem).congr_of_eventuallyEq phase_eventually_eq
    rw [phase_eq n t_mem]
    exact derivative

noncomputable def phase (params : Params) : ℝ → ℝ × ℝ :=
  Classical.choose (phase_exists params)

lemma phase_zero (params : Params) :
    phase params 0 = (params.θ0.toReal, params.ω0) :=
  (Classical.choose_spec (phase_exists params)).1

lemma phase_hasDerivAt (params : Params) (t : ℝ) :
    HasDerivAt (phase params) (phaseField params (phase params t)) t :=
  (Classical.choose_spec (phase_exists params)).2 t

def angle (params : Params) (t : ℝ) : ℝ :=
  (phase params t).1

def angularVelocity (params : Params) (t : ℝ) : ℝ :=
  (phase params t).2

lemma angle_hasDerivAt (params : Params) (t : ℝ) :
    HasDerivAt (angle params) (angularVelocity params t) t := by
  convert (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (phase_hasDerivAt params t) using 1 <;> rfl

lemma angularVelocity_hasDerivAt (params : Params) (t : ℝ) :
    HasDerivAt (angularVelocity params)
      (-params.g / params.L * Real.sin (angle params t)) t := by
  convert (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (phase_hasDerivAt params t) using 1 <;> rfl

def vectorCLM (frame : ReferenceFrame 2) [Fact frame.IsMetricConserved] :
    (Fin 2 → ℝ) →L[ℝ] frame.Vector := by
  exact LinearMap.toContinuousLinearMap
    { toFun := ReferenceFrame.Vector.mk
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

lemma vector_eq_of_components {frame : ReferenceFrame 2}
    {x y : frame.Vector} (components_eq : ∀ i, x.components i = y.components i) :
    x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  congr
  funext i
  exact components_eq i

@[simp]
lemma components_add {frame : ReferenceFrame 2}
    (x y : frame.Vector) (i : Fin 2) :
    (x + y).components i = x.components i + y.components i :=
  rfl

@[simp]
lemma components_smul {frame : ReferenceFrame 2}
    (c : ℝ) (x : frame.Vector) (i : Fin 2) :
    (c • x).components i = c * x.components i :=
  rfl

@[simp]
lemma components_neg {frame : ReferenceFrame 2}
    (x : frame.Vector) (i : Fin 2) :
    (-x).components i = -x.components i :=
  rfl

@[simp]
lemma components_sub {frame : ReferenceFrame 2}
    (x y : frame.Vector) (i : Fin 2) :
    (x - y).components i = x.components i - y.components i :=
  rfl

@[simp]
lemma components_positive_smul {frame : ReferenceFrame 2}
    (c : ℝ+) (x : frame.Vector) (i : Fin 2) :
    (c • x).components i = c.val * x.components i :=
  rfl

@[simp]
lemma components_zero {frame : ReferenceFrame 2} (i : Fin 2) :
    (0 : frame.Vector).components i = 0 :=
  rfl

def bobPosition (params : Params) (t : ℝ) : paramsFrame.Vector :=
  .mk ![params.L * Real.sin (angle params t),
    -params.L * Real.cos (angle params t)]

def bobVelocity (params : Params) (t : ℝ) : paramsFrame.Vector :=
  .mk ![params.L * angularVelocity params t * Real.cos (angle params t),
    params.L * angularVelocity params t * Real.sin (angle params t)]

def bobAcceleration (params : Params) (t : ℝ) : paramsFrame.Vector :=
  let φ := angle params t
  let ω := angularVelocity params t
  let α := -params.g / params.L * Real.sin φ
  .mk ![params.L * (α * Real.cos φ - ω ^ 2 * Real.sin φ),
    params.L * (α * Real.sin φ + ω ^ 2 * Real.cos φ)]

lemma bobPosition_hasDerivAt (params : Params) (t : ℝ) :
    HasDerivAt (bobPosition params) (bobVelocity params t) t := by
  have components_deriv : HasDerivAt
      (fun s ↦ ![params.L * Real.sin (angle params s),
        -params.L * Real.cos (angle params s)])
      ![params.L * angularVelocity params t * Real.cos (angle params t),
        params.L * angularVelocity params t * Real.sin (angle params t)] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · change HasDerivAt (fun s ↦ params.L * Real.sin (angle params s))
        (params.L * angularVelocity params t * Real.cos (angle params t)) t
      exact (HasDerivAt.const_mul params.L.val (angle_hasDerivAt params t).sin).congr_deriv
        (by ring)
    · change HasDerivAt (fun s ↦ -params.L * Real.cos (angle params s))
        (params.L * angularVelocity params t * Real.sin (angle params t)) t
      exact (HasDerivAt.const_mul (-params.L.val) (angle_hasDerivAt params t).cos).congr_deriv
        (by ring)
  convert (vectorCLM paramsFrame).hasFDerivAt.comp_hasDerivAt t components_deriv using 1 <;>
    rfl

lemma bobVelocity_hasDerivAt (params : Params) (t : ℝ) :
    HasDerivAt (bobVelocity params) (bobAcceleration params t) t := by
  let φ := angle params t
  let ω := angularVelocity params t
  let α := -params.g / params.L * Real.sin φ
  have components_deriv : HasDerivAt
      (fun s ↦ ![params.L * angularVelocity params s * Real.cos (angle params s),
        params.L * angularVelocity params s * Real.sin (angle params s)])
      ![params.L * (α * Real.cos φ - ω ^ 2 * Real.sin φ),
        params.L * (α * Real.sin φ + ω ^ 2 * Real.cos φ)] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · change HasDerivAt
        (fun s ↦ params.L * angularVelocity params s * Real.cos (angle params s))
        (params.L * (α * Real.cos φ - ω ^ 2 * Real.sin φ)) t
      convert HasDerivAt.const_mul params.L.val ((angularVelocity_hasDerivAt params t).mul
        (angle_hasDerivAt params t).cos) using 1 <;> try rfl
      all_goals first | (funext s; rw [Pi.mul_apply]; ring) |
        (dsimp only [φ, ω, α]; ring)
    · change HasDerivAt
        (fun s ↦ params.L * angularVelocity params s * Real.sin (angle params s))
        (params.L * (α * Real.sin φ + ω ^ 2 * Real.cos φ)) t
      convert HasDerivAt.const_mul params.L.val ((angularVelocity_hasDerivAt params t).mul
        (angle_hasDerivAt params t).sin) using 1 <;> try rfl
      all_goals first | (funext s; rw [Pi.mul_apply]; ring) |
        (dsimp only [φ, ω, α]; ring)
  convert (vectorCLM paramsFrame).hasFDerivAt.comp_hasDerivAt t components_deriv using 1 <;>
    rfl

lemma bobPosition_deriv (params : Params) :
    deriv (bobPosition params) = bobVelocity params := by
  funext t
  exact (bobPosition_hasDerivAt params t).deriv

lemma bobPosition_twice_differentiable (params : Params) :
    Differentiable ℝ (bobPosition params) ∧
      Differentiable ℝ (deriv (bobPosition params)) := by
  refine ⟨fun t ↦ (bobPosition_hasDerivAt params t).differentiableAt, ?_⟩
  rw [bobPosition_deriv]
  exact fun t ↦ (bobVelocity_hasDerivAt params t).differentiableAt

lemma bobAcceleration_eq (params : Params) :
    deriv (bobVelocity params) = bobAcceleration params := by
  funext t
  exact (bobVelocity_hasDerivAt params t).deriv

lemma time_deriv_bobPosition (params : Params) :
    Time.deriv (fun t : Time ↦ bobPosition params t.val) =
      fun t ↦ bobVelocity params t.val := by
  funext t
  rw [Time.deriv_eq]
  have derivative := (bobPosition_hasDerivAt params t.val).hasFDerivAt.comp t
    Time.toRealCLM.hasFDerivAt
  change (fderiv ℝ (bobPosition params ∘ Time.val) t) 1 = _
  rw [derivative.fderiv]
  simp [Time.toRealCLM]

lemma time_deriv_bobVelocity (params : Params) :
    Time.deriv (fun t : Time ↦ bobVelocity params t.val) =
      fun t ↦ bobAcceleration params t.val := by
  funext t
  rw [Time.deriv_eq]
  have derivative := (bobVelocity_hasDerivAt params t.val).hasFDerivAt.comp t
    Time.toRealCLM.hasFDerivAt
  change (fderiv ℝ (bobVelocity params ∘ Time.val) t) 1 = _
  rw [derivative.fderiv]
  simp [Time.toRealCLM]

def paramsPivot (params : Params) : paramsFrame.Particle where
  mass := params.pivotMass
  pos := 0
  pos_twice_differentiable := by
    intro
    constructor
    · fun_prop
    · have derivative_zero : Time.deriv (0 : Time → paramsFrame.Vector) = 0 := by
        funext t
        exact Time.deriv_const (t := t) 0
      rw [derivative_zero]
      fun_prop

def paramsBob (params : Params) : paramsFrame.Particle where
  mass := params.bobMass
  pos := fun t ↦ bobPosition params t.val
  pos_twice_differentiable := by
    intro
    constructor
    · exact (bobPosition_twice_differentiable params).1.fun_comp Time.val_differentiable
    · rw [time_deriv_bobPosition]
      have velocity_differentiable : Differentiable ℝ (bobVelocity params) :=
        fun t ↦ (bobVelocity_hasDerivAt params t).differentiableAt
      exact velocity_differentiable.fun_comp Time.val_differentiable

lemma paramsPivot_pos_ne_paramsBob_pos (params : Params) :
    (paramsPivot params).pos ≠ (paramsBob params).pos := by
  intro positions_eq
  have position_zero := congrFun positions_eq 0
  have x_eq := congrArg (fun v ↦ v.components 0) position_zero
  have y_eq := congrArg (fun v ↦ v.components 1) position_zero
  have L_ne_zero := ne_of_gt params.L.property
  simp only [paramsPivot, Pi.zero_apply, paramsBob, bobPosition, Matrix.cons_val_zero,
    components_zero, Time.zero_val] at x_eq
  simp only [paramsPivot, Pi.zero_apply, paramsBob, bobPosition, Matrix.cons_val_one,
    components_zero, Time.zero_val] at y_eq
  change 0 = params.L * Real.sin (angle params 0) at x_eq
  change 0 = -params.L * Real.cos (angle params 0) at y_eq
  have sin_eq_zero : Real.sin (angle params 0) = 0 := by
    apply mul_left_cancel₀ L_ne_zero
    simpa using x_eq
  have cos_eq_zero : Real.cos (angle params 0) = 0 := by
    apply mul_left_cancel₀ L_ne_zero
    linarith
  nlinarith [Real.sin_sq_add_cos_sq (angle params 0)]

lemma paramsPivot_ne_paramsBob (params : Params) :
    paramsPivot params ≠ paramsBob params := by
  intro particles_eq
  exact paramsPivot_pos_ne_paramsBob_pos params
    (congrArg ReferenceFrame.Particle.pos particles_eq)

def paramsParticles (params : Params) : Multiset paramsFrame.Particle :=
  {paramsPivot params, paramsBob params}

def paramsPivotParticle (params : Params) : paramsParticles params :=
  ⟨paramsPivot params, ⟨0, Multiset.count_pos.mpr (by simp [paramsParticles])⟩⟩

def paramsBobParticle (params : Params) : paramsParticles params :=
  ⟨paramsBob params, ⟨0, Multiset.count_pos.mpr (by simp [paramsParticles])⟩⟩

lemma paramsPivotParticle_ne_paramsBobParticle (params : Params) :
    paramsPivotParticle params ≠ paramsBobParticle params := by
  intro particles_eq
  exact paramsPivot_ne_paramsBob params (congrArg Sigma.fst particles_eq)

def paramsGravity (params : Params) (particle : paramsParticles params) :
    paramsFrame.Force (paramsParticles params) where
  value _ := .mk ![0, -particle.1.mass * params.g]
  target := particle

def paramsTension (params : Params) : paramsFrame.InternalForce (paramsParticles params) where
  value t := (-params.bobMass.val *
    (angularVelocity params t.val ^ 2 + params.g / params.L * Real.cos (angle params t.val))) •
      bobPosition params t.val
  target := paramsBobParticle params
  source := paramsPivotParticle params
  source_ne_target := paramsPivotParticle_ne_paramsBobParticle params

def paramsSupportForce (params : Params) : paramsFrame.Force (paramsParticles params) where
  value t := paramsTension params t - paramsGravity params (paramsPivotParticle params) t
  target := paramsPivotParticle params

lemma paramsBob_acc (params : Params) :
    (paramsBob params).acc = fun t ↦ bobAcceleration params t.val := by
  rw [ReferenceFrame.Particle.acc, ReferenceFrame.Particle.vel, paramsBob,
    time_deriv_bobPosition, time_deriv_bobVelocity]

lemma paramsPivot_acc (params : Params) :
    (paramsPivot params).acc = 0 := by
  rw [ReferenceFrame.Particle.acc, ReferenceFrame.Particle.vel, paramsPivot]
  have derivative_zero : Time.deriv (0 : Time → paramsFrame.Vector) = 0 := by
    funext t
    exact Time.deriv_const (t := t) 0
  rw [derivative_zero]
  funext t
  exact Time.deriv_const (t := t) 0

lemma paramsTension_central (params : Params) :
    ∀ t, ∃ c : ℝ, paramsTension params t = c •
      ((paramsTension params).target.1.pos t - (paramsTension params).source.1.pos t) := by
  intro t
  refine ⟨-params.bobMass.val *
    (angularVelocity params t.val ^ 2 + params.g / params.L * Real.cos (angle params t.val)), ?_⟩
  simp [paramsTension, paramsPivotParticle, paramsPivot, paramsBobParticle, paramsBob]

lemma paramsBob_newton_second_law (params : Params) (t : Time) :
    paramsTension params t + paramsGravity params (paramsBobParticle params) t =
      params.bobMass • bobAcceleration params t.val := by
  apply vector_eq_of_components
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) j) i
  · change (-params.bobMass.val * (angularVelocity params t ^ 2 +
        params.g.val / params.L.val * Real.cos (angle params t.val))) *
      (params.L.val * Real.sin (angle params t.val)) + 0 =
        params.bobMass.val * (params.L.val *
          ((-params.g.val / params.L.val * Real.sin (angle params t.val)) *
            Real.cos (angle params t.val) - angularVelocity params t.val ^ 2 *
              Real.sin (angle params t.val)))
    field_simp [ne_of_gt params.L.property]
    ring
  · simp [paramsTension, paramsGravity, paramsBobParticle, paramsBob, bobPosition,
      bobAcceleration]
    field_simp [ne_of_gt params.L.property]
    linear_combination params.bobMass.val * params.g.val *
      Real.sin_sq_add_cos_sq (angle params t.val)

lemma paramsPivot_newton_second_law (params : Params) (t : Time) :
    (paramsTension params).reverse t + paramsGravity params (paramsPivotParticle params) t +
        paramsSupportForce params t = 0 := by
  change -(paramsTension params t) + paramsGravity params (paramsPivotParticle params) t +
      (paramsTension params t - paramsGravity params (paramsPivotParticle params) t) = 0
  abel

lemma filtered_subtype_sum_eq_multiset_sum
    {α β : Type*} [AddCommMonoid β]
    (elements : Multiset α) (predicate : α → Prop) [DecidablePred predicate]
    (value : α → β) :
    (∑ element : elements with predicate element.1, value element.1) =
      ((elements.filter predicate).map value).sum := by
  rw [Finset.sum_filter]
  have sum_map (f : α → β) :
      (∑ element : elements, f element) = (elements.map f).sum := by
    rw [Multiset.sum_eq_sum_coe]
    apply Fintype.sum_equiv (elements.mapEquiv f)
    intro element
    rw [Multiset.mapEquiv_apply]
  calc
    _ = (elements.map fun element ↦ if predicate element then value element else 0).sum :=
      sum_map _
    _ = _ := by
      clear sum_map
      induction elements using Multiset.induction_on with
      | empty => simp
      | cons element elements inductionHypothesis =>
          by_cases satisfies : predicate element <;>
            simp [satisfies, inductionHypothesis]

lemma internalForce_reverse_reverse {frame : ReferenceFrame 2}
    {Object : Type} (force : frame.InternalForce Object) : force.reverse.reverse = force := by
  rcases force with ⟨⟨value, target⟩, source, source_ne_target⟩
  simp [ReferenceFrame.InternalForce.reverse]

lemma netForce_eq_multiset_sum
    {frame : ReferenceFrame 2}
    {particles : Multiset frame.Particle}
    (particle : particles)
    (internalForces : Multiset (frame.InternalForce particles))
    (externalForces : Multiset (frame.Force particles)) (t : Time) :
    ReferenceFrame.netForce particle internalForces externalForces t =
      ((((internalForces.map ReferenceFrame.InternalForce.toForce + externalForces).filter
        fun force ↦ force.target = particle).map fun force ↦ force t).sum) := by
  exact filtered_subtype_sum_eq_multiset_sum
    (predicate := fun force : frame.Force particles ↦ force.target = particle)
    (value := fun force ↦ force t) _

lemma paramsBob_netForce (params : Params) (t : Time) :
    ReferenceFrame.netForce (paramsBobParticle params)
      {paramsTension params, (paramsTension params).reverse}
      {paramsGravity params (paramsBobParticle params),
        paramsGravity params (paramsPivotParticle params),
        paramsSupportForce params} t =
      paramsTension params t + paramsGravity params (paramsBobParticle params) t := by
  rw [netForce_eq_multiset_sum]
  simp [Multiset.filter_singleton, paramsTension, paramsGravity, paramsSupportForce,
    ReferenceFrame.InternalForce.reverse, paramsPivotParticle_ne_paramsBobParticle]
  abel

lemma paramsPivot_netForce (params : Params) (t : Time) :
    ReferenceFrame.netForce (paramsPivotParticle params)
      {paramsTension params, (paramsTension params).reverse}
      {paramsGravity params (paramsBobParticle params),
        paramsGravity params (paramsPivotParticle params),
        paramsSupportForce params} t =
      (paramsTension params).reverse t +
        paramsGravity params (paramsPivotParticle params) t +
        paramsSupportForce params t := by
  rw [netForce_eq_multiset_sum]
  simp [Multiset.filter_singleton, paramsTension, paramsGravity, paramsSupportForce,
    ReferenceFrame.InternalForce.reverse,
    (paramsPivotParticle_ne_paramsBobParticle params).symm]
  abel

lemma paramsParticle_eq_pivot_or_bob (params : Params) (particle : paramsParticles params) :
    particle = paramsPivotParticle params ∨ particle = paramsBobParticle params := by
  rcases particle with ⟨particle, index⟩
  have particle_mem : particle ∈ paramsParticles params :=
    Multiset.count_pos.mp (Nat.zero_lt_of_lt index.isLt)
  simp [paramsParticles] at particle_mem
  rcases particle_mem with particle_eq | particle_eq
  · subst particle
    left
    congr 1
    apply Fin.ext
    have index_lt := index.isLt
    simp [paramsParticles, paramsPivot_ne_paramsBob] at index_lt
    omega
  · subst particle
    right
    congr 1
    apply Fin.ext
    have index_lt := index.isLt
    simp [paramsParticles, paramsPivot_ne_paramsBob] at index_lt
    omega

def paramsSystem (params : Params) : PointParticle.System 2 where
  frame := paramsFrame
  particles := paramsParticles params
  internalForces := {paramsTension params, (paramsTension params).reverse}
  externalForces := {paramsGravity params (paramsBobParticle params),
    paramsGravity params (paramsPivotParticle params), paramsSupportForce params}
  newton_second_law := by
    intro particle
    funext t
    rcases paramsParticle_eq_pivot_or_bob params particle with rfl | rfl
    · rw [paramsPivot_netForce, paramsPivot_newton_second_law]
      change (0 : paramsFrame.Vector) =
        params.pivotMass.val • (paramsPivot params).acc t
      rw [paramsPivot_acc]
      change (0 : paramsFrame.Vector) = params.pivotMass.val • (0 : paramsFrame.Vector)
      simp
    · rw [paramsBob_netForce, paramsBob_newton_second_law]
      change params.bobMass.val • bobAcceleration params t.val =
        params.bobMass.val • (paramsBob params).acc t
      rw [paramsBob_acc]
  newton_third_law := by
    change (paramsTension params).reverse ::ₘ {(paramsTension params).reverse.reverse} =
      {paramsTension params, (paramsTension params).reverse}
    rw [internalForce_reverse_reverse]
    exact Multiset.cons_swap _ _ _

def paramsTensionOccurrence (params : Params) : (paramsSystem params).InternalForce :=
  ⟨paramsTension params,
    ⟨0, by
      change 0 < Multiset.count (paramsTension params)
        {paramsTension params, (paramsTension params).reverse}
      simp⟩⟩

def paramsSupportForceOccurrence (params : Params) : (paramsSystem params).Force :=
  Sum.inr ⟨paramsSupportForce params,
    ⟨0, by
      change 0 < Multiset.count (paramsSupportForce params)
        {paramsGravity params (paramsBobParticle params),
          paramsGravity params (paramsPivotParticle params), paramsSupportForce params}
      apply Multiset.count_pos.mpr
      simp⟩⟩

lemma angle_chart_symm (θ : Real.Angle) :
    ⇑(chartAt ℝ θ).symm = ((↑) : ℝ → Real.Angle) := by
  change ⇑(isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd.isCoveringMap.isLocalHomeomorph.localInverseAt _).symm = _
  rw [IsLocalHomeomorph.localInverseAt_symm]
  rfl

lemma hasMFDerivAt_angle_coe
    {φ : ℝ → ℝ} {φ' t : ℝ}
    (φ_has_deriv : HasDerivAt φ φ' t)
    (φ_eq_chart : φ t = chartAt ℝ (φ t : Real.Angle) (φ t : Real.Angle)) :
    HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun s ↦ (φ s : Real.Angle)) t
      (ContinuousLinearMap.toSpanSingleton ℝ φ') := by
  let θ : Real.Angle := φ t
  let chart := chartAt ℝ θ
  have φ_mem_chart_target : φ t ∈ chart.target := by
    rw [φ_eq_chart]
    exact mem_chart_target ℝ θ
  have φ_eventually_mem_chart_target : ∀ᶠ s in 𝓝 t, φ s ∈ chart.target :=
    φ_has_deriv.continuousAt (chart.open_target.mem_nhds φ_mem_chart_target)
  refine ⟨Real.Angle.continuous_coe.continuousAt.comp φ_has_deriv.continuousAt, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq
    φ_has_deriv.hasFDerivAt.hasFDerivWithinAt
  · filter_upwards [φ_eventually_mem_chart_target.filter_mono inf_le_left] with s s_mem
    change chart (φ s : Real.Angle) = φ s
    rw [← angle_chart_symm θ]
    exact chart.right_inv s_mem
  · change chart (φ t : Real.Angle) = φ t
    exact φ_eq_chart.symm

lemma hasMFDerivAt_angle_arg
    {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (z_has_deriv : HasDerivAt z z' t)
    (z_ne_zero : ∀ s, z s ≠ 0) :
    HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun s ↦ (Complex.arg (z s) : Real.Angle)) t
      (ContinuousLinearMap.toSpanSingleton ℝ (z' / z t).im) := by
  let θ : Real.Angle := Complex.arg (z t)
  let q := chartAt ℝ θ θ
  let φ := fun s ↦ q + (Complex.log (z s / z t)).im
  have q_coe : (q : Real.Angle) = θ := by
    rw [← angle_chart_symm θ]
    exact (chartAt ℝ θ).left_inv (mem_chart_source ℝ θ)
  have log_has_deriv :
      HasDerivAt (fun s ↦ Complex.log (z s / z t)) (z' / z t) t := by
    convert (z_has_deriv.div_const (z t)).clog_real (by simp [z_ne_zero t]) using 1
    all_goals simp [z_ne_zero t]
  have log_im_has_deriv :
      HasDerivAt (fun s ↦ (Complex.log (z s / z t)).im) (z' / z t).im t := by
    convert Complex.imCLM.hasFDerivAt.comp_hasDerivAt t log_has_deriv using 1 <;>
      rfl
  have φ_has_deriv : HasDerivAt φ (z' / z t).im t := by
    simpa only [φ] using log_im_has_deriv.const_add q
  have φ_at : φ t = q := by simp [φ, z_ne_zero t]
  have coe_φ : (fun s ↦ (φ s : Real.Angle)) =
      fun s ↦ (Complex.arg (z s) : Real.Angle) := by
    funext s
    change ((q + (Complex.log (z s / z t)).im : ℝ) : Real.Angle) = _
    rw [Real.Angle.coe_add, q_coe, Complex.log_im,
      Complex.arg_div_coe_angle (z_ne_zero s) (z_ne_zero t)]
    simp only [θ]
    abel
  have coe_φ_has_mfderiv := hasMFDerivAt_angle_coe φ_has_deriv (by
    rw [φ_at]
    rw [q_coe])
  rw [coe_φ] at coe_φ_has_mfderiv
  exact coe_φ_has_mfderiv

lemma mfderiv_angle_arg
    {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (z_has_deriv : HasDerivAt z z' t)
    (z_ne_zero : ∀ s, z s ≠ 0) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s ↦ (Complex.arg (z s) : Real.Angle)) t (1 : ℝ) =
      (z' / z t).im := by
  have mfderiv_eq := (hasMFDerivAt_angle_arg z_has_deriv z_ne_zero).mfderiv
  calc
    _ = (ContinuousLinearMap.toSpanSingleton ℝ (z' / z t).im) (1 : ℝ) :=
      congrArg (fun f ↦ f (1 : ℝ)) mfderiv_eq
    _ = _ := by simp

def paramsPendulum (params : Params) : Pendulum where
  toSystem := paramsSystem params
  orthonormal := paramsFrame_orthonormal
  pivot := paramsPivotParticle params
  pivot_at_origin := rfl
  L := params.L
  bob := paramsBobParticle params
  length_constant := by
    intro t
    change ‖bobPosition params t.val‖ = params.L.val
    rw [vector_norm_l2_if_orthonormal paramsFrame_orthonormal]
    simp only [bobPosition, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have trig := Real.sin_sq_add_cos_sq (angle params t.val)
    have L_pos := params.L.property
    rw [show (params.L.val * Real.sin (angle params t.val)) ^ 2 +
        (-params.L.val * Real.cos (angle params t.val)) ^ 2 = params.L.val ^ 2 by
      nlinarith]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos L_pos]
  no_other_particles := by
    ext particle
    simp only [Set.mem_univ, true_iff]
    exact paramsParticle_eq_pivot_or_bob params particle
  tension := paramsTensionOccurrence params
  tension_targets_bob := rfl
  tension_central := paramsTension_central params
  no_other_internal_forces := rfl
  pivotSupportForce := paramsSupportForceOccurrence params
  support_targets_pivot := rfl
  g := params.g
  no_other_external_forces := by
    simp only [paramsSystem, paramsGravity, gravity, PointParticle.System.Particle.mass,
      paramsSupportForceOccurrence]
    rfl

lemma paramsPendulum_θ (params : Params) (t : ℝ) :
    (paramsPendulum params).θ t = (angle params t : Real.Angle) := by
  let z : ℂ := ⟨-(-params.L * Real.cos (angle params t)),
    params.L * Real.sin (angle params t)⟩
  have z_eq : z = params.L.val *
      (Real.Angle.cos (angle params t : Real.Angle) +
        Real.Angle.sin (angle params t : Real.Angle) * Complex.I) := by
    apply Complex.ext
    · simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.add_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Real.Angle.cos_coe,
        Real.Angle.sin_coe]
      ring
    · simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.add_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Real.Angle.cos_coe,
        Real.Angle.sin_coe]
      ring
  simp only [Pendulum.θ, paramsPendulum, PointParticle.System.Particle.pos]
  change (Complex.arg z : Real.Angle) = (angle params t : Real.Angle)
  rw [z_eq]
  exact Complex.arg_mul_cos_add_sin_mul_I_coe_angle params.L.property _

set_option backward.isDefEq.respectTransparency false in
lemma paramsPendulum_ω (params : Params) (t : ℝ) :
    (paramsPendulum params).ω t = angularVelocity params t := by
  let z := fun s ↦ Complex.equivRealProdCLM.symm
    (params.L * Real.cos (angle params s), params.L * Real.sin (angle params s))
  let z' := Complex.equivRealProdCLM.symm
    (-params.L * angularVelocity params t * Real.sin (angle params t),
      params.L * angularVelocity params t * Real.cos (angle params t))
  have re_has_deriv : HasDerivAt
      (fun s ↦ params.L * Real.cos (angle params s))
      (-params.L * angularVelocity params t * Real.sin (angle params t)) t := by
    exact (HasDerivAt.const_mul params.L.val (angle_hasDerivAt params t).cos).congr_deriv
      (by ring)
  have im_has_deriv : HasDerivAt
      (fun s ↦ params.L * Real.sin (angle params s))
      (params.L * angularVelocity params t * Real.cos (angle params t)) t := by
    exact (HasDerivAt.const_mul params.L.val (angle_hasDerivAt params t).sin).congr_deriv
      (by ring)
  have z_has_deriv : HasDerivAt z z' t := by
    convert Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      (re_has_deriv.prodMk im_has_deriv) using 1 <;> rfl
  have z_apply (s : ℝ) : z s =
      ⟨params.L * Real.cos (angle params s),
        params.L * Real.sin (angle params s)⟩ := by
    apply Complex.ext <;> rfl
  have z'_apply : z' =
      ⟨-params.L * angularVelocity params t * Real.sin (angle params t),
        params.L * angularVelocity params t * Real.cos (angle params t)⟩ := by
    apply Complex.ext <;> rfl
  have z_ne_zero : ∀ s, z s ≠ 0 := by
    intro s z_eq_zero
    have re_eq := congrArg Complex.re z_eq_zero
    have im_eq := congrArg Complex.im z_eq_zero
    change params.L * Real.cos (angle params s) = 0 at re_eq
    change params.L * Real.sin (angle params s) = 0 at im_eq
    have L_ne_zero := ne_of_gt params.L.property
    have cos_eq_zero : Real.cos (angle params s) = 0 := by
      apply mul_left_cancel₀ L_ne_zero
      simpa using re_eq
    have sin_eq_zero : Real.sin (angle params s) = 0 := by
      apply mul_left_cancel₀ L_ne_zero
      simpa using im_eq
    nlinarith [Real.sin_sq_add_cos_sq (angle params s)]
  have theta_eq : (paramsPendulum params).θ =
      fun s : Time ↦ (Complex.arg (z s.val) : Real.Angle) := by
    funext s
    simp only [Pendulum.θ, paramsPendulum, PointParticle.System.Particle.pos]
    change (Complex.arg ⟨-(-params.L * Real.cos (angle params s.val)),
      params.L * Real.sin (angle params s.val)⟩ : Real.Angle) =
        (Complex.arg (z s.val) : Real.Angle)
    have complex_eq : (⟨-(-params.L * Real.cos (angle params s.val)),
        params.L * Real.sin (angle params s.val)⟩ : ℂ) = z s.val := by
      rw [z_apply]
      apply Complex.ext <;> simp
    rw [complex_eq]
  rw [Pendulum.ω, theta_eq, Time.manifoldDeriv_eq]
  have real_derivative := hasMFDerivAt_angle_arg z_has_deriv z_ne_zero
  have time_derivative : HasMFDerivAt 𝓘(ℝ, Time) 𝓘(ℝ)
      (fun s : Time ↦ (Complex.arg (z s.val) : Real.Angle)) (t : Time)
      ((ContinuousLinearMap.toSpanSingleton ℝ (z' / z t).im).comp Time.toRealCLM) := by
    convert real_derivative.comp (t : Time)
      Time.toRealCLM.hasFDerivAt.hasMFDerivAt using 1
    all_goals rfl
  have mfderiv_eq := time_derivative.mfderiv
  rw [mfderiv_eq]
  have comp_apply_eq :
      ((ContinuousLinearMap.toSpanSingleton ℝ (z' / z t).im).comp Time.toRealCLM)
          (1 : Time) = (z' / z t).im := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    have one_eq : Time.toRealCLM (1 : Time) = (1 : ℝ) := by
      change (1 : Time).val = (1 : ℝ)
      rw [Time.one_val]
    rw [one_eq, one_smul]
  refine comp_apply_eq.trans ?_
  rw [z'_apply, z_apply t, Complex.div_im, Complex.normSq_apply]
  dsimp
  field_simp [ne_of_gt params.L.property,
    show Real.cos (angle params t) ^ 2 + Real.sin (angle params t) ^ 2 ≠ 0 by
      nlinarith [Real.sin_sq_add_cos_sq (angle params t)]]
  nlinarith [Real.sin_sq_add_cos_sq (angle params t)]

lemma params_eq_of_fields (a b : Params)
    (pivotMass_eq : a.pivotMass = b.pivotMass)
    (bobMass_eq : a.bobMass = b.bobMass)
    (L_eq : a.L = b.L)
    (g_eq : a.g = b.g)
    (θ0_eq : a.θ0 = b.θ0)
    (ω0_eq : a.ω0 = b.ω0) :
    a = b := by
  cases a
  cases b
  simp_all

lemma params_paramsPendulum (params : Params) :
    (paramsPendulum params).params = params := by
  apply params_eq_of_fields
  · simp [Pendulum.params, paramsPendulum, PointParticle.System.Particle.mass,
      paramsPivotParticle, paramsPivot]
  · simp [Pendulum.params, paramsPendulum, PointParticle.System.Particle.mass,
      paramsBobParticle, paramsBob]
  · simp [Pendulum.params, paramsPendulum]
  · simp [Pendulum.params, paramsPendulum]
  · change (paramsPendulum params).θ 0 = params.θ0
    rw [paramsPendulum_θ]
    have angle_zero := congrArg Prod.fst (phase_zero params)
    change angle params 0 = params.θ0.toReal at angle_zero
    rw [Time.zero_val, angle_zero, Real.Angle.coe_toReal]
  · change (paramsPendulum params).ω 0 = params.ω0
    rw [paramsPendulum_ω]
    rw [Time.zero_val]
    change (phase params 0).2 = params.ω0
    exact congrArg Prod.snd (phase_zero params)

lemma params_surjective : Function.Surjective Pendulum.params :=
  fun params ↦ ⟨paramsPendulum params, params_paramsPendulum params⟩

/-- Internal version of the public `make` definition, with the same defining expression. -/
noncomputable def make (params : Params) : Pendulum :=
  Classical.choose (params_surjective params)

lemma make_params (params : Params) : (make params).params = params :=
  Classical.choose_spec (params_surjective params)

def componentCLM {system : PointParticle.System 2} (i : Fin 2) :
    system.frame.Vector →L[ℝ] ℝ := by
  exact LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ v.components i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

@[simp]
lemma componentCLM_apply {system : PointParticle.System 2}
    (i : Fin 2) (v : system.frame.Vector) :
    componentCLM i v = v.components i :=
  rfl

lemma toRealCLE_symm_one : Time.toRealCLE.symm (1 : ℝ) = (1 : Time) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  change (1 : ℝ) = (1 : Time).val
  rw [Time.one_val]

lemma hasDerivAt_comp_toRealCLE_symm {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Time → E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (Time.toRealCLE.symm t)) :
    HasDerivAt (fun s : ℝ ↦ f (Time.toRealCLE.symm s))
      (Time.deriv (M := E) f (Time.toRealCLE.symm t)) t := by
  simpa [Function.comp_def, Time.deriv_eq, toRealCLE_symm_one] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq t
      ((Time.toRealCLE.symm : ℝ →L[ℝ] Time).hasDerivAt) rfl

lemma time_deriv_comp_val {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {t : Time} (hf : HasDerivAt f f' t.val) :
    Time.deriv (M := E) (fun s : Time ↦ f s.val) t = f' := by
  rw [Time.deriv_eq]
  have derivative := hf.hasFDerivAt.comp t Time.toRealCLM.hasFDerivAt
  change (fderiv ℝ (f ∘ Time.val) t) 1 = _
  rw [derivative.fderiv]
  simp [Time.toRealCLM]

lemma multiset_sum_eq_fintype_sum
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Multiset α) (f : α → M) :
    (s.map f).sum = ∑ x : s, f x.1 := by
  change (s.map f).sum =
    (((Finset.univ : Finset s).val.map fun x : s ↦ f x.1).sum)
  rw [Multiset.map_univ]

set_option backward.isDefEq.respectTransparency false in
lemma angular_velocity_eq (self : Pendulum) (t : Time) :
    self.ω t =
      ((self.bob.pos t).components 0 * (self.bob.vel t).components 1 -
        (self.bob.pos t).components 1 * (self.bob.vel t).components 0) / self.L ^ 2 := by
  let τ := Time.toRealCLE t
  let x := fun s : ℝ ↦ (self.bob.1.pos (Time.toRealCLE.symm s)).components 0
  let y := fun s : ℝ ↦ (self.bob.1.pos (Time.toRealCLE.symm s)).components 1
  let vx := (self.bob.1.vel t).components 0
  let vy := (self.bob.1.vel t).components 1
  let z := fun s ↦ Complex.equivRealProdCLM.symm (-y s, x s)
  let z' := Complex.equivRealProdCLM.symm (-vy, vx)
  have pos_has_deriv : HasDerivAt
      (fun s : ℝ ↦ self.bob.1.pos (Time.toRealCLE.symm s)) (self.bob.1.vel t) τ := by
    simpa only [τ, ContinuousLinearEquiv.symm_apply_apply,
      ReferenceFrame.Particle.vel] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.pos τ
        ((self.bob.1.pos_twice_differentiable self.isInertial.out).1.differentiableAt)
  have x_has_deriv : HasDerivAt x vx τ := by
    convert (componentCLM (system := self.toSystem) 0).hasFDerivAt.comp_hasDerivAt τ
      pos_has_deriv using 1 <;> rfl
  have y_has_deriv : HasDerivAt y vy τ := by
    convert (componentCLM (system := self.toSystem) 1).hasFDerivAt.comp_hasDerivAt τ
      pos_has_deriv using 1 <;> rfl
  have z_has_deriv : HasDerivAt z z' τ := by
    have pair_has_deriv := y_has_deriv.neg.prodMk x_has_deriv
    have complex_has_deriv :=
      Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt τ pair_has_deriv
    convert complex_has_deriv using 1 <;> rfl
  have z_ne_zero : ∀ s, z s ≠ 0 := by
    intro s z_eq_zero
    have x_eq_zero : x s = 0 := by
      have := congrArg Complex.im z_eq_zero
      simpa [z] using this
    have y_eq_zero : y s = 0 := by
      have := congrArg Complex.re z_eq_zero
      simpa [z] using this
    have pos_norm_eq_zero : ‖self.bob.1.pos (Time.toRealCLE.symm s)‖ = 0 := by
      rw [vector_norm_l2_if_orthonormal
        self.orthonormal]
      simp [Fin.sum_univ_two, x, y, x_eq_zero, y_eq_zero]
    have length_eq := self.length_constant (Time.toRealCLE.symm s)
    change ‖self.bob.1.pos (Time.toRealCLE.symm s)‖ = self.L at length_eq
    rw [pos_norm_eq_zero] at length_eq
    nlinarith [self.L.property]
  have radius_eq : Real.sqrt (x τ ^ 2 + y τ ^ 2) = self.L := by
    calc
      Real.sqrt (x τ ^ 2 + y τ ^ 2) = ‖self.bob.1.pos t‖ := by
        rw [vector_norm_l2_if_orthonormal
          self.orthonormal]
        simp only [Fin.sum_univ_two]
        simp [x, y, τ]
      _ = self.L := by
        simpa only [PointParticle.System.Particle.pos] using self.length_constant t
  have radius_sq : x τ ^ 2 + y τ ^ 2 = self.L ^ 2 := by
    have := congrArg (fun r : ℝ ↦ r ^ 2) radius_eq
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg (x τ)) (sq_nonneg (y τ)))] at this
    exact this
  have normSq_eq : Complex.normSq (z τ) = self.L ^ 2 := by
    rw [Complex.normSq_apply]
    change -y τ * -y τ + x τ * x τ = self.L ^ 2
    nlinarith
  have theta_eq : self.θ =
      fun s : Time ↦ (Complex.arg (z (Time.toRealCLE s)) : Real.Angle) := by
    funext s
    change (Complex.arg ⟨-(self.bob.pos s).components 1,
      (self.bob.pos s).components 0⟩ : Real.Angle) = _
    dsimp only [z, x, y]
    rw [show Time.toRealCLE.symm (Time.toRealCLE s) = s by simp]
    apply congrArg (fun w : ℂ ↦ (Complex.arg w : Real.Angle))
    apply Complex.ext <;> rfl
  rw [Pendulum.ω, theta_eq, Time.manifoldDeriv_eq]
  have real_derivative := hasMFDerivAt_angle_arg z_has_deriv z_ne_zero
  have time_derivative : HasMFDerivAt 𝓘(ℝ, Time) 𝓘(ℝ)
      (fun s : Time ↦ (Complex.arg (z (Time.toRealCLE s)) : Real.Angle)) t
      ((ContinuousLinearMap.toSpanSingleton ℝ (z' / z τ).im).comp Time.toRealCLM) := by
    convert real_derivative.comp t Time.toRealCLM.hasFDerivAt.hasMFDerivAt using 1
    all_goals rfl
  have mfderiv_eq := time_derivative.mfderiv
  rw [mfderiv_eq]
  have comp_apply_eq :
      ((ContinuousLinearMap.toSpanSingleton ℝ (z' / z τ).im).comp Time.toRealCLM)
          (1 : Time) = (z' / z τ).im := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    have one_eq : Time.toRealCLM (1 : Time) = (1 : ℝ) := by
      change (1 : Time).val = (1 : ℝ)
      rw [Time.one_val]
    rw [one_eq, one_smul]
  refine comp_apply_eq.trans ?_
  calc
    (z' / z τ).im = (x τ * vy - y τ * vx) / self.L ^ 2 := by
      rw [Complex.div_im, normSq_eq]
      change vx * -y τ / self.L ^ 2 - -vy * x τ / self.L ^ 2 = _
      ring
    _ = _ := by
      simp [x, y, τ, vx, vy, PointParticle.System.Particle.pos,
        PointParticle.System.Particle.vel]

lemma angular_acceleration_eq (self : Pendulum) (t : Time) :
    Time.deriv self.ω t =
      ((self.bob.pos t).components 0 * (self.bob.acc t).components 1 -
        (self.bob.pos t).components 1 * (self.bob.acc t).components 0) / self.L ^ 2 := by
  let τ := Time.toRealCLE t
  let x := fun s : ℝ ↦ (self.bob.1.pos (Time.toRealCLE.symm s)).components 0
  let y := fun s : ℝ ↦ (self.bob.1.pos (Time.toRealCLE.symm s)).components 1
  let vx := fun s : ℝ ↦ (self.bob.1.vel (Time.toRealCLE.symm s)).components 0
  let vy := fun s : ℝ ↦ (self.bob.1.vel (Time.toRealCLE.symm s)).components 1
  let ax := (self.bob.1.acc t).components 0
  let ay := (self.bob.1.acc t).components 1
  have pos_has_deriv : HasDerivAt
      (fun s : ℝ ↦ self.bob.1.pos (Time.toRealCLE.symm s)) (self.bob.1.vel t) τ := by
    simpa only [τ, ContinuousLinearEquiv.symm_apply_apply,
      ReferenceFrame.Particle.vel] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.pos τ
        (self.bob.1.pos_twice_differentiable self.isInertial.out).1.differentiableAt
  have vel_has_deriv : HasDerivAt
      (fun s : ℝ ↦ self.bob.1.vel (Time.toRealCLE.symm s)) (self.bob.1.acc t) τ := by
    simpa only [τ, ContinuousLinearEquiv.symm_apply_apply,
      ReferenceFrame.Particle.acc] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.vel τ
        (self.bob.1.pos_twice_differentiable self.isInertial.out).2.differentiableAt
  have x_has_deriv : HasDerivAt x (vx τ) τ := by
    convert (componentCLM (system := self.toSystem) 0).hasFDerivAt.comp_hasDerivAt τ
      pos_has_deriv using 1 <;> rfl
  have y_has_deriv : HasDerivAt y (vy τ) τ := by
    convert (componentCLM (system := self.toSystem) 1).hasFDerivAt.comp_hasDerivAt τ
      pos_has_deriv using 1 <;> rfl
  have vx_has_deriv : HasDerivAt vx ax τ := by
    convert (componentCLM (system := self.toSystem) 0).hasFDerivAt.comp_hasDerivAt τ
      vel_has_deriv using 1 <;> rfl
  have vy_has_deriv : HasDerivAt vy ay τ := by
    convert (componentCLM (system := self.toSystem) 1).hasFDerivAt.comp_hasDerivAt τ
      vel_has_deriv using 1 <;> rfl
  have ω_eq : self.ω =
      fun s : Time ↦ (x s.val * vy s.val - y s.val * vx s.val) / self.L ^ 2 := by
    funext s
    rw [angular_velocity_eq self s]
    simp only [PointParticle.System.Particle.pos, PointParticle.System.Particle.vel]
    dsimp only [x, y, vx, vy]
    rw [show Time.toRealCLE.symm s.val = s by
      exact Time.toRealCLE.symm_apply_apply s]
  rw [ω_eq]
  have cross_has_deriv :=
    ((x_has_deriv.mul vy_has_deriv).sub (y_has_deriv.mul vx_has_deriv)).div_const
      (self.L ^ 2)
  have cross_time_deriv := time_deriv_comp_val (t := t) cross_has_deriv
  simp only [Pi.mul_apply, Pi.sub_apply] at cross_time_deriv
  rw [cross_time_deriv]
  simp only [PointParticle.System.Particle.pos, PointParticle.System.Particle.acc]
  change ((vx τ * vy τ + x τ * ay) - (vy τ * vx τ + y τ * ax)) / self.L ^ 2 = _
  simp only [τ, x, y, vx, vy, ContinuousLinearEquiv.symm_apply_apply]
  ring

lemma tension_source_eq_pivot (self : Pendulum) :
    self.tension.source = self.pivot := by
  have source_cases : self.tension.source = self.pivot ∨ self.tension.source = self.bob := by
    have source_mem_univ : self.tension.source ∈ (Set.univ : Set self.Particle) :=
      Set.mem_univ _
    rw [self.no_other_particles] at source_mem_univ
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using source_mem_univ
  have source_ne_bob : self.tension.source ≠ self.bob := by
    intro source_eq_bob
    apply self.tension.1.source_ne_target
    exact source_eq_bob.trans self.tension_targets_bob.symm
  exact source_cases.resolve_right source_ne_bob

lemma pivot_ne_bob (self : Pendulum) : self.pivot ≠ self.bob := by
  intro pivot_eq_bob
  apply self.tension.1.source_ne_target
  calc
    self.tension.source = self.pivot := tension_source_eq_pivot self
    _ = self.bob := pivot_eq_bob
    _ = self.tension.target := self.tension_targets_bob.symm

lemma bob_newton_second_law (self : Pendulum) (t : Time) :
    self.tension.value t + gravity self.bob self.g t =
      self.bob.mass • self.bob.acc t := by
  have second_law := congrFun (self.newton_second_law self.bob) t
  rw [self.no_other_internal_forces, self.no_other_external_forces] at second_law
  rw [netForce_eq_multiset_sum] at second_law
  have tension_target : self.tension.1.target = self.bob := self.tension_targets_bob
  have reverse_target_ne : self.tension.reverse.1.target ≠ self.bob := by
    change self.tension.source ≠ self.bob
    rw [tension_source_eq_pivot]
    exact pivot_ne_bob self
  have gravity_bob_target : (gravity self.bob self.g).target = self.bob := rfl
  have gravity_pivot_target_ne : (gravity self.pivot self.g).target ≠ self.bob :=
    pivot_ne_bob self
  have support_target_ne : self.pivotSupportForce.inner.target ≠ self.bob := by
    rw [show self.pivotSupportForce.inner.target = self.pivot by
      exact self.support_targets_pivot]
    exact pivot_ne_bob self
  simp [Multiset.filter_singleton, tension_target, reverse_target_ne,
    gravity_bob_target, gravity_pivot_target_ne, support_target_ne] at second_law
  have bob_acc_eq : self.bob.1.acc t = self.bob.acc t := rfl
  simpa only [PointParticle.System.InternalForce.value,
    PointParticle.System.Particle.mass, bob_acc_eq, add_comm] using second_law

lemma horizontal_position_eq (self : Pendulum) (t : Time) :
    (self.bob.pos t).components 0 = self.L * Real.Angle.sin (self.θ t) := by
  let x := (self.bob.pos t).components 0
  let y := (self.bob.pos t).components 1
  let z := Complex.mk (-y) x
  have radius_eq : Real.sqrt (x ^ 2 + y ^ 2) = self.L := by
    calc
      Real.sqrt (x ^ 2 + y ^ 2) = ‖self.bob.pos t‖ := by
        rw [vector_norm_l2_if_orthonormal
          self.orthonormal]
        simp only [Fin.sum_univ_two]
        simp [x, y]
      _ = self.L := self.length_constant t
  have radius_sq : x ^ 2 + y ^ 2 = self.L ^ 2 := by
    have := congrArg (fun r : ℝ ↦ r ^ 2) radius_eq
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))] at this
    exact this
  have z_norm_sq : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    change -y * -y + x * x = x ^ 2 + y ^ 2
    ring
  have z_norm : ‖z‖ = self.L := by
    nlinarith [norm_nonneg z, self.L.property]
  change x = self.L * Real.Angle.sin (Complex.arg z : Real.Angle)
  rw [Real.Angle.sin_coe, Complex.sin_arg, z_norm]
  change x = self.L * (x / self.L)
  field_simp [ne_of_gt self.L.property]

lemma bob_torque_eq (self : Pendulum) (t : Time) :
    (self.bob.pos t).components 0 * (self.bob.acc t).components 1 -
        (self.bob.pos t).components 1 * (self.bob.acc t).components 0 =
      -self.g * (self.bob.pos t).components 0 := by
  obtain ⟨c, tension_central⟩ := self.tension_central t
  have pivot_pos : self.pivot.pos t = 0 := congrFun self.pivot_at_origin t
  rw [self.tension_targets_bob, tension_source_eq_pivot, pivot_pos, sub_zero]
    at tension_central
  have second_law := bob_newton_second_law self t
  rw [tension_central] at second_law
  have horizontal := congrArg (fun v ↦ v.components 0) second_law
  have vertical := congrArg (fun v ↦ v.components 1) second_law
  simp [gravity] at horizontal vertical
  have mass_pos := self.bob.mass.property
  have torque_scaled : self.bob.mass.val *
      ((self.bob.pos t).components 0 * (self.bob.acc t).components 1 -
        (self.bob.pos t).components 1 * (self.bob.acc t).components 0 +
        self.g.val * (self.bob.pos t).components 0) = 0 := by
    linear_combination
      -((self.bob.pos t).components 0) * vertical +
        (self.bob.pos t).components 1 * horizontal
  have torque_zero := (mul_eq_zero.mp torque_scaled).resolve_left (ne_of_gt mass_pos)
  linarith

lemma differential_equation (self : Pendulum) (t : Time) :
    Time.deriv self.ω t = -self.g / self.L * Real.Angle.sin (self.θ t) := by
  calc
    Time.deriv self.ω t =
        ((self.bob.pos t).components 0 * (self.bob.acc t).components 1 -
          (self.bob.pos t).components 1 * (self.bob.acc t).components 0) / self.L ^ 2 :=
      angular_acceleration_eq self t
    _ = (-self.g * (self.bob.pos t).components 0) / self.L ^ 2 := by
      rw [bob_torque_eq self t]
    _ = -self.g / self.L * Real.Angle.sin (self.θ t) := by
      rw [horizontal_position_eq self t]
      field_simp [ne_of_gt self.L.property]

lemma bounded_function_not_constant_negative_second_deriv
    (f : ℝ → ℝ) (B a : ℝ)
    (B_nonnegative : 0 ≤ B)
    (f_bounded : ∀ t, |f t| ≤ B)
    (f_differentiable : Differentiable ℝ f)
    (deriv_differentiable : Differentiable ℝ (deriv f))
    (second_deriv_eq : ∀ t, deriv (deriv f) t = a)
    (a_negative : a < 0) : False := by
  let v0 := deriv f 0
  let linear : ℝ → ℝ := fun t ↦ a * t
  let q := deriv f - linear
  have q_differentiable : Differentiable ℝ q := by
    dsimp only [q, linear]
    fun_prop
  have q_deriv_zero (t : ℝ) : deriv q t = 0 := by
    have linear_deriv : HasDerivAt linear a t := by
      exact ((hasDerivAt_id t).const_mul a).congr_deriv (by ring)
    have q_deriv : HasDerivAt q (deriv (deriv f) t - a) t :=
      (deriv_differentiable t).hasDerivAt.sub linear_deriv
    rw [q_deriv.deriv, second_deriv_eq]
    ring
  have deriv_eq (t : ℝ) : deriv f t = a * t + v0 := by
    have q_eq := is_const_of_deriv_eq_zero q_differentiable q_deriv_zero t 0
    simp only [q, linear, Pi.sub_apply] at q_eq
    linarith
  let polynomial : ℝ → ℝ :=
    (fun t ↦ a / 2 * t ^ 2) + fun t ↦ v0 * t
  let r := f - polynomial
  have r_differentiable : Differentiable ℝ r := by
    dsimp only [r, polynomial]
    fun_prop
  have r_deriv_zero (t : ℝ) : deriv r t = 0 := by
    have polynomial_deriv : HasDerivAt polynomial (a * t + v0) t := by
      apply HasDerivAt.congr_deriv
        ((((hasDerivAt_id t).pow 2).const_mul (a / 2)).add
          ((hasDerivAt_id t).const_mul v0))
      simp only [id_eq]
      ring
    have r_deriv : HasDerivAt r (deriv f t - (a * t + v0)) t :=
      (f_differentiable t).hasDerivAt.sub polynomial_deriv
    rw [r_deriv.deriv, deriv_eq]
    ring
  have function_eq (t : ℝ) : f t = a / 2 * t ^ 2 + v0 * t + f 0 := by
    have r_eq := is_const_of_deriv_eq_zero r_differentiable r_deriv_zero t 0
    simp only [r, polynomial, Pi.sub_apply, Pi.add_apply] at r_eq
    linarith
  let A := -a
  let C := |f 0| + B + 1
  let t := C / A + 1
  have A_positive : 0 < A := by simp only [A]; linarith
  have C_positive : 0 < C := by
    dsimp only [C]
    linarith [abs_nonneg (f 0)]
  have quadratic_dominates : 2 * C < A * t ^ 2 := by
    have A_ne_zero := ne_of_gt A_positive
    have C_sq_div_nonnegative : 0 ≤ C ^ 2 / A :=
      div_nonneg (sq_nonneg C) A_positive.le
    have expansion : A * t ^ 2 = C ^ 2 / A + 2 * C + A := by
      dsimp only [t]
      field_simp [A_ne_zero]
      ring
    rw [expansion]
    linarith
  have quadratic_lt : a * t ^ 2 + 2 * f 0 < -2 * B := by
    have f_zero_le : f 0 ≤ |f 0| := le_abs_self (f 0)
    dsimp only [A, C] at quadratic_dominates
    linarith
  have lower_at_t := (abs_le.mp (f_bounded t)).1
  have lower_at_neg_t := (abs_le.mp (f_bounded (-t))).1
  rw [function_eq t] at lower_at_t
  rw [function_eq (-t)] at lower_at_neg_t
  nlinarith

lemma specs_uniqueness (system : PointParticle.System 2) (self : Specs system) :
    Set.univ = {self} := by
  ext other
  simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
  have self_pivot_ne_bob : self.pivot ≠ self.bob := by
    intro pivot_eq_bob
    have length_at_zero := self.length_constant 0
    have pivot_at_zero := congrFun self.pivot_at_origin 0
    rw [← pivot_eq_bob, pivot_at_zero] at length_at_zero
    have L_eq_zero : self.L.val = 0 := by simpa using length_at_zero.symm
    exact (ne_of_gt self.L.property) L_eq_zero
  have self_particle_cases (particle : system.Particle) :
      particle = self.pivot ∨ particle = self.bob := by
    have particle_mem : particle ∈ (Set.univ : Set system.Particle) := Set.mem_univ particle
    rw [self.no_other_particles] at particle_mem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using particle_mem
  have pivots_eq : other.pivot = self.pivot := by
    rcases self_particle_cases other.pivot with pivot_eq | pivot_eq
    · exact pivot_eq
    · exfalso
      have length_at_zero := self.length_constant 0
      have other_pivot_at_zero := congrFun other.pivot_at_origin 0
      rw [← pivot_eq, other_pivot_at_zero] at length_at_zero
      have L_eq_zero : self.L.val = 0 := by simpa using length_at_zero.symm
      exact (ne_of_gt self.L.property) L_eq_zero
  have bobs_eq : other.bob = self.bob := by
    rcases self_particle_cases other.bob with bob_eq | bob_eq
    · exfalso
      have other_length_at_zero := other.length_constant 0
      have self_pivot_at_zero := congrFun self.pivot_at_origin 0
      rw [bob_eq, self_pivot_at_zero] at other_length_at_zero
      have L_eq_zero : other.L.val = 0 := by simpa using other_length_at_zero.symm
      exact (ne_of_gt other.L.property) L_eq_zero
    · exact bob_eq
  have lengths_eq : other.L = self.L := by
    apply Subtype.ext
    have other_length_at_zero := other.length_constant 0
    rw [bobs_eq] at other_length_at_zero
    exact other_length_at_zero.symm.trans (self.length_constant 0)
  have self_tension_source_eq : self.tension.source = self.pivot := by
    rcases self_particle_cases self.tension.source with source_eq | source_eq
    · exact source_eq
    · exfalso
      apply self.tension.1.source_ne_target
      exact source_eq.trans self.tension_targets_bob.symm
  let other_tension_value : system.frame.InternalForce system.Particle := other.tension.1
  let self_tension_value : system.frame.InternalForce system.Particle := self.tension.1
  let self_reverse_value : system.frame.InternalForce system.Particle := self.tension.reverse.1
  have other_tension_mem : other_tension_value ∈ system.internalForces :=
    Multiset.count_pos.mp (Nat.zero_lt_of_lt other.tension.2.isLt)
  rw [self.no_other_internal_forces] at other_tension_mem
  have other_tension_cases :
      other_tension_value = self_tension_value ∨ other_tension_value = self_reverse_value := by
    rcases Multiset.mem_cons.mp other_tension_mem with tension_eq | tension_eq
    · exact Or.inl tension_eq
    · exact Or.inr (Multiset.mem_singleton.mp tension_eq)
  have tension_values_eq : other.tension.1 = self.tension.1 := by
    rcases other_tension_cases with tension_eq | tension_eq
    · simpa only [other_tension_value, self_tension_value] using tension_eq
    · exfalso
      apply self_pivot_ne_bob
      have targets_eq := congrArg
        (fun force : system.frame.InternalForce system.Particle ↦ force.target)
        tension_eq.symm
      calc
        self.pivot = self.tension.source := self_tension_source_eq.symm
        _ = self.tension.reverse.1.target := rfl
        _ = other.tension.1.target := by
          simpa only [other_tension_value, self_reverse_value] using targets_eq
        _ = other.bob := other.tension_targets_bob
        _ = self.bob := bobs_eq
  have tension_ne_reverse : self.tension.1 ≠ self.tension.reverse.1 := by
    intro tension_eq
    apply self_pivot_ne_bob
    have targets_eq := congrArg
      (fun force : system.frame.InternalForce system.Particle ↦ force.target)
      tension_eq.symm
    calc
      self.pivot = self.tension.source := self_tension_source_eq.symm
      _ = self.tension.reverse.1.target := rfl
      _ = self.tension.1.target := targets_eq
      _ = self.bob := self.tension_targets_bob
  have tension_count : Multiset.count self.tension.1 system.internalForces = 1 := by
    calc
      _ = Multiset.count self.tension.1
          {self.tension.1, self.tension.reverse.1} :=
        congrArg (Multiset.count self.tension.1) self.no_other_internal_forces
      _ = 1 := by simp [tension_ne_reverse]
  have tensions_eq : other.tension = self.tension := by
    apply Sigma.ext
    · exact tension_values_eq
    · apply (Fin.heq_ext_iff (congrArg
        (fun force ↦ Multiset.count force system.internalForces) tension_values_eq)).2
      have other_count : Multiset.count other.tension.1 system.internalForces = 1 :=
        (congrArg (fun force ↦ Multiset.count force system.internalForces)
          tension_values_eq).trans tension_count
      have other_index_lt := other.tension.2.isLt
      have self_index_lt := self.tension.2.isLt
      omega
  have external_forces_eq :
      ({gravity self.bob other.g, gravity self.pivot other.g, ↑other.pivotSupportForce} :
        Multiset (system.frame.Force system.Particle)) =
      ({gravity self.bob self.g, gravity self.pivot self.g, ↑self.pivotSupportForce} :
        Multiset (system.frame.Force system.Particle)) := by
    simpa only [bobs_eq, pivots_eq] using
      other.no_other_external_forces.symm.trans self.no_other_external_forces
  have other_support_target : other.pivotSupportForce.inner.target = self.pivot := by
    rw [← pivots_eq]
    exact other.support_targets_pivot
  have self_support_target : self.pivotSupportForce.inner.target = self.pivot :=
    self.support_targets_pivot
  have gravity_bob_eq : gravity self.bob other.g = gravity self.bob self.g := by
    have filtered_eq := congrArg
      (Multiset.filter fun force ↦ force.target = self.bob) external_forces_eq
    simpa [Multiset.filter_cons, Multiset.filter_singleton, gravity, self_pivot_ne_bob,
      other_support_target, self_support_target] using filtered_eq
  have gravity_value_eq := congrArg
    (fun force ↦ (force.value 0).components 1) gravity_bob_eq
  simp only [gravity, Matrix.cons_val_one, Matrix.cons_val_zero] at gravity_value_eq
  have gravities_eq : other.g = self.g := by
    apply Subtype.ext
    apply mul_left_cancel₀ (ne_of_gt self.bob.mass.property)
    linarith
  have support_values_eq : other.pivotSupportForce.inner = self.pivotSupportForce.inner := by
    rw [gravities_eq] at external_forces_eq
    have without_bob_gravity :=
      (Multiset.cons_inj_right (gravity self.bob self.g)).mp external_forces_eq
    have without_pivot_gravity :=
      (Multiset.cons_inj_right (gravity self.pivot self.g)).mp without_bob_gravity
    simpa using without_pivot_gravity
  let y := fun t : ℝ ↦
    (self.bob.pos (Time.toRealCLE.symm t)).components 1
  have position_deriv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ self.bob.1.pos (Time.toRealCLE.symm s))
        (self.bob.1.vel (Time.toRealCLE.symm t)) t := by
    simpa only [ReferenceFrame.Particle.vel] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.pos t
        (self.bob.1.pos_twice_differentiable system.isInertial.out).1.differentiableAt
  have y_deriv (t : ℝ) : HasDerivAt y
      ((self.bob.vel (Time.toRealCLE.symm t)).components 1) t := by
    convert (componentCLM (system := system) 1).hasFDerivAt.comp_hasDerivAt t
      (position_deriv t) using 1 <;> rfl
  have velocity_deriv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ self.bob.1.vel (Time.toRealCLE.symm s))
        (self.bob.1.acc (Time.toRealCLE.symm t)) t := by
    simpa only [ReferenceFrame.Particle.acc] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.vel t
        (self.bob.1.pos_twice_differentiable system.isInertial.out).2.differentiableAt
  have vertical_velocity_deriv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ (self.bob.vel (Time.toRealCLE.symm s)).components 1)
        ((self.bob.acc (Time.toRealCLE.symm t)).components 1) t := by
    convert (componentCLM (system := system) 1).hasFDerivAt.comp_hasDerivAt t
      (velocity_deriv t) using 1 <;> rfl
  have deriv_y_eq : deriv y =
      fun t ↦ (self.bob.vel (Time.toRealCLE.symm t)).components 1 := by
    funext t
    exact (y_deriv t).deriv
  have y_differentiable : Differentiable ℝ y := fun t ↦ (y_deriv t).differentiableAt
  have deriv_y_differentiable : Differentiable ℝ (deriv y) := by
    rw [deriv_y_eq]
    exact fun t ↦ (vertical_velocity_deriv t).differentiableAt
  have second_deriv_y_eq (t : ℝ) :
      deriv (deriv y) t =
        (self.bob.acc (Time.toRealCLE.symm t)).components 1 := by
    rw [deriv_y_eq]
    exact (vertical_velocity_deriv t).deriv
  have y_bounded (t : ℝ) : |y t| ≤ self.L.val := by
    have norm_eq := self.length_constant (Time.toRealCLE.symm t)
    rw [vector_norm_l2_if_orthonormal self.orthonormal,
      Fin.sum_univ_two] at norm_eq
    have norm_sq := congrArg (fun r : ℝ ↦ r ^ 2) norm_eq
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at norm_sq
    have y_abs_nonnegative := abs_nonneg (y t)
    have y_abs_sq : |y t| ^ 2 = y t ^ 2 := sq_abs (y t)
    dsimp only [y]
    dsimp only [y] at y_abs_nonnegative y_abs_sq
    nlinarith [sq_nonneg
      ((self.bob.pos (Time.toRealCLE.symm t)).components 0), self.L.property]
  have tension_target_ne_pivot : self.tension.1.target ≠ self.pivot := by
    intro target_eq
    apply self_pivot_ne_bob
    exact (self.tension_targets_bob.symm.trans target_eq).symm
  have reverse_target_pivot : self.tension.reverse.1.target = self.pivot := by
    change self.tension.source = self.pivot
    exact self_tension_source_eq
  have gravity_bob_target_ne_pivot : (gravity self.bob self.g).target ≠ self.pivot :=
    self_pivot_ne_bob.symm
  have gravity_pivot_target : (gravity self.pivot self.g).target = self.pivot := rfl
  have pivot_acc_zero (t : Time) : self.pivot.1.acc t = 0 := by
    have pivot_pos : self.pivot.1.pos = 0 := by
      funext s
      have pivot_at_s := congrFun self.pivot_at_origin s
      simpa only [PointParticle.System.Particle.pos] using pivot_at_s
    rw [ReferenceFrame.Particle.acc, ReferenceFrame.Particle.vel, pivot_pos]
    have derivative_zero : Time.deriv (0 : Time → system.Vector) = 0 := by
      funext s
      exact Time.deriv_const (t := s) 0
    rw [derivative_zero]
    exact Time.deriv_const (t := t) 0
  have pivot_second_law (t : Time) :
      self.tension.reverse.1.value t + (gravity self.pivot self.g).value t +
        self.pivotSupportForce.inner.value t = 0 := by
    have second_law := congrFun (system.newton_second_law self.pivot) t
    rw [self.no_other_internal_forces, self.no_other_external_forces] at second_law
    rw [netForce_eq_multiset_sum] at second_law
    simp [Multiset.filter_singleton, tension_target_ne_pivot,
      reverse_target_pivot, gravity_bob_target_ne_pivot, gravity_pivot_target,
      self_support_target, pivot_acc_zero] at second_law
    have positive_smul_zero (m : ℝ+) : m • (0 : system.Vector) = 0 := by
      change m.val • (0 : system.Vector) = 0
      simp
    simpa only [PointParticle.System.Particle.mass, positive_smul_zero, add_comm,
      add_left_comm, add_assoc] using second_law
  let pendulum : Pendulum := { toSystem := system, toSpecs := self }
  have bob_second_law (t : Time) :
      self.tension.1.value t + (gravity self.bob self.g).value t =
        self.bob.mass • self.bob.acc t := by
    simpa only [pendulum, PointParticle.System.InternalForce.value] using
      bob_newton_second_law pendulum t
  have support_ne_reverse :
      self.pivotSupportForce.inner ≠ self.tension.reverse.1.toForce := by
    intro support_eq
    let a := -(self.pivot.mass.val * self.g.val / 2 +
      self.bob.mass.val * self.g.val) / self.bob.mass.val
    have acceleration_eq (t : Time) : (self.bob.acc t).components 1 = a := by
      have pivot_vertical := congrArg (componentCLM (system := system) 1)
        (pivot_second_law t)
      have bob_vertical := congrArg (componentCLM (system := system) 1)
        (bob_second_law t)
      simp [gravity] at pivot_vertical bob_vertical
      have support_vertical : (self.pivotSupportForce.inner.value t).components 1 =
          (self.tension.reverse.1.value t).components 1 :=
        congrArg (fun force ↦ (force.value t).components 1) support_eq
      rw [support_vertical] at pivot_vertical
      have reverse_vertical : (self.tension.reverse.1.value t).components 1 =
          -(self.tension.1.value t).components 1 := rfl
      rw [reverse_vertical] at pivot_vertical
      dsimp only [a]
      field_simp [ne_of_gt self.bob.mass.property]
      nlinarith
    have a_negative : a < 0 := by
      dsimp only [a]
      have numerator_positive : 0 < self.pivot.mass.val * self.g.val / 2 +
          self.bob.mass.val * self.g.val := by
        nlinarith [self.pivot.mass.property, self.bob.mass.property, self.g.property]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr numerator_positive)
        self.bob.mass.property
    exact bounded_function_not_constant_negative_second_deriv y self.L.val a
      self.L.property.le y_bounded y_differentiable deriv_y_differentiable
      (fun t ↦ (second_deriv_y_eq t).trans
        (acceleration_eq (Time.toRealCLE.symm t))) a_negative
  have support_ne_gravity_pivot :
      self.pivotSupportForce.inner ≠ gravity self.pivot self.g := by
    intro support_eq
    let a := -(2 * self.pivot.mass.val * self.g.val +
      self.bob.mass.val * self.g.val) / self.bob.mass.val
    have acceleration_eq (t : Time) : (self.bob.acc t).components 1 = a := by
      have pivot_vertical := congrArg (componentCLM (system := system) 1)
        (pivot_second_law t)
      have bob_vertical := congrArg (componentCLM (system := system) 1)
        (bob_second_law t)
      simp [gravity] at pivot_vertical bob_vertical
      have support_vertical : (self.pivotSupportForce.inner.value t).components 1 =
          ((gravity self.pivot self.g).value t).components 1 :=
        congrArg (fun force ↦ (force.value t).components 1) support_eq
      rw [support_vertical] at pivot_vertical
      simp only [gravity, Matrix.cons_val_one, Matrix.cons_val_zero] at pivot_vertical
      have reverse_vertical : (self.tension.reverse.1.value t).components 1 =
          -(self.tension.1.value t).components 1 := rfl
      rw [reverse_vertical] at pivot_vertical
      dsimp only [a]
      field_simp [ne_of_gt self.bob.mass.property]
      nlinarith
    have a_negative : a < 0 := by
      dsimp only [a]
      have numerator_positive : 0 < 2 * self.pivot.mass.val * self.g.val +
          self.bob.mass.val * self.g.val := by
        nlinarith [self.pivot.mass.property, self.bob.mass.property, self.g.property]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr numerator_positive)
        self.bob.mass.property
    exact bounded_function_not_constant_negative_second_deriv y self.L.val a
      self.L.property.le y_bounded y_differentiable deriv_y_differentiable
      (fun t ↦ (second_deriv_y_eq t).trans
        (acceleration_eq (Time.toRealCLE.symm t))) a_negative
  have support_ne_tension :
      self.pivotSupportForce.inner ≠ self.tension.1.toForce := by
    intro support_eq
    apply self_pivot_ne_bob
    calc
      self.pivot = self.pivotSupportForce.target := self_support_target.symm
      _ = self.tension.1.target :=
        congrArg ReferenceFrame.Force.target support_eq
      _ = self.bob := self.tension_targets_bob
  have support_ne_gravity_bob :
      self.pivotSupportForce.inner ≠ gravity self.bob self.g := by
    intro support_eq
    apply self_pivot_ne_bob
    calc
      self.pivot = self.pivotSupportForce.target := self_support_target.symm
      _ = (gravity self.bob self.g).target :=
        congrArg ReferenceFrame.Force.target support_eq
      _ = self.bob := rfl
  let support_value : system.frame.Force system.Particle := self.pivotSupportForce.inner
  have support_count : Multiset.count support_value
      system.externalForces = 1 := by
    calc
      _ = Multiset.count support_value
          {gravity self.bob self.g, gravity self.pivot self.g,
            self.pivotSupportForce.inner} := by
        exact congrArg (Multiset.count support_value) self.no_other_external_forces
      _ = 1 := by
        simp [support_value, support_ne_gravity_bob, support_ne_gravity_pivot]
  have support_is_external (support : system.Force)
      (support_value_eq : support.inner = self.pivotSupportForce.inner) :
      support.External := by
    rcases support with internal | external
    · exfalso
      let internal_value : system.frame.InternalForce system.Particle := internal.1
      have internal_mem : internal_value ∈ system.internalForces :=
        Multiset.count_pos.mp (Nat.zero_lt_of_lt internal.2.isLt)
      rw [self.no_other_internal_forces] at internal_mem
      rcases Multiset.mem_cons.mp internal_mem with internal_eq | internal_eq
      · apply support_ne_tension
        calc
          self.pivotSupportForce.inner = internal_value.toForce := by
            simpa only [PointParticle.System.Force.inner] using support_value_eq.symm
          _ = self.tension.1.toForce := congrArg ReferenceFrame.InternalForce.toForce internal_eq
      · apply support_ne_reverse
        calc
          self.pivotSupportForce.inner = internal_value.toForce := by
            simpa only [PointParticle.System.Force.inner] using support_value_eq.symm
          _ = self.tension.reverse.1.toForce :=
            congrArg ReferenceFrame.InternalForce.toForce (Multiset.mem_singleton.mp internal_eq)
    · exact Sum.isRight_inr
  have self_support_external : self.pivotSupportForce.External :=
    support_is_external self.pivotSupportForce rfl
  have other_support_external : other.pivotSupportForce.External :=
    support_is_external other.pivotSupportForce support_values_eq
  have support_forces_eq : other.pivotSupportForce = self.pivotSupportForce := by
    let other_support := other.pivotSupportForce.getRight other_support_external
    let self_support := self.pivotSupportForce.getRight self_support_external
    have other_support_value : other_support.1 = other.pivotSupportForce.inner := by
      simpa only [other_support, PointParticle.System.Force.inner] using
        congrArg PointParticle.System.Force.inner
          (Sum.inr_getRight other.pivotSupportForce other_support_external)
    have self_support_value : self_support.1 = self.pivotSupportForce.inner := by
      simpa only [self_support, PointParticle.System.Force.inner] using
        congrArg PointParticle.System.Force.inner
          (Sum.inr_getRight self.pivotSupportForce self_support_external)
    have external_values_eq : other_support.1 = self_support.1 :=
      other_support_value.trans (support_values_eq.trans self_support_value.symm)
    have external_occurrences_eq : other_support = self_support := by
      apply Sigma.ext
      · exact external_values_eq
      · apply (Fin.heq_ext_iff (congrArg
          (fun force ↦ Multiset.count force system.externalForces) external_values_eq)).2
        have other_count : Multiset.count other_support.1 system.externalForces = 1 := by
          rw [external_values_eq, self_support_value]
          exact support_count
        have self_count : Multiset.count self_support.1 system.externalForces = 1 := by
          rw [self_support_value]
          exact support_count
        have other_index_lt := other_support.2.isLt
        have self_index_lt := self_support.2.isLt
        omega
    calc
      other.pivotSupportForce = Sum.inr other_support :=
        (Sum.inr_getRight other.pivotSupportForce other_support_external).symm
      _ = Sum.inr self_support := congrArg Sum.inr external_occurrences_eq
      _ = self.pivotSupportForce :=
        Sum.inr_getRight self.pivotSupportForce self_support_external
  cases self
  cases other
  simp_all

def nonlinearPeriodIntegrand (a u : ℝ) : ℝ :=
  (√(1 - (Real.sin (a / 2) * Real.cos u) ^ 2))⁻¹

lemma nonlinearPeriod_radicand_pos {a : ℝ} (a_pos : 0 < a) (a_lt_pi : a < Real.pi)
    (u : ℝ) :
    0 < 1 - (Real.sin (a / 2) * Real.cos u) ^ 2 := by
  have half_mem : a / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have sin_sq_lt_one : Real.sin (a / 2) ^ 2 < 1 := by
    have cos_pos := Real.cos_pos_of_mem_Ioo half_mem
    nlinarith [Real.sin_sq_add_cos_sq (a / 2)]
  have cos_sq_le_one : Real.cos u ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have product_sq_lt_one :
      (Real.sin (a / 2) * Real.cos u) ^ 2 < 1 := by
    calc
      (Real.sin (a / 2) * Real.cos u) ^ 2 =
          Real.sin (a / 2) ^ 2 * Real.cos u ^ 2 := by ring
      _ ≤ Real.sin (a / 2) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left cos_sq_le_one (sq_nonneg _)
      _ < 1 := by simpa using sin_sq_lt_one
  linarith

lemma nonlinearPeriodIntegrand_pos {a : ℝ} (a_pos : 0 < a) (a_lt_pi : a < Real.pi)
    (u : ℝ) :
    0 < nonlinearPeriodIntegrand a u := by
  rw [nonlinearPeriodIntegrand]
  exact inv_pos.mpr (Real.sqrt_pos.2 (nonlinearPeriod_radicand_pos a_pos a_lt_pi u))

lemma nonlinearPeriodIntegrand_continuous {a : ℝ} (a_pos : 0 < a)
    (a_lt_pi : a < Real.pi) :
    Continuous (nonlinearPeriodIntegrand a) := by
  apply Continuous.inv₀
  · fun_prop
  intro u
  exact Real.sqrt_ne_zero'.mpr (nonlinearPeriod_radicand_pos a_pos a_lt_pi u)

lemma one_le_nonlinearPeriodIntegrand {a : ℝ} (a_pos : 0 < a)
    (a_lt_pi : a < Real.pi) (u : ℝ) :
    1 ≤ nonlinearPeriodIntegrand a u := by
  have radicand_nonneg := (nonlinearPeriod_radicand_pos a_pos a_lt_pi u).le
  have radicand_le_one : 1 - (Real.sin (a / 2) * Real.cos u) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin (a / 2) * Real.cos u)]
  have sqrt_le_one : √(1 - (Real.sin (a / 2) * Real.cos u) ^ 2) ≤ 1 := by
    calc
      √(1 - (Real.sin (a / 2) * Real.cos u) ^ 2) ≤ √(1 : ℝ) :=
        Real.sqrt_le_sqrt radicand_le_one
      _ = 1 := Real.sqrt_one
  rw [nonlinearPeriodIntegrand]
  exact (one_le_inv₀ (Real.sqrt_pos.2
    (nonlinearPeriod_radicand_pos a_pos a_lt_pi u))).mpr sqrt_le_one

def pendulumTimeScale (L g : ℝ+) : ℝ :=
  √(L / g)

lemma pendulumTimeScale_pos (L g : ℝ+) :
    0 < pendulumTimeScale L g := by
  exact Real.sqrt_pos.2 (div_pos L.property g.property)

def pendulumTimeMap (L g : ℝ+) (a r : ℝ) : ℝ :=
  pendulumTimeScale L g * ∫ u in 0..r, nonlinearPeriodIntegrand a u

lemma pendulumTimeMap_zero (L g : ℝ+) (a : ℝ) :
    pendulumTimeMap L g a 0 = 0 := by
  simp [pendulumTimeMap]

lemma pendulumTimeMap_hasDerivAt (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (r : ℝ) :
    HasDerivAt (pendulumTimeMap L g a)
      (pendulumTimeScale L g * nonlinearPeriodIntegrand a r) r := by
  let integrand := nonlinearPeriodIntegrand a
  have integrand_continuous : Continuous integrand :=
    nonlinearPeriodIntegrand_continuous a_pos a_lt_pi
  have integral_deriv :
      HasDerivAt (fun s ↦ ∫ u in 0..s, integrand u) (integrand r) r :=
    intervalIntegral.integral_hasDerivAt_right
      (integrand_continuous.intervalIntegrable 0 r)
      (integrand_continuous.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 r))
      integrand_continuous.continuousAt
  change HasDerivAt
    (fun s ↦ pendulumTimeScale L g * ∫ u in 0..s, nonlinearPeriodIntegrand a u)
    (pendulumTimeScale L g * nonlinearPeriodIntegrand a r) r
  exact integral_deriv.const_mul (pendulumTimeScale L g)

lemma pendulumTimeMap_strictMono (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    StrictMono (pendulumTimeMap L g a) := by
  apply strictMono_of_deriv_pos
  intro r
  rw [(pendulumTimeMap_hasDerivAt L g a_pos a_lt_pi r).deriv]
  exact mul_pos (pendulumTimeScale_pos L g)
    (nonlinearPeriodIntegrand_pos a_pos a_lt_pi r)

lemma pendulumTimeMap_continuous (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    Continuous (pendulumTimeMap L g a) :=
  continuous_iff_continuousAt.mpr fun r ↦
    (pendulumTimeMap_hasDerivAt L g a_pos a_lt_pi r).continuousAt

lemma pendulumTimeMap_lower_bound (L g : ℝ+) {a r : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (r_nonneg : 0 ≤ r) :
    pendulumTimeScale L g * r ≤ pendulumTimeMap L g a r := by
  have integral_lower : r ≤ ∫ u in 0..r, nonlinearPeriodIntegrand a u := by
    calc
      r = ∫ _ in 0..r, (1 : ℝ) := by simp
      _ ≤ ∫ u in 0..r, nonlinearPeriodIntegrand a u :=
        intervalIntegral.integral_mono_on r_nonneg
          (continuous_const.intervalIntegrable 0 r)
          ((nonlinearPeriodIntegrand_continuous a_pos a_lt_pi).intervalIntegrable 0 r)
          (fun u _ ↦ one_le_nonlinearPeriodIntegrand a_pos a_lt_pi u)
  exact mul_le_mul_of_nonneg_left integral_lower (pendulumTimeScale_pos L g).le

lemma pendulumTimeMap_upper_bound_of_nonpos (L g : ℝ+) {a r : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (r_nonpos : r ≤ 0) :
    pendulumTimeMap L g a r ≤ pendulumTimeScale L g * r := by
  have integral_lower : -r ≤ ∫ u in r..0, nonlinearPeriodIntegrand a u := by
    calc
      -r = ∫ _ in r..0, (1 : ℝ) := by simp
      _ ≤ ∫ u in r..0, nonlinearPeriodIntegrand a u :=
        intervalIntegral.integral_mono_on r_nonpos
          (continuous_const.intervalIntegrable r 0)
          ((nonlinearPeriodIntegrand_continuous a_pos a_lt_pi).intervalIntegrable r 0)
          (fun u _ ↦ one_le_nonlinearPeriodIntegrand a_pos a_lt_pi u)
  rw [pendulumTimeMap,
    show (∫ u in 0..r, nonlinearPeriodIntegrand a u) =
        -(∫ u in r..0, nonlinearPeriodIntegrand a u) from
      intervalIntegral.integral_symm r 0]
  have scaled_lower := mul_le_mul_of_nonneg_left integral_lower
    (pendulumTimeScale_pos L g).le
  nlinarith

lemma pendulumTimeMap_surjective (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    Function.Surjective (pendulumTimeMap L g a) := by
  intro y
  by_cases y_nonneg : 0 ≤ y
  · let r := y / pendulumTimeScale L g
    have r_nonneg : 0 ≤ r := div_nonneg y_nonneg (pendulumTimeScale_pos L g).le
    have y_le : y ≤ pendulumTimeMap L g a r := by
      calc
        y = pendulumTimeScale L g * r := by
          dsimp only [r]
          field_simp [ne_of_gt (pendulumTimeScale_pos L g)]
        _ ≤ pendulumTimeMap L g a r :=
          pendulumTimeMap_lower_bound L g a_pos a_lt_pi r_nonneg
    obtain ⟨x, _, x_eq⟩ := intermediate_value_Icc r_nonneg
      (pendulumTimeMap_continuous L g a_pos a_lt_pi).continuousOn
      ⟨by simpa [pendulumTimeMap_zero] using y_nonneg, y_le⟩
    exact ⟨x, x_eq⟩
  · have y_neg : y < 0 := lt_of_not_ge y_nonneg
    let r := y / pendulumTimeScale L g
    have r_nonpos : r ≤ 0 := (div_nonpos_of_nonpos_of_nonneg y_neg.le
      (pendulumTimeScale_pos L g).le)
    have map_le_y : pendulumTimeMap L g a r ≤ y := by
      calc
        pendulumTimeMap L g a r ≤ pendulumTimeScale L g * r :=
          pendulumTimeMap_upper_bound_of_nonpos L g a_pos a_lt_pi r_nonpos
        _ = y := by
          dsimp only [r]
          field_simp [ne_of_gt (pendulumTimeScale_pos L g)]
    obtain ⟨x, _, x_eq⟩ := intermediate_value_Icc r_nonpos
      (pendulumTimeMap_continuous L g a_pos a_lt_pi).continuousOn
      ⟨map_le_y, by simpa [pendulumTimeMap_zero] using y_neg.le⟩
    exact ⟨x, x_eq⟩

noncomputable def pendulumTimeOrderIso (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (pendulumTimeMap L g a)
    (pendulumTimeMap_strictMono L g a_pos a_lt_pi)
    (pendulumTimeMap_surjective L g a_pos a_lt_pi)

def pendulumPhaseParameter (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) : ℝ :=
  (pendulumTimeOrderIso L g a_pos a_lt_pi).symm t

lemma pendulumTimeMap_phaseParameter (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    pendulumTimeMap L g a (pendulumPhaseParameter L g a_pos a_lt_pi t) = t :=
  (pendulumTimeOrderIso L g a_pos a_lt_pi).apply_symm_apply t

lemma pendulumPhaseParameter_timeMap (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (r : ℝ) :
    pendulumPhaseParameter L g a_pos a_lt_pi (pendulumTimeMap L g a r) = r :=
  (pendulumTimeOrderIso L g a_pos a_lt_pi).symm_apply_apply r

lemma pendulumPhaseParameter_hasDerivAt (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    let r := pendulumPhaseParameter L g a_pos a_lt_pi t
    HasDerivAt (pendulumPhaseParameter L g a_pos a_lt_pi)
      (√(1 - (Real.sin (a / 2) * Real.cos r) ^ 2) / pendulumTimeScale L g) t := by
  let r := pendulumPhaseParameter L g a_pos a_lt_pi t
  have parameter_continuous :
      ContinuousAt (pendulumPhaseParameter L g a_pos a_lt_pi) t :=
    (pendulumTimeOrderIso L g a_pos a_lt_pi).symm.continuous.continuousAt
  have map_deriv := pendulumTimeMap_hasDerivAt L g a_pos a_lt_pi r
  have derivative_ne_zero :
      pendulumTimeScale L g * nonlinearPeriodIntegrand a r ≠ 0 :=
    ne_of_gt (mul_pos (pendulumTimeScale_pos L g)
      (nonlinearPeriodIntegrand_pos a_pos a_lt_pi r))
  have inverse_deriv :
      HasDerivAt (pendulumPhaseParameter L g a_pos a_lt_pi)
        (pendulumTimeScale L g * nonlinearPeriodIntegrand a r)⁻¹ t :=
    map_deriv.of_local_left_inverse parameter_continuous derivative_ne_zero
      (Filter.Eventually.of_forall fun s ↦
        pendulumTimeMap_phaseParameter L g a_pos a_lt_pi s)
  have radicand_pos := nonlinearPeriod_radicand_pos a_pos a_lt_pi r
  convert inverse_deriv using 1
  dsimp only [r]
  rw [nonlinearPeriodIntegrand]
  field_simp [ne_of_gt (pendulumTimeScale_pos L g),
    Real.sqrt_ne_zero'.mpr radicand_pos]

def positiveAmplitudeAngle (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) : ℝ :=
  2 * Real.arcsin
    (Real.sin (a / 2) * Real.cos (pendulumPhaseParameter L g a_pos a_lt_pi t))

def positiveAmplitudeAngularVelocity (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) : ℝ :=
  (-2 * Real.sin (a / 2) / pendulumTimeScale L g) *
    Real.sin (pendulumPhaseParameter L g a_pos a_lt_pi t)

def positiveAmplitudePhase (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) : ℝ × ℝ :=
  (positiveAmplitudeAngle L g a_pos a_lt_pi t,
    positiveAmplitudeAngularVelocity L g a_pos a_lt_pi t)

lemma positiveAmplitudeAngle_hasDerivAt (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    HasDerivAt (positiveAmplitudeAngle L g a_pos a_lt_pi)
      (positiveAmplitudeAngularVelocity L g a_pos a_lt_pi t) t := by
  let r := pendulumPhaseParameter L g a_pos a_lt_pi t
  let q := Real.sin (a / 2) * Real.cos r
  have radicand_pos : 0 < 1 - q ^ 2 :=
    nonlinearPeriod_radicand_pos a_pos a_lt_pi r
  have q_ne_neg_one : q ≠ -1 := by
    intro q_eq
    rw [q_eq] at radicand_pos
    norm_num at radicand_pos
  have q_ne_one : q ≠ 1 := by
    intro q_eq
    rw [q_eq] at radicand_pos
    norm_num at radicand_pos
  have parameter_deriv := pendulumPhaseParameter_hasDerivAt L g a_pos a_lt_pi t
  change HasDerivAt (pendulumPhaseParameter L g a_pos a_lt_pi)
    (√(1 - q ^ 2) / pendulumTimeScale L g) t at parameter_deriv
  have q_deriv : HasDerivAt
      (fun s ↦ Real.sin (a / 2) *
        Real.cos (pendulumPhaseParameter L g a_pos a_lt_pi s))
      (Real.sin (a / 2) *
        (-Real.sin r * (√(1 - q ^ 2) / pendulumTimeScale L g))) t := by
    exact parameter_deriv.cos.const_mul (Real.sin (a / 2))
  have arcsin_deriv := (Real.hasDerivAt_arcsin q_ne_neg_one q_ne_one).comp t q_deriv
  have doubled_deriv := arcsin_deriv.const_mul 2
  convert doubled_deriv using 1 <;> try rfl
  change (-2 * Real.sin (a / 2) / pendulumTimeScale L g) * Real.sin r =
    2 * ((1 / √(1 - q ^ 2)) *
      (Real.sin (a / 2) *
        (-Real.sin r * (√(1 - q ^ 2) / pendulumTimeScale L g))))
  field_simp [Real.sqrt_ne_zero'.mpr radicand_pos,
    ne_of_gt (pendulumTimeScale_pos L g)]

lemma pendulumTimeScale_sq (L g : ℝ+) :
    pendulumTimeScale L g ^ 2 = L / g := by
  rw [pendulumTimeScale, Real.sq_sqrt (div_nonneg L.property.le g.property.le)]

lemma positiveAmplitudeAngularVelocity_hasDerivAt (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    HasDerivAt (positiveAmplitudeAngularVelocity L g a_pos a_lt_pi)
      (-g / L * Real.sin (positiveAmplitudeAngle L g a_pos a_lt_pi t)) t := by
  let r := pendulumPhaseParameter L g a_pos a_lt_pi t
  let q := Real.sin (a / 2) * Real.cos r
  have radicand_pos : 0 < 1 - q ^ 2 :=
    nonlinearPeriod_radicand_pos a_pos a_lt_pi r
  have parameter_deriv := pendulumPhaseParameter_hasDerivAt L g a_pos a_lt_pi t
  change HasDerivAt (pendulumPhaseParameter L g a_pos a_lt_pi)
    (√(1 - q ^ 2) / pendulumTimeScale L g) t at parameter_deriv
  have sin_deriv := parameter_deriv.sin
  have scaled_deriv := sin_deriv.const_mul
    (-2 * Real.sin (a / 2) / pendulumTimeScale L g)
  convert scaled_deriv using 1 <;> try rfl
  have q_abs_lt_one : |q| < 1 := by
    rw [← abs_one, ← sq_lt_sq]
    linarith
  have q_lower : -1 ≤ q := (abs_lt.mp q_abs_lt_one).1.le
  have q_upper : q ≤ 1 := (abs_lt.mp q_abs_lt_one).2.le
  simp only [positiveAmplitudeAngle]
  change -g.val / L.val * Real.sin (2 * Real.arcsin q) =
    (-2 * Real.sin (a / 2) / pendulumTimeScale L g) *
      (Real.cos r * (√(1 - q ^ 2) / pendulumTimeScale L g))
  rw [Real.sin_two_mul, Real.sin_arcsin q_lower q_upper, Real.cos_arcsin]
  have coefficient_eq : g.val / L.val = 1 / pendulumTimeScale L g ^ 2 := by
    rw [pendulumTimeScale_sq]
    field_simp [ne_of_gt L.property, ne_of_gt g.property]
  have negative_coefficient_eq : -g.val / L.val = -(1 / pendulumTimeScale L g ^ 2) := by
    rw [neg_div, coefficient_eq]
  rw [negative_coefficient_eq]
  dsimp only [q]
  field_simp [ne_of_gt (pendulumTimeScale_pos L g)]

lemma positiveAmplitudePhase_hasDerivAt (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    HasDerivAt (positiveAmplitudePhase L g a_pos a_lt_pi)
      (phaseField
        { pivotMass := 1, bobMass := 1, L := L, g := g, θ0 := 0, ω0 := 0 }
        (positiveAmplitudePhase L g a_pos a_lt_pi t)) t := by
  exact (positiveAmplitudeAngle_hasDerivAt L g a_pos a_lt_pi t).prodMk
    (positiveAmplitudeAngularVelocity_hasDerivAt L g a_pos a_lt_pi t)

lemma pendulumPhaseParameter_zero (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    pendulumPhaseParameter L g a_pos a_lt_pi 0 = 0 := by
  simpa only [pendulumTimeMap_zero] using
    pendulumPhaseParameter_timeMap L g a_pos a_lt_pi 0

lemma positiveAmplitudePhase_zero (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    positiveAmplitudePhase L g a_pos a_lt_pi 0 = (a, 0) := by
  apply Prod.ext
  · change 2 * Real.arcsin
      (Real.sin (a / 2) * Real.cos (pendulumPhaseParameter L g a_pos a_lt_pi 0)) = a
    rw [pendulumPhaseParameter_zero, Real.cos_zero, mul_one,
      Real.arcsin_sin] <;> linarith [Real.pi_pos]
  · change (-2 * Real.sin (a / 2) / pendulumTimeScale L g) *
      Real.sin (pendulumPhaseParameter L g a_pos a_lt_pi 0) = 0
    rw [pendulumPhaseParameter_zero, Real.sin_zero]
    ring

def nonlinearPendulumPeriod (L g : ℝ+) (a : ℝ) : ℝ :=
  pendulumTimeMap L g a (2 * Real.pi)

lemma nonlinearPendulumPeriod_pos (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    0 < nonlinearPendulumPeriod L g a := by
  rw [nonlinearPendulumPeriod, ← pendulumTimeMap_zero L g a]
  exact pendulumTimeMap_strictMono L g a_pos a_lt_pi (mul_pos two_pos Real.pi_pos)

lemma nonlinearPeriodIntegrand_periodic (a : ℝ) :
    Function.Periodic (nonlinearPeriodIntegrand a) (2 * Real.pi) := by
  change Function.Periodic
    ((fun x ↦ (√(1 - (Real.sin (a / 2) * x) ^ 2))⁻¹) ∘ Real.cos)
      (2 * Real.pi)
  exact Real.cos_periodic.comp
    (fun x ↦ (√(1 - (Real.sin (a / 2) * x) ^ 2))⁻¹)

lemma pendulumTimeMap_add_period (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (r : ℝ) :
    pendulumTimeMap L g a (r + 2 * Real.pi) =
      pendulumTimeMap L g a r + nonlinearPendulumPeriod L g a := by
  have integrable (x y : ℝ) :
      IntervalIntegrable (nonlinearPeriodIntegrand a)
        MeasureTheory.volume x y :=
    (nonlinearPeriodIntegrand_continuous a_pos a_lt_pi).intervalIntegrable x y
  have split := intervalIntegral.integral_add_adjacent_intervals
    (integrable 0 r) (integrable r (r + 2 * Real.pi))
  have shifted := (nonlinearPeriodIntegrand_periodic a).intervalIntegral_add_eq r 0
  rw [zero_add] at shifted
  rw [nonlinearPendulumPeriod]
  simp only [pendulumTimeMap]
  rw [← split, shifted]
  ring

lemma pendulumPhaseParameter_add_period (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    pendulumPhaseParameter L g a_pos a_lt_pi (t + nonlinearPendulumPeriod L g a) =
      pendulumPhaseParameter L g a_pos a_lt_pi t + 2 * Real.pi := by
  apply (pendulumTimeMap_strictMono L g a_pos a_lt_pi).injective
  calc
    pendulumTimeMap L g a
        (pendulumPhaseParameter L g a_pos a_lt_pi
          (t + nonlinearPendulumPeriod L g a)) =
        t + nonlinearPendulumPeriod L g a :=
      pendulumTimeMap_phaseParameter L g a_pos a_lt_pi _
    _ = pendulumTimeMap L g a
          (pendulumPhaseParameter L g a_pos a_lt_pi t) +
            nonlinearPendulumPeriod L g a := by
      rw [pendulumTimeMap_phaseParameter]
    _ = pendulumTimeMap L g a
        (pendulumPhaseParameter L g a_pos a_lt_pi t + 2 * Real.pi) :=
      (pendulumTimeMap_add_period L g a_pos a_lt_pi _).symm

lemma positiveAmplitudePhase_periodic (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    Function.Periodic (positiveAmplitudePhase L g a_pos a_lt_pi)
      (nonlinearPendulumPeriod L g a) := by
  intro t
  apply Prod.ext
  · simp only [positiveAmplitudePhase, positiveAmplitudeAngle]
    change 2 * Real.arcsin (Real.sin (a / 2) *
        Real.cos (pendulumPhaseParameter L g a_pos a_lt_pi
          (t + nonlinearPendulumPeriod L g a))) = _
    rw [pendulumPhaseParameter_add_period, Real.cos_add_two_pi]
  · simp only [positiveAmplitudePhase, positiveAmplitudeAngularVelocity]
    change (-2 * Real.sin (a / 2) / pendulumTimeScale L g) *
      Real.sin (pendulumPhaseParameter L g a_pos a_lt_pi
        (t + nonlinearPendulumPeriod L g a)) = _
    rw [pendulumPhaseParameter_add_period, Real.sin_add_two_pi]

lemma phase_eq_positiveAmplitudePhase (params : Params) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi)
    (theta_initial : params.θ0.toReal = a) (angular_velocity_initial : params.ω0 = 0) :
    phase params = positiveAmplitudePhase params.L params.g a_pos a_lt_pi := by
  apply ODE_solution_unique_univ
    (v := fun _ ↦ phaseField params)
    (s := fun _ ↦ Set.univ)
    (K := max 1 ‖(-params.g / params.L : ℝ)‖₊)
    (t₀ := 0)
  · intro _
    exact (phaseField_lipschitz params).lipschitzOnWith
  · intro t
    exact ⟨phase_hasDerivAt params t, Set.mem_univ _⟩
  · intro t
    refine ⟨?_, Set.mem_univ _⟩
    convert positiveAmplitudePhase_hasDerivAt params.L params.g a_pos a_lt_pi t using 1 <;>
      rfl
  · rw [phase_zero, positiveAmplitudePhase_zero, theta_initial, angular_velocity_initial]

def negativeAmplitudePhase (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) : ℝ × ℝ :=
  (-(positiveAmplitudeAngle L g a_pos a_lt_pi t),
    -(positiveAmplitudeAngularVelocity L g a_pos a_lt_pi t))

lemma negativeAmplitudePhase_hasDerivAt (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    HasDerivAt (negativeAmplitudePhase L g a_pos a_lt_pi)
      (phaseField
        { pivotMass := 1, bobMass := 1, L := L, g := g, θ0 := 0, ω0 := 0 }
        (negativeAmplitudePhase L g a_pos a_lt_pi t)) t := by
  have angle_deriv := (positiveAmplitudeAngle_hasDerivAt L g a_pos a_lt_pi t).neg
  have velocity_deriv :=
    (positiveAmplitudeAngularVelocity_hasDerivAt L g a_pos a_lt_pi t).neg
  convert angle_deriv.prodMk velocity_deriv using 1 <;> try rfl
  simp [negativeAmplitudePhase, phaseField, Real.sin_neg]

lemma negativeAmplitudePhase_zero (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    negativeAmplitudePhase L g a_pos a_lt_pi 0 = (-a, 0) := by
  have phase_zero := positiveAmplitudePhase_zero L g a_pos a_lt_pi
  have angle_zero := congrArg Prod.fst phase_zero
  have velocity_zero := congrArg Prod.snd phase_zero
  simp only [positiveAmplitudePhase] at angle_zero velocity_zero
  simp [negativeAmplitudePhase, angle_zero, velocity_zero]

lemma negativeAmplitudePhase_periodic (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    Function.Periodic (negativeAmplitudePhase L g a_pos a_lt_pi)
      (nonlinearPendulumPeriod L g a) := by
  intro t
  have phase_periodic := positiveAmplitudePhase_periodic L g a_pos a_lt_pi t
  have angle_periodic := congrArg Prod.fst phase_periodic
  have velocity_periodic := congrArg Prod.snd phase_periodic
  simp only [positiveAmplitudePhase] at angle_periodic velocity_periodic
  simp only [negativeAmplitudePhase]
  rw [angle_periodic, velocity_periodic]

lemma phase_eq_negativeAmplitudePhase (params : Params) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi)
    (theta_initial : params.θ0.toReal = -a) (angular_velocity_initial : params.ω0 = 0) :
    phase params = negativeAmplitudePhase params.L params.g a_pos a_lt_pi := by
  apply ODE_solution_unique_univ
    (v := fun _ ↦ phaseField params)
    (s := fun _ ↦ Set.univ)
    (K := max 1 ‖(-params.g / params.L : ℝ)‖₊)
    (t₀ := 0)
  · intro _
    exact (phaseField_lipschitz params).lipschitzOnWith
  · intro t
    exact ⟨phase_hasDerivAt params t, Set.mem_univ _⟩
  · intro t
    refine ⟨?_, Set.mem_univ _⟩
    convert negativeAmplitudePhase_hasDerivAt params.L params.g a_pos a_lt_pi t using 1 <;>
      rfl
  · rw [phase_zero, negativeAmplitudePhase_zero, theta_initial, angular_velocity_initial]

def positiveAmplitudePosition (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) : ℝ × ℝ :=
  (Real.sin (positiveAmplitudeAngle L g a_pos a_lt_pi t),
    Real.cos (positiveAmplitudeAngle L g a_pos a_lt_pi t))

lemma positiveAmplitudePosition_periodic (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    Function.Periodic (positiveAmplitudePosition L g a_pos a_lt_pi)
      (nonlinearPendulumPeriod L g a) := by
  intro t
  have phase_periodic := positiveAmplitudePhase_periodic L g a_pos a_lt_pi t
  have angle_periodic := congrArg Prod.fst phase_periodic
  simp only [positiveAmplitudePhase] at angle_periodic
  apply Prod.ext <;> simp only [positiveAmplitudePosition] <;> rw [angle_periodic]

lemma positiveAmplitudeAngle_mem_Ioo (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    positiveAmplitudeAngle L g a_pos a_lt_pi t ∈ Set.Ioo (-Real.pi) Real.pi := by
  let r := pendulumPhaseParameter L g a_pos a_lt_pi t
  let q := Real.sin (a / 2) * Real.cos r
  have radicand_pos : 0 < 1 - q ^ 2 :=
    nonlinearPeriod_radicand_pos a_pos a_lt_pi r
  have q_abs_lt_one : |q| < 1 := by
    rw [← abs_one, ← sq_lt_sq]
    linarith
  change 2 * Real.arcsin q ∈ Set.Ioo (-Real.pi) Real.pi
  constructor
  · have := Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp q_abs_lt_one).1
    linarith
  · have := Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp q_abs_lt_one).2
    linarith

lemma positiveAmplitudePosition_eq_initial_iff (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) (t : ℝ) :
    positiveAmplitudePosition L g a_pos a_lt_pi t =
        positiveAmplitudePosition L g a_pos a_lt_pi 0 ↔
      Real.cos (pendulumPhaseParameter L g a_pos a_lt_pi t) = 1 := by
  let theta := positiveAmplitudeAngle L g a_pos a_lt_pi t
  let r := pendulumPhaseParameter L g a_pos a_lt_pi t
  have initial_angle : positiveAmplitudeAngle L g a_pos a_lt_pi 0 = a :=
    congrArg Prod.fst (positiveAmplitudePhase_zero L g a_pos a_lt_pi)
  constructor
  · intro position_eq
    have sin_eq := congrArg Prod.fst position_eq
    have cos_eq := congrArg Prod.snd position_eq
    change Real.sin theta = Real.sin
      (positiveAmplitudeAngle L g a_pos a_lt_pi 0) at sin_eq
    change Real.cos theta = Real.cos
      (positiveAmplitudeAngle L g a_pos a_lt_pi 0) at cos_eq
    rw [initial_angle] at sin_eq cos_eq
    have cos_sub_eq_one : Real.cos (theta - a) = 1 := by
      rw [Real.cos_sub, sin_eq, cos_eq]
      nlinarith [Real.sin_sq_add_cos_sq a]
    have theta_mem := positiveAmplitudeAngle_mem_Ioo L g a_pos a_lt_pi t
    have theta_eq_a : theta = a := by
      apply sub_eq_zero.mp
      exact (Real.cos_eq_one_iff_of_lt_of_lt
        (by dsimp only [theta]; linarith [theta_mem.1, a_lt_pi])
        (by dsimp only [theta]; linarith [theta_mem.2, a_pos])).mp cos_sub_eq_one
    have q_bounds : -1 ≤ Real.sin (a / 2) * Real.cos r ∧
        Real.sin (a / 2) * Real.cos r ≤ 1 := by
      have radicand_pos := nonlinearPeriod_radicand_pos a_pos a_lt_pi r
      have product_abs_lt_one : |Real.sin (a / 2) * Real.cos r| < 1 := by
        rw [← abs_one, ← sq_lt_sq]
        linarith
      exact ⟨(abs_lt.mp product_abs_lt_one).1.le,
        (abs_lt.mp product_abs_lt_one).2.le⟩
    have sin_argument_eq :
        Real.sin (a / 2) * Real.cos r = Real.sin (a / 2) := by
      have half_angle_eq := congrArg (fun x : ℝ ↦ Real.sin (x / 2)) theta_eq_a
      change Real.sin ((2 * Real.arcsin
        (Real.sin (a / 2) * Real.cos r)) / 2) = Real.sin (a / 2) at half_angle_eq
      rw [show (2 * Real.arcsin (Real.sin (a / 2) * Real.cos r)) / 2 =
        Real.arcsin (Real.sin (a / 2) * Real.cos r) by ring,
        Real.sin_arcsin q_bounds.1 q_bounds.2] at half_angle_eq
      exact half_angle_eq
    apply mul_left_cancel₀ (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (x := a / 2)
      (by linarith) (by linarith [Real.pi_pos])))
    simpa only [mul_one] using sin_argument_eq
  · intro cos_r_eq_one
    have angle_eq : positiveAmplitudeAngle L g a_pos a_lt_pi t = a := by
      change 2 * Real.arcsin (Real.sin (a / 2) * Real.cos r) = a
      rw [cos_r_eq_one, mul_one, Real.arcsin_sin] <;> linarith [Real.pi_pos]
    have initial_angle : positiveAmplitudeAngle L g a_pos a_lt_pi 0 = a :=
      congrArg Prod.fst (positiveAmplitudePhase_zero L g a_pos a_lt_pi)
    apply Prod.ext <;> simp only [positiveAmplitudePosition] <;>
      rw [angle_eq, initial_angle]

lemma positiveAmplitudePosition_isLeast_period (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    IsLeast
      {T > 0 | Function.Periodic (positiveAmplitudePosition L g a_pos a_lt_pi) T}
      (nonlinearPendulumPeriod L g a) := by
  constructor
  · exact ⟨nonlinearPendulumPeriod_pos L g a_pos a_lt_pi,
      positiveAmplitudePosition_periodic L g a_pos a_lt_pi⟩
  · intro T T_mem
    have position_return : positiveAmplitudePosition L g a_pos a_lt_pi T =
        positiveAmplitudePosition L g a_pos a_lt_pi 0 := by
      simpa only [zero_add] using T_mem.2 0
    have cosine_eq_one :=
      (positiveAmplitudePosition_eq_initial_iff L g a_pos a_lt_pi T).mp position_return
    let r := pendulumPhaseParameter L g a_pos a_lt_pi T
    have r_pos : 0 < r := by
      have parameter_mono :=
        (pendulumTimeOrderIso L g a_pos a_lt_pi).symm.strictMono T_mem.1
      change pendulumPhaseParameter L g a_pos a_lt_pi 0 < r at parameter_mono
      rwa [pendulumPhaseParameter_zero] at parameter_mono
    obtain ⟨n, n_eq⟩ := (Real.cos_eq_one_iff r).mp cosine_eq_one
    have n_pos : 0 < n := by
      have n_cast_pos : 0 < (n : ℝ) := by
        have product_pos : 0 < (n : ℝ) * (2 * Real.pi) := by rwa [n_eq]
        exact pos_of_mul_pos_left product_pos (mul_pos two_pos Real.pi_pos).le
      exact_mod_cast n_cast_pos
    have two_pi_le_r : 2 * Real.pi ≤ r := by
      rw [← n_eq]
      have n_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      nlinarith [Real.pi_pos]
    calc
      nonlinearPendulumPeriod L g a = pendulumTimeMap L g a (2 * Real.pi) := rfl
      _ ≤ pendulumTimeMap L g a r :=
        (pendulumTimeMap_strictMono L g a_pos a_lt_pi).monotone two_pi_le_r
      _ = T := pendulumTimeMap_phaseParameter L g a_pos a_lt_pi T

lemma vertical_position_eq (self : Pendulum) (t : Time) :
    (self.bob.pos t).components 1 = -self.L * Real.Angle.cos (self.θ t) := by
  let x := (self.bob.pos t).components 0
  let y := (self.bob.pos t).components 1
  let z := Complex.mk (-y) x
  have radius_eq : Real.sqrt (x ^ 2 + y ^ 2) = self.L := by
    calc
      Real.sqrt (x ^ 2 + y ^ 2) = ‖self.bob.pos t‖ := by
        rw [vector_norm_l2_if_orthonormal self.orthonormal]
        simp only [Fin.sum_univ_two]
        simp [x, y]
      _ = self.L := self.length_constant t
  have z_norm_sq : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    change -y * -y + x * x = x ^ 2 + y ^ 2
    ring
  have z_norm : ‖z‖ = self.L := by
    have radius_sq : x ^ 2 + y ^ 2 = self.L ^ 2 := by
      have := congrArg (fun r : ℝ ↦ r ^ 2) radius_eq
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))] at this
      exact this
    nlinarith [norm_nonneg z, self.L.property]
  have z_ne_zero : z ≠ 0 := by
    intro z_zero
    have := norm_eq_zero.mpr z_zero
    rw [z_norm] at this
    exact ne_of_gt self.L.property this
  change y = -self.L * Real.Angle.cos (Complex.arg z : Real.Angle)
  rw [Real.Angle.cos_coe, Complex.cos_arg z_ne_zero, z_norm]
  change y = -self.L * (-y / self.L)
  field_simp [ne_of_gt self.L.property]

lemma angularVelocity_differentiable (self : Pendulum) :
    Differentiable ℝ self.ω := by
  let x := fun t ↦ (self.bob.pos t).components 0
  let y := fun t ↦ (self.bob.pos t).components 1
  let vx := fun t ↦ (self.bob.vel t).components 0
  let vy := fun t ↦ (self.bob.vel t).components 1
  have position_differentiable : Differentiable ℝ self.bob.1.pos :=
    (self.bob.1.pos_twice_differentiable self.isInertial.out).1
  have velocity_differentiable : Differentiable ℝ self.bob.1.vel := by
    simpa only [ReferenceFrame.Particle.vel] using
      (self.bob.1.pos_twice_differentiable self.isInertial.out).2
  have x_differentiable : Differentiable ℝ x := fun t ↦ by
    exact ((componentCLM (system := self.toSystem) 0).hasFDerivAt.comp t
      (position_differentiable t).hasFDerivAt).differentiableAt
  have y_differentiable : Differentiable ℝ y := fun t ↦ by
    exact ((componentCLM (system := self.toSystem) 1).hasFDerivAt.comp t
      (position_differentiable t).hasFDerivAt).differentiableAt
  have vx_differentiable : Differentiable ℝ vx := fun t ↦ by
    exact ((componentCLM (system := self.toSystem) 0).hasFDerivAt.comp t
      (velocity_differentiable t).hasFDerivAt).differentiableAt
  have vy_differentiable : Differentiable ℝ vy := fun t ↦ by
    exact ((componentCLM (system := self.toSystem) 1).hasFDerivAt.comp t
      (velocity_differentiable t).hasFDerivAt).differentiableAt
  have omega_eq : self.ω = fun t ↦ (x t * vy t - y t * vx t) / self.L ^ 2 := by
    funext t
    exact angular_velocity_eq self t
  rw [omega_eq]
  fun_prop

lemma angularVelocity_hasDerivAt_self (self : Pendulum) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ self.ω (Time.toRealCLE.symm s))
      (-self.g / self.L * Real.Angle.sin (self.θ (Time.toRealCLE.symm t))) t := by
  exact (hasDerivAt_comp_toRealCLE_symm self.ω t
    (angularVelocity_differentiable self (Time.toRealCLE.symm t))).congr_deriv
      (differential_equation self (Time.toRealCLE.symm t))

lemma position_components_sq (self : Pendulum) (t : Time) :
    (self.bob.pos t).components 0 ^ 2 + (self.bob.pos t).components 1 ^ 2 = self.L ^ 2 := by
  have length_eq := self.length_constant t
  rw [vector_norm_l2_if_orthonormal self.orthonormal,
    Fin.sum_univ_two] at length_eq
  have length_sq := congrArg (fun r : ℝ ↦ r ^ 2) length_eq
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at length_sq
  exact length_sq

lemma velocity_components_eq (self : Pendulum) (t : Time) :
    (self.bob.vel t).components 0 = -self.ω t * (self.bob.pos t).components 1 ∧
      (self.bob.vel t).components 1 = self.ω t * (self.bob.pos t).components 0 := by
  let τ := Time.toRealCLE t
  let x := fun s : ℝ ↦ (self.bob.1.pos (Time.toRealCLE.symm s)).components 0
  let y := fun s : ℝ ↦ (self.bob.1.pos (Time.toRealCLE.symm s)).components 1
  let vx := (self.bob.1.vel t).components 0
  let vy := (self.bob.1.vel t).components 1
  have position_deriv : HasDerivAt
      (fun s : ℝ ↦ self.bob.1.pos (Time.toRealCLE.symm s)) (self.bob.1.vel t) τ := by
    simpa only [τ, ContinuousLinearEquiv.symm_apply_apply,
      ReferenceFrame.Particle.vel] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.pos τ
        (self.bob.1.pos_twice_differentiable self.isInertial.out).1.differentiableAt
  have x_deriv : HasDerivAt x vx τ := by
    convert (componentCLM (system := self.toSystem) 0).hasFDerivAt.comp_hasDerivAt τ
      position_deriv using 1 <;> rfl
  have y_deriv : HasDerivAt y vy τ := by
    convert (componentCLM (system := self.toSystem) 1).hasFDerivAt.comp_hasDerivAt τ
      position_deriv using 1 <;> rfl
  have radius_deriv := (x_deriv.mul x_deriv).add (y_deriv.mul y_deriv)
  have radius_eq : (fun s ↦ x s * x s + y s * y s) =
      fun _ ↦ self.L.val ^ 2 := by
    funext s
    simpa only [pow_two, PointParticle.System.Particle.pos, x, y] using
      position_components_sq self (Time.toRealCLE.symm s)
  have radius_deriv_zero : 2 * x τ * vx + 2 * y τ * vy = 0 := by
    have constant_deriv : HasDerivAt (fun _ : ℝ ↦ self.L.val ^ 2) 0 τ :=
      hasDerivAt_const τ _
    have transferred := radius_deriv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦ (congrFun radius_eq s).symm)
    have derivatives_eq := transferred.unique constant_deriv
    nlinarith
  have dot_eq : x τ * vx + y τ * vy = 0 := by linarith
  have cross_eq : x τ * vy - y τ * vx = self.L ^ 2 * self.ω t := by
    have omega_eq := angular_velocity_eq self t
    change self.ω t = (x τ * vy - y τ * vx) / self.L ^ 2 at omega_eq
    field_simp [ne_of_gt self.L.property] at omega_eq
    nlinarith
  have radius_sq := position_components_sq self t
  change x τ ^ 2 + y τ ^ 2 = self.L ^ 2 at radius_sq
  change vx = -self.ω t * y τ ∧ vy = self.ω t * x τ
  constructor
  · apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt self.L.property))
    calc
      self.L ^ 2 * vx = (x τ ^ 2 + y τ ^ 2) * vx := by rw [radius_sq]
      _ = x τ * (x τ * vx + y τ * vy) - y τ * (x τ * vy - y τ * vx) := by ring
      _ = self.L ^ 2 * (-self.ω t * y τ) := by rw [dot_eq, cross_eq]; ring
  · apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt self.L.property))
    calc
      self.L ^ 2 * vy = (x τ ^ 2 + y τ ^ 2) * vy := by rw [radius_sq]
      _ = y τ * (x τ * vx + y τ * vy) + x τ * (x τ * vy - y τ * vx) := by ring
      _ = self.L ^ 2 * (self.ω t * x τ) := by rw [dot_eq, cross_eq]; ring

def circlePhaseField (L g : ℝ+) (state : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  ((state.2 * state.1.2, -state.2 * state.1.1), -g / L * state.1.1)

def paramsCirclePhase (params : Params) (t : ℝ) : (ℝ × ℝ) × ℝ :=
  ((Real.sin (angle params t), Real.cos (angle params t)), angularVelocity params t)

def pendulumCirclePhase (self : Pendulum) (t : ℝ) : (ℝ × ℝ) × ℝ :=
  (((self.bob.pos (Time.toRealCLE.symm t)).components 0 / self.L,
      -(self.bob.pos (Time.toRealCLE.symm t)).components 1 / self.L),
    self.ω (Time.toRealCLE.symm t))

lemma paramsCirclePhase_hasDerivAt (params : Params) (t : ℝ) :
    HasDerivAt (paramsCirclePhase params)
      (circlePhaseField params.L params.g (paramsCirclePhase params t)) t := by
  have x_deriv := (angle_hasDerivAt params t).sin
  have y_deriv := (angle_hasDerivAt params t).cos
  have omega_deriv := angularVelocity_hasDerivAt params t
  convert (x_deriv.prodMk y_deriv).prodMk omega_deriv using 1 <;> try rfl
  simp [paramsCirclePhase, circlePhaseField]
  constructor <;> ring

lemma pendulumCirclePhase_hasDerivAt (self : Pendulum) (t : ℝ) :
    HasDerivAt (pendulumCirclePhase self)
      (circlePhaseField self.L self.g (pendulumCirclePhase self t)) t := by
  have position_deriv : HasDerivAt
      (fun s : ℝ ↦ self.bob.1.pos (Time.toRealCLE.symm s))
      (self.bob.1.vel (Time.toRealCLE.symm t)) t := by
    simpa only [ReferenceFrame.Particle.vel] using
      hasDerivAt_comp_toRealCLE_symm self.bob.1.pos t
        (self.bob.1.pos_twice_differentiable self.isInertial.out).1.differentiableAt
  have x_deriv : HasDerivAt
      (fun s : ℝ ↦ (self.bob.pos (Time.toRealCLE.symm s)).components 0)
      ((self.bob.vel (Time.toRealCLE.symm t)).components 0) t := by
    convert (componentCLM (system := self.toSystem) 0).hasFDerivAt.comp_hasDerivAt t
      position_deriv using 1 <;> rfl
  have y_deriv : HasDerivAt
      (fun s : ℝ ↦ (self.bob.pos (Time.toRealCLE.symm s)).components 1)
      ((self.bob.vel (Time.toRealCLE.symm t)).components 1) t := by
    convert (componentCLM (system := self.toSystem) 1).hasFDerivAt.comp_hasDerivAt t
      position_deriv using 1 <;> rfl
  have velocity_eq := velocity_components_eq self (Time.toRealCLE.symm t)
  have normalized_x_deriv := x_deriv.div_const self.L.val
  have normalized_y_deriv := y_deriv.neg.div_const self.L.val
  have omega_deriv := angularVelocity_hasDerivAt_self self t
  have normalized_x_deriv' : HasDerivAt
      (fun s : ℝ ↦ (self.bob.pos (Time.toRealCLE.symm s)).components 0 / self.L.val)
      (self.ω (Time.toRealCLE.symm t) *
        (-(self.bob.pos (Time.toRealCLE.symm t)).components 1 / self.L.val)) t := by
    apply normalized_x_deriv.congr_deriv
    rw [velocity_eq.1]
    ring
  have normalized_y_deriv' : HasDerivAt
      (fun s : ℝ ↦ -(self.bob.pos (Time.toRealCLE.symm s)).components 1 / self.L.val)
      (-self.ω (Time.toRealCLE.symm t) *
        ((self.bob.pos (Time.toRealCLE.symm t)).components 0 / self.L.val)) t := by
    apply normalized_y_deriv.congr_deriv
    rw [velocity_eq.2]
    ring
  have omega_deriv' : HasDerivAt
      (fun s : ℝ ↦ self.ω (Time.toRealCLE.symm s))
      (-self.g / self.L *
        ((self.bob.pos (Time.toRealCLE.symm t)).components 0 / self.L.val)) t := by
    apply omega_deriv.congr_deriv
    rw [horizontal_position_eq self (Time.toRealCLE.symm t)]
    field_simp [ne_of_gt self.L.property]
  convert (normalized_x_deriv'.prodMk normalized_y_deriv').prodMk omega_deriv' using 1 <;>
    try rfl

lemma pendulumCirclePhase_zero (self : Pendulum) :
    pendulumCirclePhase self 0 = paramsCirclePhase self.params 0 := by
  have time_zero : Time.toRealCLE.symm (0 : ℝ) = (0 : Time) :=
    map_zero Time.toRealCLE.symm
  have canonical_zero := phase_zero self.params
  have canonical_angle_zero := congrArg Prod.fst canonical_zero
  have canonical_velocity_zero := congrArg Prod.snd canonical_zero
  change angle self.params 0 = self.params.θ0.toReal at canonical_angle_zero
  change angularVelocity self.params 0 = self.params.ω0 at canonical_velocity_zero
  simp only [pendulumCirclePhase, paramsCirclePhase, time_zero]
  apply Prod.ext
  · apply Prod.ext
    · change (self.bob.pos 0).components 0 / self.L = Real.sin (angle self.params 0)
      rw [horizontal_position_eq, canonical_angle_zero]
      change self.L.val * Real.Angle.sin (self.params.θ0) / self.L.val =
        Real.sin self.params.θ0.toReal
      rw [← Real.Angle.sin_coe, Real.Angle.coe_toReal]
      field_simp [ne_of_gt self.L.property]
    · change -(self.bob.pos 0).components 1 / self.L = Real.cos (angle self.params 0)
      rw [vertical_position_eq, canonical_angle_zero]
      change -(-self.L.val * Real.Angle.cos (self.params.θ0)) / self.L.val =
        Real.cos self.params.θ0.toReal
      rw [← Real.Angle.cos_coe, Real.Angle.coe_toReal]
      field_simp [ne_of_gt self.L.property]
  · change self.ω 0 = angularVelocity self.params 0
    rw [canonical_velocity_zero]
    rfl

lemma circlePhaseField_contDiff (L g : ℝ+) :
    ContDiff ℝ 1 (circlePhaseField L g) := by
  unfold circlePhaseField
  fun_prop

lemma pendulumCirclePhase_eq_paramsCirclePhase (self : Pendulum) :
    pendulumCirclePhase self = paramsCirclePhase self.params := by
  funext t
  let leftEndpoint := min t 0 - 1
  let rightEndpoint := max t 0 + 1
  have zero_mem : (0 : ℝ) ∈ Set.Ioo leftEndpoint rightEndpoint := by
    dsimp only [leftEndpoint, rightEndpoint]
    constructor <;> linarith [min_le_right t 0, le_max_right t 0]
  have t_mem : t ∈ Set.Icc leftEndpoint rightEndpoint := by
    dsimp only [leftEndpoint, rightEndpoint]
    constructor <;> linarith [min_le_left t 0, le_max_left t 0]
  have self_continuous : Continuous (pendulumCirclePhase self) :=
    continuous_iff_continuousAt.mpr fun s ↦
      (pendulumCirclePhase_hasDerivAt self s).continuousAt
  have params_continuous : Continuous (paramsCirclePhase self.params) :=
    continuous_iff_continuousAt.mpr fun s ↦
      (paramsCirclePhase_hasDerivAt self.params s).continuousAt
  let states := pendulumCirclePhase self '' Set.Icc leftEndpoint rightEndpoint ∪
    paramsCirclePhase self.params '' Set.Icc leftEndpoint rightEndpoint
  have states_compact : IsCompact states :=
    (isCompact_Icc.image self_continuous).union
      (isCompact_Icc.image params_continuous)
  obtain ⟨radius, states_subset⟩ :=
    states_compact.isBounded.subset_closedBall (0 : (ℝ × ℝ) × ℝ)
  have field_contDiffOn : ContDiffOn ℝ 1 (circlePhaseField self.L self.g)
      (Metric.closedBall (0 : (ℝ × ℝ) × ℝ) radius) :=
    (circlePhaseField_contDiff self.L self.g).contDiffOn
  obtain ⟨K, field_lipschitz⟩ := field_contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : (ℝ × ℝ) × ℝ) radius)
    (isCompact_closedBall (0 : (ℝ × ℝ) × ℝ) radius)
  apply ODE_solution_unique_of_mem_Icc
    (v := fun _ ↦ circlePhaseField self.L self.g)
    (s := fun _ ↦ Metric.closedBall (0 : (ℝ × ℝ) × ℝ) radius)
    (K := K)
    (t₀ := 0)
  · intro _ _
    exact field_lipschitz
  · exact zero_mem
  · exact self_continuous.continuousOn
  · intro s _
    exact pendulumCirclePhase_hasDerivAt self s
  · intro s s_mem
    apply states_subset
    left
    exact ⟨s, Set.Ioo_subset_Icc_self s_mem, rfl⟩
  · exact params_continuous.continuousOn
  · intro s _
    exact paramsCirclePhase_hasDerivAt self.params s
  · intro s s_mem
    apply states_subset
    right
    exact ⟨s, Set.Ioo_subset_Icc_self s_mem, rfl⟩
  · exact pendulumCirclePhase_zero self
  · exact t_mem

lemma bobPosition_components_eq_params (self : Pendulum) (t : Time) :
    (self.bob.pos t).components 0 =
        self.L * Real.sin (angle self.params t.val) ∧
      (self.bob.pos t).components 1 =
        -self.L * Real.cos (angle self.params t.val) := by
  have phase_eq := congrFun (pendulumCirclePhase_eq_paramsCirclePhase self) t.val
  have x_eq := congrArg (fun state : (ℝ × ℝ) × ℝ ↦ state.1.1) phase_eq
  have y_eq := congrArg (fun state : (ℝ × ℝ) × ℝ ↦ state.1.2) phase_eq
  change (self.bob.pos t).components 0 / self.L = Real.sin (angle self.params t.val) at x_eq
  change -(self.bob.pos t).components 1 / self.L = Real.cos (angle self.params t.val) at y_eq
  constructor
  · field_simp [ne_of_gt self.L.property] at x_eq ⊢
    exact x_eq
  · field_simp [ne_of_gt self.L.property] at y_eq ⊢
    linarith

lemma bobPosition_periodic_iff_paramsPosition (self : Pendulum) (T : ℝ) :
    Function.Periodic self.bob.pos T ↔
      Function.Periodic
        (fun t ↦ (Real.sin (angle self.params t), Real.cos (angle self.params t))) T := by
  constructor
  · intro position_periodic t
    have position_eq := position_periodic t
    apply Prod.ext
    · have component_eq := congrArg (fun v ↦ v.components 0) position_eq
      rw [(bobPosition_components_eq_params self ((t : Time) + (T : Time))).1,
        (bobPosition_components_eq_params self (t : Time)).1] at component_eq
      exact mul_left_cancel₀ (ne_of_gt self.L.property) component_eq
    · have component_eq := congrArg (fun v ↦ v.components 1) position_eq
      rw [(bobPosition_components_eq_params self ((t : Time) + (T : Time))).2,
        (bobPosition_components_eq_params self (t : Time)).2] at component_eq
      have component_eq' :
          -self.L.val * Real.cos (angle self.params (t + T)) =
            -self.L.val * Real.cos (angle self.params t) := by
        simpa only [Time.add_val] using component_eq
      apply mul_left_cancel₀ (ne_of_gt self.L.property)
      calc
        self.L.val * Real.cos (angle self.params (t + T)) =
            -(-self.L.val * Real.cos (angle self.params (t + T))) := by ring
        _ = -(-self.L.val * Real.cos (angle self.params t)) := by rw [component_eq']
        _ = self.L.val * Real.cos (angle self.params t) := by ring
  · intro params_periodic t
    apply vector_eq_of_components
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) j) i
    · rw [(bobPosition_components_eq_params self (t + (T : Time))).1,
        (bobPosition_components_eq_params self t).1]
      exact congrArg (fun position : ℝ × ℝ ↦ self.L.val * position.1)
        (params_periodic t)
    · change (self.bob.pos (t + T)).components 1 = (self.bob.pos t).components 1
      rw [(bobPosition_components_eq_params self (t + (T : Time))).2,
        (bobPosition_components_eq_params self t).2]
      exact congrArg (fun position : ℝ × ℝ ↦ -self.L.val * position.2)
        (params_periodic t)

def reflectPosition (position : ℝ × ℝ) : ℝ × ℝ :=
  (-position.1, position.2)

lemma reflectPosition_involutive : Function.Involutive reflectPosition := by
  intro position
  rcases position with ⟨x, y⟩
  simp [reflectPosition]

lemma periodic_reflectPosition_iff (position : ℝ → ℝ × ℝ) (T : ℝ) :
    Function.Periodic (reflectPosition ∘ position) T ↔ Function.Periodic position T := by
  constructor
  · intro reflected_periodic t
    have := congrArg reflectPosition (reflected_periodic t)
    simpa only [Function.comp_apply, reflectPosition_involutive _] using this
  · intro position_periodic
    exact position_periodic.comp reflectPosition

lemma paramsPosition_eq_positiveAmplitudePosition (params : Params) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi)
    (theta_initial : params.θ0.toReal = a) (angular_velocity_initial : params.ω0 = 0) :
    (fun t ↦ (Real.sin (angle params t), Real.cos (angle params t))) =
      positiveAmplitudePosition params.L params.g a_pos a_lt_pi := by
  have phase_eq := phase_eq_positiveAmplitudePhase params a_pos a_lt_pi
    theta_initial angular_velocity_initial
  funext t
  have angle_eq := congrArg Prod.fst (congrFun phase_eq t)
  simp only [positiveAmplitudePhase] at angle_eq
  change angle params t = positiveAmplitudeAngle params.L params.g a_pos a_lt_pi t at angle_eq
  apply Prod.ext <;> simp only [positiveAmplitudePosition] <;> rw [angle_eq]

lemma paramsPosition_eq_reflectedPositiveAmplitudePosition (params : Params) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi)
    (theta_initial : params.θ0.toReal = -a) (angular_velocity_initial : params.ω0 = 0) :
    (fun t ↦ (Real.sin (angle params t), Real.cos (angle params t))) =
      reflectPosition ∘ positiveAmplitudePosition params.L params.g a_pos a_lt_pi := by
  have phase_eq := phase_eq_negativeAmplitudePhase params a_pos a_lt_pi
    theta_initial angular_velocity_initial
  funext t
  have angle_eq := congrArg Prod.fst (congrFun phase_eq t)
  simp only [negativeAmplitudePhase] at angle_eq
  change angle params t = -positiveAmplitudeAngle params.L params.g a_pos a_lt_pi t at angle_eq
  apply Prod.ext <;> simp only [Function.comp_apply, positiveAmplitudePosition, reflectPosition]
  · rw [angle_eq, Real.sin_neg]
  · rw [angle_eq, Real.cos_neg]

lemma pendulum_period_eq_nonlinearPendulumPeriod (self : Pendulum)
    (angular_velocity_initial : self.params.ω0 = 0)
    (theta_initial_ne_zero : self.params.θ0.toReal ≠ 0)
    (theta_initial_abs_lt_pi : |self.params.θ0.toReal| < Real.pi) :
    self.period = some
      (nonlinearPendulumPeriod self.L self.g |self.params.θ0.toReal|) := by
  let a := |self.params.θ0.toReal|
  have a_pos : 0 < a := abs_pos.mpr theta_initial_ne_zero
  have a_lt_pi : a < Real.pi := theta_initial_abs_lt_pi
  have params_L : self.params.L = self.L := rfl
  have params_g : self.params.g = self.g := rfl
  have physical_periods_eq_positive :
      {T : ℝ | T > 0 ∧ Function.Periodic self.bob.pos (T : Time)} =
        {T : ℝ | T > 0 ∧ Function.Periodic
          (positiveAmplitudePosition self.L self.g a_pos a_lt_pi) T} := by
    ext T
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    intro _
    rw [bobPosition_periodic_iff_paramsPosition]
    by_cases theta_initial_pos : 0 < self.params.θ0.toReal
    · have theta_initial_eq : self.params.θ0.toReal = a := by
        dsimp only [a]
        rw [abs_of_pos theta_initial_pos]
      have position_eq := paramsPosition_eq_positiveAmplitudePosition self.params
        a_pos a_lt_pi theta_initial_eq angular_velocity_initial
      simp only [params_L, params_g, position_eq]
    · have theta_initial_neg : self.params.θ0.toReal < 0 :=
        lt_of_le_of_ne (le_of_not_gt theta_initial_pos) theta_initial_ne_zero
      have theta_initial_eq : self.params.θ0.toReal = -a := by
        dsimp only [a]
        rw [abs_of_neg theta_initial_neg]
        ring
      have position_eq := paramsPosition_eq_reflectedPositiveAmplitudePosition self.params
        a_pos a_lt_pi theta_initial_eq angular_velocity_initial
      rw [position_eq, params_L, params_g, periodic_reflectPosition_iff]
  have least_period : IsLeast
      {T : ℝ | T > 0 ∧ Function.Periodic self.bob.pos (T : Time)}
      (nonlinearPendulumPeriod self.L self.g a) := by
    rw [physical_periods_eq_positive]
    exact positiveAmplitudePosition_isLeast_period self.L self.g a_pos a_lt_pi
  rw [Pendulum.period, dif_pos ⟨_, least_period⟩]
  congr 1
  exact IsLeast.unique (Classical.choose_spec ⟨_, least_period⟩) least_period

lemma nonlinearPeriodIntegrand_le {a : ℝ} (a_pos : 0 < a)
    (a_lt_pi : a < Real.pi) (u : ℝ) :
    nonlinearPeriodIntegrand a u ≤
      (√(1 - Real.sin (a / 2) ^ 2))⁻¹ := by
  have base_radicand_pos : 0 < 1 - Real.sin (a / 2) ^ 2 := by
    simpa using nonlinearPeriod_radicand_pos a_pos a_lt_pi 0
  have cos_sq_le_one : Real.cos u ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have product_sq_le :
      (Real.sin (a / 2) * Real.cos u) ^ 2 ≤ Real.sin (a / 2) ^ 2 := by
    calc
      (Real.sin (a / 2) * Real.cos u) ^ 2 =
          Real.sin (a / 2) ^ 2 * Real.cos u ^ 2 := by ring
      _ ≤ Real.sin (a / 2) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left cos_sq_le_one (sq_nonneg _)
      _ = Real.sin (a / 2) ^ 2 := mul_one _
  have sqrt_le : √(1 - Real.sin (a / 2) ^ 2) ≤
      √(1 - (Real.sin (a / 2) * Real.cos u) ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [nonlinearPeriodIntegrand]
  exact (inv_le_inv₀
    (Real.sqrt_pos.2 (nonlinearPeriod_radicand_pos a_pos a_lt_pi u))
    (Real.sqrt_pos.2 base_radicand_pos)).mpr sqrt_le

lemma nonlinearPendulumPeriod_lower_bound (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    2 * Real.pi * pendulumTimeScale L g ≤ nonlinearPendulumPeriod L g a := by
  rw [nonlinearPendulumPeriod]
  have lower := pendulumTimeMap_lower_bound L g a_pos a_lt_pi
    (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

lemma nonlinearPendulumPeriod_upper_bound (L g : ℝ+) {a : ℝ}
    (a_pos : 0 < a) (a_lt_pi : a < Real.pi) :
    nonlinearPendulumPeriod L g a ≤
      2 * Real.pi * pendulumTimeScale L g *
        (√(1 - Real.sin (a / 2) ^ 2))⁻¹ := by
  have integrand_continuous := nonlinearPeriodIntegrand_continuous a_pos a_lt_pi
  have integral_upper :
      (∫ u in 0..2 * Real.pi, nonlinearPeriodIntegrand a u) ≤
        ∫ _ in 0..2 * Real.pi, (√(1 - Real.sin (a / 2) ^ 2))⁻¹ :=
    intervalIntegral.integral_mono_on (by positivity)
      (integrand_continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun u _ ↦ nonlinearPeriodIntegrand_le a_pos a_lt_pi u)
  rw [intervalIntegral.integral_const] at integral_upper
  simp only [sub_zero, smul_eq_mul] at integral_upper
  rw [nonlinearPendulumPeriod, pendulumTimeMap]
  have scale_nonneg := (pendulumTimeScale_pos L g).le
  nlinarith

lemma nonlinearPendulumPeriod_tendsto_zero (L g : ℝ+) :
    Filter.Tendsto (nonlinearPendulumPeriod L g)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi * pendulumTimeScale L g)) := by
  let upper := fun a : ℝ ↦ 2 * Real.pi * pendulumTimeScale L g *
    (√(1 - Real.sin (a / 2) ^ 2))⁻¹
  have upper_continuous : ContinuousAt upper 0 := by
    have argument_continuous : Continuous (fun a : ℝ ↦ 1 - Real.sin (a / 2) ^ 2) :=
      continuous_const.sub ((Real.continuous_sin.comp (continuous_id.div_const 2)).pow 2)
    have denominator_continuous : ContinuousAt
        (fun a : ℝ ↦ √(1 - Real.sin (a / 2) ^ 2)) 0 :=
      Real.continuous_sqrt.continuousAt.comp argument_continuous.continuousAt
    exact continuousAt_const.mul (denominator_continuous.inv₀ (by norm_num))
  have upper_zero : upper 0 = 2 * Real.pi * pendulumTimeScale L g := by
    simp [upper]
  have upper_tendsto : Filter.Tendsto upper (𝓝[>] 0)
      (𝓝 (2 * Real.pi * pendulumTimeScale L g)) := by
    rw [← upper_zero]
    exact upper_continuous.mono_left inf_le_left
  have eventually_lt_pi : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < Real.pi :=
    (show ∀ᶠ a in 𝓝 (0 : ℝ), a < Real.pi by
      filter_upwards [Iio_mem_nhds Real.pi_pos] with a a_lt_pi
      exact a_lt_pi).filter_mono nhdsWithin_le_nhds
  apply tendsto_const_nhds.squeeze' upper_tendsto
  · filter_upwards [self_mem_nhdsWithin, eventually_lt_pi] with a a_pos a_lt_pi
    exact nonlinearPendulumPeriod_lower_bound L g a_pos a_lt_pi
  · filter_upwards [self_mem_nhdsWithin, eventually_lt_pi] with a a_pos a_lt_pi
    exact nonlinearPendulumPeriod_upper_bound L g a_pos a_lt_pi

lemma continuousAt_angleToReal_zero :
    ContinuousAt Real.Angle.toReal 0 := by
  let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos two_pos Real.pi_pos⟩
  have toReal_eq : Real.Angle.toReal =
      fun theta : Real.Angle ↦ ((AddCircle.equivIoc (2 * Real.pi) (-Real.pi)) theta).1 := by
    funext theta
    induction theta using Real.Angle.induction_on
    rfl
  rw [toReal_eq]
  apply continuous_subtype_val.continuousAt.comp
  apply AddCircle.continuousAt_equivIoc
  change (0 : Real.Angle) ≠ ((-Real.pi : ℝ) : Real.Angle)
  simpa only [Real.Angle.coe_neg, Real.Angle.neg_coe_pi] using
    Real.Angle.pi_ne_zero.symm

lemma angleAmplitude_tendsto_zero :
    Filter.Tendsto (fun theta : Real.Angle ↦ |theta.toReal|)
      (𝓝[≠] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have amplitude_continuous : ContinuousAt
        (fun theta : Real.Angle ↦ |theta.toReal|) 0 :=
      (show Continuous (fun x : ℝ ↦ |x|) from continuous_abs).continuousAt.comp
        continuousAt_angleToReal_zero
    simpa only [Real.Angle.toReal_zero, abs_zero] using
      amplitude_continuous.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with theta theta_ne_zero
    exact abs_pos.mpr (Real.Angle.toReal_eq_zero_iff.not.mpr theta_ne_zero)

lemma nonlinearPendulumPeriod_angle_tendsto_zero (L g : ℝ+) :
    Filter.Tendsto
      (fun theta : Real.Angle ↦ nonlinearPendulumPeriod L g |theta.toReal|)
      (𝓝[≠] 0)
      (𝓝 (2 * Real.pi * √(L / g))) := by
  change Filter.Tendsto
    (nonlinearPendulumPeriod L g ∘ fun theta : Real.Angle ↦ |theta.toReal|)
    (𝓝[≠] 0) (𝓝 (2 * Real.pi * pendulumTimeScale L g))
  exact (nonlinearPendulumPeriod_tendsto_zero L g).comp angleAmplitude_tendsto_zero

lemma chosenPendulum_period_eventuallyEq (params : Params)
    (angular_velocity_initial : params.ω0 = 0)
    (make : Params → Pendulum) (make_params : ∀ p, (make p).params = p) :
    (fun theta ↦ (make { params with θ0 := theta }).period) =ᶠ[𝓝[≠] 0]
      fun theta ↦ some
        (nonlinearPendulumPeriod params.L params.g |theta.toReal|) := by
  have eventually_lt_pi : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < Real.pi :=
    (show ∀ᶠ a in 𝓝 (0 : ℝ), a < Real.pi by
      filter_upwards [Iio_mem_nhds Real.pi_pos] with a a_lt_pi
      exact a_lt_pi).filter_mono nhdsWithin_le_nhds
  have amplitude_lt_pi : ∀ᶠ theta : Real.Angle in 𝓝[≠] 0,
      |theta.toReal| < Real.pi :=
    angleAmplitude_tendsto_zero.eventually eventually_lt_pi
  filter_upwards [self_mem_nhdsWithin, amplitude_lt_pi] with theta theta_ne_zero theta_lt_pi
  let p := { params with θ0 := theta }
  have selected_params := make_params p
  have selected_angular_velocity : (make p).params.ω0 = 0 := by
    rw [selected_params]
    exact angular_velocity_initial
  have selected_theta_ne_zero : (make p).params.θ0.toReal ≠ 0 := by
    rw [selected_params]
    exact Real.Angle.toReal_eq_zero_iff.not.mpr theta_ne_zero
  have selected_theta_lt_pi : |(make p).params.θ0.toReal| < Real.pi := by
    rwa [selected_params]
  have period_eq := pendulum_period_eq_nonlinearPendulumPeriod (make p)
    selected_angular_velocity selected_theta_ne_zero selected_theta_lt_pi
  have length_eq := congrArg Params.L selected_params
  have gravity_eq := congrArg Params.g selected_params
  have theta_eq := congrArg Params.θ0 selected_params
  change (make p).L = params.L at length_eq
  change (make p).g = params.g at gravity_eq
  change (make p).params.θ0 = theta at theta_eq
  rw [period_eq, length_eq, gravity_eq, theta_eq]

lemma small_angle_period
    [EMetricSpace (Option ℝ)]
    (option_edist_some : ∀ x y : ℝ, edist (some x) (some y) = edist x y)
    (params : Params) (angular_velocity_initial : params.ω0 = 0) :
    Filter.Tendsto
      (fun theta ↦ (make { params with θ0 := theta }).period)
      (𝓝[≠] 0)
      (𝓝 <| some <| 2 * Real.pi * √(params.L / params.g)) := by
  have period_eventually := chosenPendulum_period_eventuallyEq params
    angular_velocity_initial make make_params
  have value_tendsto := nonlinearPendulumPeriod_angle_tendsto_zero params.L params.g
  apply EMetric.tendsto_nhds.mpr
  intro epsilon epsilon_pos
  have value_eventually := EMetric.tendsto_nhds.mp value_tendsto epsilon epsilon_pos
  filter_upwards [period_eventually, value_eventually] with theta period_eq value_close
  rw [period_eq, option_edist_some]
  exact value_close

end

end ClassicalMechanics.Pendulum.Internal
