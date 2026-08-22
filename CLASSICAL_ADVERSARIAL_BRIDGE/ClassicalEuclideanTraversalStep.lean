import ClassicalEuclideanGregoryBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PiQuasiClassicalBridge

noncomputable section


/- ============================================================
   I. EXACT REAL EMBEDDING OF THE GREGORY NEXT CORRECTION
   ============================================================ -/

def gregoryCorrectionR
    (n : ℕ) :
    ℝ :=

  ((-1 : ℝ) ^ (n + 1) * 4)
  /
  (2 * (n : ℝ) + 3)


def traversalAngleStep
    (n : ℕ) :
    ℝ :=

  2 * gregoryCorrectionR n


theorem gregory_correction_denominator_pos
    (n : ℕ) :

    0 < 2 * (n : ℝ) + 3 := by

  positivity


theorem gregory_correction_nonzero
    (n : ℕ) :

    gregoryCorrectionR n ≠ 0 := by

  unfold gregoryCorrectionR

  have hpow :
      ((-1 : ℝ) ^ (n + 1)) ≠ 0 := by

    exact pow_ne_zero _ (by norm_num)

  have hnum :
      ((-1 : ℝ) ^ (n + 1) * 4) ≠ 0 := by

    exact mul_ne_zero hpow (by norm_num)

  have hden :
      (2 * (n : ℝ) + 3) ≠ 0 := by

    positivity

  exact div_ne_zero hnum hden


theorem traversal_angle_step_nonzero
    (n : ℕ) :

    traversalAngleStep n ≠ 0 := by

  unfold traversalAngleStep

  exact
    mul_ne_zero
      (by norm_num)
      (gregory_correction_nonzero n)


/- ============================================================
   II. MAGNITUDE OF THE ANGULAR CORRECTION
   ============================================================ -/

theorem abs_gregory_correction
    (n : ℕ) :

    |gregoryCorrectionR n|
    =
    4 / (2 * (n : ℝ) + 3) := by

  unfold gregoryCorrectionR

  have hden :
      0 < 2 * (n : ℝ) + 3 := by

    positivity

  rw [abs_div, abs_mul, abs_pow]

  norm_num [abs_of_pos hden]


theorem abs_traversal_angle_step
    (n : ℕ) :

    |traversalAngleStep n|
    =
    8 / (2 * (n : ℝ) + 3) := by

  unfold traversalAngleStep

  rw [abs_mul, abs_gregory_correction]

  ring


theorem traversal_angle_step_abs_le_eight_thirds
    (n : ℕ) :

    |traversalAngleStep n|
    ≤
    (8 : ℝ) / 3 := by

  rw [abs_traversal_angle_step]

  have hd :
      0 < 2 * (n : ℝ) + 3 := by

    positivity

  have h3 :
      (0 : ℝ) < 3 := by

    norm_num

  have hn :
      (0 : ℝ) ≤ (n : ℝ) := by

    positivity

  rw [div_le_div_iff₀ hd h3]

  nlinarith


theorem eight_thirds_lt_two_pi :

    (8 : ℝ) / 3
    <
    2 * Real.pi := by

  have hp :
      (2 : ℝ) ≤ Real.pi :=

    Real.two_le_pi

  have h84 :
      (8 : ℝ) / 3 < 4 := by

    norm_num

  nlinarith


theorem traversal_angle_step_abs_lt_two_pi
    (n : ℕ) :

    |traversalAngleStep n|
    <
    2 * Real.pi := by

  exact
    lt_of_le_of_lt
      (traversal_angle_step_abs_le_eight_thirds n)
      eight_thirds_lt_two_pi


theorem traversal_angle_step_lower_bound
    (n : ℕ) :

    -(2 * Real.pi)
    <
    traversalAngleStep n := by

  have h :=
    traversal_angle_step_abs_lt_two_pi n

  exact (abs_lt.mp h).1


theorem traversal_angle_step_upper_bound
    (n : ℕ) :

    traversalAngleStep n
    <
    2 * Real.pi := by

  have h :=
    traversal_angle_step_abs_lt_two_pi n

  exact (abs_lt.mp h).2


/- ============================================================
   III. GENUINE EUCLIDEAN CIRCLE
   ============================================================ -/

def radiusCirclePoint
    (r theta : ℝ) :
    ℝ × ℝ :=

  (
    r * Real.cos theta,
    r * Real.sin theta
  )


theorem radius_circle_point_is_euclidean
    (r theta : ℝ) :

    (radiusCirclePoint r theta).1 ^ 2
    +
    (radiusCirclePoint r theta).2 ^ 2
    =
    r ^ 2 := by

  unfold radiusCirclePoint

  have h :=
    Real.cos_sq_add_sin_sq theta

  nlinarith


/- ============================================================
   IV. A NONZERO SMALL GREGORY CORRECTION CHANGES THE
       ACTUAL EUCLIDEAN ENDPOINT
   ============================================================ -/

theorem radius_circle_point_changes_under_gregory_step
    (r : ℝ)
    (hr : r ≠ 0)
    (theta : ℝ)
    (n : ℕ) :

    radiusCirclePoint
      r
      (theta + traversalAngleStep n)
    ≠
    radiusCirclePoint
      r
      theta := by

  intro hEq

  have hx :=
    congrArg Prod.fst hEq

  have hy :=
    congrArg Prod.snd hEq

  have hcos :
      Real.cos
        (theta + traversalAngleStep n)
      =
      Real.cos theta := by

    change
      r * Real.cos
          (theta + traversalAngleStep n)
      =
      r * Real.cos theta
      at hx

    exact
      mul_left_cancel₀
        hr
        hx

  have hsin :
      Real.sin
        (theta + traversalAngleStep n)
      =
      Real.sin theta := by

    change
      r * Real.sin
          (theta + traversalAngleStep n)
      =
      r * Real.sin theta
      at hy

    exact
      mul_left_cancel₀
        hr
        hy

  have hcosStep :
      Real.cos
        (traversalAngleStep n)
      =
      1 := by

    calc

      Real.cos
          (traversalAngleStep n)
          =
          Real.cos
            (
              (theta + traversalAngleStep n)
              -
              theta
            ) := by

              congr 1
              ring

      _ =
          Real.cos
              (theta + traversalAngleStep n)
            *
          Real.cos theta
          +
          Real.sin
              (theta + traversalAngleStep n)
            *
          Real.sin theta := by

              rw [Real.cos_sub]

      _ =
          Real.cos theta * Real.cos theta
          +
          Real.sin theta * Real.sin theta := by

              rw [hcos, hsin]

      _ = 1 := by

              nlinarith
                [Real.cos_sq_add_sin_sq theta]


  have hZero :
      traversalAngleStep n = 0 :=

    (
      Real.cos_eq_one_iff_of_lt_of_lt
        (traversal_angle_step_lower_bound n)
        (traversal_angle_step_upper_bound n)
    ).mp hcosStep


  exact
    traversal_angle_step_nonzero
      n
      hZero


/- ============================================================
   V. CIRCUMFERENCE CORRECTION AS LENGTH
   ============================================================ -/

def classicalCircumferenceCorrection
    (r : ℝ)
    (n : ℕ) :
    ℝ :=

  (2 * r) * gregoryCorrectionR n


theorem circumference_correction_nonzero
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    classicalCircumferenceCorrection r n ≠ 0 := by

  unfold classicalCircumferenceCorrection

  exact
    mul_ne_zero
      (
        mul_ne_zero
          (by norm_num)
          hr
      )
      (gregory_correction_nonzero n)


/-
The exact length correction divided by radius is exactly the
angular correction:

      Delta C_n / r = 2 Delta pi_n.
-/
theorem circumference_correction_over_radius
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    classicalCircumferenceCorrection r n / r
    =
    traversalAngleStep n := by

  unfold
    classicalCircumferenceCorrection
    traversalAngleStep

  field_simp [hr]


/- ============================================================
   VI. RADIUS-NORMALIZED EUCLIDEAN TRAVERSAL BY LENGTH
   ============================================================ -/

def circleTraversalByLength
    (r s : ℝ) :
    ℝ × ℝ :=

  radiusCirclePoint
    r
    (s / r)


theorem circle_traversal_by_length_is_on_circle
    (r s : ℝ) :

    (circleTraversalByLength r s).1 ^ 2
    +
    (circleTraversalByLength r s).2 ^ 2
    =
    r ^ 2 := by

  unfold circleTraversalByLength

  exact
    radius_circle_point_is_euclidean
      r
      (s / r)


/- ============================================================
   VII. THE ACTUAL GEOMETRIC BRIDGE

   For any base traversal length s, adding the exact Gregory
   circumference correction changes the genuine Euclidean
   endpoint.

   This is no longer a numerator/state model.
   ============================================================ -/

theorem euclidean_endpoint_changes_under_every_gregory_circumference_correction
    (r : ℝ)
    (hr : r ≠ 0)
    (s : ℝ)
    (n : ℕ) :

    circleTraversalByLength
      r
      (
        s
        +
        classicalCircumferenceCorrection r n
      )
    ≠
    circleTraversalByLength
      r
      s := by

  unfold circleTraversalByLength

  have hangle :

      (
        s
        +
        classicalCircumferenceCorrection r n
      ) / r

      =

      s / r
      +
      traversalAngleStep n := by

    rw [
      add_div,
      circumference_correction_over_radius
        r
        hr
        n
    ]

  rw [hangle]

  exact
    radius_circle_point_changes_under_gregory_step
      r
      hr
      (s / r)
      n


/- ============================================================
   VIII. FINAL PACKAGE
   ============================================================ -/

structure ClassicalEuclideanTraversalStepClosure :
    Prop where

  exactCorrectionAlwaysNonzero :
    ∀ n : ℕ,
      gregoryCorrectionR n ≠ 0

  angularCorrectionAlwaysNonzero :
    ∀ n : ℕ,
      traversalAngleStep n ≠ 0

  angularCorrectionStrictlySubperiodic :
    ∀ n : ℕ,
      |traversalAngleStep n|
      <
      2 * Real.pi

  genuineEuclideanCircle :
    ∀ r theta : ℝ,
      (radiusCirclePoint r theta).1 ^ 2
      +
      (radiusCirclePoint r theta).2 ^ 2
      =
      r ^ 2

  correctionChangesEveryNonzeroRadiusEndpoint :
    ∀ r : ℝ,
      r ≠ 0
      →
      ∀ s : ℝ,
      ∀ n : ℕ,

        circleTraversalByLength
          r
          (
            s
            +
            classicalCircumferenceCorrection r n
          )

        ≠

        circleTraversalByLength
          r
          s


theorem classical_euclidean_traversal_step_closure :

    ClassicalEuclideanTraversalStepClosure := by

  exact
    {
      exactCorrectionAlwaysNonzero :=
        gregory_correction_nonzero

      angularCorrectionAlwaysNonzero :=
        traversal_angle_step_nonzero

      angularCorrectionStrictlySubperiodic :=
        traversal_angle_step_abs_lt_two_pi

      genuineEuclideanCircle :=
        radius_circle_point_is_euclidean

      correctionChangesEveryNonzeroRadiusEndpoint :=
        by
          intro r hr s n
          exact
            euclidean_endpoint_changes_under_every_gregory_circumference_correction
              r hr s n
    }


end

end PiQuasiClassicalBridge
