import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false

namespace PiQuasiClassicalBridge


/- ============================================================
   I. CLASSICAL LEIBNIZ LIMIT IS EXPLICITLY GRANTED

   This is an adversarial cross-check layer.

   Unlike the ultradeterminist core, this module deliberately
   works inside the standard real-number semantics of Mathlib.

   It does NOT deny the classical theorem

       sum (-1)^k/(2k+1) -> pi/4.
   ============================================================ -/


theorem classical_leibniz_limit_is_granted :

    Filter.Tendsto
      (
        fun k : ℕ =>
          ∑ i ∈ Finset.range k,
            (-1 : ℝ) ^ i /
            (2 * (i : ℝ) + 1)
      )
      Filter.atTop
      (nhds (Real.pi / 4)) :=

  Real.tendsto_sum_pi_div_four


/- ============================================================
   II. FINITE GREGORY STAGES ARE RATIONAL
   ============================================================ -/


def leibnizPartialQ
    (n : ℕ) :
    ℚ :=

  ∑ i ∈ Finset.range n,
    (-1 : ℚ) ^ i /
    (2 * (i : ℚ) + 1)


def gregoryPartialQ
    (n : ℕ) :
    ℚ :=

  4 * leibnizPartialQ n


def gregoryPartialR
    (n : ℕ) :
    ℝ :=

  (gregoryPartialQ n : ℝ)


/- ============================================================
   III. NO FINITE RATIONAL GREGORY STAGE IS CLASSICAL PI
   ============================================================ -/


theorem finite_gregory_stage_ne_classical_pi
    (n : ℕ) :

    gregoryPartialR n ≠ Real.pi := by

  intro h

  have hpi :
      Real.pi = (gregoryPartialQ n : ℝ) := by

    exact h.symm

  exact
    irrational_pi.ne_rat
      (gregoryPartialQ n)
      hpi


/- ============================================================
   IV. CLASSICAL CIRCUMFERENCE LENGTH
   ============================================================ -/


def finiteGregoryCircumference
    (r : ℝ)
    (n : ℕ) :
    ℝ :=

  (2 * r) * gregoryPartialR n


noncomputable def classicalCircumference
    (r : ℝ) :
    ℝ :=

  (2 * r) * Real.pi


theorem finite_gregory_circumference_ne_classical
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    finiteGregoryCircumference r n
    ≠
    classicalCircumference r := by

  intro h

  have hfactor :
      (2 * r : ℝ) ≠ 0 := by

    exact
      mul_ne_zero
        (by norm_num)
        hr

  have hpi :
      gregoryPartialR n = Real.pi := by

    exact
      mul_left_cancel₀
        hfactor
        (by
          simpa
            [finiteGregoryCircumference,
             classicalCircumference]
            using h)

  exact
    finite_gregory_stage_ne_classical_pi
      n
      hpi


/- ============================================================
   V. ACTUAL EUCLIDEAN COORDINATES:
      STEREOGRAPHIC PARAMETRIZATION OF UNIT CIRCLE
   ============================================================ -/


noncomputable def stereoX
    (t : ℝ) :
    ℝ :=

  (1 - t^2) / (1 + t^2)


noncomputable def stereoY
    (t : ℝ) :
    ℝ :=

  (2 * t) / (1 + t^2)


noncomputable def stereo
    (t : ℝ) :
    ℝ × ℝ :=

  (stereoX t, stereoY t)


/-
These are genuine standard real coordinates on

        x^2 + y^2 = 1.
-/
theorem stereo_on_unit_circle
    (t : ℝ) :

    (stereo t).1 ^ 2
    +
    (stereo t).2 ^ 2
    =
    1 := by

  have hden :
      1 + t^2 ≠ 0 := by

    positivity

  unfold stereo stereoX stereoY

  field_simp [hden]

  ring


/- ============================================================
   VI. THE STEREOGRAPHIC ENDPOINT EQUALS START
       EXACTLY WHEN ITS PARAMETER IS ZERO
   ============================================================ -/


theorem stereo_eq_start_iff
    (t : ℝ) :

    stereo t = stereo 0
    ↔
    t = 0 := by

  constructor

  · intro h

    have hy :
        stereoY t = stereoY 0 := by

      exact congrArg Prod.snd h

    have hy0 :
        (2 * t) / (1 + t^2) = 0 := by

      simpa [stereoY] using hy

    have hden :
        1 + t^2 ≠ 0 := by

      positivity

    field_simp [hden] at hy0

    linarith

  · intro ht

    subst t

    rfl


/- ============================================================
   VII. CLASSICAL PI RESIDUAL AS A GENUINE EUCLIDEAN
        UNIT-CIRCLE POINT
   ============================================================ -/


noncomputable def classicalPiResidual
    (n : ℕ) :
    ℝ :=

  gregoryPartialR n - Real.pi


noncomputable def euclideanResidualEndpoint
    (n : ℕ) :
    ℝ × ℝ :=

  stereo
    (classicalPiResidual n)


noncomputable def euclideanResidualStart :
    ℝ × ℝ :=

  stereo 0


theorem euclidean_residual_endpoint_on_unit_circle
    (n : ℕ) :

    (euclideanResidualEndpoint n).1 ^ 2
    +
    (euclideanResidualEndpoint n).2 ^ 2
    =
    1 := by

  exact
    stereo_on_unit_circle
      (classicalPiResidual n)


theorem euclidean_residual_start_on_unit_circle :

    euclideanResidualStart.1 ^ 2
    +
    euclideanResidualStart.2 ^ 2
    =
    1 := by

  exact
    stereo_on_unit_circle 0


theorem classical_pi_residual_nonzero
    (n : ℕ) :

    classicalPiResidual n ≠ 0 := by

  intro h

  have heq :
      gregoryPartialR n = Real.pi := by

    unfold classicalPiResidual at h

    linarith

  exact
    finite_gregory_stage_ne_classical_pi
      n
      heq


/- ============================================================
   VIII. CONCRETE EUCLIDEAN ENDPOINT SEPARATION
   ============================================================ -/


theorem euclidean_residual_endpoint_ne_start
    (n : ℕ) :

    euclideanResidualEndpoint n
    ≠
    euclideanResidualStart := by

  intro h

  have hz :
      classicalPiResidual n = 0 := by

    exact
      (stereo_eq_start_iff
        (classicalPiResidual n)).mp h

  exact
    classical_pi_residual_nonzero
      n
      hz


/- ============================================================
   IX. FINAL ADVERSARIAL PACKAGE

   Notice exactly what is claimed:

   1. Classical convergence is granted.
   2. Classical pi irrationality is granted.
   3. Every finite Gregory stage is rational.
   4. Therefore no finite Gregory stage equals classical pi.
   5. Hence the finite circumference formula does not equal
      the classical circumference.
   6. The nonzero residual can be represented by actual
      R^2 coordinates satisfying the standard unit-circle law.
   7. That genuine Euclidean residual endpoint is not start.

   This theorem does NOT claim that the stereographic parameter
   is classical arc length.
   ============================================================ -/


structure ClassicalEuclideanAdversarialClosure
    (r : ℝ)
    (hr : r ≠ 0) :
    Prop where

  everyFiniteGregoryStageDiffersFromPi :
    ∀ n : ℕ,
      gregoryPartialR n ≠ Real.pi

  everyFiniteGregoryCircumferenceDiffersFromClassical :
    ∀ n : ℕ,
      finiteGregoryCircumference r n
      ≠
      classicalCircumference r

  everyResidualEndpointIsOnUnitCircle :
    ∀ n : ℕ,
      (euclideanResidualEndpoint n).1 ^ 2
      +
      (euclideanResidualEndpoint n).2 ^ 2
      =
      1

  residualStartIsOnUnitCircle :
      euclideanResidualStart.1 ^ 2
      +
      euclideanResidualStart.2 ^ 2
      =
      1

  everyResidualEndpointDiffersFromStart :
    ∀ n : ℕ,
      euclideanResidualEndpoint n
      ≠
      euclideanResidualStart


theorem classical_euclidean_adversarial_closure
    (r : ℝ)
    (hr : r ≠ 0) :

    ClassicalEuclideanAdversarialClosure r hr := by

  exact
    {
      everyFiniteGregoryStageDiffersFromPi :=
        finite_gregory_stage_ne_classical_pi

      everyFiniteGregoryCircumferenceDiffersFromClassical :=
        finite_gregory_circumference_ne_classical
          r
          hr

      everyResidualEndpointIsOnUnitCircle :=
        euclidean_residual_endpoint_on_unit_circle

      residualStartIsOnUnitCircle :=
        euclidean_residual_start_on_unit_circle

      everyResidualEndpointDiffersFromStart :=
        euclidean_residual_endpoint_ne_start
    }


end PiQuasiClassicalBridge
