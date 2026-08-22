import ClassicalEuclideanTraversalStep
import Mathlib.Tactic

set_option autoImplicit false

namespace PiQuasiClassicalBridge

noncomputable section


/- ============================================================
   I. RATIONAL GREGORY STAGE RECURSION

   Recall:

      gregoryPartialQ n
        = 4 * sum_{i=0}^{n-1} (-1)^i/(2i+1)

   Therefore the correction indexed by n is the term taking

      P_(n+1) -> P_(n+2).
   ============================================================ -/


def gregoryNextCorrectionQ
    (n : ℕ) :
    ℚ :=

  ((-1 : ℚ) ^ (n + 1) * 4)
  /
  (2 * (n : ℚ) + 3)


theorem gregory_next_correction_q_denominator_form
    (n : ℕ) :

    gregoryNextCorrectionQ n
    =
    (
      (-1 : ℚ) ^ (n + 1) * 4
    )
    /
    (
      2 * ((n + 1 : ℕ) : ℚ) + 1
    ) := by

  unfold gregoryNextCorrectionQ

  congr 1

  push_cast

  ring


theorem gregory_partial_q_stage_recursion
    (n : ℕ) :

    gregoryPartialQ (n + 2)
    =
    gregoryPartialQ (n + 1)
    +
    gregoryNextCorrectionQ n := by

  unfold gregoryPartialQ leibnizPartialQ

  rw [
    show n + 2 = (n + 1) + 1 by omega,
    Finset.sum_range_succ
  ]

  rw [gregory_next_correction_q_denominator_form]

  ring


/- ============================================================
   II. THE RATIONAL CORRECTION CASTS EXACTLY TO THE
       REAL CORRECTION USED IN THE EUCLIDEAN MODULE
   ============================================================ -/


theorem gregory_next_correction_q_cast
    (n : ℕ) :

    (gregoryNextCorrectionQ n : ℝ)
    =
    gregoryCorrectionR n := by

  unfold
    gregoryNextCorrectionQ
    gregoryCorrectionR

  push_cast

  ring


/- ============================================================
   III. REAL GREGORY STAGE RECURSION
   ============================================================ -/


theorem gregory_partial_real_stage_recursion
    (n : ℕ) :

    gregoryPartialR (n + 2)
    =
    gregoryPartialR (n + 1)
    +
    gregoryCorrectionR n := by

  unfold gregoryPartialR

  rw [
    ← gregory_next_correction_q_cast n
  ]

  exact_mod_cast
    gregory_partial_q_stage_recursion n


/- ============================================================
   IV. CIRCUMFERENCE STAGE RECURSION
   ============================================================ -/


theorem finite_gregory_circumference_stage_recursion
    (r : ℝ)
    (n : ℕ) :

    finiteGregoryCircumference r (n + 2)
    =
    finiteGregoryCircumference r (n + 1)
    +
    classicalCircumferenceCorrection r n := by

  unfold
    finiteGregoryCircumference
    classicalCircumferenceCorrection

  rw [gregory_partial_real_stage_recursion]

  ring


/- ============================================================
   V. BOTH CONSECUTIVE GREGORY ENDPOINTS ARE GENUINE
      POINTS ON THE SAME EUCLIDEAN CIRCLE
   ============================================================ -/


theorem gregory_stage_endpoint_on_circle
    (r : ℝ)
    (n : ℕ) :

    (
      circleTraversalByLength
        r
        (finiteGregoryCircumference r n)
    ).1 ^ 2

    +

    (
      circleTraversalByLength
        r
        (finiteGregoryCircumference r n)
    ).2 ^ 2

    =
    r ^ 2 := by

  exact
    circle_traversal_by_length_is_on_circle
      r
      (finiteGregoryCircumference r n)


/- ============================================================
   VI. DIRECT GEOMETRIC NON-STABILIZATION OF CONSECUTIVE
       GREGORY STAGES

   This is the final missing bridge:

       actual Gregory stage
            ->
       actual circumference stage
            ->
       genuine Euclidean endpoint.

   No arithmetic numerator is renamed as an endpoint.
   ============================================================ -/


theorem consecutive_gregory_euclidean_endpoints_differ
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    circleTraversalByLength
      r
      (finiteGregoryCircumference r (n + 2))

    ≠

    circleTraversalByLength
      r
      (finiteGregoryCircumference r (n + 1)) := by

  rw [
    finite_gregory_circumference_stage_recursion
      r
      n
  ]

  exact
    euclidean_endpoint_changes_under_every_gregory_circumference_correction
      r
      hr
      (finiteGregoryCircumference r (n + 1))
      n


/- ============================================================
   VII. THERE IS NO FINITE CONSECUTIVE EUCLIDEAN
        STABILIZATION WITNESS
   ============================================================ -/


def ConsecutiveGregoryEuclideanStabilization
    (r : ℝ) :
    Prop :=

  ∃ n : ℕ,

    circleTraversalByLength
      r
      (finiteGregoryCircumference r (n + 2))

    =

    circleTraversalByLength
      r
      (finiteGregoryCircumference r (n + 1))


theorem no_consecutive_gregory_euclidean_stabilization
    (r : ℝ)
    (hr : r ≠ 0) :

    ¬ ConsecutiveGregoryEuclideanStabilization r := by

  intro h

  rcases h with ⟨n, hn⟩

  exact
    consecutive_gregory_euclidean_endpoints_differ
      r
      hr
      n
      hn


/- ============================================================
   VIII. FINAL BRIDGE PACKAGE
   ============================================================ -/


structure ClassicalGregoryStageEuclideanBridge
    (r : ℝ)
    (hr : r ≠ 0) :
    Prop where

  rationalStageRecursion :
    ∀ n : ℕ,

      gregoryPartialQ (n + 2)
      =
      gregoryPartialQ (n + 1)
      +
      gregoryNextCorrectionQ n

  realStageRecursion :
    ∀ n : ℕ,

      gregoryPartialR (n + 2)
      =
      gregoryPartialR (n + 1)
      +
      gregoryCorrectionR n

  circumferenceStageRecursion :
    ∀ n : ℕ,

      finiteGregoryCircumference r (n + 2)
      =
      finiteGregoryCircumference r (n + 1)
      +
      classicalCircumferenceCorrection r n

  everyStageEndpointOnEuclideanCircle :
    ∀ n : ℕ,

      (
        circleTraversalByLength
          r
          (finiteGregoryCircumference r n)
      ).1 ^ 2

      +

      (
        circleTraversalByLength
          r
          (finiteGregoryCircumference r n)
      ).2 ^ 2

      =
      r ^ 2

  consecutiveStageEndpointsDiffer :
    ∀ n : ℕ,

      circleTraversalByLength
        r
        (finiteGregoryCircumference r (n + 2))

      ≠

      circleTraversalByLength
        r
        (finiteGregoryCircumference r (n + 1))

  noFiniteConsecutiveStabilization :
    ¬ ConsecutiveGregoryEuclideanStabilization r


theorem classical_gregory_stage_euclidean_bridge
    (r : ℝ)
    (hr : r ≠ 0) :

    ClassicalGregoryStageEuclideanBridge r hr := by

  exact
    {
      rationalStageRecursion :=
        gregory_partial_q_stage_recursion

      realStageRecursion :=
        gregory_partial_real_stage_recursion

      circumferenceStageRecursion :=
        finite_gregory_circumference_stage_recursion r

      everyStageEndpointOnEuclideanCircle :=
        gregory_stage_endpoint_on_circle r

      consecutiveStageEndpointsDiffer :=
        consecutive_gregory_euclidean_endpoints_differ r hr

      noFiniteConsecutiveStabilization :=
        no_consecutive_gregory_euclidean_stabilization r hr
    }


end

end PiQuasiClassicalBridge
