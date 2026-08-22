import PiQuasi.CompletedTotalityDemotion
import PiQuasi.FiniteRepresentationExactnessBarrier

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. NO FINITE REPRESENTATION BRIDGES TO COMPLETION
   ============================================================ -/

def FiniteRepresentationBridgesCompletion : Prop :=
  ∃ α : Type,
  ∃ r : FiniteRepresentation α,
    representedPiObject r =
      TraditionalPiCompletionExtension.actualCompletion


theorem no_finite_representation_bridges_completion :
    ¬ FiniteRepresentationBridgesCompletion := by

  intro h

  cases h with
  | intro α hα =>
      cases hα with
      | intro r hr =>
          exact
            finite_representation_not_actual_completion
              r
              hr



/- ============================================================
   II. NO FINITE ENCODING CREATES EXACT PI
   ============================================================ -/

def FiniteEncodingCreatesExactPi : Prop :=
  ∃ α : Type,
  ∃ scheme : FiniteEncodingScheme α,
  ∃ s : TraditionalPiPotentialStage,
    RepresentationExact
      (executeEncoding scheme s)


theorem no_finite_encoding_creates_exact_pi :
    ¬ FiniteEncodingCreatesExactPi := by

  intro h

  cases h with
  | intro α hα =>
      cases hα with
      | intro scheme hs =>
          cases hs with
          | intro s hexact =>
              exact
                no_finite_encoding_scheme_creates_exactness
                  scheme
                  s
                  hexact



/- ============================================================
   III. NO FINITE PI CLOSURE ATTAINMENT
   ============================================================ -/

def FinitePiClosureAttainmentExists : Prop :=
  ∃ s : TraditionalPiPotentialStage,
    EventuallyFiniteClosure s


theorem no_finite_pi_closure_attainment :
    ¬ FinitePiClosureAttainmentExists := by

  intro h

  cases h with
  | intro s hs =>
      exact
        finite_pi_never_eventually_closes
          s
          hs



/- ============================================================
   IV. NO FINITE GEOMETRICALLY CLOSED PI CIRCLE
   ============================================================ -/

def FiniteClosedPiCircleExists : Prop :=
  ∃ c : FiniteTraditionalPiCircle,
    GeometricallyClosed c


theorem no_finite_closed_pi_circle :
    ¬ FiniteClosedPiCircleExists := by

  exact
    no_finite_closed_traditional_pi_circle_witness



/- ============================================================
   V. NO FINITE WATER-TIGHT PI BALLOON
   ============================================================ -/

def FiniteWaterTightPiBalloonExists : Prop :=
  ∃ b : FinitePiWaterBalloon,
    WaterTight b


theorem no_finite_watertight_pi_balloon :
    ¬ FiniteWaterTightPiBalloonExists := by

  exact
    no_finite_watertight_pi_balloon_witness



/- ============================================================
   VI. NO FINITELY ENCODED WATER-TIGHT PI BALLOON
   ============================================================ -/

def FiniteEncodedWaterTightPiBalloonExists : Prop :=
  ∃ α : Type,
  ∃ b : EncodedPiBalloon α,
    EncodedWaterTight b


theorem no_finite_encoded_watertight_pi_balloon :
    ¬ FiniteEncodedWaterTightPiBalloonExists := by

  intro h

  cases h with
  | intro α hα =>
      cases hα with
      | intro b hb =>
          exact
            every_finitely_encoded_pi_balloon_leaks
              b
              hb



/- ============================================================
   VII. COMPLETED TOTALITY IS NOT FINITE EXHAUSTION
   ============================================================ -/

theorem final_no_finite_exhaustion :
    ¬ FiniteExhaustion := by
  exact finite_exhaustion_impossible


theorem final_completed_totality_has_no_finite_origin :
    ¬ CompletedTotalityHasFiniteOrigin := by
  exact completed_totality_has_no_finite_origin


theorem final_extension_contains_completed_totality :
    ExtendedCompletedTotalityExists := by
  exact extended_completed_totality_exists



/- ============================================================
   VIII. COMPLETION CLOSURE EXISTS ONLY IN THE EXTENSION
   ============================================================ -/

theorem final_added_completion_carries_closure :
    CompletionClosed
      TraditionalPiCompletionExtension.actualCompletion := by

  exact added_actual_completion_is_closed


theorem final_completion_closure_not_in_finite_chain :
    ¬ ∃ s : TraditionalPiPotentialStage,
        CompletionClosed
          (TraditionalPiCompletionExtension.finite s) := by

  exact completion_closure_not_in_finite_image



/- ============================================================
   IX. FINAL ULTRAFINITARY BARRIER
   ============================================================ -/

structure UltrafinitaryPiBarrier : Prop where

  noFiniteExhaustion :
    ¬ FiniteExhaustion

  completedTotalityNoFiniteOrigin :
    ¬ CompletedTotalityHasFiniteOrigin

  noFinitePiClosureAttainment :
    ¬ FinitePiClosureAttainmentExists

  noFiniteClosedPiCircle :
    ¬ FiniteClosedPiCircleExists

  noFiniteWaterTightPiBalloon :
    ¬ FiniteWaterTightPiBalloonExists

  noFiniteRepresentationCompletionBridge :
    ¬ FiniteRepresentationBridgesCompletion

  noFiniteEncodingExactPi :
    ¬ FiniteEncodingCreatesExactPi

  noFiniteEncodedWaterTightPiBalloon :
    ¬ FiniteEncodedWaterTightPiBalloonExists

  extensionHasCompletedTotality :
    ExtendedCompletedTotalityExists

  addedCompletionHasClosure :
    CompletionClosed
      TraditionalPiCompletionExtension.actualCompletion


theorem ultrafinitary_pi_barrier :
    UltrafinitaryPiBarrier := by

  exact
    {
      noFiniteExhaustion :=
        finite_exhaustion_impossible

      completedTotalityNoFiniteOrigin :=
        completed_totality_has_no_finite_origin

      noFinitePiClosureAttainment :=
        no_finite_pi_closure_attainment

      noFiniteClosedPiCircle :=
        no_finite_closed_pi_circle

      noFiniteWaterTightPiBalloon :=
        no_finite_watertight_pi_balloon

      noFiniteRepresentationCompletionBridge :=
        no_finite_representation_bridges_completion

      noFiniteEncodingExactPi :=
        no_finite_encoding_creates_exact_pi

      noFiniteEncodedWaterTightPiBalloon :=
        no_finite_encoded_watertight_pi_balloon

      extensionHasCompletedTotality :=
        extended_completed_totality_exists

      addedCompletionHasClosure :=
        added_actual_completion_is_closed
    }


/- ============================================================
   X. OPERATIONAL DEMOTION THEOREM
   ============================================================ -/

/-
Inside the ultrafinitary universe there is simultaneously:

1. no finite exhaustion;
2. no finite pi closure;
3. no finite exact encoding;
4. no finite water-tight pi balloon.

The completion and completed-totality properties only
occur in the explicitly extended universes.
-/
theorem operational_actual_infinity_demotion :
    (¬ FiniteExhaustion) ∧
    (¬ FinitePiClosureAttainmentExists) ∧
    (¬ FiniteRepresentationBridgesCompletion) ∧
    (¬ FiniteWaterTightPiBalloonExists) := by

  exact
    ⟨
      finite_exhaustion_impossible,
      no_finite_pi_closure_attainment,
      no_finite_representation_bridges_completion,
      no_finite_watertight_pi_balloon
    ⟩


end PiQuasi
