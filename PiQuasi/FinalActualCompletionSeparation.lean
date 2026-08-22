import PiQuasi.CompletionNotAttainment
import PiQuasi.IndependentFiniteProgressBridge

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. THE ADDED COMPLETION IS CLOSED
   ============================================================ -/

/-
This is the exact completed object introduced by the
completion-extension model.

No claim is made here that it was reached by the
finite generating process.
-/
def ActualCompletionIsClosed : Prop :=
  CompletionClosed
    TraditionalPiCompletionExtension.actualCompletion


theorem actual_completion_is_closed :
    ActualCompletionIsClosed := by

  exact
    added_actual_completion_is_closed


/- ============================================================
   II. FINITE ATTAINMENT OF COMPLETION-CLOSURE
   ============================================================ -/

/-
A finite attainment of completed closure would require
one actual finite traditional-pi stage whose embedding
into the extension already carries CompletionClosed.
-/
def FiniteCompletionClosureAttainment : Prop :=
  ∃ s : TraditionalPiPotentialStage,
    CompletionClosed
      (liftFinitePi s)


theorem no_finite_completion_closure_attainment :
    ¬ FiniteCompletionClosureAttainment := by

  exact
    completion_closure_not_in_finite_image


/- ============================================================
   III. THE CLOSED COMPLETION HAS NO FINITE ORIGIN
   ============================================================ -/

theorem actual_completion_has_no_finite_origin :
    ¬ HasFinitePiOrigin
        TraditionalPiCompletionExtension.actualCompletion := by

  exact
    completion_closed_has_no_finite_pi_origin
      TraditionalPiCompletionExtension.actualCompletion
      actual_completion_is_closed


/- ============================================================
   IV. CLOSED EXTENSION OBJECTS ARE THE ADDED COMPLETION
   ============================================================ -/

/-
Inside this explicit extension model, closure identifies
the added completion constructor.

Thus closure is not secretly being carried by some
embedded finite stage.
-/
theorem every_closed_extension_is_the_added_completion
    (x : TraditionalPiCompletionExtension)
    (hx : CompletionClosed x) :

    x =
    TraditionalPiCompletionExtension.actualCompletion := by

  exact
    completion_closed_implies_added_constructor
      x
      hx


/- ============================================================
   V. EVERY FINITE STAGE REMAINS NONTERMINAL
   ============================================================ -/

theorem final_every_finite_stage_nonterminal :
    ∀ s : TraditionalPiPotentialStage,
      ¬ TraditionalPiTerminal s := by

  intro s

  exact
    traditional_pi_stage_ne_terminal s


/- ============================================================
   VI. EVERY FINITE PROGRESS STAGE REMAINS NON-CLOSED
   ============================================================ -/

theorem final_every_finite_progress_stage_nonclosed :
    ∀ s : TraditionalPiPotentialStage,

      ¬ EndpointClosed
          TraditionalPiFiniteProgressGeometry
          s := by

  intro s

  exact
    traditional_pi_finite_progress_not_closed s


theorem final_no_finite_progress_closure_witness :

    ¬ FiniteEndpointClosureWitness
        TraditionalPiFiniteProgressGeometry := by

  exact
    no_traditional_pi_finite_progress_closure_witness


/- ============================================================
   VII. NO EVENTUAL FINITE CLOSURE
   ============================================================ -/

theorem final_no_eventual_finite_closure :
    ∀ s : TraditionalPiPotentialStage,
      ¬ EventuallyFiniteClosedCircle s := by

  intro s

  exact
    traditional_pi_circle_never_closes_at_finite_refinement
      s


theorem final_no_last_finite_closure_witness :
    ∀ s : TraditionalPiPotentialStage,
      ¬ LastFiniteClosureWitness s := by

  intro s

  exact
    no_last_finite_closure_witness s


/- ============================================================
   VIII. RETROACTIVE FINITE ATTAINMENT
   ============================================================ -/

/-
This proposition expresses precisely the move rejected
by the finite-attainment analysis:

"If the added completion is closed, then some finite
generating stage must already have attained that
completion-closure."

We prove that implication itself is impossible in the
formal model.
-/
def CompletionRetroactivelyCreatesFiniteAttainment :
    Prop :=

  ActualCompletionIsClosed →
  FiniteCompletionClosureAttainment


theorem completion_does_not_retroactively_create_finite_attainment :

    ¬ CompletionRetroactivelyCreatesFiniteAttainment := by

  intro hRetro

  have hFinite :
      FiniteCompletionClosureAttainment :=

    hRetro
      actual_completion_is_closed

  exact
    no_finite_completion_closure_attainment
      hFinite


/- ============================================================
   IX. RETROACTIVE FINITE-PROGRESS CLOSURE
   ============================================================ -/

/-
A second possible retroactive interpretation would say
that closure of the completed object somehow creates a
finite closure witness in the exact finite-progress
chain.

That implication is also impossible.
-/
def CompletionRetroactivelyCreatesFiniteProgressClosure :
    Prop :=

  ActualCompletionIsClosed →

  FiniteEndpointClosureWitness
    TraditionalPiFiniteProgressGeometry


theorem completion_does_not_retroactively_create_finite_progress_closure :

    ¬ CompletionRetroactivelyCreatesFiniteProgressClosure := by

  intro hRetro

  have hFinite :
      FiniteEndpointClosureWitness
        TraditionalPiFiniteProgressGeometry :=

    hRetro
      actual_completion_is_closed

  exact
    final_no_finite_progress_closure_witness
      hFinite


/- ============================================================
   X. COMPLETED CLOSURE WITHOUT FINITE ATTAINMENT
   ============================================================ -/

/-
This is the central conjunction.

The completed extension is closed.

Simultaneously:

* no finite embedded stage carries completion-closure;
* the completed object has no finite pi origin;
* every finite stage is nonterminal;
* no finite progress closure witness exists.

Closure at completion therefore does not represent a
closure event attained by the finite generating chain.
-/
structure CompletedClosureWithoutFiniteAttainment : Prop where

  completedObjectIsClosed :
    ActualCompletionIsClosed

  completedObjectHasNoFiniteOrigin :
    ¬ HasFinitePiOrigin
        TraditionalPiCompletionExtension.actualCompletion

  noFiniteCompletionClosure :
    ¬ FiniteCompletionClosureAttainment

  everyFiniteStageNonterminal :
    ∀ s : TraditionalPiPotentialStage,
      ¬ TraditionalPiTerminal s

  noFiniteProgressClosure :
    ¬ FiniteEndpointClosureWitness
        TraditionalPiFiniteProgressGeometry

  noEventualFiniteClosure :
    ∀ s : TraditionalPiPotentialStage,
      ¬ EventuallyFiniteClosedCircle s

  noLastFiniteClosure :
    ∀ s : TraditionalPiPotentialStage,
      ¬ LastFiniteClosureWitness s


theorem completed_closure_without_finite_attainment :
    CompletedClosureWithoutFiniteAttainment := by

  exact
    {
      completedObjectIsClosed :=
        actual_completion_is_closed

      completedObjectHasNoFiniteOrigin :=
        actual_completion_has_no_finite_origin

      noFiniteCompletionClosure :=
        no_finite_completion_closure_attainment

      everyFiniteStageNonterminal :=
        final_every_finite_stage_nonterminal

      noFiniteProgressClosure :=
        final_no_finite_progress_closure_witness

      noEventualFiniteClosure :=
        final_no_eventual_finite_closure

      noLastFiniteClosure :=
        final_no_last_finite_closure_witness
    }


/- ============================================================
   XI. FINAL ACTUAL-COMPLETION SEPARATION
   ============================================================ -/

structure FinalActualCompletionSeparation : Prop where

  completionClosed :
    ActualCompletionIsClosed

  completionIsAddedConstructor :
    ∀ x : TraditionalPiCompletionExtension,
      CompletionClosed x →
      x =
      TraditionalPiCompletionExtension.actualCompletion

  completionNotInFiniteClosedImage :
    ¬ FiniteCompletionClosureAttainment

  completionNoFiniteOrigin :
    ¬ HasFinitePiOrigin
        TraditionalPiCompletionExtension.actualCompletion

  finiteProcessNeverTerminal :
    ∀ s : TraditionalPiPotentialStage,
      ¬ TraditionalPiTerminal s

  finiteProgressNeverCloses :
    ∀ s : TraditionalPiPotentialStage,

      ¬ EndpointClosed
          TraditionalPiFiniteProgressGeometry
          s

  completionCannotRetroactivelyCreateFiniteAttainment :
    ¬ CompletionRetroactivelyCreatesFiniteAttainment

  completionCannotRetroactivelyCreateProgressClosure :
    ¬ CompletionRetroactivelyCreatesFiniteProgressClosure


theorem final_actual_completion_separation :
    FinalActualCompletionSeparation := by

  exact
    {
      completionClosed :=
        actual_completion_is_closed

      completionIsAddedConstructor := by
        intro x hx

        exact
          every_closed_extension_is_the_added_completion
            x
            hx

      completionNotInFiniteClosedImage :=
        no_finite_completion_closure_attainment

      completionNoFiniteOrigin :=
        actual_completion_has_no_finite_origin

      finiteProcessNeverTerminal :=
        final_every_finite_stage_nonterminal

      finiteProgressNeverCloses :=
        final_every_finite_progress_stage_nonclosed

      completionCannotRetroactivelyCreateFiniteAttainment :=
        completion_does_not_retroactively_create_finite_attainment

      completionCannotRetroactivelyCreateProgressClosure :=
        completion_does_not_retroactively_create_finite_progress_closure
    }


end PiQuasi
