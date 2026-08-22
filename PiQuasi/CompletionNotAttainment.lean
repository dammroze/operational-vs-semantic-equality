import PiQuasi.ActualInfinityDemotion

set_option autoImplicit false

namespace PiQuasi


/-
"Eventually closes" is given its strongest operational
meaning:

there exists some finitely encoded number of refinements
after which the finite pi stage carries closure.
-/
def EventuallyFiniteClosure
    (s : TraditionalPiPotentialStage) :
    Prop :=
  ∃ k : U,
    CompletionClosed
      (TraditionalPiCompletionExtension.finite
        (finitePiIterate k s))


/-
No starting finite stage ever reaches such a finite
closure after any finitely encoded number of refinements.
-/
theorem finite_pi_never_eventually_closes
    (s : TraditionalPiPotentialStage) :
    ¬ EventuallyFiniteClosure s := by

  intro h

  cases h with
  | intro k hk =>
      exact
        no_finite_refinement_reaches_completion_closure
          k
          s
          hk


/-
The added completion object nevertheless carries
the completion property inside the enlarged universe.
-/
def AddedCompletionCarriesClosure : Prop :=
  CompletionClosed
    TraditionalPiCompletionExtension.actualCompletion


theorem added_completion_carries_closure :
    AddedCompletionCarriesClosure := by
  exact added_actual_completion_is_closed


/-
Finite origin means that an object in the enlarged
universe is literally the image of a finite pi stage.
-/
def HasFinitePiOrigin
    (x : TraditionalPiCompletionExtension) :
    Prop :=
  ∃ s : TraditionalPiPotentialStage,
    liftFinitePi s = x


/-
Anything carrying the completion property cannot have
a finite pi origin.
-/
theorem completion_closed_has_no_finite_pi_origin
    (x : TraditionalPiCompletionExtension)
    (hx : CompletionClosed x) :
    ¬ HasFinitePiOrigin x := by

  intro hOrigin

  have hxCompletion :
      x =
        TraditionalPiCompletionExtension.actualCompletion :=
    completion_closed_implies_added_constructor
      x
      hx

  cases hOrigin with
  | intro s hs =>

      have hFiniteEqCompletion :
          liftFinitePi s =
            TraditionalPiCompletionExtension.actualCompletion :=
        Eq.trans hs hxCompletion

      exact
        pi_actual_completion_ne_finite
          s
          (Eq.symm hFiniteEqCompletion)


/-
In particular, the completion object has no finite origin.
-/
theorem added_completion_has_no_finite_pi_origin :
    ¬ HasFinitePiOrigin
      TraditionalPiCompletionExtension.actualCompletion := by

  exact
    completion_closed_has_no_finite_pi_origin
      TraditionalPiCompletionExtension.actualCompletion
      added_actual_completion_is_closed


/-
The central separation statement.

The enlarged universe contains an object carrying closure,
while no finite refinement ever attains closure.
-/
structure ClosureWithoutFiniteAttainment
    (s : TraditionalPiPotentialStage) : Prop where

  completionHasClosure :
    CompletionClosed
      TraditionalPiCompletionExtension.actualCompletion

  noFiniteAttainment :
    ¬ EventuallyFiniteClosure s


theorem pi_closure_without_finite_attainment
    (s : TraditionalPiPotentialStage) :
    ClosureWithoutFiniteAttainment s := by

  exact
    {
      completionHasClosure :=
        added_actual_completion_is_closed

      noFiniteAttainment :=
        finite_pi_never_eventually_closes s
    }


/-
A property present only after explicit completion cannot
be reported as an event that occurred at a finite stage.
-/
def ClosureIsFiniteAttainmentResult
    (s : TraditionalPiPotentialStage) :
    Prop :=
  EventuallyFiniteClosure s


theorem completion_closure_is_not_finite_attainment_result
    (s : TraditionalPiPotentialStage) :
    ¬ ClosureIsFiniteAttainmentResult s := by

  exact finite_pi_never_eventually_closes s


/-
There is no "last finite refinement" at which the
completion property suddenly appears.
-/
def LastFiniteClosureWitness
    (s : TraditionalPiPotentialStage) :
    Prop :=
  ∃ k : U,
    CompletionClosed
      (TraditionalPiCompletionExtension.finite
        (finitePiIterate k s))


theorem no_last_finite_closure_witness
    (s : TraditionalPiPotentialStage) :
    ¬ LastFiniteClosureWitness s := by

  exact finite_pi_never_eventually_closes s


/-
Circle specialization.
-/
def EventuallyFiniteClosedCircle
    (s : TraditionalPiPotentialStage) :
    Prop :=
  ∃ k : U,
    TraditionalPiTerminal
      (finitePiIterate k s)


theorem traditional_pi_circle_never_closes_at_finite_refinement
    (s : TraditionalPiPotentialStage) :
    ¬ EventuallyFiniteClosedCircle s := by

  intro h

  cases h with
  | intro k hk =>
      exact
        traditional_pi_stage_ne_terminal
          (finitePiIterate k s)
          hk


/-
Water-tight specialization.
-/
def EventuallyFiniteWaterTight
    (s : TraditionalPiPotentialStage) :
    Prop :=
  ∃ k : U,
    TraditionalPiTerminal
      (finitePiIterate k s)


theorem traditional_pi_balloon_never_becomes_watertight
    (s : TraditionalPiPotentialStage) :
    ¬ EventuallyFiniteWaterTight s := by

  exact
    traditional_pi_circle_never_closes_at_finite_refinement
      s


end PiQuasi
