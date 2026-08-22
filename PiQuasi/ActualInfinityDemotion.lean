import PiQuasi.ClosureNecessityFinal

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. FINITE SUCCESSOR PROCESS
   ============================================================ -/

/-
Execute an arbitrary but finite number of refinements.
The counter U has only finite inductive construction.
-/
def finiteIterate
    (k : U)
    (s : FStage) :
    FStage :=
  match k with
  | .zero =>
      s
  | .next n =>
      extend (finiteIterate n s)


/-
The finite universe contains only actual constructed stages.

To represent a completed infinity we must enlarge the type
with a genuinely new constructor.
-/
inductive CompletionExtension : Type where
  | finite : FStage → CompletionExtension
  | actualCompletion : CompletionExtension


def liftFinite
    (s : FStage) :
    CompletionExtension :=
  .finite s


/-
The completion object is definitionally distinct
from every finite stage.
-/
theorem actual_completion_ne_finite
    (s : FStage) :
    CompletionExtension.actualCompletion ≠
      CompletionExtension.finite s := by
  intro h
  cases h


/-
No arbitrary finite sequence of refinements reaches
the added completion constructor.
-/
theorem actual_completion_ne_finite_iteration
    (k : U)
    (s : FStage) :
    CompletionExtension.actualCompletion ≠
      CompletionExtension.finite
        (finiteIterate k s) := by
  exact
    actual_completion_ne_finite
      (finiteIterate k s)


def ActualCompletionHasFinitePreimage : Prop :=
  ∃ s : FStage,
    liftFinite s =
      CompletionExtension.actualCompletion


theorem actual_completion_has_no_finite_preimage :
    ¬ ActualCompletionHasFinitePreimage := by

  intro h

  cases h with
  | intro s hs =>
      exact
        actual_completion_ne_finite s
          (Eq.symm hs)


/-
This is the precise ontological separation:

the added completion object is not any object already
present in the finite stage universe.
-/
theorem completion_is_strictly_outside_finite_image
    (s : FStage) :
    liftFinite s ≠
      CompletionExtension.actualCompletion := by
  intro h
  exact
    actual_completion_ne_finite s
      (Eq.symm h)



/- ============================================================
   II. TRADITIONAL PI PROCESS
   ============================================================ -/

/-
Arbitrarily many, but finitely encoded,
Gregory-Leibniz refinements.
-/
def finitePiIterate
    (k : U)
    (s : TraditionalPiPotentialStage) :
    TraditionalPiPotentialStage :=
  match k with
  | .zero =>
      s
  | .next n =>
      refineTraditionalPi
        (finitePiIterate n s)


/-
Again: the traditional finite pi process is one universe.

A completed-pi object is represented only by extending
that universe with a new constructor.
-/
inductive TraditionalPiCompletionExtension : Type where
  | finite :
      TraditionalPiPotentialStage →
      TraditionalPiCompletionExtension

  | actualCompletion :
      TraditionalPiCompletionExtension


def liftFinitePi
    (s : TraditionalPiPotentialStage) :
    TraditionalPiCompletionExtension :=
  .finite s


theorem pi_actual_completion_ne_finite
    (s : TraditionalPiPotentialStage) :
    TraditionalPiCompletionExtension.actualCompletion ≠
      TraditionalPiCompletionExtension.finite s := by
  intro h
  cases h


theorem pi_actual_completion_ne_any_finite_refinement
    (k : U)
    (s : TraditionalPiPotentialStage) :
    TraditionalPiCompletionExtension.actualCompletion ≠
      TraditionalPiCompletionExtension.finite
        (finitePiIterate k s) := by

  exact
    pi_actual_completion_ne_finite
      (finitePiIterate k s)


def PiActualCompletionHasFinitePreimage : Prop :=
  ∃ s : TraditionalPiPotentialStage,
    liftFinitePi s =
      TraditionalPiCompletionExtension.actualCompletion


theorem pi_actual_completion_has_no_finite_preimage :
    ¬ PiActualCompletionHasFinitePreimage := by

  intro h

  cases h with
  | intro s hs =>
      exact
        pi_actual_completion_ne_finite s
          (Eq.symm hs)



/- ============================================================
   III. WHERE DOES "CLOSURE" APPEAR?
   ============================================================ -/

/-
On a finite pi stage, exact completion means terminality.

For the newly introduced actual-completion constructor,
the infinitary model assigns completion directly.

This exposes the ontological move instead of hiding it.
-/
def CompletionClosed :
    TraditionalPiCompletionExtension → Prop
  | .finite s =>
      TraditionalPiTerminal s

  | .actualCompletion =>
      True


theorem added_actual_completion_is_closed :
    CompletionClosed
      TraditionalPiCompletionExtension.actualCompletion := by
  trivial


/-
No finite traditional-pi stage has that property.
-/
theorem no_finite_pi_extension_is_closed
    (s : TraditionalPiPotentialStage) :
    ¬ CompletionClosed
      (TraditionalPiCompletionExtension.finite s) := by

  change ¬ TraditionalPiTerminal s

  exact
    traditional_pi_stage_ne_terminal s


/-
Not after one step.
Not after ten steps.
Not after any finitely constructed number of steps.
-/
theorem no_finite_refinement_reaches_completion_closure
    (k : U)
    (s : TraditionalPiPotentialStage) :
    ¬ CompletionClosed
      (TraditionalPiCompletionExtension.finite
        (finitePiIterate k s)) := by

  exact
    no_finite_pi_extension_is_closed
      (finitePiIterate k s)


/-
Strong separation theorem:

inside this extension, anything carrying the
completion-closure property must be exactly the
new actual-completion constructor.

It cannot be a finite stage.
-/
theorem completion_closed_implies_added_constructor
    (x : TraditionalPiCompletionExtension) :
    CompletionClosed x →
    x =
      TraditionalPiCompletionExtension.actualCompletion := by

  cases x with

  | actualCompletion =>
      intro _
      rfl

  | finite s =>
      intro h

      have hf : False :=
        traditional_pi_stage_ne_terminal s h

      exact False.elim hf


/-
Therefore closure is not inherited from the
potential process.  It occurs only after the
universe has been extended by a new constructor.
-/
theorem completion_closure_not_in_finite_image :
    ¬ ∃ s : TraditionalPiPotentialStage,
        CompletionClosed
          (liftFinitePi s) := by

  intro h

  cases h with
  | intro s hs =>
      exact
        no_finite_pi_extension_is_closed
          s
          hs



/- ============================================================
   IV. PI CIRCLE CONSEQUENCE
   ============================================================ -/

/-
A genuine finite geometrically closed pi-circle
would produce a finite terminal pi stage.
Already impossible.
-/
theorem no_finite_stage_realizes_pi_circle_completion :
    ¬ ∃ c : FiniteTraditionalPiCircle,
        GeometricallyClosed c := by

  exact
    no_finite_closed_traditional_pi_circle_witness


/-
A water-tight finite pi balloon would also force
the forbidden finite terminal state.
-/
theorem no_finite_stage_realizes_watertight_pi_balloon :
    ¬ ∃ b : FinitePiWaterBalloon,
        WaterTight b := by

  exact
    no_finite_watertight_pi_balloon_witness



/- ============================================================
   V. BRUTAL SEPARATION STATEMENT
   ============================================================ -/

/-
The finite process has no completion-bearing element.
The explicitly enlarged universe does.

Both facts hold constructively and simultaneously.
-/
structure ActualCompletionSeparation : Prop where

  noFinite :
    ¬ ∃ s : TraditionalPiPotentialStage,
        CompletionClosed
          (TraditionalPiCompletionExtension.finite s)

  addedHasProperty :
    CompletionClosed
      TraditionalPiCompletionExtension.actualCompletion


theorem actual_completion_separation :
    ActualCompletionSeparation := by

  exact
    {
      noFinite :=
        completion_closure_not_in_finite_image

      addedHasProperty :=
        added_actual_completion_is_closed
    }


end PiQuasi
