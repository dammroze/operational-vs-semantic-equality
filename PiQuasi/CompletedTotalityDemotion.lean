import PiQuasi.CompletionNotAttainment

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. FINITE SUCCESSOR ORDER
   ============================================================ -/

/-
StageLE a b means:

a belongs to the initial successor segment
whose finite boundary is b.

No completed infinite order is introduced.
-/
def StageLE : FStage → FStage → Prop
  | .seed, _ =>
      True

  | .next _, .seed =>
      False

  | .next a, .next b =>
      StageLE a b


theorem stage_le_refl :
    (s : FStage) → StageLE s s
  | .seed => by
      trivial

  | .next s => by
      exact stage_le_refl s


/-
The immediate successor is never contained in
the finite initial segment ending at s.
-/
theorem successor_not_in_own_initial_segment :
    (s : FStage) →
      ¬ StageLE (extend s) s

  | .seed => by
      intro h
      exact h

  | .next s => by
      intro h
      exact
        successor_not_in_own_initial_segment
          s
          h



/- ============================================================
   II. FINITE TOTALITIES
   ============================================================ -/

/-
A finite candidate totality has one finite boundary.
It represents the initial segment generated up to
that boundary.
-/
structure FiniteTotality : Type where
  boundary : FStage


def FiniteContains
    (t : FiniteTotality)
    (s : FStage) :
    Prop :=
  StageLE s t.boundary


def FiniteTotalityContainsAll
    (t : FiniteTotality) :
    Prop :=
  (s : FStage) → FiniteContains t s


/-
Every finite candidate totality has a constructive
counterexample: successor(boundary).
-/
theorem every_finite_totality_misses_successor
    (t : FiniteTotality) :
    ¬ FiniteContains t (extend t.boundary) := by

  exact
    successor_not_in_own_initial_segment
      t.boundary


/-
Therefore no finite initial totality contains
the whole successor process.
-/
theorem no_finite_totality_contains_all :
    (t : FiniteTotality) →
      ¬ FiniteTotalityContainsAll t := by

  intro t
  intro hAll

  have hContained :
      FiniteContains t (extend t.boundary) :=
    hAll (extend t.boundary)

  exact
    every_finite_totality_misses_successor
      t
      hContained


def FiniteCompletedTotalityWitness : Prop :=
  ∃ t : FiniteTotality,
    FiniteTotalityContainsAll t


theorem no_finite_completed_totality_witness :
    ¬ FiniteCompletedTotalityWitness := by

  intro h

  cases h with
  | intro t ht =>
      exact
        no_finite_totality_contains_all
          t
          ht



/- ============================================================
   III. EXPLICIT COMPLETED-TOTALITY EXTENSION
   ============================================================ -/

/-
To possess an object declared to contain all stages,
the finite universe is explicitly enlarged.

The completed totality is not an FStage and is not
a FiniteTotality.
-/
inductive TotalityExtension : Type where
  | finite :
      FiniteTotality →
      TotalityExtension

  | completedTotality :
      TotalityExtension


def ExtendedContains
    (x : TotalityExtension)
    (s : FStage) :
    Prop :=
  match x with
  | .finite t =>
      FiniteContains t s

  | .completedTotality =>
      True


def ContainsAllStages
    (x : TotalityExtension) :
    Prop :=
  (s : FStage) →
    ExtendedContains x s


/-
The newly added object is declared to contain every
finite stage.
-/
theorem completed_totality_contains_all :
    ContainsAllStages
      TotalityExtension.completedTotality := by

  intro _
  trivial


/-
No object originating from a finite totality
has the same property.
-/
theorem lifted_finite_totality_not_complete
    (t : FiniteTotality) :
    ¬ ContainsAllStages
      (TotalityExtension.finite t) := by

  intro h

  exact
    no_finite_totality_contains_all
      t
      h


/-
Any object with the totality property must therefore
be the explicitly added completed-totality constructor.
-/
theorem contains_all_implies_completed_constructor
    (x : TotalityExtension) :
    ContainsAllStages x →
    x = TotalityExtension.completedTotality := by

  cases x with

  | completedTotality =>
      intro _
      rfl

  | finite t =>
      intro h

      have hf : False :=
        lifted_finite_totality_not_complete
          t
          h

      exact False.elim hf



/- ============================================================
   IV. NO FINITE ORIGIN
   ============================================================ -/

def liftFiniteTotality
    (t : FiniteTotality) :
    TotalityExtension :=
  .finite t


def CompletedTotalityHasFiniteOrigin : Prop :=
  ∃ t : FiniteTotality,
    liftFiniteTotality t =
      TotalityExtension.completedTotality


theorem completed_totality_has_no_finite_origin :
    ¬ CompletedTotalityHasFiniteOrigin := by

  intro h

  cases h with
  | intro t ht =>
      cases ht


/-
No finite candidate can be extended finitely until
it becomes the completed-totality constructor:
they inhabit different constructors of the enlarged type.
-/
theorem completed_totality_ne_any_finite_totality
    (t : FiniteTotality) :
    TotalityExtension.completedTotality ≠
      liftFiniteTotality t := by

  intro h
  cases h



/- ============================================================
   V. COMPLETION IS NOT EXHAUSTION
   ============================================================ -/

/-
Finite exhaustion means an actually constructed
finite candidate contains every stage.
-/
def FiniteExhaustion : Prop :=
  ∃ t : FiniteTotality,
    FiniteTotalityContainsAll t


theorem finite_exhaustion_impossible :
    ¬ FiniteExhaustion := by

  exact no_finite_completed_totality_witness


/-
Completed totality exists only in the explicitly
extended universe.
-/
def ExtendedCompletedTotalityExists : Prop :=
  ∃ x : TotalityExtension,
    ContainsAllStages x


theorem extended_completed_totality_exists :
    ExtendedCompletedTotalityExists := by

  exact
    ⟨
      TotalityExtension.completedTotality,
      completed_totality_contains_all
    ⟩


/-
Core separation:

no finite exhaustion exists,
while the enlarged universe possesses a newly
introduced object carrying the completed-totality
property.
-/
structure CompletedTotalitySeparation : Prop where

  noFiniteExhaustion :
    ¬ FiniteExhaustion

  extensionHasCompletedTotality :
    ExtendedCompletedTotalityExists

  completedHasNoFiniteOrigin :
    ¬ CompletedTotalityHasFiniteOrigin


theorem completed_totality_separation :
    CompletedTotalitySeparation := by

  exact
    {
      noFiniteExhaustion :=
        finite_exhaustion_impossible

      extensionHasCompletedTotality :=
        extended_completed_totality_exists

      completedHasNoFiniteOrigin :=
        completed_totality_has_no_finite_origin
    }



/- ============================================================
   VI. BRUTAL SUCCESSOR DIAGONAL
   ============================================================ -/

/-
Given ANY finite candidate claiming to contain all
successor-generated stages, its own boundary supplies
the counterexample.

There is no search, oracle, classical choice,
or excluded-middle argument.
-/
theorem finite_totality_self_defeat
    (t : FiniteTotality)
    (claim :
      FiniteTotalityContainsAll t) :
    False := by

  have hNext :
      FiniteContains t
        (extend t.boundary) :=
    claim (extend t.boundary)

  exact
    every_finite_totality_misses_successor
      t
      hNext


end PiQuasi
