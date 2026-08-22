import PiQuasi.FiniteFPBarrier

set_option autoImplicit false

namespace PiQuasi


/-
A word has only finite inductive construction.
The symbol type is arbitrary.
-/
inductive FiniteWord (α : Type) : Type where
  | nil : FiniteWord α
  | cons : α → FiniteWord α → FiniteWord α


def wordAppend
    {α : Type} :
    FiniteWord α →
    FiniteWord α →
    FiniteWord α
  | .nil, b =>
      b
  | .cons a rest, b =>
      .cons a (wordAppend rest b)


/-
Any finite representation of one actually available
traditional-pi stage.

The representation and the mathematical source are
kept explicitly separate.
-/
structure FiniteRepresentation
    (α : Type) : Type where
  code : FiniteWord α
  source : TraditionalPiPotentialStage


def representedPiObject
    {α : Type}
    (r : FiniteRepresentation α) :
    TraditionalPiCompletionExtension :=
  TraditionalPiCompletionExtension.finite r.source


/-
Exact closure is a property of the represented
mathematical source, not of the code spelling.
-/
def RepresentationExact
    {α : Type}
    (r : FiniteRepresentation α) :
    Prop :=
  TraditionalPiTerminal r.source


theorem finite_representation_not_exact
    {α : Type}
    (r : FiniteRepresentation α) :
    ¬ RepresentationExact r := by

  exact
    traditional_pi_stage_ne_terminal
      r.source


theorem finite_representation_not_actual_completion
    {α : Type}
    (r : FiniteRepresentation α) :
    representedPiObject r ≠
      TraditionalPiCompletionExtension.actualCompletion := by

  intro h

  exact
    pi_actual_completion_ne_finite
      r.source
      (Eq.symm h)


/-
Replace the entire finite code by another finite code,
possibly over another symbol type.

The source is unchanged.
-/
def reencode
    {α β : Type}
    (r : FiniteRepresentation α)
    (newCode : FiniteWord β) :
    FiniteRepresentation β :=
  {
    code := newCode
    source := r.source
  }


theorem arbitrary_finite_reencoding_not_exact
    {α β : Type}
    (r : FiniteRepresentation α)
    (newCode : FiniteWord β) :
    ¬ RepresentationExact
      (reencode r newCode) := by

  exact
    finite_representation_not_exact
      (reencode r newCode)


theorem arbitrary_finite_reencoding_not_completion
    {α β : Type}
    (r : FiniteRepresentation α)
    (newCode : FiniteWord β) :
    representedPiObject
      (reencode r newCode) ≠
        TraditionalPiCompletionExtension.actualCompletion := by

  exact
    finite_representation_not_actual_completion
      (reencode r newCode)


/-
Append arbitrarily much additional finite information
to the code.
-/
def growRepresentation
    {α : Type}
    (r : FiniteRepresentation α)
    (extra : FiniteWord α) :
    FiniteRepresentation α :=
  {
    code := wordAppend r.code extra
    source := r.source
  }


theorem finite_code_growth_never_creates_exactness
    {α : Type}
    (r : FiniteRepresentation α)
    (extra : FiniteWord α) :
    ¬ RepresentationExact
      (growRepresentation r extra) := by

  exact
    finite_representation_not_exact
      (growRepresentation r extra)


/-
A finite encoding scheme maps each finite pi source
to one finite code.
-/
structure FiniteEncodingScheme
    (α : Type) : Type where
  encode :
    TraditionalPiPotentialStage →
    FiniteWord α


def executeEncoding
    {α : Type}
    (scheme : FiniteEncodingScheme α)
    (s : TraditionalPiPotentialStage) :
    FiniteRepresentation α :=
  {
    code := scheme.encode s
    source := s
  }


/-
Universal barrier:

no finite encoding scheme creates exact closure
for any admissible finite pi stage.
-/
theorem no_finite_encoding_scheme_creates_exactness
    {α : Type}
    (scheme : FiniteEncodingScheme α)
    (s : TraditionalPiPotentialStage) :
    ¬ RepresentationExact
      (executeEncoding scheme s) := by

  exact
    traditional_pi_stage_ne_terminal s


theorem no_finite_encoding_scheme_creates_completion
    {α : Type}
    (scheme : FiniteEncodingScheme α)
    (s : TraditionalPiPotentialStage) :
    representedPiObject
      (executeEncoding scheme s) ≠
        TraditionalPiCompletionExtension.actualCompletion := by

  exact
    finite_representation_not_actual_completion
      (executeEncoding scheme s)


/-
Machine wrapping of a water balloon.
-/
structure EncodedPiBalloon
    (α : Type) : Type where
  balloon : FinitePiWaterBalloon
  code : FiniteWord α


def EncodedWaterTight
    {α : Type}
    (b : EncodedPiBalloon α) :
    Prop :=
  WaterTight b.balloon


def EncodedLeaks
    {α : Type}
    (b : EncodedPiBalloon α) :
    Prop :=
  ¬ EncodedWaterTight b


theorem every_finitely_encoded_pi_balloon_leaks
    {α : Type}
    (b : EncodedPiBalloon α) :
    EncodedLeaks b := by

  exact
    every_finite_traditional_pi_balloon_leaks
      b.balloon


def reencodeBalloon
    {α β : Type}
    (b : EncodedPiBalloon α)
    (newCode : FiniteWord β) :
    EncodedPiBalloon β :=
  {
    balloon := b.balloon
    code := newCode
  }


theorem arbitrary_finite_balloon_reencoding_still_leaks
    {α β : Type}
    (b : EncodedPiBalloon α)
    (newCode : FiniteWord β) :
    EncodedLeaks
      (reencodeBalloon b newCode) := by

  exact
    every_finitely_encoded_pi_balloon_leaks
      (reencodeBalloon b newCode)


/-
Meta-level barrier object:
representation growth cannot manufacture terminality,
completion, or water-tightness.
-/
structure FiniteRepresentationBarrier : Prop where

  noExactness :
    (α : Type) →
    (r : FiniteRepresentation α) →
    ¬ RepresentationExact r

  noCompletion :
    (α : Type) →
    (r : FiniteRepresentation α) →
    representedPiObject r ≠
      TraditionalPiCompletionExtension.actualCompletion

  noWaterTightness :
    (α : Type) →
    (b : EncodedPiBalloon α) →
    EncodedLeaks b


theorem finite_representation_barrier :
    FiniteRepresentationBarrier := by

  exact
    {
      noExactness := by
        intro α r
        exact finite_representation_not_exact r

      noCompletion := by
        intro α r
        exact finite_representation_not_actual_completion r

      noWaterTightness := by
        intro α b
        exact every_finitely_encoded_pi_balloon_leaks b
    }


end PiQuasi
