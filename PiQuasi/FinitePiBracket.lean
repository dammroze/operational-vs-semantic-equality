import PiQuasi.SignedExact
import PiQuasi.QuasiCircle

set_option autoImplicit false

namespace PiQuasi


/-
Every value of P is strictly away from the
zero constructor of U.
-/
theorem pToU_ne_zero :
    (p : P) → pToU p ≠ U.zero
  | .one => by
      intro h
      cases h

  | .next p => by
      intro h
      cases h


/-
A positive exact finite fraction.

Its numerator cannot represent zero because
the numerator inhabits P.
-/
structure PositiveFraction : Type where
  num : P
  den : P


def positiveFractionToFraction
    (q : PositiveFraction) :
    Fraction :=
  {
    num := pToU q.num
    den := q.den
  }


theorem positive_fraction_numerator_ne_zero
    (q : PositiveFraction) :
    pToU q.num ≠ U.zero := by
  exact pToU_ne_zero q.num


/-
One finite state of a traditional-pi computation.

It does NOT contain a completed infinite value.

Instead it contains:

  left  : one finite exact candidate/bound
  width : strictly positive finite unresolved gap

The right endpoint is left + width semantically.
-/
structure FinitePiBracket : Type where
  left : Fraction
  width : PositiveFraction


/-
A finite pi bracket has collapsed to one exact
value only if its strictly positive width became zero.
-/
def BracketCollapsed
    (s : FinitePiBracket) :
    Prop :=
  pToU s.width.num = U.zero


theorem finite_pi_bracket_ne_collapsed
    (s : FinitePiBracket) :
    ¬ BracketCollapsed s := by
  exact pToU_ne_zero s.width.num


/-
A traditional-pi finite execution state consists
of one actual finite construction stage together
with unresolved positive-width pi information.
-/
structure TraditionalPiFiniteState : Type where
  construction : FStage
  bracket : FinitePiBracket


def ExactFinitePi
    (s : TraditionalPiFiniteState) :
    Prop :=
  BracketCollapsed s.bracket


theorem traditional_pi_finite_state_not_exact
    (s : TraditionalPiFiniteState) :
    ¬ ExactFinitePi s := by
  exact finite_pi_bracket_ne_collapsed s.bracket


/-
There is no finite state in this execution universe
that supplies a completed exact pi value.
-/
def FiniteExactPiWitness : Prop :=
  ∃ s : TraditionalPiFiniteState,
    ExactFinitePi s


theorem no_finite_exact_pi_witness :
    ¬ FiniteExactPiWitness := by
  intro h

  cases h with
  | intro s hs =>
      exact
        traditional_pi_finite_state_not_exact
          s
          hs


/-
Operational construction of a circle whose endpoint
requires exact completion of its pi state.
-/
structure TraditionalPiCircleAttempt : Type where
  piState : TraditionalPiFiniteState


def OperationallyClosed
    (c : TraditionalPiCircleAttempt) :
    Prop :=
  ExactFinitePi c.piState


theorem traditional_pi_circle_attempt_not_closed
    (c : TraditionalPiCircleAttempt) :
    ¬ OperationallyClosed c := by
  exact
    traditional_pi_finite_state_not_exact
      c.piState


/-
The unresolved width is the exact finite leakage
certificate of the attempted closure.
-/
def leakage
    (c : TraditionalPiCircleAttempt) :
    PositiveFraction :=
  c.piState.bracket.width


theorem leakage_numerator_ne_zero
    (c : TraditionalPiCircleAttempt) :
    pToU (leakage c).num ≠ U.zero := by
  exact
    pToU_ne_zero
      (leakage c).num


/-
Operational quasi-circle:

the attempted pi-generated circle plus a constructive
proof that the finite execution did not close.
-/
structure OperationalPiQuasiCircle : Type where
  attempt : TraditionalPiCircleAttempt
  notClosed : ¬ OperationallyClosed attempt


def quasiCircleFromAttempt
    (c : TraditionalPiCircleAttempt) :
    OperationalPiQuasiCircle :=
  {
    attempt := c
    notClosed :=
      traditional_pi_circle_attempt_not_closed c
  }


theorem every_finite_traditional_pi_attempt_is_quasi
    (c : TraditionalPiCircleAttempt) :
    ∃ q : OperationalPiQuasiCircle,
      q.attempt = c := by
  exact
    ⟨quasiCircleFromAttempt c, rfl⟩


end PiQuasi
