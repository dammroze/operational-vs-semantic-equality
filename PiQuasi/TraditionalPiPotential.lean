import PiQuasi.FinitePiBracket
import PiQuasi.SignedExact

set_option autoImplicit false

namespace PiQuasi


/-
Finite constants.
-/
def uOne : U :=
  .next .zero

def uFour : U :=
  .next (.next (.next (.next .zero)))

def pTwo : P :=
  .next .one


/-
Alternating sign.
-/
inductive AltSign : Type where
  | pos : AltSign
  | neg : AltSign

def flipSign : AltSign → AltSign
  | .pos => .neg
  | .neg => .pos

def altSign : U → AltSign
  | .zero   => .pos
  | .next k => flipSign (altSign k)


/-
Odd denominator:

1, 3, 5, 7, ...
-/
def oddDenom : U → P
  | .zero   => .one
  | .next k => pAdd (oddDenom k) pTwo


/-
Finite Gregory-Leibniz correction for pi itself:

+4/1, -4/3, +4/5, -4/7, ...

Every correction is a finite exact signed fraction.
-/
def gregoryPiTerm
    (k : U) :
    ExactSignedFraction :=
  match altSign k with
  | .pos =>
      ⟨signedPositive uFour, oddDenom k⟩

  | .neg =>
      ⟨signedNegative uFour, oddDenom k⟩


/-
Finite partial execution.
No completed sequence is represented.
-/
def gregoryPiPartial : U → ExactSignedFraction
  | .zero =>
      gregoryPiTerm .zero

  | .next k =>
      exactAdd
        (gregoryPiPartial k)
        (gregoryPiTerm (.next k))


/-
A correction is operationally zero only when both
finite numerator components are zero.
-/
def CorrectionZero
    (q : ExactSignedFraction) :
    Prop :=
  q.num.pos = U.zero ∧
  q.num.neg = U.zero


theorem uFour_ne_zero :
    uFour ≠ U.zero := by
  intro h
  cases h


/-
Every finite next Gregory-Leibniz correction is nonzero.
-/
theorem gregory_pi_term_nonzero
    (k : U) :
    ¬ CorrectionZero (gregoryPiTerm k) := by

  unfold CorrectionZero gregoryPiTerm

  cases h : altSign k with
  | pos =>
      intro hz
      cases hz with
      | intro hp hn =>
          change uFour = U.zero at hp
          exact uFour_ne_zero hp

  | neg =>
      intro hz
      cases hz with
      | intro hp hn =>
          change uFour = U.zero at hn
          exact uFour_ne_zero hn


/-
One actually executed finite stage.
-/
structure TraditionalPiPotentialStage : Type where
  index : U
  value : ExactSignedFraction
  valueCorrect :
    value = gregoryPiPartial index


def initialTraditionalPiStage :
    TraditionalPiPotentialStage :=
  {
    index := .zero
    value := gregoryPiPartial .zero
    valueCorrect := rfl
  }


def refineTraditionalPi
    (s : TraditionalPiPotentialStage) :
    TraditionalPiPotentialStage :=
  {
    index := .next s.index
    value := gregoryPiPartial (.next s.index)
    valueCorrect := rfl
  }


/-
For this potential process, a finite stage could be final
only if its next exact correction were zero.
-/
def TraditionalPiTerminal
    (s : TraditionalPiPotentialStage) :
    Prop :=
  CorrectionZero
    (gregoryPiTerm (.next s.index))


theorem traditional_pi_stage_ne_terminal
    (s : TraditionalPiPotentialStage) :
    ¬ TraditionalPiTerminal s := by

  exact
    gregory_pi_term_nonzero
      (.next s.index)


def TraditionalPiFiniteFinalWitness : Prop :=
  ∃ s : TraditionalPiPotentialStage,
    TraditionalPiTerminal s


theorem no_traditional_pi_finite_final_witness :
    ¬ TraditionalPiFiniteFinalWitness := by

  intro h

  cases h with
  | intro s hs =>
      exact
        traditional_pi_stage_ne_terminal
          s
          hs


/-
A circle attempt driven by the actually executed
traditional-pi potential process.
-/
structure TraditionalPiOperationalCircle : Type where
  piStage : TraditionalPiPotentialStage


def TraditionalPiOperationalClosed
    (c : TraditionalPiOperationalCircle) :
    Prop :=
  TraditionalPiTerminal c.piStage


theorem traditional_pi_operational_circle_not_closed
    (c : TraditionalPiOperationalCircle) :
    ¬ TraditionalPiOperationalClosed c := by

  exact
    traditional_pi_stage_ne_terminal
      c.piStage


structure TraditionalPiOperationalQuasiCircle : Type where
  circle : TraditionalPiOperationalCircle
  openCertificate :
    ¬ TraditionalPiOperationalClosed circle


def traditionalPiQuasiCircle
    (c : TraditionalPiOperationalCircle) :
    TraditionalPiOperationalQuasiCircle :=
  {
    circle := c
    openCertificate :=
      traditional_pi_operational_circle_not_closed c
  }


theorem every_finite_traditional_pi_circle_is_quasi
    (c : TraditionalPiOperationalCircle) :
    ∃ q : TraditionalPiOperationalQuasiCircle,
      q.circle = c := by

  exact
    ⟨traditionalPiQuasiCircle c, rfl⟩


end PiQuasi
