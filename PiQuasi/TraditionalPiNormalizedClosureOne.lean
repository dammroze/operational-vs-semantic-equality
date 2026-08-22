import PiQuasi.TraditionalPiUltradeterministCircumference

set_option autoImplicit false

namespace PiQuasi


/- 0 = no exact-closure certificate
   1 = exact-closure certificate -/
def closureZero : U :=
  U.zero

def closureOne : U :=
  U.next U.zero


theorem closure_one_ne_zero :
    closureOne ≠ closureZero := by
  intro h
  cases h


/-
A sound normalized indicator may output 1 only if the
exact circumference closure debt is zero.
-/
structure NormalizedClosureIndicator
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :
    Type where

  value : U

  oneMeansZeroDebt :
    value = closureOne →
    CorrectionZero
      (traditionalPiCircumferenceClosureDebt r s)


/-
Because the exact debt is nonzero at every constructed
stage, a sound indicator can never output 1.
-/
theorem normalized_closure_one_impossible
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage)
    (I : NormalizedClosureIndicator r s) :

    I.value ≠ closureOne := by

  intro hOne

  have hZero :
      CorrectionZero
        (traditionalPiCircumferenceClosureDebt r s) :=
    I.oneMeansZeroDebt hOne

  exact
    circumference_closure_debt_nonzero
      r
      s
      hZero


/-
The same remains true after any actually finite
number of refinements.
-/
theorem normalized_closure_one_impossible_after_any_finite_refinement
    (r : PositiveExactRadius)
    (k : U)
    (s : TraditionalPiPotentialStage)
    (I :
      NormalizedClosureIndicator
        r
        (finiteTraditionalPiIterate k s)) :

    I.value ≠ closureOne := by

  intro hOne

  have hZero :
      CorrectionZero
        (
          traditionalPiCircumferenceClosureDebt
            r
            (finiteTraditionalPiIterate k s)
        ) :=
    I.oneMeansZeroDebt hOne

  exact
    every_finite_continuation_has_nonzero_closure_debt
      r
      k
      s
      hZero


/-
Excel-style logical rule:

    IF exact_debt = 0 THEN 1

The converse branch need not be implemented in Lean.
We prove that the 1 branch is impossible.
-/
theorem excel_style_closure_one_impossible
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage)
    (value : U)
    (hSound :
      value = closureOne →
      CorrectionZero
        (traditionalPiCircumferenceClosureDebt r s)) :

    value ≠ closureOne := by

  intro hOne

  exact
    circumference_closure_debt_nonzero
      r
      s
      (hSound hOne)


structure TraditionalPiNormalizedClosureFinal
    (r : PositiveExactRadius) :
    Prop where

  noConstructedStageCanOutputOne :
    ∀
      (s : TraditionalPiPotentialStage)
      (I : NormalizedClosureIndicator r s),
      I.value ≠ closureOne

  noFiniteContinuationCanOutputOne :
    ∀
      (k : U)
      (s : TraditionalPiPotentialStage)
      (I :
        NormalizedClosureIndicator
          r
          (finiteTraditionalPiIterate k s)),
      I.value ≠ closureOne


theorem traditional_pi_normalized_closure_final
    (r : PositiveExactRadius) :

    TraditionalPiNormalizedClosureFinal r := by

  exact
    {
      noConstructedStageCanOutputOne :=
        normalized_closure_one_impossible r

      noFiniteContinuationCanOutputOne := by
        intro k s I
        exact
          normalized_closure_one_impossible_after_any_finite_refinement
            r k s I
    }


end PiQuasi
