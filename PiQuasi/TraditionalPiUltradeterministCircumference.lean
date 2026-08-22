import PiQuasi.IndependentFiniteProgressBridge

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. POSITIVE EXACT RADIUS
   ============================================================ -/

structure PositiveExactRadius : Type where
  num : P
  den : P


/-
2a in the project's strictly-positive finite arithmetic.
-/
def circumferenceDoublePositive
    (a : P) :
    P :=
  pAdd a a


/- ============================================================
   II. FINITE ITERATION ONLY
   ============================================================ -/

/-
There is deliberately no stage "at infinity".

Every construction stage is reached by an actually
finite U-valued iteration count.
-/
def finiteTraditionalPiIterate :
    U →
    TraditionalPiPotentialStage →
    TraditionalPiPotentialStage

  | .zero, s =>
      s

  | .next k, s =>
      refineTraditionalPi
        (finiteTraditionalPiIterate k s)


/- ============================================================
   III. EXACT CIRCUMFERENCE CLOSURE DEBT
   ============================================================ -/

/-
Let

        r = a / b

and let the next Gregory correction after stage n be

                   ±4
        Δπ_n = -----------
                 2n + 3.

For circumference

        C = 2 r π,

the induced exact next correction is

                   ±8a
        ΔC_n = ----------------.
                 b (2n + 3)

The implementation below contains no division and no
floating point.

The signed ±4 numerator is scaled by the positive
finite factor 2a and the odd Gregory denominator is
multiplied by b.
-/
def traditionalPiCircumferenceClosureDebt
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :
    ExactSignedFraction :=

  {
    num :=
      signedScale
        (gregoryPiTerm (.next s.index)).num
        (circumferenceDoublePositive r.num)

    den :=
      pMul
        (gregoryPiTerm (.next s.index)).den
        r.den
  }


/- ============================================================
   IV. EXACT FORMULA AUDIT
   ============================================================ -/

theorem circumference_debt_numerator_formula
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    (traditionalPiCircumferenceClosureDebt r s).num
    =
    signedScale
      (gregoryPiTerm (.next s.index)).num
      (circumferenceDoublePositive r.num) := by

  rfl


theorem circumference_debt_denominator_formula
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    (traditionalPiCircumferenceClosureDebt r s).den
    =
    pMul
      (oddDenom (.next s.index))
      r.den := by

  unfold traditionalPiCircumferenceClosureDebt
  unfold gregoryPiTerm

  cases h : altSign (.next s.index) with

  | pos =>
      rfl

  | neg =>
      rfl


theorem circumference_debt_sign_formula
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    (traditionalPiCircumferenceClosureDebt r s).num
    =
    match altSign (.next s.index) with

    | .pos =>
        signedScale
          (signedPositive uFour)
          (circumferenceDoublePositive r.num)

    | .neg =>
        signedScale
          (signedNegative uFour)
          (circumferenceDoublePositive r.num) := by

  unfold traditionalPiCircumferenceClosureDebt
  unfold gregoryPiTerm

  cases h : altSign (.next s.index) with

  | pos =>
      rfl

  | neg =>
      rfl


/- ============================================================
   V. ZERO DEBT WOULD FORCE A TERMINAL PI STAGE
   ============================================================ -/

theorem circumference_debt_zero_forces_terminal
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    CorrectionZero
      (traditionalPiCircumferenceClosureDebt r s)

    →

    TraditionalPiTerminal s := by

  intro hZero

  have hpScaled :
      uMul
        (gregoryPiTerm (.next s.index)).num.pos
        (pToU (circumferenceDoublePositive r.num))
      =
      U.zero := by

    exact hZero.1


  have hnScaled :
      uMul
        (gregoryPiTerm (.next s.index)).num.neg
        (pToU (circumferenceDoublePositive r.num))
      =
      U.zero := by

    exact hZero.2


  have hp :
      (gregoryPiTerm (.next s.index)).num.pos
      =
      U.zero :=

    progress_uMul_pToU_eq_zero_implies_left_zero
      (gregoryPiTerm (.next s.index)).num.pos
      (circumferenceDoublePositive r.num)
      hpScaled


  have hn :
      (gregoryPiTerm (.next s.index)).num.neg
      =
      U.zero :=

    progress_uMul_pToU_eq_zero_implies_left_zero
      (gregoryPiTerm (.next s.index)).num.neg
      (circumferenceDoublePositive r.num)
      hnScaled


  change
    (gregoryPiTerm (.next s.index)).num.pos = U.zero
    ∧
    (gregoryPiTerm (.next s.index)).num.neg = U.zero

  exact ⟨hp, hn⟩


/- ============================================================
   VI. EVERY CONSTRUCTED STAGE HAS NONZERO CLOSURE DEBT
   ============================================================ -/

theorem circumference_closure_debt_nonzero
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    ¬ CorrectionZero
        (traditionalPiCircumferenceClosureDebt r s) := by

  intro hZero

  have hTerminal :
      TraditionalPiTerminal s :=

    circumference_debt_zero_forces_terminal
      r
      s
      hZero

  exact
    traditional_pi_stage_ne_terminal
      s
      hTerminal


/- ============================================================
   VII. CIRCUMFERENCE CLOSURE
   ============================================================ -/

/-
Within this construction, exact circumference closure
at a stage would require the next exact induced
circumference correction to be zero.

No epsilon or tolerance appears here.
-/
def TraditionalPiCircumferenceClosed
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :
    Prop :=

  CorrectionZero
    (traditionalPiCircumferenceClosureDebt r s)


theorem no_constructed_stage_closes_circumference
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    ¬ TraditionalPiCircumferenceClosed r s := by

  exact
    circumference_closure_debt_nonzero
      r
      s


/- ============================================================
   VIII. NO FINITE CLOSURE WITNESS
   ============================================================ -/

def TraditionalPiCircumferenceClosureWitness
    (r : PositiveExactRadius) :
    Prop :=

  ∃ s : TraditionalPiPotentialStage,
    TraditionalPiCircumferenceClosed r s


theorem no_traditional_pi_circumference_closure_witness
    (r : PositiveExactRadius) :

    ¬ TraditionalPiCircumferenceClosureWitness r := by

  intro h

  cases h with

  | intro s hs =>

      exact
        no_constructed_stage_closes_circumference
          r
          s
          hs


/- ============================================================
   IX. ANY FINITE CONTINUATION STILL FAILS TO CLOSE
   ============================================================ -/

theorem every_finite_continuation_has_nonzero_closure_debt
    (r : PositiveExactRadius)
    (k : U)
    (s : TraditionalPiPotentialStage) :

    ¬ CorrectionZero
        (
          traditionalPiCircumferenceClosureDebt
            r
            (finiteTraditionalPiIterate k s)
        ) := by

  exact
    circumference_closure_debt_nonzero
      r
      (finiteTraditionalPiIterate k s)


theorem every_finite_continuation_remains_nonclosed
    (r : PositiveExactRadius)
    (k : U)
    (s : TraditionalPiPotentialStage) :

    ¬ TraditionalPiCircumferenceClosed
        r
        (finiteTraditionalPiIterate k s) := by

  exact
    every_finite_continuation_has_nonzero_closure_debt
      r
      k
      s


/- ============================================================
   X. NO EVENTUAL FINITE CLOSURE
   ============================================================ -/

def EventuallyTraditionalPiCircumferenceClosed
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :
    Prop :=

  ∃ k : U,
    TraditionalPiCircumferenceClosed
      r
      (finiteTraditionalPiIterate k s)


theorem traditional_pi_circumference_never_eventually_closes
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage) :

    ¬ EventuallyTraditionalPiCircumferenceClosed r s := by

  intro h

  cases h with

  | intro k hk =>

      exact
        every_finite_continuation_remains_nonclosed
          r
          k
          s
          hk


/- ============================================================
   XI. ULTRA-DETERMINIST FINAL RESULT
   ============================================================ -/

/-
No actual-infinite constructor is introduced.

The statement quantifies only over actually finite
construction stages.

For every such stage, and after every finite number
of further refinements, the exact induced
circumference closure debt remains nonzero.
-/
structure TraditionalPiUltradeterministCircumferenceNonclosure
    (r : PositiveExactRadius) :
    Prop where

  everyConstructedStageHasNonzeroDebt :
    ∀ s : TraditionalPiPotentialStage,

      ¬ CorrectionZero
          (traditionalPiCircumferenceClosureDebt r s)

  noConstructedClosureWitness :
    ¬ TraditionalPiCircumferenceClosureWitness r

  everyFiniteContinuationHasNonzeroDebt :
    ∀
      (k : U)
      (s : TraditionalPiPotentialStage),

      ¬ CorrectionZero
          (
            traditionalPiCircumferenceClosureDebt
              r
              (finiteTraditionalPiIterate k s)
          )

  noEventualFiniteClosure :
    ∀ s : TraditionalPiPotentialStage,

      ¬ EventuallyTraditionalPiCircumferenceClosed
          r
          s


theorem traditional_pi_ultradeterminist_circumference_nonclosure
    (r : PositiveExactRadius) :

    TraditionalPiUltradeterministCircumferenceNonclosure r := by

  exact
    {
      everyConstructedStageHasNonzeroDebt :=
        circumference_closure_debt_nonzero r

      noConstructedClosureWitness :=
        no_traditional_pi_circumference_closure_witness r

      everyFiniteContinuationHasNonzeroDebt := by
        intro k s

        exact
          every_finite_continuation_has_nonzero_closure_debt
            r
            k
            s

      noEventualFiniteClosure := by
        intro s

        exact
          traditional_pi_circumference_never_eventually_closes
            r
            s
    }


end PiQuasi
