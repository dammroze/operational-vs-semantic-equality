import PiQuasi.CompletedTotalityDemotion
import PiQuasi.CompletionNotAttainment

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. FINITE PRECISION IS NEVER AN ACTUAL COMPLETION
   ============================================================ -/

/-
Private precision counter.
Every precision value is finitely constructed.
-/
theorem u_next_ne_self :
    (u : U) → U.next u ≠ u

  | .zero => by
      intro h
      cases h

  | .next u => by
      intro h

      have hu :
          U.next u = u :=
        U.next.inj h

      exact
        u_next_ne_self u hu


/-
A finite machine word.

precision:
  arbitrary finite precision size.

payload:
  arbitrary finite radix numeral.

No IEEE semantics is needed for this impossibility result.
-/
structure FiniteFPWord : Type where
  precision : U
  payload : FiniteRadix


def increaseFPPrecision
    (w : FiniteFPWord) :
    FiniteFPWord :=
  {
    precision := .next w.precision
    payload := w.payload
  }


def PrecisionTerminal
    (w : FiniteFPWord) :
    Prop :=
  U.next w.precision = w.precision


theorem finite_precision_ne_terminal
    (w : FiniteFPWord) :
    ¬ PrecisionTerminal w := by

  exact
    u_next_ne_self
      w.precision


/-
Arbitrarily many, but finitely encoded,
precision increases.
-/
def increaseFPPrecisionMany
    (k : U)
    (w : FiniteFPWord) :
    FiniteFPWord :=
  match k with
  | .zero =>
      w

  | .next n =>
      increaseFPPrecision
        (increaseFPPrecisionMany n w)


theorem every_finitely_increased_precision_is_nonterminal
    (k : U)
    (w : FiniteFPWord) :
    ¬ PrecisionTerminal
      (increaseFPPrecisionMany k w) := by

  exact
    finite_precision_ne_terminal
      (increaseFPPrecisionMany k w)



/- ============================================================
   II. FINITE MACHINE REPRESENTATION OF A PI STAGE
   ============================================================ -/

/-
A finite machine representation is attached to one
actually available finite traditional-pi stage.
-/
structure FiniteFPPiExecution : Type where
  word : FiniteFPWord
  source : TraditionalPiPotentialStage


def fpPiObject
    (e : FiniteFPPiExecution) :
    TraditionalPiCompletionExtension :=
  TraditionalPiCompletionExtension.finite
    e.source


/-
Regardless of precision size or payload, the represented
source remains in the finite constructor.
-/
theorem finite_fp_source_ne_actual_completion
    (e : FiniteFPPiExecution) :
    fpPiObject e ≠
      TraditionalPiCompletionExtension.actualCompletion := by

  intro h

  exact
    pi_actual_completion_ne_finite
      e.source
      (Eq.symm h)


/-
Closure of the represented pi object.
-/
def FPPiClosed
    (e : FiniteFPPiExecution) :
    Prop :=
  CompletionClosed (fpPiObject e)


/-
No finite machine representation carries completion
closure, independently of its precision size.
-/
theorem finite_fp_pi_never_closed
    (e : FiniteFPPiExecution) :
    ¬ FPPiClosed e := by

  exact
    no_finite_pi_extension_is_closed
      e.source


/-
Increasing machine precision does not change the finite
pi source.
-/
def increaseExecutionPrecision
    (e : FiniteFPPiExecution) :
    FiniteFPPiExecution :=
  {
    word := increaseFPPrecision e.word
    source := e.source
  }


theorem increased_precision_still_not_closed
    (e : FiniteFPPiExecution) :
    ¬ FPPiClosed
      (increaseExecutionPrecision e) := by

  exact
    finite_fp_pi_never_closed
      (increaseExecutionPrecision e)


def increaseExecutionPrecisionMany
    (k : U)
    (e : FiniteFPPiExecution) :
    FiniteFPPiExecution :=
  match k with
  | .zero =>
      e

  | .next n =>
      increaseExecutionPrecision
        (increaseExecutionPrecisionMany n e)


/-
Core size-independent result:

after any finitely encoded number of precision increases,
closure is still impossible.
-/
theorem arbitrary_finite_precision_still_not_closed
    (k : U)
    (e : FiniteFPPiExecution) :
    ¬ FPPiClosed
      (increaseExecutionPrecisionMany k e) := by

  exact
    finite_fp_pi_never_closed
      (increaseExecutionPrecisionMany k e)


def SomeFinitePrecisionEventuallyCloses
    (e : FiniteFPPiExecution) :
    Prop :=
  ∃ k : U,
    FPPiClosed
      (increaseExecutionPrecisionMany k e)


theorem no_finite_precision_eventually_closes
    (e : FiniteFPPiExecution) :
    ¬ SomeFinitePrecisionEventuallyCloses e := by

  intro h

  cases h with
  | intro k hk =>
      exact
        arbitrary_finite_precision_still_not_closed
          k
          e
          hk



/- ============================================================
   III. MACHINE PRECISION CANNOT REPAIR THE WATER BALLOON
   ============================================================ -/

structure FPWrappedBalloon : Type where
  balloon : FinitePiWaterBalloon
  word : FiniteFPWord


/-
The machine layer does not replace the membrane.
Water-tightness still requires the underlying
geometric closure certificate.
-/
def FPWaterTight
    (b : FPWrappedBalloon) :
    Prop :=
  WaterTight b.balloon


def FPLeaks
    (b : FPWrappedBalloon) :
    Prop :=
  ¬ FPWaterTight b


theorem every_finite_fp_wrapped_balloon_leaks
    (b : FPWrappedBalloon) :
    FPLeaks b := by

  exact
    every_finite_traditional_pi_balloon_leaks
      b.balloon


def increaseBalloonPrecision
    (b : FPWrappedBalloon) :
    FPWrappedBalloon :=
  {
    balloon := b.balloon
    word := increaseFPPrecision b.word
  }


def increaseBalloonPrecisionMany
    (k : U)
    (b : FPWrappedBalloon) :
    FPWrappedBalloon :=
  match k with
  | .zero =>
      b

  | .next n =>
      increaseBalloonPrecision
        (increaseBalloonPrecisionMany n b)


theorem leakage_survives_any_finite_precision_increase
    (k : U)
    (b : FPWrappedBalloon) :
    FPLeaks
      (increaseBalloonPrecisionMany k b) := by

  exact
    every_finite_fp_wrapped_balloon_leaks
      (increaseBalloonPrecisionMany k b)


def FinitePrecisionRepairsLeakage
    (b : FPWrappedBalloon) :
    Prop :=
  ∃ k : U,
    FPWaterTight
      (increaseBalloonPrecisionMany k b)


theorem finite_precision_never_repairs_leakage
    (b : FPWrappedBalloon) :
    ¬ FinitePrecisionRepairsLeakage b := by

  intro h

  cases h with
  | intro k hk =>
      exact
        leakage_survives_any_finite_precision_increase
          k
          b
          hk



/- ============================================================
   IV. BOTTLENECK MONOTONICITY
   ============================================================ -/

/-
The finite machine layer cannot discharge the original
closure obligation.

This records monotonicity of the obstruction:
the original leakage theorem survives wrapping.
-/
structure FPBottleneckCertificate
    (b : FPWrappedBalloon) : Prop where

  baseLeakage :
    Leaks b.balloon

  wrappedLeakage :
    FPLeaks b


theorem fp_bottleneck_persists
    (b : FPWrappedBalloon) :
    FPBottleneckCertificate b := by

  exact
    {
      baseLeakage :=
        every_finite_traditional_pi_balloon_leaks
          b.balloon

      wrappedLeakage :=
        every_finite_fp_wrapped_balloon_leaks
          b
    }


/-
Precision growth cannot remove either obstruction.
-/
theorem fp_bottleneck_persists_after_any_finite_growth
    (k : U)
    (b : FPWrappedBalloon) :
    FPBottleneckCertificate
      (increaseBalloonPrecisionMany k b) := by

  exact
    fp_bottleneck_persists
      (increaseBalloonPrecisionMany k b)


end PiQuasi
