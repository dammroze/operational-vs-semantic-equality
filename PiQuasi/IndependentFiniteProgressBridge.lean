import PiQuasi.IndependentClosureInterface

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. PRIVATE FINITE ADDITION CANCELLATION
   ============================================================ -/

theorem progress_uAdd_zero_left
    (a : U) :
    uAdd U.zero a = a := by

  induction a with

  | zero =>
      rfl

  | next a ih =>
      change U.next (uAdd U.zero a) = U.next a
      exact congrArg U.next ih


theorem progress_uAdd_next_left
    (a b : U) :
    uAdd (U.next a) b =
    U.next (uAdd a b) := by

  induction b with

  | zero =>
      rfl

  | next b ih =>
      change
        U.next (uAdd (U.next a) b) =
        U.next (U.next (uAdd a b))

      exact congrArg U.next ih


theorem progress_uAdd_comm
    (a b : U) :
    uAdd a b = uAdd b a := by

  induction b with

  | zero =>
      change a = uAdd U.zero a
      exact Eq.symm (progress_uAdd_zero_left a)

  | next b ih =>
      change
        U.next (uAdd a b) =
        uAdd (U.next b) a

      rw [progress_uAdd_next_left]

      exact congrArg U.next ih


theorem progress_uAdd_right_cancel
    (a b c : U) :
    uAdd a c = uAdd b c →
    a = b := by

  induction c with

  | zero =>
      intro h
      exact h

  | next c ih =>
      intro h

      change
        U.next (uAdd a c) =
        U.next (uAdd b c)
        at h

      have h' :
          uAdd a c =
          uAdd b c :=
        U.next.inj h

      exact ih h'


theorem progress_uAdd_eq_self_implies_zero
    (a b : U) :
    uAdd a b = a →
    b = U.zero := by

  intro h

  have hComm :
      uAdd b a = a := by
    rw [progress_uAdd_comm]
    exact h

  have hZero :
      uAdd U.zero a = a :=
    progress_uAdd_zero_left a

  have hSame :
      uAdd b a =
      uAdd U.zero a :=
    Eq.trans hComm (Eq.symm hZero)

  exact
    progress_uAdd_right_cancel
      b
      U.zero
      a
      hSame


theorem progress_uAdd_eq_zero_implies_right_zero
    (a b : U) :
    uAdd a b = U.zero →
    b = U.zero := by

  cases b with

  | zero =>
      intro _
      rfl

  | next b =>
      intro h

      change
        U.next (uAdd a b) =
        U.zero
        at h

      cases h


/- ============================================================
   II. POSITIVE FINITE SCALING CANNOT CREATE ZERO
   ============================================================ -/

/-
If multiplying an unsigned finite value by a
strictly positive finite value gives zero, then
the unsigned value itself was already zero.

No division or quotient is required.
-/
theorem progress_uMul_pToU_eq_zero_implies_left_zero
    (a : U)
    (p : P) :
    uMul a (pToU p) = U.zero →
    a = U.zero := by

  cases p with

  | one =>
      intro h

      change
        uAdd U.zero a =
        U.zero
        at h

      exact
        progress_uAdd_eq_zero_implies_right_zero
          U.zero
          a
          h

  | next p =>
      intro h

      change
        uAdd
          (uMul a (pToU p))
          a =
        U.zero
        at h

      exact
        progress_uAdd_eq_zero_implies_right_zero
          (uMul a (pToU p))
          a
          h


/- ============================================================
   III. EXACT SIGNED ADDITION CANCELLATION
   ============================================================ -/

/-
If adding one signed finite value leaves another
signed finite value structurally unchanged, then
both unsigned components of the added value are zero.

This follows from finite Peano cancellation only.
-/
theorem progress_signed_add_eq_self_implies_zero
    (a b : SignedFinite) :
    signedAdd a b = a →
    b.pos = U.zero ∧
    b.neg = U.zero := by

  intro h

  have hp :
      uAdd a.pos b.pos =
      a.pos := by

    have hp0 :=
      congrArg SignedFinite.pos h

    change
      uAdd a.pos b.pos =
      a.pos
      at hp0

    exact hp0


  have hn :
      uAdd a.neg b.neg =
      a.neg := by

    have hn0 :=
      congrArg SignedFinite.neg h

    change
      uAdd a.neg b.neg =
      a.neg
      at hn0

    exact hn0


  exact
    ⟨
      progress_uAdd_eq_self_implies_zero
        a.pos
        b.pos
        hp,

      progress_uAdd_eq_self_implies_zero
        a.neg
        b.neg
        hn
    ⟩


/- ============================================================
   IV. COMMON-DENOMINATOR FINITE PROGRESS GEOMETRY
   ============================================================ -/

/-
The next finite Gregory correction associated with
one already executed stage.
-/
def traditionalPiNextCorrection
    (s : TraditionalPiPotentialStage) :
    ExactSignedFraction :=
  gregoryPiTerm (.next s.index)


/-
Current numerator transported to the common
denominator used by exact addition with the next
Gregory correction.
-/
def traditionalPiProgressStart
    (s : TraditionalPiPotentialStage) :
    SignedFinite :=

  signedScale
    s.value.num
    (traditionalPiNextCorrection s).den


/-
The scaled numerator contributed by the next
Gregory correction.
-/
def traditionalPiProgressIncrement
    (s : TraditionalPiPotentialStage) :
    SignedFinite :=

  signedScale
    (traditionalPiNextCorrection s).num
    s.value.den


/-
Numerator after exact addition at that common
denominator.
-/
def traditionalPiProgressFinish
    (s : TraditionalPiPotentialStage) :
    SignedFinite :=

  signedAdd
    (traditionalPiProgressStart s)
    (traditionalPiProgressIncrement s)


/-
This is not the old spatial seam.

Its points are exact finite signed numerators
expressed at the common denominator naturally
generated by exactAdd.
-/
def TraditionalPiFiniteProgressGeometry :
    FiniteEndpointGeometry where

  Point :=
    SignedFinite

  start :=
    traditionalPiProgressStart

  finish :=
    traditionalPiProgressFinish


/-
Audit identity:

the finish endpoint is exactly the numerator
computed by adding the next Gregory correction
to the current exact finite stage.
-/
theorem traditional_pi_progress_finish_is_exact_add_numerator
    (s : TraditionalPiPotentialStage) :

    traditionalPiProgressFinish s =
    (
      exactAdd
        s.value
        (traditionalPiNextCorrection s)
    ).num := by

  rfl


/- ============================================================
   V. DERIVED BRIDGE: CLOSURE FORCES TERMINALITY
   ============================================================ -/

/-
This is the substantive bridge.

Endpoint closure is merely equality between the
common-denominator numerator before and after the
next exact Gregory correction.

TraditionalPiTerminal does not occur in the
definition of endpoint closure.

From equality, finite cancellation forces the
scaled correction numerator to zero.

Because its scaling denominator is strictly
positive, the original correction numerator
must already have been zero.
-/
theorem traditional_pi_progress_closure_forces_terminal
    (s : TraditionalPiPotentialStage) :

    EndpointClosed
      TraditionalPiFiniteProgressGeometry
      s →

    TraditionalPiTerminal s := by

  intro hClosed

  change
    traditionalPiProgressFinish s =
    traditionalPiProgressStart s
    at hClosed


  have hScaledZero :
      (traditionalPiProgressIncrement s).pos = U.zero
      ∧
      (traditionalPiProgressIncrement s).neg = U.zero :=

    progress_signed_add_eq_self_implies_zero
      (traditionalPiProgressStart s)
      (traditionalPiProgressIncrement s)
      hClosed


  have hpScaled :
      uMul
        (traditionalPiNextCorrection s).num.pos
        (pToU s.value.den) =
      U.zero := by

    exact hScaledZero.1


  have hnScaled :
      uMul
        (traditionalPiNextCorrection s).num.neg
        (pToU s.value.den) =
      U.zero := by

    exact hScaledZero.2


  have hp :
      (traditionalPiNextCorrection s).num.pos =
      U.zero :=

    progress_uMul_pToU_eq_zero_implies_left_zero
      (traditionalPiNextCorrection s).num.pos
      s.value.den
      hpScaled


  have hn :
      (traditionalPiNextCorrection s).num.neg =
      U.zero :=

    progress_uMul_pToU_eq_zero_implies_left_zero
      (traditionalPiNextCorrection s).num.neg
      s.value.den
      hnScaled


  unfold TraditionalPiTerminal
  unfold CorrectionZero
  unfold traditionalPiNextCorrection at hp hn

  exact ⟨hp, hn⟩


/-
The bridge required by the generic independent
closure interface is now constructed, rather than
postulated for this finite-progress geometry.
-/
def TraditionalPiFiniteProgressBridge :
    PiTerminalClosureBridge
      TraditionalPiFiniteProgressGeometry where

  closureForcesTerminal :=
    traditional_pi_progress_closure_forces_terminal


/- ============================================================
   VI. UNCONDITIONAL NON-CLOSURE OF THIS FINITE-PROGRESS MODEL
   ============================================================ -/

theorem traditional_pi_finite_progress_not_closed
    (s : TraditionalPiPotentialStage) :

    ¬ EndpointClosed
        TraditionalPiFiniteProgressGeometry
        s := by

  exact
    endpoint_closure_impossible_under_bridge
      TraditionalPiFiniteProgressGeometry
      TraditionalPiFiniteProgressBridge
      s


theorem no_traditional_pi_finite_progress_closure_witness :

    ¬ FiniteEndpointClosureWitness
        TraditionalPiFiniteProgressGeometry := by

  exact
    no_finite_endpoint_closure_witness_under_bridge
      TraditionalPiFiniteProgressGeometry
      TraditionalPiFiniteProgressBridge


/- ============================================================
   VII. EXPLICIT CLASSIFICATION
   ============================================================ -/

structure IndependentFiniteProgressBridgeResult : Prop where

  closureDefinitionIndependent :
    ∀ s : TraditionalPiPotentialStage,

      EndpointClosed
        TraditionalPiFiniteProgressGeometry
        s

      ↔

      traditionalPiProgressFinish s =
      traditionalPiProgressStart s

  closureForcesTerminal :
    ∀ s : TraditionalPiPotentialStage,

      EndpointClosed
        TraditionalPiFiniteProgressGeometry
        s →

      TraditionalPiTerminal s

  everyFiniteStageNonClosed :
    ∀ s : TraditionalPiPotentialStage,

      ¬ EndpointClosed
          TraditionalPiFiniteProgressGeometry
          s


theorem independent_finite_progress_bridge_result :
    IndependentFiniteProgressBridgeResult := by

  exact
    {
      closureDefinitionIndependent := by
        intro s
        rfl

      closureForcesTerminal :=
        traditional_pi_progress_closure_forces_terminal

      everyFiniteStageNonClosed :=
        traditional_pi_finite_progress_not_closed
    }


end PiQuasi
