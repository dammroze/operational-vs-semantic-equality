import PiQuasi.PotentiallyUnboundedFluidLeakage

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. EXACT NO-ESCAPE REQUIREMENT
   ============================================================ -/

/-
Exact operational containment means:

for no finitely represented initial delay and
no finite execution time may an escape certificate
be produced.

No probability, tolerance, epsilon, or approximate
equality occurs in this predicate.
-/
def NoFiniteOperationalEscape
    (openBoundary : Prop) :
    Prop :=

  ∀ delay time : U,
    ¬ OperationalEscapeAt
      openBoundary
      delay
      time


/-
An open boundary satisfying the finite transport rule
cannot satisfy exact no-escape containment.
-/
theorem open_boundary_not_exactly_no_escape
    (openBoundary : Prop)
    (hOpen : openBoundary) :
    ¬ NoFiniteOperationalEscape openBoundary := by

  intro hSafe

  have hEscape :
      OperationalEscapeAt
        openBoundary
        U.zero
        (.next U.zero) :=

    open_boundary_escape_after_any_finite_delay
      openBoundary
      hOpen
      U.zero

  exact
    hSafe
      U.zero
      (.next U.zero)
      hEscape


/- ============================================================
   II. SAFETY-CRITICAL CERTIFICATION POLICY
   ============================================================ -/

/-
A safety-critical policy is deliberately abstract.

No spacecraft, diving system, pressure value, material,
or physical law is built into the theorem.

The only policy condition represented here is:

if the system is certified admissible, then the adopted
operational model must certify absence of every finite
escape.
-/
structure ExactContainmentSafetyPolicy
    (openBoundary : Prop) : Type where

  admissible : Prop

  admissibleRequiresNoFiniteEscape :
    admissible →
    NoFiniteOperationalEscape openBoundary


theorem open_boundary_rejected_by_exact_safety_policy
    (openBoundary : Prop)
    (hOpen : openBoundary)
    (P : ExactContainmentSafetyPolicy openBoundary) :
    ¬ P.admissible := by

  intro hAdmissible

  have hNoEscape :
      NoFiniteOperationalEscape openBoundary :=
    P.admissibleRequiresNoFiniteEscape
      hAdmissible

  exact
    open_boundary_not_exactly_no_escape
      openBoundary
      hOpen
      hNoEscape


/- ============================================================
   III. PI OPERATIONAL-SEAM INSTANCE
   ============================================================ -/

theorem spatial_pi_operational_model_not_exactly_no_escape
    (s : TraditionalPiPotentialStage) :
    ¬ NoFiniteOperationalEscape
        (SpatialPiOpenBoundary s) := by

  exact
    open_boundary_not_exactly_no_escape
      (SpatialPiOpenBoundary s)
      (spatial_pi_boundary_open s)


theorem spatial_pi_operational_model_rejected_by_exact_safety_policy
    (s : TraditionalPiPotentialStage)
    (P :
      ExactContainmentSafetyPolicy
        (SpatialPiOpenBoundary s)) :
    ¬ P.admissible := by

  exact
    open_boundary_rejected_by_exact_safety_policy
      (SpatialPiOpenBoundary s)
      (spatial_pi_boundary_open s)
      P


/- ============================================================
   IV. POTENTIALLY UNBOUNDED DELAY DOES NOT RESTORE SAFETY
   ============================================================ -/

/-
Exact containment cannot be restored by increasing
a finite delay.

The already-proved potential-unboundedness theorem
shows that arbitrarily large finite modeled delays
remain compatible with a later finite escape.
-/
theorem potentially_unbounded_delay_does_not_restore_exact_containment
    (s : TraditionalPiPotentialStage) :

    PotentiallyUnboundedOperationalLeakage
      (SpatialPiOpenBoundary s)

    ∧

    ¬ NoFiniteOperationalEscape
        (SpatialPiOpenBoundary s) := by

  constructor

  · exact
      spatial_pi_model_potentially_unbounded_operational_leakage
        s

  · exact
      spatial_pi_operational_model_not_exactly_no_escape
        s


end PiQuasi
