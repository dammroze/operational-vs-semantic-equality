import PiQuasi.ArbitraryPrecisionWithoutAttainment
import PiQuasi.TraditionalPiUltradeterministCircumference

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. EXTERNAL LIMIT CLAIM

   LimitClaim is deliberately left external.

   It may stand for a classical theorem such as:

       lim P_n = pi

   provided by a richer semantic framework.

   This module does NOT deny or redefine that theorem.
   ============================================================ -/


def ExternalLimitImpliesPiFiniteAttainment
    (r : PositiveExactRadius)
    (LimitClaim : Prop) :
    Prop :=

  LimitClaim
  →
  TraditionalPiCircumferenceClosureWitness r


/-
Even if LimitClaim is explicitly granted as true,
it cannot imply finite exact stabilization, because finite
attainment has independently been proved impossible.
-/
theorem external_limit_claim_does_not_force_pi_finite_attainment
    (r : PositiveExactRadius)
    (LimitClaim : Prop)
    (hLimit : LimitClaim) :

    ¬ ExternalLimitImpliesPiFiniteAttainment
        r
        LimitClaim := by

  intro hImp

  have hAttainment :
      TraditionalPiCircumferenceClosureWitness r :=

    hImp hLimit

  exact
    no_traditional_pi_circumference_closure_witness
      r
      hAttainment


/- ============================================================
   II. EXTERNAL LIMIT CLAIM DOES NOT FORCE EVENTUAL
       FINITE STABILIZATION EITHER
   ============================================================ -/


def ExternalLimitImpliesPiEventualFiniteStabilization
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage)
    (LimitClaim : Prop) :
    Prop :=

  LimitClaim
  →
  EventuallyTraditionalPiCircumferenceClosed
    r
    s


theorem external_limit_claim_does_not_force_eventual_finite_stabilization
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage)
    (LimitClaim : Prop)
    (hLimit : LimitClaim) :

    ¬ ExternalLimitImpliesPiEventualFiniteStabilization
        r
        s
        LimitClaim := by

  intro hImp

  have hEventually :
      EventuallyTraditionalPiCircumferenceClosed
        r
        s :=

    hImp hLimit

  exact
    traditional_pi_circumference_never_eventually_closes
      r
      s
      hEventually


/- ============================================================
   III. THE SAME LOGICAL SEPARATION IN THE DYADIC
        CONTROL MODEL
   ============================================================ -/


def ExternalLimitImpliesDyadicFiniteAttainment
    (LimitClaim : Prop) :
    Prop :=

  LimitClaim
  →
  DyadicExactTargetAttained


theorem external_limit_claim_does_not_force_dyadic_finite_attainment
    (LimitClaim : Prop)
    (hLimit : LimitClaim) :

    ¬ ExternalLimitImpliesDyadicFiniteAttainment
        LimitClaim := by

  intro hImp

  have hAttainment :
      DyadicExactTargetAttained :=

    hImp hLimit

  exact
    no_dyadic_exact_target_attainment
      hAttainment


/- ============================================================
   IV. COMPATIBILITY PACKAGE

   The external limit claim can be granted while the formal
   system simultaneously retains:

   - arbitrary finite dyadic precision;
   - no exact dyadic finite attainment;
   - no traditional-pi finite stabilization;
   - no eventual finite stabilization.

   Therefore the paper's theorem is NOT:

       "classical convergence is false".

   It is:

       "classical convergence does not constitute
        finite attainment".
   ============================================================ -/


structure ExternalLimitCompatibleWithNoFiniteAttainment
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage)
    (LimitClaim : Prop) :
    Prop where

  externalLimitClaimGranted :
    LimitClaim

  arbitraryFiniteDyadicPrecision :
    ArbitraryFiniteDyadicPrecision

  dyadicExactFiniteAttainment :
    ¬ DyadicExactTargetAttained

  piFiniteExactAttainment :
    ¬ TraditionalPiCircumferenceClosureWitness r

  piEventualFiniteStabilization :
    ¬ EventuallyTraditionalPiCircumferenceClosed
        r
        s


theorem external_limit_compatible_with_no_finite_attainment
    (r : PositiveExactRadius)
    (s : TraditionalPiPotentialStage)
    (LimitClaim : Prop)
    (hLimit : LimitClaim) :

    ExternalLimitCompatibleWithNoFiniteAttainment
      r
      s
      LimitClaim := by

  exact
    {
      externalLimitClaimGranted :=
        hLimit

      arbitraryFiniteDyadicPrecision :=
        arbitrary_finite_dyadic_precision

      dyadicExactFiniteAttainment :=
        no_dyadic_exact_target_attainment

      piFiniteExactAttainment :=
        no_traditional_pi_circumference_closure_witness
          r

      piEventualFiniteStabilization :=
        traditional_pi_circumference_never_eventually_closes
          r
          s
    }


end PiQuasi
