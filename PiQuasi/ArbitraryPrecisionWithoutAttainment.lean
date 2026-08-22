import PiQuasi.TraditionalPiPotential

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. DYADIC CONTROL MODEL

   This module deliberately does NOT concern pi.

   It formalizes the reviewer's geometric-series intuition:

       residual_n = 1 / 2^(n+1)

   Every finite refinement makes the denominator acquire one
   additional factor 2, while the exact numerator remains 1.

   Therefore arbitrary finite precision depth and exact
   non-attainment coexist.
   ============================================================ -/


def dyadicTwo : P :=
  P.next P.one


/-
Stage 0 denominator = 2.
Every successor multiplies the denominator by 2.

Thus, externally written:

    D_n = 2^(n+1).

No host exponentiation is used.
-/
def dyadicDenominator : U → P
  | .zero =>
      dyadicTwo

  | .next n =>
      pMul
        (dyadicDenominator n)
        dyadicTwo


theorem dyadic_denominator_successor
    (n : U) :

    dyadicDenominator (.next n)
    =
    pMul
      (dyadicDenominator n)
      dyadicTwo := by

  rfl


/-
Exact residual:

        1
    -----------
       D_n

with D_n = 2^(n+1) by recursive construction.
-/
def dyadicResidual
    (n : U) :
    ExactSignedFraction :=

  {
    num :=
      {
        pos := pToU P.one
        neg := U.zero
      }

    den :=
      dyadicDenominator n
  }


theorem dyadic_residual_denominator_formula
    (n : U) :

    (dyadicResidual n).den
    =
    dyadicDenominator n := by

  rfl


theorem dyadic_residual_numerator_formula
    (n : U) :

    (dyadicResidual n).num.pos
    =
    pToU P.one := by

  rfl


/- ============================================================
   II. EXACT NONZERO RESIDUAL
   ============================================================ -/


theorem dyadic_one_ne_zero :

    pToU P.one ≠ U.zero := by

  change U.next U.zero ≠ U.zero

  intro h
  cases h


theorem dyadic_residual_nonzero
    (n : U) :

    ¬ CorrectionZero
        (dyadicResidual n) := by

  intro h

  unfold CorrectionZero at h

  change
    pToU P.one = U.zero
    ∧
    U.zero = U.zero
    at h

  exact
    dyadic_one_ne_zero
      h.1


/- ============================================================
   III. FINITE PRECISION DEPTH
   ============================================================ -/

/-
FiniteDepthLE request stage means:

the actual stage has reached at least the requested finite
dyadic refinement depth.

This is a purely finite inductive relation.
-/
inductive FiniteDepthLE :
    U → U → Prop

  | refl (n : U) :
      FiniteDepthLE n n

  | step
      {request stage : U} :

      FiniteDepthLE request stage
      →
      FiniteDepthLE request (.next stage)


def DyadicPrecisionReached
    (request stage : U) :
    Prop :=

  FiniteDepthLE request stage


/-
For every finite requested depth there exists an actually
finite stage satisfying that request.

Choosing stage=request already suffices.
-/
theorem every_finite_dyadic_precision_request_is_reachable
    (request : U) :

    ∃ stage : U,
      DyadicPrecisionReached request stage := by

  exact
    ⟨request,
     FiniteDepthLE.refl request⟩


/-
And at that precision depth the residual is STILL exactly
nonzero.

This is the key review-control theorem.
-/
theorem every_finite_precision_request_has_nonzero_residual
    (request : U) :

    ∃ stage : U,

      DyadicPrecisionReached request stage
      ∧
      ¬ CorrectionZero
          (dyadicResidual stage) := by

  exact
    ⟨request,
     FiniteDepthLE.refl request,
     dyadic_residual_nonzero request⟩


/- ============================================================
   IV. ARBITRARY FINITE PRECISION
   ============================================================ -/

def ArbitraryFiniteDyadicPrecision :
    Prop :=

  ∀ request : U,

    ∃ stage : U,
      DyadicPrecisionReached request stage


theorem arbitrary_finite_dyadic_precision :

    ArbitraryFiniteDyadicPrecision := by

  intro request

  exact
    every_finite_dyadic_precision_request_is_reachable
      request


/- ============================================================
   V. EXACT FINITE ATTAINMENT
   ============================================================ -/

/-
The exact target would be attained at a finite stage only if
the exact residual became zero.
-/
def DyadicExactTargetAttained :
    Prop :=

  ∃ stage : U,
    CorrectionZero
      (dyadicResidual stage)


theorem no_dyadic_exact_target_attainment :

    ¬ DyadicExactTargetAttained := by

  intro h

  cases h with

  | intro stage hZero =>

      exact
        dyadic_residual_nonzero
          stage
          hZero


/- ============================================================
   VI. THE REVIEWER'S CENTRAL DISTINCTION, FORMALIZED

   Arbitrarily deep finite precision DOES NOT imply
   finite exact attainment.

   This is not a criticism of classical convergence.
   It is an exact separation of two propositions.
   ============================================================ -/

theorem arbitrary_finite_precision_does_not_imply_exact_attainment :

    ¬
    (
      ArbitraryFiniteDyadicPrecision
      →
      DyadicExactTargetAttained
    ) := by

  intro hImp

  have hAttained :
      DyadicExactTargetAttained :=

    hImp
      arbitrary_finite_dyadic_precision

  exact
    no_dyadic_exact_target_attainment
      hAttained


structure ArbitraryPrecisionWithoutAttainment :
    Prop where

  arbitraryFinitePrecision :
    ArbitraryFiniteDyadicPrecision

  everyRequestedDepthStillHasNonzeroResidual :
    ∀ request : U,

      ∃ stage : U,

        DyadicPrecisionReached request stage
        ∧
        ¬ CorrectionZero
            (dyadicResidual stage)

  noFiniteExactAttainment :
    ¬ DyadicExactTargetAttained


theorem arbitrary_precision_without_attainment :

    ArbitraryPrecisionWithoutAttainment := by

  exact
    {
      arbitraryFinitePrecision :=
        arbitrary_finite_dyadic_precision

      everyRequestedDepthStillHasNonzeroResidual :=
        every_finite_precision_request_has_nonzero_residual

      noFiniteExactAttainment :=
        no_dyadic_exact_target_attainment
    }


end PiQuasi
