import PiQuasi.QuasiCircle
import PiQuasi.FiniteRadix

set_option autoImplicit false

namespace PiQuasi


def NoFractionPresentation
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    Prop :=
  ¬ HasFractionPresentation interpret target


def NoFiniteRadixPresentation
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    Prop :=
  ¬ HasFiniteRadixPresentation interpret target


/-
If an object cannot be represented by any finite
fraction, then it cannot have any exact finite
positional-radix representation.
-/
theorem no_fraction_implies_no_finite_radix
    {α : Type}
    (interpret : Fraction → α)
    (target : α)
    (hNoFraction :
      NoFractionPresentation interpret target) :
    NoFiniteRadixPresentation interpret target := by

  intro hRadix

  have hFraction :
      HasFractionPresentation interpret target :=
    finite_radix_implies_fraction
      interpret
      target
      hRadix

  exact hNoFraction hFraction


/-
An exact finite arc presentation carries both:

1. a finite construction stage;
2. an exact finite positional representation
   of the target value.
-/
structure ExactFiniteArcPresentation
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    Type where

  arc : FinitePiArc
  numeral : FiniteRadix

  exactValue :
    interpret (decodeFiniteRadix numeral) = target


/-
A closed exact finite presentation additionally
requires the finite closure certificate already
excluded by Gate 1.
-/
structure ExactFiniteClosedPresentation
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    Type where

  presentation :
    ExactFiniteArcPresentation interpret target

  closure :
    FinitePiClosureCertificate presentation.arc


/-
Non-fractionality already excludes every exact
finite arc presentation.
-/
theorem no_fraction_implies_no_exact_finite_arc
    {α : Type}
    (interpret : Fraction → α)
    (target : α)
    (hNoFraction :
      NoFractionPresentation interpret target) :
    ExactFiniteArcPresentation interpret target →
    False := by

  intro h

  apply hNoFraction

  exact
    ⟨ decodeFiniteRadix h.numeral,
      h.exactValue ⟩


/-
Consequently it excludes every exact finite
closed presentation.
-/
theorem no_fraction_implies_no_exact_finite_closed
    {α : Type}
    (interpret : Fraction → α)
    (target : α)
    (hNoFraction :
      NoFractionPresentation interpret target) :
    ExactFiniteClosedPresentation interpret target →
    False := by

  intro h

  exact
    no_fraction_implies_no_exact_finite_arc
      interpret
      target
      hNoFraction
      h.presentation


/-
Independent second obstruction:

even if an exact finite numerical presentation
were supplied, Gate 1 forbids the closure certificate.
-/
theorem no_exact_finite_closed_by_refinement
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    ExactFiniteClosedPresentation interpret target →
    False := by

  intro h

  exact
    no_finite_pi_closure
      h.presentation.arc
      h.closure


end PiQuasi
