import PiQuasi.FiniteRadixExclusion

set_option autoImplicit false

namespace PiQuasi


/-
Exact signed finite value represented as

  positivePart - negativePart.

No primitive subtraction is required.
-/
structure SignedFinite : Type where
  pos : U
  neg : U


def signedZero : SignedFinite :=
  ⟨.zero, .zero⟩


def signedPositive (a : U) : SignedFinite :=
  ⟨a, .zero⟩


def signedNegative (a : U) : SignedFinite :=
  ⟨.zero, a⟩


def signedNeg (a : SignedFinite) : SignedFinite :=
  ⟨a.neg, a.pos⟩


def signedAdd
    (a b : SignedFinite) :
    SignedFinite :=
  ⟨uAdd a.pos b.pos,
   uAdd a.neg b.neg⟩


/-
(a-b)(c-d)
=
(ac+bd) - (ad+bc)
-/
def signedMul
    (a b : SignedFinite) :
    SignedFinite :=
  ⟨
    uAdd
      (uMul a.pos b.pos)
      (uMul a.neg b.neg),

    uAdd
      (uMul a.pos b.neg)
      (uMul a.neg b.pos)
  ⟩


/-
Semantic equality without normalization.

(a-b) = (c-d)
iff
a+d = c+b.
-/
def SignedEq
    (a b : SignedFinite) :
    Prop :=
  uAdd a.pos b.neg =
  uAdd b.pos a.neg


theorem signed_eq_refl
    (a : SignedFinite) :
    SignedEq a a := by
  rfl


theorem signed_eq_symm
    (a b : SignedFinite) :
    SignedEq a b →
    SignedEq b a := by
  intro h
  exact Eq.symm h


theorem signed_neg_neg
    (a : SignedFinite) :
    signedNeg (signedNeg a) = a := by
  cases a
  rfl


theorem signed_add_zero_right
    (a : SignedFinite) :
    signedAdd a signedZero = a := by
  cases a
  rfl


/-
Scaling a signed value by a strictly positive
finite factor.
-/
def signedScale
    (a : SignedFinite)
    (p : P) :
    SignedFinite :=
  ⟨
    uMul a.pos (pToU p),
    uMul a.neg (pToU p)
  ⟩


/-
Exact signed fraction.

The denominator cannot be zero because P has
no zero constructor.
-/
structure ExactSignedFraction : Type where
  num : SignedFinite
  den : P


def exactZero : ExactSignedFraction :=
  ⟨signedZero, .one⟩


def exactNeg
    (a : ExactSignedFraction) :
    ExactSignedFraction :=
  ⟨signedNeg a.num, a.den⟩


def exactAdd
    (a b : ExactSignedFraction) :
    ExactSignedFraction :=
  ⟨
    signedAdd
      (signedScale a.num b.den)
      (signedScale b.num a.den),

    pMul a.den b.den
  ⟩


def exactMul
    (a b : ExactSignedFraction) :
    ExactSignedFraction :=
  ⟨
    signedMul a.num b.num,
    pMul a.den b.den
  ⟩


/-
a/b = c/d
iff
a*d = c*b

where equality of signed numerators is itself
implemented by finite unsigned arithmetic.
-/
def ExactEq
    (a b : ExactSignedFraction) :
    Prop :=
  SignedEq
    (signedScale a.num b.den)
    (signedScale b.num a.den)


theorem exact_eq_refl
    (a : ExactSignedFraction) :
    ExactEq a a := by
  exact signed_eq_refl
    (signedScale a.num a.den)


theorem exact_eq_symm
    (a b : ExactSignedFraction) :
    ExactEq a b →
    ExactEq b a := by
  intro h
  exact signed_eq_symm
    (signedScale a.num b.den)
    (signedScale b.num a.den)
    h


/-
Embed the unsigned finite fraction already
certified in Gate 2A.
-/
def fractionToExact
    (q : Fraction) :
    ExactSignedFraction :=
  ⟨signedPositive q.num, q.den⟩


theorem finite_fraction_has_exact_signed_form
    (q : Fraction) :
    ∃ z : ExactSignedFraction,
      z = fractionToExact q := by
  exact ⟨fractionToExact q, rfl⟩


/-
Every finite radix numeral therefore has an
explicit exact signed-fraction value.
-/
def decodeFiniteRadixExact
    (x : FiniteRadix) :
    ExactSignedFraction :=
  fractionToExact (decodeFiniteRadix x)


theorem finite_radix_has_exact_signed_form
    (x : FiniteRadix) :
    ∃ z : ExactSignedFraction,
      z = decodeFiniteRadixExact x := by
  exact ⟨decodeFiniteRadixExact x, rfl⟩


end PiQuasi
