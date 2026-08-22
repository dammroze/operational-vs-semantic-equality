import PiQuasi.SignedExact

set_option autoImplicit false

namespace PiQuasi


/-
Finite polynomial coefficient chain.

cons a rest represents

a + x * rest.

There is no constructor for an infinite coefficient chain.
-/
inductive Poly : Type where
  | nil : Poly
  | cons : ExactSignedFraction → Poly → Poly


def exactOne : ExactSignedFraction :=
  ⟨signedPositive (.next .zero), .one⟩


def polyZero : Poly :=
  .nil


def polyOne : Poly :=
  .cons exactOne .nil


def polyConst
    (a : ExactSignedFraction) :
    Poly :=
  .cons a .nil


/-
Multiply every coefficient by one exact scalar.
-/
def polyScale
    (c : ExactSignedFraction) :
    Poly → Poly
  | .nil =>
      .nil
  | .cons a rest =>
      .cons
        (exactMul c a)
        (polyScale c rest)


/-
Multiply by the formal variable x.
-/
def polyShift
    (p : Poly) :
    Poly :=
  .cons exactZero p


def polyAdd :
    Poly → Poly → Poly
  | .nil, q =>
      q

  | p, .nil =>
      p

  | .cons a as, .cons b bs =>
      .cons
        (exactAdd a b)
        (polyAdd as bs)


/-
Finite distributive multiplication.

(a + x A) Q
=
a Q + x (A Q).
-/
def polyMul :
    Poly → Poly → Poly
  | .nil, _ =>
      .nil

  | .cons a as, q =>
      polyAdd
        (polyScale a q)
        (polyShift (polyMul as q))


/-
Finite exponentiation indexed by the private
finite counter U.
-/
def polyPow
    (p : Poly) :
    U → Poly
  | .zero =>
      polyOne

  | .next k =>
      polyMul
        (polyPow p k)
        p


/-
Exact Horner evaluation.
-/
def polyEval
    (p : Poly)
    (x : ExactSignedFraction) :
    ExactSignedFraction :=
  match p with
  | .nil =>
      exactZero

  | .cons a rest =>
      exactAdd
        a
        (exactMul x (polyEval rest x))


/-
Embed a strictly positive finite multiplier
as an exact signed fraction.
-/
def positiveToExact
    (k : P) :
    ExactSignedFraction :=
  ⟨signedPositive (pToU k), .one⟩


def exactMulPositive
    (a : ExactSignedFraction)
    (k : P) :
    ExactSignedFraction :=
  exactMul a (positiveToExact k)


/-
The tail coefficients begin at degree one.

Input:

a1 + a2*x + a3*x^2 + ...

Output with starting multiplier k:

k*a1 + (k+1)*a2*x + ...
-/
def derivativeTail
    (k : P) :
    Poly → Poly
  | .nil =>
      .nil

  | .cons a rest =>
      .cons
        (exactMulPositive a k)
        (derivativeTail (.next k) rest)


/-
Formal finite derivative.

The constant coefficient is discarded.
-/
def polyDerivative :
    Poly → Poly
  | .nil =>
      .nil

  | .cons _ rest =>
      derivativeTail .one rest


/-
Repeated derivative, still indexed only by U.
-/
def polyDerivativeIter :
    U → Poly → Poly
  | .zero, p =>
      p

  | .next k, p =>
      polyDerivativeIter
        k
        (polyDerivative p)


/-
Two-coefficient polynomial:

c0 + c1*x.
-/
def polyLinear
    (c0 c1 : ExactSignedFraction) :
    Poly :=
  .cons c0 (.cons c1 .nil)


/-
Constructibility certificates.
-/
theorem poly_add_constructible
    (p q : Poly) :
    ∃ r : Poly,
      r = polyAdd p q := by
  exact ⟨polyAdd p q, rfl⟩


theorem poly_mul_constructible
    (p q : Poly) :
    ∃ r : Poly,
      r = polyMul p q := by
  exact ⟨polyMul p q, rfl⟩


theorem poly_pow_constructible
    (p : Poly)
    (k : U) :
    ∃ r : Poly,
      r = polyPow p k := by
  exact ⟨polyPow p k, rfl⟩


theorem poly_derivative_constructible
    (p : Poly) :
    ∃ r : Poly,
      r = polyDerivative p := by
  exact ⟨polyDerivative p, rfl⟩


theorem poly_derivative_iter_constructible
    (k : U)
    (p : Poly) :
    ∃ r : Poly,
      r = polyDerivativeIter k p := by
  exact ⟨polyDerivativeIter k p, rfl⟩


theorem poly_eval_constructible
    (p : Poly)
    (x : ExactSignedFraction) :
    ∃ z : ExactSignedFraction,
      z = polyEval p x := by
  exact ⟨polyEval p x, rfl⟩


end PiQuasi
