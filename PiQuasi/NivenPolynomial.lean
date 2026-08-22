import PiQuasi.FinitePolynomial

set_option autoImplicit false

namespace PiQuasi


/-
Finite successor converted directly into the
strictly positive counting domain.
-/
def succUToP : U → P
  | .zero =>
      .one
  | .next k =>
      .next (succUToP k)


/-
Strictly positive finite power.
-/
def pPow
    (a : P) :
    U → P
  | .zero =>
      .one
  | .next k =>
      pMul (pPow a k) a


/-
Finite factorial.
Every result is strictly positive by type.
-/
def factorial : U → P
  | .zero =>
      .one
  | .next k =>
      pMul
        (factorial k)
        (succUToP k)


/-
Exact positive ratio p/q.
-/
def positiveRatio
    (p q : P) :
    ExactSignedFraction :=
  ⟨signedPositive (pToU p), q⟩


/-
The formal variable x.
-/
def polyX : Poly :=
  .cons
    exactZero
    (.cons exactOne .nil)


/-
a - b*x
-/
def polyAminusBX
    (a b : P) :
    Poly :=
  polyLinear
    (positiveToExact a)
    (exactNeg (positiveToExact b))


/-
Raw Niven factor:

x^k * (a - b*x)^k
-/
def nivenRaw
    (a b : P)
    (k : U) :
    Poly :=
  polyMul
    (polyPow polyX k)
    (polyPow (polyAminusBX a b) k)


/-
Classical Niven scaling factor under the
temporary algebraic relation a = b*pi:

b^k / k!
-/
def nivenScale
    (b : P)
    (k : U) :
    ExactSignedFraction :=
  positiveRatio
    (pPow b k)
    (factorial k)


/-
Finite auxiliary Niven polynomial:

f_k(x)
 =
(b^k / k!)
x^k
(a - b*x)^k

No completed infinite object occurs here.
-/
def nivenPolynomial
    (a b : P)
    (k : U) :
    Poly :=
  polyScale
    (nivenScale b k)
    (nivenRaw a b k)


theorem factorial_constructible
    (k : U) :
    ∃ p : P,
      p = factorial k := by
  exact ⟨factorial k, rfl⟩


theorem positive_power_constructible
    (b : P)
    (k : U) :
    ∃ p : P,
      p = pPow b k := by
  exact ⟨pPow b k, rfl⟩


theorem niven_raw_constructible
    (a b : P)
    (k : U) :
    ∃ p : Poly,
      p = nivenRaw a b k := by
  exact ⟨nivenRaw a b k, rfl⟩


theorem niven_scale_constructible
    (b : P)
    (k : U) :
    ∃ z : ExactSignedFraction,
      z = nivenScale b k := by
  exact ⟨nivenScale b k, rfl⟩


theorem niven_polynomial_constructible
    (a b : P)
    (k : U) :
    ∃ p : Poly,
      p = nivenPolynomial a b k := by
  exact ⟨nivenPolynomial a b k, rfl⟩


theorem niven_polynomial_is_scaled_product
    (a b : P)
    (k : U) :
    nivenPolynomial a b k =
      polyScale
        (positiveRatio
          (pPow b k)
          (factorial k))
        (polyMul
          (polyPow polyX k)
          (polyPow
            (polyAminusBX a b)
            k)) := by
  rfl


end PiQuasi
