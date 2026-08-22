set_option autoImplicit false

namespace PiQuasi

/-
Private finite counting object.
No built-in natural-number type is used.
-/
inductive U : Type where
  | zero : U
  | next : U → U

/-
Strictly positive finite counting object.
one = 1
next p = p + 1
-/
inductive P : Type where
  | one : P
  | next : P → P


/-- finite unsigned addition -/
def uAdd : U → U → U
  | a, .zero   => a
  | a, .next b => .next (uAdd a b)

/-- finite unsigned multiplication -/
def uMul : U → U → U
  | _, .zero   => .zero
  | a, .next b => uAdd (uMul a b) a


/-- positive value embedded into U -/
def pToU : P → U
  | .one    => .next .zero
  | .next p => .next (pToU p)

/-- addition on strictly positive values -/
def pAdd : P → P → P
  | .one, b    => .next b
  | .next a, b => .next (pAdd a b)

/-- multiplication on strictly positive values -/
def pMul : P → P → P
  | .one, b    => b
  | .next a, b => pAdd (pMul a b) b


/-
A finite fraction is represented without division
and without quotient types.

num / den

The denominator is positive by construction.
-/
structure Fraction : Type where
  num : U
  den : P


/-
A finite positional numeral.

whole . d1 d2 ... dk  (base B)

The list itself is inductively finite.
-/
structure FiniteRadix : Type where
  base  : P
  whole : U
  frac  : List U


/-
Appending one radix digit transforms

N / D

into

(N*B + digit) / (D*B).
-/
def radixStep
    (base : P)
    (q : Fraction)
    (digit : U) :
    Fraction :=
  {
    num := uAdd (uMul q.num (pToU base)) digit
    den := pMul q.den base
  }


/-
Finite evaluator over the finite digit list.
-/
def evalDigits
    (base : P) :
    List U → Fraction → Fraction
  | [], q      => q
  | d :: ds, q => evalDigits base ds (radixStep base q d)


/-
Exact decoding of a finite radix numeral into
a finite fraction representation.
-/
def decodeFiniteRadix
    (x : FiniteRadix) :
    Fraction :=
  evalDigits
    x.base
    x.frac
    {
      num := x.whole
      den := .one
    }


/-
No existential/classical choice is needed:
the rational witness is computed directly.
-/
theorem finite_radix_has_fraction
    (x : FiniteRadix) :
    ∃ q : Fraction,
      q = decodeFiniteRadix x := by
  exact ⟨decodeFiniteRadix x, rfl⟩


/-
Generic semantic bridge.

The target domain α is arbitrary.
interpret gives the mathematical meaning of an
exact finite fraction inside α.
-/
def HasFiniteRadixPresentation
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    Prop :=
  ∃ x : FiniteRadix,
    interpret (decodeFiniteRadix x) = target


def HasFractionPresentation
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    Prop :=
  ∃ q : Fraction,
    interpret q = target


/-
Central Gate 2A theorem:

If any mathematical object has an exact finite-radix
presentation, then it has an exact finite-fraction
presentation.

No property of pi is assumed here.
-/
theorem finite_radix_implies_fraction
    {α : Type}
    (interpret : Fraction → α)
    (target : α) :
    HasFiniteRadixPresentation interpret target →
    HasFractionPresentation interpret target := by
  intro h
  cases h with
  | intro x hx =>
      exact ⟨decodeFiniteRadix x, hx⟩

end PiQuasi
