namespace PiQuasi

/-!
Concrete finite counterexample:

  explicit arbitrarily-small modulus
  DOES NOT imply
  finite exact zero attainment.

The witness is the exact magnitude of the finite
Gregory-Leibniz next correction

    4 / (2n + 3).

Everything below is generated from a private finite
successor type.  No completed infinite stage is introduced.
-/

inductive UFin : Type where
  | z : UFin
  | s : UFin → UFin

open UFin

def add : UFin → UFin → UFin
  | a, z   => a
  | a, s b => s (add a b)

def mul : UFin → UFin → UFin
  | _, z   => z
  | a, s b => add (mul a b) a

def one : UFin :=
  s z

def two : UFin :=
  s one

def three : UFin :=
  s two

def four : UFin :=
  s three

/-
Strict finite order, encoded by an explicit positive gap:

  a < b  iff  a + (gap + 1) = b

No host arithmetic is required.
-/
def FLt (a b : UFin) : Prop :=
  ∃ gap : UFin, add a (s gap) = b

inductive Polarity : Type where
  | plus
  | minus

def flip : Polarity → Polarity
  | .plus  => .minus
  | .minus => .plus

/-
For

  Δπ_n = (-1)^(n+1) 4/(2n+3),

stage zero is negative and every successor flips sign.
-/
def gregorySign : UFin → Polarity
  | z   => .minus
  | s n => flip (gregorySign n)

/-
Exact finite representation of 2n+3.

With the private addition convention this is

  n + (n + 3).
-/
def gregoryDen (n : UFin) : UFin :=
  add n (add n three)

structure SignedFracCode : Type where
  sign : Polarity
  num  : UFin
  den  : UFin

def gregoryDelta (n : UFin) : SignedFracCode :=
  {
    sign := gregorySign n
    num  := four
    den  := gregoryDen n
  }

/-
Exact zero means zero numerator.

No tolerance or representation-level approximation
is accepted as zero.
-/
def ExactZero (q : SignedFracCode) : Prop :=
  q.num = z

def FiniteZeroAttained
    (q : UFin → SignedFracCode) : Prop :=
  ∃ n : UFin, ExactZero (q n)

/-
Cross-multiplied exact smallness.

For positive precision p,

    p * num < den

is the finite rational inequality corresponding to

    num / den < 1 / p.

No division is used.
-/
def AbsSmallAt
    (p : UFin)
    (q : SignedFracCode) : Prop :=
  FLt (mul p q.num) q.den

/-
Explicit zero modulus:

for every requested positive finite precision p = k+1,
there exists a finite stage whose exact residual magnitude
is below 1/p.

This encodes arbitrary finite precision WITHOUT asserting
that any residual is zero.
-/
def ExplicitZeroModulus
    (q : UFin → SignedFracCode) : Prop :=
  ∀ k : UFin, ∃ n : UFin, AbsSmallAt (s k) (q n)

/-
Core finite arithmetic fact:

  n < 2n+3.

The positive gap is explicitly n+2.
-/
theorem self_lt_gregoryDen
    (n : UFin) :
    FLt n (gregoryDen n) := by
  refine ⟨add n two, ?_⟩
  rfl

theorem four_ne_zero :
    four ≠ z := by
  intro h
  cases h

/-
Every finite Gregory correction has numerator magnitude four.
Hence no constructed finite correction is exactly zero.
-/
theorem gregory_delta_nonzero
    (n : UFin) :
    ¬ ExactZero (gregoryDelta n) := by
  intro h
  exact four_ne_zero h

theorem gregory_no_finite_zero_attainment :
    ¬ FiniteZeroAttained gregoryDelta := by
  intro h
  rcases h with ⟨n, hn⟩
  exact gregory_delta_nonzero n hn

/-
For precision p = k+1 choose

  n = 4p.

Then

  p*4 = n < 2n+3.

Therefore the exact Gregory residual has an explicit
arbitrarily-fine finite zero modulus.
-/
theorem gregory_explicit_zero_modulus :
    ExplicitZeroModulus gregoryDelta := by
  intro k
  let p : UFin := s k
  let n : UFin := mul p four
  refine ⟨n, ?_⟩
  exact self_lt_gregoryDen n

/-
The decisive certificate:

the SAME exact finite Gregory construction has

  (1) arbitrary finite smallness, and
  (2) no finite exact zero stage.
-/
theorem gregory_modulus_and_nonattainment :
    ExplicitZeroModulus gregoryDelta
      ∧
    ¬ FiniteZeroAttained gregoryDelta := by
  exact ⟨
    gregory_explicit_zero_modulus,
    gregory_no_finite_zero_attainment
  ⟩

/-
Direct refutation of the universal bridge

  explicit zero modulus
      ->
  finite zero attainment.

The concrete counterexample is gregoryDelta.
-/
theorem explicit_zero_modulus_does_not_force_finite_attainment :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        ExplicitZeroModulus q →
        FiniteZeroAttained q
    ) := by
  intro bridge
  have h :
      FiniteZeroAttained gregoryDelta :=
    bridge gregoryDelta gregory_explicit_zero_modulus
  exact gregory_no_finite_zero_attainment h

/-
Equivalent implication-level formulation for the
specific traditional-pi correction.
-/
theorem gregory_zero_modulus_not_finite_zero :
    ExplicitZeroModulus gregoryDelta →
    ¬ FiniteZeroAttained gregoryDelta := by
  intro _
  exact gregory_no_finite_zero_attainment

#print axioms self_lt_gregoryDen
#print axioms gregory_delta_nonzero
#print axioms gregory_no_finite_zero_attainment
#print axioms gregory_explicit_zero_modulus
#print axioms gregory_modulus_and_nonattainment
#print axioms explicit_zero_modulus_does_not_force_finite_attainment
#print axioms gregory_zero_modulus_not_finite_zero


/-!
V2 — full finite-tail strengthening.

The previous theorem established:

  for every requested finite precision,
  some finite Gregory correction is small enough,

while no finite Gregory correction is exactly zero.

The result below strengthens "some stage" to an entire
successor tail:

  for every requested precision p,
  there is a finite N such that every stage N+t
  satisfies the requested exact smallness relation.

Thus the exact residual admits a constructive finite
tail modulus while never attaining exact zero.
-/

/-
Associativity of the private finite addition.
-/
theorem add_assoc_private
    (a b c : UFin) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | z =>
      rfl
  | s c ih =>
      change
        s (add (add a b) c) =
        s (add a (add b c))
      exact congrArg s ih

/-
If m is obtained from n by an arbitrary finite successor
extension t,

    m = n + t,

then n is still strictly below

    2m + 3.

This gives the monotone denominator fact needed for a
whole-tail modulus.
-/
theorem base_lt_gregoryDen_tail
    (n t : UFin) :
    FLt n (gregoryDen (add n t)) := by
  refine ⟨add t (add (add n t) two), ?_⟩

  change
    s (add n (add t (add (add n t) two))) =
    s (add (add n t) (add (add n t) two))

  apply congrArg s

  rw [← add_assoc_private]

/-
Whole-tail exact smallness.

For every positive finite requested precision p = k+1,
there is a finite boundary N such that every finite
successor extension N+t satisfies

    p * |q_(N+t)| < 1

in cross-multiplied fraction form.

For gregoryDelta, whose numerator magnitude is four,
this is exactly

    p*4 < denominator(N+t).
-/
def ExplicitTailZeroModulus
    (q : UFin → SignedFracCode) : Prop :=
  ∀ k : UFin,
    ∃ N : UFin,
      ∀ t : UFin,
        AbsSmallAt (s k) (q (add N t))

/-
Take

    p = k+1
    N = 4p.

For every finite t,

    N < 2(N+t)+3,

so every stage in the finite tail starting at N
has residual magnitude below 1/p.
-/
theorem gregory_explicit_tail_zero_modulus :
    ExplicitTailZeroModulus gregoryDelta := by
  intro k

  let p : UFin := s k
  let N : UFin := mul p four

  refine ⟨N, ?_⟩

  intro t

  change
    FLt N (gregoryDen (add N t))

  exact base_lt_gregoryDen_tail N t

/-
Operational constructive equivalence to exact zero.

This deliberately records the tail property directly
instead of quotienting sequences into a completed object.

No identification step changes any finite q n into zero.
-/
def ConstructiveTailEqZero
    (q : UFin → SignedFracCode) : Prop :=
  ExplicitTailZeroModulus q

theorem gregory_constructive_tail_eq_zero :
    ConstructiveTailEqZero gregoryDelta := by
  exact gregory_explicit_tail_zero_modulus

/-
The decisive conjunction.

The same exact sequence satisfies the full tail-to-zero
criterion and nevertheless has no exact-zero finite stage.
-/
theorem gregory_tail_equivalence_and_nonattainment :
    ConstructiveTailEqZero gregoryDelta
      ∧
    ¬ FiniteZeroAttained gregoryDelta := by
  exact ⟨
    gregory_constructive_tail_eq_zero,
    gregory_no_finite_zero_attainment
  ⟩

/-
Direct formal destruction of the proposed bridge:

  constructive tail-equivalence to zero
       ->
  some finite exact-zero stage.

The Gregory correction itself is the counterexample.
-/
theorem constructive_tail_eq_zero_does_not_force_finite_attainment :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        ConstructiveTailEqZero q →
        FiniteZeroAttained q
    ) := by
  intro bridge

  have h :
      FiniteZeroAttained gregoryDelta :=
    bridge
      gregoryDelta
      gregory_constructive_tail_eq_zero

  exact gregory_no_finite_zero_attainment h

/-
Even stronger formulation:

tail-equivalence can coexist permanently with
pointwise non-equality to exact zero.
-/
theorem tail_equivalence_with_pointwise_nonzero :
    ConstructiveTailEqZero gregoryDelta
      ∧
    (∀ n : UFin, ¬ ExactZero (gregoryDelta n)) := by
  constructor
  · exact gregory_constructive_tail_eq_zero
  · intro n
    exact gregory_delta_nonzero n

#print axioms add_assoc_private
#print axioms base_lt_gregoryDen_tail
#print axioms gregory_explicit_tail_zero_modulus
#print axioms gregory_constructive_tail_eq_zero
#print axioms gregory_tail_equivalence_and_nonattainment
#print axioms constructive_tail_eq_zero_does_not_force_finite_attainment
#print axioms tail_equivalence_with_pointwise_nonzero


/-!
V3 — SEMANTIC SEPARATION

We now distinguish explicitly:

  TailEqZero q

from

  StageEqZero q.

TailEqZero is the already-proved full finite-tail
arbitrary-precision criterion.

StageEqZero requires an actually constructed finite
stage whose exact numerator is zero.

The Gregory correction sequence satisfies the first
and refutes the second.

The final generic theorem then shows:

Any completion/equality semantics which accepts
TailEqZero as sufficient for "equality to zero"
cannot identify that semantic equality with
finite-stage attainment.
-/

/-
Exact equality attained at some constructed finite stage.
-/
def StageEqZero
    (q : UFin → SignedFracCode) : Prop :=
  FiniteZeroAttained q

/-
Full constructive tail equality criterion already established
in V2.
-/
def TailEqZero
    (q : UFin → SignedFracCode) : Prop :=
  ConstructiveTailEqZero q

theorem gregory_tail_eq_zero :
    TailEqZero gregoryDelta := by
  exact gregory_constructive_tail_eq_zero

theorem gregory_not_stage_eq_zero :
    ¬ StageEqZero gregoryDelta := by
  exact gregory_no_finite_zero_attainment

/-
Concrete semantic separation on the SAME mathematical source.
-/
theorem gregory_tail_eq_without_stage_eq :
    TailEqZero gregoryDelta
      ∧
    ¬ StageEqZero gregoryDelta := by
  exact ⟨
    gregory_tail_eq_zero,
    gregory_not_stage_eq_zero
  ⟩

/-
Direct refutation of the bridge

  TailEqZero -> StageEqZero.
-/
theorem tail_eq_zero_does_not_imply_stage_eq_zero :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        TailEqZero q →
        StageEqZero q
    ) := by
  intro bridge

  have hs :
      StageEqZero gregoryDelta :=
    bridge gregoryDelta gregory_tail_eq_zero

  exact gregory_not_stage_eq_zero hs

/-
Generic completion semantics.

CompletedEqZero is deliberately arbitrary.

It may represent:
  - a Cauchy setoid equality,
  - a quotient equality,
  - a constructive-real equality,
  - an externally added completion equality,
  - or any other completion semantics.

The only assumption is that this semantics accepts every
TailEqZero object as equal to zero.

Under that single assumption, semantic equality cannot
universally imply finite-stage equality.
-/
theorem completion_accepting_tail_zero_has_nonattained_equal_object
    (CompletedEqZero :
      (UFin → SignedFracCode) → Prop)
    (acceptsTail :
      ∀ q : UFin → SignedFracCode,
        TailEqZero q →
        CompletedEqZero q) :
    ∃ q : UFin → SignedFracCode,
      CompletedEqZero q
        ∧
      ¬ StageEqZero q := by

  refine ⟨gregoryDelta, ?_, ?_⟩

  · exact acceptsTail
      gregoryDelta
      gregory_tail_eq_zero

  · exact gregory_not_stage_eq_zero

/-
The strongest bridge-destruction form.

Any completion semantics which accepts tail-zero
cannot also satisfy universally:

  CompletedEqZero q -> StageEqZero q.
-/
theorem completion_eq_zero_does_not_force_finite_stage
    (CompletedEqZero :
      (UFin → SignedFracCode) → Prop)
    (acceptsTail :
      ∀ q : UFin → SignedFracCode,
        TailEqZero q →
        CompletedEqZero q) :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        CompletedEqZero q →
        StageEqZero q
    ) := by

  intro completionImpliesStage

  have hc :
      CompletedEqZero gregoryDelta :=
    acceptsTail
      gregoryDelta
      gregory_tail_eq_zero

  have hs :
      StageEqZero gregoryDelta :=
    completionImpliesStage
      gregoryDelta
      hc

  exact gregory_not_stage_eq_zero hs

/-
Equivalent incompatibility theorem:

A semantics cannot simultaneously

  (A) accept all full tail-zero sequences as zero

and

  (B) require every zero object to have a finite
      exact-zero stage.

The Gregory correction is the explicit obstruction.
-/
theorem tail_acceptance_incompatible_with_universal_stage_attainment :
    ¬ (
      ∃ CompletedEqZero :
          (UFin → SignedFracCode) → Prop,
        (∀ q : UFin → SignedFracCode,
          TailEqZero q →
          CompletedEqZero q)
        ∧
        (∀ q : UFin → SignedFracCode,
          CompletedEqZero q →
          StageEqZero q)
    ) := by

  intro h

  rcases h with
    ⟨CompletedEqZero, acceptsTail, impliesStage⟩

  have hc :
      CompletedEqZero gregoryDelta :=
    acceptsTail
      gregoryDelta
      gregory_tail_eq_zero

  have hs :
      StageEqZero gregoryDelta :=
    impliesStage
      gregoryDelta
      hc

  exact gregory_not_stage_eq_zero hs

/-
No completion semantics is required for the basic result.

The finite construction itself already exhibits:

  full tail-to-zero behavior
  AND
  permanent finite nonzero behavior.
-/
theorem finite_core_semantic_gap_certificate :
    TailEqZero gregoryDelta
      ∧
    (∀ n : UFin,
      ¬ ExactZero (gregoryDelta n)) := by

  exact ⟨
    gregory_tail_eq_zero,
    gregory_delta_nonzero
  ⟩

#print axioms gregory_tail_eq_zero
#print axioms gregory_not_stage_eq_zero
#print axioms gregory_tail_eq_without_stage_eq
#print axioms tail_eq_zero_does_not_imply_stage_eq_zero
#print axioms completion_accepting_tail_zero_has_nonattained_equal_object
#print axioms completion_eq_zero_does_not_force_finite_stage
#print axioms tail_acceptance_incompatible_with_universal_stage_attainment
#print axioms finite_core_semantic_gap_certificate


/-!
V4 — WITNESS EXTRACTION BARRIER

V3 established the semantic separation:

  TailEqZero q

does not imply

  StageEqZero q.

V4 strengthens this from proposition-level separation
to witness extraction.

Even when supplied with a proof of TailEqZero q,
there is no universal finite extractor capable of
returning a stage at which q is exactly zero.

The same result is then lifted to any completion
semantics which accepts TailEqZero.
-/

/-
The two notions are not universally equivalent.

The obstruction is the exact Gregory correction family.
-/
theorem tail_eq_zero_not_equivalent_to_stage_eq_zero :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        TailEqZero q ↔ StageEqZero q
    ) := by

  intro equivalence

  have hs :
      StageEqZero gregoryDelta :=
    (equivalence gregoryDelta).mp
      gregory_tail_eq_zero

  exact gregory_not_stage_eq_zero hs

/-
There is no universal finite stage extractor from a proof
of TailEqZero.

Such an extractor would have to accept gregoryDelta,
whose full tail criterion is already proved, and return
a stage whose exact correction is zero.

But every finite Gregory correction is nonzero.
-/
theorem no_tail_zero_finite_stage_extractor :
    ¬ (
      ∃ pick :
          (q : UFin → SignedFracCode) →
          TailEqZero q →
          UFin,
        ∀ (q : UFin → SignedFracCode)
          (h : TailEqZero q),
          ExactZero (q (pick q h))
    ) := by

  intro h

  rcases h with ⟨pick, hpick⟩

  have hz :
      ExactZero
        (gregoryDelta
          (pick
            gregoryDelta
            gregory_tail_eq_zero)) :=
    hpick
      gregoryDelta
      gregory_tail_eq_zero

  exact
    gregory_delta_nonzero
      (pick
        gregoryDelta
        gregory_tail_eq_zero)
      hz

/-
Generic completion version.

CompletedEqZero is arbitrary.

The only requirement is that every object satisfying
TailEqZero is accepted as semantically equal to zero.

Under that assumption, there cannot exist a universal
finite-stage extractor from semantic equality.
-/
theorem no_completion_zero_finite_stage_extractor
    (CompletedEqZero :
      (UFin → SignedFracCode) → Prop)
    (acceptsTail :
      ∀ q : UFin → SignedFracCode,
        TailEqZero q →
        CompletedEqZero q) :
    ¬ (
      ∃ pick :
          (q : UFin → SignedFracCode) →
          CompletedEqZero q →
          UFin,
        ∀ (q : UFin → SignedFracCode)
          (h : CompletedEqZero q),
          ExactZero (q (pick q h))
    ) := by

  intro h

  rcases h with ⟨pick, hpick⟩

  have hc :
      CompletedEqZero gregoryDelta :=
    acceptsTail
      gregoryDelta
      gregory_tail_eq_zero

  have hz :
      ExactZero
        (gregoryDelta
          (pick gregoryDelta hc)) :=
    hpick
      gregoryDelta
      hc

  exact
    gregory_delta_nonzero
      (pick gregoryDelta hc)
      hz

/-
Proposition-valued version of the same barrier.

A completion proof cannot universally be converted into
an existential finite attainment proof.
-/
theorem no_completion_zero_to_stage_attainment_bridge
    (CompletedEqZero :
      (UFin → SignedFracCode) → Prop)
    (acceptsTail :
      ∀ q : UFin → SignedFracCode,
        TailEqZero q →
        CompletedEqZero q) :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        CompletedEqZero q →
        ∃ n : UFin,
          ExactZero (q n)
    ) := by

  intro bridge

  have hc :
      CompletedEqZero gregoryDelta :=
    acceptsTail
      gregoryDelta
      gregory_tail_eq_zero

  have hs :
      ∃ n : UFin,
        ExactZero (gregoryDelta n) :=
    bridge
      gregoryDelta
      hc

  rcases hs with ⟨n, hn⟩

  exact
    gregory_delta_nonzero n hn

/-
The strongest concrete certificate required for the
current adversarial comparison.

The finite source simultaneously carries:

  a full tail-zero proof,

while every concrete finite stage remains exactly nonzero.
-/
theorem gregory_tail_proof_with_permanent_stage_failure :
    TailEqZero gregoryDelta
      ∧
    (∀ n : UFin,
      ¬ ExactZero (gregoryDelta n)) := by

  constructor

  · exact gregory_tail_eq_zero

  · exact gregory_delta_nonzero

/-
Having a total family over all finite stages does not
supply a terminal equality stage.

The family itself is explicit and total.
-/
def GregoryFiniteFamily :
    UFin → SignedFracCode :=
  gregoryDelta

theorem gregory_total_family_has_no_exact_zero_stage :
    ¬ (
      ∃ n : UFin,
        ExactZero (GregoryFiniteFamily n)
    ) := by

  intro h

  rcases h with ⟨n, hn⟩

  exact gregory_delta_nonzero n hn

#print axioms tail_eq_zero_not_equivalent_to_stage_eq_zero
#print axioms no_tail_zero_finite_stage_extractor
#print axioms no_completion_zero_finite_stage_extractor
#print axioms no_completion_zero_to_stage_attainment_bridge
#print axioms gregory_tail_proof_with_permanent_stage_failure
#print axioms gregory_total_family_has_no_exact_zero_stage


/-!
V5 — LITERAL CAUCHY-ZERO SEPARATION

The adversarial proposal appeals to Cauchy/regular-real
semantics.

We therefore define, directly and without Quotients, the
zero-equivalence relation relevant to the concrete claim.

A sequence is Cauchy-equivalent to zero here when:

  for every requested positive finite precision p,
  there is a finite boundary N such that every finite
  successor extension N+t has exact magnitude < 1/p.

This is precisely the full-tail modulus already proved
for the Gregory correction family.

Finite attainment is deliberately kept separate:

  some concrete finite stage has exact numerator zero.

The concrete Gregory family satisfies the first and
refutes the second.
-/

/-
Literal zero sequence in the finite fraction-code universe.
-/
def zeroFracCode : SignedFracCode :=
  {
    sign := .plus
    num  := z
    den  := one
  }

def zeroSequence :
    UFin → SignedFracCode :=
  fun _ => zeroFracCode

theorem zeroFracCode_exact :
    ExactZero zeroFracCode := by
  rfl

theorem zeroSequence_exact
    (n : UFin) :
    ExactZero (zeroSequence n) := by
  rfl

/-
Cauchy-style equality TO ZERO.

No quotient is introduced.

The relation is intentionally stated operationally:
arbitrary requested finite precision plus an entire
finite successor tail satisfying that precision.

For the current adversarial issue, this is exactly the
equality-to-zero direction needed.
-/
def CauchyEqZero
    (q : UFin → SignedFracCode) : Prop :=
  ∀ k : UFin,
    ∃ N : UFin,
      ∀ t : UFin,
        AbsSmallAt (s k) (q (add N t))

/-
The V2 tail theorem is literally a proof of
CauchyEqZero for the Gregory correction family.
-/
theorem gregory_cauchy_eq_zero :
    CauchyEqZero gregoryDelta := by
  exact gregory_explicit_tail_zero_modulus

/-
Yet no finite member of that same sequence is zero.
-/
theorem gregory_cauchy_zero_without_pointwise_zero :
    CauchyEqZero gregoryDelta
      ∧
    (∀ n : UFin,
      ¬ ExactZero (gregoryDelta n)) := by

  exact ⟨
    gregory_cauchy_eq_zero,
    gregory_delta_nonzero
  ⟩

/-
Therefore Cauchy equality to zero does not imply
finite zero attainment.
-/
theorem cauchy_eq_zero_does_not_imply_finite_zero :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        CauchyEqZero q →
        ∃ n : UFin,
          ExactZero (q n)
    ) := by

  intro bridge

  have h :
      ∃ n : UFin,
        ExactZero (gregoryDelta n) :=
    bridge
      gregoryDelta
      gregory_cauchy_eq_zero

  rcases h with ⟨n, hn⟩

  exact gregory_delta_nonzero n hn

/-
Likewise, there is no universal witness extractor from
a CauchyEqZero proof to an exact-zero finite stage.
-/
theorem no_cauchy_zero_finite_witness_extractor :
    ¬ (
      ∃ pick :
          (q : UFin → SignedFracCode) →
          CauchyEqZero q →
          UFin,
        ∀ (q : UFin → SignedFracCode)
          (h : CauchyEqZero q),
          ExactZero (q (pick q h))
    ) := by

  intro h

  rcases h with ⟨pick, hpick⟩

  have hz :
      ExactZero
        (gregoryDelta
          (pick
            gregoryDelta
            gregory_cauchy_eq_zero)) :=
    hpick
      gregoryDelta
      gregory_cauchy_eq_zero

  exact
    gregory_delta_nonzero
      (pick
        gregoryDelta
        gregory_cauchy_eq_zero)
      hz

/-
This records the semantic distinction without any
completion object whatsoever.
-/
def CauchySemanticZero
    (q : UFin → SignedFracCode) : Prop :=
  CauchyEqZero q

def FiniteOperationalZero
    (q : UFin → SignedFracCode) : Prop :=
  ∃ n : UFin,
    ExactZero (q n)

theorem gregory_semantic_zero_not_operational_zero :
    CauchySemanticZero gregoryDelta
      ∧
    ¬ FiniteOperationalZero gregoryDelta := by

  constructor

  · exact gregory_cauchy_eq_zero

  · intro h
    rcases h with ⟨n, hn⟩
    exact gregory_delta_nonzero n hn

/-
The two predicates cannot be universally identified.
-/
theorem cauchy_semantic_zero_not_universally_operational_zero :
    ¬ (
      ∀ q : UFin → SignedFracCode,
        CauchySemanticZero q ↔
        FiniteOperationalZero q
    ) := by

  intro h

  have hop :
      FiniteOperationalZero gregoryDelta :=
    (h gregoryDelta).mp
      gregory_cauchy_eq_zero

  exact
    gregory_semantic_zero_not_operational_zero.2
      hop

/-
A generic "completed real equality" may accept the
Cauchy criterion.

If it does, it cannot thereby provide finite attainment.
-/
theorem completed_equality_accepting_cauchy_has_nonattained_case
    (CompletedEqZero :
      (UFin → SignedFracCode) → Prop)
    (acceptsCauchy :
      ∀ q : UFin → SignedFracCode,
        CauchyEqZero q →
        CompletedEqZero q) :
    ∃ q : UFin → SignedFracCode,
      CompletedEqZero q
        ∧
      ¬ FiniteOperationalZero q := by

  refine ⟨gregoryDelta, ?_, ?_⟩

  · exact acceptsCauchy
      gregoryDelta
      gregory_cauchy_eq_zero

  · intro h
    rcases h with ⟨n, hn⟩
    exact gregory_delta_nonzero n hn

#print axioms zeroFracCode_exact
#print axioms zeroSequence_exact
#print axioms gregory_cauchy_eq_zero
#print axioms gregory_cauchy_zero_without_pointwise_zero
#print axioms cauchy_eq_zero_does_not_imply_finite_zero
#print axioms no_cauchy_zero_finite_witness_extractor
#print axioms gregory_semantic_zero_not_operational_zero
#print axioms cauchy_semantic_zero_not_universally_operational_zero
#print axioms completed_equality_accepting_cauchy_has_nonattained_case

end PiQuasi
