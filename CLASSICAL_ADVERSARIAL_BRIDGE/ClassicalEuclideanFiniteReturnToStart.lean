import ClassicalEuclideanGregoryBridge
import ClassicalEuclideanTraversalStep
import ClassicalEuclideanGregoryStageBridge

namespace PiQuasiClassicalBridge

/-!
V1.5.3-A

Reviewer-hardening theorem.

The existing V1.5 classical layer proves:

  * every finite Gregory stage is rational and differs from Real.pi;
  * every finite Gregory circumference differs from 2*r*pi;
  * consecutive finite Gregory-generated Euclidean endpoints differ.

The present module closes the stronger question:

Can a nontrivial finite Gregory circumference stage return exactly
to the initial Euclidean point, even if it does not stabilize there?

Answer: no.

The proof has two parts.

A1. Every nonempty Gregory partial sum is strictly positive.

A2. Equality of the corresponding Euclidean traversal endpoint with
    the initial endpoint would force the rational finite Gregory
    stage to be an integer multiple of irrational pi.

The zero integer multiple is excluded by A1.
Every nonzero integer multiple contradicts irrationality of pi.
-/


/- ============================================================
   I. LOCAL TERM NOTATION
   ============================================================ -/

private def leibnizTermQ153
    (i : ℕ) :
    ℚ :=

  (-1 : ℚ) ^ i /
    (2 * (i : ℚ) + 1)


private theorem leibniz_partial_succ_153
    (n : ℕ) :

    leibnizPartialQ (n + 1)
    =
    leibnizPartialQ n
      +
    leibnizTermQ153 n := by

  unfold leibnizPartialQ leibnizTermQ153

  rw [Finset.sum_range_succ]


/- ============================================================
   II. EXACT SIGNS OF EVEN / ODD TERMS
   ============================================================ -/

private theorem neg_one_pow_even_153
    (k : ℕ) :

    (-1 : ℚ) ^ (2 * k) = 1 := by

  rw [pow_mul]

  norm_num


private theorem neg_one_pow_odd_153
    (k : ℕ) :

    (-1 : ℚ) ^ (2 * k + 1) = -1 := by

  rw [
    show
      2 * k + 1
      =
      (2 * k) + 1
      by omega,
    pow_succ,
    neg_one_pow_even_153
  ]

  norm_num


private theorem even_term_form_153
    (k : ℕ) :

    leibnizTermQ153 (2 * k)
    =
    1 / (4 * (k : ℚ) + 1) := by

  norm_num [
    leibnizTermQ153,
    neg_one_pow_even_153
  ] <;> ring


private theorem odd_term_form_153
    (k : ℕ) :

    leibnizTermQ153 (2 * k + 1)
    =
    -(1 / (4 * (k : ℚ) + 3)) := by

  norm_num [
    leibnizTermQ153,
    neg_one_pow_odd_153
  ] <;> ring


/- ============================================================
   III. EACH COMPLETE GREGORY PAIR IS STRICTLY POSITIVE
   ============================================================ -/

private theorem leibniz_pair_pos_153
    (k : ℕ) :

    0
    <
    leibnizTermQ153 (2 * k)
      +
    leibnizTermQ153 (2 * k + 1) := by

  rw [
    even_term_form_153,
    odd_term_form_153
  ]

  have h1 :
      (0 : ℚ)
      <
      4 * (k : ℚ) + 1 := by
    positivity

  have h3 :
      (0 : ℚ)
      <
      4 * (k : ℚ) + 3 := by
    positivity

  have hden :
      4 * (k : ℚ) + 1
      <
      4 * (k : ℚ) + 3 := by
    norm_num

  have hfrac :
      (1 : ℚ) / (4 * (k : ℚ) + 3)
      <
      1 / (4 * (k : ℚ) + 1) := by

    rw [div_lt_div_iff₀ h3 h1]

    nlinarith

  linarith


private theorem even_term_pos_153
    (k : ℕ) :

    0 < leibnizTermQ153 (2 * k) := by

  rw [even_term_form_153]

  positivity


/- ============================================================
   IV. TWO-STEP RECURRENCE
   ============================================================ -/

private theorem leibniz_partial_two_step_153
    (k : ℕ) :

    leibnizPartialQ (2 * k + 2)
    =
    leibnizPartialQ (2 * k)
      +
    leibnizTermQ153 (2 * k)
      +
    leibnizTermQ153 (2 * k + 1) := by

  calc

    leibnizPartialQ (2 * k + 2)
        =
        leibnizPartialQ ((2 * k + 1) + 1) := by
          congr 1

    _ =
        leibnizPartialQ (2 * k + 1)
          +
        leibnizTermQ153 (2 * k + 1) := by
          exact
            leibniz_partial_succ_153
              (2 * k + 1)

    _ =
        (
          leibnizPartialQ (2 * k)
            +
          leibnizTermQ153 (2 * k)
        )
          +
        leibnizTermQ153 (2 * k + 1) := by

          rw [
            leibniz_partial_succ_153
              (2 * k)
          ]

    _ =
        leibnizPartialQ (2 * k)
          +
        leibnizTermQ153 (2 * k)
          +
        leibnizTermQ153 (2 * k + 1) := by
          rfl


/- ============================================================
   V. NONNEGATIVE EVEN PARTIALS
   ============================================================ -/

private theorem leibniz_even_nonneg_153
    (k : ℕ) :

    0 ≤ leibnizPartialQ (2 * k) := by

  induction k with

  | zero =>

      unfold leibnizPartialQ

      norm_num


  | succ k ih =>

      have hp :=
        leibniz_pair_pos_153 k

      have hrec :=
        leibniz_partial_two_step_153 k

      rw [
        show
          2 * Nat.succ k
          =
          2 * k + 2
          by omega,
        hrec
      ]

      linarith


/- ============================================================
   VI. STRICT POSITIVITY OF ALL NONEMPTY PARTIAL SUMS
   ============================================================ -/

private theorem leibniz_odd_pos_153
    (k : ℕ) :

    0 < leibnizPartialQ (2 * k + 1) := by

  have he :=
    leibniz_even_nonneg_153 k

  have ht :=
    even_term_pos_153 k

  have hs :=
    leibniz_partial_succ_153 (2 * k)

  rw [hs]

  linarith


private theorem leibniz_positive_even_successor_153
    (k : ℕ) :

    0 < leibnizPartialQ (2 * k + 2) := by

  have he :=
    leibniz_even_nonneg_153 k

  have hp :=
    leibniz_pair_pos_153 k

  have hrec :=
    leibniz_partial_two_step_153 k

  rw [hrec]

  linarith


theorem leibniz_nonempty_partial_positive
    (n : ℕ) :

    0 < leibnizPartialQ (n + 1) := by

  obtain ⟨k, hk⟩ :
      ∃ k : ℕ,
        n = 2 * k
        ∨
        n = 2 * k + 1 := by
    induction n with
    | zero =>
        exact ⟨0, Or.inl (by norm_num)⟩
    | succ n ih =>
        rcases ih with ⟨k, hk | hk⟩
        · refine ⟨k, Or.inr ?_⟩
          omega
        · refine ⟨k + 1, Or.inl ?_⟩
          omega

  rcases hk with hk | hk

  · subst n

    exact
      leibniz_odd_pos_153 k

  · subst n

    have h :=
      leibniz_positive_even_successor_153 k

    convert h using 1 <;> omega


/- ============================================================
   VII. GREGORY NONEMPTY STAGES ARE STRICTLY POSITIVE
   ============================================================ -/

theorem gregory_nonempty_partial_q_positive
    (n : ℕ) :

    0 < gregoryPartialQ (n + 1) := by

  unfold gregoryPartialQ

  have h :=
    leibniz_nonempty_partial_positive n

  nlinarith


theorem gregory_nonempty_partial_r_positive
    (n : ℕ) :

    0 < gregoryPartialR (n + 1) := by

  unfold gregoryPartialR

  exact_mod_cast
    gregory_nonempty_partial_q_positive n


theorem gregory_nonempty_partial_r_nonzero
    (n : ℕ) :

    gregoryPartialR (n + 1) ≠ 0 := by

  exact
    ne_of_gt
      (gregory_nonempty_partial_r_positive n)


/- ============================================================
   VIII. CIRCUMFERENCE ANGLE REDUCTION
   ============================================================ -/

private theorem finite_gregory_angle_nonempty
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    finiteGregoryCircumference r (n + 1) / r
    =
    2 * gregoryPartialR (n + 1) := by

  unfold finiteGregoryCircumference

  field_simp [hr] <;> ring


/- ============================================================
   IX. NO NONTRIVIAL FINITE GREGORY STAGE RETURNS TO START
   ============================================================ -/

theorem finite_gregory_euclidean_endpoint_ne_start
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    circleTraversalByLength
      r
      (finiteGregoryCircumference r (n + 1))
    ≠
    circleTraversalByLength r 0 := by

  intro hEq

  have hy :=
    congrArg Prod.snd hEq

  change
    r *
      Real.sin
        (
          finiteGregoryCircumference
            r
            (n + 1)
          /
          r
        )
    =
    r * Real.sin (0 / r)
    at hy

  have hsin_raw :
      Real.sin
        (
          finiteGregoryCircumference
            r
            (n + 1)
          /
          r
        )
      =
      Real.sin (0 / r) := by

    exact
      mul_left_cancel₀
        hr
        hy

  have hangle :=
    finite_gregory_angle_nonempty
      r
      hr
      n

  have hsin :
      Real.sin
        (2 * gregoryPartialR (n + 1))
      =
      0 := by

    rw [hangle] at hsin_raw

    simpa using hsin_raw


  rcases
      (Real.sin_eq_zero_iff).mp hsin
    with
      ⟨k, hk⟩


  have hkrel :
      (k : ℝ) * Real.pi
      =
      2 * gregoryPartialR (n + 1) := by

    first
    | simpa [
        mul_comm,
        mul_left_comm,
        mul_assoc
      ] using hk
    | simpa [
        mul_comm,
        mul_left_comm,
        mul_assoc
      ] using hk.symm


  by_cases hk0 : k = 0

  · subst k

    have hp :=
      gregory_nonempty_partial_r_positive n

    norm_num at hkrel

    nlinarith


  · have hkR :
        (k : ℝ) ≠ 0 := by
      exact_mod_cast hk0


    let q : ℚ :=
      (2 * gregoryPartialQ (n + 1))
      /
      (k : ℚ)


    have hpi_div :
        Real.pi
        =
        (
          2 * gregoryPartialR (n + 1)
        )
        /
        (k : ℝ) := by

      apply
        (eq_div_iff hkR).2

      calc

        Real.pi * (k : ℝ)
            =
            (k : ℝ) * Real.pi := by
              ring

        _ =
            2 * gregoryPartialR (n + 1) :=
              hkrel


    have hcast :
        (
          (
            2 * gregoryPartialR (n + 1)
          )
          /
          (k : ℝ)
        )
        =
        (q : ℝ) := by

      unfold gregoryPartialR

      dsimp [q]

      norm_cast


    have hpi_rat :
        Real.pi = (q : ℝ) := by

      exact
        hpi_div.trans hcast


    exact
      irrational_pi.ne_rat
        q
        hpi_rat


/- ============================================================
   X. EXISTENTIAL RETURN-TO-START BARRIER
   ============================================================ -/

theorem no_nontrivial_finite_gregory_return_to_start
    (r : ℝ)
    (hr : r ≠ 0) :

    ¬ ∃ n : ℕ,
        circleTraversalByLength
          r
          (finiteGregoryCircumference r (n + 1))
        =
        circleTraversalByLength r 0 := by

  intro h

  rcases h with ⟨n, hn⟩

  exact
    finite_gregory_euclidean_endpoint_ne_start
      r
      hr
      n
      hn


/- ============================================================
   XI. GENUINE CIRCLE + RETURN BARRIER PACKAGE
   ============================================================ -/

theorem nontrivial_gregory_endpoint_on_circle_and_ne_start
    (r : ℝ)
    (hr : r ≠ 0)
    (n : ℕ) :

    (
      (
        circleTraversalByLength
          r
          (finiteGregoryCircumference r (n + 1))
      ).1 ^ 2
      +
      (
        circleTraversalByLength
          r
          (finiteGregoryCircumference r (n + 1))
      ).2 ^ 2
      =
      r ^ 2
    )
    ∧
    (
      circleTraversalByLength
        r
        (finiteGregoryCircumference r (n + 1))
      ≠
      circleTraversalByLength r 0
    ) := by

  constructor

  · exact
      circle_traversal_by_length_is_on_circle
        r
        (finiteGregoryCircumference r (n + 1))

  · exact
      finite_gregory_euclidean_endpoint_ne_start
        r
        hr
        n


#print axioms leibniz_nonempty_partial_positive
#print axioms gregory_nonempty_partial_q_positive
#print axioms gregory_nonempty_partial_r_positive
#print axioms gregory_nonempty_partial_r_nonzero
#print axioms finite_gregory_euclidean_endpoint_ne_start
#print axioms no_nontrivial_finite_gregory_return_to_start
#print axioms nontrivial_gregory_endpoint_on_circle_and_ne_start

end PiQuasiClassicalBridge
