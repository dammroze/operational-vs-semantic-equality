import PiQuasi.TraditionalPiPotential

set_option autoImplicit false

namespace PiQuasi

/-
Final operational theorem.

There exists no finitely executed Gregory-Leibniz
pi-driven circle carrying an exact finite closure
certificate.
-/
theorem no_finite_closed_traditional_pi_circle :
    ¬ ∃ c : TraditionalPiOperationalCircle,
        TraditionalPiOperationalClosed c := by
  intro h
  cases h with
  | intro c hc =>
      exact
        traditional_pi_operational_circle_not_closed
          c
          hc


/-
Every finitely executed traditional-pi circle
belongs constructively to the quasi-circle class.
-/
theorem finite_traditional_pi_circle_is_quasi
    (c : TraditionalPiOperationalCircle) :
    ∃ q : TraditionalPiOperationalQuasiCircle,
      q.circle = c := by
  exact every_finite_traditional_pi_circle_is_quasi c


/-
There is no finite final pi witness in the
underlying traditional potential process.
-/
theorem traditional_pi_has_no_finite_terminal :
    ¬ TraditionalPiFiniteFinalWitness := by
  exact no_traditional_pi_finite_final_witness


end PiQuasi
