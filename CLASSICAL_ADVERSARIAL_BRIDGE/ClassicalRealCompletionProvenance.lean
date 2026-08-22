import ClassicalEuclideanGregoryBridge
import Mathlib.Topology.MetricSpace.CauSeqFilter

set_option autoImplicit false

namespace PiQuasiClassicalBridge

theorem gregory_partial_real_formula
    (n : ℕ) :
    gregoryPartialR n =
      4 * ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) := by
  unfold gregoryPartialR gregoryPartialQ leibnizPartialQ
  norm_cast

theorem gregory_partial_real_tendsto_pi :
    Filter.Tendsto
      gregoryPartialR
      Filter.atTop
      (nhds Real.pi) := by
  have h := classical_leibniz_limit_is_granted
  have hc :
      Filter.Tendsto
        (fun _ : ℕ => (4 : ℝ))
        Filter.atTop
        (nhds 4) :=
    tendsto_const_nhds
  have h4 := hc.mul h
  convert h4 using 1
  · funext n
    exact gregory_partial_real_formula n
  · ring

theorem gregory_partial_q_isCauSeq :
    IsCauSeq (abs : ℚ → ℚ) gregoryPartialQ := by
  have hcR : CauchySeq gregoryPartialR :=
    gregory_partial_real_tendsto_pi.cauchySeq
  have hiR : IsCauSeq norm gregoryPartialR :=
    hcR.isCauSeq
  intro ε hε
  have hεR : (0 : ℝ) < (ε : ℝ) := by
    exact_mod_cast hε
  obtain ⟨N, hN⟩ := hiR (ε : ℝ) hεR
  refine ⟨N, ?_⟩
  intro j hj
  have h := hN j hj
  change ‖(gregoryPartialQ j : ℝ) - (gregoryPartialQ N : ℝ)‖ < (ε : ℝ) at h
  rw [Real.norm_eq_abs] at h
  exact_mod_cast h

def gregoryCauSeq : CauSeq ℚ abs :=
  ⟨gregoryPartialQ, gregory_partial_q_isCauSeq⟩

@[simp]
theorem gregoryCauSeq_apply
    (n : ℕ) :
    gregoryCauSeq n = gregoryPartialQ n :=
  rfl

theorem gregory_concrete_real_completion_eq_pi :
    Real.mk gregoryCauSeq = Real.pi := by
  by_contra hne
  have hd :
      0 < |Real.mk gregoryCauSeq - Real.pi| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  let ε : ℝ := |Real.mk gregoryCauSeq - Real.pi| / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 gregory_partial_real_tendsto_pi) ε hε
  have hnear :
      |Real.mk gregoryCauSeq - Real.pi| ≤ ε := by
    apply Real.mk_near_of_forall_near
    refine ⟨N, ?_⟩
    intro j hj
    have hdist := hN j hj
    have habs :
        |gregoryPartialR j - Real.pi| < ε := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using hdist
    change |(gregoryPartialQ j : ℝ) - Real.pi| ≤ ε
    exact le_of_lt habs
  dsimp [ε] at hnear
  linarith

theorem concrete_gregory_completion_without_finite_attainment :
    Real.mk gregoryCauSeq = Real.pi
    ∧
    ∀ n : ℕ,
      ((gregoryCauSeq n : ℚ) : ℝ) ≠ Real.pi := by
  refine ⟨gregory_concrete_real_completion_eq_pi, ?_⟩
  intro n
  change gregoryPartialR n ≠ Real.pi
  exact finite_gregory_stage_ne_classical_pi n

#print axioms gregory_partial_q_isCauSeq
#print axioms gregory_concrete_real_completion_eq_pi
#print axioms concrete_gregory_completion_without_finite_attainment

end PiQuasiClassicalBridge
