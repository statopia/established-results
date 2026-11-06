import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3923772922_929a3872 : ∀ (D0 Kt D1 A : ℝ) (hD0 : 0 < D0) (hKt : 0 < Kt) (hD1 : 0 < 1 + D1)
    (hA : A = 100 * (1 + Kt) * (1 + D1) ^ 2),
    ∃ M0 : ℕ, 3 ≤ M0 ∧
      ∀ (m : ℕ), M0 ≤ m →
        (A * Real.rpow (m : ℝ) (-(D0 + 9)) ≤ 1 ∧
          24 * (1 + Kt) * (1 + D1) ^ 3 * Real.rpow (m : ℝ) (-(D0 + 8)) ≤ 1) := by
  /- @proof-region region.target-node.session.2b6d2e44cbddfaf3 begin -/
  intro D0 Kt D1 A hD0 hKt hD1 hA
  set B : ℝ := 24 * (1 + Kt) * (1 + D1) ^ 3 with hB
  have hApos : 0 < A := by
    rw [hA]
    have h1 : (0 : ℝ) < 1 + Kt := by linarith
    have h3 : (0 : ℝ) < (1 + D1) ^ 2 := pow_pos hD1 2
    exact mul_pos (mul_pos (by norm_num) h1) h3
  have hBpos : 0 < B := by
    rw [hB]
    have h1 : (0 : ℝ) < 1 + Kt := by linarith
    have h3 : (0 : ℝ) < (1 + D1) ^ 3 := pow_pos hD1 3
    exact mul_pos (mul_pos (by norm_num) h1) h3
  obtain ⟨N, hN⟩ := exists_nat_gt (max 3 (A + B + 1))
  refine ⟨N, ?_, ?_⟩
  · have h3N : (3 : ℝ) ≤ (N : ℝ) :=
      le_of_lt (lt_of_le_of_lt (le_max_left (3 : ℝ) (A + B + 1)) hN)
    exact_mod_cast h3N
  · intro m hm
    have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmax : max 3 (A + B + 1) < (m : ℝ) := lt_of_lt_of_le hN hNm
    have hcomp : A + B + 1 ≤ max 3 (A + B + 1) := le_max_right (3 : ℝ) (A + B + 1)
    have hA_lt : A < (m : ℝ) := by linarith
    have hB_lt : B < (m : ℝ) := by linarith
    have hm3 : (3 : ℝ) ≤ (m : ℝ) :=
      le_of_lt (lt_of_le_of_lt (le_max_left (3 : ℝ) (A + B + 1)) hmax)
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hnn9 : (0 : ℝ) ≤ Real.rpow (m : ℝ) (-(D0 + 9)) := Real.rpow_nonneg (le_of_lt hm0) _
    have hnn8 : (0 : ℝ) ≤ Real.rpow (m : ℝ) (-(D0 + 8)) := Real.rpow_nonneg (le_of_lt hm0) _
    have hshift9 : (m : ℝ) * Real.rpow (m : ℝ) (-(D0 + 9)) = Real.rpow (m : ℝ) (-(D0 + 8)) := by
      have h := Real.rpow_add hm0 (-(D0 + 9)) 1
      rw [Real.rpow_one] at h
      have he : -(D0 + 9) + 1 = -(D0 + 8) := by ring
      rw [he] at h
      have h2 : Real.rpow (m : ℝ) (-(D0 + 8)) = Real.rpow (m : ℝ) (-(D0 + 9)) * (m : ℝ) := h
      rw [h2]
      exact mul_comm _ _
    have hshift8 : (m : ℝ) * Real.rpow (m : ℝ) (-(D0 + 8)) = Real.rpow (m : ℝ) (-(D0 + 7)) := by
      have h := Real.rpow_add hm0 (-(D0 + 8)) 1
      rw [Real.rpow_one] at h
      have he : -(D0 + 8) + 1 = -(D0 + 7) := by ring
      rw [he] at h
      have h2 : Real.rpow (m : ℝ) (-(D0 + 7)) = Real.rpow (m : ℝ) (-(D0 + 8)) * (m : ℝ) := h
      rw [h2]
      exact mul_comm _ _
    have h8le : Real.rpow (m : ℝ) (-(D0 + 8)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
    have h7le : Real.rpow (m : ℝ) (-(D0 + 7)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
    constructor
    · calc A * Real.rpow (m : ℝ) (-(D0 + 9))
          ≤ (m : ℝ) * Real.rpow (m : ℝ) (-(D0 + 9)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hA_lt) hnn9
        _ = Real.rpow (m : ℝ) (-(D0 + 8)) := hshift9
        _ ≤ 1 := h8le
    · calc B * Real.rpow (m : ℝ) (-(D0 + 8))
          ≤ (m : ℝ) * Real.rpow (m : ℝ) (-(D0 + 8)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hB_lt) hnn8
        _ = Real.rpow (m : ℝ) (-(D0 + 7)) := hshift8
        _ ≤ 1 := h7le
  /- @proof-region region.target-node.session.2b6d2e44cbddfaf3 end -/

end Statlib.Imported

