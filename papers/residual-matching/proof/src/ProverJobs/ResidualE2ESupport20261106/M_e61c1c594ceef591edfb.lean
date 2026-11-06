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
theorem statopia_math_node_1768303233_f2c5ce27 : ∀ (D0 Kt CD C0 D1 L E : ℝ) (m n : ℕ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (hCD : Kt * (D0 + 12) ≤ CD) (hC0 : 0 ≤ C0)
    (hm : 3 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hD1 : D1 = 2 * CD + C0 + Kt + 1)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) + C0)
    (hE : E = Real.exp (-L / Kt)),
    L + Kt ≤ D1 * (m : ℝ) ∧
      E ≤ Real.rpow ((m : ℝ) * (n : ℝ)) (-(D0 + 12)) := by
  /- @proof-region region.target-node.session.60681ecf5913491e begin -/
  intro D0 Kt CD C0 D1 L E m n hD0 hKt hCD hC0 hm hn hnm hD1 hL hE
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_le_m : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hmn_pos : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hm0 hn0
  have hmn_one : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by
    have h := mul_le_mul hm1 hn1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hm0)
    simpa using h
  have hlog_nonneg : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := Real.log_nonneg hmn_one
  have hlog_prod_le : Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * (m : ℝ) := by
    have h1 : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hn0 hn_le_m
    have h2 : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hm0
    have h3 : Real.log ((m : ℝ) * (n : ℝ)) = Real.log (m : ℝ) + Real.log (n : ℝ) :=
      Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)
    rw [h3]
    linarith
  have hD012 : (0 : ℝ) < D0 + 12 := by linarith
  have hCDpos : (0 : ℝ) < CD := lt_of_lt_of_le (mul_pos hKt hD012) hCD
  have hLK : L + Kt ≤ D1 * (m : ℝ) := by
    have hlog_term : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤ CD * (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_prod_le (le_of_lt hCDpos)
    have hC0m : C0 ≤ C0 * (m : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hm1 hC0
    have hKtm : Kt ≤ Kt * (m : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hm1 (le_of_lt hKt)
    rw [hL, hD1]
    nlinarith [hlog_term, hC0m, hKtm, hm1]
  have hdiv' : (D0 + 12) * Real.log ((m : ℝ) * (n : ℝ)) * Kt ≤ L := by
    have hktCD : Kt * (D0 + 12) * Real.log ((m : ℝ) * (n : ℝ)) ≤
        CD * Real.log ((m : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hCD hlog_nonneg
    rw [hL]
    nlinarith [hktCD, hC0]
  constructor
  · exact hLK
  · rw [hE]
    have hexp_le : Real.exp (-L / Kt) ≤
        Real.exp (Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12))) := by
      refine Real.exp_le_exp.mpr ?_
      rw [div_le_iff₀ hKt]
      have hkey : Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12)) * Kt =
          -((D0 + 12) * Real.log ((m : ℝ) * (n : ℝ)) * Kt) := by ring
      rw [hkey]
      linarith
    calc Real.exp (-L / Kt) ≤
          Real.exp (Real.log ((m : ℝ) * (n : ℝ)) * (-(D0 + 12))) := hexp_le
      _ = Real.rpow ((m : ℝ) * (n : ℝ)) (-(D0 + 12)) :=
          (Real.rpow_def_of_pos hmn_pos _).symm
  /- @proof-region region.target-node.session.60681ecf5913491e end -/

end Statlib.Imported

