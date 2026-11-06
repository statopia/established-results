import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_ae08acc324cb15c4e196

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
theorem statopia_math_node_1258620162_ba622d86 : ∀ (Cbv CD Kt D0 alpha0 D : ℝ)
    (hCbv : 1 ≤ Cbv) (hD0 : 0 < D0) (hKt : 0 < Kt) (halpha0 : 15 < alpha0)
    (hD : 0 < D),
    ∃ M1 : ℕ,
      (∀ m : ℕ, M1 ≤ m →
        3 * Cbv *
          (Real.rpow (m : ℝ) (-(1 / 4)) * Real.rpow (Real.log (m : ℝ)) (3 / 4)
            + Real.rpow (m : ℝ) (-(1 / 2)) *
                Real.sqrt (max 1 ((D + 2) * Real.log (m : ℝ)))
            + Real.rpow (3 * (2 * CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
                  * Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2)) (1 / 3)
                * Real.rpow (max 1 ((D + 2) * Real.log (m : ℝ))) (2 / 3)
            + 3 * (2 * CD + 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4)
                  * Real.rpow (Real.log (m : ℝ)) (1 - alpha0 / 2)
                * max 1 ((D + 2) * Real.log (m : ℝ)))
          ≤ 1 * (Real.log (m : ℝ))⁻¹) ∧
      (∀ m n : ℕ, M1 ≤ m → 2 ≤ n → n ≤ m →
        6 * (m : ℝ) * Real.exp (-(max 1 ((D + 2) * Real.log (m : ℝ))))
          ≤ 10 ^ 6 * Real.rpow (n : ℝ) (-D)) := by
  /- @proof-region region.target-node.session.54adbf6a0ac90506 begin -/
  classical
  intro Cbv CD Kt D0 alpha0 D hCbv hD0 hKt halpha0 hD
  obtain ⟨M1a, hM1a⟩ :=
    statopia_math_node_3491744900_7d9db115 Cbv CD Kt D0 alpha0 D hCbv hD0 hKt halpha0 hD
  refine ⟨M1a, hM1a, ?_⟩
  · intro m n hm hn hnm
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := le_trans hn2 hnm'
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
    have hD' : (0 : ℝ) ≤ D := le_of_lt hD
    have hstep1 : Real.exp (-(max 1 ((D + 2) * Real.log (m : ℝ))))
        ≤ Real.rpow (m : ℝ) (-(D + 2)) := by
      have h1 : -(max 1 ((D + 2) * Real.log (m : ℝ)))
          ≤ -((D + 2) * Real.log (m : ℝ)) := by
        have h2 := le_max_right (1 : ℝ) ((D + 2) * Real.log (m : ℝ))
        linarith
      have hrp : (m : ℝ) ^ (-(D + 2)) = Real.exp (-((D + 2) * Real.log (m : ℝ))) := by
        rw [Real.rpow_def_of_pos hmpos]
        congr 1
        ring
      calc Real.exp (-(max 1 ((D + 2) * Real.log (m : ℝ))))
          ≤ Real.exp (-((D + 2) * Real.log (m : ℝ))) := Real.exp_le_exp.mpr h1
        _ = Real.rpow (m : ℝ) (-(D + 2)) := hrp.symm
    have hstep2 : 6 * (m : ℝ) * Real.exp (-(max 1 ((D + 2) * Real.log (m : ℝ))))
        ≤ 6 * (m : ℝ) * Real.rpow (m : ℝ) (-(D + 2)) := by
      apply mul_le_mul_of_nonneg_left hstep1
      positivity
    have hmul : (m : ℝ) * Real.rpow (m : ℝ) (-(D + 2))
        = Real.rpow (m : ℝ) (-(D + 1)) := by
      have hsum : (m : ℝ) ^ (-(D + 1)) = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (-(D + 2)) := by
        rw [show -(D + 1) = 1 + -(D + 2) by ring]
        rw [Real.rpow_add hmpos]
      rw [Real.rpow_one] at hsum
      exact hsum.symm
    have hstep3 : 6 * (m : ℝ) * Real.rpow (m : ℝ) (-(D + 2))
        = 6 * Real.rpow (m : ℝ) (-(D + 1)) := by
      rw [mul_assoc, hmul]
    have hstep4 : Real.rpow (m : ℝ) (-(D + 1)) = (Real.rpow (m : ℝ) (D + 1))⁻¹ :=
      Real.rpow_neg (le_of_lt hmpos) (D + 1)
    have hle1 : Real.rpow (n : ℝ) D ≤ Real.rpow (m : ℝ) D := by
      apply Real.rpow_le_rpow (le_of_lt hnpos) hnm' hD'
    have hle2 : Real.rpow (m : ℝ) D ≤ Real.rpow (m : ℝ) (D + 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hm1
      linarith
    have hle3 : Real.rpow (n : ℝ) D ≤ Real.rpow (m : ℝ) (D + 1) := le_trans hle1 hle2
    have hpos_nD : (0 : ℝ) < Real.rpow (n : ℝ) D := Real.rpow_pos_of_pos hnpos D
    have hstep5 : (Real.rpow (m : ℝ) (D + 1))⁻¹ ≤ Real.rpow (n : ℝ) (-D) := by
      have ha : (0 : ℝ) < Real.rpow (m : ℝ) (D + 1) := Real.rpow_pos_of_pos hmpos (D + 1)
      have h := (inv_le_inv₀ (a := Real.rpow (m : ℝ) (D + 1)) (b := Real.rpow (n : ℝ) D)
        ha hpos_nD).mpr hle3
      refine le_trans h ?_
      exact le_of_eq (Real.rpow_neg (le_of_lt hnpos) D).symm
    have hstep6 : (0 : ℝ) ≤ Real.rpow (n : ℝ) (-D) := (Real.rpow_pos_of_pos hnpos (-D)).le
    calc
      6 * (m : ℝ) * Real.exp (-(max 1 ((D + 2) * Real.log (m : ℝ))))
          ≤ 6 * (m : ℝ) * Real.rpow (m : ℝ) (-(D + 2)) := hstep2
      _ = 6 * Real.rpow (m : ℝ) (-(D + 1)) := hstep3
      _ = 6 * (Real.rpow (m : ℝ) (D + 1))⁻¹ := by rw [hstep4]
      _ ≤ 6 * Real.rpow (n : ℝ) (-D) := by
            apply mul_le_mul_of_nonneg_left hstep5
            norm_num
      _ ≤ 10 ^ 6 * Real.rpow (n : ℝ) (-D) := by nlinarith

  /- @proof-region region.target-node.session.54adbf6a0ac90506 end -/

end Statlib.Imported

