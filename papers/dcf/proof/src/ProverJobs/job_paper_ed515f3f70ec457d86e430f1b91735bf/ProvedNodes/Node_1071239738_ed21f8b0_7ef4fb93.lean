import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1071239738_ed21f8b0 : ∀ (p : ℕ) (beta : ℝ) (S : (Fin p → ℝ) → ℝ)
    (dS : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ℝ))
    (dS2 : (Fin p → ℝ) → ((Fin p → ℝ) →L[ℝ] ((Fin p → ℝ) →L[ℝ] ℝ)))
    (hbeta : 0 < beta)
    (hS_pos : ∀ w : Fin p → ℝ, 0 < S w)
    (hS_bound : ∀ w : Fin p → ℝ, ‖dS w‖ ≤ beta * S w)
    (hS2_bound : ∀ w : Fin p → ℝ, ‖dS2 w‖ ≤ beta ^ 2 * S w),
    ∀ w : Fin p → ℝ,
      ‖(beta)⁻¹ • ((S w)⁻¹ • dS2 w +
          ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight
            (dS w))‖ ≤ 2 * beta := by
  /- @proof-region region.target-node.session.dfcdd3e37c53eb8c begin -/
  intro p beta S dS dS2 hbeta hS_pos hS_bound hS2_bound w
  have hSpos : 0 < S w := hS_pos w
  have hSne : S w ≠ 0 := ne_of_gt hSpos
  have hS2ne : S w ^ 2 ≠ 0 := pow_ne_zero 2 hSne
  have hcpos : 0 < (S w ^ 2)⁻¹ := inv_pos.mpr (pow_pos hSpos 2)
  have hinvpos : 0 < beta⁻¹ := inv_pos.mpr hbeta
  have hSin : 0 ≤ (S w)⁻¹ := le_of_lt (inv_pos.mpr hSpos)
  have hcn : ‖(-(S w ^ 2)⁻¹)‖ = (S w ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hcpos]
  have hX : ‖(S w)⁻¹ • dS2 w‖ ≤ beta ^ 2 := by
    have h1 : ‖(S w)⁻¹ • dS2 w‖ ≤ ‖(S w)⁻¹‖ * ‖dS2 w‖ :=
      ContinuousLinearMap.opNorm_smul_le ((S w)⁻¹) (dS2 w)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hSpos)] at h1
    refine le_trans h1 ?_
    calc (S w)⁻¹ * ‖dS2 w‖ ≤ (S w)⁻¹ * (beta ^ 2 * S w) :=
          mul_le_mul_of_nonneg_left (hS2_bound w) hSin
      _ = beta ^ 2 := by
          rw [show (S w)⁻¹ * (beta ^ 2 * S w) = ((S w)⁻¹ * S w) * beta ^ 2 by ring,
            inv_mul_cancel₀ hSne, one_mul]
  have hAnorm : ‖(ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)‖
      ≤ (S w ^ 2)⁻¹ * ‖dS w‖ := by
    calc ‖(ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)‖
        ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)‖ * ‖dS w‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖(-(S w ^ 2)⁻¹)‖ * ‖dS w‖ := by rw [ContinuousLinearMap.norm_toSpanSingleton]
      _ = (S w ^ 2)⁻¹ * ‖dS w‖ := by rw [hcn]
  have hY : ‖((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight
        (dS w)‖ ≤ beta ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have h0 : 0 ≤ ‖dS w‖ := norm_nonneg _
    have hbS : 0 ≤ beta * S w := le_of_lt (mul_pos hbeta hSpos)
    have hcc : 0 ≤ (S w ^ 2)⁻¹ := le_of_lt hcpos
    calc ‖(ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)‖ * ‖dS w‖
        ≤ ((S w ^ 2)⁻¹ * ‖dS w‖) * ‖dS w‖ := mul_le_mul_of_nonneg_right hAnorm h0
      _ ≤ ((S w ^ 2)⁻¹ * (beta * S w)) * (beta * S w) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hS_bound w) hcc) (hS_bound w) h0
            (mul_nonneg hcc hbS)
      _ = beta ^ 2 := by
          rw [show (S w ^ 2)⁻¹ * (beta * S w) * (beta * S w)
                = ((S w ^ 2)⁻¹ * (S w ^ 2)) * beta ^ 2 by ring,
            inv_mul_cancel₀ hS2ne, one_mul]
  have htri : ‖(S w)⁻¹ • dS2 w +
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w)‖
      ≤ beta ^ 2 + beta ^ 2 := by
    calc ‖(S w)⁻¹ • dS2 w +
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w)‖
        ≤ ‖(S w)⁻¹ • dS2 w‖ +
            ‖((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight
              (dS w)‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ beta ^ 2 + beta ^ 2 := add_le_add hX hY
  calc ‖beta⁻¹ • ((S w)⁻¹ • dS2 w +
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w))‖
      ≤ ‖beta⁻¹‖ * ‖(S w)⁻¹ • dS2 w +
          ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w)‖ :=
        ContinuousLinearMap.opNorm_smul_le beta⁻¹ _
    _ = beta⁻¹ * ‖(S w)⁻¹ • dS2 w +
          ((ContinuousLinearMap.toSpanSingleton ℝ (-(S w ^ 2)⁻¹)).comp (dS w)).smulRight (dS w)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos hinvpos]
    _ ≤ beta⁻¹ * (beta ^ 2 + beta ^ 2) :=
        mul_le_mul_of_nonneg_left htri (le_of_lt hinvpos)
    _ = 2 * beta := by
        rw [show beta⁻¹ * (beta ^ 2 + beta ^ 2) = (beta⁻¹ * beta) * (2 * beta) by ring,
          inv_mul_cancel₀ (ne_of_gt hbeta), one_mul]
  /- @proof-region region.target-node.session.dfcdd3e37c53eb8c end -/

end

end Statlib.Imported

