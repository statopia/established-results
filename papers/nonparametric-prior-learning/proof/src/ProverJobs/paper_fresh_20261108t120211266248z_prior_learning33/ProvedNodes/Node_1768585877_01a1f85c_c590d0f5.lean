import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1768585877_01a1f85c : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (v v' y : H) (c M K a V : ℝ)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hK : 0 ≤ K) (ha : 0 ≤ a) (hV : 0 ≤ V)
    (h1 : ‖v - v'‖ ^ 2 ≤ c * V ^ 2)
    (h2 : ‖v + v'‖ ^ 2 ≤ c * (2 * M) ^ 2)
    (h3 : |inner ℝ y (v - v')| ≤ K * a * V),
    |(1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2) - inner ℝ y (v - v')| ≤ (c * M + K * a) * V := by
  /- @proof-region region.target-node.session.ba1375702ab3972d begin -/
  intro H
  refine fun v v' y c M K a V hc hM hK ha hV h1 h2 h3 => ?_
  have hsym : inner ℝ v v' = inner ℝ v' v := by simp [real_inner_comm v v']
  have hkey : ‖v‖ ^ 2 - ‖v'‖ ^ 2 = inner ℝ (v + v') (v - v') := by
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, hsym]
    ring
  have hXY : (0 : ℝ) ≤ c * 2 * M * V :=
    mul_nonneg (mul_nonneg (mul_nonneg hc (by norm_num)) hM) hV
  have hsq : (‖v + v'‖ * ‖v - v'‖) ^ 2 ≤ (c * 2 * M * V) ^ 2 := by
    have e1 : (‖v + v'‖ * ‖v - v'‖) ^ 2 = ‖v + v'‖ ^ 2 * ‖v - v'‖ ^ 2 := by ring
    have e2 : (c * 2 * M * V) ^ 2 = (c * (2 * M) ^ 2) * (c * V ^ 2) := by ring
    rw [e1, e2]
    exact mul_le_mul h2 h1 (sq_nonneg _) (mul_nonneg hc (sq_nonneg _))
  have hprod : ‖v + v'‖ * ‖v - v'‖ ≤ c * 2 * M * V := by
    have h := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      abs_of_nonneg hXY] at h
  have hA : |(1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2)| ≤ c * M * V := by
    rw [hkey, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hcs : |inner ℝ (v + v') (v - v')| ≤ ‖v + v'‖ * ‖v - v'‖ :=
      abs_real_inner_le_norm (v + v') (v - v')
    calc (1 / 2) * |inner ℝ (v + v') (v - v')|
        ≤ (1 / 2) * (‖v + v'‖ * ‖v - v'‖) :=
          mul_le_mul_of_nonneg_left hcs (by norm_num)
      _ ≤ (1 / 2) * (c * 2 * M * V) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = c * M * V := by ring
  have htri : |(1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2) - inner ℝ y (v - v')| ≤
      |(1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2)| + |inner ℝ y (v - v')| := by
    have h := abs_add_le ((1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2)) (-(inner ℝ y (v - v')))
    have h' : (1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2) + -(inner ℝ y (v - v')) =
        (1 / 2 : ℝ) * (‖v‖ ^ 2 - ‖v'‖ ^ 2) - inner ℝ y (v - v') := by ring
    rwa [h', abs_neg] at h
  nlinarith [htri, hA, h3]
  /- @proof-region region.target-node.session.ba1375702ab3972d end -/

end Statlib.Imported
end

