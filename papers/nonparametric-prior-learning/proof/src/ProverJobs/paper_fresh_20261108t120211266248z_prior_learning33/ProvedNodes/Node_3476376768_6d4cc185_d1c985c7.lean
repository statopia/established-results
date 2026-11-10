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
theorem statopia_math_node_3476376768_6d4cc185 : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type*) (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ) (M : ℝ)
    (hmu_pos : ∀ i : ι, 0 < mu i) (hM_one : 1 ≤ M) (hmu_le : ∀ i : ι, mu i ≤ M)
    (t : ℝ) (ht : 0 ≤ t) (z : H),
    ENNReal.ofReal (‖z‖ ^ 2) ≤ ENNReal.ofReal (Real.rpow M t) * HScaleNorm bH mu t z := by
  /- @proof-region region.target-node.session.c38145cf0080e14c begin -/
  intro H _ _ _ ι bH mu M hmu_pos hM_one hmu_le t ht z
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM_one
  have hmt : -t ≤ 0 := by linarith
  have hct : 0 ≤ Real.rpow M t := Real.rpow_nonneg (le_of_lt hMpos) t
  have hc : 0 ≤ Real.rpow M (-t) := Real.rpow_nonneg (le_of_lt hMpos) (-t)
  have hterm : ∀ i, ENNReal.ofReal (Real.rpow M (-t) * (inner ℝ (bH i) z) ^ 2)
      ≤ ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) z) ^ 2) := by
    intro i
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (hmu_pos i) (hmu_le i) hmt) (sq_nonneg _)
  have hsummable : Summable (fun i => (inner ℝ (bH i) z) ^ 2) := by
    simpa [pow_two, real_inner_comm z] using bH.summable_inner_mul_inner z z
  have hparseval : ∑' i, (inner ℝ (bH i) z) ^ 2 = ‖z‖ ^ 2 := by
    have h := bH.tsum_inner_mul_inner z z
    rw [real_inner_self_eq_norm_sq] at h
    rw [← h]
    apply tsum_congr
    intro i
    rw [pow_two, real_inner_comm z (bH i)]
  have hOfReal : ENNReal.ofReal (‖z‖ ^ 2)
      = ∑' i, ENNReal.ofReal ((inner ℝ (bH i) z) ^ 2) := by
    rw [← hparseval, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsummable]
  have hEq : ENNReal.ofReal (Real.rpow M (-t)) * ENNReal.ofReal (‖z‖ ^ 2)
      = ∑' i, ENNReal.ofReal (Real.rpow M (-t) * (inner ℝ (bH i) z) ^ 2) := by
    rw [hOfReal, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro i
    rw [ENNReal.ofReal_mul hc]
  have hbound : ENNReal.ofReal (Real.rpow M (-t)) * ENNReal.ofReal (‖z‖ ^ 2)
      ≤ HScaleNorm bH mu t z := by
    rw [hEq]
    simpa only [HScaleNorm] using ENNReal.tsum_le_tsum hterm
  have hrpow_mul : Real.rpow M t * Real.rpow M (-t) = 1 := by
    have h := Real.rpow_add hMpos t (-t)
    rw [add_neg_cancel, Real.rpow_zero] at h
    exact h.symm
  have hofreal_mul :
      ENNReal.ofReal (Real.rpow M t) * ENNReal.ofReal (Real.rpow M (-t)) = 1 := by
    rw [← ENNReal.ofReal_mul hct, hrpow_mul, ENNReal.ofReal_one]
  calc ENNReal.ofReal (‖z‖ ^ 2)
      = (ENNReal.ofReal (Real.rpow M t) * ENNReal.ofReal (Real.rpow M (-t)))
          * ENNReal.ofReal (‖z‖ ^ 2) := by rw [hofreal_mul, one_mul]
    _ = ENNReal.ofReal (Real.rpow M t)
          * (ENNReal.ofReal (Real.rpow M (-t)) * ENNReal.ofReal (‖z‖ ^ 2)) :=
          mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (Real.rpow M t) * HScaleNorm bH mu t z :=
          mul_le_mul_left' hbound (ENNReal.ofReal (Real.rpow M t))
  /- @proof-region region.target-node.session.c38145cf0080e14c end -/

end Statlib.Imported
end

