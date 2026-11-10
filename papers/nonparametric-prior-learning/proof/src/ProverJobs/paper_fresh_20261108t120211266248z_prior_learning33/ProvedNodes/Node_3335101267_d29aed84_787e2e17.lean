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
theorem statopia_math_node_3335101267_d29aed84 : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ιH : Type*) (bH : HilbertBasis ιH ℝ H) (mu : ιH → ℝ)
    (hmu_pos : ∀ i : ιH, 0 < mu i)
    (C : ℝ) (hC : 0 < C) (hlo : ∀ i : ιH, C⁻¹ ≤ mu i) (hhi : ∀ i : ιH, mu i ≤ C)
    (t : ℝ) (w : H),
    HScaleNorm bH mu t w ≠ ⊤ →
    ‖w‖ ^ 2 ≤ Real.rpow C |t| * (HScaleNorm bH mu t w).toReal := by
  /- @proof-region region.target-node.session.2ca18459690e748a begin -/
  intro H hNAC hIPS hCS ιH bH mu hmu_pos C hC hlo hhi t w hne
  have hkey : ∀ i : ιH, Real.rpow C (-|t|) ≤ Real.rpow (mu i) (-t) := by
    intro i
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
      show C ^ (-t) ≤ (mu i) ^ (-t)
      rw [Real.rpow_neg_eq_inv_rpow C t, Real.rpow_neg_eq_inv_rpow (mu i) t]
      exact Real.rpow_le_rpow (inv_nonneg.mpr hC.le)
        ((inv_le_inv₀ hC (hmu_pos i)).mpr (hhi i)) ht
    · push_neg at ht
      rw [abs_of_neg ht, neg_neg]
      show C ^ t ≤ (mu i) ^ (-t)
      have h2 : C ^ t = (C⁻¹) ^ (-t) := by
        rw [← Real.rpow_neg_eq_inv_rpow C (-t), neg_neg]
      rw [h2]
      exact Real.rpow_le_rpow (inv_nonneg.mpr hC.le) (hlo i) (by linarith)
  have hcomm : ∀ i : ιH, (inner ℝ (bH i) w) ^ 2 = inner ℝ w (bH i) * inner ℝ (bH i) w := by
    intro i
    rw [pow_two, real_inner_comm w (bH i)]
  have hsummable : Summable (fun i : ιH => (inner ℝ (bH i) w) ^ 2) := by
    have h := bH.summable_inner_mul_inner w w
    have h' : (fun i : ιH => (inner ℝ (bH i) w) ^ 2)
        = fun i : ιH => inner ℝ w (bH i) * inner ℝ (bH i) w := by
      funext i
      exact hcomm i
    rw [h']
    exact h
  have hsq : (∑' i : ιH, (inner ℝ (bH i) w) ^ 2) = ‖w‖ ^ 2 := by
    calc (∑' i : ιH, (inner ℝ (bH i) w) ^ 2)
        = ∑' i : ιH, inner ℝ w (bH i) * inner ℝ (bH i) w := tsum_congr hcomm
      _ = inner ℝ w w := bH.tsum_inner_mul_inner w w
      _ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have htsum_sq : (∑' i : ιH, ENNReal.ofReal ((inner ℝ (bH i) w) ^ 2))
      = ENNReal.ofReal (‖w‖ ^ 2) := by
    rw [← hsq]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg (inner ℝ (bH i) w))
      hsummable).symm
  have hf : 0 ≤ Real.rpow C (-|t|) := Real.rpow_nonneg hC.le _
  have hconst : (∑' i : ιH, ENNReal.ofReal (Real.rpow C (-|t|) * (inner ℝ (bH i) w) ^ 2))
      = ENNReal.ofReal (Real.rpow C (-|t|) * ‖w‖ ^ 2) := by
    calc (∑' i : ιH, ENNReal.ofReal (Real.rpow C (-|t|) * (inner ℝ (bH i) w) ^ 2))
        = ∑' i : ιH, ENNReal.ofReal (Real.rpow C (-|t|)) *
            ENNReal.ofReal ((inner ℝ (bH i) w) ^ 2) := by
          exact tsum_congr (fun i => ENNReal.ofReal_mul hf)
      _ = ENNReal.ofReal (Real.rpow C (-|t|)) *
            ∑' i : ιH, ENNReal.ofReal ((inner ℝ (bH i) w) ^ 2) := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (Real.rpow C (-|t|)) * ENNReal.ofReal (‖w‖ ^ 2) := by rw [htsum_sq]
      _ = ENNReal.ofReal (Real.rpow C (-|t|) * ‖w‖ ^ 2) := (ENNReal.ofReal_mul hf).symm
  have hle : ENNReal.ofReal (Real.rpow C (-|t|) * ‖w‖ ^ 2) ≤ HScaleNorm bH mu t w := by
    rw [← hconst]
    show (∑' i : ιH, ENNReal.ofReal (Real.rpow C (-|t|) * (inner ℝ (bH i) w) ^ 2))
      ≤ ∑' i : ιH, ENNReal.ofReal (Real.rpow (mu i) (-t) * (inner ℝ (bH i) w) ^ 2)
    exact ENNReal.tsum_le_tsum (fun i =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hkey i) (sq_nonneg _)))
  have htoReal : Real.rpow C (-|t|) * ‖w‖ ^ 2 ≤ (HScaleNorm bH mu t w).toReal := by
    have h1 : (ENNReal.ofReal (Real.rpow C (-|t|) * ‖w‖ ^ 2)).toReal
        ≤ (HScaleNorm bH mu t w).toReal := ENNReal.toReal_mono hne hle
    have h2 : (ENNReal.ofReal (Real.rpow C (-|t|) * ‖w‖ ^ 2)).toReal
        = Real.rpow C (-|t|) * ‖w‖ ^ 2 :=
      ENNReal.toReal_ofReal (mul_nonneg hf (sq_nonneg ‖w‖))
    linarith
  have hone : Real.rpow C |t| * Real.rpow C (-|t|) = 1 := by
    have h : C ^ |t| * C ^ (-|t|) = (1 : ℝ) := by
      rw [← Real.rpow_add hC]
      simp
    exact h
  have hmul : Real.rpow C |t| * (Real.rpow C (-|t|) * ‖w‖ ^ 2)
      ≤ Real.rpow C |t| * (HScaleNorm bH mu t w).toReal :=
    mul_le_mul_of_nonneg_left htoReal (Real.rpow_nonneg hC.le |t|)
  calc ‖w‖ ^ 2 = (Real.rpow C |t| * Real.rpow C (-|t|)) * ‖w‖ ^ 2 := by rw [hone, one_mul]
    _ = Real.rpow C |t| * (Real.rpow C (-|t|) * ‖w‖ ^ 2) := by ring
    _ ≤ Real.rpow C |t| * (HScaleNorm bH mu t w).toReal := hmul
  /- @proof-region region.target-node.session.2ca18459690e748a end -/

end Statlib.Imported
end

