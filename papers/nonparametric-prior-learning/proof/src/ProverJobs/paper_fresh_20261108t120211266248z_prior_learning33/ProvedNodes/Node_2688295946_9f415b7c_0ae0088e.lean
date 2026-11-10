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
theorem statopia_math_node_2688295946_9f415b7c : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ι : Type*) (bH : HilbertBasis ι ℝ H) (mu : ι → ℝ)
    (hmu : ∀ i : ι, 0 < mu i)
    (C1 : H →L[ℝ] H) (hC1_eigen : ∀ i : ι, C1 (bH i) = mu i • bH i),
    (∀ i : ι, mu i ≤ ‖C1‖) ∧
    (∀ i : ι, mu i ≤ max 1 ‖C1‖) ∧
    (∀ (t : ℝ), 0 ≤ t → ∀ z : H, HScaleNorm bH mu t z < ⊤ →
      ‖z‖ ≤ Real.rpow (max 1 ‖C1‖) (t / 2) * (HScaleDist bH mu t z 0).toReal) := by
  /- @proof-region region.target-node.session.895b7d900638a2fd begin -/
  intro H _ _ ι bH mu hmu C1 hC1_eigen
  have hbound : ∀ i : ι, mu i ≤ ‖C1‖ := by
    intro i
    have h1 : ‖bH i‖ = 1 := bH.orthonormal.1 i
    have hinner : inner ℝ (bH i) (C1 (bH i)) = mu i := by
      rw [hC1_eigen i, inner_smul_right, real_inner_self_eq_norm_sq, h1]
      ring
    calc mu i = inner ℝ (bH i) (C1 (bH i)) := hinner.symm
      _ ≤ ‖bH i‖ * ‖C1 (bH i)‖ := real_inner_le_norm _ _
      _ = ‖C1 (bH i)‖ := by rw [h1, one_mul]
      _ ≤ ‖C1‖ := by
            have h := C1.le_opNorm (bH i)
            rw [h1, mul_one] at h
            exact h
  refine ⟨hbound, fun i => le_trans (hbound i) (le_max_right 1 ‖C1‖), ?_⟩
  intro t ht z hz
  have hmubar_pos : 0 < max 1 ‖C1‖ := lt_of_lt_of_le one_pos (le_max_left 1 ‖C1‖)
  have hmu_le : ∀ i : ι, mu i ≤ max 1 ‖C1‖ := fun i => le_trans (hbound i) (le_max_right 1 ‖C1‖)
  have hparseval : ∑' i : ι, (inner ℝ (bH i) z) ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq z, ← bH.tsum_inner_mul_inner z z]
    refine tsum_congr (fun i => ?_)
    rw [real_inner_comm z (bH i)]
    ring
  have hsum_sq : Summable (fun i : ι => (inner ℝ (bH i) z) ^ 2) := by
    have h := bH.summable_inner_mul_inner z z
    have heq : (fun i : ι => (inner ℝ (bH i) z) ^ 2)
        = (fun i : ι => inner ℝ z (bH i) * inner ℝ (bH i) z) := by
      funext i
      rw [pow_two, real_inner_comm z (bH i)]
    rw [heq]
    exact h
  have hterm_le : ∀ i : ι,
      Real.rpow (max 1 ‖C1‖) (-t) * (inner ℝ (bH i) z) ^ 2
        ≤ Real.rpow (mu i) (-t) * (inner ℝ (bH i) z) ^ 2 := by
    intro i
    have hrpow : Real.rpow (max 1 ‖C1‖) (-t) ≤ Real.rpow (mu i) (-t) :=
      Real.rpow_le_rpow_of_nonpos (hmu i) (hmu_le i) (by linarith)
    exact mul_le_mul_of_nonneg_right hrpow (sq_nonneg _)
  have hCsum : ∑' i : ι, ENNReal.ofReal ((inner ℝ (bH i) z) ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsum_sq, hparseval]
  have hle : ∑' i : ι, ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * (inner ℝ (bH i) z) ^ 2)
      ≤ HScaleNorm bH mu t z := by
    unfold HScaleNorm
    exact ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal (hterm_le i))
  have hFsum : ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2)
      = ∑' i : ι, ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * (inner ℝ (bH i) z) ^ 2) := by
    calc ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2)
        = ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t)) * ENNReal.ofReal (‖z‖ ^ 2) :=
            ENNReal.ofReal_mul (p := Real.rpow (max 1 ‖C1‖) (-t))
              (le_of_lt (Real.rpow_pos_of_pos hmubar_pos (-t)))
      _ = ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t))
            * (∑' i : ι, ENNReal.ofReal ((inner ℝ (bH i) z) ^ 2)) := by rw [hCsum]
      _ = ∑' i : ι,
            ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t)) * ENNReal.ofReal ((inner ℝ (bH i) z) ^ 2) := by
            rw [← ENNReal.tsum_mul_left]
      _ = ∑' i : ι, ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * (inner ℝ (bH i) z) ^ 2) := by
            refine tsum_congr (fun i => ?_)
            exact (ENNReal.ofReal_mul (p := Real.rpow (max 1 ‖C1‖) (-t))
              (le_of_lt (Real.rpow_pos_of_pos hmubar_pos (-t)))).symm
  have hkey : ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2) ≤ HScaleNorm bH mu t z := by
    rw [hFsum]
    exact hle
  have hkey_real : Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2 ≤ (HScaleNorm bH mu t z).toReal := by
    have hfin : HScaleNorm bH mu t z ≠ ⊤ := ne_of_lt hz
    have hnn : 0 ≤ Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2 :=
      mul_nonneg (Real.rpow_pos_of_pos hmubar_pos (-t)).le (sq_nonneg _)
    calc Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2
        = (ENNReal.ofReal (Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2)).toReal :=
            (ENNReal.toReal_ofReal hnn).symm
      _ ≤ (HScaleNorm bH mu t z).toReal := ENNReal.toReal_mono hfin hkey
  have hN2 : ‖z‖ ^ 2 ≤ Real.rpow (max 1 ‖C1‖) t * (HScaleNorm bH mu t z).toReal := by
    have hrt_pos : 0 < Real.rpow (max 1 ‖C1‖) t := Real.rpow_pos_of_pos hmubar_pos t
    have h1 : Real.rpow (max 1 ‖C1‖) t * (Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2)
        ≤ Real.rpow (max 1 ‖C1‖) t * (HScaleNorm bH mu t z).toReal :=
      mul_le_mul_of_nonneg_left hkey_real hrt_pos.le
    have hpow : Real.rpow (max 1 ‖C1‖) t * Real.rpow (max 1 ‖C1‖) (-t) = 1 := by
      have hadd : Real.rpow (max 1 ‖C1‖) (t + -t)
          = Real.rpow (max 1 ‖C1‖) t * Real.rpow (max 1 ‖C1‖) (-t) :=
        Real.rpow_add hmubar_pos t (-t)
      have hzero : Real.rpow (max 1 ‖C1‖) (t + -t) = 1 := by
        rw [show t + -t = 0 by ring]
        exact Real.rpow_zero (max 1 ‖C1‖)
      rw [← hadd]
      exact hzero
    calc ‖z‖ ^ 2
        = Real.rpow (max 1 ‖C1‖) t * (Real.rpow (max 1 ‖C1‖) (-t) * ‖z‖ ^ 2) := by
            rw [← mul_assoc, hpow, one_mul]
      _ ≤ Real.rpow (max 1 ‖C1‖) t * (HScaleNorm bH mu t z).toReal := h1
  have hr2 : Real.rpow (max 1 ‖C1‖) t
      = Real.rpow (max 1 ‖C1‖) (t / 2) * Real.rpow (max 1 ‖C1‖) (t / 2) := by
    have hadd : Real.rpow (max 1 ‖C1‖) (t / 2 + t / 2)
        = Real.rpow (max 1 ‖C1‖) (t / 2) * Real.rpow (max 1 ‖C1‖) (t / 2) :=
      Real.rpow_add hmubar_pos (t / 2) (t / 2)
    rw [← hadd, show t / 2 + t / 2 = t by ring]
  have hr_nonneg : 0 ≤ Real.rpow (max 1 ‖C1‖) (t / 2) := (Real.rpow_pos_of_pos hmubar_pos (t / 2)).le
  have hsq : ‖z‖ ^ 2 ≤ (Real.rpow (max 1 ‖C1‖) (t / 2)) ^ 2 * (HScaleNorm bH mu t z).toReal := by
    have heq : (Real.rpow (max 1 ‖C1‖) (t / 2)) ^ 2 * (HScaleNorm bH mu t z).toReal
        = Real.rpow (max 1 ‖C1‖) t * (HScaleNorm bH mu t z).toReal := by
      rw [sq, ← hr2]
    rw [heq]
    exact hN2
  have hdist : (HScaleDist bH mu t z 0).toReal = Real.sqrt ((HScaleNorm bH mu t z).toReal) := by
    rw [HScaleDist, sub_zero, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  have hstep : ‖z‖ ≤ Real.rpow (max 1 ‖C1‖) (t / 2) * Real.sqrt ((HScaleNorm bH mu t z).toReal) := by
    have hs := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg z)] at hs
    have hrhs : Real.sqrt ((Real.rpow (max 1 ‖C1‖) (t / 2)) ^ 2 * (HScaleNorm bH mu t z).toReal)
        = Real.rpow (max 1 ‖C1‖) (t / 2) * Real.sqrt ((HScaleNorm bH mu t z).toReal) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr_nonneg]
    rw [hrhs] at hs
    exact hs
  rw [hdist]
  exact hstep
  /- @proof-region region.target-node.session.895b7d900638a2fd end -/

end Statlib.Imported
end

