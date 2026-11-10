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
theorem statopia_math_node_3944456172_a26782c9 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (t : ℝ) (a b : U)
    (ha : UScaleNorm e lam t a < ⊤) (hb : UScaleNorm e lam t b < ⊤),
    UScaleNorm e lam t (a - b) < ⊤ := by
  /- @proof-region region.target-node.session.2d8b40118bc4ecba begin -/
  intro U _ _ _ e lam hlam_pos t a b ha hb
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have key : ∀ k : ℕ,
      ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ 2 * (ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2)) := by
    intro k
    have hw : 0 ≤ Real.rpow (lam k) (-t) := Real.rpow_nonneg (hlam_pos k).le (-t)
    have hsub : inner ℝ (e k) (a - b) = inner ℝ (e k) a - inner ℝ (e k) b := by
      rw [inner_sub_right]
    have hsq : (inner ℝ (e k) a - inner ℝ (e k) b) ^ 2
        ≤ 2 * (inner ℝ (e k) a) ^ 2 + 2 * (inner ℝ (e k) b) ^ 2 := by
      nlinarith [sq_nonneg (inner ℝ (e k) a + inner ℝ (e k) b)]
    have hP : (0 : ℝ) ≤ Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2 :=
      mul_nonneg hw (sq_nonneg _)
    have hQ : (0 : ℝ) ≤ Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2 :=
      mul_nonneg hw (sq_nonneg _)
    have e2P : ENNReal.ofReal (2 * (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2))
        = 2 * ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h2]
    have e2Q : ENNReal.ofReal (2 * (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2))
        = 2 * ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h2]
    calc ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) (a - b)) ^ 2)
        = ENNReal.ofReal (Real.rpow (lam k) (-t)
            * (inner ℝ (e k) a - inner ℝ (e k) b) ^ 2) := by rw [hsub]
      _ ≤ ENNReal.ofReal (Real.rpow (lam k) (-t)
            * (2 * (inner ℝ (e k) a) ^ 2 + 2 * (inner ℝ (e k) b) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left hsq hw
      _ = ENNReal.ofReal (2 * (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + 2 * (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2)) := by
          rw [show Real.rpow (lam k) (-t)
                * (2 * (inner ℝ (e k) a) ^ 2 + 2 * (inner ℝ (e k) b) ^ 2)
              = 2 * (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
                + 2 * (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2) by ring]
      _ = 2 * ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + 2 * ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2) := by
          rw [ENNReal.ofReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hQ), e2P, e2Q]
      _ = 2 * (ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2)) := by
          rw [mul_add]
  have hbound : UScaleNorm e lam t (a - b) ≤ 2 * (UScaleNorm e lam t a + UScaleNorm e lam t b) := by
    unfold UScaleNorm
    calc ∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) (a - b)) ^ 2)
        ≤ ∑' k : ℕ, 2 * (ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2)) :=
          ENNReal.tsum_le_tsum key
      _ = 2 * ∑' k : ℕ, (ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2)) :=
          ENNReal.tsum_mul_left
      _ = 2 * (∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) a) ^ 2)
            + ∑' k : ℕ, ENNReal.ofReal (Real.rpow (lam k) (-t) * (inner ℝ (e k) b) ^ 2)) := by
          rw [ENNReal.tsum_add]
  exact lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨ha, hb⟩))
  /- @proof-region region.target-node.session.2d8b40118bc4ecba end -/

end Statlib.Imported
end

