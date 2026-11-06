import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2432609000_515200a8 : ∀ (m n : ℕ) (hn : 0 < n) (c1 c2 : ℝ)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2),
    ‖Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (c1 • (1 : Matrix (Fin m) (Fin m) ℝ))
        (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
        (c2 • (1 : Matrix (Fin n) (Fin n) ℝ)))‖ = c2 := by
  /- @proof-region region.target-node.session.27e17c12a63f6b7f begin -/
  intro m n hn c1 c2 hc1 hc12
  have hc2 : 0 ≤ c2 := hc1.trans hc12
  set w : Fin (m + n) → ℝ :=
    (fun i => Sum.elim (fun _ => c1) (fun _ => c2) (finSumFinEquiv.symm i)) with hw
  have hM : Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (c1 • (1 : Matrix (Fin m) (Fin m) ℝ))
        (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
        (c2 • (1 : Matrix (Fin n) (Fin n) ℝ))) = Matrix.diagonal w := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, hw]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rcases hh : finSumFinEquiv.symm i with a | b
      · simp [Matrix.fromBlocks]
      · simp [Matrix.fromBlocks]
    · rw [if_neg hij]
      rcases hi : finSumFinEquiv.symm i with a | b <;>
        rcases hj : finSumFinEquiv.symm j with a' | b'
      · have haa' : a ≠ a' := by
          rintro rfl
          exact hij (by rw [← Equiv.apply_symm_apply finSumFinEquiv i, ← Equiv.apply_symm_apply finSumFinEquiv j, hi, hj])
        simp [Matrix.fromBlocks, haa']
      · simp [Matrix.fromBlocks]
      · simp [Matrix.fromBlocks]
      · have hbb' : b ≠ b' := by
          rintro rfl
          exact hij (by rw [← Equiv.apply_symm_apply finSumFinEquiv i, ← Equiv.apply_symm_apply finSumFinEquiv j, hi, hj])
        simp [Matrix.fromBlocks, hbb']
  rw [hM, Matrix.l2_opNorm_diagonal]
  have hval : ∀ i, w i = c1 ∨ w i = c2 := by
    intro i
    rcases hh : finSumFinEquiv.symm i with a | b
    · left; rw [hw]; simp [hh]
    · right; rw [hw]; simp [hh]
  haveI : Nonempty (Fin (m + n)) := ⟨finSumFinEquiv (Sum.inr ⟨0, hn⟩)⟩
  have hle : ‖w‖ ≤ c2 := by
    rw [Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs]
    rw [Finset.sup'_le_iff]
    intro i _
    rcases hval i with h | h
    · rw [h, abs_of_nonneg hc1]; exact hc12
    · rw [h, abs_of_nonneg hc2]
  have hge : c2 ≤ ‖w‖ := by
    have hwit : w (finSumFinEquiv (Sum.inr ⟨0, hn⟩)) = c2 := by
      show Sum.elim (fun _ => c1) (fun _ => c2)
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr ⟨0, hn⟩))) = c2
      rw [Equiv.symm_apply_apply]
      rfl
    have habs : |w (finSumFinEquiv (Sum.inr ⟨0, hn⟩))| = c2 := by
      rw [hwit, abs_of_nonneg hc2]
    rw [Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs]
    exact Finset.le_sup'_of_le (fun i => |w i|)
      (Finset.mem_univ (finSumFinEquiv (Sum.inr ⟨0, hn⟩))) (le_of_eq habs.symm)
  exact le_antisymm hle hge
  /- @proof-region region.target-node.session.27e17c12a63f6b7f end -/

end

end Statlib.Imported

