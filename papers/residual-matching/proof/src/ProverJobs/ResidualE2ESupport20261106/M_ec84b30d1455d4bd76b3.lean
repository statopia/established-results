import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_4c185f8e948d76caeb7e

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
theorem statopia_math_node_740990000_94fc0980 : ∀ (m n : ℕ) (hmn : 0 < m + n)
    (A : Matrix (Fin m) (Fin n) ℝ),
    (let D : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A A.transpose
            (0 : Matrix (Fin n) (Fin n) ℝ))
     ∀ H : (Matrix.of (fun a b : Fin (m + n) => ((D a b : ℝ) : ℂ))).IsHermitian,
      (⨆ a : Fin (m + n), |(Matrix.IsHermitian.eigenvalues H a)|) = specNorm D) := by
  /- @proof-region region.target-node.session.9c52aa5a47507c36 begin -/
  intro m n hmn A
  dsimp only
  intro H
  set D : Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A A.transpose
        (0 : Matrix (Fin n) (Fin n) ℝ)) with hDdef
  haveI hne : Nonempty (Fin (m + n)) := ⟨⟨0, hmn⟩⟩
  have hM : (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A A.transpose
      (0 : Matrix (Fin n) (Fin n) ℝ)).IsSymm :=
    Matrix.IsSymm.fromBlocks (by simp [Matrix.IsSymm]) rfl (by simp [Matrix.IsSymm])
  have hD : D.IsHermitian := by
    rw [hDdef]
    apply Statlib.HighDim.CovarianceMatrix.real_isHermitian_of_isSymm
    unfold Matrix.IsSymm at hM ⊢
    rw [Matrix.transpose_reindex, hM]
  have hspecnorm : specNorm D = ‖D‖ := (Matrix.l2_opNorm_def D).symm
  have hnorm : ‖D‖ = ⨆ i, |hD.eigenvalues i| := by
    rw [Statlib.HighDim.CovarianceMatrix.hermitian_norm_eq_sup_abs_eigenvalues D hD]
    refine le_antisymm ?_ ?_
    · rw [Finset.sup'_le_iff]
      intro b _
      exact le_csSup (Set.finite_range _ |>.bddAbove) (Set.mem_range_self b)
    · refine Real.iSup_le (fun i => ?_) ?_
      · exact Finset.le_sup' (fun i => |hD.eigenvalues i|) (Finset.mem_univ i)
      · exact le_trans (abs_nonneg _)
          (Finset.le_sup' (fun i => |hD.eigenvalues i|) (Finset.mem_univ ⟨0, hmn⟩))
  have hbridge : (⨆ a, |H.eigenvalues a|) = ⨆ i, |hD.eigenvalues i| :=
    statopia_math_node_4153628898_515516f4 (m + n) D hD H
  calc (⨆ a, |H.eigenvalues a|) = ⨆ i, |hD.eigenvalues i| := hbridge
    _ = ‖D‖ := hnorm.symm
    _ = specNorm D := hspecnorm.symm
  /- @proof-region region.target-node.session.9c52aa5a47507c36 end -/

end

end Statlib.Imported

