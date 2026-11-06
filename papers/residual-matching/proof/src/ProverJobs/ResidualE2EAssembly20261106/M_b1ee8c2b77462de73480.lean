import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_183065247_d0f01c1a : ∀ (m r : ℕ) (hr : 1 ≤ r) (sig : Fin r → ℝ) (hsig : ∀ t, 0 ≤ sig t)
    (U : Matrix (Fin m) (Fin r) ℝ) (hU : Matrix.transpose U * U = 1),
    spectralNorm (U * Matrix.diagonal (fun t => Real.sqrt (sig t))) = Real.sqrt (SMax sig) := by
  /- @proof-region region.target-node.session.70c035ad0c1553f5 begin -/
  intro m r hr sig hsig U hU
  haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  set d : Fin r → ℝ := fun t => Real.sqrt (sig t) with hd
  have hbdd : BddAbove (Set.range sig) := (Set.finite_range sig).bddAbove
  have hle_sup : ∀ i, sig i ≤ SMax sig := fun i => le_csSup hbdd ⟨i, rfl⟩
  have hSmax_nonneg : 0 ≤ SMax sig := le_trans (hsig ⟨0, by omega⟩) (hle_sup ⟨0, by omega⟩)
  have hpi_le : ‖sig‖ ≤ SMax sig := by
    refine (pi_norm_le_iff_of_nonneg (x := sig) (r := SMax sig) hSmax_nonneg).2 ?_
    intro i
    rw [show ‖sig i‖ = sig i from by simp [abs_of_nonneg (hsig i)]]
    exact hle_sup i
  have hSmax_le : SMax sig ≤ ‖sig‖ :=
    ciSup_le (f := sig) (fun i => by
      rw [show sig i = ‖sig i‖ from by simp [abs_of_nonneg (hsig i)]]
      exact norm_le_pi_norm sig i)
  have hpi : ‖sig‖ = SMax sig := le_antisymm hpi_le hSmax_le
  have hdiag : ‖Matrix.diagonal sig‖ = SMax sig := by
    rw [Matrix.l2_opNorm_diagonal]
    exact hpi
  have hDtr : Matrix.transpose (Matrix.diagonal d) = Matrix.diagonal d := by
    ext i j
    rw [Matrix.transpose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hdd : (fun i => d i * d i) = sig := by
    funext i
    simpa [hd] using Real.mul_self_sqrt (hsig i)
  have hXtX : Matrix.transpose (U * Matrix.diagonal d) * (U * Matrix.diagonal d)
      = Matrix.diagonal sig := by
    rw [Matrix.transpose_mul, hDtr, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.transpose U) U (Matrix.diagonal d), hU, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, hdd]
  have hopDiag : Statlib.HighDim.MatrixAnalysis.opNorm (Matrix.diagonal sig) = SMax sig := by
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    exact hdiag
  have hconj : Matrix.conjTranspose (U * Matrix.diagonal d)
      = Matrix.transpose (U * Matrix.diagonal d) := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hcs : Statlib.HighDim.MatrixAnalysis.opNorm
        (Matrix.conjTranspose (U * Matrix.diagonal d) * (U * Matrix.diagonal d))
      = Statlib.HighDim.MatrixAnalysis.opNorm (U * Matrix.diagonal d)
        * Statlib.HighDim.MatrixAnalysis.opNorm (U * Matrix.diagonal d) := by
    have hcs_l2 := Matrix.l2_opNorm_conjTranspose_mul_self (U * Matrix.diagonal d)
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2
        (Matrix.conjTranspose (U * Matrix.diagonal d) * (U * Matrix.diagonal d)),
      hcs_l2, ← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 (U * Matrix.diagonal d)]
  have hXsq : Statlib.HighDim.MatrixAnalysis.opNorm (U * Matrix.diagonal d)
        * Statlib.HighDim.MatrixAnalysis.opNorm (U * Matrix.diagonal d) = SMax sig := by
    rw [← hcs, hconj, hXtX]
    exact hopDiag
  have hfinal : Real.sqrt (SMax sig)
      = Statlib.HighDim.MatrixAnalysis.opNorm (U * Matrix.diagonal d) := by
    rw [← hXsq, ← pow_two]
    exact Real.sqrt_sq (Statlib.HighDim.MatrixAnalysis.opNorm_nonneg (U * Matrix.diagonal d))
  have hspec : spectralNorm (U * Matrix.diagonal d)
      = Statlib.HighDim.MatrixAnalysis.opNorm (U * Matrix.diagonal d) := rfl
  rw [hspec]
  exact hfinal.symm
  /- @proof-region region.target-node.session.70c035ad0c1553f5 end -/

end

end Statlib.Imported

