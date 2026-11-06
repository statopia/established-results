import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.Vocabulary.Norms
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
theorem statopia_math_node_2004537962_c9e99f7f : ∀ (m n r : ℕ)
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin n) (Fin r) ℝ),
    frobSq (A * Matrix.transpose B) ≤ spectralNorm A ^ 2 * frobSq B := by
  /- @proof-region region.target-node.session.c6e2db94f6df50b6 begin -/
  intro m n r A B
  have hfrob : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ),
      frobSq M = Statlib.HighDim.Vocabulary.frobeniusNormSq M := by
    intro m n M
    simp only [frobSq, Statlib.HighDim.Vocabulary.frobeniusNormSq]
  have hcomm : frobSq (Matrix.transpose B) = frobSq B := by
    simp only [frobSq, Matrix.transpose_apply]
    exact Finset.sum_comm
  have hcol : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ),
      Statlib.HighDim.Vocabulary.frobeniusNormSq M
        = ∑ j : Fin b, ‖Statlib.HighDim.MatrixAnalysis.colOf M j‖ ^ 2 := by
    intro a b M
    have h := Statlib.HighDim.MatrixAnalysis.frobSq_mul_col
      (1 : Matrix (Fin a) (Fin a) ℝ) M
    rw [Matrix.one_mul] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    rw [Statlib.HighDim.MatrixAnalysis.toEuclideanLin_col, Matrix.one_mul]
  have hL : frobSq (A * Matrix.transpose B)
      = ∑ j : Fin n, ‖(Matrix.toEuclideanLin A)
          (Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j)‖ ^ 2 := by
    rw [hfrob]
    exact Statlib.HighDim.MatrixAnalysis.frobSq_mul_col A (Matrix.transpose B)
  have hterm : ∀ j : Fin n,
      ‖(Matrix.toEuclideanLin A)
          (Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j)‖ ^ 2
      ≤ Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 *
          ‖Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j‖ ^ 2 := by
    intro j
    let v : EuclideanSpace ℝ (Fin r) :=
      Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j
    let w : EuclideanSpace ℝ (Fin m) := (Matrix.toEuclideanLin A) v
    change ‖w‖ ^ 2 ≤ Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 * ‖v‖ ^ 2
    have hle : ‖w‖ ≤ Statlib.HighDim.MatrixAnalysis.opNorm A * ‖v‖ :=
      Statlib.HighDim.MatrixAnalysis.opNorm_vec_le A v
    have hprod : (0:ℝ) ≤
        (Statlib.HighDim.MatrixAnalysis.opNorm A * ‖v‖ - ‖w‖) *
        (Statlib.HighDim.MatrixAnalysis.opNorm A * ‖v‖ + ‖w‖) := by
      apply mul_nonneg
      · linarith
      · have := norm_nonneg w; linarith
    have hsq : ‖w‖ ^ 2 ≤ (Statlib.HighDim.MatrixAnalysis.opNorm A * ‖v‖) ^ 2 := by
      nlinarith [hprod]
    calc ‖w‖ ^ 2
        ≤ (Statlib.HighDim.MatrixAnalysis.opNorm A * ‖v‖) ^ 2 := hsq
      _ = Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 * ‖v‖ ^ 2 := by ring
  have hsum : (∑ j : Fin n, ‖(Matrix.toEuclideanLin A)
        (Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j)‖ ^ 2)
      ≤ Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 *
        (∑ j : Fin n, ‖Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j‖ ^ 2) := by
    calc (∑ j : Fin n, ‖(Matrix.toEuclideanLin A)
          (Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j)‖ ^ 2)
        ≤ ∑ j : Fin n, Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 *
            ‖Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j‖ ^ 2 :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 *
            (∑ j : Fin n, ‖Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j‖ ^ 2) := by
          rw [Finset.mul_sum]
  have hBcol : (∑ j : Fin n,
        ‖Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j‖ ^ 2) = frobSq B := by
    rw [← hcol (Matrix.transpose B), ← hfrob (Matrix.transpose B), hcomm]
  rw [hL]
  calc (∑ j : Fin n, ‖(Matrix.toEuclideanLin A)
        (Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j)‖ ^ 2)
      ≤ Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 *
          (∑ j : Fin n, ‖Statlib.HighDim.MatrixAnalysis.colOf (Matrix.transpose B) j‖ ^ 2) := hsum
    _ = Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 * frobSq B := by rw [hBcol]
    _ = spectralNorm A ^ 2 * frobSq B := rfl
  /- @proof-region region.target-node.session.c6e2db94f6df50b6 end -/

end

end Statlib.Imported

