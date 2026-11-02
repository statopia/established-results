import Statlib.HighDim.MatrixAnalysis.FenchelDualNuclearNormProx
import Statlib.HighDim.MatrixAnalysis.SVDFoundation
import Statlib.HighDim.Vocabulary.SVD
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_3358557989_a82a71cb_8dd80962
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_3825179525_37ca31cf_d4c05cca

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix

open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_1491593895_e4edda66 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Statlib.HighDim.Vocabulary.SVD A),
    frobNorm (Statlib.HighDim.MatrixAnalysis.svdPosU s *
        Matrix.transpose (Statlib.HighDim.MatrixAnalysis.svdPosV s)) =
      Real.sqrt ((Matrix.rank A : ℕ) : ℝ) := by
  /- @proof-region region.target-node.session.7086975c8cfda7af begin -/
  intro m n A s
  let I : Type := {k : Fin (min m n) //
    0 < s.sigma (Fin.castLE (min_le_left m n) k) (Fin.castLE (min_le_right m n) k)}
  let U : Matrix (Fin m) I ℝ := Statlib.HighDim.MatrixAnalysis.svdPosU s
  let V : Matrix (Fin n) I ℝ := Statlib.HighDim.MatrixAnalysis.svdPosV s
  let M : Matrix (Fin m) (Fin n) ℝ := U * Matrix.transpose V
  have hcard : Fintype.card I = A.rank := statopia_math_node_3358557989_a82a71cb m n A s
  have hchild := statopia_math_node_3825179525_37ca31cf m n A s
    (Classical.choice (Statlib.HighDim.MatrixAnalysis.svd_exists _))
  have hUtU : Matrix.transpose U * U = 1 := by simpa [U] using hchild.1
  have hVtV : Matrix.transpose V * V = 1 := by simpa [V] using hchild.2.1
  have hmul : ∀ X : Matrix I (Fin n) ℝ, Matrix.transpose U * (U * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hUtU, Matrix.one_mul]
  have hMt : Matrix.transpose M * M = V * Matrix.transpose V := by
    have e : Matrix.transpose M = V * Matrix.transpose U := by
      simp [M, Matrix.transpose_mul]
    rw [e, Matrix.mul_assoc, hmul]
  have htr : (Matrix.transpose M * M).trace = (Fintype.card I : ℝ) := by
    rw [hMt, Matrix.trace_mul_comm, hVtV, Matrix.trace_one]
  have hMtrace : ∑ i : Fin m, ∑ j : Fin n, M i j ^ 2 = (Matrix.transpose M * M).trace := by
    have hr : (Matrix.transpose M * M).trace = ∑ j : Fin n, ∑ i : Fin m, M i j * M i j := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hr, Finset.sum_comm]
    simp [pow_two]
  have hsq : frobNorm M ^ 2 = (Fintype.card I : ℝ) := by
    have hS : frobNorm M ^ 2 = ∑ i : Fin m, ∑ j : Fin n, M i j ^ 2 := by
      show Real.sqrt (∑ i : Fin m, ∑ j : Fin n, M i j ^ 2) ^ 2
        = ∑ i : Fin m, ∑ j : Fin n, M i j ^ 2
      rw [Real.sq_sqrt]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    rw [hS, hMtrace, htr]
  have hnn : 0 ≤ frobNorm M := Real.sqrt_nonneg _
  show frobNorm M = Real.sqrt (A.rank : ℝ)
  rw [← Real.sqrt_sq hnn, hsq, hcard]
  /- @proof-region region.target-node.session.7086975c8cfda7af end -/

end Statlib.Imported

