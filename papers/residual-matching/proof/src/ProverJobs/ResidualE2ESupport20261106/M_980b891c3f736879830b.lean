import Lean
import ProverJobs.ResidualE2ESupport20261106.M_97bf2c576cc17ed23abb

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ResidualMaskRepair20261106

lemma dilation_matrixUnit_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (∑ q : Fin m × Fin n, A q.1 q.2 •
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
          (Statlib.Imported.matrixUnit q.1 q.2) (Statlib.Imported.matrixUnit q.1 q.2).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ))) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A A.transpose
        (0 : Matrix (Fin n) (Fin n) ℝ)) := by
  classical
  ext a b
  cases ha : finSumFinEquiv.symm a <;> cases hb : finSumFinEquiv.symm b <;>
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.reindex_apply, ha, hb,
      Matrix.transpose_apply, Statlib.Imported.matrixUnit, Fintype.sum_prod_type,
      ite_and]

lemma dilation_bilinear {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v w : Fin (m+n) → ℝ) :
    (∑ a : Fin (m+n), ∑ b : Fin (m+n), v a *
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) A A.transpose
          (0 : Matrix (Fin n) (Fin n) ℝ))) a b * w b) =
      (∑ i : Fin m, ∑ j : Fin n, v (finSumFinEquiv (Sum.inl i)) * A i j *
        w (finSumFinEquiv (Sum.inr j))) +
      (∑ j : Fin n, ∑ i : Fin m, v (finSumFinEquiv (Sum.inr j)) * A i j *
        w (finSumFinEquiv (Sum.inl i))) := by
  classical
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp_rw [← Equiv.sum_comp finSumFinEquiv (fun b => _ * _ * w b)]
  simp [Fintype.sum_sum_type, Matrix.reindex_apply, Matrix.transpose_apply]

lemma split_norm_square {m n : ℕ} (v : Fin (m+n) → ℝ) :
    (∑ a : Fin (m+n), (v a)^2) =
      (∑ i : Fin m, (v (finSumFinEquiv (Sum.inl i)))^2) +
      (∑ j : Fin n, (v (finSumFinEquiv (Sum.inr j)))^2) := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [Fintype.sum_sum_type]

#print axioms dilation_bilinear
end ResidualMaskRepair20261106

