import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_35bed150fbe6905c6172

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

namespace ResidualSparseRepair20261106.GaussianTail

noncomputable def entryMatrix {m n : ℕ} (x : EuclideanSpace ℝ (Fin (m * n))) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => x (finProdFinEquiv (i, j))

lemma opNorm_entryMatrix_le {m n : ℕ} (x : EuclideanSpace ℝ (Fin (m * n))) :
    Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix x) ≤ ‖x‖ := by
  rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg x)
  intro v hv
  have hs : (∑ i : Fin m, ∑ j : Fin n, (entryMatrix x i j) ^ 2) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← Equiv.sum_comp finProdFinEquiv (fun i => (x i) ^ 2)]
    simp [entryMatrix, Fintype.sum_prod_type]
  have hv' : (∑ j : Fin n, (v j) ^ 2) = 1 := by
    have h := EuclideanSpace.norm_sq_eq v
    simp only [Real.norm_eq_abs, sq_abs] at h
    rw [hv] at h
    simpa using h.symm
  have hrow (i : Fin m) : (∑ j : Fin n, entryMatrix x i j * v j) ^ 2 ≤
      ∑ j : Fin n, (entryMatrix x i j) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun j => entryMatrix x i j) (g := fun j => v j)
    simpa [hv'] using h
  have hh : ‖((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (entryMatrix x)) v‖ ^ 2
      ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ i : Fin m, (∑ j : Fin n, entryMatrix x i j * v j) ^ 2 := by
        simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, (entryMatrix x i j) ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = ‖x‖ ^ 2 := hs
  nlinarith [norm_nonneg (((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
    (entryMatrix x)) v), norm_nonneg x]

/-- The spectral norm of a rectangular matrix is 1-Lipschitz in its Euclidean entries. -/
theorem opNorm_entryMatrix_lipschitz (m n : ℕ) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin (m * n)) =>
      Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix x)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  calc
    |Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix x) -
        Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix y)|
      ≤ ‖entryMatrix x - entryMatrix y‖ := by
        simpa only [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2] using
          abs_norm_sub_norm_le (entryMatrix x) (entryMatrix y)
    _ = Statlib.HighDim.MatrixAnalysis.opNorm (entryMatrix (x - y)) := by
      rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
      rfl
    _ ≤ ‖x - y‖ := opNorm_entryMatrix_le (x - y)
    _ = dist x y := (dist_eq_norm x y).symm

#print axioms opNorm_entryMatrix_lipschitz
end ResidualSparseRepair20261106.GaussianTail

