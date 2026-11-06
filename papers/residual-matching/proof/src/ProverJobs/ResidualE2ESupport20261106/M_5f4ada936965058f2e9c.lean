import Lean
import ProverJobs.ResidualE2ESupport20261106.M_64a82130c2793a9532fe
import ProverJobs.ResidualE2ESupport20261106.M_f36ae02d45ed65920a57

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianResolventBounds

theorem real_gram_resolvent_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : A.conjTranspose = A.transpose)
    (z : ℂ) : (gramResolvent A z).transpose = gramResolvent A z := by
  simp only [gramResolvent, gramMatrix, hA, Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_mul_resolvent_identity {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    gramMatrix A * gramResolvent A z = 1 + z • gramResolvent A z := by
  have h := Matrix.mul_nonsing_inv (gramMatrix A - z • 1)
    ((Matrix.isUnit_iff_isUnit_det _).1 (gram_pencil_isUnit A z hz))
  change (gramMatrix A - z • 1) * gramResolvent A z = 1 at h
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
  exact sub_eq_iff_eq_add.mp h

theorem weighted_entry_contraction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i : Fin m, ∑ j : Fin n, A i j * (A * Q) i j) =
      (A.transpose * A * Q).trace := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem weighted_derivative_contraction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : A.conjTranspose = A.transpose)
    (z : ℂ) :
    (∑ i : Fin m, ∑ j : Fin n,
      weightedResolventDerivative A (Matrix.single i j (1 : ℂ)) z i j) =
      (m : ℂ) * (gramResolvent A z).trace -
        ((gramMatrix A * (gramResolvent A z * gramResolvent A z)).trace +
          (gramMatrix A * gramResolvent A z).trace * (gramResolvent A z).trace) := by
  classical
  let Q := gramResolvent A z
  have hQ : Q.transpose = Q := real_gram_resolvent_transpose A hA z
  have he (i : Fin m) (j : Fin n) :
      weightedResolventDerivative A (Matrix.single i j (1 : ℂ)) z i j =
        Q j j - (m : ℝ)⁻¹ •
          (A * Q * ((Matrix.single i j (1 : ℂ)).transpose * A +
            A.transpose * Matrix.single i j (1 : ℂ)) * Q) i j := by
    simp only [weightedResolventDerivative, Q, Matrix.sub_apply,
      Matrix.conjTranspose_single, star_one, hA, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_apply, Matrix.transpose_single]
    rw [Matrix.single_mul_apply_same]
    simp only [one_mul, Matrix.mul_assoc]
  simp_rw [he, Finset.sum_sub_distrib]
  have hmain : (∑ _i : Fin m, ∑ j : Fin n, Q j j) = (m : ℂ) * Q.trace := by
    simp [Matrix.trace, Matrix.diag_apply]
  have hcor : (∑ i : Fin m, ∑ j : Fin n,
      (m : ℝ)⁻¹ • (A * Q * ((Matrix.single i j (1 : ℂ)).transpose * A +
        A.transpose * Matrix.single i j (1 : ℂ)) * Q) i j) =
      (gramMatrix A * (Q * Q)).trace + (gramMatrix A * Q).trace * Q.trace := by
    simp_rw [← Finset.smul_sum]
    rw [loop_derivative_contraction A Q hQ, smul_add, gramMatrix, hA,
      Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul]
    simp only [smul_mul_assoc]
  rw [hmain, hcor]

theorem weighted_derivative_trace_polynomial {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : A.conjTranspose = A.transpose)
    (z : ℂ) (hz : 0 < z.im) :
    (∑ i : Fin m, ∑ j : Fin n,
      weightedResolventDerivative A (Matrix.single i j (1 : ℂ)) z i j) =
      ((m : ℂ) - n - 1) * (gramResolvent A z).trace -
        z * (gramResolvent A z * gramResolvent A z).trace -
        z * (gramResolvent A z).trace ^ 2 := by
  rw [weighted_derivative_contraction A hA z]
  have hSQ := gram_mul_resolvent_identity A z hz
  have hSQ2 : gramMatrix A * (gramResolvent A z * gramResolvent A z) =
      gramResolvent A z + z • (gramResolvent A z * gramResolvent A z) := by
    rw [← Matrix.mul_assoc, hSQ, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hSQ2, hSQ]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  ring

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.weighted_derivative_trace_polynomial

