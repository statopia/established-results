import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualSparseRepair20261106.GaussianCalculus

theorem mul_single_mul_entry {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (a : Fin m) (b : Fin n) (c : Fin p) (d : Fin q) :
    (A * Matrix.single b c (1 : ℂ) * B) a d = A a b * B c d := by
  rw [Matrix.mul_apply]
  calc
    (∑ x, (A * Matrix.single b c (1 : ℂ)) a x * B x d) =
        (A * Matrix.single b c (1 : ℂ)) a c * B c d := by
      apply Finset.sum_eq_single c
      · intro x hx hxc
        rw [Matrix.mul_single_apply_of_ne (1 : ℂ) b c a x hxc A]
        simp
      · intro hc
        exact (hc (Finset.mem_univ c)).elim
    _ = A a b * B c d := by simp

theorem loop_derivative_contraction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.transpose = Q) :
    (∑ i : Fin m, ∑ j : Fin n,
      (A * Q * ((Matrix.single i j (1 : ℂ)).transpose * A +
        A.transpose * Matrix.single i j (1 : ℂ)) * Q) i j) =
      (A.transpose * A * (Q * Q)).trace +
        (A.transpose * A * Q).trace * Q.trace := by
  have ht (i : Fin m) (j : Fin n) :
      (Matrix.single i j (1 : ℂ)).transpose = Matrix.single j i (1 : ℂ) := by
    simp
  have hentry (i : Fin m) (j : Fin n) :
      (A * Q * ((Matrix.single i j (1 : ℂ)).transpose * A +
        A.transpose * Matrix.single i j (1 : ℂ)) * Q) i j =
      (A * Q) i j * (A * Q) i j + (A * Q * A.transpose) i i * Q j j := by
    rw [ht, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    congr 1
    · simpa only [Matrix.mul_assoc] using
        mul_single_mul_entry (A * Q) (A * Q) i j i j
    · rw [← Matrix.mul_assoc (A * Q) A.transpose (Matrix.single i j (1 : ℂ))]
      exact mul_single_mul_entry (A * Q * A.transpose) Q i i j j
  simp_rw [hentry, Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin m, ∑ j : Fin n, (A * Q) i j * (A * Q) i j) =
      ((A * Q).transpose * (A * Q)).trace := by
    rw [Matrix.trace, Finset.sum_comm]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hsecond : (∑ i : Fin m, ∑ j : Fin n, (A * Q * A.transpose) i i * Q j j) =
      (A * Q * A.transpose).trace * Q.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hfirst2 : ((A * Q).transpose * (A * Q)).trace =
      (A.transpose * A * (Q * Q)).trace := by
    rw [Matrix.transpose_mul, hQ, Matrix.mul_assoc,
      Matrix.trace_mul_comm Q (A.transpose * (A * Q))]
    simp only [Matrix.mul_assoc]
  rw [hfirst, hsecond, hfirst2, Matrix.trace_mul_cycle A Q A.transpose]

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.loop_derivative_contraction

