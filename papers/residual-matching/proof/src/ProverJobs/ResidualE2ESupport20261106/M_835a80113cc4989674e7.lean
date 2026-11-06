import Lean
import ProverJobs.ResidualE2ESupport20261106.M_cb5e65f3c1f34ce67cbc

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianResolventBounds
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianCalculus

noncomputable def gramMatrix {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := ((m : ℝ)⁻¹) • (X.conjTranspose * X)
noncomputable def gramResolvent {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ := (gramMatrix X - z • 1)⁻¹

/-- The norm here is the matrix L2 operator norm throughout. -/
theorem gram_resolvent_norm {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (z : ℂ) (hz : 0 < z.im) : ‖gramResolvent X z‖ ≤ z.im⁻¹ := by
  apply hermitian_resolvent_norm (gramMatrix X) _ z hz
  change (((m : ℝ)⁻¹) • (X.conjTranspose * X)).conjTranspose = _
  simp [gramMatrix]

private theorem gram_mul_resolvent {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    gramMatrix X * gramResolvent X z = 1 + z • gramResolvent X z := by
  have hu : IsUnit (gramMatrix X - z • 1) := gram_pencil_isUnit X z hz
  have hh := Matrix.mul_nonsing_inv (gramMatrix X - z • 1)
    ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  change (gramMatrix X - z • 1) * gramResolvent X z = 1 at hh
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hh
  exact sub_eq_iff_eq_add.mp hh

set_option maxHeartbeats 1000000 in
theorem norm_mul_gram_resolvent_le {m n : ℕ} (hm : 1 ≤ m)
    (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    ‖X * gramResolvent X z‖ ≤
      Real.sqrt ((m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  let Q := gramResolvent X z
  have hQ : ‖Q‖ ≤ z.im⁻¹ := gram_resolvent_norm X z hz
  have hHQ : gramMatrix X * Q = 1 + z • Q := gram_mul_resolvent X z hz
  have hGram : X.conjTranspose * X = (m : ℝ) • gramMatrix X := by
    rw [gramMatrix, smul_smul, mul_inv_cancel₀ hmne, one_smul]
  have hIdentity : (X * Q).conjTranspose * (X * Q) =
      (m : ℝ) • (Q.conjTranspose + z • (Q.conjTranspose * Q)) := by
    rw [Matrix.conjTranspose_mul]
    calc Q.conjTranspose * X.conjTranspose * (X * Q)
        = Q.conjTranspose * (X.conjTranspose * X) * Q := by simp only [Matrix.mul_assoc]
      _ = (m : ℝ) • (Q.conjTranspose * (gramMatrix X * Q)) := by
        rw [hGram, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = (m : ℝ) • (Q.conjTranspose + z • (Q.conjTranspose * Q)) := by
        rw [hHQ, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hInner : ‖Q.conjTranspose + z • (Q.conjTranspose * Q)‖ ≤
      z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2 := by
    calc ‖Q.conjTranspose + z • (Q.conjTranspose * Q)‖
        ≤ ‖Q.conjTranspose‖ + ‖z • (Q.conjTranspose * Q)‖ := norm_add_le _ _
      _ = ‖Q‖ + ‖z‖ * ‖Q.conjTranspose * Q‖ := by
        rw [norm_smul, Matrix.l2_opNorm_conjTranspose]
      _ ≤ ‖Q‖ + ‖z‖ * (‖Q‖ * ‖Q‖) := by
        gcongr
        simpa only [Matrix.l2_opNorm_conjTranspose] using Matrix.l2_opNorm_mul Q.conjTranspose Q
      _ ≤ z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2 := by
        rw [pow_two]
        gcongr
  apply Real.le_sqrt_of_sq_le
  calc ‖X * Q‖ ^ 2 = ‖(X * Q).conjTranspose * (X * Q)‖ := by
        rw [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]
    _ = (m : ℝ) * ‖Q.conjTranspose + z • (Q.conjTranspose * Q)‖ := by
        rw [hIdentity, norm_smul, Real.norm_eq_abs, abs_of_pos hm0]
    _ ≤ (m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hInner hm0.le

theorem norm_mul_gram_resolvent_entry_le {m n : ℕ} (hm : 1 ≤ m)
    (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im)
    (i : Fin m) (j : Fin n) :
    ‖(X * gramResolvent X z) i j‖ ≤
      Real.sqrt ((m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2)) :=
  (matrix_entry_le_l2_norm _ i j).trans (norm_mul_gram_resolvent_le hm X z hz)

#print axioms gram_resolvent_norm
#print axioms norm_mul_gram_resolvent_le
#print axioms norm_mul_gram_resolvent_entry_le
end ResidualSparseRepair20261106.GaussianResolventBounds

