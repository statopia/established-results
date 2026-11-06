import Lean
import ProverJobs.ResidualE2ESupport20261106.M_cf7b12db4124e8a07731

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianResolventBounds

noncomputable def weightedResolventDerivative {m n : ℕ}
    (X E : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  E * gramResolvent X z -
    X * (gramResolvent X z *
      (((m : ℝ)⁻¹) • (E.conjTranspose * X + X.conjTranspose * E)) * gramResolvent X z)

set_option maxHeartbeats 2000000 in
theorem norm_weighted_resolvent_derivative_le {m n : ℕ} (hm : 1 ≤ m)
    (X E : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    ‖weightedResolventDerivative X E z‖ ≤
      ‖E‖ * (3 * z.im⁻¹ + 2 * ‖z‖ * (z.im⁻¹) ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  have hr : 0 ≤ z.im⁻¹ := (inv_pos.mpr hz).le
  let Q := gramResolvent X z
  let F := X * Q
  let C := X * Q * X.conjTranspose
  have hQ : ‖Q‖ ≤ z.im⁻¹ := gram_resolvent_norm X z hz
  have hF : ‖F‖ ^ 2 ≤ (m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mp
    exact norm_mul_gram_resolvent_le hm X z hz
  have hC : ‖C‖ ≤ (m : ℝ) * (1 + ‖z‖ * z.im⁻¹) :=
    norm_gram_resolvent_compressed_le hm X z hz
  have hRewrite : weightedResolventDerivative X E z =
      E * Q - (((m : ℝ)⁻¹) • (F * E.conjTranspose * F) +
        ((m : ℝ)⁻¹) • (C * E * Q)) := by
    dsimp only [weightedResolventDerivative, F, C, Q]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, smul_add, Matrix.mul_assoc]
  have hEQ : ‖E * Q‖ ≤ ‖E‖ * z.im⁻¹ :=
    (Matrix.l2_opNorm_mul E Q).trans (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))
  have hFirst : ‖((m : ℝ)⁻¹) • (F * E.conjTranspose * F)‖ ≤
      ‖E‖ * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm0)]
    calc (m : ℝ)⁻¹ * ‖F * E.conjTranspose * F‖
        ≤ (m : ℝ)⁻¹ * ((‖F‖ * ‖E‖) * ‖F‖) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm0.le)
          exact (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right
              (by simpa only [Matrix.l2_opNorm_conjTranspose] using
                Matrix.l2_opNorm_mul F E.conjTranspose) (norm_nonneg _))
      _ = (m : ℝ)⁻¹ * (‖F‖ ^ 2 * ‖E‖) := by ring
      _ ≤ (m : ℝ)⁻¹ * (((m : ℝ) * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2)) * ‖E‖) := by
          gcongr
      _ = ‖E‖ * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) := by
          field_simp
  have hSecond : ‖((m : ℝ)⁻¹) • (C * E * Q)‖ ≤
      ‖E‖ * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm0)]
    calc (m : ℝ)⁻¹ * ‖C * E * Q‖
        ≤ (m : ℝ)⁻¹ * ((‖C‖ * ‖E‖) * ‖Q‖) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm0.le)
          exact (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul C E) (norm_nonneg _))
      _ ≤ (m : ℝ)⁻¹ * (((m : ℝ) * (1 + ‖z‖ * z.im⁻¹) * ‖E‖) * z.im⁻¹) := by
          gcongr
      _ = ‖E‖ * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) := by
          field_simp
          <;> ring
  rw [hRewrite]
  calc ‖E * Q - (((m : ℝ)⁻¹) • (F * E.conjTranspose * F) +
          ((m : ℝ)⁻¹) • (C * E * Q))‖
      ≤ ‖E * Q‖ + (‖((m : ℝ)⁻¹) • (F * E.conjTranspose * F)‖ +
          ‖((m : ℝ)⁻¹) • (C * E * Q)‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ‖E‖ * z.im⁻¹ +
        (‖E‖ * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2) +
          ‖E‖ * (z.im⁻¹ + ‖z‖ * (z.im⁻¹) ^ 2)) :=
        add_le_add hEQ (add_le_add hFirst hSecond)
    _ = ‖E‖ * (3 * z.im⁻¹ + 2 * ‖z‖ * (z.im⁻¹) ^ 2) := by ring

theorem norm_weighted_resolvent_derivative_entry_le {m n : ℕ} (hm : 1 ≤ m)
    (X E : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im)
    (i : Fin m) (j : Fin n) :
    ‖weightedResolventDerivative X E z i j‖ ≤
      ‖E‖ * (3 * z.im⁻¹ + 2 * ‖z‖ * (z.im⁻¹) ^ 2) :=
  (matrix_entry_le_l2_norm _ i j).trans (norm_weighted_resolvent_derivative_le hm X E z hz)

#print axioms norm_weighted_resolvent_derivative_le
#print axioms norm_weighted_resolvent_derivative_entry_le
end ResidualSparseRepair20261106.GaussianResolventBounds

