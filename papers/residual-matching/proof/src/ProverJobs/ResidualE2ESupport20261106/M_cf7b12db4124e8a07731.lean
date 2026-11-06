import Lean
import ProverJobs.ResidualE2ESupport20261106.M_835a80113cc4989674e7

namespace PaperProofTasks.ResidualE2ESupport20261106

open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianResolventBounds
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianCalculus

set_option maxHeartbeats 1000000 in
theorem norm_gram_resolvent_compressed_le {m n : ℕ} (hm : 1 ≤ m)
    (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    ‖X * gramResolvent X z * X.conjTranspose‖ ≤
      (m : ℝ) * (1 + ‖z‖ * z.im⁻¹) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  haveI : NeZero m := ⟨by omega⟩
  let B : Matrix (Fin m) (Fin m) ℂ := ((m : ℝ)⁻¹) • (X * X.conjTranspose)
  let P := B - z • 1
  let R := P⁻¹
  let T := gramMatrix X - z • 1
  let Q := gramResolvent X z
  have hB : B.IsHermitian := by change (((m : ℝ)⁻¹) • (X * X.conjTranspose)).conjTranspose = _; simp [B]
  have hu : IsUnit P := hermitian_resolvent_isUnit B hB z hz
  have hRP : R * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hTQ : T * Q = 1 := Matrix.mul_nonsing_inv T
    ((Matrix.isUnit_iff_isUnit_det _).1 (gram_pencil_isUnit X z hz))
  have hPX : P * X = X * T := by
    dsimp [P, T, B, gramMatrix]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hPXQ : P * (X * Q) = X := by
    rw [← Matrix.mul_assoc, hPX, Matrix.mul_assoc, hTQ, Matrix.mul_one]
  have hXQ : X * Q = R * X := by
    calc X * Q = (R * P) * (X * Q) := by rw [hRP, Matrix.one_mul]
      _ = R * X := by rw [Matrix.mul_assoc, hPXQ]
  have hRB : R * B = 1 + z • R := by
    have hh := hRP
    change R * (B - z • 1) = 1 at hh
    have hexpand : R * (B - z • 1) = R * B - z • R := by
      rw [Matrix.mul_sub]
      congr 1
      simpa only [Matrix.mul_one] using
        (Matrix.mul_smul R z (1 : Matrix (Fin m) (Fin m) ℂ))
    rw [hexpand] at hh
    exact sub_eq_iff_eq_add.mp hh
  have hXX : X * X.conjTranspose = (m : ℝ) • B := by
    dsimp [B]
    rw [smul_smul, mul_inv_cancel₀ hmne, one_smul]
  have hIdentity : X * Q * X.conjTranspose = (m : ℝ) • (1 + z • R) := by
    rw [hXQ, Matrix.mul_assoc, hXX, Matrix.mul_smul, hRB]
  have hR : ‖R‖ ≤ z.im⁻¹ := hermitian_resolvent_norm B hB z hz
  change ‖X * Q * X.conjTranspose‖ ≤ _
  rw [hIdentity, norm_smul, Real.norm_eq_abs, abs_of_pos hm0]
  apply mul_le_mul_of_nonneg_left _ hm0.le
  calc ‖(1 : Matrix (Fin m) (Fin m) ℂ) + z • R‖
      ≤ ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ + ‖z • R‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * ‖R‖ := by rw [norm_one, norm_smul]
    _ ≤ 1 + ‖z‖ * z.im⁻¹ := by gcongr

theorem norm_gram_resolvent_compressed_entry_le {m n : ℕ} (hm : 1 ≤ m)
    (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im)
    (i j : Fin m) :
    ‖(X * gramResolvent X z * X.conjTranspose) i j‖ ≤
      (m : ℝ) * (1 + ‖z‖ * z.im⁻¹) :=
  (matrix_entry_le_l2_norm _ i j).trans (norm_gram_resolvent_compressed_le hm X z hz)

#print axioms norm_gram_resolvent_compressed_le
#print axioms norm_gram_resolvent_compressed_entry_le
end ResidualSparseRepair20261106.GaussianResolventBounds

