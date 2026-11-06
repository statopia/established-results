import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualSparseRepair20261106.DenseGaussian

/-- Quantitative MP branch stability for aspect ratio at most one.
The sum of the two roots has nonpositive imaginary part. A genuine MP root with
imaginary part at least `c * z.im` therefore separates every upper-half-plane
approximate root from the other algebraic branch. -/
theorem mp_sce_stability (rho c : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hc : 0 < c) (z q s : ℂ) (hz : 0 < z.im)
    (hq : (rho : ℂ) * z * q ^ 2 + (z + (rho : ℂ) - 1) * q + 1 = 0)
    (hqim : c * z.im ≤ q.im) (hsim : 0 ≤ s.im) (δ : ℝ)
    (hδ : ‖(rho : ℂ) * z * s ^ 2 + (z + (rho : ℂ) - 1) * s + 1‖ ≤ δ) :
    ‖s - q‖ ≤ δ / (rho * c * z.im ^ 2) := by
  have hz0 : z ≠ 0 := by intro h; simpa only [h, Complex.zero_im, lt_self_iff_false] using hz
  have hrho0 : (rho : ℂ) ≠ 0 := by exact_mod_cast hrho.ne'
  have hA0 : (rho : ℂ) * z ≠ 0 := mul_ne_zero hrho0 hz0
  let S : ℂ := -(z + (rho : ℂ) - 1) / ((rho : ℂ) * z)
  let r : ℂ := S - q
  have hSform : S = ((-1 / rho : ℝ) : ℂ) +
      (((1 - rho) / rho : ℝ) : ℂ) * z⁻¹ := by
    dsimp only [S]
    push_cast
    field_simp [hrho0, hz0]
    <;> ring
  have hInv : (z⁻¹).im ≤ 0 := by
    rw [Complex.inv_im]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.le) (Complex.normSq_nonneg z)
  have hS : S.im ≤ 0 := by
    rw [hSform]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (sub_nonneg.mpr hrho1) hrho.le) hInv
  have hfactor : (rho : ℂ) * z * (s - q) * (s - r) =
      (rho : ℂ) * z * s ^ 2 + (z + (rho : ℂ) - 1) * s + 1 := by
    calc
      (rho : ℂ) * z * (s - q) * (s - r) =
          (rho : ℂ) * z * s ^ 2 + (z + (rho : ℂ) - 1) * s -
            ((rho : ℂ) * z * q ^ 2 + (z + (rho : ℂ) - 1) * q) := by
        dsimp only [r, S]
        field_simp [hA0]
        <;> ring
      _ = _ := by linear_combination -hq
  have hgap : c * z.im ≤ ‖s - r‖ := by
    have hrim : r.im = S.im - q.im := by simp only [r, Complex.sub_im]
    have hh : q.im ≤ (s - r).im := by rw [Complex.sub_im, hrim]; linarith
    exact hqim.trans (hh.trans (Complex.im_le_norm _))
  have hAnorm : rho * z.im ≤ ‖(rho : ℂ) * z‖ := by
    rw [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho]
    exact mul_le_mul_of_nonneg_left (Complex.im_le_norm z) hrho.le
  have hnorm : ‖(rho : ℂ) * z * s ^ 2 + (z + (rho : ℂ) - 1) * s + 1‖ =
      ‖(rho : ℂ) * z‖ * ‖s - q‖ * ‖s - r‖ := by
    rw [← hfactor, norm_mul, norm_mul]
  have hprod : (rho * c * z.im ^ 2) * ‖s - q‖ ≤ δ := by
    have hh := mul_le_mul hAnorm hgap (mul_nonneg hc.le hz.le) (norm_nonneg _)
    have hh' := mul_le_mul_of_nonneg_right hh (norm_nonneg (s - q))
    calc (rho * c * z.im ^ 2) * ‖s - q‖ =
        (rho * z.im * (c * z.im)) * ‖s - q‖ := by ring
      _ ≤ (‖(rho : ℂ) * z‖ * ‖s - r‖) * ‖s - q‖ := hh'
      _ = ‖(rho : ℂ) * z * s ^ 2 + (z + (rho : ℂ) - 1) * s + 1‖ := by rw [hnorm]; ring
      _ ≤ δ := hδ
  apply (le_div_iff₀ (mul_pos (mul_pos hrho hc) (sq_pos_of_pos hz))).mpr
  simpa only [mul_comm] using hprod

#print axioms mp_sce_stability
end ResidualSparseRepair20261106.DenseGaussian

