import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory

namespace ResidualSparseRepair20261106.DenseGaussian

/-- A probability measure supported in a fixed compact interval has an explicit
uniform imaginary-part lower bound for its Stieltjes transform on bounded windows. -/
theorem stieltjes_im_lower_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) (z : ℂ)
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hRe : |z.re| ≤ B)
    (hsupp : ∀ᵐ x ∂μ, |x| ≤ R) :
    ((R + B) ^ 2 + 1)⁻¹ * z.im ≤ (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
    intro x h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hh
    linarith
  have hm : Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) :=
    (Complex.continuous_ofReal.sub continuous_const).inv₀ hne
  have hi : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable (1 / z.im)
    filter_upwards with x
    have hb : z.im ≤ ‖(x : ℂ) - z‖ := by
      have hh := Complex.abs_im_le_norm ((x : ℂ) - z)
      simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] using hh
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hz hb
  have hkernel : ∀ x : ℝ, (((x : ℂ) - z)⁻¹).im =
      z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
    intro x
    simp [Complex.inv_im, Complex.normSq_apply, pow_two]
  have hpoint : ∀ᵐ x : ℝ ∂μ, z.im / ((R + B) ^ 2 + 1) ≤ (((x : ℂ) - z)⁻¹).im := by
    filter_upwards [hsupp] with x hx
    have habs : |x - z.re| ≤ R + B := by
      calc |x - z.re| ≤ |x| + |-z.re| := abs_add_le x (-z.re)
        _ = |x| + |z.re| := by rw [abs_neg]
        _ ≤ R + B := add_le_add hx hRe
    have hsq : (x - z.re) ^ 2 ≤ (R + B) ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (x - z.re)) (add_nonneg hR hB)).mpr habs
      simpa only [sq_abs] using hh
    have hηsq : z.im ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hz1)]
    have hd : 0 < (x - z.re) ^ 2 + z.im ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hz)
    rw [hkernel]
    exact div_le_div_of_nonneg_left hz.le hd (add_le_add hsq hηsq)
  have hh := integral_mono_ae (integrable_const (z.im / ((R + B) ^ 2 + 1))) hi.im hpoint
  rw [integral_const] at hh
  simp only [measureReal_univ_eq_one, one_smul] at hh
  change ((R + B) ^ 2 + 1)⁻¹ * z.im ≤ RCLike.im (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ)
  rw [← integral_im hi]
  simpa only [div_eq_mul_inv, mul_comm] using hh

#print axioms stieltjes_im_lower_bound
end ResidualSparseRepair20261106.DenseGaussian

