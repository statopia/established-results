import Lean
import ProverJobs.ResidualE2ESupport20261106.M_86291834286a381d80d7

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory

namespace ResidualSparseRepair20261106.GaussianCalculus

theorem mp_quadratic_residual_of_loop {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℂ)
    (hf : MemLp f 2 μ) (hg : Integrable g μ)
    (rho : ℝ) (hrho : 0 ≤ rho) (m : ℕ) (hm : 1 ≤ m)
    (η : ℝ) (hη : 0 < η) (z : ℂ)
    (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ η⁻¹)
    (hg_bound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ (η⁻¹) ^ 2)
    (hloop : 1 + (z + (rho : ℂ) - 1 + (m : ℂ)⁻¹) * (∫ ω, f ω ∂μ) +
      (rho : ℂ) * z * (∫ ω, (f ω) ^ 2 ∂μ) +
      (z / (m : ℂ)) * (∫ ω, g ω ∂μ) = 0) :
    ‖(rho : ℂ) * z * (∫ ω, f ω ∂μ) ^ 2 +
      (z + (rho : ℂ) - 1) * (∫ ω, f ω ∂μ) + 1‖ ≤
      rho * ‖z‖ * (∫ ω, ‖f ω - ∫ ω', f ω' ∂μ‖ ^ 2 ∂μ) +
        1 / ((m : ℝ) * η) + ‖z‖ / ((m : ℝ) * η ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have ha : ‖∫ ω, f ω ∂μ‖ ≤ η⁻¹ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hh := integral_mono_ae hi.norm (integrable_const (η⁻¹)) hf_bound
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hb : ‖∫ ω, g ω ∂μ‖ ≤ (η⁻¹) ^ 2 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hh := integral_mono_ae hg.norm (integrable_const ((η⁻¹) ^ 2)) hg_bound
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hvar := norm_complex_second_moment_sub_mean_sq_le μ f hf
  have heq : (rho : ℂ) * z * (∫ ω, f ω ∂μ) ^ 2 +
      (z + (rho : ℂ) - 1) * (∫ ω, f ω ∂μ) + 1 =
      -((rho : ℂ) * z * ((∫ ω, (f ω) ^ 2 ∂μ) - (∫ ω, f ω ∂μ) ^ 2)) -
        (m : ℂ)⁻¹ * (∫ ω, f ω ∂μ) -
        (z / (m : ℂ)) * (∫ ω, g ω ∂μ) := by
    linear_combination hloop
  have htriangle (u v w : ℂ) : ‖-u - v - w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
    calc ‖-u - v - w‖ ≤ ‖-u - v‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ (‖-u‖ + ‖v‖) + ‖w‖ := add_le_add (norm_sub_le (-u) v) le_rfl
      _ = _ := by rw [norm_neg]
  rw [heq]
  calc
    _ ≤ ‖(rho : ℂ) * z * ((∫ ω, (f ω) ^ 2 ∂μ) - (∫ ω, f ω ∂μ) ^ 2)‖ +
        ‖(m : ℂ)⁻¹ * (∫ ω, f ω ∂μ)‖ +
        ‖(z / (m : ℂ)) * (∫ ω, g ω ∂μ)‖ := by
      exact htriangle _ _ _
    _ ≤ rho * ‖z‖ * (∫ ω, ‖f ω - ∫ ω', f ω' ∂μ‖ ^ 2 ∂μ) +
        (m : ℝ)⁻¹ * η⁻¹ + (‖z‖ / (m : ℝ)) * (η⁻¹) ^ 2 := by
      simp only [norm_mul, norm_inv, norm_div, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrho]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hvar (mul_nonneg hrho (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hm0.le)))
        (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hm0.le))
    _ = _ := by ring

theorem mp_quadratic_residual_on_window {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℂ)
    (hf : MemLp f 2 μ) (hg : Integrable g μ)
    (rhoMinus rho : ℝ) (hmin : 0 < rhoMinus) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (hz : 0 < z.im) (hz1 : z.im ≤ 1)
    (hRe : |z.re| ≤ 20)
    (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ z.im⁻¹)
    (hg_bound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ (z.im⁻¹) ^ 2)
    (hloop : 1 + (z + (rho : ℂ) - 1 + (m : ℂ)⁻¹) * (∫ ω, f ω ∂μ) +
      (rho : ℂ) * z * (∫ ω, (f ω) ^ 2 ∂μ) +
      (z / (m : ℂ)) * (∫ ω, g ω ∂μ) = 0)
    (hvar : (∫ ω, ‖f ω - ∫ ω', f ω' ∂μ‖ ^ 2 ∂μ) ≤
      (2 / rhoMinus ^ 2) / ((m : ℝ) * z.im ^ 2)) :
    ‖(rho : ℂ) * z * (∫ ω, f ω ∂μ) ^ 2 +
      (z + (rho : ℂ) - 1) * (∫ ω, f ω ∂μ) + 1‖ ≤
      (42 / rhoMinus ^ 2 + 22) / ((m : ℝ) * z.im ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnorm : ‖z‖ ≤ 21 := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz] at hh
    linarith
  have hcoef : rho * ‖z‖ ≤ 21 := by
    calc rho * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho1 (norm_nonneg _)
      _ ≤ 21 := by simpa only [one_mul] using hnorm
  have hvar0 : 0 ≤ (∫ ω, ‖f ω - ∫ ω', f ω' ∂μ‖ ^ 2 ∂μ) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hηsq : z.im ^ 2 ≤ z.im := by nlinarith
  have hone : 1 / ((m : ℝ) * z.im) ≤ 1 / ((m : ℝ) * z.im ^ 2) :=
    one_div_le_one_div_of_le (mul_pos hm0 (sq_pos_of_pos hz))
      (mul_le_mul_of_nonneg_left hηsq hm0.le)
  refine (mp_quadratic_residual_of_loop μ f g hf hg rho hrho m hm z.im hz z
    hf_bound hg_bound hloop).trans ?_
  calc
    _ ≤ 21 * ((2 / rhoMinus ^ 2) / ((m : ℝ) * z.im ^ 2)) +
        1 / ((m : ℝ) * z.im ^ 2) + 21 / ((m : ℝ) * z.im ^ 2) :=
      add_le_add (add_le_add (mul_le_mul hcoef hvar hvar0 (by norm_num)) hone)
        (div_le_div_of_nonneg_right hnorm (by positivity))
    _ = _ := by ring

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.mp_quadratic_residual_of_loop
#print axioms ResidualSparseRepair20261106.GaussianCalculus.mp_quadratic_residual_on_window

