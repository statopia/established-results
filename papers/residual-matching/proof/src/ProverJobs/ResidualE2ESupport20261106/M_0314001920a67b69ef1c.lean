import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_b778b4d5dcd692cef346

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

namespace ResidualSparseRepair20261106.GaussianTail

lemma covariance_excess_le (M a : ℝ) (hM : 0 < M) (ha : 0 ≤ a) :
    max (a^2 / M - 4) 0 ≤
      4 * max (a - 2 * Real.sqrt M) 0 / Real.sqrt M +
      (max (a - 2 * Real.sqrt M) 0)^2 / M := by
  have hs := Real.sqrt_pos.2 hM
  have hsq := Real.sq_sqrt hM.le
  by_cases h : a ≤ 2 * Real.sqrt M
  · rw [max_eq_right (by linarith : a - 2 * Real.sqrt M ≤ 0)]
    simp only [mul_zero, zero_div, zero_pow (by omega : 2 ≠ 0), add_zero]
    apply max_le
    · have hb : a^2 / M ≤ 4 := (div_le_iff₀ hM).2 (by nlinarith)
      linarith
    · rfl
  · rw [max_eq_left (by linarith : 0 ≤ a - 2 * Real.sqrt M)]
    have hid : a^2 / M - 4 = 4 * (a - 2 * Real.sqrt M) / Real.sqrt M +
        (a - 2 * Real.sqrt M)^2 / M := by
      field_simp
      nlinarith [hsq]
    rw [hid]
    apply max_le le_rfl
    have hy : 0 ≤ a - 2 * Real.sqrt M := by linarith
    positivity

/-- The canonical Gaussian covariance spectrum's scalar outlier budget is O(m⁻¹ᐟ²). -/
theorem canonical_covariance_tail (m n : ℕ) (hm : 1 ≤ m) (hnm : n ≤ m) :
    Integrable (fun g : (Fin m × Fin n) → ℝ => matrixNorm g ^ 2) (canonicalMeasure m n) ∧
    Integrable (fun g : (Fin m × Fin n) → ℝ => max (matrixNorm g ^ 2 / (m : ℝ) - 4) 0)
      (canonicalMeasure m n) ∧
    (∫ g, max (matrixNorm g ^ 2 / (m : ℝ) - 4) 0 ∂canonicalMeasure m n) ≤
      24 / Real.sqrt (m : ℝ) := by
  let μ := canonicalMeasure m n
  haveI : IsProbabilityMeasure μ := canonicalMeasure_probability m n
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hs0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hs1 : 1 ≤ Real.sqrt (m : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
  have hsq := Real.sq_sqrt hm0.le
  let Y := fun g : (Fin m × Fin n) → ℝ => max (matrixNorm g - 2 * Real.sqrt (m : ℝ)) 0
  obtain ⟨hi1, hi2, hb1, hb2⟩ := canonical_edge_moments m n hnm
  change Integrable Y μ at hi1
  change Integrable (fun g => Y g ^ 2) μ at hi2
  change (∫ g, Y g ∂μ) ≤ 5 at hb1
  change (∫ g, Y g ^ 2 ∂μ) ≤ 4 at hb2
  have hY0 (g) : 0 ≤ Y g := le_max_right _ _
  have ha0 (g : (Fin m × Fin n) → ℝ) : 0 ≤ matrixNorm g := by
    dsimp [matrixNorm]
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    exact norm_nonneg _
  have ham (g) : matrixNorm g ≤ Y g + 2 * Real.sqrt (m : ℝ) := by
    have := le_max_left (matrixNorm g - 2 * Real.sqrt (m : ℝ)) 0
    dsimp [Y]
    linarith
  have hnorm2 : Integrable (fun g => matrixNorm g ^ 2) μ := by
    apply ((hi2.const_mul 2).add (integrable_const (8 * (m : ℝ)))).mono
      ((matrixNorm_measurable m n).pow_const 2).aestronglyMeasurable
    filter_upwards with g
    change ‖matrixNorm g ^ 2‖ ≤ ‖2 * Y g ^ 2 + 8 * (m : ℝ)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (matrixNorm g)),
      abs_of_nonneg (show 0 ≤ 2 * Y g ^ 2 + 8 * (m : ℝ) by positivity)]
    have hh : matrixNorm g ^ 2 ≤ (Y g + 2 * Real.sqrt (m : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (ha0 g) (ham g) 2
    nlinarith [hh, sq_nonneg (Y g - 2 * Real.sqrt (m : ℝ))]
  let E := fun g : (Fin m × Fin n) → ℝ => max (matrixNorm g ^ 2 / (m : ℝ) - 4) 0
  let B := fun g : (Fin m × Fin n) → ℝ => 4 * Y g / Real.sqrt (m : ℝ) + Y g ^ 2 / (m : ℝ)
  have hBint : Integrable B μ := (hi1.const_mul 4 |>.div_const _).add (hi2.div_const _)
  have hle (g) : E g ≤ B g := covariance_excess_le (m : ℝ) (matrixNorm g) hm0 (ha0 g)
  have hEint : Integrable E μ := hBint.mono
    ((((matrixNorm_measurable m n).pow_const 2).div_const _).sub measurable_const |>.max measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => by
      have hB0 : 0 ≤ B g := by dsimp [B]; positivity
      have hE0 : 0 ≤ E g := le_max_right _ _
      simpa only [Real.norm_eq_abs, abs_of_nonneg hE0, abs_of_nonneg hB0] using hle g)
  refine ⟨hnorm2, hEint, ?_⟩
  change (∫ g, E g ∂μ) ≤ _
  calc
    _ ≤ ∫ g, B g ∂μ := integral_mono hEint hBint hle
    _ = 4 * (∫ g, Y g ∂μ) / Real.sqrt (m : ℝ) + (∫ g, Y g ^ 2 ∂μ) / (m : ℝ) := by
      dsimp [B]
      rw [integral_add (hi1.const_mul 4 |>.div_const _) (hi2.div_const _),
        integral_div, integral_const_mul, integral_div]
    _ ≤ 4 * 5 / Real.sqrt (m : ℝ) + 4 / (m : ℝ) := by
      exact add_le_add (div_le_div_of_nonneg_right (by linarith) hs0.le)
        (div_le_div_of_nonneg_right hb2 hm0.le)
    _ ≤ 24 / Real.sqrt (m : ℝ) := by
      have hms : Real.sqrt (m : ℝ) ≤ m := by nlinarith
      have hd := one_div_le_one_div_of_le hs0 hms
      calc
        4 * 5 / Real.sqrt (m : ℝ) + 4 / (m : ℝ)
          = 20 * (1 / Real.sqrt (m : ℝ)) + 4 * (1 / (m : ℝ)) := by ring
        _ ≤ 20 * (1 / Real.sqrt (m : ℝ)) + 4 * (1 / Real.sqrt (m : ℝ)) := by linarith
        _ = 24 / Real.sqrt (m : ℝ) := by ring

#print axioms canonical_covariance_tail
end ResidualSparseRepair20261106.GaussianTail

