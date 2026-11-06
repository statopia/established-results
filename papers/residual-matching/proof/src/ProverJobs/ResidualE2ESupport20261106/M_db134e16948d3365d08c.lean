import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory

namespace ResidualSparseRepair20261106.GaussianTail

/-- A Gaussian upper tail gives its second moment, including integrability. -/
theorem second_moment_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω)
    (hTail : ∀ t : ℝ, 0 < t → μ {ω | t < Y ω} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))) :
    Integrable (fun ω => Y ω ^ 2) μ ∧ (∫ ω, Y ω ^ 2 ∂μ) ≤ 4 := by
  have hn : 0 ≤ᵐ[μ] fun ω => Y ω ^ 2 := Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hmeas : Measurable (fun ω => Y ω ^ 2) := hY.pow_const 2
  have hlayer := lintegral_eq_lintegral_meas_lt μ hn hmeas.aemeasurable
  have hbound : (∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ) ≤ ENNReal.ofReal 4 := by
    rw [hlayer]
    calc
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-(1 / 2 : ℝ) * t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
        have heq : {ω | t < Y ω ^ 2} = {ω | Real.sqrt t < Y ω} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          constructor
          · intro h
            nlinarith [Real.sq_sqrt ht.le, hY0 ω]
          · intro h
            nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
        rw [heq]
        convert hTail (Real.sqrt t) hs using 1
        rw [Real.sq_sqrt ht.le]
        congr 2
        ring
      _ = ENNReal.ofReal 4 := by
        have hi : IntegrableOn (fun t : ℝ => 2 * Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi 0) :=
          (exp_neg_integrableOn_Ioi 0 (b := (1 / 2 : ℝ)) (by norm_num)).const_mul 2
        rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => by positivity)]
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0]
        norm_num
  have hi : Integrable (fun ω => Y ω ^ 2) μ :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hn).2
      (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa using this

/-- A convenient first-moment consequence, without an extra moment assumption. -/
theorem first_moment_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hi : Integrable (fun ω => Y ω ^ 2) μ)
    (hbound : (∫ ω, Y ω ^ 2 ∂μ) ≤ 4) :
    Integrable Y μ ∧ (∫ ω, Y ω ∂μ) ≤ 5 := by
  have hle : ∀ ω, Y ω ≤ Y ω ^ 2 + 1 := fun ω => by nlinarith [sq_nonneg (Y ω - 1 / 2)]
  have hint : Integrable Y μ := (hi.add (integrable_const 1)).mono hY.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      have hn : 0 ≤ Y ω ^ 2 + 1 := by positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg (hY0 ω), abs_of_nonneg hn] using hle ω)
  refine ⟨hint, ?_⟩
  have hb := integral_mono hint (hi.add (integrable_const 1)) hle
  change (∫ x, Y x ∂μ) ≤ (∫ x, Y x ^ 2 + 1 ∂μ) at hb
  rw [integral_add hi (integrable_const 1)] at hb
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hb
  linarith

#print axioms second_moment_of_gaussian_tail
#print axioms first_moment_of_second_moment
end ResidualSparseRepair20261106.GaussianTail

