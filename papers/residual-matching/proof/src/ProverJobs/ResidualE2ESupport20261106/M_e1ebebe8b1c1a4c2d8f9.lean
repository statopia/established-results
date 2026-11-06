import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2bc3eb410430a5b6fbb6

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.CDFRegularity

namespace ResidualSparseRepair20261106.DenseGaussian

/-- The square-root map is globally Hölder of exponent one half, including negative arguments. -/
theorem sqrt_holder_half (x y : ℝ) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · have hh := this y x (le_of_not_ge hxy)
    simpa only [abs_sub_comm] using hh
  have hsq : (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    by_cases hy : y ≤ 0
    · rw [Real.sqrt_eq_zero_of_nonpos (hxy.trans hy), Real.sqrt_eq_zero_of_nonpos hy]
      nlinarith
    · have hy0 : 0 ≤ y := (lt_of_not_ge hy).le
      by_cases hx : x ≤ 0
      · rw [Real.sqrt_eq_zero_of_nonpos hx]
        nlinarith [Real.sq_sqrt hy0]
      · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
        have hmul := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) (Real.sqrt_nonneg x)
        nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  exact Real.abs_le_sqrt hsq

private theorem rootedMP_integrable (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) :
    Integrable (rootedMPDensity rho) volume := by
  have hi : IntegrableOn (rootedMPDensity rho) (Set.Icc (0 : ℝ) 2) volume := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
      (hmpDensity_measurable rho).aestronglyMeasurable (2 / (Real.pi * rho))
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using rootedMPDensity_abs_bound rho rho hρ le_rfl hhi x
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hl := hmpLambdaMinus_nonneg rho hhi
  have hu : mpLambdaPlus rho ≤ 2 := by
    have hh : Real.sqrt rho ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hhi⟩
    dsimp [mpLambdaPlus]
    linarith
  have hcases : x < 0 ∨ 2 < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  rcases hcases with hx | hx
  · exact hmpDensity_zero_of_lt rho x (by linarith)
  · exact hmpDensity_zero_of_gt rho x (by linarith)

/-- The covariance MP CDF, written using the rooted-MP density, is uniformly Hölder one half. -/
theorem covarianceMP_integral_holder_half (rhoMinus rho : ℝ)
    (hmin : 0 < rhoMinus) (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1) :
    ∀ x y : ℝ,
      |(∫ u in (mpLambdaMinus rho)..(Real.sqrt x), rootedMPDensity rho u) -
        (∫ u in (mpLambdaMinus rho)..(Real.sqrt y), rootedMPDensity rho u)| ≤
        (2 / (Real.pi * rhoMinus)) * Real.sqrt |x - y| := by
  have hi := rootedMP_integrable rho (lt_of_lt_of_le hmin hlo) hhi
  intro x y
  rw [intervalIntegral.integral_interval_sub_left hi.intervalIntegrable hi.intervalIntegrable]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := rootedMPDensity rho) (a := Real.sqrt y) (b := Real.sqrt x)
    (C := 2 / (Real.pi * rhoMinus))
    (fun u _ => by simpa only [Real.norm_eq_abs] using
      rootedMPDensity_abs_bound rhoMinus rho hmin hlo hhi u)
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans
    (mul_le_mul_of_nonneg_left (sqrt_holder_half x y) (by positivity))

/-- Transfer the actual rooted-density CDF representation to the covariance probability law. -/
theorem covarianceMP_cdf_holder_half (rhoMinus rho : ℝ)
    (hmin : 0 < rhoMinus) (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1) (ν : Measure ℝ)
    (hCDF : ∀ x : ℝ, (ν (Set.Iic x)).toReal =
      ∫ u in (mpLambdaMinus rho)..(Real.sqrt x), rootedMPDensity rho u) :
    ∀ x y : ℝ, |(ν (Set.Iic x)).toReal - (ν (Set.Iic y)).toReal| ≤
      (2 / (Real.pi * rhoMinus)) * Real.sqrt |x - y| := by
  intro x y
  rw [hCDF x, hCDF y]
  exact covarianceMP_integral_holder_half rhoMinus rho hmin hlo hhi x y

#print axioms sqrt_holder_half
#print axioms covarianceMP_cdf_holder_half
end ResidualSparseRepair20261106.DenseGaussian

