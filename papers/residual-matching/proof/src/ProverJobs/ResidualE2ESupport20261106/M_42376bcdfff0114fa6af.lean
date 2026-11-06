import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.Vocabulary.Distributions
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_e1ebebe8b1c1a4c2d8f9
import Statlib.RandomMatrix.MeasuresAreProbability

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open Statlib.RandomMatrix.Vocabulary
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.CDFRegularity

namespace ResidualSparseRepair20261106.DenseGaussian

lemma mpMeasure_eq_density (rho : ℝ) (hhi : rho ≤ 1) :
    mpMeasure rho = volume.withDensity (fun x => ENNReal.ofReal (Statlib.RandomMatrix.Vocabulary.mpDensity rho x)) := by
  simp only [mpMeasure, if_neg (not_lt.mpr hhi), zero_smul, add_zero]

lemma mpDensity_nonneg (rho x : ℝ) : 0 ≤ Statlib.RandomMatrix.Vocabulary.mpDensity rho x := by
  by_cases hρ : 0 < rho
  · simp only [Statlib.RandomMatrix.Vocabulary.mpDensity, if_pos hρ]
    split_ifs with hx
    · have ha : 0 ≤ mpLowerEdge rho := sq_nonneg _
      have hxp : 0 < x := lt_of_le_of_lt ha hx.1
      exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  · simp only [Statlib.RandomMatrix.Vocabulary.mpDensity, if_neg hρ]
    exact le_rfl

lemma mpDensity_measurable (rho : ℝ) : Measurable (Statlib.RandomMatrix.Vocabulary.mpDensity rho) := by
  unfold Statlib.RandomMatrix.Vocabulary.mpDensity
  split_ifs
  · apply Measurable.ite measurableSet_Ioo
    · fun_prop
    · exact measurable_const
  · exact measurable_const

lemma mpDensity_integrable (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) :
    Integrable (Statlib.RandomMatrix.Vocabulary.mpDensity rho) volume := by
  haveI : IsProbabilityMeasure (mpMeasure rho) :=
    Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho hρ
  have hfin : (∫⁻ x : ℝ, ENNReal.ofReal (Statlib.RandomMatrix.Vocabulary.mpDensity rho x)) ≠ ⊤ := by
    have hh : (volume.withDensity (fun x => ENNReal.ofReal (Statlib.RandomMatrix.Vocabulary.mpDensity rho x))) Set.univ ≠ ⊤ := by
      rw [← mpMeasure_eq_density rho hhi]
      exact measure_ne_top _ _
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hh
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (Statlib.RandomMatrix.Vocabulary.mpDensity rho x)) :=
    ENNReal.measurable_ofReal.comp (mpDensity_measurable rho)
  have hh := integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin
  simpa only [ENNReal.toReal_ofReal (mpDensity_nonneg rho _)] using hh

lemma mpMeasure_support_four (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) :
    ∀ᵐ x ∂mpMeasure rho, |x| ≤ 4 := by
  apply ae_iff.mpr
  rw [mpMeasure_eq_density rho hhi]
  have hs : MeasurableSet {x : ℝ | ¬ |x| ≤ 4} := by measurability
  rw [withDensity_apply _ hs]
  apply setLIntegral_eq_zero hs
  intro x hx
  have hroot : Real.sqrt rho ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hhi⟩
  have hup : mpUpperEdge rho ≤ 4 := by
    dsimp only [mpUpperEdge]
    nlinarith [Real.sqrt_nonneg rho]
  have hlow : 0 ≤ mpLowerEdge rho := sq_nonneg _
  have hn : ¬ (mpLowerEdge rho < x ∧ x < mpUpperEdge rho) := by
    intro hh
    have hb : |x| ≤ 4 := by rw [abs_of_nonneg (by linarith : 0 ≤ x)]; linarith
    exact hx hb
  change ENNReal.ofReal (Statlib.RandomMatrix.Vocabulary.mpDensity rho x) = 0
  simp [Statlib.RandomMatrix.Vocabulary.mpDensity, hρ, hn]

lemma rootedMPDensity_eq_square_jacobian (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1)
    (u : ℝ) (hu : 0 < u) :
    rootedMPDensity rho u = (2 * u) * Statlib.RandomMatrix.Vocabulary.mpDensity rho (u ^ 2) := by
  have ha : 0 ≤ mpLambdaMinus rho := hmpLambdaMinus_nonneg rho hhi
  have hb : 0 < mpLambdaPlus rho := hmpLambdaPlus_pos rho hρ.le
  have haeq : mpLowerEdge rho = (mpLambdaMinus rho) ^ 2 := rfl
  have hbeq : mpUpperEdge rho = (mpLambdaPlus rho) ^ 2 := rfl
  by_cases hinside : mpLambdaMinus rho < u ∧ u < mpLambdaPlus rho
  · have hsquare : mpLowerEdge rho < u ^ 2 ∧ u ^ 2 < mpUpperEdge rho := by
      rw [haeq, hbeq]
      constructor
      · exact (sq_lt_sq₀ ha hu.le).mpr hinside.1
      · exact (sq_lt_sq₀ hu.le hb.le).mpr hinside.2
    have hclosed : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho :=
      ⟨hinside.1.le, hinside.2.le⟩
    have hmformula : Statlib.RandomMatrix.Vocabulary.mpDensity rho (u ^ 2) =
        Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) /
          (2 * Real.pi * rho * u ^ 2) := by
      simp only [Statlib.RandomMatrix.Vocabulary.mpDensity, if_pos hρ, if_pos hsquare]
      rw [haeq, hbeq]
    rw [hmformula]
    simp only [rootedMPDensity, if_pos hclosed, mul_one]
    field_simp [ne_of_gt hρ, ne_of_gt hu, Real.pi_ne_zero]
    <;> ring
  · have hsquare : ¬ (mpLowerEdge rho < u ^ 2 ∧ u ^ 2 < mpUpperEdge rho) := by
      intro hh
      rw [haeq, hbeq] at hh
      exact hinside ⟨(sq_lt_sq₀ ha hu.le).mp hh.1, (sq_lt_sq₀ hu.le hb.le).mp hh.2⟩
    rw [show Statlib.RandomMatrix.Vocabulary.mpDensity rho (u ^ 2) = 0 by simp [Statlib.RandomMatrix.Vocabulary.mpDensity, hρ, hsquare], mul_zero]
    by_cases hclosed : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
    · have hend : u = mpLambdaMinus rho ∨ u = mpLambdaPlus rho := by
        by_cases hl : mpLambdaMinus rho < u
        · exact Or.inr (le_antisymm hclosed.2 (le_of_not_gt (fun hh => hinside ⟨hl, hh⟩)))
        · exact Or.inl (le_antisymm (le_of_not_gt hl) hclosed.1)
      rcases hend with rfl | rfl <;> simp [rootedMPDensity]
    · simp only [rootedMPDensity, if_neg hclosed, mul_zero]

lemma mpMeasure_cdf_eq_setIntegral (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) (x : ℝ) :
    (mpMeasure rho (Set.Iic x)).toReal =
      ∫ u in Set.Iic x, Statlib.RandomMatrix.Vocabulary.mpDensity rho u := by
  rw [mpMeasure_eq_density rho hhi, withDensity_apply _ measurableSet_Iic]
  have hm : Measurable (fun u : ℝ => ENNReal.ofReal (Statlib.RandomMatrix.Vocabulary.mpDensity rho u)) :=
    ENNReal.measurable_ofReal.comp (mpDensity_measurable rho)
  have hh := integral_toReal (μ := volume.restrict (Set.Iic x)) hm.aemeasurable
    (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)
  simpa only [ENNReal.toReal_ofReal (mpDensity_nonneg rho _)] using hh.symm

lemma mpDensity_zero_nonpos (rho : ℝ) (hρ : 0 < rho) (x : ℝ) (hx : x ≤ 0) :
    Statlib.RandomMatrix.Vocabulary.mpDensity rho x = 0 := by
  have hn : ¬ (mpLowerEdge rho < x ∧ x < mpUpperEdge rho) := by
    intro hh
    have ha : 0 ≤ mpLowerEdge rho := sq_nonneg _
    linarith
  simp [Statlib.RandomMatrix.Vocabulary.mpDensity, hρ, hn]

lemma mpMeasure_cdf_eq_interval (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) (x : ℝ) :
    (mpMeasure rho (Set.Iic x)).toReal =
      ∫ u in (0 : ℝ)..x, Statlib.RandomMatrix.Vocabulary.mpDensity rho u := by
  rw [mpMeasure_cdf_eq_setIntegral rho hρ hhi x]
  have hi := mpDensity_integrable rho hρ hhi
  have hzero : (∫ u in Set.Iic (0 : ℝ), Statlib.RandomMatrix.Vocabulary.mpDensity rho u) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    exact mpDensity_zero_nonpos rho hρ u hu
  have hh := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x)
    hi.integrableOn hi.integrableOn
  simpa only [hzero, sub_zero] using hh

lemma rootedMP_intervalIntegrable (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) (a b : ℝ) :
    IntervalIntegrable (rootedMPDensity rho) volume a b := by
  have hi : IntegrableOn (rootedMPDensity rho) (Set.uIcc a b) volume := by
    apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
      (hmpDensity_measurable rho).aestronglyMeasurable (2 / (Real.pi * rho))
    filter_upwards with u
    simpa only [Real.norm_eq_abs] using rootedMPDensity_abs_bound rho rho hρ le_rfl hhi u
  exact hi.intervalIntegrable

lemma rootedMP_integral_below (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) :
    (∫ u in (0 : ℝ)..(mpLambdaMinus rho), rootedMPDensity rho u) = 0 := by
  rw [intervalIntegral.integral_of_le (hmpLambdaMinus_nonneg rho hhi)]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rcases lt_or_eq_of_le hu.2 with h | h
  · exact hmpDensity_zero_of_lt rho u h
  · rw [h]
    simp [rootedMPDensity]

lemma rootedMP_square_substitution (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, rootedMPDensity rho u) =
      ∫ x in (0 : ℝ)..(t ^ 2), Statlib.RandomMatrix.Vocabulary.mpDensity rho x := by
  have himage : (fun u : ℝ => u ^ 2) '' Set.Ioc (0 : ℝ) t = Set.Ioc (0 : ℝ) (t ^ 2) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨sq_pos_of_pos hu.1, (sq_le_sq₀ hu.1.le ht).mpr hu.2⟩
    · intro hx
      refine ⟨Real.sqrt x, ⟨Real.sqrt_pos.mpr hx.1,
        (Real.sqrt_le_iff).mpr ⟨ht, hx.2⟩⟩, Real.sq_sqrt hx.1.le⟩
  have hderiv : ∀ u ∈ Set.Ioc (0 : ℝ) t,
      HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * u) (Set.Ioc (0 : ℝ) t) u := by
    intro u _
    simpa using ((hasDerivAt_id u).pow 2).hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => u ^ 2) (Set.Ioc (0 : ℝ) t) := by
    intro u hu v hv he
    exact (sq_eq_sq₀ hu.1.le hv.1.le).mp he
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hderiv hinj
    (Statlib.RandomMatrix.Vocabulary.mpDensity rho)
  rw [himage] at hh
  have hconvert : (∫ u in Set.Ioc (0 : ℝ) t,
      |2 * u| • Statlib.RandomMatrix.Vocabulary.mpDensity rho (u ^ 2)) =
      ∫ u in Set.Ioc (0 : ℝ) t, rootedMPDensity rho u := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    change |2 * u| * Statlib.RandomMatrix.Vocabulary.mpDensity rho (u ^ 2) = rootedMPDensity rho u
    rw [abs_of_pos (mul_pos (by norm_num) hu.1),
      rootedMPDensity_eq_square_jacobian rho hρ hhi u hu.1]
  rw [hconvert] at hh
  simpa only [intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_of_le (sq_nonneg t)] using hh.symm

/-- The actual Statlib covariance MP measure has exactly the rooted-density CDF used by the job. -/
theorem mpMeasure_cdf_eq_rooted_integral (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) (x : ℝ) :
    (mpMeasure rho (Set.Iic x)).toReal =
      ∫ u in (mpLambdaMinus rho)..(Real.sqrt x), rootedMPDensity rho u := by
  have hbase := rootedMP_integral_below rho hρ hhi
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (rootedMP_intervalIntegrable rho hρ hhi 0 (mpLambdaMinus rho))
    (rootedMP_intervalIntegrable rho hρ hhi (mpLambdaMinus rho) (Real.sqrt x))
  rw [hbase, zero_add] at hadd
  rw [hadd]
  by_cases hx : 0 ≤ x
  · rw [mpMeasure_cdf_eq_interval rho hρ hhi x,
      rootedMP_square_substitution rho hρ hhi (Real.sqrt x) (Real.sqrt_nonneg x), Real.sq_sqrt hx]
  · have hx0 : x ≤ 0 := (lt_of_not_ge hx).le
    rw [Real.sqrt_eq_zero_of_nonpos hx0, intervalIntegral.integral_same,
      mpMeasure_cdf_eq_setIntegral rho hρ hhi x]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    exact mpDensity_zero_nonpos rho hρ u (hu.trans hx0)

/-- Uniform Hölder control for Statlib's genuine MP probability measure. -/
theorem mpMeasure_cdf_holder_half (rhoMinus rho : ℝ) (hmin : 0 < rhoMinus)
    (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1) :
    ∀ x y : ℝ, |(mpMeasure rho (Set.Iic x)).toReal - (mpMeasure rho (Set.Iic y)).toReal| ≤
      (2 / (Real.pi * rhoMinus)) * Real.sqrt |x - y| :=
  covarianceMP_cdf_holder_half rhoMinus rho hmin hlo hhi (mpMeasure rho)
    (mpMeasure_cdf_eq_rooted_integral rho (lt_of_lt_of_le hmin hlo) hhi)

#print axioms mpMeasure_support_four
#print axioms rootedMPDensity_eq_square_jacobian
#print axioms mpMeasure_cdf_eq_rooted_integral
#print axioms mpMeasure_cdf_holder_half
end ResidualSparseRepair20261106.DenseGaussian

