import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.Vocabulary.Distributions
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_25b575e712786d8e5814
import ProverJobs.ResidualE2ESupport20261106.M_42376bcdfff0114fa6af
import ProverJobs.ResidualE2ESupport20261106.M_71b77c9e423ac8b670cf
import ProverJobs.ResidualE2ESupport20261106.M_bfd32cde8e43b4eecc52

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory Set
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported Statlib.RandomMatrix.Vocabulary

namespace ResidualSparseRepair20261106.DenseGaussian

theorem rootedMP_integral_Iic (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) (x : ℝ) :
    (∫ u in Iic x, rootedMPDensity rho u) =
      ∫ u in (mpLambdaMinus rho)..x, rootedMPDensity rho u := by
  have hi := (statopia_math_node_39993368_ddc1c47b rho hρ hhi).1
  have hz : (∫ u in Iic (mpLambdaMinus rho), rootedMPDensity rho u) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    change u ≤ mpLambdaMinus rho at hu
    rcases lt_or_eq_of_le hu with hl | he
    · exact CDFRegularity.hmpDensity_zero_of_lt rho u hl
    · rw [he]
      simp [rootedMPDensity]
  have hh := intervalIntegral.integral_Iic_sub_Iic (a := mpLambdaMinus rho) (b := x)
    hi.integrableOn hi.integrableOn
  simpa only [hz, sub_zero] using hh

theorem rootedMP_integral_univ (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) :
    (∫ u, rootedMPDensity rho u) = 1 := by
  have hs : Function.support (rootedMPDensity rho) ⊆ Ioc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hm : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho := by
      by_contra hh
      exact hu (by simp only [rootedMPDensity, if_neg hh, mul_zero])
    refine ⟨lt_of_le_of_ne hm.1 ?_, hm.2⟩
    intro he
    exact hu (by rw [← he]; simp [rootedMPDensity])
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  exact statopia_math_node_503473485_2877602c rho hρ hhi

theorem symmetricSqrtMP_cdf_eq_density (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) (x : ℝ) :
    (symmetricSqrtMeasure (mpMeasure rho)).real (Iic x) =
      ∫ u in Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 := by
  haveI : IsProbabilityMeasure (mpMeasure rho) :=
    Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho hρ
  have hmass := statopia_math_node_503473485_2877602c rho hρ hhi
  by_cases hx : 0 ≤ x
  · rw [symmetricSqrtMeasure_cdf_nonneg _ x hx,
      statopia_math_node_1589508588_b622d3e8 rho x hρ hhi hx hmass]
    have hh := mpMeasure_cdf_eq_rooted_integral rho hρ hhi (x ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx] at hh
    change (1 / 2 : ℝ) + 1 / 2 * (mpMeasure rho (Iic (x ^ 2))).toReal = _
    rw [hh]
    ring
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [symmetricSqrtMeasure_cdf_neg _ x hx']
    have hsingle : mpMeasure rho {x ^ 2} = 0 := by
      rw [mpMeasure_eq_density rho hhi]
      exact measure_singleton _
    have hIio : (mpMeasure rho).real (Iio (x ^ 2)) = (mpMeasure rho).real (Iic (x ^ 2)) := by
      exact congrArg ENNReal.toReal (measure_congr (Iio_ae_eq_Iic' hsingle))
    have hF := mpMeasure_cdf_eq_rooted_integral rho hρ hhi (x ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hx'] at hF
    change (mpMeasure rho).real (Iic (x ^ 2)) = _ at hF
    rw [hIio, hF]
    have hi := (statopia_math_node_39993368_ddc1c47b rho hρ hhi).1
    have hni := (statopia_math_node_39993368_ddc1c47b rho hρ hhi).2
    have hzero : (∫ u in Iic x, rootedMPDensity rho u) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro u hu
      change u ≤ x at hu
      exact CDFRegularity.hmpDensity_zero_of_lt rho u
        (lt_of_le_of_lt hu (hx'.trans_le (CDFRegularity.hmpLambdaMinus_nonneg rho hhi)))
    have htail : (∫ u in Ioi (-x), rootedMPDensity rho u) =
        1 - ∫ u in (mpLambdaMinus rho)..(-x), rootedMPDensity rho u := by
      have hh := intervalIntegral.integral_Iic_add_Ioi (f := rootedMPDensity rho) (b := -x)
        hi.integrableOn hi.integrableOn
      rw [rootedMP_integral_univ rho hρ hhi, rootedMP_integral_Iic rho hρ hhi] at hh
      linarith
    rw [integral_div, integral_add hi.integrableOn hni.integrableOn,
      hzero, zero_add, integral_comp_neg_Iic, htail]
    ring

end ResidualSparseRepair20261106.DenseGaussian

#print axioms ResidualSparseRepair20261106.DenseGaussian.symmetricSqrtMP_cdf_eq_density

