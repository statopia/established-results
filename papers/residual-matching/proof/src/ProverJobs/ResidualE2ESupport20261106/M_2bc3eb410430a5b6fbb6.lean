import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

namespace ResidualSparseRepair20261106.CDFRegularity

theorem hmpLambdaMinus_nonneg : ∀ (rho : ℝ), rho ≤ 1 → 0 ≤ mpLambdaMinus rho := by
  intro rho hrho
  have hle : Real.sqrt rho ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using hrho⟩
  simp only [mpLambdaMinus]
  linarith

theorem hmpLambdaPlus_pos : ∀ (rho : ℝ), 0 ≤ rho → 0 < mpLambdaPlus rho := by
  intro rho hrho
  have h : (0 : ℝ) ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  simp only [mpLambdaPlus]
  linarith

theorem hmpDensity_nonneg : ∀ (rho x : ℝ), 0 < rho → 0 < x → 0 ≤ rootedMPDensity rho x := by
  intro rho x hρ hx
  unfold rootedMPDensity
  have hnum : (0 : ℝ) ≤
      Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) :=
    Real.sqrt_nonneg _
  have hfac : (0 : ℝ) ≤
      (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) /
        (rho * x) :=
    div_nonneg (mul_nonneg (by positivity) hnum) (mul_pos hρ hx).le
  split
  · simpa using hfac
  · simp

theorem hmpDensity_zero_of_lt : ∀ (rho x : ℝ), x < mpLambdaMinus rho → rootedMPDensity rho x = 0 := by
  intro rho x hx
  unfold rootedMPDensity
  have hneg : ¬ (mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho) :=
    fun h => absurd h.1 (not_le.mpr hx)
  simp [hneg]

theorem hmpDensity_zero_of_gt : ∀ (rho x : ℝ), mpLambdaPlus rho < x → rootedMPDensity rho x = 0 := by
  intro rho x hx
  unfold rootedMPDensity
  have hneg : ¬ (mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho) :=
    fun h => absurd h.2 (not_le.mpr hx)
  simp [hneg]

theorem hmpDensity_zero : ∀ (rho : ℝ), rootedMPDensity rho 0 = 0 := by
  intro rho
  unfold rootedMPDensity
  simp

theorem hmpDensity_bound : ∀ (rho x : ℝ), 0 < rho → rho ≤ 1 → 0 < x →
    rootedMPDensity rho x ≤ mpLambdaPlus rho / (Real.pi * rho) := by
  intro rho x hρ hρ1 hx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlamMinus : (0 : ℝ) ≤ mpLambdaMinus rho := hmpLambdaMinus_nonneg rho hρ1
  have hlamPlus : (0 : ℝ) < mpLambdaPlus rho := hmpLambdaPlus_pos rho hρ.le
  have hpos : (0 : ℝ) < Real.pi * rho := mul_pos hpi hρ
  have hxne : x ≠ 0 := ne_of_gt hx
  have hrne : rho ≠ 0 := ne_of_gt hρ
  have hpne : Real.pi ≠ 0 := ne_of_gt hpi
  unfold rootedMPDensity
  by_cases hmask : mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho
  · rw [if_pos hmask, mul_one]
    obtain ⟨hm1, hm2⟩ := hmask
    have hp2 : (0 : ℝ) ≤ (x - mpLambdaMinus rho) * (x + mpLambdaMinus rho) := by
      apply mul_nonneg <;> linarith
    have hf2 : (0 : ℝ) ≤ x ^ 2 - mpLambdaMinus rho ^ 2 := by nlinarith [hp2]
    have hprod_le : (mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)
        ≤ (mpLambdaPlus rho * x) ^ 2 := by
      have hx2 : (0 : ℝ) ≤ x ^ 2 := by positivity
      have hmm2 : (0 : ℝ) ≤ mpLambdaMinus rho ^ 2 := by positivity
      have h1 : mpLambdaPlus rho ^ 2 - x ^ 2 ≤ mpLambdaPlus rho ^ 2 := by linarith
      have h2 : x ^ 2 - mpLambdaMinus rho ^ 2 ≤ x ^ 2 := by linarith
      have h3 : (0 : ℝ) ≤ mpLambdaPlus rho ^ 2 := by positivity
      have h4 := mul_le_mul h1 h2 hf2 h3
      nlinarith [h4]
    have hsqrt_le :
        Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2))
          ≤ mpLambdaPlus rho * x := by
      rw [Real.sqrt_le_iff]
      exact ⟨le_of_lt (mul_pos hlamPlus hx), hprod_le⟩
    rw [le_div_iff₀ hpos]
    have hxinv : (0 : ℝ) ≤ x⁻¹ := inv_nonneg.mpr hx.le
    have hmul := mul_le_mul_of_nonneg_right hsqrt_le hxinv
    have hxcan : (mpLambdaPlus rho * x) * x⁻¹ = mpLambdaPlus rho := by
      field_simp
    rw [hxcan] at hmul
    have heq : (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) /
          (rho * x) * (Real.pi * rho)
        = Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) *
            x⁻¹ := by
      field_simp
    rw [heq]
    exact hmul
  · rw [if_neg hmask, mul_zero]
    exact div_nonneg hlamPlus.le hpos.le

theorem hmpDensity_nonneg' : ∀ (rho u : ℝ), 0 < rho → 0 ≤ u → 0 ≤ rootedMPDensity rho u := by
  intro rho u hρ hu
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h]
    exact le_of_eq (hmpDensity_zero rho).symm
  · exact hmpDensity_nonneg rho u hρ h

theorem hmpDensity_bound' : ∀ (rho x : ℝ), 0 < rho → rho ≤ 1 → 0 ≤ x →
    rootedMPDensity rho x ≤ mpLambdaPlus rho / (Real.pi * rho) := by
  intro rho x hρ hρ1 hx
  have hnonneg : (0 : ℝ) ≤ mpLambdaPlus rho / (Real.pi * rho) :=
    div_nonneg (hmpLambdaPlus_pos rho hρ.le).le (mul_pos Real.pi_pos hρ).le
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, hmpDensity_zero rho]
    exact hnonneg
  · exact hmpDensity_bound rho x hρ hρ1 h

theorem hmpDensity_abs_bound : ∀ (rho x : ℝ), 0 < rho → rho ≤ 1 → 0 ≤ x →
    |rootedMPDensity rho x| ≤ mpLambdaPlus rho / (Real.pi * rho) := by
  intro rho x hρ hρ1 hx
  rw [abs_of_nonneg (hmpDensity_nonneg' rho x hρ hx)]
  exact hmpDensity_bound' rho x hρ hρ1 hx

theorem hmpDensity_abs_bound_all : ∀ (rho x : ℝ), 0 < rho → rho ≤ 1 →
    |rootedMPDensity rho x| ≤ mpLambdaPlus rho / (Real.pi * rho) := by
  intro rho x hρ hρ1
  by_cases hx : 0 ≤ x
  · exact hmpDensity_abs_bound rho x hρ hρ1 hx
  · push_neg at hx
    have hzero : rootedMPDensity rho x = 0 :=
      hmpDensity_zero_of_lt rho x (lt_of_lt_of_le hx (hmpLambdaMinus_nonneg rho hρ1))
    rw [hzero, abs_zero]
    exact div_nonneg (hmpLambdaPlus_pos rho hρ.le).le (mul_pos Real.pi_pos hρ).le

theorem hmpDensity_measurable : ∀ (rho : ℝ), Measurable (rootedMPDensity rho) := by
  intro rho
  have hbase : Measurable fun x : ℝ =>
      (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) /
        (rho * x) := by
    refine Measurable.div ?_ ?_
    · exact Measurable.mul measurable_const
        (Real.continuous_sqrt.measurable.comp (by fun_prop))
    · exact measurable_const.mul measurable_id
  have hind : Measurable fun x : ℝ =>
      (if mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho then (1 : ℝ) else 0) := by
    refine Measurable.ite measurableSet_Icc measurable_const measurable_const
  exact hbase.mul hind

theorem rootedMPDensity_abs_bound (rhoMinus rho : ℝ)
    (hmin : 0 < rhoMinus) (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1) (x : ℝ) :
    |rootedMPDensity rho x| ≤ 2 / (Real.pi * rhoMinus) := by
  have hρ : 0 < rho := lt_of_lt_of_le hmin hlo
  have he : mpLambdaPlus rho ≤ 2 := by
    have hh : Real.sqrt rho ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hhi⟩
    dsimp [mpLambdaPlus]
    linarith
  refine (hmpDensity_abs_bound_all rho x hρ hhi).trans ?_
  have hd : 0 < Real.pi * rhoMinus := mul_pos Real.pi_pos hmin
  have hd' : 0 < Real.pi * rho := mul_pos Real.pi_pos hρ
  calc mpLambdaPlus rho / (Real.pi * rho) ≤ 2 / (Real.pi * rho) :=
      div_le_div_of_nonneg_right he hd'.le
    _ ≤ 2 / (Real.pi * rhoMinus) :=
      div_le_div_of_nonneg_left (by norm_num) hd (mul_le_mul_of_nonneg_left hlo Real.pi_pos.le)

noncomputable def symmetrizedRootedMPDensity (rho x : ℝ) : ℝ :=
  (rootedMPDensity rho x + rootedMPDensity rho (-x)) / 2

theorem symmetrizedRootedMPDensity_abs_bound (rhoMinus rho : ℝ)
    (hmin : 0 < rhoMinus) (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1) (x : ℝ) :
    |symmetrizedRootedMPDensity rho x| ≤ 2 / (Real.pi * rhoMinus) := by
  have hx := rootedMPDensity_abs_bound rhoMinus rho hmin hlo hhi x
  have hn := rootedMPDensity_abs_bound rhoMinus rho hmin hlo hhi (-x)
  dsimp only [symmetrizedRootedMPDensity]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := abs_add_le (rootedMPDensity rho x) (rootedMPDensity rho (-x))
  linarith

theorem symmetrizedRootedMPDensity_integrable (rho : ℝ) (hρ : 0 < rho) (hhi : rho ≤ 1) :
    Integrable (symmetrizedRootedMPDensity rho) volume := by
  have hm : Measurable (symmetrizedRootedMPDensity rho) :=
    ((hmpDensity_measurable rho).add ((hmpDensity_measurable rho).comp measurable_neg)).div_const 2
  have hi : IntegrableOn (symmetrizedRootedMPDensity rho) (Set.Icc (-2 : ℝ) 2) volume := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hm.aestronglyMeasurable
      (2 / (Real.pi * rho))
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using symmetrizedRootedMPDensity_abs_bound rho rho hρ le_rfl hhi x
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hl := hmpLambdaMinus_nonneg rho hhi
  have hu : mpLambdaPlus rho ≤ 2 := by
    have hh : Real.sqrt rho ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hhi⟩
    dsimp [mpLambdaPlus]
    linarith
  have hz : ∀ u : ℝ, u < -2 ∨ 2 < u → rootedMPDensity rho u = 0 := by
    intro u hh
    rcases hh with hh | hh
    · exact hmpDensity_zero_of_lt rho u (by linarith)
    · exact hmpDensity_zero_of_gt rho u (by linarith)
  have hcases : x < -2 ∨ 2 < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  have hxzero : rootedMPDensity rho x = 0 := hz x hcases
  have hnzero : rootedMPDensity rho (-x) = 0 := hz (-x) (by rcases hcases with h | h <;> [right; left] <;> linarith)
  simp only [symmetrizedRootedMPDensity, hxzero, hnzero, zero_add, zero_div]

theorem symmetrized_rootedMP_cdf_lipschitz (rhoMinus rho : ℝ)
    (hmin : 0 < rhoMinus) (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1)
    (ν : Measure ℝ)
    (hcdf : ∀ x : ℝ, (ν (Set.Iic x)).toReal =
      ∫ u in Set.Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2) :
    ∀ x y : ℝ, |(ν (Set.Iic x)).toReal - (ν (Set.Iic y)).toReal| ≤
      (2 / (Real.pi * rhoMinus)) * |x - y| := by
  have hρ : 0 < rho := lt_of_lt_of_le hmin hlo
  have hi := symmetrizedRootedMPDensity_integrable rho hρ hhi
  intro x y
  rw [hcdf x, hcdf y]
  change |(∫ u in Set.Iic x, symmetrizedRootedMPDensity rho u) -
    (∫ u in Set.Iic y, symmetrizedRootedMPDensity rho u)| ≤ _
  rw [intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := symmetrizedRootedMPDensity rho) (a := y) (b := x) (C := 2 / (Real.pi * rhoMinus))
    (fun u _ => by simpa only [Real.norm_eq_abs] using
      symmetrizedRootedMPDensity_abs_bound rhoMinus rho hmin hlo hhi u)
  simpa only [Real.norm_eq_abs] using hh

#print axioms symmetrized_rootedMP_cdf_lipschitz
end ResidualSparseRepair20261106.CDFRegularity

