import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1012033153_fe69c14e : ∀ (rho : ℝ) (hrho_pos : 0 < rho) (hrho_le : rho ≤ 1)
    (nu : MeasureTheory.Measure ℝ)
    (hnu_cdf : ∀ x : ℝ, (nu (Set.Iic x)).toReal =
      ∫ u in Set.Iic x,
        (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2)
    (hmass : ∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u = 1),
    ∀ x : ℝ, 4 ≤ x → (nu (Set.Iic x)).toReal = 1 := by
  /- @proof-region region.target-node.session.5d286673e3aab3ce begin -/
  intro rho hrho_pos hrho_le nu hnu_cdf hmass x hx
  classical
  have hsqrt_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_le
    rwa [Real.sqrt_one] at h
  have hlam_m : mpLambdaMinus rho = 1 - Real.sqrt rho := rfl
  have hlam_p : mpLambdaPlus rho = 1 + Real.sqrt rho := rfl
  have hlam_m_nonneg : 0 ≤ mpLambdaMinus rho := by rw [hlam_m]; linarith
  have hlam_p_nonneg : 0 ≤ mpLambdaPlus rho := by rw [hlam_p]; linarith
  have hlam_p_le_two : mpLambdaPlus rho ≤ 2 := by rw [hlam_p]; linarith
  have hlam_le : mpLambdaMinus rho ≤ mpLambdaPlus rho := by rw [hlam_m, hlam_p]; linarith
  have hsupp : ∀ u : ℝ, ¬ (mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho) → rootedMPDensity rho u = 0 := by
    intro u hu
    unfold rootedMPDensity
    rw [if_neg hu]
    ring
  have hρne : rho ≠ 0 := ne_of_gt hrho_pos
  set C : ℝ := (1 / Real.pi) * mpLambdaPlus rho / rho with hC
  have hC_nonneg : 0 ≤ C := by
    rw [hC]
    exact div_nonneg (mul_nonneg (by positivity) hlam_p_nonneg) hrho_pos.le
  have hbound : ∀ u : ℝ, |rootedMPDensity rho u| ≤ C := by
    intro u
    by_cases hu : mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho
    · obtain ⟨hu1, hu2⟩ := hu
      have hu0 : 0 ≤ u := le_trans hlam_m_nonneg hu1
      have hA : 0 ≤ mpLambdaPlus rho ^ 2 - u ^ 2 := by nlinarith
      have hS_le : Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))
          ≤ mpLambdaPlus rho * u := by
        rw [Real.sqrt_mul hA]
        have h1 : Real.sqrt (mpLambdaPlus rho ^ 2 - u ^ 2) ≤ mpLambdaPlus rho := by
          have h := Real.sqrt_le_sqrt (show mpLambdaPlus rho ^ 2 - u ^ 2 ≤ mpLambdaPlus rho ^ 2 by nlinarith)
          rwa [Real.sqrt_sq hlam_p_nonneg] at h
        have h2 : Real.sqrt (u ^ 2 - mpLambdaMinus rho ^ 2) ≤ u := by
          have h := Real.sqrt_le_sqrt (show u ^ 2 - mpLambdaMinus rho ^ 2 ≤ u ^ 2 by nlinarith)
          rwa [Real.sqrt_sq hu0] at h
        exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hlam_p_nonneg
      have hval : rootedMPDensity rho u
          = (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) := by
        unfold rootedMPDensity
        rw [if_pos ⟨hu1, hu2⟩, mul_one]
      rw [hval]
      rcases eq_or_lt_of_le hu0 with h0 | h0
      · rw [← h0]
        simp only [mul_zero, div_zero, abs_zero]
        exact hC_nonneg
      · have hpi : 0 ≤ (1 / Real.pi) := by positivity
        have hden : 0 < rho * u := mul_pos hrho_pos h0
        have hnn : 0 ≤ (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u) :=
          div_nonneg (mul_nonneg hpi (Real.sqrt_nonneg _)) hden.le
        rw [abs_of_nonneg hnn]
        have hle1 : (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2))
            ≤ (1 / Real.pi) * (mpLambdaPlus rho * u) :=
          mul_le_mul_of_nonneg_left hS_le hpi
        have hCalc : (1 / Real.pi) * (mpLambdaPlus rho * u) / (rho * u) = C := by
          rw [hC]
          have h1 : rho * u ≠ 0 := ne_of_gt hden
          field_simp
        calc (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)
            ≤ (1 / Real.pi) * (mpLambdaPlus rho * u) / (rho * u) := div_le_div_of_nonneg_right hle1 hden.le
          _ = C := hCalc
    · rw [hsupp u hu, abs_zero]
      exact hC_nonneg
  have hν_meas : Measurable (rootedMPDensity rho) := by
    unfold rootedMPDensity
    have h1 : Measurable (fun u : ℝ => (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - u ^ 2) * (u ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * u)) := by
      measurability
    have h2 : Measurable (fun u : ℝ => (if mpLambdaMinus rho ≤ u ∧ u ≤ mpLambdaPlus rho then (1 : ℝ) else 0)) := by
      have hc1 : Measurable (fun _ : ℝ => (1 : ℝ)) := measurable_const
      have hc0 : Measurable (fun _ : ℝ => (0 : ℝ)) := measurable_const
      have hite : Measurable (fun u : ℝ => if u ∈ Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho) then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_Icc (a := mpLambdaMinus rho) (b := mpLambdaPlus rho)) hc1 hc0
      simpa [Set.mem_Icc] using hite
    exact h1.mul h2
  have hIntν : Integrable (rootedMPDensity rho) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho))) :=
      Real.isFiniteMeasure_restrict_Icc (mpLambdaMinus rho) (mpLambdaPlus rho)
    have hOn : IntegrableOn (rootedMPDensity rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) volume :=
      MeasureTheory.Integrable.of_bound hν_meas.aestronglyMeasurable C
        (Filter.Eventually.of_forall (fun u => by simpa [Real.norm_eq_abs] using hbound u))
    exact MeasureTheory.IntegrableOn.integrable_of_ae_notMem_eq_zero hOn
      (Filter.Eventually.of_forall (fun u hu => hsupp u hu))
  have hνneg_meas : Measurable (fun u : ℝ => rootedMPDensity rho (-u)) := hν_meas.comp measurable_neg
  have hsupp_neg : ∀ u : ℝ, ¬ (-(mpLambdaPlus rho) ≤ u ∧ u ≤ -(mpLambdaMinus rho)) → rootedMPDensity rho (-u) = 0 := by
    intro u hu
    exact hsupp (-u) (fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩)
  have hIntνneg : Integrable (fun u : ℝ => rootedMPDensity rho (-u)) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho)))) :=
      Real.isFiniteMeasure_restrict_Icc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho))
    have hOn : IntegrableOn (fun u : ℝ => rootedMPDensity rho (-u)) (Set.Icc (-(mpLambdaPlus rho)) (-(mpLambdaMinus rho))) volume :=
      MeasureTheory.Integrable.of_bound hνneg_meas.aestronglyMeasurable C
        (Filter.Eventually.of_forall (fun u => by simpa [Real.norm_eq_abs] using hbound (-u)))
    exact MeasureTheory.IntegrableOn.integrable_of_ae_notMem_eq_zero hOn
      (Filter.Eventually.of_forall (fun u hu => hsupp_neg u hu))
  have hIcic : ∫ u in Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho), rootedMPDensity rho u = 1 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hlam_le]
    exact hmass
  have hIntEq : ∫ u, rootedMPDensity rho u = 1 := by
    have h := MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) (f := rootedMPDensity rho)
      (fun u hu => hsupp u hu)
    rw [← h]
    exact hIcic
  have hIntνneg_val : ∫ u, rootedMPDensity rho (-u) = 1 := by
    have hcomp : ∫ u in Set.Iic x, rootedMPDensity rho (-u) = ∫ u in Set.Ioi (-x), rootedMPDensity rho u :=
      integral_comp_neg_Iic x (rootedMPDensity rho)
    have hEq1 : ∫ u in Set.Iic x, rootedMPDensity rho (-u) = ∫ u, rootedMPDensity rho (-u) :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Set.Iic x)
        (f := fun u : ℝ => rootedMPDensity rho (-u)) (fun u hu => by
          have hxu : x < u := not_le.mp hu
          have hneg : -u < mpLambdaMinus rho := by nlinarith
          exact hsupp (-u) (fun h => absurd h.1 (not_le.mpr hneg)))
    have hEq2 : ∫ u in Set.Ioi (-x), rootedMPDensity rho u = ∫ u, rootedMPDensity rho u :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Set.Ioi (-x))
        (f := rootedMPDensity rho) (fun u hu => by
          have hux : u ≤ -x := not_lt.mp hu
          have hlt : u < mpLambdaMinus rho := by nlinarith
          exact hsupp u (fun h => absurd h.1 (not_le.mpr hlt)))
    rw [← hEq1, hcomp, hEq2, hIntEq]
  have hf : ∫ u, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 = 1 := by
    have heq : (fun u : ℝ => (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2)
        = fun u : ℝ => (1 / 2 : ℝ) • (rootedMPDensity rho u + rootedMPDensity rho (-u)) := by
      funext u
      rw [smul_eq_mul]
      ring
    rw [heq, integral_smul, smul_eq_mul, integral_add hIntν hIntνneg, hIntEq, hIntνneg_val]
    norm_num
  have hf_zero_off : ∀ u : ℝ, u ∉ Set.Iic x → (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 = 0 := by
    intro u hu
    have hxu : x < u := not_le.mp hu
    have hxlam : mpLambdaPlus rho ≤ x := by linarith
    have h1 : rootedMPDensity rho u = 0 :=
      hsupp u (fun h => absurd h.2 (not_le.mpr (lt_of_le_of_lt hxlam hxu)))
    have hneg : -u < mpLambdaMinus rho := by nlinarith
    have h2 : rootedMPDensity rho (-u) = 0 :=
      hsupp (-u) (fun h => absurd h.1 (not_le.mpr hneg))
    rw [h1, h2]
    norm_num
  have hset : ∫ u in Set.Iic x, (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2 = 1 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Set.Iic x)
      (f := fun u : ℝ => (rootedMPDensity rho u + rootedMPDensity rho (-u)) / 2) hf_zero_off]
    exact hf
  rw [hnu_cdf x]
  exact hset
  /- @proof-region region.target-node.session.5d286673e3aab3ce end -/

end Statlib.Imported

