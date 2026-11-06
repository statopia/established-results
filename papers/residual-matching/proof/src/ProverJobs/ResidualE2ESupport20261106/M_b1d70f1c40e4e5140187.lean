import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_393f49f06ac135373093

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
theorem statopia_math_node_3459853827_bfe4599e : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (rho : ℝ) (h_rho_lo : rhoMinus ≤ rho) (h_rho_hi : rho ≤ 1)
    (hmass : (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u) = 1),
    Continuous (mpTail rho) ∧
      StrictAntiOn (mpTail rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) := by
  /- @proof-region region.target-node.session.b180d1834ca7f554 begin -/
  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le rho h_rho_lo h_rho_hi hmass
  have hrho_pos : 0 < rho := lt_of_lt_of_le h_rhoMinus_pos h_rho_lo
  have hsq_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsq_le_one : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr h_rho_hi
  have hlm_eq : mpLambdaMinus rho = 1 - Real.sqrt rho := rfl
  have hlp_eq : mpLambdaPlus rho = 1 + Real.sqrt rho := rfl
  have hlm_nonneg : 0 ≤ mpLambdaMinus rho := by rw [hlm_eq]; linarith
  have hlm_le_lp : mpLambdaMinus rho ≤ mpLambdaPlus rho := by rw [hlm_eq, hlp_eq]; linarith
  have hlp_pos : 0 < mpLambdaPlus rho := by rw [hlp_eq]; linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hC_nonneg : 0 ≤ mpLambdaPlus rho / (Real.pi * rho) :=
    le_of_lt (div_pos hlp_pos (mul_pos Real.pi_pos hrho_pos))
  have hν_zero_out : ∀ x, ¬ (mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho) →
      rootedMPDensity rho x = 0 := by
    intro x hx
    rw [rootedMPDensity, if_neg hx, mul_zero]
  have hν_nonneg : ∀ x, 0 ≤ rootedMPDensity rho x := by
    intro x
    by_cases hx : mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho
    · rw [rootedMPDensity, if_pos hx, mul_one]
      exact div_nonneg
        (mul_nonneg (div_nonneg zero_le_one (le_of_lt hpi_pos)) (Real.sqrt_nonneg _))
        (mul_nonneg (le_of_lt hrho_pos) (le_trans hlm_nonneg hx.1))
    · rw [rootedMPDensity, if_neg hx]
      simp
  have hν_support : Function.support (rootedMPDensity rho) ⊆
      Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
    intro x hx
    by_contra hcon
    exact hx (hν_zero_out x hcon)
  have hbd : ∀ x ∈ Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho),
      ‖rootedMPDensity rho x‖ ≤ mpLambdaPlus rho / (Real.pi * rho) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [rootedMPDensity, if_pos ⟨hx1, hx2⟩, mul_one]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [mul_zero, div_zero, norm_zero]
      exact hC_nonneg
    · have hx_nonneg : 0 ≤ x := le_trans hlm_nonneg hx1
      have hxpos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
      have hA1 : 0 ≤ mpLambdaPlus rho ^ 2 - x ^ 2 := by nlinarith
      have hA2 : 0 ≤ x ^ 2 - mpLambdaMinus rho ^ 2 := by nlinarith
      have hsqrtA : Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2))
          = Real.sqrt (mpLambdaPlus rho ^ 2 - x ^ 2) *
            Real.sqrt (x ^ 2 - mpLambdaMinus rho ^ 2) := Real.sqrt_mul hA1 _
      have hs1 : Real.sqrt (mpLambdaPlus rho ^ 2 - x ^ 2) ≤ mpLambdaPlus rho := by
        have h2 := Real.sqrt_le_sqrt (by nlinarith : mpLambdaPlus rho ^ 2 - x ^ 2 ≤ mpLambdaPlus rho ^ 2)
        rwa [Real.sqrt_sq (le_of_lt hlp_pos)] at h2
      have hs2 : Real.sqrt (x ^ 2 - mpLambdaMinus rho ^ 2) ≤ x := by
        have h2 := Real.sqrt_le_sqrt (by nlinarith : x ^ 2 - mpLambdaMinus rho ^ 2 ≤ x ^ 2)
        rwa [Real.sqrt_sq (le_of_lt hxpos)] at h2
      have hsA : Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) ≤
          mpLambdaPlus rho * x := by
        rw [hsqrtA]
        exact mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (le_of_lt hlp_pos)
      have hexpr : 0 ≤ (1 / Real.pi) *
          Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * x) :=
        div_nonneg
          (mul_nonneg (div_nonneg zero_le_one (le_of_lt hpi_pos)) (Real.sqrt_nonneg _))
          (le_of_lt (mul_pos hrho_pos hxpos))
      rw [Real.norm_eq_abs, abs_of_nonneg hexpr, mul_div_assoc]
      have hstep : Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) /
            (rho * x) ≤ mpLambdaPlus rho / rho := by
        have hinv : Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) *
            x⁻¹ ≤ mpLambdaPlus rho := by
          have h := mul_le_mul_of_nonneg_right hsA (inv_nonneg.mpr (le_of_lt hxpos))
          rwa [mul_assoc, mul_inv_cancel₀ hxpos.ne', mul_one] at h
        calc Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) /
              (rho * x)
            = Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) *
                x⁻¹ * rho⁻¹ := by
              rw [div_eq_mul_inv, mul_inv_rev, mul_assoc]
          _ ≤ mpLambdaPlus rho * rho⁻¹ :=
            mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr (le_of_lt hrho_pos))
          _ = mpLambdaPlus rho / rho := by rw [div_eq_mul_inv]
      calc (1 / Real.pi) * (Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) *
              (x ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * x))
          ≤ (1 / Real.pi) * (mpLambdaPlus rho / rho) :=
            mul_le_mul_of_nonneg_left hstep (div_nonneg zero_le_one (le_of_lt hpi_pos))
        _ = mpLambdaPlus rho / (Real.pi * rho) := by field_simp
  have hbd_all : ∀ a : ℝ, ‖rootedMPDensity rho a‖ ≤ mpLambdaPlus rho / (Real.pi * rho) := by
    intro a
    by_cases h : mpLambdaMinus rho ≤ a ∧ a ≤ mpLambdaPlus rho
    · exact hbd a h
    · rw [hν_zero_out a h, norm_zero]
      exact hC_nonneg
  have hIntOnConst : IntegrableOn (fun _ : ℝ => mpLambdaPlus rho / (Real.pi * rho))
      (Set.Ioc (mpLambdaMinus rho - 1) (mpLambdaPlus rho + 1)) volume := by
    have h := intervalIntegral.intervalIntegrable_const (μ := volume)
      (a := mpLambdaMinus rho - 1) (b := mpLambdaPlus rho + 1)
      (c := mpLambdaPlus rho / (Real.pi * rho))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h
  have hmeas : Measurable (rootedMPDensity rho) := by
    have hx2 : Measurable fun x : ℝ => x ^ 2 := (continuous_id.pow 2).measurable
    have hnum : Measurable fun x : ℝ => (1 / Real.pi) *
        Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) := by
      refine Measurable.mul measurable_const ?_
      exact Real.continuous_sqrt.measurable.comp
        ((measurable_const.sub hx2).mul (hx2.sub measurable_const))
    have hden : Measurable fun x : ℝ => rho * x := measurable_const.mul measurable_id
    have hif : Measurable fun x : ℝ =>
        if mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho then (1 : ℝ) else 0 :=
      Measurable.ite measurableSet_Icc measurable_const measurable_const
    exact (hnum.div hden).mul hif
  have haebd : ∀ᵐ a ∂(volume.restrict (Set.Ioc (mpLambdaMinus rho - 1) (mpLambdaPlus rho + 1))),
      ‖rootedMPDensity rho a‖ ≤ ‖(fun _ : ℝ => mpLambdaPlus rho / (Real.pi * rho)) a‖ := by
    refine Filter.Eventually.of_forall (fun a => ?_)
    have h1 : ‖(fun _ : ℝ => mpLambdaPlus rho / (Real.pi * rho)) a‖ =
        mpLambdaPlus rho / (Real.pi * rho) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hC_nonneg]
    rw [h1]
    exact hbd_all a
  have hIntOn : IntegrableOn (rootedMPDensity rho)
      (Set.Ioc (mpLambdaMinus rho - 1) (mpLambdaPlus rho + 1)) volume :=
    MeasureTheory.Integrable.mono hIntOnConst hmeas.aestronglyMeasurable haebd
  have hsupp : Function.support (rootedMPDensity rho) ⊆
      Set.Ioc (mpLambdaMinus rho - 1) (mpLambdaPlus rho + 1) := by
    intro x hx
    have hx' := hν_support hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hInt : Integrable (rootedMPDensity rho) volume :=
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn
  have hcont : Continuous (mpTail rho) := by
    have hfun : mpTail rho =
        fun t => -(∫ x in (mpLambdaPlus rho)..t, rootedMPDensity rho x) := by
      funext t
      rw [mpTail, intervalIntegral.integral_symm]
    rw [hfun]
    exact (hInt.continuous_primitive (mpLambdaPlus rho)).neg
  have hII : ∀ a b : ℝ, IntervalIntegrable (rootedMPDensity rho) volume a b := by
    intro a b
    exact MeasureTheory.IntegrableOn.intervalIntegrable (hInt.mono_measure Measure.restrict_le_self)
  have hν_pos : ∀ m ∈ Set.Ioo (mpLambdaMinus rho) (mpLambdaPlus rho),
      0 < rootedMPDensity rho m := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := hm
    have hmpos : 0 < m := lt_of_le_of_lt hlm_nonneg hm1
    have hA1 : 0 < mpLambdaPlus rho ^ 2 - m ^ 2 := by nlinarith
    have hA2 : 0 < m ^ 2 - mpLambdaMinus rho ^ 2 := by nlinarith
    have hsqrtpos : 0 < Real.sqrt ((mpLambdaPlus rho ^ 2 - m ^ 2) * (m ^ 2 - mpLambdaMinus rho ^ 2)) :=
      Real.sqrt_pos.mpr (mul_pos hA1 hA2)
    rw [rootedMPDensity, if_pos ⟨le_of_lt hm1, le_of_lt hm2⟩, mul_one]
    exact div_pos (mul_pos (div_pos one_pos hpi_pos) hsqrtpos) (mul_pos hrho_pos hmpos)
  have hkey : ∀ s t : ℝ, mpLambdaMinus rho ≤ s → s ≤ t → t ≤ mpLambdaPlus rho →
      mpTail rho s = mpTail rho t → s = t := by
    intro s t hs1 hst ht2 heq
    by_contra hne
    have hlt : s < t := lt_of_le_of_ne hst hne
    have hadd : mpTail rho s - mpTail rho t = ∫ x in s..t, rootedMPDensity rho x := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals (hII s t) (hII t (mpLambdaPlus rho))
      rw [mpTail, mpTail]
      linarith
    have hzero : ∫ x in s..t, rootedMPDensity rho x = 0 := by
      rw [← hadd, heq, sub_self]
    have hposint : 0 < ∫ x in ((s + t) / 2)..((s + t) / 2 + (t - s) / 4), rootedMPDensity rho x := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on (hII _ _) ?_ (by linarith)
      intro x hx
      exact hν_pos x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmono : ∫ x in ((s + t) / 2)..((s + t) / 2 + (t - s) / 4), rootedMPDensity rho x ≤
        ∫ x in s..t, rootedMPDensity rho x :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall hν_nonneg) (hII s t)
    linarith
  have hinj : Set.InjOn (mpTail rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) := by
    intro s hs t ht hst
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨ht1, ht2⟩ := ht
    rcases le_total s t with h | h
    · exact hkey s t hs1 h ht2 hst
    · exact (hkey t s ht1 h hs2 hst.symm).symm
  have hba : mpTail rho (mpLambdaPlus rho) ≤ mpTail rho (mpLambdaMinus rho) := by
    have h1 : mpTail rho (mpLambdaPlus rho) = 0 := by
      rw [mpTail, intervalIntegral.integral_same]
    have h2 : mpTail rho (mpLambdaMinus rho) = 1 := hmass
    rw [h1, h2]
    norm_num
  exact ⟨hcont, ContinuousOn.strictAntiOn_of_injOn_Icc hlm_le_lp hba hcont.continuousOn hinj⟩
  /- @proof-region region.target-node.session.b180d1834ca7f554 end -/

end Statlib.Imported

