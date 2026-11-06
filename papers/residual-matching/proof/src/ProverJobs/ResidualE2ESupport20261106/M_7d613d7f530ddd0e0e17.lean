import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_b1d70f1c40e4e5140187
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
theorem statopia_math_node_3889982342_370fdb2e : ∀ (rhoMinus : ℝ) (h_rhoMinus_pos : 0 < rhoMinus) (h_rhoMinus_le : rhoMinus ≤ 1)
    (rho : ℝ) (h_rho_lo : rhoMinus ≤ rho) (h_rho_hi : rho ≤ 1)
    (hmass : (∫ u in (mpLambdaMinus rho)..(mpLambdaPlus rho), rootedMPDensity rho u) = 1)
    (htail_one : ∀ t : ℝ, t ≤ mpLambdaMinus rho → mpTail rho t = 1)
    (htail_zero : ∀ t : ℝ, mpLambdaPlus rho ≤ t → mpTail rho t = 0)
    (hcont : Continuous (mpTail rho))
    (hanti : StrictAntiOn (mpTail rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin n),
    (mpLambdaMinus rho ≤ mpQuantile rho n i ∧ mpQuantile rho n i ≤ mpLambdaPlus rho) ∧
      mpTail rho (mpQuantile rho n i) = (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ∧
      (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i), rootedMPDensity rho u)
          = 1 - (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ∧
      (∀ s : ℝ, 0 < s →
        (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i + s), rootedMPDensity rho u)
          = (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i), rootedMPDensity rho u) +
            (∫ u in (mpQuantile rho n i)..(mpQuantile rho n i + s), rootedMPDensity rho u)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i - s), rootedMPDensity rho u)
          = (∫ u in (mpLambdaMinus rho)..(mpQuantile rho n i), rootedMPDensity rho u) -
            (∫ u in (mpQuantile rho n i - s)..(mpQuantile rho n i), rootedMPDensity rho u)) := by
  /- @proof-region region.target-node.session.98c3a1abcd8bbb59 begin -/
  intro rhoMinus h_rhoMinus_pos h_rhoMinus_le rho h_rho_lo h_rho_hi hmass hTailOne hTailZero hCont hAnti n hn i
  have hlam_le : mpLambdaMinus rho ≤ mpLambdaPlus rho := by
    unfold mpLambdaMinus mpLambdaPlus
    linarith [Real.sqrt_nonneg rho]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    exact_mod_cast h
  have hL_pos : 0 < (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
    apply div_pos _ hnpos
    have hnn : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg (i : ℕ)
    linarith
  have hL_le_one : (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hnpos]
    have h1 : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      have h2 : (i : ℕ) + 1 ≤ n := Nat.succ_le_of_lt i.isLt
      exact_mod_cast h2
    linarith
  have hII : ∀ a b : ℝ, IntervalIntegrable (rootedMPDensity rho) volume a b := by
    have hrpos : 0 < rho := lt_of_lt_of_le h_rhoMinus_pos h_rho_lo
    have hlp_pos : 0 < mpLambdaPlus rho := by unfold mpLambdaPlus; positivity
    have hlm_nonneg : 0 ≤ mpLambdaMinus rho := by
      unfold mpLambdaMinus
      have h := Real.sqrt_le_one.mpr h_rho_hi
      linarith
    have hC_nonneg : 0 ≤ mpLambdaPlus rho / (Real.pi * rho) :=
      div_nonneg hlp_pos.le (le_of_lt (mul_pos Real.pi_pos hrpos))
    have hbound : ∀ x : ℝ, ‖rootedMPDensity rho x‖ ≤ mpLambdaPlus rho / (Real.pi * rho) := by
      intro x
      rw [rootedMPDensity]
      by_cases hx : mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho
      · rw [if_pos hx, mul_one]
        rcases lt_or_eq_of_le (le_trans hlm_nonneg hx.1) with hxpos | hx0
        · have hden_pos : 0 < rho * x := mul_pos hrpos hxpos
          have hsx : Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) ≤ mpLambdaPlus rho * x := by
            have hprod_le : (mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2) ≤ (mpLambdaPlus rho * x) ^ 2 := by
              have ha_le : mpLambdaPlus rho ^ 2 - x ^ 2 ≤ mpLambdaPlus rho ^ 2 := by nlinarith [sq_nonneg x]
              have hb_le : x ^ 2 - mpLambdaMinus rho ^ 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (mpLambdaMinus rho)]
              have hb_nn : 0 ≤ x ^ 2 - mpLambdaMinus rho ^ 2 := by
                have h1 : 0 ≤ x - mpLambdaMinus rho := by linarith [hx.1]
                have h2 : 0 ≤ x + mpLambdaMinus rho := by linarith [hx.1, hlm_nonneg]
                nlinarith [mul_nonneg h1 h2]
              have hP_nn : 0 ≤ mpLambdaPlus rho ^ 2 := by positivity
              calc (mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)
                  ≤ mpLambdaPlus rho ^ 2 * (x ^ 2 - mpLambdaMinus rho ^ 2) := mul_le_mul_of_nonneg_right ha_le hb_nn
                _ ≤ mpLambdaPlus rho ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hb_le hP_nn
                _ = (mpLambdaPlus rho * x) ^ 2 := by ring
            calc Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2))
                ≤ Real.sqrt ((mpLambdaPlus rho * x) ^ 2) := Real.sqrt_le_sqrt hprod_le
              _ = mpLambdaPlus rho * x := Real.sqrt_sq (mul_nonneg hlp_pos.le hxpos.le)
          have hval_nonneg : 0 ≤ (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * x) :=
            div_nonneg (by positivity) hden_pos.le
          have hval_le : (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * x) ≤ mpLambdaPlus rho / (Real.pi * rho) := by
            rw [div_le_iff₀ hden_pos]
            have h1 : (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) ≤ (1 / Real.pi) * (mpLambdaPlus rho * x) :=
              mul_le_mul_of_nonneg_left hsx (by positivity)
            have h2 : (1 / Real.pi) * (mpLambdaPlus rho * x) = (mpLambdaPlus rho / (Real.pi * rho)) * (rho * x) := by field_simp
            rw [h2] at h1
            exact h1
          rw [Real.norm_eq_abs, abs_of_nonneg hval_nonneg]
          exact hval_le
        · rw [← hx0]
          simp only [mul_zero, div_zero, norm_zero]
          exact hC_nonneg
      · rw [if_neg hx, mul_zero, norm_zero]
        exact hC_nonneg
    have hMeas : Measurable (rootedMPDensity rho) := by
      have hnum_cont : Continuous (fun x : ℝ => (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2))) := by continuity
      have hden : Measurable (fun x : ℝ => rho * x) := (continuous_const.mul continuous_id).measurable
      have hg : Measurable (fun x : ℝ => (1 / Real.pi) * Real.sqrt ((mpLambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - mpLambdaMinus rho ^ 2)) / (rho * x)) :=
        hnum_cont.measurable.div hden
      have hfac : Measurable (fun x : ℝ => if mpLambdaMinus rho ≤ x ∧ x ≤ mpLambdaPlus rho then (1 : ℝ) else 0) :=
        Measurable.ite measurableSet_Icc measurable_const measurable_const
      unfold rootedMPDensity
      exact hg.mul hfac
    have hsupp : Function.support (rootedMPDensity rho) ⊆ Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho) := by
      intro x hx
      by_contra h
      apply hx
      rw [rootedMPDensity]
      rw [if_neg (by rintro ⟨h1, h2⟩; exact h ⟨h1, h2⟩)]
      ring
    have hIntegrable : Integrable (rootedMPDensity rho) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho))) := Real.isFiniteMeasure_restrict_Icc _ _
      have hIntOn : IntegrableOn (rootedMPDensity rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) volume := by
        refine MeasureTheory.Integrable.mono (g := fun _ : ℝ => mpLambdaPlus rho / (Real.pi * rho)) (integrable_const _) hMeas.aestronglyMeasurable ?_
        filter_upwards with x
        have hR : ‖(fun _ : ℝ => mpLambdaPlus rho / (Real.pi * rho)) x‖ = mpLambdaPlus rho / (Real.pi * rho) := by
          simp only [Real.norm_eq_abs, abs_of_nonneg hC_nonneg]
        rw [hR]
        exact hbound x
      exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn
    intro a b
    exact MeasureTheory.IntegrableOn.intervalIntegrable (hIntegrable.mono_measure (MeasureTheory.Measure.restrict_le_self (s := Set.uIcc a b)))
  have hcontOn : ContinuousOn (mpTail rho) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)) := hCont.continuousOn
  have hIVT := intermediate_value_Icc hlam_le (hcontOn.neg :
    ContinuousOn (fun x => -mpTail rho x) (Set.Icc (mpLambdaMinus rho) (mpLambdaPlus rho)))
  have hmem : -((((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ)) ∈
      Set.Icc (-mpTail rho (mpLambdaMinus rho)) (-mpTail rho (mpLambdaPlus rho)) := by
    rw [hTailOne (mpLambdaMinus rho) le_rfl, hTailZero (mpLambdaPlus rho) le_rfl]
    simp only [neg_zero]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨xstar, hxstar_mem, hxstar_neg⟩ := hIVT hmem
  have hxstar_val : mpTail rho xstar = (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
    simpa only [neg_inj] using hxstar_neg
  have hle : ∀ y ∈ {x : ℝ | (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ≤ mpTail rho x}, y ≤ xstar := by
    intro y hy
    change (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ≤ mpTail rho y at hy
    by_cases hy1 : y ≤ mpLambdaMinus rho
    · exact le_trans hy1 hxstar_mem.1
    · push_neg at hy1
      by_cases hy2 : y ≤ mpLambdaPlus rho
      · by_contra hcon
        push_neg at hcon
        have hlt := hAnti hxstar_mem ⟨le_of_lt hy1, hy2⟩ hcon
        rw [hxstar_val] at hlt
        linarith
      · push_neg at hy2
        rw [hTailZero y (le_of_lt hy2)] at hy
        linarith
  have hxstarS : xstar ∈ {x : ℝ | (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) ≤ mpTail rho x} :=
    le_of_eq hxstar_val.symm
  have hQsupp : mpQuantile rho n i = xstar := by
    have h1 : mpQuantile rho n i ≤ xstar := csSup_le ⟨xstar, hxstarS⟩ hle
    have h2 : xstar ≤ mpQuantile rho n i := le_csSup ⟨xstar, hle⟩ hxstarS
    exact le_antisymm h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hQsupp]; exact hxstar_mem
  · rw [hQsupp]; exact hxstar_val
  · rw [hQsupp]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (f := rootedMPDensity rho) (μ := volume)
      (a := mpLambdaMinus rho) (b := xstar) (c := mpLambdaPlus rho) (hII _ _) (hII _ _)
    have htail : (∫ u in xstar..(mpLambdaPlus rho), rootedMPDensity rho u) = (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ) := by
      simpa only [mpTail] using hxstar_val
    rw [hmass, htail] at hadj
    linarith
  · intro s _
    rw [hQsupp]
    exact (intervalIntegral.integral_add_adjacent_intervals (f := rootedMPDensity rho) (μ := volume)
      (a := mpLambdaMinus rho) (b := xstar) (c := xstar + s) (hII _ _) (hII _ _)).symm
  · intro s _
    rw [hQsupp]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (f := rootedMPDensity rho) (μ := volume)
      (a := mpLambdaMinus rho) (b := xstar - s) (c := xstar) (hII _ _) (hII _ _)
    linarith
  /- @proof-region region.target-node.session.98c3a1abcd8bbb59 end -/

end Statlib.Imported

