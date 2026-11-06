import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3704530209_4bfe08cb : ∀ (rhoMin rho : ℝ)
    (h_rhoMin_pos : 0 < rhoMin) (h_rho_ge : rhoMin ≤ rho) (h_rho_le : rho ≤ 1)
    (h_norm : ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho), nuRho rho x = 1)
    (h_bound : ∀ x ∈ Set.Icc (lambdaMinus rho) (lambdaPlus rho),
      0 ≤ nuRho rho x ∧ nuRho rho x ≤ 2 / (Real.pi * rhoMin))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (gamma : ℝ)
    (h_gamma : ∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x
      = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)),
    gamma ≤ lambdaPlus rho ∧ (i ∈ indexSet n → Real.pi * rhoMin / 12 ≤ gamma) := by
  /- @proof-region region.target-node.session.a9e40d4b177a0780 begin -/
  intro rhoMin rho hrhoMin hrho_lo hrho_hi hnorm hbound n hn i gamma hgamma
  constructor
  · by_contra hgt
    push_neg at hgt
    have hzero : ∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x = 0 := by
      have hempty : Set.Icc gamma (lambdaPlus rho) = ∅ := by
        ext x
        exact ⟨fun ⟨h1, h2⟩ => absurd (le_trans h1 h2) (not_le.mpr hgt),
          fun h => absurd h (by simp)⟩
      rw [hempty]
      simp
    rw [hzero] at hgamma
    have hLpos : (0 : ℝ) < (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hnum : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 - 1 / 2 := by linarith
      exact div_pos hnum (by linarith)
    linarith only [hgamma, hLpos]
  · intro hi
    by_contra hgc
    push_neg at hgc
    have hrho_pos : (0 : ℝ) < rho := lt_of_lt_of_le hrhoMin hrho_lo
    have hsqrt_le : Real.sqrt rho ≤ 1 := by
      have h := Real.sqrt_le_sqrt hrho_hi
      rwa [Real.sqrt_one] at h
    have ha_nonneg : (0 : ℝ) ≤ lambdaMinus rho := by
      rw [lambdaMinus]
      linarith
    have hf_nonneg : ∀ x : ℝ, 0 ≤ nuRho rho x := by
      intro x
      unfold nuRho
      split_ifs with hx
      · have hx0 : (0 : ℝ) ≤ x := le_trans ha_nonneg hx.1
        exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
      · exact le_refl 0
    have hL_lt : (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) < 5 / 6 := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hmem : (i : ℕ) + 1 ≤ 2 * n / 3 := by
        have h := hi
        simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h.2
      have h3 : 3 * ((i : ℕ) + 1) ≤ 2 * n := by omega
      have h4 : 3 * (((i : ℕ) : ℝ) + 1) ≤ 2 * (n : ℝ) := by exact_mod_cast h3
      have hnum : (((i : ℕ) : ℝ) + 1 - 1 / 2) = ((i : ℕ) : ℝ) + 1 / 2 := by ring
      rw [hnum]
      have h6 : ((i : ℕ) : ℝ) + 1 / 2 < (5 / 6) * (n : ℝ) := by linarith
      calc (((i : ℕ) : ℝ) + 1 / 2) / (n : ℝ)
          = (((i : ℕ) : ℝ) + 1 / 2) * (1 / (n : ℝ)) := by ring
        _ < ((5 / 6) * (n : ℝ)) * (1 / (n : ℝ)) :=
            mul_lt_mul_of_pos_right h6 (one_div_pos.mpr hnpos)
        _ = 5 / 6 := by field_simp
    have ha_le_b : lambdaMinus rho ≤ lambdaPlus rho := by
      rw [lambdaMinus, lambdaPlus]
      have := Real.sqrt_nonneg rho
      linarith
    have hc_le_b : Real.pi * rhoMin / 12 ≤ lambdaPlus rho := by
      have hr1 : rhoMin ≤ 1 := le_trans hrho_lo hrho_hi
      have h1 : Real.pi * rhoMin ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hr1 (le_of_lt Real.pi_pos)
      have h4 : (1 : ℝ) ≤ lambdaPlus rho := by
        rw [lambdaPlus]
        have := Real.sqrt_nonneg rho
        linarith
      have h3 : Real.pi / 12 < 1 := by linarith [Real.pi_lt_four]
      linarith
    have hmeas : Measurable (nuRho rho) := by
      have hF : Measurable fun x : ℝ =>
          Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
            (Real.pi * rho * x) := by
        measurability
      have hEq : nuRho rho =
          (Set.Icc (lambdaMinus rho) (lambdaPlus rho)).indicator (fun x : ℝ =>
            Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
              (Real.pi * rho * x)) := by
        funext x
        unfold nuRho
        by_cases hx : x ∈ Set.Icc (lambdaMinus rho) (lambdaPlus rho)
        · rw [if_pos (show lambdaMinus rho ≤ x ∧ x ≤ lambdaPlus rho from hx)]
          simp [Set.indicator_of_mem hx]
        · rw [if_neg (show ¬ (lambdaMinus rho ≤ x ∧ x ≤ lambdaPlus rho) from hx)]
          simp [Set.indicator, hx]
      rw [hEq]
      exact hF.indicator measurableSet_Icc
    have hbound_all : ∀ x : ℝ, ‖nuRho rho x‖ ≤ 2 / (Real.pi * rhoMin) := by
      intro x
      by_cases hx : x ∈ Set.Icc (lambdaMinus rho) (lambdaPlus rho)
      · have h1 := (hbound x hx).1
        have h2 := (hbound x hx).2
        rwa [Real.norm_of_nonneg h1]
      · have hz : nuRho rho x = 0 := by
          unfold nuRho
          rw [if_neg]
          exact hx
        rw [hz, norm_zero]
        exact div_nonneg (by norm_num) (by positivity)
    have hIoc_lt : ∀ p q : ℝ, volume (Set.Ioc p q) < ⊤ := by
      intro p q
      have h2 : volume (Set.Ioc p q) ≤ volume (Set.Icc p q) :=
        MeasureTheory.measure_mono Set.Ioc_subset_Icc_self
      have h3 : volume (Set.Icc p q) < ⊤ := by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt h2 h3
    have hII : ∀ u v : ℝ, u ≤ v → IntervalIntegrable (nuRho rho) volume u v := by
      intro u v huv
      have h1 : IntegrableOn (nuRho rho) (Set.Ioc u v) volume :=
        MeasureTheory.IntegrableOn.of_bound (hIoc_lt u v) hmeas.aestronglyMeasurable _
          (Filter.Eventually.of_forall hbound_all)
      have h2 : IntegrableOn (nuRho rho) (Set.Ioc v u) volume :=
        MeasureTheory.IntegrableOn.of_bound (hIoc_lt v u) hmeas.aestronglyMeasurable _
          (Filter.Eventually.of_forall hbound_all)
      unfold IntervalIntegrable
      exact ⟨h1, h2⟩
    have hconv : ∀ u v : ℝ, u ≤ v →
        ∫ x in u..v, nuRho rho x = ∫ x in Set.Icc u v, nuRho rho x := by
      intro u v huv
      rw [intervalIntegral.integral_of_le huv, MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hQ_mono : ∀ s t : ℝ, s ≤ t → t ≤ lambdaPlus rho →
        ∫ x in Set.Icc t (lambdaPlus rho), nuRho rho x ≤
          ∫ x in Set.Icc s (lambdaPlus rho), nuRho rho x := by
      intro s t hst htb
      have hsb : s ≤ lambdaPlus rho := le_trans hst htb
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hII s t hst) (hII t (lambdaPlus rho) htb)
      have hnn : 0 ≤ ∫ x in s..t, nuRho rho x := by
        rw [intervalIntegral.integral_of_le hst]
        exact MeasureTheory.integral_nonneg (fun x => hf_nonneg x)
      have hmono : ∫ x in t..(lambdaPlus rho), nuRho rho x ≤
          ∫ x in s..(lambdaPlus rho), nuRho rho x := by linarith
      rw [← hconv t (lambdaPlus rho) htb, ← hconv s (lambdaPlus rho) hsb]
      exact hmono
    by_cases hca : Real.pi * rhoMin / 12 < lambdaMinus rho
    · have hm2 : ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho), nuRho rho x ≤
          ∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x :=
        hQ_mono gamma (lambdaMinus rho) (by linarith) ha_le_b
      linarith only [hnorm, hm2, hgamma, hL_lt]
    · push_neg at hca
      have hQc_ge : 5 / 6 ≤
          ∫ x in Set.Icc (Real.pi * rhoMin / 12) (lambdaPlus rho), nuRho rho x := by
        have hreal : volume.real (Set.Icc (lambdaMinus rho) (Real.pi * rhoMin / 12)) =
            Real.pi * rhoMin / 12 - lambdaMinus rho := by
          have h0 : (0 : ℝ) ≤ Real.pi * rhoMin / 12 - lambdaMinus rho := by linarith
          show (volume (Set.Icc (lambdaMinus rho) (Real.pi * rhoMin / 12))).toReal = _
          rw [Real.volume_Icc, ENNReal.toReal_ofReal h0]
        have habound : ∀ x ∈ Set.Icc (lambdaMinus rho) (Real.pi * rhoMin / 12),
            ‖nuRho rho x‖ ≤ 2 / (Real.pi * rhoMin) := fun x _ => hbound_all x
        have hnb := MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (μ := volume) (s := Set.Icc (lambdaMinus rho) (Real.pi * rhoMin / 12))
          (f := nuRho rho)
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) habound
        rw [hreal] at hnb
        have hnn : 0 ≤ ∫ x in Set.Icc (lambdaMinus rho) (Real.pi * rhoMin / 12),
            nuRho rho x := MeasureTheory.integral_nonneg (fun x => hf_nonneg x)
        have step : ∫ x in Set.Icc (lambdaMinus rho) (Real.pi * rhoMin / 12), nuRho rho x ≤
            (2 / (Real.pi * rhoMin)) * (Real.pi * rhoMin / 12 - lambdaMinus rho) := by
          rw [← Real.norm_of_nonneg hnn]
          exact hnb
        have hMc : (2 / (Real.pi * rhoMin)) * (Real.pi * rhoMin / 12) = 1 / 6 := by
          field_simp
          norm_num
        have hMpos : 0 < 2 / (Real.pi * rhoMin) := by positivity
        have hle : (2 / (Real.pi * rhoMin)) * (Real.pi * rhoMin / 12 - lambdaMinus rho) ≤
            (2 / (Real.pi * rhoMin)) * (Real.pi * rhoMin / 12) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hMpos)
          linarith only [ha_nonneg]
        have hI1 : IntervalIntegrable (nuRho rho) volume (lambdaMinus rho) (Real.pi * rhoMin / 12) :=
          hII (lambdaMinus rho) (Real.pi * rhoMin / 12) hca
        have hI2 : IntervalIntegrable (nuRho rho) volume (Real.pi * rhoMin / 12) (lambdaPlus rho) :=
          hII (Real.pi * rhoMin / 12) (lambdaPlus rho) hc_le_b
        have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
        rw [hconv (lambdaMinus rho) (Real.pi * rhoMin / 12) hca,
          hconv (Real.pi * rhoMin / 12) (lambdaPlus rho) hc_le_b,
          hconv (lambdaMinus rho) (lambdaPlus rho) ha_le_b] at hadd
        rw [hnorm] at hadd
        linarith only [hadd, step, hle, hMc]
      have hQc_le : ∫ x in Set.Icc (Real.pi * rhoMin / 12) (lambdaPlus rho), nuRho rho x ≤
          ∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x :=
        hQ_mono gamma (Real.pi * rhoMin / 12) (le_of_lt hgc) hc_le_b
      linarith only [hQc_ge, hQc_le, hgamma, hL_lt]
  /- @proof-region region.target-node.session.a9e40d4b177a0780 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3704530209_4bfe08cb


