import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_ec65cfcb2b89edfb62bb
import ProverJobs.ResidualE2ESupport20261106.M_7617d4926dfc0173c0de
import ProverJobs.ResidualE2ESupport20261106.M_fbef5f49b6ef54c42054

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
theorem statopia_math_node_2262828856_34ee8798 : ∀ (rhoMin rho : ℝ) (h_rhoMin_pos : 0 < rhoMin) (h_rho_ge : rhoMin ≤ rho)
    (h_rho_le : rho ≤ 1),
    (∫ x, nuRho rho x ∂(volume.restrict (Set.Icc (lambdaMinus rho) (lambdaPlus rho)))) = 1 ∧
    (∀ x ∈ Set.Icc (lambdaMinus rho) (lambdaPlus rho),
      0 ≤ nuRho rho x ∧ nuRho rho x ≤ 2 / (Real.pi * rhoMin)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ i : Fin n, ∃! gamma : ℝ,
      (∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x)
        = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∃ gamma : Fin n → ℝ,
      (∀ i : Fin n, (∫ x in Set.Icc (gamma i) (lambdaPlus rho), nuRho rho x)
        = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ)) ∧
      (∀ i : Fin n, gamma i ≤ lambdaPlus rho) ∧
      (∀ i ∈ indexSet n, Real.pi * rhoMin / 12 ≤ gamma i)) := by
  /- @proof-region region.target-node.session.088bdc03bfec2fe7 begin -/
  intro rhoMin rho hrhoMin hrho_lo hrho_hi
  have hnorm : ∫ x in Set.Icc (lambdaMinus rho) (lambdaPlus rho), nuRho rho x = 1 :=
    statopia_math_node_1728106886_3c04fa7a rho (lt_of_lt_of_le hrhoMin hrho_lo) hrho_hi
  have hbound : ∀ x ∈ Set.Icc (lambdaMinus rho) (lambdaPlus rho),
      0 ≤ nuRho rho x ∧ nuRho rho x ≤ 2 / (Real.pi * rhoMin) := by
    have hrho_pos : 0 < rho := lt_of_lt_of_le hrhoMin hrho_lo
    have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hrho_hi
    have hlm_nonneg : 0 ≤ lambdaMinus rho := by
      unfold lambdaMinus
      linarith
    have hlp_nonneg : 0 ≤ lambdaPlus rho := by
      unfold lambdaPlus
      linarith [Real.sqrt_nonneg rho]
    have hlp_le_two : lambdaPlus rho ≤ 2 := by
      unfold lambdaPlus
      linarith
    have hdenmin_pos : 0 < Real.pi * rhoMin := mul_pos Real.pi_pos hrhoMin
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    by_cases hx0 : x = 0
    · have hz : nuRho rho x = 0 := by simp [nuRho, hx0]
      rw [hz]
      exact ⟨le_refl 0, div_nonneg (by norm_num) (le_of_lt hdenmin_pos)⟩
    · have hx_pos : 0 < x := lt_of_le_of_ne (le_trans hlm_nonneg hx1) (Ne.symm hx0)
      have hnu : nuRho rho x =
          Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
            (Real.pi * rho * x) := by
        unfold nuRho
        rw [if_pos ⟨hx1, hx2⟩]
      have hden_pos : 0 < Real.pi * rho * x := mul_pos (mul_pos Real.pi_pos hrho_pos) hx_pos
      have hnum_le : Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2))
          ≤ lambdaPlus rho * x := by
        have hx2m2_nonneg : 0 ≤ x ^ 2 - lambdaMinus rho ^ 2 := by
          have h := mul_nonneg (sub_nonneg.2 hx1) (by linarith : (0:ℝ) ≤ x + lambdaMinus rho)
          nlinarith [h]
        have hdiff : lambdaPlus rho ^ 2 - x ^ 2 ≤ lambdaPlus rho ^ 2 := by
          nlinarith [sq_nonneg x]
        have hprod : (lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)
            ≤ lambdaPlus rho ^ 2 * (x ^ 2 - lambdaMinus rho ^ 2) :=
          mul_le_mul_of_nonneg_right hdiff hx2m2_nonneg
        refine le_trans (Real.sqrt_le_sqrt hprod) ?_
        rw [Real.sqrt_mul (sq_nonneg (lambdaPlus rho)), Real.sqrt_sq hlp_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ hlp_nonneg
        calc Real.sqrt (x ^ 2 - lambdaMinus rho ^ 2) ≤ Real.sqrt (x ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (lambdaMinus rho)])
          _ = x := Real.sqrt_sq hx_pos.le
      refine ⟨?_, ?_⟩
      · rw [hnu]
        exact div_nonneg (Real.sqrt_nonneg _) hden_pos.le
      · rw [hnu]
        have hq : (lambdaPlus rho * x) / (Real.pi * rho * x) = lambdaPlus rho / (Real.pi * rho) := by
          rw [mul_comm (lambdaPlus rho) x, mul_comm (Real.pi * rho) x]
          exact mul_div_mul_left _ _ hx0
        have hstep : lambdaPlus rho / (Real.pi * rho) ≤ 2 / (Real.pi * rhoMin) := by
          have hA : lambdaPlus rho / (Real.pi * rho) ≤ 2 / (Real.pi * rho) := by
            rw [← sub_nonneg, ← sub_div]
            exact div_nonneg (by linarith) (mul_pos Real.pi_pos hrho_pos).le
          have hB : 2 / (Real.pi * rho) ≤ 2 / (Real.pi * rhoMin) := by
            have hle : Real.pi * rhoMin ≤ Real.pi * rho :=
              mul_le_mul_of_nonneg_left hrho_lo Real.pi_pos.le
            have hinv : 1 / (Real.pi * rho) ≤ 1 / (Real.pi * rhoMin) :=
              one_div_le_one_div_of_le hdenmin_pos hle
            have hm : 2 * (1 / (Real.pi * rho)) ≤ 2 * (1 / (Real.pi * rhoMin)) :=
              mul_le_mul_of_nonneg_left hinv (by norm_num)
            calc 2 / (Real.pi * rho) = 2 * (1 / (Real.pi * rho)) := by rw [mul_one_div]
              _ ≤ 2 * (1 / (Real.pi * rhoMin)) := hm
              _ = 2 / (Real.pi * rhoMin) := by rw [mul_one_div]
          linarith
        have hratio : Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
              (Real.pi * rho * x) ≤ (lambdaPlus rho * x) / (Real.pi * rho * x) := by
          rw [← sub_nonneg, ← sub_div]
          exact div_nonneg (by linarith) hden_pos.le
        calc Real.sqrt ((lambdaPlus rho ^ 2 - x ^ 2) * (x ^ 2 - lambdaMinus rho ^ 2)) /
              (Real.pi * rho * x)
            ≤ (lambdaPlus rho * x) / (Real.pi * rho * x) := hratio
          _ = lambdaPlus rho / (Real.pi * rho) := hq
          _ ≤ 2 / (Real.pi * rhoMin) := hstep
  have hall : ∀ (n : ℕ), 1 ≤ n → ∀ i : Fin n, ∃! gamma : ℝ,
      (∫ x in Set.Icc gamma (lambdaPlus rho), nuRho rho x)
        = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) :=
    fun n hn i =>
      statopia_math_node_763568752_c90d820b rho (lt_of_lt_of_le hrhoMin hrho_lo) hrho_hi hnorm
        n hn i
  refine ⟨hnorm, hbound, hall, ?_⟩
  intro n hn
  let gamma : Fin n → ℝ := fun i => Classical.choose (hall n hn i)
  have hgamma : ∀ i : Fin n,
      (∫ x in Set.Icc (gamma i) (lambdaPlus rho), nuRho rho x)
        = (((i : ℕ) : ℝ) + 1 - 1 / 2) / (n : ℝ) :=
    fun i => (Classical.choose_spec (hall n hn i)).1
  refine ⟨gamma, hgamma, ?_, ?_⟩
  · intro i
    exact (statopia_math_node_3704530209_4bfe08cb rhoMin rho hrhoMin hrho_lo hrho_hi hnorm hbound
      n hn i (gamma i) (hgamma i)).1
  · intro i hi
    exact (statopia_math_node_3704530209_4bfe08cb rhoMin rho hrhoMin hrho_lo hrho_hi hnorm hbound
      n hn i (gamma i) (hgamma i)).2 hi
  /- @proof-region region.target-node.session.088bdc03bfec2fe7 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_2262828856_34ee8798


