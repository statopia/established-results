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
theorem statopia_math_node_1255057691_189df777 : ∀ (D : ℝ) (hD : 0 < D) (rhoM : ℝ)
    (hrhoM : 0 < rhoM) (alpha : ℝ) (halpha : 1 / 2 < alpha),
    ∃ m0 : ℕ, 2 ≤ m0 ∧ ∀ (m n : ℕ) (p : ℝ), n ≤ m → m0 ≤ m →
      rhoM * (m : ℝ) ≤ (n : ℝ) →
      Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
      2 * Real.exp (-(2 * (m : ℝ) * (n : ℝ) * p ^ 2)) ≤ Real.rpow (n : ℝ) (-D) := by
  /- @proof-region region.target-node.session.14a4032ddbb8278c begin -/
  intro D hD rhoM hrhoM alpha halpha
  have he : (0 : ℝ) < 2 * alpha - 1 := by linarith
  obtain ⟨k, -, hke⟩ : ∃ k : ℕ, 1 ≤ k ∧ (1 : ℝ) ≤ (k : ℝ) * (2 * alpha - 1) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (2 * alpha - 1))
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_trans (div_pos one_pos he) hk
    refine ⟨k, ?_, ?_⟩
    · have hk0 : 0 < k := by exact_mod_cast hkpos
      omega
    · have hmul : 1 < (k : ℝ) * (2 * alpha - 1) := by
        have h := mul_lt_mul_of_pos_right hk he
        have h1 : (1 / (2 * alpha - 1)) * (2 * alpha - 1) = 1 := by field_simp
        linarith [h, h1]
      linarith
  set M : ℝ := max (2 * D) (2 * Real.log 2) with hM
  set u : ℝ := max (M / rhoM) 1
  have hu1 : 1 ≤ u := le_max_right _ _
  have huM : M / rhoM ≤ u := le_max_left _ _
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  set T : ℝ := max 1 (u ^ (k : ℝ))
  have hT1 : 1 ≤ T := le_max_left _ _
  have hcore : M / rhoM ≤ T ^ (2 * alpha - 1) := by
    have h1 : u ^ (k : ℝ) ≤ T := le_max_right _ _
    have h2 : (u ^ (k : ℝ)) ^ (2 * alpha - 1) = u ^ ((k : ℝ) * (2 * alpha - 1)) := by
      rw [← Real.rpow_mul (le_of_lt hu0)]
    have h3 : u ^ (1 : ℝ) ≤ u ^ ((k : ℝ) * (2 * alpha - 1)) :=
      Real.rpow_le_rpow_of_exponent_le hu1 hke
    rw [Real.rpow_one] at h3
    have h4 : (u ^ (k : ℝ)) ^ (2 * alpha - 1) ≤ T ^ (2 * alpha - 1) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hu0) _) h1 (le_of_lt he)
    linarith [huM, h2, h3, h4]
  have hgrow : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → D * t + Real.log 2 ≤ rhoM * (t ^ alpha) ^ 2 := by
    refine ⟨T, ?_⟩
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hT1 ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hmono : T ^ (2 * alpha - 1) ≤ t ^ (2 * alpha - 1) :=
      Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le zero_lt_one hT1)) ht (le_of_lt he)
    have hMrho : rhoM * (M / rhoM) = M := by field_simp
    have hb : M ≤ rhoM * t ^ (2 * alpha - 1) := by
      rw [← hMrho]
      exact mul_le_mul_of_nonneg_left (le_trans hcore hmono) (le_of_lt hrhoM)
    have hY1 : 2 * D ≤ rhoM * t ^ (2 * alpha - 1) := by
      linarith [hb, hM, le_max_left (2 * D) (2 * Real.log 2)]
    have hY2 : 2 * Real.log 2 ≤ rhoM * t ^ (2 * alpha - 1) := by
      linarith [hb, hM, le_max_right (2 * D) (2 * Real.log 2)]
    have hYpos : (0 : ℝ) < rhoM * t ^ (2 * alpha - 1) := by linarith [hY1]
    have hpow2 : (t ^ alpha) ^ 2 = t ^ (2 * alpha) := by
      rw [pow_two, ← Real.rpow_add htpos, show alpha + alpha = 2 * alpha by ring]
    have hsplit : t ^ (2 * alpha) = t * t ^ (2 * alpha - 1) := by
      have h := Real.rpow_add htpos (1 : ℝ) (2 * alpha - 1)
      rw [Real.rpow_one] at h
      rw [show (1 : ℝ) + (2 * alpha - 1) = 2 * alpha by ring] at h
      exact h
    have hX : rhoM * (t ^ alpha) ^ 2 = t * (rhoM * t ^ (2 * alpha - 1)) := by
      rw [hpow2, hsplit]
      ring
    have h1 : 2 * D * t ≤ t * (rhoM * t ^ (2 * alpha - 1)) := by
      nlinarith [hY1, htpos.le]
    have h2 : 2 * Real.log 2 ≤ t * (rhoM * t ^ (2 * alpha - 1)) := by
      nlinarith [hY2, ht1, hYpos]
    rw [hX]
    linarith
  obtain ⟨T, hT⟩ := hgrow
  obtain ⟨m0, hm0ge, hm0T⟩ : ∃ m0 : ℕ, 2 ≤ m0 ∧ T ≤ Real.log (m0 : ℝ) := by
    obtain ⟨m0, hm0⟩ := exists_nat_ge (max (Real.exp T) 2)
    refine ⟨m0, ?_, ?_⟩
    · have h2 : (2 : ℝ) ≤ (m0 : ℝ) := le_trans (le_max_right _ _) hm0
      exact_mod_cast h2
    · have hexp : Real.exp T ≤ (m0 : ℝ) := le_trans (le_max_left _ _) hm0
      calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
        _ ≤ Real.log ((m0 : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos T) hexp
  refine ⟨m0, hm0ge, ?_⟩
  intro m n p hnm hmm hn hmp
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by
    have h3 : 2 ≤ m := le_trans hm0ge hmm
    exact_mod_cast h3
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm0le : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmm
  have hm0pos : (0 : ℝ) < (m0 : ℝ) := by
    have h2 : (2 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast hm0ge
    linarith
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (mul_pos hrhoM hmpos) hn
  have hrpowpos : 0 < Real.rpow (Real.log (m : ℝ)) alpha := Real.rpow_pos_of_pos hlogpos alpha
  have hstep1 : rhoM * ((m : ℝ) * p) ^ 2 ≤ (m : ℝ) * (n : ℝ) * p ^ 2 := by
    have h2 : (m : ℝ) * (rhoM * (m : ℝ)) ≤ (m : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hn (le_of_lt hmpos)
    calc rhoM * ((m : ℝ) * p) ^ 2 = (m : ℝ) * (rhoM * (m : ℝ)) * p ^ 2 := by ring
      _ ≤ (m : ℝ) * (n : ℝ) * p ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg p)
  have hpow_sq : (Real.rpow (Real.log (m : ℝ)) alpha) ^ 2 ≤ ((m : ℝ) * p) ^ 2 := by
    nlinarith [hrpowpos, hmp]
  have hD1 : rhoM * (Real.rpow (Real.log (m : ℝ)) alpha) ^ 2 ≤ (m : ℝ) * (n : ℝ) * p ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hpow_sq (le_of_lt hrhoM)) hstep1
  set S : ℝ := 2 * (m : ℝ) * (n : ℝ) * p ^ 2 with hS
  have hS2 : 2 * (rhoM * (Real.rpow (Real.log (m : ℝ)) alpha) ^ 2) ≤ S := by
    rw [hS]
    linarith
  have hA0 : (0 : ℝ) ≤ rhoM * (Real.rpow (Real.log (m : ℝ)) alpha) ^ 2 :=
    mul_nonneg (le_of_lt hrhoM) (sq_nonneg _)
  have hTapp : T ≤ Real.log (m : ℝ) := le_trans hm0T (Real.log_le_log hm0pos hm0le)
  have hTlog : D * Real.log (m : ℝ) + Real.log 2 ≤
      rhoM * (Real.rpow (Real.log (m : ℝ)) alpha) ^ 2 := hT (Real.log (m : ℝ)) hTapp
  have hSge : D * Real.log (m : ℝ) + Real.log 2 ≤ S := by linarith
  have hexp_le : Real.exp (-S) ≤ Real.exp (-(D * Real.log (m : ℝ) + Real.log 2)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have h3 : Real.exp (-(D * Real.log (m : ℝ))) = (m : ℝ) ^ (-D) := by
    rw [show -(D * Real.log (m : ℝ)) = Real.log (m : ℝ) * (-D) by ring]
    exact (Real.rpow_def_of_pos hmpos (-D)).symm
  have hval : Real.exp (-(D * Real.log (m : ℝ) + Real.log 2)) = (1 / 2) * (m : ℝ) ^ (-D) := by
    have h2 : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [show -(D * Real.log (m : ℝ) + Real.log 2)
        = -(D * Real.log (m : ℝ)) + -(Real.log 2) by ring, Real.exp_add, h3, h2]
    ring
  have hmainS : 2 * Real.exp (-S) ≤ (m : ℝ) ^ (-D) := by
    have h2 := mul_le_mul_of_nonneg_left hexp_le (by norm_num : (0 : ℝ) ≤ 2)
    rw [hval] at h2
    linarith
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hpowD : (n : ℝ) ^ D ≤ (m : ℝ) ^ D :=
    Real.rpow_le_rpow (le_of_lt hnpos) hnmR (le_of_lt hD)
  have hmono : (m : ℝ) ^ (-D) ≤ (n : ℝ) ^ (-D) := by
    have hm' : (m : ℝ) ^ (-D) = ((m : ℝ) ^ D)⁻¹ := Real.rpow_neg (le_of_lt hmpos) D
    have hn' : (n : ℝ) ^ (-D) = ((n : ℝ) ^ D)⁻¹ := Real.rpow_neg (le_of_lt hnpos) D
    rw [hm', hn']
    simpa [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos D) hpowD
  exact le_trans hmainS hmono
  /- @proof-region region.target-node.session.14a4032ddbb8278c end -/

end Statlib.Imported

end


