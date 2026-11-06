import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_321355006_cfdd7f53 : ∀ (alpha0 p : ℝ) (m n : ℕ)
    (halpha0 : 15 < alpha0) (hm : 3 ≤ m) (hn1 : 1 ≤ n) (hnm : n ≤ m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hgrowth : (m : ℝ) * p ≥ Real.rpow (Real.log (m : ℝ)) alpha0),
    Real.sqrt ((1 - p) / (m : ℝ)) * Real.sqrt (6 * Real.log (n : ℝ))
      + Real.rpow (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) (1 / 3)
        * Real.rpow (Real.sqrt (1 - p)) (2 / 3)
        * Real.rpow (6 * Real.log (n : ℝ)) (2 / 3)
      + (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) * (6 * Real.log (n : ℝ))
      ≤ 12 := by
  /- @proof-region region.target-node.session.ea7e5195637130ea begin -/
  intro alpha0 p m n halpha0 hm hn1 hnm hp0 hp1 hgrowth
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hnLm : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  have hLpos : 0 < Real.log (m:ℝ) := Real.log_pos (by linarith)
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
    rw [Real.log_exp] at h
    exact h
  have hLge1 : (1:ℝ) ≤ Real.log (m:ℝ) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hm3)
  have hln_nonneg : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1'
  have hln_le : Real.log (n:ℝ) ≤ Real.log (m:ℝ) := Real.log_le_log hn0 hnLm
  have hS1 : Real.sqrt ((1 - p) / (m : ℝ)) * Real.sqrt (6 * Real.log (n : ℝ)) ≤ 5 / 2 := by
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    have hx_nn : (0:ℝ) ≤ (1 - p)/(m:ℝ) := div_nonneg h1p (le_of_lt hm0)
    have h6ln_nn : (0:ℝ) ≤ 6 * Real.log (n:ℝ) := by linarith [hln_nonneg]
    have hlogm_le_m : Real.log (m:ℝ) ≤ (m:ℝ) := by
      have h := Real.log_le_sub_one_of_pos hm0
      linarith
    have hinv_nn : (0:ℝ) < 1/(m:ℝ) := div_pos one_pos hm0
    have ha : (1 - p)/(m:ℝ) ≤ 1/(m:ℝ) := by
      rw [div_le_iff₀ hm0]
      have hmul : (1/(m:ℝ)) * (m:ℝ) = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hm0)]
      rw [hmul]
      linarith
    have hb : 6 * Real.log (n:ℝ) ≤ 6 * Real.log (m:ℝ) := by linarith [hln_le]
    have step1 : ((1 - p)/(m:ℝ)) * (6 * Real.log (n:ℝ)) ≤ (1/(m:ℝ)) * (6 * Real.log (m:ℝ)) :=
      mul_le_mul ha hb h6ln_nn (le_of_lt hinv_nn)
    have key : (1/(m:ℝ)) * (6 * Real.log (m:ℝ)) ≤ 6 := by
      have hsplit : (1/(m:ℝ)) * (6 * Real.log (m:ℝ)) = (6 * Real.log (m:ℝ)) / (m:ℝ) := by ring
      rw [hsplit, div_le_iff₀ hm0]
      linarith [hlogm_le_m]
    have hprod : ((1 - p)/(m:ℝ)) * (6 * Real.log (n:ℝ)) ≤ 6 := le_trans step1 key
    rw [← Real.sqrt_mul hx_nn]
    apply le_trans (Real.sqrt_le_sqrt hprod)
    have hsq : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
    nlinarith [hsq, hnn]
  have hS2 : Real.rpow (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3)
        * Real.rpow (Real.sqrt (1 - p)) ((2 : ℝ) / 3)
        * Real.rpow (6 * Real.log (n : ℝ)) ((2 : ℝ) / 3) ≤ 7 / 2 := by
    have hM_le : max p (1 - p) ≤ 1 := max_le hp1 (by linarith)
    have hM_nn : 0 ≤ max p (1 - p) := le_trans hp0 (le_max_left p (1 - p))
    have hsqrt_rpow : Real.sqrt (Real.rpow (Real.log (m:ℝ)) alpha0) = Real.rpow (Real.log (m:ℝ)) (alpha0/2) := by
      rw [Real.sqrt_eq_rpow]
      rw [show alpha0 / 2 = alpha0 * ((1:ℝ)/2) from by ring]
      exact (Real.rpow_mul (le_of_lt hLpos) alpha0 ((1:ℝ)/2)).symm
    have hq_ge_pow : Real.rpow (Real.log (m:ℝ)) (alpha0/2) ≤ Real.sqrt ((m:ℝ)*p) := by
      have h := Real.sqrt_le_sqrt hgrowth
      rwa [hsqrt_rpow] at h
    have hLpow_pos : 0 < Real.rpow (Real.log (m:ℝ)) (alpha0/2) := Real.rpow_pos_of_pos hLpos (alpha0/2)
    have hq_pos : 0 < Real.sqrt ((m:ℝ)*p) := lt_of_lt_of_le hLpow_pos hq_ge_pow
    have hR_le_pow : max p (1 - p) / Real.sqrt ((m:ℝ)*p) ≤ Real.rpow (Real.log (m:ℝ)) (-(alpha0/2)) := by
      have hR1 : max p (1 - p) / Real.sqrt ((m:ℝ)*p) ≤ 1 / Real.sqrt ((m:ℝ)*p) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa using mul_le_mul_of_nonneg_right hM_le (inv_nonneg.mpr (le_of_lt hq_pos))
      have hR2 : 1 / Real.sqrt ((m:ℝ)*p) ≤ 1 / Real.rpow (Real.log (m:ℝ)) (alpha0/2) :=
        one_div_le_one_div_of_le hLpow_pos hq_ge_pow
      have hneg : (1:ℝ) / Real.rpow (Real.log (m:ℝ)) (alpha0/2) = Real.rpow (Real.log (m:ℝ)) (-(alpha0/2)) := by
        rw [one_div]
        change (Real.log (m:ℝ) ^ (alpha0/2))⁻¹ = Real.log (m:ℝ) ^ (-(alpha0/2))
        rw [Real.rpow_neg (le_of_lt hLpos) (alpha0/2)]
      exact le_trans hR1 (le_trans hR2 (le_of_eq hneg))
    have hR_nn : 0 ≤ max p (1 - p) / Real.sqrt ((m:ℝ)*p) := div_nonneg hM_nn (le_of_lt hq_pos)
    have hR13 : Real.rpow (max p (1 - p) / Real.sqrt ((m:ℝ)*p)) ((1:ℝ)/3) ≤ Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) := by
      have hmono : Real.rpow (max p (1 - p) / Real.sqrt ((m:ℝ)*p)) ((1:ℝ)/3) ≤ Real.rpow (Real.rpow (Real.log (m:ℝ)) (-(alpha0/2))) ((1:ℝ)/3) :=
        Real.rpow_le_rpow hR_nn hR_le_pow (by norm_num : (0:ℝ) ≤ 1/3)
      have heq : Real.rpow (Real.rpow (Real.log (m:ℝ)) (-(alpha0/2))) ((1:ℝ)/3) = Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) := by
        rw [show -(alpha0/6) = (-(alpha0/2)) * ((1:ℝ)/3) from by ring]
        exact (Real.rpow_mul (le_of_lt hLpos) (-(alpha0/2)) ((1:ℝ)/3)).symm
      exact le_trans hmono (le_of_eq heq)
    have ha_le1 : Real.rpow (Real.sqrt (1 - p)) ((2:ℝ)/3) ≤ 1 := by
      have hsp_nonneg : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
      have hsp_le : Real.sqrt (1 - p) ≤ 1 := by
        have h : Real.sqrt (1 - p) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        rwa [Real.sqrt_one] at h
      have h := Real.rpow_le_rpow hsp_nonneg hsp_le (by norm_num : (0:ℝ) ≤ 2/3)
      rw [show (1:ℝ) ^ ((2:ℝ)/3) = 1 from Real.one_rpow _] at h
      exact h
    have ha_nn : 0 ≤ Real.rpow (Real.sqrt (1 - p)) ((2:ℝ)/3) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb_nn : 0 ≤ 6 * Real.log (n:ℝ) := by linarith [hln_nonneg]
    have hb_le : Real.rpow (6 * Real.log (n:ℝ)) ((2:ℝ)/3) ≤ Real.rpow 6 ((2:ℝ)/3) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3) := by
      have h1 : Real.rpow (6 * Real.log (n:ℝ)) ((2:ℝ)/3) ≤ Real.rpow (6 * Real.log (m:ℝ)) ((2:ℝ)/3) :=
        Real.rpow_le_rpow hb_nn (by linarith [hln_le]) (by norm_num : (0:ℝ) ≤ 2/3)
      have h2 : Real.rpow (6 * Real.log (m:ℝ)) ((2:ℝ)/3) = Real.rpow 6 ((2:ℝ)/3) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3) := by
        change (6 * Real.log (m:ℝ)) ^ ((2:ℝ)/3) = (6:ℝ) ^ ((2:ℝ)/3) * (Real.log (m:ℝ)) ^ ((2:ℝ)/3)
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) (le_of_lt hLpos)]
      exact le_trans h1 (le_of_eq h2)
    have hb6_nn : 0 ≤ Real.rpow (6 * Real.log (n:ℝ)) ((2:ℝ)/3) := Real.rpow_nonneg hb_nn _
    have hL_prod : Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3) ≤ 1 := by
      have h_exp : Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3) ≤ Real.rpow (Real.log (m:ℝ)) (alpha0/6) :=
        Real.rpow_le_rpow_of_exponent_le hLge1 (by linarith)
      have hneg : Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) = (Real.rpow (Real.log (m:ℝ)) (alpha0/6))⁻¹ :=
        Real.rpow_neg (le_of_lt hLpos) (alpha0/6)
      have hpos : 0 < Real.rpow (Real.log (m:ℝ)) (alpha0/6) := Real.rpow_pos_of_pos hLpos (alpha0/6)
      calc Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3)
          ≤ Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * Real.rpow (Real.log (m:ℝ)) (alpha0/6) :=
              mul_le_mul_of_nonneg_left h_exp (Real.rpow_nonneg (le_of_lt hLpos) _)
        _ = (Real.rpow (Real.log (m:ℝ)) (alpha0/6))⁻¹ * Real.rpow (Real.log (m:ℝ)) (alpha0/6) := by rw [hneg]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have h6 : Real.rpow (6:ℝ) ((2:ℝ)/3) ≤ 7/2 := by
      have hu_nn : 0 ≤ Real.rpow (6:ℝ) ((2:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
      have hu3r : (Real.rpow (6:ℝ) ((2:ℝ)/3)) ^ ((3:ℕ):ℝ) = 36 := by
        change ((6:ℝ) ^ ((2:ℝ)/3)) ^ ((3:ℕ):ℝ) = 36
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 6) ((2:ℝ)/3) ((3:ℕ):ℝ)]
        rw [show ((2:ℝ)/3) * ((3:ℕ):ℝ) = ((2:ℕ):ℝ) from by norm_num]
        rw [Real.rpow_natCast]
        norm_num
      have hy3 : ((7/2:ℝ)) ^ ((3:ℕ):ℝ) = 343/8 := by
        rw [Real.rpow_natCast]
        norm_num
      have key : (Real.rpow (6:ℝ) ((2:ℝ)/3)) ^ ((3:ℕ):ℝ) ≤ ((7/2:ℝ)) ^ ((3:ℕ):ℝ) := by
        rw [hu3r, hy3]
        norm_num
      exact (Real.rpow_le_rpow_iff (x := Real.rpow (6:ℝ) ((2:ℝ)/3)) (y := (7/2:ℝ)) (z := ((3:ℕ):ℝ)) hu_nn (by norm_num) (by norm_num)).mp key
    have hstepA : Real.rpow (max p (1 - p) / Real.sqrt ((m:ℝ)*p)) ((1:ℝ)/3) * Real.rpow (Real.sqrt (1 - p)) ((2:ℝ)/3) ≤ Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * 1 :=
      mul_le_mul hR13 ha_le1 ha_nn (Real.rpow_nonneg (le_of_lt hLpos) (-(alpha0/6)))
    have hlt_nn : 0 ≤ Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * 1 :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hLpos) (-(alpha0/6))) zero_le_one
    have hcombine : Real.rpow (max p (1 - p) / Real.sqrt ((m:ℝ)*p)) ((1:ℝ)/3) * Real.rpow (Real.sqrt (1 - p)) ((2:ℝ)/3) * Real.rpow (6 * Real.log (n:ℝ)) ((2:ℝ)/3)
        ≤ (Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * 1) * (Real.rpow 6 ((2:ℝ)/3) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3)) :=
      mul_le_mul hstepA hb_le hb6_nn hlt_nn
    calc Real.rpow (max p (1 - p) / Real.sqrt ((m:ℝ)*p)) ((1:ℝ)/3) * Real.rpow (Real.sqrt (1 - p)) ((2:ℝ)/3) * Real.rpow (6 * Real.log (n:ℝ)) ((2:ℝ)/3)
        ≤ (Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * 1) * (Real.rpow 6 ((2:ℝ)/3) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3)) := hcombine
      _ = Real.rpow 6 ((2:ℝ)/3) * (Real.rpow (Real.log (m:ℝ)) (-(alpha0/6)) * Real.rpow (Real.log (m:ℝ)) ((2:ℝ)/3)) := by ring
      _ ≤ Real.rpow 6 ((2:ℝ)/3) * 1 := mul_le_mul_of_nonneg_left hL_prod (Real.rpow_nonneg (by norm_num) _)
      _ = Real.rpow 6 ((2:ℝ)/3) := by ring
      _ ≤ 7 / 2 := h6
  have hS3 : (max p (1 - p) / Real.sqrt ((m : ℝ) * p)) * (6 * Real.log (n : ℝ)) ≤ 6 := by
    have hM_le : max p (1 - p) ≤ 1 := max_le hp1 (by linarith)
    have hL_sq_le : Real.log (m:ℝ)^2 ≤ (m:ℝ) * p := by
      have h1 : Real.rpow (Real.log (m:ℝ)) (2:ℝ) ≤ Real.rpow (Real.log (m:ℝ)) alpha0 :=
        Real.rpow_le_rpow_of_exponent_le hLge1 (by linarith)
      have h2 : Real.rpow (Real.log (m:ℝ)) (2:ℝ) = Real.log (m:ℝ)^2 := by
        change (Real.log (m:ℝ)) ^ ((2:ℕ):ℝ) = Real.log (m:ℝ)^2
        rw [Real.rpow_natCast]
      rw [h2] at h1
      linarith [hgrowth, h1]
    have hq_ge : Real.log (m:ℝ) ≤ Real.sqrt ((m:ℝ)*p) := by
      calc Real.log (m:ℝ) = Real.sqrt (Real.log (m:ℝ)^2) := (Real.sqrt_sq (le_of_lt hLpos)).symm
        _ ≤ Real.sqrt ((m:ℝ)*p) := Real.sqrt_le_sqrt hL_sq_le
    have hq_pos : 0 < Real.sqrt ((m:ℝ)*p) := lt_of_lt_of_le hLpos hq_ge
    have hR1 : max p (1 - p) / Real.sqrt ((m:ℝ)*p) ≤ 1 / Real.sqrt ((m:ℝ)*p) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_right hM_le (inv_nonneg.mpr (le_of_lt hq_pos))
    have hR2 : 1 / Real.sqrt ((m:ℝ)*p) ≤ 1 / Real.log (m:ℝ) :=
      one_div_le_one_div_of_le hLpos hq_ge
    have hR_le : max p (1 - p) / Real.sqrt ((m:ℝ)*p) ≤ 1 / Real.log (m:ℝ) := le_trans hR1 hR2
    have h6Le : 6 * Real.log (n:ℝ) ≤ 6 * Real.log (m:ℝ) := by linarith [hln_le]
    have h6Ln_nn : 0 ≤ 6 * Real.log (n:ℝ) := by linarith [hln_nonneg]
    have step : (max p (1 - p) / Real.sqrt ((m:ℝ)*p)) * (6 * Real.log (n:ℝ))
        ≤ (1 / Real.log (m:ℝ)) * (6 * Real.log (m:ℝ)) :=
      mul_le_mul hR_le h6Le h6Ln_nn (le_of_lt (one_div_pos.mpr hLpos))
    have final_le : (1 / Real.log (m:ℝ)) * (6 * Real.log (m:ℝ)) ≤ 6 := by
      have hsplit : (1/(Real.log (m:ℝ))) * (6 * Real.log (m:ℝ)) = (6 * Real.log (m:ℝ)) / (Real.log (m:ℝ)) := by ring
      rw [hsplit, div_le_iff₀ hLpos]
    exact le_trans step final_le
  have e12 : (5:ℝ) / 2 + 7 / 2 + 6 = 12 := by norm_num
  linarith [hS1, hS2, hS3, e12]
  /- @proof-region region.target-node.session.ea7e5195637130ea end -/

end

end Statlib.Imported

