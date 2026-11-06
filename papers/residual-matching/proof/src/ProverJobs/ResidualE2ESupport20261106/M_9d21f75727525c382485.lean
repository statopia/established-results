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
theorem statopia_math_node_4055001358_e7cf4d8e : ∀ (D0 Kt alpha0 CD : ℝ) (hD0 : 0 < D0) (hKt : 0 < Kt) (halpha0 : 15 < alpha0)
    (hCD : Kt * (D0 + 12) ≤ CD),
    ∃ M0 : ℕ, ∀ (m n : ℕ) (L : ℝ), 1 ≤ m → 1 ≤ n → n ≤ m → M0 ≤ m →
      L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 →
      ∀ (p : ℝ), 0 < p → p ≤ 1 →
      Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p →
      Real.sqrt ((n : ℝ) / p) * (64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)) ≤
        Real.rpow (n : ℝ) (-(D0 + 5)) := by
  /- @proof-region region.target-node.session.67486abc0341d397 begin -/
  intro D0 Kt alpha0 CD hD0 hKt halpha0 hCD
  have hKt1 : (0:ℝ) < Kt + 1 := by linarith
  have hD01 : (0:ℝ) < D0 + 1 := by linarith
  have halpha1 : (0:ℝ) < alpha0 + 1 := by linarith
  obtain ⟨T, hTval⟩ : ∃ T : ℝ, T = (10:ℝ) ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := ⟨_, rfl⟩
  have hTpos : 0 < T := by
    rw [hTval]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKt1 4)) (pow_pos hD01 4)) (pow_pos halpha1 4)
  have hCDpos : 0 < CD := by
    have h1 : 0 < Kt * (D0 + 12) := mul_pos hKt (by linarith)
    linarith
  have hATpos : 0 < CD + T := by linarith
  have hATKpos : 0 < CD + T + Kt := by linarith
  obtain ⟨Cc, hCval⟩ : ∃ Cc : ℝ, Cc = 64 * (Kt + 1) * (CD + T) * (CD + T + Kt) ^ 2 := ⟨_, rfl⟩
  have hCpos : 0 < Cc := by
    rw [hCval]
    have h64 : (0:ℝ) < 64 * (Kt + 1) := by linarith
    exact mul_pos (mul_pos h64 hATpos) (pow_pos hATKpos 2)
  obtain ⟨beta, hbetaval⟩ : ∃ beta : ℝ, beta = alpha0 / 2 := ⟨_, rfl⟩
  have hbetapos : 0 < beta := by rw [hbetaval]; linarith
  obtain ⟨ell, hellval⟩ : ∃ ell : ℝ, ell = Real.log 2 := ⟨_, rfl⟩
  have hellpos : 0 < ell := by rw [hellval]; exact Real.log_pos (by norm_num)
  obtain ⟨M0, hM03, hM0K⟩ : ∃ M0 : ℕ, 3 ≤ M0 ∧ Cc / ell ^ beta < (M0:ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (max 3 (Cc / ell ^ beta))
    refine ⟨k, ?_, ?_⟩
    · have h : (3:ℝ) ≤ (k:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hk)
      exact_mod_cast h
    · exact lt_of_le_of_lt (le_max_right _ _) hk
  refine ⟨M0, ?_⟩
  intro m n L hm hn hnm hMm hL p hp0 hp1 hsparse
  have hm3 : 3 ≤ m := le_trans hM03 hMm
  have hm2 : 2 ≤ m := le_trans (by norm_num) hm3
  have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmRpos : (0:ℝ) < (m:ℝ) := by linarith
  have hmR1lt : (1:ℝ) < (m:ℝ) := by
    have h : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm3
    linarith
  have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnRpos : (0:ℝ) < (n:ℝ) := by linarith
  have hx1 : (1:ℝ) ≤ (m:ℝ) * (n:ℝ) := by
    have hxy := mul_le_mul hmR1 hnR1 (by norm_num : (0:ℝ) ≤ 1) (le_trans (by norm_num : (0:ℝ) ≤ 1) hmR1)
    simpa using hxy
  have hxpos : (0:ℝ) < (m:ℝ) * (n:ℝ) := by linarith
  have hlogx : 0 ≤ Real.log ((m:ℝ) * (n:ℝ)) := Real.log_nonneg hx1
  have hLval : L = CD * Real.log ((m:ℝ) * (n:ℝ)) + T := by
    have h2 := hL
    rw [← hTval] at h2
    exact h2
  have hLpos : 0 < L := by
    rw [hLval]
    have h1 : 0 ≤ CD * Real.log ((m:ℝ) * (n:ℝ)) := mul_nonneg hCDpos.le hlogx
    linarith
  have hlmpos : 0 < Real.log (m:ℝ) := Real.log_pos hmR1lt
  have hApos : 0 < (Real.log (m:ℝ)) ^ alpha0 := Real.rpow_pos_of_pos hlmpos alpha0
  have hAp : (Real.log (m:ℝ)) ^ alpha0 / p ≤ (m:ℝ) := by
    rw [div_le_iff₀ hp0]
    exact hsparse
  have h1p : 1 / p ≤ (m:ℝ) * (Real.log (m:ℝ)) ^ (-alpha0) := by
    have h3 : (m:ℝ) * (Real.log (m:ℝ)) ^ (-alpha0) = (m:ℝ) / (Real.log (m:ℝ)) ^ alpha0 := by
      rw [Real.rpow_neg hlmpos.le, div_eq_mul_inv]
    have hid : (1/p) * (Real.log (m:ℝ)) ^ alpha0 = (Real.log (m:ℝ)) ^ alpha0 / p := by
      rw [one_div, mul_comm, div_eq_mul_inv]
    rw [h3, le_div_iff₀ hApos, hid]
    exact hAp
  have hnp : (n:ℝ) / p ≤ ((m:ℝ) * (n:ℝ)) * (Real.log (m:ℝ)) ^ (-alpha0) := by
    have hpinv : p⁻¹ ≤ (m:ℝ) * (Real.log (m:ℝ)) ^ (-alpha0) := by
      rw [← one_div]; exact h1p
    rw [div_eq_mul_inv]
    calc (n:ℝ) * p⁻¹ ≤ (n:ℝ) * ((m:ℝ) * (Real.log (m:ℝ)) ^ (-alpha0)) :=
          mul_le_mul_of_nonneg_left hpinv (le_of_lt hnRpos)
      _ = ((m:ℝ) * (n:ℝ)) * (Real.log (m:ℝ)) ^ (-alpha0) := by ring
  have hsqrt : Real.sqrt ((n:ℝ) / p) ≤
      ((m:ℝ) * (n:ℝ)) ^ ((1:ℝ)/2) * (Real.log (m:ℝ)) ^ (-beta) := by
    have hlmnn : (0:ℝ) ≤ (Real.log (m:ℝ)) ^ (-alpha0) := (Real.rpow_pos_of_pos hlmpos _).le
    have hstep : ((Real.log (m:ℝ)) ^ (-alpha0)) ^ ((1:ℝ)/2)
        = (Real.log (m:ℝ)) ^ (-alpha0 * ((1:ℝ)/2)) :=
      (Real.rpow_mul hlmpos.le (-alpha0) ((1:ℝ)/2)).symm
    have hbexp : -alpha0 * ((1:ℝ)/2) = -beta := by rw [hbetaval]; ring
    have hsqrtsq : Real.sqrt (((m:ℝ) * (n:ℝ)) * (Real.log (m:ℝ)) ^ (-alpha0))
        = ((m:ℝ) * (n:ℝ)) ^ ((1:ℝ)/2) * (Real.log (m:ℝ)) ^ (-beta) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hxpos.le hlmnn, hstep, hbexp]
    calc Real.sqrt ((n:ℝ) / p)
        ≤ Real.sqrt (((m:ℝ) * (n:ℝ)) * (Real.log (m:ℝ)) ^ (-alpha0)) := Real.sqrt_le_sqrt hnp
      _ = ((m:ℝ) * (n:ℝ)) ^ ((1:ℝ)/2) * (Real.log (m:ℝ)) ^ (-beta) := hsqrtsq
  have hexp : Real.exp (-L / Kt) ≤ Real.rpow ((m:ℝ) * (n:ℝ)) (-(D0 + 12)) := by
    have hR : Real.rpow ((m:ℝ) * (n:ℝ)) (-(D0 + 12))
        = Real.exp (Real.log ((m:ℝ) * (n:ℝ)) * (-(D0 + 12))) := Real.rpow_def_of_pos hxpos _
    rw [hR]
    apply Real.exp_le_exp.mpr
    rw [hLval]
    have hmul : Kt * (D0 + 12) * Real.log ((m:ℝ) * (n:ℝ)) ≤ CD * Real.log ((m:ℝ) * (n:ℝ)) :=
      mul_le_mul_of_nonneg_right hCD hlogx
    have hkey : -(CD * Real.log ((m:ℝ) * (n:ℝ)) + T) ≤ Real.log ((m:ℝ) * (n:ℝ)) * (-(D0 + 12)) * Kt := by
      have h2 : (D0 + 12) * Real.log ((m:ℝ) * (n:ℝ)) * Kt ≤ CD * Real.log ((m:ℝ) * (n:ℝ)) := by
        have e : (D0 + 12) * Real.log ((m:ℝ) * (n:ℝ)) * Kt
            = Kt * (D0 + 12) * Real.log ((m:ℝ) * (n:ℝ)) := by ring
        rw [e]
        exact hmul
      have e2 : Real.log ((m:ℝ) * (n:ℝ)) * (-(D0 + 12)) * Kt
          = -((D0 + 12) * Real.log ((m:ℝ) * (n:ℝ)) * Kt) := by ring
      rw [e2]
      linarith [h2, hTpos]
    exact (div_le_iff₀ hKt).mpr hkey
  have hpoly : 64 * (Kt + 1) * L * (L + Kt) ^ 2 ≤ Cc * ((m:ℝ) * (n:ℝ)) ^ 3 := by
    have hlogle : Real.log ((m:ℝ) * (n:ℝ)) ≤ (m:ℝ) * (n:ℝ) := by
      have h := Real.log_le_sub_one_of_pos hxpos
      linarith
    have hLle : L ≤ (CD + T) * ((m:ℝ) * (n:ℝ)) := by
      rw [hLval]
      have h1 : CD * Real.log ((m:ℝ) * (n:ℝ)) ≤ CD * ((m:ℝ) * (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hlogle hCDpos.le
      have h2 : T ≤ T * ((m:ℝ) * (n:ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hx1 hTpos.le
        simpa using h
      have h3 : CD * ((m:ℝ) * (n:ℝ)) + T * ((m:ℝ) * (n:ℝ)) = (CD + T) * ((m:ℝ) * (n:ℝ)) := by ring
      linarith [h1, h2, h3]
    have hLKle : L + Kt ≤ (CD + T + Kt) * ((m:ℝ) * (n:ℝ)) := by
      have h2 : Kt ≤ Kt * ((m:ℝ) * (n:ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hx1 hKt.le
        simpa using h
      have h3 : (CD + T) * ((m:ℝ) * (n:ℝ)) + Kt * ((m:ℝ) * (n:ℝ))
          = (CD + T + Kt) * ((m:ℝ) * (n:ℝ)) := by ring
      linarith [hLle, h2, h3]
    have hsq : (L + Kt) ^ 2 ≤ ((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) ^ 2 := by
      have hBA : (0:ℝ) ≤ ((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) - (L + Kt) := by linarith
      have hAB : (0:ℝ) ≤ ((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) + (L + Kt) := by linarith
      have hmul2 : (0:ℝ) ≤ (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) - (L + Kt))
          * (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) + (L + Kt)) := mul_nonneg hBA hAB
      have hid2 : ((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) ^ 2 - (L + Kt) ^ 2
          = (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) - (L + Kt))
            * (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) + (L + Kt)) := by ring
      linarith [hmul2, hid2]
    rw [hCval]
    have hmain : 64 * (Kt + 1) * (L * (L + Kt) ^ 2)
        ≤ 64 * (Kt + 1) *
            (((CD + T) * ((m:ℝ) * (n:ℝ))) * (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0:ℝ) ≤ 64 * (Kt + 1))
      exact mul_le_mul hLle hsq (sq_nonneg _) (mul_nonneg hATpos.le (by linarith))
    have hxx : ((CD + T) * ((m:ℝ) * (n:ℝ))) * (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) ^ 2)
        = (CD + T) * (CD + T + Kt) ^ 2 * ((m:ℝ) * (n:ℝ)) ^ 3 := by ring
    calc 64 * (Kt + 1) * L * (L + Kt) ^ 2 = 64 * (Kt + 1) * (L * (L + Kt) ^ 2) := by ring
      _ ≤ 64 * (Kt + 1) *
            (((CD + T) * ((m:ℝ) * (n:ℝ))) * (((CD + T + Kt) * ((m:ℝ) * (n:ℝ))) ^ 2)) := hmain
      _ = 64 * (Kt + 1) * ((CD + T) * (CD + T + Kt) ^ 2 * ((m:ℝ) * (n:ℝ)) ^ 3) := by rw [hxx]
      _ = 64 * (Kt + 1) * (CD + T) * (CD + T + Kt) ^ 2 * ((m:ℝ) * (n:ℝ)) ^ 3 := by ring
  have hPE : 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)
      ≤ Cc * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 9)) := by
    have h1 : 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt)
        ≤ (Cc * ((m:ℝ) * (n:ℝ)) ^ 3) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 12)) :=
      mul_le_mul hpoly hexp (Real.exp_pos _).le (mul_nonneg hCpos.le (by positivity))
    have h2 : (Cc * ((m:ℝ) * (n:ℝ)) ^ 3) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 12))
        = Cc * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 9)) := by
      have hpair : ((m:ℝ) * (n:ℝ)) ^ (3:ℝ) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 12))
          = ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 9)) := by
        rw [← Real.rpow_add hxpos]
        rw [show (3:ℝ) + (-(D0 + 12)) = -(D0 + 9) by ring]
      rw [show ((m:ℝ) * (n:ℝ)) ^ 3 = ((m:ℝ) * (n:ℝ)) ^ (3:ℝ) from
        (Real.rpow_natCast ((m:ℝ) * (n:ℝ)) 3).symm]
      rw [mul_assoc, hpair]
    rwa [h2] at h1
  have hxid : ((m:ℝ) * (n:ℝ)) ^ ((1:ℝ)/2) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 9))
      = ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5)) := by
    rw [← Real.rpow_add hxpos]
    rw [show ((1:ℝ)/2) + (-(D0 + 9)) = -(D0 + 8.5) by ring]
  have hClm : Cc * (Real.log (m:ℝ)) ^ (-beta) ≤ (m:ℝ) ^ (D0 + 8.5) := by
    have hellle : ell ≤ Real.log (m:ℝ) := by
      rw [hellval]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hlm_le : (Real.log (m:ℝ)) ^ (-beta) ≤ ell ^ (-beta) :=
      Real.rpow_le_rpow_of_nonpos hellpos hellle (by linarith : -beta ≤ 0)
    have hA1 : Cc * (Real.log (m:ℝ)) ^ (-beta) ≤ Cc * ell ^ (-beta) :=
      mul_le_mul_of_nonneg_left hlm_le hCpos.le
    have hA2 : Cc * ell ^ (-beta) < (m:ℝ) := by
      have h1 : Cc * ell ^ (-beta) = Cc / ell ^ beta := by
        rw [Real.rpow_neg (le_of_lt hellpos), div_eq_mul_inv]
      have h2 : Cc / ell ^ beta < (M0:ℝ) := hM0K
      have h3 : (M0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hMm
      linarith
    have hm1le : (m:ℝ) ≤ (m:ℝ) ^ (D0 + 8.5) := by
      have h1 : (m:ℝ) ^ (1:ℝ) ≤ (m:ℝ) ^ (D0 + 8.5) :=
        (Real.rpow_le_rpow_left_iff hmR1lt).mpr (by linarith)
      rwa [Real.rpow_one] at h1
    linarith
  have hs3 : (n:ℝ) ^ (-(D0 + 8.5)) ≤ (n:ℝ) ^ (-(D0 + 5)) := by
    have hsplit : (n:ℝ) ^ (-(D0 + 8.5)) = (n:ℝ) ^ (-(D0 + 5)) * (n:ℝ) ^ (-(3.5) : ℝ) := by
      rw [show -(D0 + 8.5) = -(D0 + 5) + (-(3.5) : ℝ) by ring]
      rw [Real.rpow_add hnRpos]
    rw [hsplit]
    calc (n:ℝ) ^ (-(D0 + 5)) * (n:ℝ) ^ (-(3.5) : ℝ)
        ≤ (n:ℝ) ^ (-(D0 + 5)) * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hnR1 (by norm_num : (-(3.5) : ℝ) ≤ 0))
            (Real.rpow_nonneg hnRpos.le _)
      _ = (n:ℝ) ^ (-(D0 + 5)) := by ring
  have key3 : Cc * (Real.log (m:ℝ)) ^ (-beta) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5))
      ≤ (n:ℝ) ^ (-(D0 + 5)) := by
    have hs1 : Cc * (Real.log (m:ℝ)) ^ (-beta) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5))
        ≤ (m:ℝ) ^ (D0 + 8.5) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5)) :=
      mul_le_mul_of_nonneg_right hClm (Real.rpow_nonneg hxpos.le _)
    have hs2 : (m:ℝ) ^ (D0 + 8.5) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5))
        = (n:ℝ) ^ (-(D0 + 8.5)) := by
      have hsplit2 : ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5))
          = (m:ℝ) ^ (-(D0 + 8.5)) * (n:ℝ) ^ (-(D0 + 8.5)) := by
        rw [Real.mul_rpow (le_of_lt hmRpos) (le_of_lt hnRpos)]
      have hm0 : (m:ℝ) ^ (D0 + 8.5) * (m:ℝ) ^ (-(D0 + 8.5)) = (1:ℝ) := by
        rw [← Real.rpow_add hmRpos]
        rw [show (D0 + 8.5) + (-(D0 + 8.5)) = (0:ℝ) by ring]
        exact Real.rpow_zero _
      calc (m:ℝ) ^ (D0 + 8.5) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5))
          = (m:ℝ) ^ (D0 + 8.5) * ((m:ℝ) ^ (-(D0 + 8.5)) * (n:ℝ) ^ (-(D0 + 8.5))) := by
            rw [hsplit2]
        _ = ((m:ℝ) ^ (D0 + 8.5) * (m:ℝ) ^ (-(D0 + 8.5))) * (n:ℝ) ^ (-(D0 + 8.5)) := by ring
        _ = (n:ℝ) ^ (-(D0 + 8.5)) := by rw [hm0, one_mul]
    calc Cc * (Real.log (m:ℝ)) ^ (-beta) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5))
        ≤ (m:ℝ) ^ (D0 + 8.5) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5)) := hs1
      _ = (n:ℝ) ^ (-(D0 + 8.5)) := hs2
      _ ≤ (n:ℝ) ^ (-(D0 + 5)) := hs3
  have hPnonneg : (0:ℝ) ≤ 64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt) := by
    have h1 : (0:ℝ) < 64 * (Kt + 1) * L := by
      have h2 : (0:ℝ) < 64 * (Kt + 1) := by linarith
      exact mul_pos h2 hLpos
    exact (mul_pos (mul_pos h1 (pow_pos (by linarith : (0:ℝ) < L + Kt) 2)) (Real.exp_pos _)).le
  have key2 : (((m:ℝ) * (n:ℝ)) ^ ((1:ℝ)/2) * (Real.log (m:ℝ)) ^ (-beta))
      * (Cc * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 9)))
      = Cc * (Real.log (m:ℝ)) ^ (-beta) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5)) := by
    rw [← hxid]
    ring
  calc Real.sqrt ((n:ℝ) / p) * (64 * (Kt + 1) * L * (L + Kt) ^ 2 * Real.exp (-L / Kt))
      ≤ (((m:ℝ) * (n:ℝ)) ^ ((1:ℝ)/2) * (Real.log (m:ℝ)) ^ (-beta))
          * (Cc * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 9))) :=
        mul_le_mul hsqrt hPE hPnonneg
          (mul_nonneg (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg hlmpos.le _))
    _ = Cc * (Real.log (m:ℝ)) ^ (-beta) * ((m:ℝ) * (n:ℝ)) ^ (-(D0 + 8.5)) := key2
    _ ≤ Real.rpow (n:ℝ) (-(D0 + 5)) := key3
  /- @proof-region region.target-node.session.67486abc0341d397 end -/

end Statlib.Imported

