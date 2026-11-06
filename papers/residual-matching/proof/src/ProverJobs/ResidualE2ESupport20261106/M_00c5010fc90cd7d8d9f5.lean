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
theorem statopia_math_node_3064412691_7282c3bb : ∀ (D0 Kt CD C0 D1 A L E : ℝ) (m n : ℕ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (hCD : Kt * (D0 + 12) ≤ CD)
    (hC0ge2 : 2 ≤ C0) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hD1 : D1 = 2 * CD + C0 + Kt + 1)
    (hA : A = 100 * (1 + Kt) * (1 + D1) ^ 2)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) + C0)
    (hEdef : E = Real.exp (-L / Kt))
    (hM0 : A * Real.rpow (m : ℝ) (-(D0 + 9)) ≤ 1),
    2 * (L + Kt) * E ≤ 1 ∧
      (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 ≤ (1 : ℝ) / 2 := by
  /- @proof-region region.target-node.session.98e596618431e79c begin -/
  intro D0 Kt CD C0 D1 A L E m n hD0 hKt hCD hC0ge2 hm hn hnm hD1 hA hL hEdef hM0
  have hM0' : A * (m:ℝ)^(-(D0+9)) ≤ 1 := hM0
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith only [hm1]
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith only [hn1]
  have hCDpos : 0 < CD := lt_of_lt_of_le (mul_pos hKt (by linarith only [hD0] : (0:ℝ) < D0 + 12)) hCD
  have hlogm_nn : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg hm1
  have hlogn_nn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hlogmn : Real.log ((m:ℝ)*(n:ℝ)) = Real.log (m:ℝ) + Real.log (n:ℝ) :=
    Real.log_mul (ne_of_gt hmpos) (ne_of_gt hnpos)
  have hlogmn_nn : 0 ≤ Real.log ((m:ℝ)*(n:ℝ)) := by rw [hlogmn]; linarith only [hlogm_nn, hlogn_nn]
  have hL_ge_C0 : C0 ≤ L := by
    rw [hL]
    have h : 0 ≤ CD * Real.log ((m:ℝ)*(n:ℝ)) := mul_nonneg (le_of_lt hCDpos) hlogmn_nn
    linarith only [h]
  have hLpos : 0 < L := by linarith only [hL_ge_C0, hC0ge2]
  have hlogm_ub : Real.log (m:ℝ) ≤ (m:ℝ) - 1 := Real.log_le_sub_one_of_pos hmpos
  have hlogn_ub : Real.log (n:ℝ) ≤ (n:ℝ) - 1 := Real.log_le_sub_one_of_pos hnpos
  have hlogmn_ub : Real.log ((m:ℝ)*(n:ℝ)) ≤ 2 * (m:ℝ) := by
    rw [hlogmn]
    linarith only [hlogm_ub, hlogn_ub, hnm']
  have hL_ge : Kt * (D0 + 12) * Real.log (m:ℝ) ≤ L := by
    rw [hL]
    have hlog_le : Real.log (m:ℝ) ≤ Real.log ((m:ℝ)*(n:ℝ)) := by rw [hlogmn]; linarith only [hlogn_nn]
    calc Kt * (D0 + 12) * Real.log (m:ℝ)
        ≤ CD * Real.log (m:ℝ) := mul_le_mul_of_nonneg_right hCD hlogm_nn
      _ ≤ CD * Real.log ((m:ℝ)*(n:ℝ)) := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hCDpos)
      _ ≤ CD * Real.log ((m:ℝ)*(n:ℝ)) + C0 := by linarith only [hC0ge2]
  have hLK_bound : L + Kt ≤ D1 * (m:ℝ) := by
    have hc : CD * Real.log ((m:ℝ)*(n:ℝ)) ≤ CD * (2 * (m:ℝ)) :=
      mul_le_mul_of_nonneg_left hlogmn_ub (le_of_lt hCDpos)
    have h1 : L + Kt ≤ CD * (2 * (m:ℝ)) + C0 + Kt := by rw [hL]; linarith only [hc]
    have hC0m : C0 ≤ C0 * (m:ℝ) := by
      have h : C0 * 1 ≤ C0 * (m:ℝ) := mul_le_mul_of_nonneg_left hm1 (by linarith only [hC0ge2])
      simpa using h
    have hKtm : Kt ≤ Kt * (m:ℝ) := by
      have h : Kt * 1 ≤ Kt * (m:ℝ) := mul_le_mul_of_nonneg_left hm1 (le_of_lt hKt)
      simpa using h
    have h2 : CD * (2 * (m:ℝ)) + C0 + Kt ≤ (2 * CD + C0 + Kt) * (m:ℝ) := by
      nlinarith only [hC0m, hKtm]
    have h3 : (2 * CD + C0 + Kt) * (m:ℝ) ≤ D1 * (m:ℝ) := by
      have h : 2 * CD + C0 + Kt ≤ D1 := by rw [hD1]; linarith only [hKt]
      exact mul_le_mul_of_nonneg_right h (le_of_lt hmpos)
    linarith only [h1, h2, h3]
  have hD1ge2 : 2 ≤ D1 := by rw [hD1]; linarith only [hCDpos, hKt, hC0ge2]
  have hD1pos : 0 < D1 := by linarith only [hD1ge2]
  have hA1 : 2 * D1 ≤ A := by rw [hA]; nlinarith only [hKt, hD1pos, hD1ge2]
  have hEpos : 0 < E := by rw [hEdef]; positivity
  have hE_bound : ∀ s : ℝ, s ≤ D0 + 12 → E ≤ (m:ℝ) ^ (-s) := by
    intro s hs
    have hsK : s * Real.log (m:ℝ) * Kt ≤ L := by
      have h1 : s * Real.log (m:ℝ) ≤ (D0 + 12) * Real.log (m:ℝ) :=
        mul_le_mul_of_nonneg_right hs hlogm_nn
      have h2 : s * Real.log (m:ℝ) * Kt ≤ (D0 + 12) * Real.log (m:ℝ) * Kt :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hKt)
      have h3 : (D0 + 12) * Real.log (m:ℝ) * Kt = Kt * (D0 + 12) * Real.log (m:ℝ) := by ring
      linarith only [h2, h3, hL_ge]
    rw [hEdef, Real.rpow_def_of_pos hmpos (-s)]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hKt]
    nlinarith only [hsK]
  have hEm10 : E ≤ (m:ℝ) ^ (-(D0+10)) := hE_bound (D0+10) (by linarith only [hD0])
  have hEm11 : E ≤ (m:ℝ) ^ (-(D0+11)) := hE_bound (D0+11) (by linarith only [hD0])
  have hEle1 : E ≤ 1 := by
    have hle : -L / Kt ≤ 0 := by rw [div_le_iff₀ hKt]; linarith only [hLpos]
    rw [hEdef]
    simpa using (Real.exp_le_exp.mpr hle)
  have hE2 : E ^ 2 ≤ E := by
    have h := mul_le_mul hEle1 (le_refl E) (le_of_lt hEpos) (by norm_num : (0:ℝ) ≤ 1)
    simpa [pow_two] using h
  have hu_pos : (0:ℝ) < (m:ℝ) ^ (-(D0+9)) := Real.rpow_pos_of_pos hmpos (-(D0+9))
  have hu_nn : (0:ℝ) ≤ (m:ℝ) ^ (-(D0+9)) := le_of_lt hu_pos
  have hLle : L ≤ D1 * (m:ℝ) := by linarith only [hLK_bound, hKt]
  have hLK_nn : (0:ℝ) ≤ L + Kt := by linarith only [hLpos, hKt]
  have hmE : (m:ℝ) * E ≤ (m:ℝ) ^ (-(D0+9)) := by
    have hstep : (m:ℝ) * E ≤ (m:ℝ) * (m:ℝ) ^ (-(D0+10)) :=
      mul_le_mul_of_nonneg_left hEm10 (le_of_lt hmpos)
    have heq : (m:ℝ) * (m:ℝ)^(-(D0+10)) = (m:ℝ)^(-(D0+9)) := by
      have e := Real.rpow_add_natCast' (x := (m:ℝ)) (y := -(D0+10)) (n := 1)
        (le_of_lt hmpos) (by push_cast; intro hh; linarith only [hD0, hh])
      rw [show -(D0+10) + ((1:ℕ):ℝ) = -(D0+9) by push_cast; ring] at e
      rw [pow_one] at e
      exact (mul_comm _ _).trans e.symm
    linarith only [hstep, heq]
  have hm2E : (m:ℝ)^2 * E ≤ (m:ℝ)^(-(D0+9)) := by
    have hstep : (m:ℝ)^2 * E ≤ (m:ℝ)^2 * (m:ℝ)^(-(D0+11)) :=
      mul_le_mul_of_nonneg_left hEm11 (by positivity)
    have heq : (m:ℝ)^2 * (m:ℝ)^(-(D0+11)) = (m:ℝ)^(-(D0+9)) := by
      have e := Real.rpow_add_natCast' (x := (m:ℝ)) (y := -(D0+11)) (n := 2)
        (le_of_lt hmpos) (by push_cast; intro hh; linarith only [hD0, hh])
      rw [show -(D0+11) + ((2:ℕ):ℝ) = -(D0+9) by push_cast; ring] at e
      exact (mul_comm _ _).trans e.symm
    linarith only [hstep, heq]
  have hm2E2 : (m:ℝ)^2 * E^2 ≤ (m:ℝ)^(-(D0+9)) := by
    have hstep : (m:ℝ)^2 * E^2 ≤ (m:ℝ)^2 * E :=
      mul_le_mul_of_nonneg_left hE2 (by positivity)
    linarith only [hstep, hm2E]
  have hb1 : 2 * (L + Kt) * E ≤ 1 := by
    have h2E : (0:ℝ) ≤ 2 * E := by linarith only [hEpos]
    have a1 : (L + Kt) * (2 * E) ≤ (D1 * (m:ℝ)) * (2 * E) :=
      mul_le_mul_of_nonneg_right hLK_bound h2E
    have a2 : (D1 * (m:ℝ)) * (2 * E) = 2 * D1 * ((m:ℝ) * E) := by ring
    have a3 : 2 * D1 * ((m:ℝ) * E) ≤ 2 * D1 * (m:ℝ)^(-(D0+9)) :=
      mul_le_mul_of_nonneg_left hmE (by linarith only [hD1pos])
    have a4 : 2 * D1 * (m:ℝ)^(-(D0+9)) ≤ A * (m:ℝ)^(-(D0+9)) :=
      mul_le_mul_of_nonneg_right hA1 hu_nn
    have chain : (L + Kt) * (2 * E) ≤ 1 :=
      le_trans a1 (le_trans (le_of_eq a2) (le_trans a3 (le_trans a4 hM0')))
    have hr : 2 * (L + Kt) * E = (L + Kt) * (2 * E) := by ring
    rw [hr]; exact chain
  have hLsq : L^2 ≤ (D1 * (m:ℝ))^2 := by
    have h1 : L * L ≤ (D1 * (m:ℝ)) * (D1 * (m:ℝ)) :=
      mul_le_mul hLle hLle (le_of_lt hLpos) (le_of_lt (mul_pos hD1pos hmpos))
    simpa [pow_two] using h1
  have hLKs : (L + Kt)^2 ≤ (D1 * (m:ℝ))^2 := by
    have h1 : (L + Kt) * (L + Kt) ≤ (D1 * (m:ℝ)) * (D1 * (m:ℝ)) :=
      mul_le_mul hLK_bound hLK_bound hLK_nn (le_of_lt (mul_pos hD1pos hmpos))
    simpa [pow_two] using h1
  have ha : 2 * L^2 * E ≤ 2 * D1^2 * (m:ℝ)^(-(D0+9)) := by
    have h2E : (0:ℝ) ≤ 2 * E := by linarith only [hEpos]
    have hh : L^2 * (2 * E) ≤ (D1 * (m:ℝ))^2 * (2 * E) :=
      mul_le_mul_of_nonneg_right hLsq h2E
    have s1 : 2 * L^2 * E ≤ 2 * (D1 * (m:ℝ))^2 * E := by
      calc 2 * L^2 * E = L^2 * (2 * E) := by ring
        _ ≤ (D1 * (m:ℝ))^2 * (2 * E) := hh
        _ = 2 * (D1 * (m:ℝ))^2 * E := by ring
    have s2 : 2 * (D1 * (m:ℝ))^2 * E = 2 * D1^2 * ((m:ℝ)^2 * E) := by ring
    have s3 : 2 * D1^2 * ((m:ℝ)^2 * E) ≤ 2 * D1^2 * (m:ℝ)^(-(D0+9)) :=
      mul_le_mul_of_nonneg_left hm2E (by positivity)
    linarith only [s1, s2, s3]
  have hbb : 4 * Kt * (L + Kt) * E ≤ 4 * Kt * D1 * (m:ℝ)^(-(D0+9)) := by
    have h4 : (0:ℝ) ≤ 4 * Kt * E := by nlinarith only [hKt, hEpos]
    have hh : (L + Kt) * (4 * Kt * E) ≤ (D1 * (m:ℝ)) * (4 * Kt * E) :=
      mul_le_mul_of_nonneg_right hLK_bound h4
    have s1 : 4 * Kt * (L + Kt) * E ≤ 4 * Kt * (D1 * (m:ℝ)) * E := by
      calc 4 * Kt * (L + Kt) * E = (L + Kt) * (4 * Kt * E) := by ring
        _ ≤ (D1 * (m:ℝ)) * (4 * Kt * E) := hh
        _ = 4 * Kt * (D1 * (m:ℝ)) * E := by ring
    have s2 : 4 * Kt * (D1 * (m:ℝ)) * E = 4 * Kt * D1 * ((m:ℝ) * E) := by ring
    have s3 : 4 * Kt * D1 * ((m:ℝ) * E) ≤ 4 * Kt * D1 * (m:ℝ)^(-(D0+9)) :=
      mul_le_mul_of_nonneg_left hmE (by nlinarith only [hKt, hD1pos])
    linarith only [s1, s2, s3]
  have hcc : 4 * (L + Kt)^2 * E^2 ≤ 4 * D1^2 * (m:ℝ)^(-(D0+9)) := by
    have h4 : (0:ℝ) ≤ 4 * E^2 := by positivity
    have hh : (L + Kt)^2 * (4 * E^2) ≤ (D1 * (m:ℝ))^2 * (4 * E^2) :=
      mul_le_mul_of_nonneg_right hLKs h4
    have s1 : 4 * (L + Kt)^2 * E^2 ≤ 4 * (D1 * (m:ℝ))^2 * E^2 := by
      calc 4 * (L + Kt)^2 * E^2 = (L + Kt)^2 * (4 * E^2) := by ring
        _ ≤ (D1 * (m:ℝ))^2 * (4 * E^2) := hh
        _ = 4 * (D1 * (m:ℝ))^2 * E^2 := by ring
    have s2 : 4 * (D1 * (m:ℝ))^2 * E^2 = 4 * D1^2 * ((m:ℝ)^2 * E^2) := by ring
    have s3 : 4 * D1^2 * ((m:ℝ)^2 * E^2) ≤ 4 * D1^2 * (m:ℝ)^(-(D0+9)) :=
      mul_le_mul_of_nonneg_left hm2E2 (by positivity)
    linarith only [s1, s2, s3]
  have hsum : 2 * L^2 * E + 4 * Kt * (L + Kt) * E + 4 * (L + Kt)^2 * E^2
      ≤ (6 * D1^2 + 4 * Kt * D1) * (m:ℝ)^(-(D0+9)) := by
    have h := add_le_add (add_le_add ha hbb) hcc
    have hr : (2 * D1^2 * (m:ℝ)^(-(D0+9)) + 4 * Kt * D1 * (m:ℝ)^(-(D0+9)))
        + 4 * D1^2 * (m:ℝ)^(-(D0+9)) = (6 * D1^2 + 4 * Kt * D1) * (m:ℝ)^(-(D0+9)) := by ring
    calc (2 * L^2 * E + 4 * Kt * (L + Kt) * E) + 4 * (L + Kt)^2 * E^2
        ≤ (2 * D1^2 * (m:ℝ)^(-(D0+9)) + 4 * Kt * D1 * (m:ℝ)^(-(D0+9)))
            + 4 * D1^2 * (m:ℝ)^(-(D0+9)) := h
      _ = (6 * D1^2 + 4 * Kt * D1) * (m:ℝ)^(-(D0+9)) := hr
  have hConst : 6 * D1^2 + 4 * Kt * D1 ≤ A / 2 := by
    have hAall : 12 * D1^2 + 8 * Kt * D1 ≤ A := by rw [hA]; nlinarith only [hKt, hD1pos]
    linarith only [hAall]
  have hub : (6 * D1^2 + 4 * Kt * D1) * (m:ℝ)^(-(D0+9)) ≤ 1/2 := by
    have h1 : (6 * D1^2 + 4 * Kt * D1) * (m:ℝ)^(-(D0+9)) ≤ (A/2) * (m:ℝ)^(-(D0+9)) :=
      mul_le_mul_of_nonneg_right hConst hu_nn
    have h2 : (A/2) * (m:ℝ)^(-(D0+9)) = (1/2) * (A * (m:ℝ)^(-(D0+9))) := by ring
    have h3 : (1/2) * (A * (m:ℝ)^(-(D0+9))) ≤ 1/2 := by linarith only [hM0']
    linarith only [h1, h2, h3]
  have hb2 : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2 ≤ 1 / 2 := by
    have hexp : (2 * L ^ 2 + 4 * Kt * (L + Kt)) * E + 4 * (L + Kt) ^ 2 * E ^ 2
        = 2 * L^2 * E + 4 * Kt * (L + Kt) * E + 4 * (L + Kt)^2 * E^2 := by ring
    rw [hexp]
    linarith only [hsum, hub]
  exact ⟨hb1, hb2⟩
  /- @proof-region region.target-node.session.98e596618431e79c end -/

end Statlib.Imported

