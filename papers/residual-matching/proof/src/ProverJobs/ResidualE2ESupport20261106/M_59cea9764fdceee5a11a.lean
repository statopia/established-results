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
theorem statopia_math_node_1813084325_ae3c2094 : ∀ (D0 Kt alpha0 CD L p : ℝ) (m n : ℕ)
    (hD0 : 0 < D0) (hKt : 0 < Kt) (h_alpha0 : 15 < alpha0) (hCD_pos : 0 < CD)
    (hCD_ge : Kt * (D0 + 12) ≤ CD)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
      10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4),
    Real.sqrt ((n : ℝ) * (24 * (L + Kt) ^ 3 * Real.exp (-L / Kt)) ^ 2 / p)
      ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := by
  /- @proof-region region.target-node.session.7fd818d8ee62f64f begin -/
  intro D0 Kt alpha0 CD L p m n hD0 hKt h_alpha0 hCD_pos hCD_ge hm hn hnm hp0 hp1 hsparse hL
  obtain ⟨T, hT⟩ : ∃ x : ℝ, x = 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ x : ℝ, x = (m : ℝ) * (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = CD * Real.log t := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ x : ℝ, x = T / Kt := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ x : ℝ, x = 24 * (L + Kt) ^ 3 * Real.exp (-L / Kt) := ⟨_, rfl⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hTpos : 0 < T := by rw [hT]; positivity
  have ht2 : 2 ≤ t := by
    rw [ht]
    have h1 : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ (m : ℝ) := by linarith
    have h3 : (2 : ℝ) * 1 ≤ (m : ℝ) * (n : ℝ) := mul_le_mul hmR hnR (by norm_num) h2
    linarith
  have ht1 : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogm_ge : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
  have hlogm_pos : 0 < Real.log (m : ℝ) := by linarith
  have hlogt_eq : Real.log t = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    rw [ht, Real.log_mul (ne_of_gt hmpos) (ne_of_gt hnpos)]
  have hlogt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
  have hLT : L = A + T := by
    rw [hA, hT, ht]
    exact hL
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (le_of_lt hCD_pos) (le_of_lt hlogt_pos)
  have hLpos : 0 < L := by rw [hLT]; linarith
  have hspos : 0 < s := by rw [hs]; positivity
  have hKt4le : Kt ^ 4 ≤ (Kt + 1) ^ 4 := by
    have h3 : (0 : ℝ) < Kt ^ 3 := pow_pos hKt 3
    have h2 : (0 : ℝ) ≤ Kt ^ 2 := sq_nonneg Kt
    nlinarith only [h3, h2, hKt]
  have h4Kt : 4 * Kt ≤ (Kt + 1) ^ 4 := by
    have h4 : (0 : ℝ) < Kt ^ 4 := pow_pos hKt 4
    have h3 : (0 : ℝ) < Kt ^ 3 := pow_pos hKt 3
    have h2 : (0 : ℝ) ≤ Kt ^ 2 := sq_nonneg Kt
    nlinarith only [h4, h3, h2]
  have h16 : (65536 : ℝ) ≤ (alpha0 + 1) ^ 4 := by
    have hu : (0 : ℝ) ≤ alpha0 - 15 := by linarith only [h_alpha0]
    have h2 : (0 : ℝ) ≤ (alpha0 - 15) ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ (alpha0 - 15) ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ (alpha0 - 15) ^ 4 := by positivity
    nlinarith only [hu, h2, h3, h4]
  have hD0one : (1 : ℝ) ≤ (D0 + 1) ^ 4 := by
    have h2 : (0 : ℝ) ≤ D0 ^ 2 := sq_nonneg D0
    have h3 : (0 : ℝ) < D0 ^ 3 := pow_pos hD0 3
    have h4 : (0 : ℝ) < D0 ^ 4 := pow_pos hD0 4
    nlinarith only [hD0, h2, h3, h4]
  have hT_lower_a : 4000000 * (alpha0 + 1) ^ 4 * Kt ≤ T := by
    rw [hT]
    have hA : (0 : ℝ) ≤ (alpha0 + 1) ^ 4 := by positivity
    have hP : (Kt + 1) ^ 4 * 1 ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left hD0one (by positivity)
    have hstep : 4 * Kt * (alpha0 + 1) ^ 4 ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      have h1 : 4 * Kt ≤ (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by nlinarith only [h4Kt, hP]
      exact mul_le_mul_of_nonneg_right h1 hA
    nlinarith only [hstep]
  have hT_lower_b : 65536000000 * Kt ^ 4 * (D0 + 1) ^ 4 ≤ T := by
    rw [hT]
    have hD : (0 : ℝ) ≤ (D0 + 1) ^ 4 := by positivity
    have hstep : Kt ^ 4 * 65536 * (D0 + 1) ^ 4 ≤ (Kt + 1) ^ 4 * (alpha0 + 1) ^ 4 * (D0 + 1) ^ 4 := by
      have h0 : Kt ^ 4 * 65536 ≤ (Kt + 1) ^ 4 * (alpha0 + 1) ^ 4 :=
        mul_le_mul hKt4le h16 (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_right h0 hD
    nlinarith only [hstep]
  have hs_ge_a : 4000000 * (alpha0 + 1) ^ 4 ≤ s := by
    rw [hs, le_div_iff₀ hKt]
    linarith only [hT_lower_a]
  have hs_lo : (262144000000 : ℝ) ≤ s := by
    nlinarith only [hs_ge_a, h16]
  have hs_ge_b : 65536000000 * Kt ^ 3 * (D0 + 1) ^ 4 ≤ s := by
    rw [hs, le_div_iff₀ hKt]
    have heq : 65536000000 * Kt ^ 3 * (D0 + 1) ^ 4 * Kt = 65536000000 * Kt ^ 4 * (D0 + 1) ^ 4 := by
      ring
    rw [heq]
    exact hT_lower_b
  have hKt3_le_s : Kt ^ 3 ≤ s := by
    have h1 : Kt ^ 3 ≤ 65536000000 * Kt ^ 3 * (D0 + 1) ^ 4 := by
      have h2 : (1 : ℝ) ≤ 65536000000 * (D0 + 1) ^ 4 := by nlinarith only [hD0one]
      have h3 : (0 : ℝ) ≤ Kt ^ 3 := by positivity
      nlinarith only [h2, h3]
    linarith only [h1, hs_ge_b]
  have halpha_le_s : alpha0 ≤ s := by
    have h1 : alpha0 ≤ 4000000 * (alpha0 + 1) ^ 4 := by
      have h0 : (0 : ℝ) ≤ alpha0 := by linarith only [h_alpha0]
      have h2 : (0 : ℝ) ≤ alpha0 ^ 2 := sq_nonneg alpha0
      have h3 : (0 : ℝ) ≤ alpha0 ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ alpha0 ^ 4 := by positivity
      nlinarith only [h0, h2, h3, h4]
    linarith only [h1, hs_ge_a]
  have hDcube_le_s : 248832 * Kt ^ 3 * (D0 + 12) ^ 3 ≤ s := by
    have hDc : 248832 * (D0 + 12) ^ 3 ≤ 65536000000 * (D0 + 1) ^ 4 := by
      have h1 : (0 : ℝ) ≤ D0 := le_of_lt hD0
      have h2 : (0 : ℝ) ≤ D0 ^ 2 := sq_nonneg D0
      have h3 : (0 : ℝ) ≤ D0 ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ D0 ^ 4 := by positivity
      nlinarith only [h1, h2, h3, h4]
    have hK : (0 : ℝ) ≤ Kt ^ 3 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hDc hK
    nlinarith only [hstep, hs_ge_b]
  have hexp_le_one : ∀ y : ℝ, y ≤ 0 → Real.exp y ≤ 1 := by
    intro y hy
    have h1 : (1 : ℝ) ≤ Real.exp (-y) := by
      have h0 := Real.add_one_le_exp (-y)
      linarith only [h0, hy]
    have h2 : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
    have h4 : (0 : ℝ) < Real.exp y := Real.exp_pos _
    nlinarith only [h1, h2, h3, h4]
  have hexp_mono : ∀ a b : ℝ, a ≤ b → Real.exp a ≤ Real.exp b := by
    intro a b hab
    have h1 : Real.exp (a - b) ≤ 1 := hexp_le_one (a - b) (by linarith only [hab])
    have h2 : Real.exp a = Real.exp (a - b) * Real.exp b := by
      rw [← Real.exp_add]
      ring_nf
    have h3 : (0 : ℝ) < Real.exp b := Real.exp_pos _
    nlinarith only [h1, h2, h3]
  have hcubexp : ∀ x : ℝ, 0 ≤ x → x ^ 3 * Real.exp (-x) ≤ 48 := by
    intro x hx
    have h1 : (x / 2) ^ 3 / 6 ≤ Real.exp (x / 2) := by
      have h := Real.pow_div_factorial_le_exp (x / 2) (by linarith only [hx]) 3
      norm_num at h
      exact h
    have h2 : (x / 2) ^ 3 ≤ 6 * Real.exp (x / 2) := by
      have h4 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 by norm_num)
      have h5 : 6 * ((x / 2) ^ 3 / 6) = (x / 2) ^ 3 := by field_simp
      linarith only [h4, h5]
    have h3 : x ^ 3 ≤ 48 * Real.exp (x / 2) := by
      have h7 : x ^ 3 = 8 * (x / 2) ^ 3 := by ring_nf
      nlinarith only [h2, h7]
    have h8 : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      ring_nf
    have h9 : Real.exp (-(x / 2)) ≤ 1 := hexp_le_one _ (by linarith only [hx])
    have h10 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    nlinarith only [h3, h8, h9, h10]
  have hexp_ge : s ≤ Real.exp (s / 2) := by
    have h1 : s / 4 ≤ Real.exp (s / 4) := by
      have h0 := Real.add_one_le_exp (s / 4)
      linarith only [h0]
    have hp4 : (0 : ℝ) < Real.exp (s / 4) := Real.exp_pos _
    have hs4 : (0 : ℝ) ≤ s / 4 := by linarith only [hs_lo]
    have hsq : s / 4 * (s / 4) ≤ Real.exp (s / 4) * Real.exp (s / 4) :=
      mul_le_mul h1 h1 hs4 (le_of_lt hp4)
    have hE2 : Real.exp (s / 4) * Real.exp (s / 4) = Real.exp (s / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h4 : (4 : ℝ) * (s / 4) ≤ s / 4 * (s / 4) :=
      mul_le_mul (by linarith only [hs_lo] : (4 : ℝ) ≤ s / 4) le_rfl hs4 hs4
    have h4s : (4 : ℝ) * (s / 4) = s := by ring
    linarith only [hsq, hE2, h4, h4s]
  have he1 : s * Real.exp (-(s / 2)) ≤ 1 := by
    have hpos : (0 : ℝ) < Real.exp (-(s / 2)) := Real.exp_pos _
    have hprod : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hm := mul_le_mul_of_nonneg_right hexp_ge (le_of_lt hpos)
    linarith only [hm, hprod]
  have hid2 : ∀ u : ℝ, (2 * u) ^ 3 = 8 * u ^ 3 := fun u => by ring
  have h2s : 2 * (s / 2) = s := by ring
  set_option maxHeartbeats 2000000 in
  have hs3e : s ^ 3 * Real.exp (-(s / 2)) ≤ 384 := by
    have h0 := hcubexp (s / 2) (by linarith only [hs_lo])
    have h1 : 8 * ((s / 2) ^ 3 * Real.exp (-(s / 2))) ≤ 8 * 48 :=
      mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ 8)
    have h2 : s ^ 3 = 8 * (s / 2) ^ 3 := by
      calc s ^ 3 = (2 * (s / 2)) ^ 3 := by rw [h2s]
        _ = 8 * (s / 2) ^ 3 := hid2 (s / 2)
    calc s ^ 3 * Real.exp (-(s / 2)) = 8 * ((s / 2) ^ 3 * Real.exp (-(s / 2))) := by
          rw [h2, mul_assoc]
      _ ≤ 8 * 48 := h1
      _ = 384 := by norm_num
  have hKt3_strong : 65536000000 * Kt ^ 3 ≤ s := by
    have h3 : (0 : ℝ) ≤ 65536000000 * Kt ^ 3 := by positivity
    have h4 := mul_le_mul_of_nonneg_left hD0one h3
    linarith only [h4, hs_ge_b]
  obtain ⟨Cc, hCc⟩ : ∃ x : ℝ, x = Real.exp (-(alpha0 / 2 * Real.log (Real.log 2))) := ⟨_, rfl⟩
  have hCcpos : 0 < Cc := by rw [hCc]; exact Real.exp_pos _
  have hCcnonneg : 0 ≤ Cc := le_of_lt hCcpos
  have hexpneg1 : Real.exp (-1) ≤ 1 / 2 := by
    have h0 := Real.add_one_le_exp 1
    have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hp1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hp2 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    nlinarith only [h0, hprod, hp1, hp2]
  have hlog2ge : Real.exp (-1) ≤ Real.log 2 := by linarith only [hexpneg1, hlog2half]
  have hloglog2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    have h := Real.log_le_log (Real.exp_pos (-1)) hlog2ge
    rwa [Real.log_exp] at h
  have h2alpha : 2 * alpha0 ≤ s := by
    have h1 : 2 * alpha0 ≤ 4000000 * (alpha0 + 1) ^ 4 := by
      have h0 : (0 : ℝ) ≤ alpha0 := by linarith only [h_alpha0]
      have h2 : (0 : ℝ) ≤ alpha0 ^ 2 := sq_nonneg alpha0
      have h3 : (0 : ℝ) ≤ alpha0 ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ alpha0 ^ 4 := by positivity
      nlinarith only [h0, h2, h3, h4]
    linarith only [h1, hs_ge_a]
  have hCcle : Cc ≤ Real.exp (s / 4) := by
    rw [hCc]
    apply hexp_mono
    have ha : (0 : ℝ) ≤ alpha0 / 2 := by linarith only [h_alpha0]
    nlinarith only [hloglog2, ha, h2alpha]
  have hloglogm : Real.log (Real.log 2) ≤ Real.log (Real.log (m : ℝ)) :=
    Real.log_le_log hlog2_pos hlogm_ge
  have hrpow_a : (Real.log (m : ℝ)).rpow alpha0 = Real.exp (Real.log (Real.log (m : ℝ)) * alpha0) := by
    simpa using Real.rpow_def_of_pos hlogm_pos alpha0
  have hrpow_na : (Real.log (m : ℝ)).rpow (-alpha0) = Real.exp (Real.log (Real.log (m : ℝ)) * -alpha0) := by
    simpa using Real.rpow_def_of_pos hlogm_pos (-alpha0)
  have hApos : (0 : ℝ) < (Real.log (m : ℝ)).rpow alpha0 := by
    rw [hrpow_a]
    exact Real.exp_pos _
  have hprod1 : (Real.log (m : ℝ)).rpow (-alpha0) * (Real.log (m : ℝ)).rpow alpha0 = 1 := by
    rw [hrpow_na, hrpow_a, ← Real.exp_add]
    have hz : Real.log (Real.log (m : ℝ)) * -alpha0 + Real.log (Real.log (m : ℝ)) * alpha0 = 0 := by
      ring
    rw [hz, Real.exp_zero]
  have hCc2 : (Real.log (m : ℝ)).rpow (-alpha0) ≤ Cc * Cc := by
    have e2 : Cc * Cc =
        Real.exp (-(alpha0 / 2 * Real.log (Real.log 2)) + -(alpha0 / 2 * Real.log (Real.log 2))) := by
      rw [hCc, ← Real.exp_add]
    rw [hrpow_na, e2]
    apply hexp_mono
    nlinarith only [hloglogm, h_alpha0]
  have hCc2nonneg : (0 : ℝ) ≤ Cc * Cc := mul_nonneg hCcnonneg hCcnonneg
  have hstep1 : 1 ≤ (Real.log (m : ℝ)).rpow alpha0 * (Cc * Cc) := by
    have h := mul_le_mul_of_nonneg_right hCc2 (le_of_lt hApos)
    rw [hprod1] at h
    linarith only [h]
  have hstep2 : (Real.log (m : ℝ)).rpow alpha0 * (Cc * Cc) ≤ (m : ℝ) * p * (Cc * Cc) := by
    have h := mul_le_mul_of_nonneg_right hsparse hCc2nonneg
    linarith only [h]
  have hstep3 : (m : ℝ) ≤ ((m : ℝ) * Cc) ^ 2 * p := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hmpos
    have h := mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) hm0
    nlinarith only [h]
  have hnp : (n : ℝ) / p ≤ ((m : ℝ) * Cc) ^ 2 := by
    rw [div_le_iff₀ hp0]
    exact le_trans hnmR hstep3
  have hsqrtp : Real.sqrt ((n : ℝ) / p) ≤ (m : ℝ) * Cc := by
    rw [Real.sqrt_le_iff]
    exact ⟨mul_nonneg (le_of_lt hmpos) hCcnonneg, hnp⟩
  have hAid : A / Kt = CD / Kt * Real.log t := by
    rw [hA]
    have hf : ∀ x y z : ℝ, z ≠ 0 → x * y / z = x / z * y := by
      intro x y z hz
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    exact hf CD (Real.log t) Kt (ne_of_gt hKt)
  have hmul_A : ∀ x : ℝ, x * (A / Kt) = (x * (CD / Kt)) * Real.log t := by
    intro x
    rw [hAid]
    ring
  have hdec_gen : ∀ c : ℝ, D0 + 5 ≤ c →
      Real.exp (-(c * Real.log t)) * (m : ℝ) * (n : ℝ) ^ (D0 + 5) ≤ 1 := by
    intro c hc
    have hmexp : Real.exp (Real.log (m : ℝ)) = (m : ℝ) := Real.exp_log hmpos
    have hnexp : (n : ℝ) ^ (D0 + 5) = Real.exp (Real.log (n : ℝ) * (D0 + 5)) :=
      Real.rpow_def_of_pos hnpos (D0 + 5)
    have hlognn : (0 : ℝ) ≤ Real.log (n : ℝ) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hnR
      rwa [Real.log_one] at h
    have hlogmn : (0 : ℝ) ≤ Real.log (m : ℝ) := le_of_lt hlogm_pos
    have hnpos' : (0 : ℝ) ≤ (n : ℝ) ^ (D0 + 5) := by
      rw [hnexp]
      exact le_of_lt (Real.exp_pos _)
    have hm_le : (m : ℝ) ≤ Real.exp (Real.log (m : ℝ)) := le_of_eq hmexp.symm
    have hn_le : (n : ℝ) ^ (D0 + 5) ≤ Real.exp (Real.log (n : ℝ) * (D0 + 5)) := le_of_eq hnexp
    have hinner : (m : ℝ) * (n : ℝ) ^ (D0 + 5) ≤
        Real.exp (Real.log (m : ℝ)) * Real.exp (Real.log (n : ℝ) * (D0 + 5)) :=
      mul_le_mul hm_le hn_le hnpos' (le_of_lt (Real.exp_pos _))
    have hstep1 : Real.exp (-(c * Real.log t)) * (m : ℝ) * (n : ℝ) ^ (D0 + 5) ≤
        Real.exp (-(c * Real.log t)) * Real.exp (Real.log (m : ℝ)) *
          Real.exp (Real.log (n : ℝ) * (D0 + 5)) := by
      have h := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.exp_pos (-(c * Real.log t))))
      linarith only [h]
    have hstep2 : Real.exp (-(c * Real.log t)) * Real.exp (Real.log (m : ℝ)) *
          Real.exp (Real.log (n : ℝ) * (D0 + 5)) =
        Real.exp (-(c * Real.log t) + Real.log (m : ℝ) + Real.log (n : ℝ) * (D0 + 5)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    have hstep3 : Real.exp (-(c * Real.log t) + Real.log (m : ℝ) + Real.log (n : ℝ) * (D0 + 5)) ≤ 1 := by
      apply hexp_le_one
      rw [hlogt_eq]
      nlinarith only [hc, hlogmn, hlognn, hD0]
    linarith only [hstep1, hstep2, hstep3]
  obtain ⟨θ, hθpos, hθ⟩ : ∃ x : ℝ, 0 < x ∧ x * (D0 + 12) = 7 := by
    refine ⟨7 / (D0 + 12), by positivity, ?_⟩
    have hne : (D0 + 12) ≠ 0 := by positivity
    field_simp
  have hD12pos : (0 : ℝ) < D0 + 12 := by linarith only [hD0]
  have h1θ : (1 - θ) * (D0 + 12) = D0 + 5 := by nlinarith only [hθ]
  have h1θ_nonneg : (0 : ℝ) ≤ 1 - θ := by nlinarith only [h1θ, hD0]
  have h343 : θ ^ 3 * (D0 + 12) ^ 3 = 343 := by
    rw [← mul_pow, hθ]
    norm_num
  have hcdK : D0 + 12 ≤ CD / Kt := by
    rw [le_div_iff₀ hKt]
    linarith only [hCD_ge]
  have hc1 : D0 + 5 ≤ (1 - θ) * (CD / Kt) := by
    have h := mul_le_mul_of_nonneg_left hcdK h1θ_nonneg
    rw [h1θ] at h
    linarith only [h]
  have h4alpha : 4 * alpha0 ≤ s := by
    have h1 : 4 * alpha0 ≤ 4000000 * (alpha0 + 1) ^ 4 := by
      have h0 : (0 : ℝ) ≤ alpha0 := by linarith only [h_alpha0]
      have h2 : (0 : ℝ) ≤ alpha0 ^ 2 := sq_nonneg alpha0
      have h3 : (0 : ℝ) ≤ alpha0 ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ alpha0 ^ 4 := by positivity
      nlinarith only [h0, h2, h3, h4]
    linarith only [h1, hs_ge_a]
  have hCcle8 : Cc ≤ Real.exp (s / 8) := by
    rw [hCc]
    apply hexp_mono
    have ha : (0 : ℝ) ≤ alpha0 / 2 := by linarith only [h_alpha0]
    nlinarith only [hloglog2, ha, h4alpha]
  have hAsplit : Real.exp (-(A / Kt)) =
      Real.exp (-(θ * (A / Kt))) * Real.exp (-((1 - θ) * (A / Kt))) := by
    have harg : -(A / Kt) = -(θ * (A / Kt)) + -((1 - θ) * (A / Kt)) := by ring
    rw [harg, Real.exp_add]
  have hLarg : -L / Kt = -(A / Kt) + -s := by
    rw [hLT, hs, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hexpL : Real.exp (-L / Kt) = Real.exp (-(A / Kt)) * Real.exp (-s) := by
    rw [hLarg, Real.exp_add]
  have hLplus : L + Kt = Kt * (A / Kt + s + 1) := by
    rw [hLT, hs]
    have hK : Kt ≠ 0 := ne_of_gt hKt
    field_simp
  have hpair : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
    intro x y hx hy
    have hxy : (0 : ℝ) ≤ x + y := by linarith only [hx, hy]
    have hsq : (0 : ℝ) ≤ (x - y) ^ 2 := sq_nonneg _
    have hprod : (0 : ℝ) ≤ (x - y) ^ 2 * (x + y) := mul_nonneg hsq hxy
    nlinarith only [hprod]
  have hcube3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      (a + b + c) ^ 3 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) := by
    intro a b c ha hb hc
    have h1 : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := hpair a b ha hb
    have h2 : (a + b + c) ^ 3 ≤ 4 * ((a + b) ^ 3 + c ^ 3) :=
      hpair (a + b) c (by linarith only [ha, hb]) hc
    have h3 : (0 : ℝ) ≤ a ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ b ^ 3 := by positivity
    have h5 : (0 : ℝ) ≤ c ^ 3 := by positivity
    nlinarith only [h1, h2, h3, h4, h5]
  have hdet : (0 : ℝ) ≤ A / Kt := by
    rw [hAid]
    exact mul_nonneg (div_nonneg (le_of_lt hCD_pos) (le_of_lt hKt)) (le_of_lt hlogt_pos)
  have ha3 : (A / Kt) ^ 3 * Real.exp (-(θ * (A / Kt))) ≤ 48 * (D0 + 12) ^ 3 := by
    have hx0 : (0 : ℝ) ≤ θ * (A / Kt) := mul_nonneg (le_of_lt hθpos) hdet
    have h0 := hcubexp (θ * (A / Kt)) hx0
    have hid3 : (θ * (A / Kt)) ^ 3 = (A / Kt) ^ 3 * θ ^ 3 := by ring
    rw [hid3] at h0
    have hE0 : (0 : ℝ) ≤ (A / Kt) ^ 3 * Real.exp (-(θ * (A / Kt))) :=
      mul_nonneg (by positivity) (le_of_lt (Real.exp_pos _))
    have hstep := mul_le_mul_of_nonneg_right h0 (show (0 : ℝ) ≤ (D0 + 12) ^ 3 by positivity)
    nlinarith only [hstep, h343, hE0]
  have hdecA : Real.exp (-(A / Kt)) * (m : ℝ) * (n : ℝ) ^ (D0 + 5) ≤ 1 := by
    have h := hdec_gen (CD / Kt) (by linarith only [hcdK])
    rw [hAid]
    exact h
  have hdec1 : Real.exp (-((1 - θ) * (A / Kt))) * (m : ℝ) * (n : ℝ) ^ (D0 + 5) ≤ 1 := by
    have harg1 : (1 - θ) * (A / Kt) = ((1 - θ) * (CD / Kt)) * Real.log t := hmul_A (1 - θ)
    rw [harg1]
    exact hdec_gen ((1 - θ) * (CD / Kt)) hc1
  have hn_eq : (n : ℝ) ^ (D0 + 5) = Real.exp (Real.log (n : ℝ) * (D0 + 5)) :=
    Real.rpow_def_of_pos hnpos (D0 + 5)
  have hcomb1 : Real.exp (-((1 - θ) * (A / Kt))) * (m : ℝ) *
      Real.exp (Real.log (n : ℝ) * (D0 + 5)) ≤ 1 := by
    rw [← hn_eq]
    exact hdec1
  have hcomb0 : Real.exp (-(A / Kt)) * (m : ℝ) *
      Real.exp (Real.log (n : ℝ) * (D0 + 5)) ≤ 1 := by
    rw [← hn_eq]
    exact hdecA
  have hE_nonneg : (0 : ℝ) ≤ E := by
    rw [hE]
    have h1 : (0 : ℝ) < L + Kt := by linarith only [hLpos, hKt]
    have h2 : (0 : ℝ) ≤ (L + Kt) ^ 3 := by positivity
    have h3 : (0 : ℝ) < Real.exp (-L / Kt) := Real.exp_pos _
    have h4 : (0 : ℝ) ≤ 24 := by norm_num
    exact mul_nonneg (mul_nonneg h4 h2) (le_of_lt h3)
  have hEeq : E = 24 * Kt ^ 3 * (A / Kt + s + 1) ^ 3 * Real.exp (-(θ * (A / Kt))) *
      Real.exp (-((1 - θ) * (A / Kt))) * Real.exp (-s) := by
    rw [hE, hexpL, hAsplit, hLplus, mul_pow]
    ring
  have hdecay : Real.exp (-(7 * s / 8)) ≤ Real.exp (-(s / 2)) :=
    hexp_mono _ _ (by nlinarith only [hs_lo])
  have hE1le : Real.exp (-(θ * (A / Kt))) ≤ 1 :=
    hexp_le_one _ (by nlinarith only [hθpos, hdet])
  have h7s0 : (0 : ℝ) ≤ Real.exp (-(7 * s / 8)) := le_of_lt (Real.exp_pos _)
  have hR : Cc * Real.exp (-s) ≤ Real.exp (-(7 * s / 8)) := by
    have h := mul_le_mul hCcle8 (le_refl (Real.exp (-s))) (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos (s / 8)))
    have h2 : Real.exp (s / 8) * Real.exp (-s) = Real.exp (-(7 * s / 8)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [h2] at h
  have hRc0 : (0 : ℝ) ≤ Cc * Real.exp (-s) := mul_nonneg hCcnonneg (le_of_lt (Real.exp_pos _))
  have hQRc : (Real.exp (-((1 - θ) * (A / Kt))) * (m : ℝ) * Real.exp (Real.log (n : ℝ) * (D0 + 5))) *
      (Cc * Real.exp (-s)) ≤ Real.exp (-(7 * s / 8)) := by
    have h := mul_le_mul hcomb1 hR hRc0 (by norm_num : (0 : ℝ) ≤ 1)
    linarith only [h]
  set_option maxHeartbeats 4000000 in
  have hstepA : E * (m : ℝ) * Cc * Real.exp (Real.log (n : ℝ) * (D0 + 5)) ≤
      648 * Kt ^ 3 * ((A / Kt) ^ 3 + s ^ 3 + 1) * Real.exp (-(θ * (A / Kt))) *
        (Real.exp (-((1 - θ) * (A / Kt))) * (m : ℝ) * Real.exp (Real.log (n : ℝ) * (D0 + 5))) *
        (Cc * Real.exp (-s)) := by
    rw [hEeq]
    have hcube_step : (A / Kt + s + 1) ^ 3 ≤ 27 * ((A / Kt) ^ 3 + s ^ 3 + 1) := by
      simpa using hcube3 (A / Kt) s 1 hdet (le_of_lt hspos) (by norm_num)
    have hnn : (0 : ℝ) ≤ 24 * Kt ^ 3 * Real.exp (-(θ * (A / Kt))) *
        Real.exp (-((1 - θ) * (A / Kt))) * Real.exp (-s) * (m : ℝ) * Cc *
        Real.exp (Real.log (n : ℝ) * (D0 + 5)) := by positivity
    have hm := mul_le_mul_of_nonneg_left hcube_step hnn
    linarith only [hm]
  have hA1 : 648 * Kt ^ 3 * ((A / Kt) ^ 3 + s ^ 3 + 1) * Real.exp (-(θ * (A / Kt))) *
        (Real.exp (-((1 - θ) * (A / Kt))) * (m : ℝ) * Real.exp (Real.log (n : ℝ) * (D0 + 5))) *
        (Cc * Real.exp (-s)) ≤
      648 * Kt ^ 3 * ((A / Kt) ^ 3 + s ^ 3 + 1) * Real.exp (-(θ * (A / Kt))) *
        Real.exp (-(7 * s / 8)) := by
    have hM : (0 : ℝ) ≤ 648 * Kt ^ 3 * ((A / Kt) ^ 3 + s ^ 3 + 1) * Real.exp (-(θ * (A / Kt))) := by
      have h1 : (0 : ℝ) ≤ (A / Kt) ^ 3 := pow_nonneg hdet 3
      have h2 : (0 : ℝ) ≤ s ^ 3 := pow_nonneg (le_of_lt hspos) 3
      have h3 : (0 : ℝ) ≤ Kt ^ 3 := pow_nonneg (le_of_lt hKt) 3
      have h5 : (0 : ℝ) ≤ (A / Kt) ^ 3 + s ^ 3 + 1 := by linarith only [h1, h2]
      have h6 : (0 : ℝ) ≤ 648 * Kt ^ 3 * ((A / Kt) ^ 3 + s ^ 3 + 1) := by nlinarith only [h3, h5]
      exact mul_nonneg h6 (le_of_lt (Real.exp_pos _))
    have h := mul_le_mul_of_nonneg_left hQRc hM
    linarith only [h]
  have hsum : ((A / Kt) ^ 3 + s ^ 3 + 1) * Real.exp (-(θ * (A / Kt))) ≤
      48 * (D0 + 12) ^ 3 + s ^ 3 + 1 := by
    have h2 : s ^ 3 * Real.exp (-(θ * (A / Kt))) ≤ s ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hE1le (pow_nonneg (le_of_lt hspos) 3)
      linarith only [h]
    linarith only [ha3, h2, hE1le]
  have hA2 : 648 * Kt ^ 3 * ((A / Kt) ^ 3 + s ^ 3 + 1) * Real.exp (-(θ * (A / Kt))) *
        Real.exp (-(7 * s / 8)) ≤
      648 * Kt ^ 3 * (48 * (D0 + 12) ^ 3 + s ^ 3 + 1) * Real.exp (-(7 * s / 8)) := by
    have hM2 : (0 : ℝ) ≤ 648 * Kt ^ 3 * Real.exp (-(7 * s / 8)) := by positivity
    have h := mul_le_mul_of_nonneg_right hsum hM2
    linarith only [h]
  have hcub4 : ∀ x : ℝ, 0 ≤ x → x ^ 4 * Real.exp (-x) ≤ 24 := by
    intro x hx
    have h := Real.pow_div_factorial_le_exp x hx 4
    norm_num at h
    have hpos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    have hprod : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    rw [hprod] at h2
    linarith only [h2]
  have hquart : s ^ 4 * Real.exp (-(7 * s / 8)) ≤ 128 := by
    have h0 := hcub4 (7 * s / 8) (by linarith only [hs_lo])
    have hpow : s ^ 4 = (8 / 7) ^ 4 * (7 * s / 8) ^ 4 := by ring
    have hkey : (8 / 7) ^ 4 * ((7 * s / 8) ^ 4 * Real.exp (-(7 * s / 8))) ≤ (8 / 7) ^ 4 * 24 :=
      mul_le_mul_of_nonneg_left h0 (by norm_num)
    have hbase : ((8 : ℝ) / 7) ^ 4 * 24 ≤ 128 := by norm_num
    calc s ^ 4 * Real.exp (-(7 * s / 8))
        = ((8 : ℝ) / 7) ^ 4 * ((7 * s / 8) ^ 4 * Real.exp (-(7 * s / 8))) := by
          rw [hpow]
          ring
      _ ≤ ((8 : ℝ) / 7) ^ 4 * 24 := hkey
      _ ≤ 128 := hbase
  have hD8 : 8 * (31104 * Kt ^ 3 * (D0 + 12) ^ 3) ≤ s := by linarith only [hDcube_le_s]
  have hT1 : 648 * Kt ^ 3 * 48 * (D0 + 12) ^ 3 * Real.exp (-(7 * s / 8)) ≤ 1 / 8 := by
    have h1 : 8 * (31104 * Kt ^ 3 * (D0 + 12) ^ 3) * Real.exp (-(7 * s / 8)) ≤
        s * Real.exp (-(7 * s / 8)) := mul_le_mul_of_nonneg_right hD8 h7s0
    have h2 : s * Real.exp (-(7 * s / 8)) ≤ s * Real.exp (-(s / 2)) :=
      mul_le_mul_of_nonneg_left hdecay (le_of_lt hspos)
    linarith only [h1, h2, he1]
  have hT2 : 648 * Kt ^ 3 * s ^ 3 * Real.exp (-(7 * s / 8)) ≤ 1 / 8 := by
    have hq2 : 648 * (s ^ 4 * Real.exp (-(7 * s / 8))) ≤ 648 * 128 :=
      mul_le_mul_of_nonneg_left hquart (by norm_num)
    have hmul : 65536000000 * (648 * Kt ^ 3 * s ^ 3 * Real.exp (-(7 * s / 8))) ≤
        648 * (s ^ 4 * Real.exp (-(7 * s / 8))) := by
      have h := mul_le_mul_of_nonneg_right hKt3_strong
        (show (0 : ℝ) ≤ 648 * s ^ 3 * Real.exp (-(7 * s / 8)) by positivity)
      linarith only [h]
    linarith only [hmul, hq2]
  have hT3 : 648 * Kt ^ 3 * Real.exp (-(7 * s / 8)) ≤ 1 / 8 := by
    have hmul : 65536000000 * (648 * Kt ^ 3 * Real.exp (-(7 * s / 8))) ≤
        648 * (s * Real.exp (-(7 * s / 8))) := by
      have h := mul_le_mul_of_nonneg_right hKt3_strong
        (show (0 : ℝ) ≤ 648 * Real.exp (-(7 * s / 8)) by positivity)
      linarith only [h]
    have h2 : s * Real.exp (-(7 * s / 8)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hdecay (le_of_lt hspos)) he1
    linarith only [hmul, h2]
  have hfin : 648 * Kt ^ 3 * (48 * (D0 + 12) ^ 3 + s ^ 3 + 1) * Real.exp (-(7 * s / 8)) ≤ 1 := by
    have hsplit : 648 * Kt ^ 3 * (48 * (D0 + 12) ^ 3 + s ^ 3 + 1) * Real.exp (-(7 * s / 8)) =
        648 * Kt ^ 3 * 48 * (D0 + 12) ^ 3 * Real.exp (-(7 * s / 8))
        + 648 * Kt ^ 3 * s ^ 3 * Real.exp (-(7 * s / 8))
        + 648 * Kt ^ 3 * Real.exp (-(7 * s / 8)) := by ring
    linarith only [hsplit, hT1, hT2, hT3]
  have hD : E * (m : ℝ) * Cc * Real.exp (Real.log (n : ℝ) * (D0 + 5)) ≤ 1 :=
    hstepA.trans (hA1.trans (hA2.trans hfin))
  have hYval : Real.rpow (n : ℝ) (-(D0 + 5)) = Real.exp (Real.log (n : ℝ) * (-(D0 + 5))) :=
    Real.rpow_def_of_pos hnpos _
  have hYpos : (0 : ℝ) < Real.rpow (n : ℝ) (-(D0 + 5)) := by
    rw [hYval]
    exact Real.exp_pos _
  have hcancel : Real.exp (Real.log (n : ℝ) * (D0 + 5)) *
      Real.exp (Real.log (n : ℝ) * (-(D0 + 5))) = 1 := by
    rw [← Real.exp_add]
    have hz : Real.log (n : ℝ) * (D0 + 5) + Real.log (n : ℝ) * (-(D0 + 5)) = 0 := by ring
    rw [hz, Real.exp_zero]
  have hEmc : E * ((m : ℝ) * Cc) ≤ Real.rpow (n : ℝ) (-(D0 + 5)) := by
    have h1 : E * ((m : ℝ) * Cc) * Real.exp (Real.log (n : ℝ) * (D0 + 5)) ≤ 1 := by
      linarith only [hD]
    have h2 : E * ((m : ℝ) * Cc) * Real.exp (Real.log (n : ℝ) * (D0 + 5)) *
          Real.exp (Real.log (n : ℝ) * (-(D0 + 5))) ≤
        1 * Real.exp (Real.log (n : ℝ) * (-(D0 + 5))) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
    have h3 : E * ((m : ℝ) * Cc) * Real.exp (Real.log (n : ℝ) * (D0 + 5)) *
          Real.exp (Real.log (n : ℝ) * (-(D0 + 5))) = E * ((m : ℝ) * Cc) := by
      rw [mul_assoc, hcancel, mul_one]
    rw [hYval]
    linarith only [h2, h3]
  obtain ⟨Y, hY⟩ : ∃ y : ℝ, y = Real.rpow (n : ℝ) (-(D0 + 5)) := ⟨_, rfl⟩
  have hYpos' : (0 : ℝ) < Y := by rw [hY]; exact hYpos
  have hEmc' : E * ((m : ℝ) * Cc) ≤ Y := by rw [hY]; exact hEmc
  set_option maxHeartbeats 4000000 in
  have hXle : (n : ℝ) * E ^ 2 / p ≤ Y ^ 2 := by
    have h1 : (n : ℝ) * E ^ 2 / p = E ^ 2 * ((n : ℝ) / p) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    have h2 : E ^ 2 * ((n : ℝ) / p) ≤ E ^ 2 * ((m : ℝ) * Cc) ^ 2 :=
      mul_le_mul_of_nonneg_left hnp (sq_nonneg E)
    have h3 : E ^ 2 * ((m : ℝ) * Cc) ^ 2 = (E * ((m : ℝ) * Cc)) ^ 2 := by ring
    have h4 : (E * ((m : ℝ) * Cc)) ^ 2 ≤ Y ^ 2 := by
      have h0 : (0 : ℝ) ≤ E * ((m : ℝ) * Cc) :=
        mul_nonneg hE_nonneg (mul_nonneg (le_of_lt hmpos) hCcnonneg)
      have hY0 : (0 : ℝ) ≤ Y := le_of_lt hYpos'
      have hmm : E * ((m : ℝ) * Cc) * (E * ((m : ℝ) * Cc)) ≤ Y * Y :=
        mul_le_mul hEmc' hEmc' h0 hY0
      calc (E * ((m : ℝ) * Cc)) ^ 2 = E * ((m : ℝ) * Cc) * (E * ((m : ℝ) * Cc)) :=
            pow_two (E * ((m : ℝ) * Cc))
        _ ≤ Y * Y := hmm
        _ = Y ^ 2 := (pow_two Y).symm
    calc (n : ℝ) * E ^ 2 / p = E ^ 2 * ((n : ℝ) / p) := h1
      _ ≤ E ^ 2 * ((m : ℝ) * Cc) ^ 2 := h2
      _ = (E * ((m : ℝ) * Cc)) ^ 2 := h3
      _ ≤ Y ^ 2 := h4
  rw [← hE, Real.sqrt_le_iff, ← hY]
  exact ⟨le_of_lt hYpos', hXle⟩
  /- @proof-region region.target-node.session.7fd818d8ee62f64f end -/

end Statlib.Imported

