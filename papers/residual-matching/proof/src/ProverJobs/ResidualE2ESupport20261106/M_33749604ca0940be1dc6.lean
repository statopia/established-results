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
theorem statopia_math_node_3865474750_001c1756 : ∀ (L Kt CD D0 alpha0 : ℝ) (m n : ℕ)
    (hKt : 0 < Kt) (hD0 : 0 < D0) (h_alpha0 : 15 < alpha0) (hCD : 0 < CD)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hL : L = CD * Real.log ((m : ℝ) * (n : ℝ)) +
        10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4),
    (((2 * L ^ 2 + 4 * Kt * (L + Kt)) * Real.exp (-L / Kt) ≤ 1 / 16)
      ∧ (2 * (L + Kt) * Real.exp (-L / Kt) ≤ 1 / 4)) := by
  /- @proof-region region.target-node.session.d36fd0b23c16f7dc begin -/
  intro L Kt CD D0 alpha0 m n hKt hD0 h_alpha0 hCD hm hn hL
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = L / Kt := ⟨_, rfl⟩
  have hKtne : Kt ≠ 0 := ne_of_gt hKt
  have hExp : Real.exp (-L / Kt) = Real.exp (-y) := by
    rw [hy]
    congr 1
    ring_nf
  have hLy : L = y * Kt := by
    rw [hy]
    field_simp
  have hKtpow : Kt ≤ (Kt + 1) ^ 4 := by
    nlinarith only [hKt, sq_nonneg Kt, sq_nonneg (Kt ^ 2)]
  have hKt3 : Kt ^ 3 ≤ (Kt + 1) ^ 4 := by
    nlinarith only [hKt, sq_nonneg Kt, sq_nonneg (Kt ^ 2)]
  have hD0f : (1 : ℝ) ≤ (D0 + 1) ^ 4 := by
    nlinarith only [hD0, sq_nonneg D0, sq_nonneg (D0 ^ 2)]
  have hAlf : (1 : ℝ) ≤ (alpha0 + 1) ^ 4 := by
    nlinarith only [h_alpha0, sq_nonneg alpha0, sq_nonneg (alpha0 ^ 2)]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
    apply Real.log_nonneg
    nlinarith only [hm1, hn1]
  have hCDlog : 0 ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := mul_nonneg (le_of_lt hCD) hlog
  have hTsub : 10 ^ 6 * (Kt + 1) ^ 4 ≤ L := by
    have hAnn : (0 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 := by linarith only [hKt, hKtpow]
    have hA1 : 10 ^ 6 * (Kt + 1) ^ 4 ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by
      have h := mul_le_mul_of_nonneg_left hD0f hAnn
      simpa using h
    have hA2 : 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 ≤
        10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 * (alpha0 + 1) ^ 4 := by
      have hnn : (0 : ℝ) ≤ 10 ^ 6 * (Kt + 1) ^ 4 * (D0 + 1) ^ 4 := by
        linarith only [hAnn, hA1]
      have h := mul_le_mul_of_nonneg_left hAlf hnn
      simpa using h
    rw [hL]
    linarith only [hCDlog, hA1, hA2]
  have hy_lb : 10 ^ 6 * (Kt + 1) ^ 4 / Kt ≤ y := by
    rw [div_le_iff₀ hKt]
    linarith only [hTsub, hLy]
  have hy_ge6 : 10 ^ 6 ≤ y := by
    have h1 : 10 ^ 6 ≤ 10 ^ 6 * (Kt + 1) ^ 4 / Kt := by
      rw [le_div_iff₀ hKt]
      linarith only [hKtpow]
    linarith only [h1, hy_lb]
  have hy_pos : 0 < y := by linarith only [hy_ge6]
  have hy_ge1 : 1 ≤ y := by linarith only [hy_ge6]
  have hT_Kt : 10 ^ 6 * Kt ^ 3 ≤ L := by
    have h1 : 10 ^ 6 * Kt ^ 3 ≤ 10 ^ 6 * (Kt + 1) ^ 4 := by linarith only [hKt3]
    linarith only [h1, hTsub]
  have hprod2 : 10 ^ 6 * Kt ^ 3 ≤ y * Kt := by linarith only [hT_Kt, hLy]
  have hKt2 : Kt ^ 2 ≤ y / 10 ^ 6 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)]
    by_contra hcon
    push_neg at hcon
    have h1 := mul_lt_mul_of_pos_right hcon hKt
    nlinarith only [hprod2, h1]
  have hstep : Real.exp (-(y / 4)) * (y + 4) ≤ 4 := by
    have h1 : y / 4 + 1 ≤ Real.exp (y / 4) := Real.add_one_le_exp (y / 4)
    have h2 : y + 4 ≤ 4 * Real.exp (y / 4) := by linarith only [h1]
    have h3 : Real.exp (-(y / 4)) * (y + 4) ≤
        Real.exp (-(y / 4)) * (4 * Real.exp (y / 4)) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-(y / 4))))
    have h5 : Real.exp (-(y / 4)) * Real.exp (y / 4) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h4 : Real.exp (-(y / 4)) * (4 * Real.exp (y / 4)) = 4 := by
      rw [show Real.exp (-(y / 4)) * (4 * Real.exp (y / 4)) =
        4 * (Real.exp (-(y / 4)) * Real.exp (y / 4)) by ring, h5]
      norm_num
    linarith only [h3, h4]
  have hnn4 : (0 : ℝ) ≤ Real.exp (-(y / 4)) * (y + 4) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (by linarith only [hy_pos])
  have hsq4 : (Real.exp (-(y / 4)) * (y + 4)) * (Real.exp (-(y / 4)) * (y + 4)) ≤ 16 := by
    have h := mul_le_mul hstep hstep hnn4 (by norm_num : (0 : ℝ) ≤ 4)
    linarith only [h]
  have hpow4 : (Real.exp (-(y / 4)) * (y + 4)) ^ 4 ≤ 256 := by
    calc (Real.exp (-(y / 4)) * (y + 4)) ^ 4 =
        ((Real.exp (-(y / 4)) * (y + 4)) * (Real.exp (-(y / 4)) * (y + 4))) *
        ((Real.exp (-(y / 4)) * (y + 4)) * (Real.exp (-(y / 4)) * (y + 4))) := by ring
      _ ≤ 16 * 16 := mul_le_mul hsq4 hsq4
          (mul_nonneg hnn4 hnn4) (by norm_num)
      _ = 256 := by norm_num
  have hpow : Real.exp (-y) = (Real.exp (-(y / 4))) ^ 4 := by
    have key : Real.exp (-(y / 4)) * Real.exp (-(y / 4)) * Real.exp (-(y / 4)) *
        Real.exp (-(y / 4)) = Real.exp (-y) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← key]
    ring
  have hE : Real.exp (-y) * (y + 4) ^ 4 ≤ 256 := by
    have hmul : (Real.exp (-(y / 4))) ^ 4 * (y + 4) ^ 4 =
        (Real.exp (-(y / 4)) * (y + 4)) ^ 4 := by ring
    calc Real.exp (-y) * (y + 4) ^ 4 = (Real.exp (-(y / 4))) ^ 4 * (y + 4) ^ 4 := by
          rw [hpow]
      _ = (Real.exp (-(y / 4)) * (y + 4)) ^ 4 := hmul
      _ ≤ 256 := hpow4
  have hy1le4 : (y + 1) ^ 4 ≤ (y + 4) ^ 4 := by
    have hsq : (y + 1) * (y + 1) ≤ (y + 4) * (y + 4) :=
      mul_le_mul (by linarith only [hy_pos]) (by linarith only [hy_pos])
        (by linarith only [hy_pos]) (by linarith only [hy_pos])
    have e1 : (y + 1) ^ 4 = ((y + 1) * (y + 1)) * ((y + 1) * (y + 1)) := by ring
    have e2 : (y + 4) ^ 4 = ((y + 4) * (y + 4)) * ((y + 4) * (y + 4)) := by ring
    rw [e1, e2]
    exact mul_le_mul hsq hsq (mul_nonneg (by linarith only [hy_pos]) (by linarith only [hy_pos]))
      (mul_nonneg (by linarith only [hy_pos]) (by linarith only [hy_pos]))
  have hEp : Real.exp (-y) * (y + 1) ^ 4 ≤ 256 := by
    have h1 : Real.exp (-y) * (y + 1) ^ 4 ≤ Real.exp (-y) * (y + 4) ^ 4 :=
      mul_le_mul_of_nonneg_left hy1le4 (le_of_lt (Real.exp_pos _))
    linarith only [h1, hE]
  have hy3 : y ^ 3 ≤ (y + 1) ^ 4 := by
    nlinarith only [hy_pos, sq_nonneg y, sq_nonneg (y ^ 2)]
  have hE3 : Real.exp (-y) * y ^ 3 ≤ 256 := by
    have h1 : Real.exp (-y) * y ^ 3 ≤ Real.exp (-y) * (y + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left hy3 (le_of_lt (Real.exp_pos _))
    linarith only [h1, hEp]
  have hquad : 2 * y ^ 2 + 4 * y + 4 ≤ 10 * y ^ 2 := by
    nlinarith only [hy_ge1, sq_nonneg (y - 1)]
  have hqnn : (0 : ℝ) ≤ 2 * y ^ 2 + 4 * y + 4 := by
    nlinarith only [sq_nonneg (y + 1)]
  have hcoh : Kt ^ 2 * (2 * y ^ 2 + 4 * y + 4) ≤ (y / 10 ^ 6) * (10 * y ^ 2) :=
    mul_le_mul hKt2 hquad hqnn (div_nonneg (le_of_lt hy_pos) (by norm_num))
  have hconj1 : (Kt ^ 2 * (2 * y ^ 2 + 4 * y + 4)) * Real.exp (-y) ≤ 1 / 16 := by
    have heq1 : (y / 10 ^ 6) * (10 * y ^ 2) = y ^ 3 / 10 ^ 5 := by ring
    have hX : Kt ^ 2 * (2 * y ^ 2 + 4 * y + 4) * Real.exp (-y) ≤
        (y ^ 3 / 10 ^ 5) * Real.exp (-y) := by
      calc Kt ^ 2 * (2 * y ^ 2 + 4 * y + 4) * Real.exp (-y)
          ≤ ((y / 10 ^ 6) * (10 * y ^ 2)) * Real.exp (-y) :=
            mul_le_mul_of_nonneg_right hcoh (le_of_lt (Real.exp_pos _))
        _ = (y ^ 3 / 10 ^ 5) * Real.exp (-y) := by rw [heq1]
    have hY : (y ^ 3 / 10 ^ 5) * Real.exp (-y) ≤ 1 / 16 := by
      have heq2 : (y ^ 3 / 10 ^ 5) * Real.exp (-y) = (Real.exp (-y) * y ^ 3) / 10 ^ 5 := by
        ring
      rw [heq2]
      linarith only [hE3]
    linarith only [hX, hY]
  have hKle1 : Kt ≤ 1 + Kt ^ 2 := by nlinarith only [sq_nonneg (2 * Kt - 1)]
  have hKle2 : 1 + Kt ^ 2 ≤ 1 + y / 10 ^ 6 := by linarith only [hKt2]
  have hKle3 : 1 + y / 10 ^ 6 ≤ y + 1 := by linarith only [hy_pos]
  have hKle : Kt ≤ y + 1 := by linarith only [hKle1, hKle2, hKle3]
  have hB1 : 2 * Kt * (y + 1) ≤ 2 * (y + 1) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hKle (show (0 : ℝ) ≤ 2 * (y + 1) by linarith only [hy_pos])
    calc 2 * Kt * (y + 1) = 2 * (y + 1) * Kt := by ring
      _ ≤ 2 * (y + 1) * (y + 1) := h
      _ = 2 * (y + 1) ^ 2 := by ring
  have hconj2 : (2 * Kt * (y + 1)) * Real.exp (-y) ≤ 1 / 4 := by
    have h2 : (2 * Kt * (y + 1)) * Real.exp (-y) ≤ 2 * (y + 1) ^ 2 * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right hB1 (le_of_lt (Real.exp_pos _))
    have hXnn : (0 : ℝ) ≤ 2 * (y + 1) ^ 2 * Real.exp (-y) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (y + 1))) (le_of_lt (Real.exp_pos _))
    have hkey : (2 * (y + 1) ^ 2 * Real.exp (-y)) * (y + 1) ^ 2 ≤ 512 := by
      have heq : (2 * (y + 1) ^ 2 * Real.exp (-y)) * (y + 1) ^ 2 =
          2 * (Real.exp (-y) * (y + 1) ^ 4) := by ring
      rw [heq]
      linarith only [hEp]
    have hbig : (10 : ℝ) ^ 12 ≤ (y + 1) ^ 2 := by
      have hy1ge : (10 : ℝ) ^ 6 ≤ y + 1 := by linarith only [hy_ge6]
      have e1 : (10 : ℝ) ^ 12 = (10 : ℝ) ^ 6 * (10 : ℝ) ^ 6 := by ring
      have e2 : (y + 1) ^ 2 = (y + 1) * (y + 1) := by ring
      rw [e1, e2]
      exact mul_le_mul hy1ge hy1ge (by norm_num) (by linarith only [hy1ge])
    have h3 : (2 * (y + 1) ^ 2 * Real.exp (-y)) * (10 : ℝ) ^ 12 ≤ 512 := by
      have h4 := mul_le_mul_of_nonneg_left hbig hXnn
      linarith only [h4, hkey]
    linarith only [h2, h3]
  have hAlg1 : 2 * L ^ 2 + 4 * Kt * (L + Kt) = Kt ^ 2 * (2 * y ^ 2 + 4 * y + 4) := by
    rw [hLy]
    ring
  have hAlg2 : 2 * (L + Kt) = 2 * Kt * (y + 1) := by
    rw [hLy]
    ring
  constructor
  · rw [hAlg1, hExp]
    exact hconj1
  · rw [hAlg2, hExp]
    exact hconj2
  /- @proof-region region.target-node.session.d36fd0b23c16f7dc end -/

end Statlib.Imported

