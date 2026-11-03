import Lean
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Vocabulary
import ProverJobs.job_paper_8d45c5e7199146b78778677b2fbc23cf.Base

namespace PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_856880814_cb48915c : ∀ (m : ℕ) (hm : 1 ≤ m) (L B s : ℝ)
    (hL : 0 < L) (hB : 0 ≤ B) (hs : 0 ≤ s),
    (2 : ℝ) ^ (m - 1) *
        (s ^ (m - 1) * (s * (2 * (m.factorial : ℝ) * (8 * L) ^ m)) + (B * s) ^ m)
      ≤ ((32 * L + B) * s * (m : ℝ)) ^ m := by
  /- @proof-region region.target-node.session.7ac6969b5f1d8865 begin -/
  intro m hm L B s hL hB hs
  have pow_mono : ∀ (a b : ℝ) (n : ℕ), 0 ≤ a → a ≤ b → a ^ n ≤ b ^ n := by
    intro a b n ha hab
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      calc a ^ k * a ≤ b ^ k * a := mul_le_mul_of_nonneg_right ih ha
        _ ≤ b ^ k * b := mul_le_mul_of_nonneg_left hab (pow_nonneg (le_trans ha hab) k)
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    have hfac_all : ∀ n : ℕ, (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Nat.factorial_succ]
        push_cast
        calc ((k : ℝ) + 1) * (k.factorial : ℝ) ≤ ((k : ℝ) + 1) * (k : ℝ) ^ k :=
                mul_le_mul_of_nonneg_left ih (by positivity)
          _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ k :=
                mul_le_mul_of_nonneg_left
                  (pow_mono (k : ℝ) ((k : ℝ) + 1) k (by positivity) (by linarith))
                  (by positivity)
          _ = ((k : ℝ) + 1) ^ (k + 1) := by rw [pow_succ]; ring
    exact hfac_all m
  have h2 : (2 : ℝ) ^ (m - 1) ≤ (m : ℝ) ^ m := by
    rcases eq_or_lt_of_le hm with h1 | hgt
    · rw [← h1]; norm_num
    · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by
        have h : (2 : ℕ) ≤ m := by omega
        exact_mod_cast h
      have step1 : (2 : ℝ) ^ (m - 1) ≤ (m : ℝ) ^ (m - 1) :=
        pow_mono 2 (m : ℝ) (m - 1) (by norm_num) hm2
      have step2 : (m : ℝ) ^ (m - 1) ≤ (m : ℝ) ^ m := by
        have hge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hb : (0 : ℝ) ≤ (m : ℝ) ^ (m - 1) := pow_nonneg (by positivity) _
        calc (m : ℝ) ^ (m - 1) = (m : ℝ) ^ (m - 1) * 1 := by ring
          _ ≤ (m : ℝ) ^ (m - 1) * (m : ℝ) := mul_le_mul_of_nonneg_left hge hb
          _ = (m : ℝ) ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
      exact le_trans step1 step2
  have hspow : s ^ (m - 1) * s = s ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
  have hBspow : (B * s) ^ m = B ^ m * s ^ m := by rw [mul_pow]
  have hsnn : (0 : ℝ) ≤ s ^ m := pow_nonneg hs m
  have hA : (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m) ≤
      (16 * L * (m : ℝ)) ^ m := by
    have hEq : (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m)
        = (16 * L) ^ m * (m.factorial : ℝ) := by
      have hp : (2 : ℝ) ^ (m - 1) * 2 = 2 ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
      have h2L : (2 : ℝ) ^ m * (8 * L) ^ m = (16 * L) ^ m := by
        rw [← mul_pow]; congr 1; ring
      calc (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m)
          = ((2 : ℝ) ^ (m - 1) * 2) * ((8 * L) ^ m * (m.factorial : ℝ)) := by ring
        _ = (2 : ℝ) ^ m * ((8 * L) ^ m * (m.factorial : ℝ)) := by rw [hp]
        _ = ((2 : ℝ) ^ m * (8 * L) ^ m) * (m.factorial : ℝ) := by ring
        _ = (16 * L) ^ m * (m.factorial : ℝ) := by rw [h2L]
    rw [hEq]
    calc (16 * L) ^ m * (m.factorial : ℝ) ≤ (16 * L) ^ m * (m : ℝ) ^ m :=
            mul_le_mul_of_nonneg_left hfac (pow_nonneg (mul_nonneg (by norm_num) hL.le) m)
      _ = (16 * L * (m : ℝ)) ^ m := by rw [← mul_pow]
  have hB2 : (2 : ℝ) ^ (m - 1) * B ^ m ≤ (B * (m : ℝ)) ^ m := by
    have h : (2 : ℝ) ^ (m - 1) * B ^ m ≤ (m : ℝ) ^ m * B ^ m :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hB m)
    calc (2 : ℝ) ^ (m - 1) * B ^ m ≤ (m : ℝ) ^ m * B ^ m := h
      _ = B ^ m * (m : ℝ) ^ m := by ring
      _ = (B * (m : ℝ)) ^ m := by rw [mul_pow]
  have hbinom : (16 * L * (m : ℝ)) ^ m + (B * (m : ℝ)) ^ m ≤ ((16 * L + B) * (m : ℝ)) ^ m := by
    have h := pow_add_pow_le (x := 16 * L * (m : ℝ)) (y := B * (m : ℝ)) (n := m)
      (mul_nonneg (mul_nonneg (by norm_num) hL.le) (by positivity))
      (mul_nonneg hB (by positivity))
      (by omega)
    rw [show 16 * L * (m : ℝ) + B * (m : ℝ) = (16 * L + B) * (m : ℝ) by ring] at h
    exact h
  have hkey : (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m + B ^ m) ≤
      ((32 * L + B) * (m : ℝ)) ^ m := by
    have hsplit : (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m + B ^ m)
        = (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m) + (2 : ℝ) ^ (m - 1) * B ^ m := by
          ring
    rw [hsplit]
    calc (2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m) + (2 : ℝ) ^ (m - 1) * B ^ m
        ≤ (16 * L * (m : ℝ)) ^ m + (B * (m : ℝ)) ^ m := add_le_add hA hB2
      _ ≤ ((16 * L + B) * (m : ℝ)) ^ m := hbinom
      _ ≤ ((32 * L + B) * (m : ℝ)) ^ m := by
            apply pow_mono
            · exact mul_nonneg (by linarith [hL, hB]) (by positivity)
            · exact mul_le_mul_of_nonneg_right (by linarith [hL]) (by positivity)
  have hLs : (2 : ℝ) ^ (m - 1) *
        (s ^ (m - 1) * (s * (2 * (m.factorial : ℝ) * (8 * L) ^ m)) + (B * s) ^ m)
      = s ^ m * ((2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m + B ^ m)) := by
    have h1 : s ^ (m - 1) * (s * (2 * (m.factorial : ℝ) * (8 * L) ^ m))
        = s ^ m * (2 * (m.factorial : ℝ) * (8 * L) ^ m) := by
      rw [← hspow]; ring
    rw [hBspow, h1]; ring
  have hRs : ((32 * L + B) * s * (m : ℝ)) ^ m = s ^ m * ((32 * L + B) * (m : ℝ)) ^ m := by
    rw [show (32 * L + B) * s * (m : ℝ) = s * ((32 * L + B) * (m : ℝ)) from by ring]
    rw [mul_pow]
  calc (2 : ℝ) ^ (m - 1) *
        (s ^ (m - 1) * (s * (2 * (m.factorial : ℝ) * (8 * L) ^ m)) + (B * s) ^ m)
      = s ^ m * ((2 : ℝ) ^ (m - 1) * (2 * (m.factorial : ℝ) * (8 * L) ^ m + B ^ m)) := hLs
    _ ≤ s ^ m * ((32 * L + B) * (m : ℝ)) ^ m := mul_le_mul_of_nonneg_left hkey hsnn
    _ = ((32 * L + B) * s * (m : ℝ)) ^ m := by rw [hRs]
  /- @proof-region region.target-node.session.7ac6969b5f1d8865 end -/

end Statlib.Imported

