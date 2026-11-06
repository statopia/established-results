import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
set_option autoImplicit false in
theorem statopia_math_node_3407536053_46f66794 (Kt L : ℝ) (hKt : 0 < Kt)
    (hL1 : 1 ≤ L) (hLbig : (10 : ℝ) ^ 6 * (Kt + 1) ^ 4 ≤ L) :
    4 * (L + Kt) ^ 2 * Real.exp (-L / Kt) +
      4 * (L + Kt) ^ 2 * (Real.exp (-L / Kt)) ^ 2 ≤ 3 / 4 := by
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hK4 : Kt ^ 4 ≤ (Kt + 1) ^ 4 := by
    gcongr
    linarith
  have hK4L : 1000000 * Kt ^ 4 ≤ L := by
    nlinarith [hK4]
  have hKL : Kt ≤ L := by
    by_cases h : Kt ≤ 1
    · exact le_trans h hL1
    · have h1 : 1 ≤ Kt := le_of_lt (lt_of_not_ge h)
      have hp : Kt ^ 1 ≤ Kt ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
      norm_num at hp
      nlinarith [pow_nonneg hKt.le 4]
  have hexp : Real.exp (-L / Kt) * L ^ 4 ≤ 24 * Kt ^ 4 := by
    have ht := Real.pow_div_factorial_le_exp (L / Kt) (div_nonneg hL.le hKt.le) 4
    norm_num at ht
    have hmul := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-L / Kt)).le
    have he : Real.exp (L / Kt) * Real.exp (-L / Kt) = 1 := by
      rw [← Real.exp_add, show L / Kt + -L / Kt = 0 by ring, Real.exp_zero]
    rw [he] at hmul
    have hh : Real.exp (-L / Kt) * (L / Kt) ^ 4 ≤ 24 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hh (pow_nonneg hKt.le 4)
    have hid : Real.exp (-L / Kt) * (L / Kt) ^ 4 * Kt ^ 4 =
        Real.exp (-L / Kt) * L ^ 4 := by
      field_simp [ne_of_gt hKt]
    rwa [hid] at h
  have hsq : (L + Kt) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hpoly : 768 * Kt ^ 4 ≤ (3 / 4 : ℝ) * L ^ 2 := by
    nlinarith [sq_nonneg (L - 1), pow_nonneg hKt.le 4]
  have hmain : 8 * (L + Kt) ^ 2 * Real.exp (-L / Kt) ≤ 3 / 4 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hL 4)).mp
    calc
      (8 * (L + Kt) ^ 2 * Real.exp (-L / Kt)) * L ^ 4 =
          (8 * (L + Kt) ^ 2) * (Real.exp (-L / Kt) * L ^ 4) := by ring
      _ ≤ (8 * (L + Kt) ^ 2) * (24 * Kt ^ 4) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 32 * L ^ 2 * (24 * Kt ^ 4) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [hsq]) (by positivity)
      _ = L ^ 2 * (768 * Kt ^ 4) := by ring
      _ ≤ L ^ 2 * ((3 / 4 : ℝ) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hpoly (sq_nonneg L)
      _ = (3 / 4 : ℝ) * L ^ 4 := by ring
  have he1 : Real.exp (-L / Kt) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL.le) hKt.le
  have he2 : Real.exp (-L / Kt) ^ 2 ≤ Real.exp (-L / Kt) := by
    nlinarith [Real.exp_pos (-L / Kt)]
  have := mul_le_mul_of_nonneg_left he2 (show 0 ≤ 4 * (L + Kt) ^ 2 by positivity)
  linarith
#print axioms statopia_math_node_3407536053_46f66794
end Statlib.Imported

