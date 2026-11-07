import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1914057860_9bbc8370 : ∀ (a L K1 c1 Cvar B N y d m1 : ℝ)
    (ha : 0 < a) (hL : 0 < L) (hK1 : 0 < K1) (hc1 : 0 < c1) (hCvar : 0 < Cvar)
    (hN : 0 < N) (hy : 0 < y) (hd : 0 < d) (hB : 1 ≤ B) (hm1 : 1 ≤ m1)
    (hc1le : c1 ≤ 1)
    (hLa : L ≤ a) (hay : a ≤ y)
    (h4 : 12 * K1 * c1 ^ ((1 : ℝ) / 3) ≤ L)
    (h5 : 96 * K1 ^ 2 * Cvar * c1 ^ ((2 : ℝ) / 3) ≤ L ^ 3)
    (h6 : K1 * c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) = 2 * m1)
    (h7 : B ^ 2 * y ^ 7 / N ≤ c1),
    (let T : ℝ :=
        Real.sqrt N / (4 * d * (K1 * (B ^ 2 * a ^ 4 * d ^ 6 / N) ^ ((-1 : ℝ) / 6)) * a);
      (3 * B * y ≤ T) ∧ (3 * y ≤ T ^ 2 / (2 * Cvar * B ^ 2)) ∧
        (T + B ≤ (1 / (8 * L) + L ^ ((-7 : ℝ) / 2)) * Real.sqrt N)) := by
  /- @proof-region region.target-node.session.5ff5d5c219f003bd begin -/
  intro a L K1 c1 Cvar B N y d m1 ha hL hK1 hc1 hCvar hN hy hd hB hm1 hc1le hLa hay h4 h5 h6 h7
  dsimp only
  set T : ℝ := Real.sqrt N / (4 * d * (K1 * (B ^ 2 * a ^ 4 * d ^ 6 / N) ^ ((-1 : ℝ) / 6)) * a) with hT
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hY : (B ^ 2 * a ^ 4 * d ^ 6 / N) ^ ((-1 : ℝ) / 6)
      = B ^ ((-1 : ℝ) / 3) * a ^ ((-2 : ℝ) / 3) * d ^ (-1 : ℝ) * N ^ ((1 : ℝ) / 6) := by
    rw [Real.div_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have hy1 : (B ^ 2) ^ ((-1 : ℝ) / 6) = B ^ ((-1 : ℝ) / 3) := by
      rw [show (B : ℝ) ^ 2 = B ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast B 2).symm]
      rw [← Real.rpow_mul (le_of_lt hB0)]
      rw [show ((2 : ℕ) : ℝ) * ((-1 : ℝ) / 6) = (-1 : ℝ) / 3 by norm_num]
    have hy2 : (a ^ 4) ^ ((-1 : ℝ) / 6) = a ^ ((-2 : ℝ) / 3) := by
      rw [show (a : ℝ) ^ 4 = a ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast a 4).symm]
      rw [← Real.rpow_mul (le_of_lt ha)]
      rw [show ((4 : ℕ) : ℝ) * ((-1 : ℝ) / 6) = (-2 : ℝ) / 3 by norm_num]
    have hy3 : (d ^ 6) ^ ((-1 : ℝ) / 6) = d ^ (-1 : ℝ) := by
      rw [show (d : ℝ) ^ 6 = d ^ ((6 : ℕ) : ℝ) from (Real.rpow_natCast d 6).symm]
      rw [← Real.rpow_mul (le_of_lt hd)]
      rw [show ((6 : ℕ) : ℝ) * ((-1 : ℝ) / 6) = (-1 : ℝ) by norm_num]
    have hy4 : N ^ ((-1 : ℝ) / 6) = (N ^ ((1 : ℝ) / 6))⁻¹ := by
      rw [show ((-1 : ℝ) / 6) = -((1 : ℝ) / 6) by norm_num, Real.rpow_neg (le_of_lt hN)]
    rw [hy1, hy2, hy3, hy4, div_eq_mul_inv, inv_inv]
  have hwd : d ^ (-1 : ℝ) * d = 1 := by
    have h := Real.rpow_add hd (-1 : ℝ) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h, show (-1 : ℝ) + 1 = 0 by norm_num, Real.rpow_zero]
  have hva : a ^ ((-2 : ℝ) / 3) * a = a ^ ((1 : ℝ) / 3) := by
    have h := Real.rpow_add ha ((-2 : ℝ) / 3) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h, show ((-2 : ℝ) / 3) + 1 = (1 : ℝ) / 3 by norm_num]
  have hD : 4 * d * (K1 * (B ^ 2 * a ^ 4 * d ^ 6 / N) ^ ((-1 : ℝ) / 6)) * a
      = 4 * K1 * B ^ ((-1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6) := by
    rw [hY]
    calc 4 * d * (K1 * (B ^ ((-1 : ℝ) / 3) * a ^ ((-2 : ℝ) / 3) * d ^ (-1 : ℝ) * N ^ ((1 : ℝ) / 6))) * a
        = 4 * K1 * B ^ ((-1 : ℝ) / 3) * (a ^ ((-2 : ℝ) / 3) * a) * (d ^ (-1 : ℝ) * d) * N ^ ((1 : ℝ) / 6) := by ring
      _ = 4 * K1 * B ^ ((-1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * 1 * N ^ ((1 : ℝ) / 6) := by rw [hva, hwd]
      _ = 4 * K1 * B ^ ((-1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6) := by ring
  have hBnp : 0 < B ^ ((-1 : ℝ) / 3) := Real.rpow_pos_of_pos hB0 _
  have hap : 0 < a ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ha _
  have hN6p : 0 < N ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hN _
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hNN : N ^ ((1 : ℝ) / 2) = N ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_add hN]
    rw [show (1 : ℝ) / 3 + 1 / 6 = 1 / 2 by norm_num]
  have hB13 : B ^ ((1 : ℝ) / 3) * B ^ ((-1 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hB0]
    rw [show (1 : ℝ) / 3 + (-1) / 3 = 0 by norm_num, Real.rpow_zero]
  have hB23 : B ^ ((2 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) = B := by
    rw [← Real.rpow_add hB0]
    rw [show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one]
  have hT' : T = Real.sqrt N / (4 * K1 * B ^ ((-1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6)) := by
    rw [hT, hD]
  have hT1 : T = N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) / (4 * K1 * a ^ ((1 : ℝ) / 3)) := by
    rw [hT', Real.sqrt_eq_rpow, hNN]
    rw [div_eq_div_iff (ne_of_gt (mul_pos (mul_pos (mul_pos (mul_pos h4pos hK1) hBnp) hap) hN6p))
      (ne_of_gt (mul_pos (mul_pos h4pos hK1) hap))]
    calc N ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6) * (4 * K1 * a ^ ((1 : ℝ) / 3))
        = 4 * K1 * (N ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6)) * a ^ ((1 : ℝ) / 3) := by ring
      _ = 4 * K1 * (N ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6)) * a ^ ((1 : ℝ) / 3) * (B ^ ((1 : ℝ) / 3) * B ^ ((-1 : ℝ) / 3)) := by
          rw [hB13, mul_one]
      _ = N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) * (4 * K1 * B ^ ((-1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6)) := by ring
  have hBp : 0 < B ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hB0 _
  have hB2p : 0 < B ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hB0 _
  have hNp : 0 < N ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN _
  have hc1p : 0 < c1 ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc1 _

  refine ⟨?_, ?_, ?_⟩
  · rw [hT1]
    have hDpos : 0 < 4 * K1 * a ^ ((1 : ℝ) / 3) := mul_pos (mul_pos h4pos hK1) hap
    rw [le_div_iff₀ hDpos]
    have h7' : B ^ 2 * y ^ 7 ≤ c1 * N := (div_le_iff₀ hN).mp h7
    have hu : (B ^ 2 * y ^ 7) ^ ((1 : ℝ) / 3) ≤ (c1 * N) ^ ((1 : ℝ) / 3) :=
      (Real.rpow_le_rpow_iff (mul_nonneg (pow_nonneg (le_of_lt hB0) 2) (pow_nonneg (le_of_lt hy) 7))
        (mul_nonneg (le_of_lt hc1) (le_of_lt hN)) (by norm_num)).mpr h7'
    have hu2 : B ^ ((2 : ℝ) / 3) * y ^ ((7 : ℝ) / 3) ≤ c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) := by
      have e1 : (B ^ 2 * y ^ 7) ^ ((1 : ℝ) / 3) = B ^ ((2 : ℝ) / 3) * y ^ ((7 : ℝ) / 3) := by
        rw [Real.mul_rpow (pow_nonneg (le_of_lt hB0) 2) (pow_nonneg (le_of_lt hy) 7)]
        rw [show (B : ℝ) ^ 2 = B ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast B 2).symm]
        rw [← Real.rpow_mul (le_of_lt hB0)]
        rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 3) = (2 : ℝ) / 3 by norm_num]
        rw [show (y : ℝ) ^ 7 = y ^ ((7 : ℕ) : ℝ) from (Real.rpow_natCast y 7).symm]
        rw [← Real.rpow_mul (le_of_lt hy)]
        rw [show ((7 : ℕ) : ℝ) * ((1 : ℝ) / 3) = (7 : ℝ) / 3 by norm_num]
      have e2 : (c1 * N) ^ ((1 : ℝ) / 3) = c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) := by
        rw [Real.mul_rpow (le_of_lt hc1) (le_of_lt hN)]
      rw [e1, e2] at hu
      exact hu
    have hy7p : 0 < y ^ ((-7 : ℝ) / 3) := Real.rpow_pos_of_pos hy _
    have hyy : y ^ ((7 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hy]
      rw [show (7 : ℝ) / 3 + (-7) / 3 = 0 by norm_num, Real.rpow_zero]
    have hAz : B ^ ((2 : ℝ) / 3) ≤ c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_right hu2 (le_of_lt hy7p)
      have hL : (B ^ ((2 : ℝ) / 3) * y ^ ((7 : ℝ) / 3)) * y ^ ((-7 : ℝ) / 3) = B ^ ((2 : ℝ) / 3) := by
        calc (B ^ ((2 : ℝ) / 3) * y ^ ((7 : ℝ) / 3)) * y ^ ((-7 : ℝ) / 3)
            = B ^ ((2 : ℝ) / 3) * (y ^ ((7 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3)) := by ring
          _ = B ^ ((2 : ℝ) / 3) := by rw [hyy, mul_one]
      have hR : (c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3)) * y ^ ((-7 : ℝ) / 3)
          = c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3) := by ring
      rw [hL, hR] at h
      exact h
    have ha4 : a ^ ((4 : ℝ) / 3) = a * a ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_add ha (1 : ℝ) ((1 : ℝ) / 3)
      rw [Real.rpow_one] at h
      rw [← h]
      rw [show (1 : ℝ) + (1 : ℝ) / 3 = (4 : ℝ) / 3 by norm_num]
    have hL4 : 12 * K1 * c1 ^ ((1 : ℝ) / 3) ≤ a := le_trans h4 hLa
    have h1' : 12 * K1 * c1 ^ ((1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) ≤ a ^ ((4 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_right hL4 (le_of_lt hap)
      rw [ha4]
      exact h
    have h2' : a ^ ((4 : ℝ) / 3) ≤ y ^ ((4 : ℝ) / 3) :=
      (Real.rpow_le_rpow_iff (le_of_lt ha) (le_of_lt hy) (by norm_num)).mpr hay
    have hLt : 12 * K1 * c1 ^ ((1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) ≤ y ^ ((4 : ℝ) / 3) := le_trans h1' h2'
    have h4a : y * y ^ ((-7 : ℝ) / 3) = y ^ ((-4 : ℝ) / 3) := by
      have h := Real.rpow_add hy (1 : ℝ) ((-7 : ℝ) / 3)
      rw [Real.rpow_one] at h
      rw [← h]
      rw [show (1 : ℝ) + (-7 : ℝ) / 3 = (-4 : ℝ) / 3 by norm_num]
    have hy4 : y ^ ((4 : ℝ) / 3) * y ^ ((-4 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hy]
      rw [show (4 : ℝ) / 3 + (-4) / 3 = 0 by norm_num, Real.rpow_zero]
    have hmain : 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B ^ ((2 : ℝ) / 3) ≤ N ^ ((1 : ℝ) / 3) := by
      have hs1 : 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B ^ ((2 : ℝ) / 3)
          ≤ 12 * K1 * a ^ ((1 : ℝ) / 3) * y * (c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3)) := by
        have hnn : 0 ≤ 12 * K1 * a ^ ((1 : ℝ) / 3) * y :=
          le_of_lt (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 12) hK1) hap) hy)
        have h := mul_le_mul_of_nonneg_left hAz hnn
        calc 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B ^ ((2 : ℝ) / 3)
            = (12 * K1 * a ^ ((1 : ℝ) / 3) * y) * B ^ ((2 : ℝ) / 3) := by ring
          _ ≤ (12 * K1 * a ^ ((1 : ℝ) / 3) * y) * (c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3)) := h
          _ = 12 * K1 * a ^ ((1 : ℝ) / 3) * y * (c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3)) := by ring
      have hs2 : 12 * K1 * a ^ ((1 : ℝ) / 3) * y * (c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3)) ≤ N ^ ((1 : ℝ) / 3) := by
        have he : 12 * K1 * a ^ ((1 : ℝ) / 3) * y * (c1 ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-7 : ℝ) / 3))
            = 12 * K1 * c1 ^ ((1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * (y * y ^ ((-7 : ℝ) / 3)) := by ring
        rw [he, h4a]
        have hnn2 : 0 ≤ N ^ ((1 : ℝ) / 3) * y ^ ((-4 : ℝ) / 3) :=
          le_of_lt (mul_pos hNp (Real.rpow_pos_of_pos hy _))
        have h := mul_le_mul_of_nonneg_right hLt hnn2
        calc 12 * K1 * c1 ^ ((1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3) * y ^ ((-4 : ℝ) / 3)
            = (12 * K1 * c1 ^ ((1 : ℝ) / 3) * a ^ ((1 : ℝ) / 3)) * (N ^ ((1 : ℝ) / 3) * y ^ ((-4 : ℝ) / 3)) := by ring
          _ ≤ y ^ ((4 : ℝ) / 3) * (N ^ ((1 : ℝ) / 3) * y ^ ((-4 : ℝ) / 3)) := h
          _ = (y ^ ((4 : ℝ) / 3) * y ^ ((-4 : ℝ) / 3)) * N ^ ((1 : ℝ) / 3) := by ring
          _ = N ^ ((1 : ℝ) / 3) := by rw [hy4, one_mul]
      exact le_trans hs1 hs2
    have hBmul : 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B ≤ N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_right hmain (le_of_lt hBp)
      have he : (12 * K1 * a ^ ((1 : ℝ) / 3) * y * B ^ ((2 : ℝ) / 3)) * B ^ ((1 : ℝ) / 3)
          = 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B := by
        calc (12 * K1 * a ^ ((1 : ℝ) / 3) * y * B ^ ((2 : ℝ) / 3)) * B ^ ((1 : ℝ) / 3)
            = 12 * K1 * a ^ ((1 : ℝ) / 3) * y * (B ^ ((2 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)) := by ring
          _ = 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B := by rw [hB23]
      rw [he] at h
      exact h
    calc 3 * B * y * (4 * K1 * a ^ ((1 : ℝ) / 3))
        = 12 * K1 * a ^ ((1 : ℝ) / 3) * y * B := by ring
      _ ≤ N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) := hBmul
  · have hDpo : 0 < 4 * K1 * a ^ ((1 : ℝ) / 3) := mul_pos (mul_pos h4pos hK1) hap
    have hden2 : 0 < 2 * Cvar * B ^ 2 := mul_pos (mul_pos (by norm_num) hCvar) (pow_pos hB0 2)
    have hC2pos : 0 < (4 * K1 * a ^ ((1 : ℝ) / 3)) ^ 2 := pow_pos hDpo 2
    have hc1n2p : 0 < c1 ^ ((-2 : ℝ) / 3) := Real.rpow_pos_of_pos hc1 _
    have ha2p : 0 < a ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos ha _
    have hN2p : 0 < N ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hN _
    have hyinv : 0 < y ^ ((-7 : ℝ)) := Real.rpow_pos_of_pos hy _
    have hTmul : T * (4 * K1 * a ^ ((1 : ℝ) / 3)) = N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) := by
      rw [hT1]
      exact le_antisymm ((le_div_iff₀ hDpo).mp le_rfl) ((div_le_iff₀ hDpo).mp le_rfl)
    have hTsq : T ^ 2 * (4 * K1 * a ^ ((1 : ℝ) / 3)) ^ 2 = (N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)) ^ 2 := by
      rw [← hTmul]
      ring
    have hT2div : T ^ 2 = (N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)) ^ 2 / (4 * K1 * a ^ ((1 : ℝ) / 3)) ^ 2 := by
      apply le_antisymm
      · exact (le_div_iff₀ hC2pos).mpr (le_of_eq hTsq)
      · exact (div_le_iff₀ hC2pos).mpr (le_of_eq hTsq.symm)
    have h7b : B ^ 2 * y ^ 7 ≤ c1 * N := (div_le_iff₀ hN).mp h7
    have hy7cancel : y ^ 7 * y ^ ((-7 : ℝ)) = 1 := by
      rw [show (y : ℝ) ^ 7 = y ^ ((7 : ℕ) : ℝ) from (Real.rpow_natCast y 7).symm]
      rw [← Real.rpow_add hy]
      rw [show ((7 : ℕ) : ℝ) + (-7 : ℝ) = 0 by norm_num, Real.rpow_zero]
    have hB2le : B ^ 2 ≤ c1 * N * y ^ ((-7 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right h7b (le_of_lt hyinv)
      have h2 : B ^ 2 * y ^ 7 * y ^ ((-7 : ℝ)) = B ^ 2 := by
        calc B ^ 2 * y ^ 7 * y ^ ((-7 : ℝ)) = B ^ 2 * (y ^ 7 * y ^ ((-7 : ℝ))) := by ring
          _ = B ^ 2 := by rw [hy7cancel, mul_one]
      rw [h2] at h
      exact h
    have hB4 : (B ^ 2) ^ ((-2 : ℝ) / 3) = B ^ ((-4 : ℝ) / 3) := by
      rw [show (B : ℝ) ^ 2 = B ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast B 2).symm]
      rw [← Real.rpow_mul (le_of_lt hB0)]
      rw [show ((2 : ℕ) : ℝ) * ((-2 : ℝ) / 3) = (-4 : ℝ) / 3 by norm_num]
    have hc1N : (c1 * N * y ^ ((-7 : ℝ))) ^ ((-2 : ℝ) / 3)
        = c1 ^ ((-2 : ℝ) / 3) * N ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3) := by
      rw [Real.mul_rpow (mul_nonneg (le_of_lt hc1) (le_of_lt hN)) (le_of_lt hyinv)]
      rw [Real.mul_rpow (le_of_lt hc1) (le_of_lt hN)]
      rw [← Real.rpow_mul (le_of_lt hy)]
      rw [show (-7 : ℝ) * ((-2 : ℝ) / 3) = (14 : ℝ) / 3 by norm_num]
    have hBm4 : c1 ^ ((-2 : ℝ) / 3) * N ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3) ≤ B ^ ((-4 : ℝ) / 3) := by
      have h := Real.rpow_le_rpow_of_nonpos (pow_pos hB0 2) hB2le (show (-2 : ℝ) / 3 ≤ 0 by norm_num)
      rwa [hc1N, hB4] at h
    have hN23 : N ^ ((2 : ℝ) / 3) * N ^ ((-2 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hN]
      rw [show (2 : ℝ) / 3 + (-2) / 3 = 0 by norm_num, Real.rpow_zero]
    have hstep : c1 ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3) ≤ N ^ ((2 : ℝ) / 3) * B ^ ((-4 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_left hBm4 (le_of_lt hN2p)
      have he : N ^ ((2 : ℝ) / 3) * (c1 ^ ((-2 : ℝ) / 3) * N ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3))
          = (N ^ ((2 : ℝ) / 3) * N ^ ((-2 : ℝ) / 3)) * (c1 ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3)) := by ring
      rw [he, hN23, one_mul] at h
      exact h
    have hBsplit : B ^ ((2 : ℝ) / 3) = B ^ 2 * B ^ ((-4 : ℝ) / 3) := by
      have h := Real.rpow_add hB0 ((2 : ℕ) : ℝ) ((-4 : ℝ) / 3)
      rw [Real.rpow_natCast] at h
      rw [show ((2 : ℕ) : ℝ) + (-4 : ℝ) / 3 = (2 : ℝ) / 3 by norm_num] at h
      exact h
    have hRH : B ^ 2 * (c1 ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3)) ≤ N ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_left hstep (le_of_lt (pow_pos hB0 2))
      have hR : B ^ 2 * (N ^ ((2 : ℝ) / 3) * B ^ ((-4 : ℝ) / 3)) = N ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
        calc B ^ 2 * (N ^ ((2 : ℝ) / 3) * B ^ ((-4 : ℝ) / 3))
            = N ^ ((2 : ℝ) / 3) * (B ^ 2 * B ^ ((-4 : ℝ) / 3)) := by ring
          _ = N ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by rw [← hBsplit]
      rw [hR] at h
      exact h
    have hc1cancel : c1 ^ ((2 : ℝ) / 3) * c1 ^ ((-2 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hc1]
      rw [show (2 : ℝ) / 3 + (-2) / 3 = 0 by norm_num, Real.rpow_zero]
    have hA1 : 96 * K1 ^ 2 * Cvar ≤ L ^ 3 * c1 ^ ((-2 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_right h5 (le_of_lt hc1n2p)
      have he : (96 * K1 ^ 2 * Cvar * c1 ^ ((2 : ℝ) / 3)) * c1 ^ ((-2 : ℝ) / 3) = 96 * K1 ^ 2 * Cvar := by
        calc (96 * K1 ^ 2 * Cvar * c1 ^ ((2 : ℝ) / 3)) * c1 ^ ((-2 : ℝ) / 3)
            = 96 * K1 ^ 2 * Cvar * (c1 ^ ((2 : ℝ) / 3) * c1 ^ ((-2 : ℝ) / 3)) := by ring
          _ = 96 * K1 ^ 2 * Cvar := by rw [hc1cancel, mul_one]
      rw [he] at h
      exact h
    have hLy : L ^ 3 ≤ y ^ 3 := by
      have hr : L ^ ((3 : ℕ) : ℝ) ≤ y ^ ((3 : ℕ) : ℝ) :=
        (Real.rpow_le_rpow_iff (le_of_lt hL) (le_of_lt hy)
          (show (0 : ℝ) < ((3 : ℕ) : ℝ) by norm_num)).mpr (le_trans hLa hay)
      rwa [Real.rpow_natCast, Real.rpow_natCast] at hr
    have ha23 : a ^ ((2 : ℝ) / 3) ≤ y ^ ((2 : ℝ) / 3) :=
      (Real.rpow_le_rpow_iff (le_of_lt ha) (le_of_lt hy) (by norm_num)).mpr hay
    have hy3 : y ^ 3 * y ^ ((2 : ℝ) / 3) = y ^ ((11 : ℝ) / 3) := by
      rw [show (y : ℝ) ^ 3 = y ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast y 3).symm]
      rw [← Real.rpow_add hy]
      rw [show ((3 : ℕ) : ℝ) + (2 : ℝ) / 3 = (11 : ℝ) / 3 by norm_num]
    have hLa3 : L ^ 3 * a ^ ((2 : ℝ) / 3) ≤ y ^ ((11 : ℝ) / 3) := by
      calc L ^ 3 * a ^ ((2 : ℝ) / 3) ≤ y ^ 3 * y ^ ((2 : ℝ) / 3) :=
            mul_le_mul hLy ha23 (le_of_lt ha2p) (le_of_lt (pow_pos hy 3))
        _ = y ^ ((11 : ℝ) / 3) := hy3
    have hy14 : y * y ^ ((11 : ℝ) / 3) = y ^ ((14 : ℝ) / 3) := by
      have h := Real.rpow_add hy (1 : ℝ) ((11 : ℝ) / 3)
      rw [Real.rpow_one] at h
      rw [← h]
      rw [show (1 : ℝ) + (11 : ℝ) / 3 = (14 : ℝ) / 3 by norm_num]
    have hAlpha : 96 * K1 ^ 2 * Cvar * y * a ^ ((2 : ℝ) / 3) ≤ c1 ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3) := by
      have h1 := mul_le_mul_of_nonneg_right hA1 (le_of_lt (mul_pos hy ha2p))
      have he1 : (96 * K1 ^ 2 * Cvar) * (y * a ^ ((2 : ℝ) / 3)) = 96 * K1 ^ 2 * Cvar * y * a ^ ((2 : ℝ) / 3) := by ring
      rw [he1] at h1
      have h2 : L ^ 3 * c1 ^ ((-2 : ℝ) / 3) * (y * a ^ ((2 : ℝ) / 3)) ≤ c1 ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3) := by
        have he : L ^ 3 * c1 ^ ((-2 : ℝ) / 3) * (y * a ^ ((2 : ℝ) / 3))
            = c1 ^ ((-2 : ℝ) / 3) * y * (L ^ 3 * a ^ ((2 : ℝ) / 3)) := by ring
        rw [he]
        calc c1 ^ ((-2 : ℝ) / 3) * y * (L ^ 3 * a ^ ((2 : ℝ) / 3))
            ≤ c1 ^ ((-2 : ℝ) / 3) * y * y ^ ((11 : ℝ) / 3) :=
              mul_le_mul_of_nonneg_left hLa3 (le_of_lt (mul_pos hc1n2p hy))
          _ = c1 ^ ((-2 : ℝ) / 3) * y ^ ((14 : ℝ) / 3) := by rw [mul_assoc, hy14]
      exact le_trans h1 h2
    have hmain2 : 96 * K1 ^ 2 * Cvar * B ^ 2 * y * a ^ ((2 : ℝ) / 3) ≤ N ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
      have h := mul_le_mul_of_nonneg_left hAlpha (le_of_lt (pow_pos hB0 2))
      have he : B ^ 2 * (96 * K1 ^ 2 * Cvar * y * a ^ ((2 : ℝ) / 3)) = 96 * K1 ^ 2 * Cvar * B ^ 2 * y * a ^ ((2 : ℝ) / 3) := by ring
      rw [he] at h
      exact le_trans h hRH
    have hL2 : 3 * y * (2 * Cvar * B ^ 2) * (4 * K1 * a ^ ((1 : ℝ) / 3)) ^ 2 = 96 * K1 ^ 2 * Cvar * B ^ 2 * y * a ^ ((2 : ℝ) / 3) := by
      have ha2 : (a ^ ((1 : ℝ) / 3)) ^ 2 = a ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / 3)) 2]
        rw [← Real.rpow_mul (le_of_lt ha)]
        rw [show ((1 : ℝ) / 3) * ((2 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num]
      calc 3 * y * (2 * Cvar * B ^ 2) * (4 * K1 * a ^ ((1 : ℝ) / 3)) ^ 2
          = 96 * K1 ^ 2 * Cvar * B ^ 2 * y * (a ^ ((1 : ℝ) / 3)) ^ 2 := by ring
        _ = 96 * K1 ^ 2 * Cvar * B ^ 2 * y * a ^ ((2 : ℝ) / 3) := by rw [ha2]
    have hR2 : (N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)) ^ 2 = N ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
      have hN2 : (N ^ ((1 : ℝ) / 3)) ^ 2 = N ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast (N ^ ((1 : ℝ) / 3)) 2]
        rw [← Real.rpow_mul (le_of_lt hN)]
        rw [show ((1 : ℝ) / 3) * ((2 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num]
      have hB2 : (B ^ ((1 : ℝ) / 3)) ^ 2 = B ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast (B ^ ((1 : ℝ) / 3)) 2]
        rw [← Real.rpow_mul (le_of_lt hB0)]
        rw [show ((1 : ℝ) / 3) * ((2 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num]
      rw [mul_pow, hN2, hB2]
    rw [hT2div, le_div_iff₀ hden2, le_div_iff₀ hC2pos, hL2, hR2]
    exact hmain2
  · have h8L : 0 < 8 * L := mul_pos (by norm_num) hL
    have hNh : 0 < N ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hN _
    have hc16p : 0 < c1 ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hc1 _
    have hLm16p : 0 < L ^ ((-1 : ℝ) / 6) := Real.rpow_pos_of_pos hL _
    have hL7 : 0 < L ^ ((-7 : ℝ) / 2) := Real.rpow_pos_of_pos hL _
    have hy7 : 0 < y ^ ((-7 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
    have hyinv : 0 < y ^ ((-7 : ℝ)) := Real.rpow_pos_of_pos hy _
    have hly : L ≤ y := le_trans hLa hay
    have h7c : B ^ 2 * y ^ 7 ≤ c1 * N := (div_le_iff₀ hN).mp h7
    have hy7cancel : y ^ 7 * y ^ ((-7 : ℝ)) = 1 := by
      rw [show (y : ℝ) ^ 7 = y ^ ((7 : ℕ) : ℝ) from (Real.rpow_natCast y 7).symm]
      rw [← Real.rpow_add hy]
      rw [show ((7 : ℕ) : ℝ) + (-7 : ℝ) = 0 by norm_num, Real.rpow_zero]
    have hB2le : B ^ 2 ≤ c1 * N * y ^ ((-7 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right h7c (le_of_lt hyinv)
      have h2 : B ^ 2 * y ^ 7 * y ^ ((-7 : ℝ)) = B ^ 2 := by
        calc B ^ 2 * y ^ 7 * y ^ ((-7 : ℝ)) = B ^ 2 * (y ^ 7 * y ^ ((-7 : ℝ))) := by ring
          _ = B ^ 2 := by rw [hy7cancel, mul_one]
      rw [h2] at h
      exact h
    have hB16 : (B ^ 2) ^ ((1 : ℝ) / 6) ≤ (c1 * N * y ^ ((-7 : ℝ))) ^ ((1 : ℝ) / 6) :=
      (Real.rpow_le_rpow_iff (pow_nonneg (le_of_lt hB0) 2)
        (mul_nonneg (mul_nonneg (le_of_lt hc1) (le_of_lt hN)) (le_of_lt hyinv))
        (show (0 : ℝ) < (1 : ℝ) / 6 by norm_num)).mpr hB2le
    have hB2six : (B ^ 2) ^ ((1 : ℝ) / 6) = B ^ ((1 : ℝ) / 3) := by
      rw [show (B : ℝ) ^ 2 = B ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast B 2).symm]
      rw [← Real.rpow_mul (le_of_lt hB0)]
      rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 6) = (1 : ℝ) / 3 by norm_num]
    have hRsix : (c1 * N * y ^ ((-7 : ℝ))) ^ ((1 : ℝ) / 6)
        = c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * y ^ ((-7 : ℝ) / 6) := by
      rw [Real.mul_rpow (mul_nonneg (le_of_lt hc1) (le_of_lt hN)) (le_of_lt hyinv)]
      rw [Real.mul_rpow (le_of_lt hc1) (le_of_lt hN)]
      rw [← Real.rpow_mul (le_of_lt hy)]
      rw [show (-7 : ℝ) * ((1 : ℝ) / 6) = (-7 : ℝ) / 6 by norm_num]
    have hB13le : B ^ ((1 : ℝ) / 3) ≤ c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * y ^ ((-7 : ℝ) / 6) := by
      rw [← hB2six, ← hRsix]
      exact hB16
    have hylow : y ^ ((-7 : ℝ) / 6) ≤ L ^ ((-7 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_nonpos hL hly (show (-7 : ℝ) / 6 ≤ 0 by norm_num)
    have hB13le' : B ^ ((1 : ℝ) / 3) ≤ c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * L ^ ((-7 : ℝ) / 6) :=
      le_trans hB13le (mul_le_mul_of_nonneg_left hylow (le_of_lt (mul_pos hc16p hN6p)))
    have hLm16 : L * L ^ ((-7 : ℝ) / 6) = L ^ ((-1 : ℝ) / 6) := by
      have h := Real.rpow_add hL (1 : ℝ) ((-7 : ℝ) / 6)
      rw [Real.rpow_one] at h
      rw [← h]
      rw [show (1 : ℝ) + (-7 : ℝ) / 6 = (-1 : ℝ) / 6 by norm_num]
    have hL13eq : L ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6) = L ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add hL]
      rw [show (1 : ℝ) / 2 + (-1 : ℝ) / 6 = (1 : ℝ) / 3 by norm_num]
    have hc1m : c1 ^ ((-1 : ℝ) / 6) * c1 ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc1]
      rw [show (-1 : ℝ) / 6 + (1 : ℝ) / 6 = 0 by norm_num, Real.rpow_zero]
    have hK1L : 2 * c1 ^ ((1 : ℝ) / 6) ≤ K1 * L ^ ((1 : ℝ) / 2) := by
      have he : (K1 * c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2)) * c1 ^ ((1 : ℝ) / 6) = K1 * L ^ ((1 : ℝ) / 2) := by
        calc (K1 * c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2)) * c1 ^ ((1 : ℝ) / 6)
            = K1 * L ^ ((1 : ℝ) / 2) * (c1 ^ ((-1 : ℝ) / 6) * c1 ^ ((1 : ℝ) / 6)) := by ring
          _ = K1 * L ^ ((1 : ℝ) / 2) := by rw [hc1m, mul_one]
      have h : K1 * L ^ ((1 : ℝ) / 2) = (2 * m1) * c1 ^ ((1 : ℝ) / 6) := by
        calc K1 * L ^ ((1 : ℝ) / 2)
            = (K1 * c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2)) * c1 ^ ((1 : ℝ) / 6) := he.symm
          _ = (2 * m1) * c1 ^ ((1 : ℝ) / 6) := by rw [h6]
      rw [h]
      have hh : 1 * c1 ^ ((1 : ℝ) / 6) ≤ m1 * c1 ^ ((1 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right hm1 (le_of_lt hc16p)
      calc 2 * c1 ^ ((1 : ℝ) / 6) = 2 * (1 * c1 ^ ((1 : ℝ) / 6)) := by ring
        _ ≤ 2 * (m1 * c1 ^ ((1 : ℝ) / 6)) := mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = 2 * m1 * c1 ^ ((1 : ℝ) / 6) := by ring
    have hchain : 2 * L * N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) ≤ N ^ ((1 : ℝ) / 2) * K1 * a ^ ((1 : ℝ) / 3) := by
      have ha1 : 2 * L * N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)
          ≤ 2 * L * N ^ ((1 : ℝ) / 3) * (c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * L ^ ((-7 : ℝ) / 6)) := by
        have h := mul_le_mul_of_nonneg_left hB13le'
          (le_of_lt (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hL) hNp))
        calc 2 * L * N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)
            = (2 * L * N ^ ((1 : ℝ) / 3)) * B ^ ((1 : ℝ) / 3) := by ring
          _ ≤ (2 * L * N ^ ((1 : ℝ) / 3)) * (c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * L ^ ((-7 : ℝ) / 6)) := h
          _ = 2 * L * N ^ ((1 : ℝ) / 3) * (c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * L ^ ((-7 : ℝ) / 6)) := by ring
      have ha2 : 2 * L * N ^ ((1 : ℝ) / 3) * (c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * L ^ ((-7 : ℝ) / 6))
          = 2 * c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6) := by
        calc 2 * L * N ^ ((1 : ℝ) / 3) * (c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 6) * L ^ ((-7 : ℝ) / 6))
            = 2 * c1 ^ ((1 : ℝ) / 6) * (N ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 6)) * (L * L ^ ((-7 : ℝ) / 6)) := by ring
          _ = 2 * c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6) := by
              simp only [← hNN, hLm16]
      have h2 : 2 * c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6)
          ≤ N ^ ((1 : ℝ) / 2) * K1 * L ^ ((1 : ℝ) / 3) := by
        have h := mul_le_mul_of_nonneg_right hK1L (le_of_lt (mul_pos hNh hLm16p))
        have heL : K1 * L ^ ((1 : ℝ) / 2) * (N ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6)) = N ^ ((1 : ℝ) / 2) * K1 * L ^ ((1 : ℝ) / 3) := by
          rw [← hL13eq]
          ring
        rw [heL] at h
        have he1 : 2 * c1 ^ ((1 : ℝ) / 6) * (N ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6))
            = 2 * c1 ^ ((1 : ℝ) / 6) * N ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 6) := by ring
        rwa [he1] at h
      have hL13a : L ^ ((1 : ℝ) / 3) ≤ a ^ ((1 : ℝ) / 3) :=
        (Real.rpow_le_rpow_iff (le_of_lt hL) (le_of_lt ha) (by norm_num)).mpr hLa
      have ha3 : N ^ ((1 : ℝ) / 2) * K1 * L ^ ((1 : ℝ) / 3) ≤ N ^ ((1 : ℝ) / 2) * K1 * a ^ ((1 : ℝ) / 3) := by
        have h := mul_le_mul_of_nonneg_left hL13a (le_of_lt (mul_pos hNh hK1))
        calc N ^ ((1 : ℝ) / 2) * K1 * L ^ ((1 : ℝ) / 3)
            = (N ^ ((1 : ℝ) / 2) * K1) * L ^ ((1 : ℝ) / 3) := by ring
          _ ≤ (N ^ ((1 : ℝ) / 2) * K1) * a ^ ((1 : ℝ) / 3) := h
          _ = N ^ ((1 : ℝ) / 2) * K1 * a ^ ((1 : ℝ) / 3) := by ring
      refine le_trans ha1 ?_
      rw [ha2]
      exact le_trans h2 ha3
    have hTle : T ≤ Real.sqrt N / (8 * L) := by
      rw [hT1]
      rw [div_le_div_iff₀ (mul_pos (mul_pos h4pos hK1) hap) h8L]
      have h4c := mul_le_mul_of_nonneg_left hchain (by norm_num : (0 : ℝ) ≤ 4)
      calc N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) * (8 * L)
          = 4 * (2 * L * N ^ ((1 : ℝ) / 3) * B ^ ((1 : ℝ) / 3)) := by ring
        _ ≤ 4 * (N ^ ((1 : ℝ) / 2) * K1 * a ^ ((1 : ℝ) / 3)) := h4c
        _ = Real.sqrt N * (4 * K1 * a ^ ((1 : ℝ) / 3)) := by rw [Real.sqrt_eq_rpow]; ring
    have hBsq : (B ^ 2) ^ ((1 : ℝ) / 2) = B := by
      rw [show (B : ℝ) ^ 2 = B ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast B 2).symm]
      rw [← Real.rpow_mul (le_of_lt hB0)]
      rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    have hBhalf : (B ^ 2) ^ ((1 : ℝ) / 2) ≤ (c1 * N * y ^ ((-7 : ℝ))) ^ ((1 : ℝ) / 2) :=
      (Real.rpow_le_rpow_iff (pow_nonneg (le_of_lt hB0) 2)
        (mul_nonneg (mul_nonneg (le_of_lt hc1) (le_of_lt hN)) (le_of_lt hyinv))
        (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)).mpr hB2le
    have hRhalf : (c1 * N * y ^ ((-7 : ℝ))) ^ ((1 : ℝ) / 2)
        = c1 ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) * y ^ ((-7 : ℝ) / 2) := by
      rw [Real.mul_rpow (mul_nonneg (le_of_lt hc1) (le_of_lt hN)) (le_of_lt hyinv)]
      rw [Real.mul_rpow (le_of_lt hc1) (le_of_lt hN)]
      rw [← Real.rpow_mul (le_of_lt hy)]
      rw [show (-7 : ℝ) * ((1 : ℝ) / 2) = (-7 : ℝ) / 2 by norm_num]
    have hc1half : c1 ^ ((1 : ℝ) / 2) ≤ 1 := by
      have h := (Real.rpow_le_rpow_iff (le_of_lt hc1) (by norm_num : (0 : ℝ) ≤ 1)
        (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)).mpr hc1le
      simpa using h
    have hstep1 : c1 ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) * y ^ ((-7 : ℝ) / 2) ≤ N ^ ((1 : ℝ) / 2) * y ^ ((-7 : ℝ) / 2) := by
      have h := mul_le_mul_of_nonneg_right hc1half (le_of_lt (mul_pos hNh hy7))
      have he : c1 ^ ((1 : ℝ) / 2) * (N ^ ((1 : ℝ) / 2) * y ^ ((-7 : ℝ) / 2))
          = c1 ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) * y ^ ((-7 : ℝ) / 2) := by ring
      rw [he, one_mul] at h
      exact h
    have hylow2 : y ^ ((-7 : ℝ) / 2) ≤ L ^ ((-7 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hL hly (show (-7 : ℝ) / 2 ≤ 0 by norm_num)
    have hstep2 : N ^ ((1 : ℝ) / 2) * y ^ ((-7 : ℝ) / 2) ≤ N ^ ((1 : ℝ) / 2) * L ^ ((-7 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hylow2 (le_of_lt hNh)
    have hBle : B ≤ Real.sqrt N * L ^ ((-7 : ℝ) / 2) := by
      rw [← hBsq, Real.sqrt_eq_rpow]
      exact le_trans hBhalf (le_trans (le_of_eq hRhalf) (le_trans hstep1 hstep2))
    have hsum : T + B ≤ Real.sqrt N / (8 * L) + Real.sqrt N * L ^ ((-7 : ℝ) / 2) := add_le_add hTle hBle
    have hfin : Real.sqrt N / (8 * L) + Real.sqrt N * L ^ ((-7 : ℝ) / 2)
        = (1 / (8 * L) + L ^ ((-7 : ℝ) / 2)) * Real.sqrt N := by
      rw [add_mul]
      ring
    exact le_trans hsum (le_of_eq hfin)
  /- @proof-region region.target-node.session.5ff5d5c219f003bd end -/

end Statlib.Imported

