import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ProvedNodes.Node_1914057860_9bbc8370_2b47e152

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
theorem statopia_math_node_2877967487_e4e3f4f7 : ∀ (delta1 Cvar Kstar : ℝ)
    (hdelta1 : 0 < delta1) (hCvar_pos : 0 < Cvar) (hCvar_lt : Cvar < 1)
    (hKstar : 0 < Kstar),
    let m1 : ℝ := max 1 delta1
    let C1 : ℝ := 1 / (8 * Real.log 2) + (Real.log 2) ^ ((-7 : ℝ) / 2)
    ∃ c1 : ℝ, 0 < c1 ∧
      ∃ K1 : ℝ, 0 < K1 ∧
        c1 ≤ 1 ∧
        K1 ≤ (max Kstar 2)⁻¹ ∧
        K1 * c1 ^ ((-1 : ℝ) / 6) * (Real.log 2) ^ ((1 : ℝ) / 2) = 2 * m1 ∧
        K1 * c1 ^ ((1 : ℝ) / 3) ≤ Real.log 2 / 12 ∧
        K1 ^ 2 * c1 ^ ((2 : ℝ) / 3) ≤ (Real.log 2) ^ 3 / (96 * Cvar) ∧
        ∀ (n : ℕ), 0 < n → ∀ (m : ℕ), 0 < m → ∀ (p : ℕ), 2 ≤ p →
          ∀ (B : ℝ), 1 ≤ B → ∀ (delta : ℝ), 0 < |delta| → |delta| < delta1 →
            B ^ 2 * (Real.log ((p : ℝ) * (n : ℝ))) ^ 7 / (n : ℝ) ≤ c1 →
              B ^ 2 * (Real.log ((p : ℝ) * (m : ℝ))) ^ 7 / (m : ℝ) ≤ c1 →
                let phi_n : ℝ :=
                  K1 * (B ^ 2 * (Real.log (p : ℝ)) ^ 4 / (n : ℝ)) ^ ((-1 : ℝ) / 6)
                let phi_m : ℝ :=
                  K1 * (B ^ 2 * (Real.log (p : ℝ)) ^ 4 * |delta| ^ 6 / (m : ℝ)) ^ ((-1 : ℝ) / 6)
                let t_n : ℝ := Real.sqrt (n : ℝ) / (4 * phi_n * Real.log (p : ℝ))
                let t_m : ℝ := Real.sqrt (m : ℝ) / (4 * |delta| * phi_m * Real.log (p : ℝ))
                2 ≤ phi_n ∧ 2 ≤ phi_m ∧
                  3 * B * Real.log ((p : ℝ) * (n : ℝ)) ≤ t_n ∧
                  3 * B * Real.log ((p : ℝ) * (m : ℝ)) ≤ t_m ∧
                  3 * Real.log ((p : ℝ) * (n : ℝ)) ≤ t_n ^ 2 / (2 * Cvar * B ^ 2) ∧
                  3 * Real.log ((p : ℝ) * (m : ℝ)) ≤ t_m ^ 2 / (2 * Cvar * B ^ 2) ∧
                  t_n + B ≤ C1 * Real.sqrt (n : ℝ) ∧
                  t_m + B ≤ C1 * Real.sqrt (m : ℝ) := by
  /- @proof-region region.target-node.session.7462d8f5babac5a1 begin -/
  intro delta1 Cvar Kstar hdelta1 hCvar_pos hCvar_lt hKstar
  dsimp only
  set L : ℝ := Real.log 2 with hLdef
  set m1 : ℝ := max 1 delta1 with hm1def
  obtain ⟨c1, hc1def⟩ : ∃ c : ℝ,
      c = min (min 1 (L ^ (3 : ℝ) / (576 * m1 ^ 2)))
        (min (L ^ (4 : ℝ) / (384 * m1 ^ 2 * Cvar))
          (((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) ^ ((6 : ℝ)))) := ⟨_, rfl⟩
  obtain ⟨K1, hK1def⟩ : ∃ k : ℝ, k = 2 * m1 * c1 ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2) :=
    ⟨_, rfl⟩
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by norm_num)
  have hm1pos : 0 < m1 := by
    rw [hm1def]
    positivity
  have hm1ge1 : 1 ≤ m1 := by
    rw [hm1def]
    exact le_max_left 1 delta1
  have hKmax : 0 < max Kstar 2 := lt_of_lt_of_le (by norm_num) (le_max_right Kstar 2)
  have hc1pos : 0 < c1 := by
    rw [hc1def]
    have h2 : 0 < L ^ (3 : ℝ) / (576 * m1 ^ 2) := by positivity
    have h3 : 0 < L ^ (4 : ℝ) / (384 * m1 ^ 2 * Cvar) := by positivity
    have h4 : 0 < ((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) ^ ((6 : ℝ)) := by positivity
    positivity
  have hK1pos : 0 < K1 := by
    rw [hK1def]
    positivity
  have hc1le1 : c1 ≤ 1 := by
    rw [hc1def]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hceq : K1 * c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) = 2 * m1 := by
    rw [hK1def]
    have hc1r : c1 ^ ((1 : ℝ) / 6) * c1 ^ ((-1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc1pos, show (1 : ℝ) / 6 + (-1 : ℝ) / 6 = 0 from by norm_num,
        Real.rpow_zero]
    have hLr : L ^ ((-1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hLpos, show (-1 : ℝ) / 2 + (1 : ℝ) / 2 = 0 from by norm_num,
        Real.rpow_zero]
    calc 2 * m1 * c1 ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2) * c1 ^ ((-1 : ℝ) / 6)
          * L ^ ((1 : ℝ) / 2)
        = 2 * m1 * (c1 ^ ((1 : ℝ) / 6) * c1 ^ ((-1 : ℝ) / 6))
            * (L ^ ((-1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) := by ring
      _ = 2 * m1 := by
          rw [hc1r, hLr]
          ring
  have hd : K1 * c1 ^ ((1 : ℝ) / 3) ≤ L / 12 := by
    rw [hK1def]
    have hD2 : c1 ≤ L ^ (3 : ℝ) / (576 * m1 ^ 2) := by
      rw [hc1def]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hL32 : (L ^ (3 : ℝ)) ^ ((1 : ℝ) / 2) = L ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_mul (le_of_lt hLpos) 3 ((1 : ℝ) / 2),
        show (3 : ℝ) * ((1 : ℝ) / 2) = (3 : ℝ) / 2 from by norm_num]
    have h576 : ((576 : ℝ) * m1 ^ 2) ^ ((1 : ℝ) / 2) = 24 * m1 := by
      rw [← Real.sqrt_eq_rpow]
      rw [show (576 : ℝ) * m1 ^ 2 = (24 * m1) ^ 2 from by ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 24 * m1)]
    have hD2half : (L ^ (3 : ℝ) / (576 * m1 ^ 2)) ^ ((1 : ℝ) / 2)
        = L ^ ((3 : ℝ) / 2) / (24 * m1) := by
      rw [Real.div_rpow (by positivity) (by positivity) ((1 : ℝ) / 2), hL32, h576]
    have hc1half : c1 ^ ((1 : ℝ) / 2) ≤ L ^ ((3 : ℝ) / 2) / (24 * m1) := by
      calc c1 ^ ((1 : ℝ) / 2) ≤ (L ^ (3 : ℝ) / (576 * m1 ^ 2)) ^ ((1 : ℝ) / 2) :=
            (Real.rpow_le_rpow_iff (le_of_lt hc1pos) (by positivity) (by norm_num)).2 hD2
        _ = L ^ ((3 : ℝ) / 2) / (24 * m1) := hD2half
    have hc16_13 : c1 ^ ((1 : ℝ) / 6) * c1 ^ ((1 : ℝ) / 3) = c1 ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hc1pos, show (1 : ℝ) / 6 + (1 : ℝ) / 3 = (1 : ℝ) / 2 from by norm_num]
    have hstep : 2 * m1 * c1 ^ ((1 : ℝ) / 2) ≤ L ^ ((3 : ℝ) / 2) / 12 := by
      have h1 : 2 * m1 * c1 ^ ((1 : ℝ) / 2) ≤ 2 * m1 * (L ^ ((3 : ℝ) / 2) / (24 * m1)) :=
        mul_le_mul_of_nonneg_left hc1half (by linarith)
      have h2 : 2 * m1 * (L ^ ((3 : ℝ) / 2) / (24 * m1)) = L ^ ((3 : ℝ) / 2) / 12 := by
        field_simp
        ring
      linarith [h1, h2]
    calc 2 * m1 * c1 ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2) * c1 ^ ((1 : ℝ) / 3)
        = 2 * m1 * (c1 ^ ((1 : ℝ) / 6) * c1 ^ ((1 : ℝ) / 3)) * L ^ ((-1 : ℝ) / 2) := by ring
      _ = 2 * m1 * c1 ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 2) := by rw [hc16_13]
      _ ≤ (L ^ ((3 : ℝ) / 2) / 12) * L ^ ((-1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = L / 12 := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hLpos,
            show (3 : ℝ) / 2 + (-1 : ℝ) / 2 = 1 from by norm_num, Real.rpow_one]
  have he : K1 ^ 2 * c1 ^ ((2 : ℝ) / 3) ≤ L ^ 3 / (96 * Cvar) := by
    rw [hK1def]
    have hc1sq : (c1 ^ ((1 : ℝ) / 6)) ^ 2 = c1 ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hc1pos) ((1 : ℝ) / 6) 2,
        show (1 : ℝ) / 6 * 2 = (1 : ℝ) / 3 from by norm_num]
    have hLsq : (L ^ ((-1 : ℝ) / 2)) ^ 2 = L ^ ((-1 : ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hLpos) ((-1 : ℝ) / 2) 2,
        show (-1 : ℝ) / 2 * 2 = (-1 : ℝ) from by norm_num]
    have hD3 : c1 ≤ L ^ (4 : ℝ) / (384 * m1 ^ 2 * Cvar) := by
      rw [hc1def]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hc1_13_23 : c1 ^ ((1 : ℝ) / 3) * c1 ^ ((2 : ℝ) / 3) = c1 := by
      rw [← Real.rpow_add hc1pos, show (1 : ℝ) / 3 + (2 : ℝ) / 3 = 1 from by norm_num,
        Real.rpow_one]
    have hKsq : (2 * m1 * c1 ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2)) ^ 2
        = 4 * m1 ^ 2 * (c1 ^ ((1 : ℝ) / 3) * L ^ ((-1 : ℝ))) := by
      rw [mul_pow, mul_pow, mul_pow, hc1sq, hLsq]
      ring
    calc (2 * m1 * c1 ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2)) ^ 2 * c1 ^ ((2 : ℝ) / 3)
        = (4 * m1 ^ 2 * (c1 ^ ((1 : ℝ) / 3) * L ^ ((-1 : ℝ)))) * c1 ^ ((2 : ℝ) / 3) := by
          rw [hKsq]
      _ = 4 * m1 ^ 2 * (c1 ^ ((1 : ℝ) / 3) * c1 ^ ((2 : ℝ) / 3)) * L ^ ((-1 : ℝ)) := by ring
      _ = 4 * m1 ^ 2 * c1 * L ^ ((-1 : ℝ)) := by rw [hc1_13_23]
      _ ≤ 4 * m1 ^ 2 * (L ^ (4 : ℝ) / (384 * m1 ^ 2 * Cvar)) * L ^ ((-1 : ℝ)) := by
            have hnn : (0 : ℝ) ≤ 4 * m1 ^ 2 * L ^ ((-1 : ℝ)) := by positivity
            calc 4 * m1 ^ 2 * c1 * L ^ ((-1 : ℝ))
                = (4 * m1 ^ 2 * L ^ ((-1 : ℝ))) * c1 := by ring
              _ ≤ (4 * m1 ^ 2 * L ^ ((-1 : ℝ))) * (L ^ (4 : ℝ) / (384 * m1 ^ 2 * Cvar)) :=
                  mul_le_mul_of_nonneg_left hD3 hnn
              _ = 4 * m1 ^ 2 * (L ^ (4 : ℝ) / (384 * m1 ^ 2 * Cvar)) * L ^ ((-1 : ℝ)) := by ring
      _ = L ^ 3 / (96 * Cvar) := by
            rw [← Real.rpow_natCast L 3]
            have hcombine : L ^ (4 : ℝ) * L ^ ((-1 : ℝ)) = L ^ (((3 : ℕ)) : ℝ) := by
              rw [← Real.rpow_add hLpos,
                show (4 : ℝ) + (-1 : ℝ) = (((3 : ℕ)) : ℝ) from by norm_num]
            rw [← hcombine]
            field_simp
            ring
  refine ⟨c1, hc1pos, K1, hK1pos, hc1le1, ?_, hceq, hd, he, ?_⟩
  · rw [hK1def]
    have hbasepos : 0 < (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1) := by positivity
    have hbase6pos : 0 < ((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) ^ ((6 : ℝ)) := by
      positivity
    have hD4 : c1 ≤ ((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) ^ ((6 : ℝ)) := by
      rw [hc1def]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hc16 : c1 ^ ((1 : ℝ) / 6) ≤ (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1) := by
      have h6 : (((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) ^ ((6 : ℝ))) ^ ((1 : ℝ) / 6)
          = (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1) := by
        rw [← Real.rpow_mul (le_of_lt hbasepos) 6 ((1 : ℝ) / 6),
          show (6 : ℝ) * ((1 : ℝ) / 6) = 1 from by norm_num, Real.rpow_one]
      calc c1 ^ ((1 : ℝ) / 6)
          ≤ (((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) ^ ((6 : ℝ))) ^ ((1 : ℝ) / 6) :=
            (Real.rpow_le_rpow_iff (le_of_lt hc1pos) (le_of_lt hbase6pos) (by norm_num)).2 hD4
        _ = (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1) := h6
    have hstep : 2 * m1 * c1 ^ ((1 : ℝ) / 6) ≤ (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) := by
      have h1 : 2 * m1 * c1 ^ ((1 : ℝ) / 6)
          ≤ 2 * m1 * ((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1)) :=
        mul_le_mul_of_nonneg_left hc16 (by linarith)
      have h2 : 2 * m1 * ((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) / (2 * m1))
          = (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2) := by
        field_simp
      linarith [h1, h2]
    calc 2 * m1 * c1 ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2)
        ≤ ((max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2)) * L ^ ((-1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (max Kstar 2)⁻¹ * (L ^ ((1 : ℝ) / 2) * L ^ ((-1 : ℝ) / 2)) := by ring
      _ = (max Kstar 2)⁻¹ * L ^ ((1 : ℝ) / 2 + (-1 : ℝ) / 2) := by
          rw [Real.rpow_add hLpos]
      _ = (max Kstar 2)⁻¹ * L ^ (0 : ℝ) := by
          rw [show (1 : ℝ) / 2 + (-1 : ℝ) / 2 = 0 from by norm_num]
      _ = (max Kstar 2)⁻¹ := by rw [Real.rpow_zero, mul_one]
  · intro n hn m hm p hp B hB delta hdelta hdeltalt hf hg
    set a : ℝ := Real.log (p : ℝ) with hadef
    set yn : ℝ := Real.log ((p : ℝ) * (n : ℝ)) with hyndef
    set ym : ℝ := Real.log ((p : ℝ) * (m : ℝ)) with hymdef
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have ha_pos : 0 < a := by
      rw [hadef]
      exact Real.log_pos hp1
    have hL_le_a : L ≤ a := by
      rw [hadef, hLdef]
      exact Real.log_le_log (by norm_num) (by linarith)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hpn_ge : (p : ℝ) ≤ (p : ℝ) * (n : ℝ) := by
      calc (p : ℝ) = (p : ℝ) * 1 := by ring
        _ ≤ (p : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 (le_of_lt hp0)
    have hpm_ge : (p : ℝ) ≤ (p : ℝ) * (m : ℝ) := by
      calc (p : ℝ) = (p : ℝ) * 1 := by ring
        _ ≤ (p : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_left hm1 (le_of_lt hp0)
    have ha_le_yn : a ≤ yn := by
      rw [hadef, hyndef]
      exact Real.log_le_log hp0 hpn_ge
    have ha_le_ym : a ≤ ym := by
      rw [hadef, hymdef]
      exact Real.log_le_log hp0 hpm_ge
    have hyn_pos : 0 < yn := lt_of_lt_of_le ha_pos ha_le_yn
    have hym_pos : 0 < ym := lt_of_lt_of_le ha_pos ha_le_ym
    have hL_le_yn : L ≤ yn := le_trans hL_le_a ha_le_yn
    have hL_le_ym : L ≤ ym := le_trans hL_le_a ha_le_ym
    have hdelta_le : |delta| ≤ m1 := by
      rw [hm1def]
      exact le_trans (le_of_lt hdeltalt) (le_max_right 1 delta1)
    have hdeltapos : 0 < |delta| := hdelta
    have hLneg3 : L ^ ((-3 : ℝ)) * L ^ 3 = 1 := by
      rw [← Real.rpow_natCast L 3, ← Real.rpow_add hLpos ((-3 : ℝ)) (((3 : ℕ)) : ℝ),
        show (-3 : ℝ) + (((3 : ℕ)) : ℝ) = 0 from by norm_num, Real.rpow_zero]
    have hLneg : (L ^ ((-3 : ℝ))) ^ ((-1 : ℝ) / 6) = L ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (le_of_lt hLpos) ((-3 : ℝ)) ((-1 : ℝ) / 6),
        show (-3 : ℝ) * ((-1 : ℝ) / 6) = (1 : ℝ) / 2 from by norm_num]
    have hLneg3' : L ^ 3 * L ^ ((-3 : ℝ)) = 1 := by rw [mul_comm]; exact hLneg3
    have hratio_gen : ∀ y : ℝ, 0 < y → a ≤ y → a ^ 4 / y ^ 7 ≤ L ^ ((-3 : ℝ)) := by
      intro y hy hle
      have hL3a3 : L ^ 3 ≤ a ^ 3 := by gcongr
      have hA : a ^ 4 * L ^ 3 ≤ a ^ 4 * a ^ 3 := by gcongr
      have hA2 : a ^ 4 * a ^ 3 = a ^ 7 := by ring
      have hB7 : a ^ 7 ≤ y ^ 7 := by gcongr
      have h1 : a ^ 4 * L ^ 3 ≤ y ^ 7 := by linarith
      have h2 : a ^ 4 ≤ y ^ 7 * L ^ ((-3 : ℝ)) := by
        have h3 : a ^ 4 * L ^ 3 * L ^ ((-3 : ℝ)) ≤ y ^ 7 * L ^ ((-3 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h4 : a ^ 4 * L ^ 3 * L ^ ((-3 : ℝ)) = a ^ 4 := by
          rw [mul_assoc, hLneg3', mul_one]
        linarith [h3, h4]
      have h5 : a ^ 4 * (y ^ 7)⁻¹ ≤ y ^ 7 * L ^ ((-3 : ℝ)) * (y ^ 7)⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h6 : y ^ 7 * L ^ ((-3 : ℝ)) * (y ^ 7)⁻¹ = L ^ ((-3 : ℝ)) := by
        field_simp
      have h7 : a ^ 4 * (y ^ 7)⁻¹ = a ^ 4 / y ^ 7 := by ring
      linarith [h5, h6, h7]
    have hYX_gen : ∀ (N y t : ℝ), 0 < N → 0 < y → a ≤ y → B ^ 2 * y ^ 7 / N ≤ c1 →
        B ^ 2 * a ^ 4 * t ^ 6 / N ≤ c1 * L ^ ((-3 : ℝ)) * t ^ 6 := by
      intro N y t hN hy hle hg
      have hr : a ^ 4 / y ^ 7 ≤ L ^ ((-3 : ℝ)) := hratio_gen y hy hle
      have h1 : B ^ 2 * a ^ 4 * t ^ 6 / N = (B ^ 2 * y ^ 7 / N) * (a ^ 4 / y ^ 7) * t ^ 6 := by
        field_simp
      calc B ^ 2 * a ^ 4 * t ^ 6 / N
          = (B ^ 2 * y ^ 7 / N) * (a ^ 4 / y ^ 7) * t ^ 6 := h1
        _ ≤ c1 * (a ^ 4 / y ^ 7) * t ^ 6 := by
            have h2 : (B ^ 2 * y ^ 7 / N) * (a ^ 4 / y ^ 7) ≤ c1 * (a ^ 4 / y ^ 7) :=
              mul_le_mul_of_nonneg_right hg (by positivity)
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ c1 * L ^ ((-3 : ℝ)) * t ^ 6 := by
            have h3 : c1 * (a ^ 4 / y ^ 7) ≤ c1 * L ^ ((-3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hr (le_of_lt hc1pos)
            exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have hYXn : B ^ 2 * a ^ 4 / (n : ℝ) ≤ c1 * L ^ ((-3 : ℝ)) := by
      have h := hYX_gen (n : ℝ) yn 1 hnn hyn_pos ha_le_yn hf
      simpa using h
    have hYXm : B ^ 2 * a ^ 4 * |delta| ^ 6 / (m : ℝ) ≤ c1 * L ^ ((-3 : ℝ)) * |delta| ^ 6 :=
      hYX_gen (m : ℝ) ym |delta| hmm hym_pos ha_le_ym hg
    have hd_inv : |delta| ^ ((-1 : ℝ)) * |delta| = 1 := by
      have h1 : |delta| ^ ((-1 : ℝ)) * |delta| ^ (1 : ℝ) = 1 := by
        rw [← Real.rpow_add hdeltapos ((-1 : ℝ)) 1,
          show (-1 : ℝ) + 1 = 0 from by norm_num, Real.rpow_zero]
      rwa [Real.rpow_one] at h1
    have hZval_gen : ∀ t : ℝ, 0 < t →
        (c1 * L ^ ((-3 : ℝ)) * t ^ 6) ^ ((-1 : ℝ) / 6)
          = c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) * t ^ ((-1 : ℝ)) := by
      intro t ht
      have hd6 : (t ^ 6) ^ ((-1 : ℝ) / 6) = t ^ ((-1 : ℝ)) := by
        rw [← Real.rpow_natCast t 6, ← Real.rpow_mul (le_of_lt ht) (((6 : ℕ)) : ℝ) ((-1 : ℝ) / 6),
          show (((6 : ℕ)) : ℝ) * ((-1 : ℝ) / 6) = (-1 : ℝ) from by norm_num]
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ c1 * L ^ ((-3 : ℝ))) (by positivity : (0 : ℝ) ≤ t ^ 6),
        Real.mul_rpow (le_of_lt hc1pos) (by positivity : (0 : ℝ) ≤ L ^ ((-3 : ℝ))),
        hLneg, hd6]
    have h4 : 12 * K1 * c1 ^ ((1 : ℝ) / 3) ≤ L := by linarith [hd]
    have h5 : 96 * K1 ^ 2 * Cvar * c1 ^ ((2 : ℝ) / 3) ≤ L ^ 3 := by
      have h96pos : (0 : ℝ) < 96 * Cvar := by linarith [hCvar_pos]
      have hstep : 96 * Cvar * (K1 ^ 2 * c1 ^ ((2 : ℝ) / 3)) ≤ 96 * Cvar * (L ^ 3 / (96 * Cvar)) :=
        mul_le_mul_of_nonneg_left he (le_of_lt h96pos)
      have hsimp : 96 * Cvar * (L ^ 3 / (96 * Cvar)) = L ^ 3 := by field_simp
      linarith [hstep, hsimp]
    have hgen_n := statopia_math_node_1914057860_9bbc8370 a L K1 c1 Cvar B (n : ℝ) yn 1 m1
      ha_pos hLpos hK1pos hc1pos hCvar_pos hnn hyn_pos (by norm_num) hB hm1ge1 hc1le1
      hL_le_a ha_le_yn h4 h5 hceq hf
    simp only [] at hgen_n
    obtain ⟨h1n, h2n, h3n⟩ := hgen_n
    have hgen_m := statopia_math_node_1914057860_9bbc8370 a L K1 c1 Cvar B (m : ℝ) ym |delta| m1
      ha_pos hLpos hK1pos hc1pos hCvar_pos hmm hym_pos hdeltapos hB hm1ge1 hc1le1
      hL_le_a ha_le_ym h4 h5 hceq hg
    simp only [] at hgen_m
    obtain ⟨h1m, h2m, h3m⟩ := hgen_m
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hYpos : 0 < B ^ 2 * a ^ 4 / (n : ℝ) := by positivity
      have hZn : (c1 * L ^ ((-3 : ℝ))) ^ ((-1 : ℝ) / 6) = c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) := by
        rw [Real.mul_rpow (le_of_lt hc1pos) (by positivity), hLneg]
      have hmono : (c1 * L ^ ((-3 : ℝ))) ^ ((-1 : ℝ) / 6)
          ≤ (B ^ 2 * a ^ 4 / (n : ℝ)) ^ ((-1 : ℝ) / 6) :=
        Real.rpow_le_rpow_of_nonpos hYpos hYXn (by norm_num)
      have hfin : 2 ≤ K1 * (c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2)) := by
        have h1 : K1 * (c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2)) = 2 * m1 := by
          rw [← hceq]
          ring
        linarith [hm1ge1, h1]
      calc 2 ≤ K1 * (c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2)) := hfin
        _ = K1 * (c1 * L ^ ((-3 : ℝ))) ^ ((-1 : ℝ) / 6) := by rw [hZn]
        _ ≤ K1 * (B ^ 2 * a ^ 4 / (n : ℝ)) ^ ((-1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left hmono (le_of_lt hK1pos)
    · have hYpos : 0 < B ^ 2 * a ^ 4 * |delta| ^ 6 / (m : ℝ) := by positivity
      have hmono : (c1 * L ^ ((-3 : ℝ)) * |delta| ^ 6) ^ ((-1 : ℝ) / 6)
          ≤ (B ^ 2 * a ^ 4 * |delta| ^ 6 / (m : ℝ)) ^ ((-1 : ℝ) / 6) :=
        Real.rpow_le_rpow_of_nonpos hYpos hYXm (by norm_num)
      have hfin : 2 ≤ K1 * (c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) * |delta| ^ ((-1 : ℝ))) := by
        have h1 : K1 * (c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) * |delta| ^ ((-1 : ℝ)))
            = 2 * m1 * |delta| ^ ((-1 : ℝ)) := by
          rw [← hceq]
          ring
        have h2 : (1 : ℝ) ≤ m1 * |delta| ^ ((-1 : ℝ)) := by
          calc (1 : ℝ) = |delta| * |delta| ^ ((-1 : ℝ)) := by
                rw [mul_comm]; exact hd_inv.symm
            _ ≤ m1 * |delta| ^ ((-1 : ℝ)) :=
                mul_le_mul_of_nonneg_right hdelta_le (by positivity)
        have h3 : (2 : ℝ) ≤ 2 * (m1 * |delta| ^ ((-1 : ℝ))) := by linarith
        linarith [h1, h3]
      calc 2 ≤ K1 * (c1 ^ ((-1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) * |delta| ^ ((-1 : ℝ))) := hfin
        _ = K1 * (c1 * L ^ ((-3 : ℝ)) * |delta| ^ 6) ^ ((-1 : ℝ) / 6) := by
            rw [hZval_gen |delta| hdeltapos]
        _ ≤ K1 * (B ^ 2 * a ^ 4 * |delta| ^ 6 / (m : ℝ)) ^ ((-1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left hmono (le_of_lt hK1pos)
    · simpa using h1n
    · simpa using h1m
    · simpa using h2n
    · simpa using h2m
    · simpa using h3n
    · simpa using h3m
  /- @proof-region region.target-node.session.7462d8f5babac5a1 end -/

end Statlib.Imported

