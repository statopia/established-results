import Statlib.StatFoundation.BasicAnalysis.SpectralEntropy
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
theorem statopia_math_node_2243148282_1fc9761b : ∀ (alpha CD T Ch Cw : ℝ)
    (halpha : 15 < alpha) (hCD : 0 < CD) (hT : 0 < T)
    (hCh : 0 ≤ Ch) (hCw : 0 ≤ Cw),
    ∃ M : ℕ,
      ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) (hM : M ≤ m)
        (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
        (hsparse : Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p),
        Ch * (2 / Real.sqrt (m : ℝ) *
              Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))) +
            Real.rpow
                (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) /
                  Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) *
              Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3) +
            (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) /
                Real.sqrt ((m : ℝ) * p)) *
              (CD * Real.log ((m : ℝ) * (n : ℝ)))) +
          Cw * (Real.sqrt (m : ℝ))⁻¹ ≤ deltaM m := by
  /- @proof-region region.target-node.session.b779d767dd4e3e3f begin -/
  intro alpha CD T Ch Cw halpha hCD hT hCh hCw
  have e1 : ∀ᶠ m : ℕ in Filter.atTop, ∀ (n : ℕ), 1 ≤ n → n ≤ m → ∀ (p : ℝ), 0 < p → p ≤ 1 →
      Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
      Ch * (Real.log (m : ℝ) * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))))) ≤ 1 / 8 := by
    have halg : ∀ (m n : ℕ) (p : ℝ), 3 ≤ m → 1 ≤ n → n ≤ m →
        Real.log (m : ℝ) * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))))
          ≤ 2 * Real.sqrt (2 * CD) *
            ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ)) := by
      intro m n p hm3 hn hnm
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hL0 : 0 < Real.log (m : ℝ) := Real.log_pos hm1
      have hcoef : (0 : ℝ) ≤ 2 / Real.sqrt (m : ℝ) := by positivity
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hLln : Real.log ((m : ℝ) * (n : ℝ)) = Real.log (m : ℝ) + Real.log (n : ℝ) :=
        Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)
      have hlogn : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hn0 hnm'
      have hLl : Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * Real.log (m : ℝ) := by rw [hLln]; linarith
      have hCDl : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * CD * Real.log (m : ℝ) := by nlinarith
      have hsq1 : Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))) ≤
          Real.sqrt (2 * CD) * Real.sqrt (Real.log (m : ℝ)) := by
        refine le_trans (Real.sqrt_le_sqrt hCDl) ?_
        rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * CD)]
      have hLs : Real.log (m : ℝ) * Real.sqrt (Real.log (m : ℝ)) =
          (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) := by
        have h1 : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) =
            (Real.log (m : ℝ)) ^ (1 + (1 : ℝ) / 2) := by norm_num
        rw [h1, Real.rpow_add hL0, Real.rpow_one, Real.sqrt_eq_rpow]
      have hle : 2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ)))
          ≤ 2 / Real.sqrt (m : ℝ) * (Real.sqrt (2 * CD) * Real.sqrt (Real.log (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hsq1 hcoef
      calc Real.log (m : ℝ) * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))))
          ≤ Real.log (m : ℝ) * (2 / Real.sqrt (m : ℝ) * (Real.sqrt (2 * CD) * Real.sqrt (Real.log (m : ℝ)))) :=
            mul_le_mul_of_nonneg_left hle hL0.le
        _ = 2 * Real.sqrt (2 * CD) *
              (Real.log (m : ℝ) * Real.sqrt (Real.log (m : ℝ)) / Real.sqrt (m : ℝ)) := by ring
        _ = 2 * Real.sqrt (2 * CD) *
              ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ)) := by rw [hLs]
    have hbase3 : ∀ᶠ m : ℕ in Filter.atTop, 3 ≤ m := Filter.eventually_atTop.2 ⟨3, fun b hb => hb⟩
    have hcube : ∀ᶠ m : ℕ in Filter.atTop,
        (Real.log (m : ℝ)) ^ ((3 : ℝ)) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) := by
      have h0 : (fun x : ℝ => Real.log x ^ ((3 : ℝ))) =o[Filter.atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2)) :=
        isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 2) (3 : ℝ) (by norm_num)
      have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ ((3 : ℝ))‖ ≤ ‖x ^ ((1 : ℝ) / 2)‖ := h0.eventuallyLE
      have h2 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩
      have h3 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ ((3 : ℝ)) ≤ x ^ ((1 : ℝ) / 2) := by
        refine (h2.and h1).mono ?_
        rintro x ⟨hx1, hx⟩
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
          abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)] at hx
        exact hx
      exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h3
    have hq : ∀ᶠ m : ℕ in Filter.atTop,
        (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
      refine (hcube.and hbase3).mono ?_
      rintro m ⟨hm, hm3⟩
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hL0 : (0 : ℝ) ≤ Real.log (m : ℝ) := (Real.log_pos hm1).le
      calc (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2)
          = ((Real.log (m : ℝ)) ^ ((3 : ℝ))) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_mul hL0]; norm_num
        _ ≤ ((m : ℝ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hL0 ((3 : ℝ))) hm (by norm_num)
        _ = (m : ℝ) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_mul (le_of_lt hm0)]; norm_num
    have hbig : ∀ᶠ m : ℕ in Filter.atTop,
        (2 * Real.sqrt (2 * CD)) / (1 / (8 * (Ch + 1))) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
      have htend : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 4)) Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
      exact Filter.tendsto_atTop.1 htend ((2 * Real.sqrt (2 * CD)) / (1 / (8 * (Ch + 1))))
    refine (hq.and (hbig.and hbase3)).mono ?_
    rintro m ⟨hqm, hbigm, hm3⟩
    have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hDpos : (0 : ℝ) < 2 * Real.sqrt (2 * CD) := by positivity
    have hKpos : (0 : ℝ) < (2 * Real.sqrt (2 * CD)) / (1 / (8 * (Ch + 1))) := by positivity
    have hm4pos : (0 : ℝ) < (m : ℝ) ^ ((1 : ℝ) / 4) := lt_of_lt_of_le hKpos hbigm
    have hD4 : (m : ℝ) ^ ((1 : ℝ) / 2) = ((m : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
      rw [show ((1 : ℝ) / 2) = (1 : ℝ) / 4 + (1 : ℝ) / 4 from by norm_num, Real.rpow_add hm0]
      ring
    have hstep1 : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ) ≤
        1 / (m : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, hD4, div_le_div_iff₀ (pow_pos hm4pos 2) hm4pos]
      have hkey : (Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) * (m : ℝ) ^ ((1 : ℝ) / 4) ≤
          (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hqm hm4pos.le
      nlinarith [hkey, pow_pos hm4pos 2]
    have hstep2 : 1 / (m : ℝ) ^ ((1 : ℝ) / 4) ≤
        (1 / (8 * (Ch + 1))) / (2 * Real.sqrt (2 * CD)) := by
      have h2 : (1 : ℝ) / ((2 * Real.sqrt (2 * CD)) / (1 / (8 * (Ch + 1)))) =
          (1 / (8 * (Ch + 1))) / (2 * Real.sqrt (2 * CD)) := by field_simp
      rw [← h2]
      rw [div_le_div_iff₀ hm4pos hKpos]
      linarith
    have h3 : 2 * Real.sqrt (2 * CD) * (1 / (m : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / (8 * (Ch + 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hstep2 hDpos.le
      have h2 : 2 * Real.sqrt (2 * CD) * ((1 / (8 * (Ch + 1))) / (2 * Real.sqrt (2 * CD))) =
          1 / (8 * (Ch + 1)) := by field_simp
      rwa [h2] at h1
    have h5 : Ch * (1 / (8 * (Ch + 1))) ≤ 1 / 8 := by
      have hDen : (0 : ℝ) < 8 * (Ch + 1) := by positivity
      have heq : Ch * (1 / (8 * (Ch + 1))) = Ch / (8 * (Ch + 1)) := by ring
      rw [heq, div_le_iff₀ hDen]
      linarith
    have h4 : Ch * (2 * Real.sqrt (2 * CD) *
        ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ))) ≤ 1 / 8 := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hCh) h5
      calc 2 * Real.sqrt (2 * CD) * ((Real.log (m : ℝ)) ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ))
          ≤ 2 * Real.sqrt (2 * CD) * (1 / (m : ℝ) ^ ((1 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left hstep1 hDpos.le
        _ ≤ 1 / (8 * (Ch + 1)) := h3
    intro n hn' hnm' p hp0 hp1 hsparse
    exact le_trans (mul_le_mul_of_nonneg_left (halg m n p hm3 hn' hnm') hCh) h4
  have e2 : ∀ᶠ m : ℕ in Filter.atTop, ∀ (n : ℕ), 1 ≤ n → n ≤ m → ∀ (p : ℝ), 0 < p → p ≤ 1 →
      Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
      Ch * (Real.log (m : ℝ) * (Real.rpow (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) *
        Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3))) ≤ 1 / 8 := by
    have hlogtop : Filter.Tendsto (fun m : ℕ => Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hL1ev : ∀ᶠ m : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (m : ℝ) :=
      Filter.tendsto_atTop.1 hlogtop 1
    have hden7 : ∀ (m : ℕ) (p : ℝ), 3 ≤ m → (1 : ℝ) ≤ Real.log (m : ℝ) →
        Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
        (Real.log (m : ℝ)) ^ 7 ≤ Real.sqrt ((m : ℝ) * p) := by
      intro m p hm3 hL1 hsp
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
      have hL0 : (0 : ℝ) < Real.log (m : ℝ) := by linarith
      have h14 : (Real.log (m : ℝ)) ^ 14 ≤ (Real.log (m : ℝ)) ^ alpha := by
        have h1 : (Real.log (m : ℝ)) ^ (14 : ℝ) ≤ (Real.log (m : ℝ)) ^ alpha :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : (14 : ℝ) ≤ alpha)
        rwa [Real.rpow_ofNat] at h1
      have h14' : (Real.log (m : ℝ)) ^ 14 ≤ (m : ℝ) * p := le_trans h14 hsp
      calc (Real.log (m : ℝ)) ^ 7 = Real.sqrt ((Real.log (m : ℝ)) ^ 14) := by
            rw [show (Real.log (m : ℝ)) ^ 14 = ((Real.log (m : ℝ)) ^ 7) ^ 2 by ring,
              Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt ((m : ℝ) * p) := Real.sqrt_le_sqrt h14'
    have halg2 : ∀ (m n : ℕ) (p : ℝ), 3 ≤ m → 1 ≤ n → n ≤ m → (1 : ℝ) ≤ Real.log (m : ℝ) →
        0 < p → (Real.log (m : ℝ)) ^ 7 ≤ Real.sqrt ((m : ℝ) * p) →
        Real.log (m : ℝ) *
            ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ^ ((1 : ℝ) / 3) *
              (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ) / 3)) ≤
          (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) * (Real.log (m : ℝ)) ^ (-(1 : ℝ) / 3) := by
      intro m n p hm3 hn hnm hL1 hp0 hden
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hL0 : (0 : ℝ) < Real.log (m : ℝ) := lt_of_lt_of_le zero_lt_one hL1
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hLln : Real.log ((m : ℝ) * (n : ℝ)) = Real.log (m : ℝ) + Real.log (n : ℝ) :=
        Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)
      have hlogn : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hn0 hnm'
      have hLl : Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * Real.log (m : ℝ) := by rw [hLln]; linarith
      have hX : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * CD * Real.log (m : ℝ) := by nlinarith
      have hX0 : (0 : ℝ) ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := by
        have hl0 : (0 : ℝ) ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
          rw [hLln]
          have := Real.log_nonneg hn1
          linarith
        exact mul_nonneg hCD.le hl0
      have hnum : 3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) ≤
          3 * (2 * CD + T) * Real.log (m : ℝ) := by nlinarith
      have hdenpos : (0 : ℝ) < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.2 (by positivity)
      have hR : 3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p) ≤
          3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7 := by
        rw [div_le_div_iff₀ hdenpos (pow_pos hL0 7)]
        exact mul_le_mul hnum hden (le_of_lt (pow_pos hL0 7)) (by positivity)
      have hR0 : (0 : ℝ) ≤
          3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p) := by
        have h1 : (0 : ℝ) ≤ 3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) := by linarith
        exact div_nonneg h1 hdenpos.le
      have hX2 : (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ)) ≤
          (2 * CD * Real.log (m : ℝ)) ^ ((2 : ℝ)) :=
        Real.rpow_le_rpow hX0 hX (by norm_num)
      have hRX : (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
            (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ))
          ≤ (3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7) *
            (2 * CD * Real.log (m : ℝ)) ^ ((2 : ℝ)) := by
        refine le_trans (mul_le_mul_of_nonneg_left hX2 hR0) ?_
        exact mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * CD * Real.log (m : ℝ)) 2)
      have hsimp : (3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7) *
            (2 * CD * Real.log (m : ℝ)) ^ ((2 : ℝ))
          = 12 * CD ^ 2 * (2 * CD + T) / (Real.log (m : ℝ)) ^ 4 := by
        rw [Real.rpow_ofNat]
        field_simp
        ring
      have hstep1 : ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
            (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ))) ^ ((1 : ℝ) / 3)
          = (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ^ ((1 : ℝ) / 3) *
            (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ) / 3) := by
        rw [Real.mul_rpow hR0 (Real.rpow_nonneg hX0 2)]
        rw [← Real.rpow_mul hX0]
        rw [show (2 : ℝ) * ((1 : ℝ) / 3) = (2 : ℝ) / 3 from by norm_num]
      have hdiv : (12 * CD ^ 2 * (2 * CD + T) / (Real.log (m : ℝ)) ^ 4) ^ ((1 : ℝ) / 3)
          = (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) *
            (Real.log (m : ℝ)) ^ (-(4 : ℝ) / 3) := by
        rw [Statlib.StatFoundation.BasicAnalysis.div_rpow_eq_mul_rpow_neg (12 * CD ^ 2 * (2 * CD + T))
          ((Real.log (m : ℝ)) ^ 4) 3 (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_ofNat]
        rw [← Real.rpow_mul hL0.le]
        rw [show (4 * (-((1 : ℝ) / 3))) = -(4 : ℝ) / 3 from by norm_num]
      have hLmul : Real.log (m : ℝ) *
            ((12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) * (Real.log (m : ℝ)) ^ (-(4 : ℝ) / 3))
          = (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) *
            (Real.log (m : ℝ)) ^ (-(1 : ℝ) / 3) := by
        rw [show (-(1 : ℝ) / 3) = 1 + (-(4 : ℝ) / 3) from by norm_num, Real.rpow_add hL0,
          Real.rpow_one]
        ring
      calc Real.log (m : ℝ) *
            ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ^ ((1 : ℝ) / 3) *
              (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ) / 3))
          = Real.log (m : ℝ) *
            (((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
              (CD * Real.log ((m : ℝ) * (n : ℝ))) ^ ((2 : ℝ))) ^ ((1 : ℝ) / 3)) := by rw [hstep1]
        _ ≤ Real.log (m : ℝ) *
            (((3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7) *
              (2 * CD * Real.log (m : ℝ)) ^ ((2 : ℝ))) ^ ((1 : ℝ) / 3)) := by
            apply mul_le_mul_of_nonneg_left _ hL0.le
            exact Real.rpow_le_rpow (by positivity) hRX (by norm_num)
        _ = Real.log (m : ℝ) *
            ((12 * CD ^ 2 * (2 * CD + T) / (Real.log (m : ℝ)) ^ 4) ^ ((1 : ℝ) / 3)) := by rw [hsimp]
        _ = Real.log (m : ℝ) *
            ((12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) *
              (Real.log (m : ℝ)) ^ (-(4 : ℝ) / 3)) := by rw [hdiv]
        _ = (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) *
            (Real.log (m : ℝ)) ^ (-(1 : ℝ) / 3) := hLmul
    have hbig3 : ∀ᶠ m : ℕ in Filter.atTop,
        ((12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3)) / (1 / (8 * (Ch + 1))) ≤
          (Real.log (m : ℝ)) ^ ((1 : ℝ) / 3) := by
      have htend : Filter.Tendsto (fun m : ℕ => (Real.log (m : ℝ)) ^ ((1 : ℝ) / 3))
          Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)).comp hlogtop
      exact Filter.tendsto_atTop.1 htend _
    have hbase2 : ∀ᶠ m : ℕ in Filter.atTop, 3 ≤ m := Filter.eventually_atTop.2 ⟨3, fun b hb => hb⟩
    refine (hbig3.and (hL1ev.and hbase2)).mono ?_
    rintro m ⟨hb3, hL1, hm3⟩ n hn hnm p hp0 hp1 hsp
    have hL0 : (0 : ℝ) < Real.log (m : ℝ) := lt_of_lt_of_le zero_lt_one hL1
    have hεpos : (0 : ℝ) < 1 / (8 * (Ch + 1)) := by positivity
    have hkey : (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) ≤
        (1 / (8 * (Ch + 1))) * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 3) := by
      have h1 := mul_le_mul_of_nonneg_left hb3 hεpos.le
      have h2 : (1 / (8 * (Ch + 1))) * (((12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3)) /
          (1 / (8 * (Ch + 1)))) = (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) := by field_simp
      rwa [h2] at h1
    have heq1 : (Real.log (m : ℝ)) ^ (-(1 : ℝ) / 3) = ((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3))⁻¹ := by
      rw [show (-(1 : ℝ) / 3) = (1 : ℝ) / 3 * (-1) from by norm_num, Real.rpow_mul hL0.le,
        Real.rpow_neg_one]
    have hstepA : (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) *
        (Real.log (m : ℝ)) ^ (-(1 : ℝ) / 3) ≤ 1 / (8 * (Ch + 1)) := by
      rw [heq1]
      rcases eq_or_lt_of_le (Real.rpow_nonneg hL0.le ((1 : ℝ) / 3)) with hx | hx
      · rw [← hx, inv_zero, mul_zero]
        exact hεpos.le
      · calc (12 * CD ^ 2 * (2 * CD + T)) ^ ((1 : ℝ) / 3) * ((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3))⁻¹
            ≤ ((1 / (8 * (Ch + 1))) * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 3)) *
              ((Real.log (m : ℝ)) ^ ((1 : ℝ) / 3))⁻¹ :=
              mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = 1 / (8 * (Ch + 1)) := by
              rw [mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
    have hfin2 : Ch * (1 / (8 * (Ch + 1))) ≤ 1 / 8 := by
      have hDen : (0 : ℝ) < 8 * (Ch + 1) := by positivity
      have heq : Ch * (1 / (8 * (Ch + 1))) = Ch / (8 * (Ch + 1)) := by ring
      rw [heq, div_le_iff₀ hDen]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left
      (le_trans (halg2 m n p hm3 hn hnm hL1 hp0 (hden7 m p hm3 hL1 hsp)) hstepA) hCh) hfin2
  have e3 : ∀ᶠ m : ℕ in Filter.atTop, ∀ (n : ℕ), 1 ≤ n → n ≤ m → ∀ (p : ℝ), 0 < p → p ≤ 1 →
      Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
      Ch * (Real.log (m : ℝ) * ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
        (CD * Real.log ((m : ℝ) * (n : ℝ))))) ≤ 1 / 8 := by
    have hlogtop : Filter.Tendsto (fun m : ℕ => Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hL1ev : ∀ᶠ m : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (m : ℝ) :=
      Filter.tendsto_atTop.1 hlogtop 1
    have hden7 : ∀ (m : ℕ) (p : ℝ), 3 ≤ m → (1 : ℝ) ≤ Real.log (m : ℝ) →
        Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
        (Real.log (m : ℝ)) ^ 7 ≤ Real.sqrt ((m : ℝ) * p) := by
      intro m p hm3 hL1 hsp
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
      have hL0 : (0 : ℝ) < Real.log (m : ℝ) := by linarith
      have h14 : (Real.log (m : ℝ)) ^ 14 ≤ (Real.log (m : ℝ)) ^ alpha := by
        have h1 : (Real.log (m : ℝ)) ^ (14 : ℝ) ≤ (Real.log (m : ℝ)) ^ alpha :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : (14 : ℝ) ≤ alpha)
        rwa [Real.rpow_ofNat] at h1
      have h14' : (Real.log (m : ℝ)) ^ 14 ≤ (m : ℝ) * p := le_trans h14 hsp
      calc (Real.log (m : ℝ)) ^ 7 = Real.sqrt ((Real.log (m : ℝ)) ^ 14) := by
            rw [show (Real.log (m : ℝ)) ^ 14 = ((Real.log (m : ℝ)) ^ 7) ^ 2 by ring,
              Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt ((m : ℝ) * p) := Real.sqrt_le_sqrt h14'
    have hbig4 : ∀ᶠ m : ℕ in Filter.atTop,
        48 * CD * (2 * CD + T) * (Ch + 1) ≤ (Real.log (m : ℝ)) ^ 4 := by
      have hKpos : (0 : ℝ) < 48 * CD * (2 * CD + T) * (Ch + 1) := by positivity
      have hlow : ∀ᶠ m : ℕ in Filter.atTop,
          Real.rpow (48 * CD * (2 * CD + T) * (Ch + 1)) ((1 : ℝ) / 4) ≤ Real.log (m : ℝ) :=
        Filter.tendsto_atTop.1 hlogtop (Real.rpow (48 * CD * (2 * CD + T) * (Ch + 1)) ((1 : ℝ) / 4))
      refine hlow.mono ?_
      intro m hm
      have h1 : ((48 * CD * (2 * CD + T) * (Ch + 1)) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) ≤
          (Real.log (m : ℝ)) ^ (4 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hKpos.le _) hm (by norm_num)
      have h2 : ((48 * CD * (2 * CD + T) * (Ch + 1)) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) =
          48 * CD * (2 * CD + T) * (Ch + 1) := by
        rw [← Real.rpow_mul hKpos.le]
        rw [show ((1 : ℝ) / 4 * 4) = 1 by norm_num, Real.rpow_one]
      have h3 : (Real.log (m : ℝ)) ^ (4 : ℝ) = (Real.log (m : ℝ)) ^ 4 := by
        rw [Real.rpow_ofNat]
      rwa [h2, h3] at h1
    have halg3 : ∀ (m n : ℕ) (p : ℝ), 3 ≤ m → 1 ≤ n → n ≤ m → (1 : ℝ) ≤ Real.log (m : ℝ) →
        0 < p → (Real.log (m : ℝ)) ^ 7 ≤ Real.sqrt ((m : ℝ) * p) →
        Real.log (m : ℝ) *
            ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
              (CD * Real.log ((m : ℝ) * (n : ℝ)))) ≤
          6 * CD * (2 * CD + T) / (Real.log (m : ℝ)) ^ 4 := by
      intro m n p hm3 hn hnm hL1 hp0 hden
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hL0 : (0 : ℝ) < Real.log (m : ℝ) := by linarith
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hLln : Real.log ((m : ℝ) * (n : ℝ)) = Real.log (m : ℝ) + Real.log (n : ℝ) :=
        Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)
      have hlogn : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hn0 hnm'
      have hLl : Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * Real.log (m : ℝ) := by rw [hLln]; linarith
      have hX : CD * Real.log ((m : ℝ) * (n : ℝ)) ≤ 2 * CD * Real.log (m : ℝ) := by nlinarith
      have hX0 : (0 : ℝ) ≤ CD * Real.log ((m : ℝ) * (n : ℝ)) := by
        have hl0 : (0 : ℝ) ≤ Real.log ((m : ℝ) * (n : ℝ)) := by
          rw [hLln]
          have := Real.log_nonneg hn1
          linarith
        exact mul_nonneg hCD.le hl0
      have hnum : 3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) ≤
          3 * (2 * CD + T) * Real.log (m : ℝ) := by nlinarith
      have hdenpos : (0 : ℝ) < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.2 (by positivity)
      have hR : 3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p) ≤
          3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7 := by
        rw [div_le_div_iff₀ hdenpos (pow_pos hL0 7)]
        exact mul_le_mul hnum hden (le_of_lt (pow_pos hL0 7)) (by positivity)
      calc Real.log (m : ℝ) *
            ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
              (CD * Real.log ((m : ℝ) * (n : ℝ))))
          ≤ Real.log (m : ℝ) *
            ((3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7) *
              (CD * Real.log ((m : ℝ) * (n : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ hL0.le
            exact mul_le_mul_of_nonneg_right hR hX0
        _ ≤ Real.log (m : ℝ) *
            ((3 * (2 * CD + T) * Real.log (m : ℝ) / (Real.log (m : ℝ)) ^ 7) *
              (2 * CD * Real.log (m : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hL0.le
            exact mul_le_mul_of_nonneg_left hX (by positivity)
        _ = 6 * CD * (2 * CD + T) / (Real.log (m : ℝ)) ^ 4 := by
            field_simp
            ring
    have hbase : ∀ᶠ m : ℕ in Filter.atTop, 3 ≤ m := Filter.eventually_atTop.2 ⟨3, fun b hb => hb⟩
    refine (hbig4.and (hL1ev.and hbase)).mono ?_
    rintro m ⟨hb4, hL1, hm3⟩ n hn hnm p hp0 hp1 hsp
    have hL0 : (0 : ℝ) < Real.log (m : ℝ) := lt_of_lt_of_le zero_lt_one hL1
    have hL4pos : (0 : ℝ) < (Real.log (m : ℝ)) ^ 4 := by positivity
    have hstep : 6 * CD * (2 * CD + T) / (Real.log (m : ℝ)) ^ 4 ≤ 1 / (8 * (Ch + 1)) := by
      rw [div_le_iff₀ hL4pos]
      have hmul := mul_le_mul_of_nonneg_left hb4 (by positivity : (0 : ℝ) ≤ 1 / (8 * (Ch + 1)))
      have heq : (1 / (8 * (Ch + 1))) * (48 * CD * (2 * CD + T) * (Ch + 1)) =
          6 * CD * (2 * CD + T) := by field_simp <;> norm_num
      rwa [heq] at hmul
    have hA := halg3 m n p hm3 hn hnm hL1 hp0 (hden7 m p hm3 hL1 hsp)
    have hfin : Ch * (1 / (8 * (Ch + 1))) ≤ 1 / 8 := by
      have hDen : (0 : ℝ) < 8 * (Ch + 1) := by positivity
      have heq : Ch * (1 / (8 * (Ch + 1))) = Ch / (8 * (Ch + 1)) := by ring
      rw [heq, div_le_iff₀ hDen]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left (le_trans hA hstep) hCh) hfin
  have e4 : ∀ᶠ m : ℕ in Filter.atTop, ∀ (n : ℕ), 1 ≤ n → n ≤ m → ∀ (p : ℝ), 0 < p → p ≤ 1 →
      Real.rpow (Real.log (m : ℝ)) alpha ≤ (m : ℝ) * p →
      Cw * (Real.log (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹) ≤ 1 / 8 := by
    have hlsq : ∀ᶠ m : ℕ in Filter.atTop, (Real.log (m : ℝ)) ^ 2 ≤ Real.sqrt (m : ℝ) := by
      have h0 : (fun x : ℝ => Real.log x ^ ((2 : ℝ))) =o[Filter.atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2)) :=
        isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 2) (2 : ℝ) (by norm_num)
      have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ ((2 : ℝ))‖ ≤ ‖x ^ ((1 : ℝ) / 2)‖ := h0.eventuallyLE
      have h2 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩
      have h3 : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ 2 ≤ Real.sqrt x := by
        refine (h2.and h1).mono ?_
        rintro x ⟨hx1, hx⟩
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
          abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)] at hx
        rw [Real.rpow_ofNat, ← Real.sqrt_eq_rpow] at hx
        exact hx
      exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h3
    have hbiglog : ∀ᶠ m : ℕ in Filter.atTop, 8 * (Cw + 1) ≤ Real.log (m : ℝ) :=
      Filter.tendsto_atTop.1 (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))) (8 * (Cw + 1))
    have hbase4 : ∀ᶠ m : ℕ in Filter.atTop, 3 ≤ m := Filter.eventually_atTop.2 ⟨3, fun b hb => hb⟩
    refine (hlsq.and (hbiglog.and hbase4)).mono ?_
    rintro m ⟨hsm, hlg, hm3⟩ n hn hnm p hp0 hp1 hsparse
    have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hL0 : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    have hsqm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
    have hstep : Real.log (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹ ≤ 1 / (8 * (Cw + 1)) := by
      have h1 : Real.log (m : ℝ) / Real.sqrt (m : ℝ) ≤ 1 / Real.log (m : ℝ) := by
        rw [div_le_div_iff₀ hsqm hL0]
        nlinarith [hsm]
      have h2 : 1 / Real.log (m : ℝ) ≤ 1 / (8 * (Cw + 1)) := by
        rw [div_le_div_iff₀ hL0 (by positivity : (0 : ℝ) < 8 * (Cw + 1))]
        linarith
      calc Real.log (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹ = Real.log (m : ℝ) / Real.sqrt (m : ℝ) := by ring
        _ ≤ 1 / Real.log (m : ℝ) := h1
        _ ≤ 1 / (8 * (Cw + 1)) := h2
    have hfin : Cw * (1 / (8 * (Cw + 1))) ≤ 1 / 8 := by
      have hDen : (0 : ℝ) < 8 * (Cw + 1) := by positivity
      have heq : Cw * (1 / (8 * (Cw + 1))) = Cw / (8 * (Cw + 1)) := by ring
      rw [heq, div_le_iff₀ hDen]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left hstep hCw) hfin
  have h3 : ∀ᶠ m : ℕ in Filter.atTop, 3 ≤ m := Filter.eventually_atTop.2 ⟨3, fun b hb => hb⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (h3.and (e1.and (e2.and (e3.and e4))))
  refine ⟨M, ?_⟩
  intro m n hm hn hnm hMle p hp0 hp1 hsparse
  obtain ⟨hm3, hB1, hB2, hB3, hB4⟩ := hM m hMle
  have b1 := hB1 n hn hnm p hp0 hp1 hsparse
  have b2 := hB2 n hn hnm p hp0 hp1 hsparse
  have b3 := hB3 n hn hnm p hp0 hp1 hsparse
  have b4 := hB4 n hn hnm p hp0 hp1 hsparse
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hLpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have key : Real.log (m : ℝ) * (Ch * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))) +
        Real.rpow (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) *
          Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3) +
        (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
          (CD * Real.log ((m : ℝ) * (n : ℝ)))) + Cw * (Real.sqrt (m : ℝ))⁻¹) ≤ 1 / 2 := by
    have hsum : Ch * (Real.log (m : ℝ) * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))))) +
        Ch * (Real.log (m : ℝ) * (Real.rpow (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) * Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3))) +
        Ch * (Real.log (m : ℝ) * ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) * (CD * Real.log ((m : ℝ) * (n : ℝ))))) +
        Cw * (Real.log (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹) ≤ 1 / 2 := by linarith
    calc Real.log (m : ℝ) * (Ch * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))) +
          Real.rpow (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) *
            Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3) +
          (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
            (CD * Real.log ((m : ℝ) * (n : ℝ)))) + Cw * (Real.sqrt (m : ℝ))⁻¹)
        = Ch * (Real.log (m : ℝ) * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))))) +
          Ch * (Real.log (m : ℝ) * (Real.rpow (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) * Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3))) +
          Ch * (Real.log (m : ℝ) * ((3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) * (CD * Real.log ((m : ℝ) * (n : ℝ))))) +
          Cw * (Real.log (m : ℝ) * (Real.sqrt (m : ℝ))⁻¹) := by ring
      _ ≤ 1 / 2 := hsum
  rw [deltaM]
  have hmul : Real.log (m : ℝ) * (Ch * (2 / Real.sqrt (m : ℝ) * Real.sqrt (CD * Real.log ((m : ℝ) * (n : ℝ))) +
        Real.rpow (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) ((1 : ℝ) / 3) *
          Real.rpow (CD * Real.log ((m : ℝ) * (n : ℝ))) ((2 : ℝ) / 3) +
        (3 * (CD * Real.log ((m : ℝ) * (n : ℝ)) + T) / Real.sqrt ((m : ℝ) * p)) *
          (CD * Real.log ((m : ℝ) * (n : ℝ)))) + Cw * (Real.sqrt (m : ℝ))⁻¹) ≤ Real.log (m : ℝ) * (Real.log (m : ℝ))⁻¹ := by
    rw [mul_inv_cancel₀ hLpos.ne']
    linarith
  exact le_of_mul_le_mul_left hmul hLpos
  /- @proof-region region.target-node.session.b779d767dd4e3e3f end -/

end Statlib.Imported

