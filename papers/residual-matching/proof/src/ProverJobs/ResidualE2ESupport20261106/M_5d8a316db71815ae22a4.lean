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
theorem statopia_math_node_1358304067_3215dc50 : ∀ (C0 c0 D0 : ℝ) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hD0 : 0 < D0),
    ∃ M : ℕ, ∀ (m : ℕ), M ≤ m →
      (Real.rpow (m : ℝ) (-(2 / 3)) ≤ 1 / (2 * Real.log (m : ℝ)) ∧
        1 / (2 * Real.log (m : ℝ)) ≤ 1 / 4 ∧
        C0 * (m : ℝ) ^ 2 *
            Real.exp (-(c0 * (m : ℝ) * Real.rpow (1 / (2 * Real.log (m : ℝ))) (3 / 2))) ≤
          Real.rpow (m : ℝ) (-(D0 + 4)) / 2) := by
  /- @proof-region region.target-node.session.92b37c5bbfce9c6c begin -/
  intro C0 c0 D0 hC0 hc0 hD0
  have h2 : ∀ᶠ m : ℕ in Filter.atTop, 1 / (2 * Real.log (m:ℝ)) ≤ 1 / 4 := by
    have hlog : ∀ᶠ m : ℕ in Filter.atTop, (4:ℝ) ≤ 2 * Real.log (m:ℝ) := by
      have h : ∀ᶠ m : ℕ in Filter.atTop, (2:ℝ) ≤ Real.log (m:ℝ) :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (Filter.eventually_ge_atTop (2:ℝ))
      filter_upwards [h] with m hm
      linarith
    filter_upwards [hlog] with m hm
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * Real.log (m:ℝ)) (by norm_num : (0:ℝ) < 4)]
    linarith
  have h1 : ∀ᶠ m : ℕ in Filter.atTop, Real.rpow (m:ℝ) (-(2/3)) ≤ 1 / (2 * Real.log (m:ℝ)) := by
    have hlo : (fun x : ℝ => Real.log x) =o[Filter.atTop] (fun x : ℝ => x ^ (2/3:ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have htd : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ (2/3:ℝ)) Filter.atTop (nhds 0) :=
      hlo.tendsto_div_nhds_zero
    have hevR : ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.log x ≤ x ^ (2/3:ℝ) := by
      have hlt : ∀ᶠ x : ℝ in Filter.atTop, Real.log x / x ^ (2/3:ℝ) < 1/2 :=
        (tendsto_order.1 htd).2 (1/2) (by norm_num)
      filter_upwards [hlt, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
      have hxpos : (0:ℝ) < x ^ (2/3:ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have hmul := mul_lt_mul_of_pos_right hx hxpos
      rw [div_mul_cancel₀ _ (ne_of_gt hxpos)] at hmul
      linarith
    have hevN : ∀ᶠ m : ℕ in Filter.atTop, 2 * Real.log (m:ℝ) ≤ (m:ℝ) ^ (2/3:ℝ) :=
      hevR.natCast_atTop
    have hposN : ∀ᶠ m : ℕ in Filter.atTop, (0:ℝ) < 2 * Real.log (m:ℝ) := by
      have h : ∀ᶠ m : ℕ in Filter.atTop, (0:ℝ) < Real.log (m:ℝ) :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (Filter.eventually_gt_atTop (0:ℝ))
      filter_upwards [h] with m hm
      linarith
    filter_upwards [hevN, hposN] with m hm hpm
    have hxpos : (0:ℝ) < (m:ℝ) ^ (2/3:ℝ) := lt_of_lt_of_le hpm hm
    have hinv : ((m:ℝ) ^ (2/3:ℝ))⁻¹ ≤ (2 * Real.log (m:ℝ))⁻¹ := by
      rw [inv_le_inv₀ hxpos hpm]
      exact hm
    calc Real.rpow (m:ℝ) (-(2/3)) = ((m:ℝ) ^ (2/3:ℝ))⁻¹ :=
          Real.rpow_neg (by positivity : (0:ℝ) ≤ (m:ℝ)) (2/3)
      _ ≤ (2 * Real.log (m:ℝ))⁻¹ := hinv
      _ = 1 / (2 * Real.log (m:ℝ)) := (one_div _).symm
  have h3 : ∀ᶠ m : ℕ in Filter.atTop,
      C0 * (m:ℝ)^2 * Real.exp (-(c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2)))
        ≤ Real.rpow (m:ℝ) (-(D0+4))/2 := by
    have hkey : ∀ᶠ m : ℕ in Filter.atTop,
        Real.log (Real.rpow (m:ℝ) (D0+6) * (2*C0))
          ≤ c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2) := by
      set d : ℝ := 1/(2*(D0+6)) with hd
      set B : ℝ := d⁻¹ * (2*C0) ^ d * (2:ℝ) ^ (3/2:ℝ) with hB
      have hD6 : (0:ℝ) < D0 + 6 := by linarith
      have hdpos : (0:ℝ) < d := by
        rw [hd]
        exact div_pos one_pos (by linarith)
      have hBpos : (0:ℝ) < B := by
        rw [hB]
        exact mul_pos (mul_pos (inv_pos.mpr hdpos)
          (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 2*C0) d))
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (3/2))
      have hasymR : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ (3/2:ℝ) ≤ (c0/B) * x ^ (1/2:ℝ) := by
        have hlo : (fun x : ℝ => Real.log x ^ (3/2:ℝ)) =o[Filter.atTop] (fun x : ℝ => x ^ (1/2:ℝ)) :=
          isLittleO_log_rpow_rpow_atTop (s := (1/2:ℝ)) (3/2) (by norm_num)
        have htd : Filter.Tendsto (fun x : ℝ => Real.log x ^ (3/2:ℝ) / x ^ (1/2:ℝ)) Filter.atTop (nhds 0) :=
          hlo.tendsto_div_nhds_zero
        have hlt : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ (3/2:ℝ) / x ^ (1/2:ℝ) < c0/B :=
          (tendsto_order.1 htd).2 (c0/B) (div_pos hc0 hBpos)
        filter_upwards [hlt, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
        have hxpos : (0:ℝ) < x ^ (1/2:ℝ) := Real.rpow_pos_of_pos (by linarith) _
        have hmul := mul_lt_mul_of_pos_right hx hxpos
        rw [div_mul_cancel₀ _ (ne_of_gt hxpos)] at hmul
        linarith
      have hasym : ∀ᶠ m : ℕ in Filter.atTop,
          Real.log (m:ℝ) ^ (3/2:ℝ) ≤ (c0/B) * (m:ℝ) ^ (1/2:ℝ) := hasymR.natCast_atTop
      have hlogpos : ∀ᶠ m : ℕ in Filter.atTop, (0:ℝ) < Real.log (m:ℝ) :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (Filter.eventually_gt_atTop (0:ℝ))
      have hm1 : ∀ᶠ m : ℕ in Filter.atTop, (1:ℕ) ≤ m :=
        Filter.eventually_atTop.2 ⟨1, fun m hm => hm⟩
      filter_upwards [hasym, hlogpos, hm1] with m hasy hlogm hm1'
      have hmpos : (0:ℝ) < (m:ℝ) := by
        have h : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1'
        linarith
      have hC2 : (0:ℝ) < 2*C0 := by linarith
      have hArpow : (0:ℝ) < (m:ℝ) ^ (D0+6) := Real.rpow_pos_of_pos hmpos _
      have hYnn : (0:ℝ) ≤ (m:ℝ) ^ (D0+6) * (2*C0) := le_of_lt (mul_pos hArpow hC2)
      have hlogY : Real.log ((m:ℝ) ^ (D0+6) * (2*C0)) ≤ ((m:ℝ) ^ (D0+6) * (2*C0)) ^ d / d :=
        Real.log_le_rpow_div hYnn hdpos
      have hYrpow : ((m:ℝ) ^ (D0+6) * (2*C0)) ^ d = (m:ℝ) ^ (1/2:ℝ) * (2*C0) ^ d := by
        rw [Real.mul_rpow (le_of_lt hArpow) (le_of_lt hC2),
          ← Real.rpow_mul (le_of_lt hmpos) (D0+6) d]
        have hD6d : (D0+6) * d = 1/2 := by
          rw [hd, one_div, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hD6)]
          norm_num
        rw [hD6d]
      have hbound : ((m:ℝ) ^ (D0+6) * (2*C0)) ^ d / d
          ≤ c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2) := by
        have hLpos : (0:ℝ) < 2*Real.log (m:ℝ) := by linarith
        have hXp : (0:ℝ) < (2*Real.log (m:ℝ)) ^ (3/2:ℝ) := Real.rpow_pos_of_pos hLpos _
        have hT1i : (1/(2*Real.log (m:ℝ))) ^ (3/2:ℝ) = 1 / (2*Real.log (m:ℝ)) ^ (3/2:ℝ) := by
          rw [one_div, ← Real.rpow_neg_eq_inv_rpow (2*Real.log (m:ℝ)) (3/2),
            Real.rpow_neg (le_of_lt hLpos) (3/2)]
          exact (one_div _).symm
        have hT1 : Real.rpow (1/(2*Real.log (m:ℝ))) (3/2) = 1 / (2*Real.log (m:ℝ)) ^ (3/2:ℝ) :=
          hT1i
        rw [hYrpow, hT1, mul_one_div, le_div_iff₀ hXp]
        have hLHS : ((m:ℝ) ^ (1/2:ℝ) * (2*C0) ^ d) / d * (2*Real.log (m:ℝ)) ^ (3/2:ℝ)
            = B * ((m:ℝ) ^ (1/2:ℝ) * Real.log (m:ℝ) ^ (3/2:ℝ)) := by
          rw [hB, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hlogm), div_eq_mul_inv]
          ring
        rw [hLHS]
        have hstep : (m:ℝ) ^ (1/2:ℝ) * Real.log (m:ℝ) ^ (3/2:ℝ) ≤ (c0/B) * (m:ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hasy
            (le_of_lt (Real.rpow_pos_of_pos hmpos (1/2:ℝ)))
          have hsq : (m:ℝ) ^ (1/2:ℝ) * (m:ℝ) ^ (1/2:ℝ) = (m:ℝ) := by
            rw [← Real.rpow_add hmpos]
            norm_num
          calc (m:ℝ) ^ (1/2:ℝ) * Real.log (m:ℝ) ^ (3/2:ℝ)
              ≤ (m:ℝ) ^ (1/2:ℝ) * ((c0/B) * (m:ℝ) ^ (1/2:ℝ)) := hmul
            _ = (c0/B) * (m:ℝ) := by
                rw [← mul_assoc, mul_comm ((m:ℝ) ^ (1/2:ℝ)) (c0/B),
                  mul_assoc (c0/B) ((m:ℝ) ^ (1/2:ℝ)) ((m:ℝ) ^ (1/2:ℝ)), hsq]
        calc B * ((m:ℝ) ^ (1/2:ℝ) * Real.log (m:ℝ) ^ (3/2:ℝ))
            ≤ B * ((c0/B) * (m:ℝ)) := mul_le_mul_of_nonneg_left hstep (le_of_lt hBpos)
          _ = c0 * (m:ℝ) := by
              rw [← mul_assoc, mul_comm B (c0/B), div_mul_cancel₀ c0 (ne_of_gt hBpos)]
      exact le_trans hlogY hbound
    filter_upwards [hkey, Filter.eventually_ge_atTop (1:ℕ)] with m hm hm1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      have h : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      linarith
    have hC2 : (0:ℝ) < 2*C0 := by linarith
    have hYpos : (0:ℝ) < Real.rpow (m:ℝ) (D0+6) * (2*C0) :=
      mul_pos (Real.rpow_pos_of_pos hmpos (D0+6)) hC2
    have hexp : Real.exp (Real.log (Real.rpow (m:ℝ) (D0+6) * (2*C0)))
        ≤ Real.exp (c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2)) :=
      Real.exp_le_exp.mpr hm
    rw [Real.exp_log hYpos] at hexp
    have hinv : (Real.exp (c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2)))⁻¹
        ≤ (Real.rpow (m:ℝ) (D0+6) * (2*C0))⁻¹ := by
      rw [inv_le_inv₀ (Real.exp_pos _) hYpos]
      exact hexp
    have hexpneg : Real.exp (-(c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2)))
        = (Real.exp (c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2)))⁻¹ :=
      Real.exp_neg _
    rw [hexpneg]
    have hsc : C0 * (2*C0)⁻¹ = (1:ℝ)/2 := by
      have hne : C0 ≠ 0 := ne_of_gt hC0
      rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      norm_num
    have hcomb : ((m:ℝ)^2) * ((m:ℝ) ^ (-(D0+6))) = ((m:ℝ) ^ (-(D0+4))) := by
      rw [← Real.rpow_natCast (m:ℝ) 2, ← Real.rpow_add hmpos]
      congr 1
      push_cast
      ring
    calc C0 * (m:ℝ)^2 * (Real.exp (c0 * (m:ℝ) * Real.rpow (1/(2*Real.log (m:ℝ))) (3/2)))⁻¹
        ≤ C0 * (m:ℝ)^2 * (((m:ℝ) ^ (D0+6)) * (2*C0))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (mul_nonneg (le_of_lt hC0) (by positivity))
      _ = (C0 * (2*C0)⁻¹) * (((m:ℝ)^2) * ((m:ℝ) ^ (D0+6))⁻¹) := by
          rw [mul_inv_rev]; ring
      _ = (1/2) * (((m:ℝ)^2) * ((m:ℝ) ^ (D0+6))⁻¹) := by rw [hsc]
      _ = (1/2) * (((m:ℝ)^2) * ((m:ℝ) ^ (-(D0+6)))) := by
          rw [Real.rpow_neg (le_of_lt hmpos) (D0+6)]
      _ = (1/2) * ((m:ℝ) ^ (-(D0+4))) := by rw [hcomb]
      _ = ((m:ℝ) ^ (-(D0+4)))/2 := by ring
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  exact ⟨M, fun m hm => hM m hm⟩
  /- @proof-region region.target-node.session.92b37c5bbfce9c6c end -/

end Statlib.Imported

