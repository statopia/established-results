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
theorem statopia_math_node_3453903389_21203619 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C_var : ℝ) (hB : 0 < B)
    (hCvar : C_var = sSup {y : ℝ | ∃ x : ℝ, 0 < x ∧ y = x ^ 2 / (Real.exp x - 1)})
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (hexp_int : Integrable (fun ω => Real.exp (|Z ω| / B)) P)
    (hexp_bound : ∫ ω, Real.exp (|Z ω| / B) ∂P ≤ 2),
    0 < C_var ∧ C_var < 1 ∧
      Integrable (fun ω => (Z ω) ^ 2) P ∧
      ∫ ω, (Z ω) ^ 2 ∂P ≤ C_var * B ^ 2 := by
  /- @proof-region region.target-node.session.3aeeef47aeb5de63 begin -/
  intro Ω _ P _ B C_var hB hCvar Z hZ hexp_int hexp_bound
  classical
  let S : Set ℝ := {y : ℝ | ∃ x : ℝ, 0 < x ∧ y = x ^ 2 / (Real.exp x - 1)}
  have hCvar' : C_var = sSup S := hCvar
  have hkey : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ (7 / 8) * (Real.exp x - 1) := by
    intro x hx
    have hT : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
      have h := Real.sum_le_exp_of_nonneg hx 4
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
      linarith
    have hq : (0 : ℝ) ≤ 7 * x ^ 2 - 27 * x + 42 := by
      nlinarith [sq_nonneg (14 * x - 27)]
    nlinarith [hT, hx, hq]
  have hS_bdd : BddAbove S := by
    refine ⟨7 / 8, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hpos : 0 < Real.exp x - 1 := by
      have h1 : Real.exp 0 < Real.exp x := Real.exp_lt_exp.mpr hx
      rw [Real.exp_zero] at h1
      linarith
    have hmain : x ^ 2 ≤ (7 / 8) * (Real.exp x - 1) := hkey x (le_of_lt hx)
    calc x ^ 2 / (Real.exp x - 1)
        = x ^ 2 * (Real.exp x - 1)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ ((7 / 8) * (Real.exp x - 1)) * (Real.exp x - 1)⁻¹ := by
            apply mul_le_mul_of_nonneg_right hmain
            exact inv_nonneg.mpr (le_of_lt hpos)
      _ = 7 / 8 := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  have hS_ne : S.Nonempty :=
    ⟨1 / (Real.exp 1 - 1), 1, one_pos, by norm_num⟩
  have hCvar_pos : 0 < C_var := by
    have hmem : (1 / (Real.exp 1 - 1)) ∈ S := ⟨1, one_pos, by norm_num⟩
    have hle : 1 / (Real.exp 1 - 1) ≤ C_var := by
      rw [hCvar']
      exact le_csSup hS_bdd hmem
    have hpos : 0 < 1 / (Real.exp 1 - 1) := by
      apply div_pos one_pos
      have h1 : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
      rw [Real.exp_zero] at h1
      linarith
    exact lt_of_lt_of_le hpos hle
  have hCvar_lt : C_var < 1 := by
    have hsup_le : sSup S ≤ 7 / 8 := by
      apply csSup_le hS_ne
      rintro y ⟨x, hx, rfl⟩
      have hpos : 0 < Real.exp x - 1 := by
        have h1 : Real.exp 0 < Real.exp x := Real.exp_lt_exp.mpr hx
        rw [Real.exp_zero] at h1
        linarith
      have hmain : x ^ 2 ≤ (7 / 8) * (Real.exp x - 1) := hkey x (le_of_lt hx)
      calc x ^ 2 / (Real.exp x - 1)
          = x ^ 2 * (Real.exp x - 1)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ ((7 / 8) * (Real.exp x - 1)) * (Real.exp x - 1)⁻¹ := by
              apply mul_le_mul_of_nonneg_right hmain
              exact inv_nonneg.mpr (le_of_lt hpos)
        _ = 7 / 8 := by
              rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
    rw [hCvar']
    calc sSup S ≤ 7 / 8 := hsup_le
      _ < 1 := by norm_num
  have hle_div : ∀ x : ℝ, 0 < x → x ^ 2 ≤ C_var * (Real.exp x - 1) := by
    intro x hx
    have hpos : 0 < Real.exp x - 1 := by
      have h1 : Real.exp 0 < Real.exp x := Real.exp_lt_exp.mpr hx
      rw [Real.exp_zero] at h1
      linarith
    have hmem : x ^ 2 / (Real.exp x - 1) ∈ S := ⟨x, hx, rfl⟩
    have hle : x ^ 2 / (Real.exp x - 1) ≤ C_var := by
      rw [hCvar']
      exact le_csSup hS_bdd hmem
    calc x ^ 2 = x ^ 2 / (Real.exp x - 1) * (Real.exp x - 1) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      _ ≤ C_var * (Real.exp x - 1) :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
  have hle_ge : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ C_var * (Real.exp x - 1) := by
    intro x hx
    rcases lt_or_eq_of_le hx with h | h
    · exact hle_div x h
    · subst h
      simp [Real.exp_zero]
  have habs : ∀ a : ℝ, |a| ^ 2 = a ^ 2 := by
    intro a
    rcases le_or_gt 0 a with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]; ring
  have hpt : ∀ ω : Ω, (Z ω) ^ 2 ≤ C_var * B ^ 2 * (Real.exp (|Z ω| / B) - 1) := by
    intro ω
    have hy : 0 ≤ |Z ω| / B := div_nonneg (abs_nonneg _) (le_of_lt hB)
    have hb : (|Z ω| / B) ^ 2 ≤ C_var * (Real.exp (|Z ω| / B) - 1) := hle_ge (|Z ω| / B) hy
    have hX : (Z ω) ^ 2 = B ^ 2 * ((|Z ω| / B) ^ 2) := by
      rw [← habs (Z ω), div_pow, mul_comm (B ^ 2), div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hB))]
    rw [hX]
    calc B ^ 2 * ((|Z ω| / B) ^ 2)
        ≤ B ^ 2 * (C_var * (Real.exp (|Z ω| / B) - 1)) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg B)
      _ = C_var * B ^ 2 * (Real.exp (|Z ω| / B) - 1) := by ring
  have hint : Integrable (fun ω => C_var * B ^ 2 * (Real.exp (|Z ω| / B) - 1)) P := by
    have h1 : Integrable (fun ω => (C_var * B ^ 2) * Real.exp (|Z ω| / B)) P :=
      hexp_int.const_mul (C_var * B ^ 2)
    have h2 : Integrable (fun _ : Ω => C_var * B ^ 2) P := integrable_const (C_var * B ^ 2)
    have hsub := h1.sub h2
    simpa [mul_sub, mul_one] using hsub
  have hZ2int : Integrable (fun ω => (Z ω) ^ 2) P := by
    have hm : Measurable (fun ω => (Z ω) ^ 2) := by
      simpa [pow_two] using hZ.mul hZ
    refine Integrable.mono' hint hm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Z ω))]
    exact hpt ω
  have hbound : ∫ ω, (Z ω) ^ 2 ∂P ≤ C_var * B ^ 2 := by
    have hmono : ∫ ω, (Z ω) ^ 2 ∂P
        ≤ ∫ ω, C_var * B ^ 2 * (Real.exp (|Z ω| / B) - 1) ∂P :=
      integral_mono hZ2int hint (fun ω => hpt ω)
    have hA : ∫ ω, C_var * B ^ 2 * (Real.exp (|Z ω| / B) - 1) ∂P
        = (C_var * B ^ 2) * ∫ ω, (Real.exp (|Z ω| / B) - 1) ∂P := by
      rw [integral_const_mul]
    have hB2 : (∫ ω, (Real.exp (|Z ω| / B) - 1) ∂P)
        = (∫ ω, Real.exp (|Z ω| / B) ∂P) - 1 := by
      rw [integral_sub hexp_int (integrable_const (1 : ℝ))]
      congr 1
      simp
    have hCB : 0 ≤ C_var * B ^ 2 := mul_nonneg (le_of_lt hCvar_pos) (sq_nonneg B)
    have hexp1 : (∫ ω, Real.exp (|Z ω| / B) ∂P) - 1 ≤ 1 := by linarith [hexp_bound]
    calc ∫ ω, (Z ω) ^ 2 ∂P
        ≤ ∫ ω, C_var * B ^ 2 * (Real.exp (|Z ω| / B) - 1) ∂P := hmono
      _ = (C_var * B ^ 2) * ((∫ ω, Real.exp (|Z ω| / B) ∂P) - 1) := by rw [hA, hB2]
      _ ≤ (C_var * B ^ 2) * 1 := mul_le_mul_of_nonneg_left hexp1 hCB
      _ = C_var * B ^ 2 := by ring
  exact ⟨hCvar_pos, hCvar_lt, hZ2int, hbound⟩
  /- @proof-region region.target-node.session.3aeeef47aeb5de63 end -/

end Statlib.Imported

