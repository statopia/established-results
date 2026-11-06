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
theorem statopia_math_node_3217929161_d25f0da7 : ∀ (m : ℕ) (alpha0 p Lv C1 t : ℝ)
    (hm : 0 < (m : ℝ)) (hp : 0 < p) (ht : 0 < t)
    (hlog : 1 ≤ Real.log (m : ℝ))
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (hC1 : 18 * C1 ^ 2 ≤ Real.rpow (Real.log (m : ℝ)) (alpha0 - 4))
    (hLv_nonneg : 0 ≤ Lv)
    (hLv_le : Lv ≤ C1 * Real.log (m : ℝ))
    (ht_inv : (Real.log (m : ℝ))⁻¹ ≤ t),
    9 * Lv ^ 2 / ((m : ℝ) * p) / t ^ 2 ≤ 1 / 2 := by
  /- @proof-region region.target-node.session.71c70db94672ee5b begin -/
  intro m alpha0 p Lv C1 t hm hp ht hlog hsparse hC1 hLv_nonneg hLv_le ht_inv
  set g := Real.log (m : ℝ) with hg
  have hg_pos : 0 < g := lt_of_lt_of_le zero_lt_one hlog
  have hA_pos : 0 < (m : ℝ) * p := mul_pos hm hp
  have hg2_pos : 0 < g ^ 2 := pow_pos hg_pos 2
  have hg2_ne : g ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hg_pos)
  have hLv_sq_bound : Lv ^ 2 ≤ C1 ^ 2 * g ^ 2 := by
    have h1 : 0 ≤ C1 * g - Lv := by linarith
    have h2 : 0 ≤ C1 * g + Lv := by linarith
    have hfac : 0 ≤ (C1 * g - Lv) * (C1 * g + Lv) := mul_nonneg h1 h2
    nlinarith [hfac]
  have hstep1 : 18 * Lv ^ 2 ≤ 18 * C1 ^ 2 * g ^ 2 := by nlinarith [hLv_sq_bound]
  have hgi : 0 < g⁻¹ := inv_pos.mpr hg_pos
  have ht_sq_bound : (g ^ 2)⁻¹ ≤ t ^ 2 := by
    have h1 : 0 ≤ t - g⁻¹ := by linarith
    have h2 : 0 ≤ t + g⁻¹ := by linarith
    have hfac : 0 ≤ (t - g⁻¹) * (t + g⁻¹) := mul_nonneg h1 h2
    have hs : (g⁻¹) ^ 2 ≤ t ^ 2 := by nlinarith [hfac]
    rwa [inv_pow] at hs
  have h4 : g ^ 4 = g.rpow (4 : ℝ) := by
    first
      | exact Real.rpow_natCast g 4
      | exact (Real.rpow_natCast g 4).symm
  have hKey4 : 18 * C1 ^ 2 * g.rpow (4 : ℝ) ≤ g.rpow alpha0 := by
    have hpos4 : 0 < g.rpow (4 : ℝ) := Real.rpow_pos_of_pos hg_pos 4
    have h := mul_le_mul_of_nonneg_right hC1 (le_of_lt hpos4)
    have hprod : g.rpow (alpha0 - 4) * g.rpow (4 : ℝ) = g.rpow ((alpha0 - 4) + 4) :=
      (Real.rpow_add hg_pos (alpha0 - 4) 4).symm
    rw [hprod] at h
    have harg : (alpha0 - 4) + 4 = alpha0 := by ring
    rwa [harg] at h
  have hKey : 18 * C1 ^ 2 * g ^ 4 ≤ g.rpow alpha0 := by
    rw [h4]
    exact hKey4
  have hstep2 : 18 * C1 ^ 2 * g ^ 2 ≤ g.rpow alpha0 * (g ^ 2)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hKey (le_of_lt (inv_pos.mpr hg2_pos))
    have heq : 18 * C1 ^ 2 * g ^ 4 * (g ^ 2)⁻¹ = 18 * C1 ^ 2 * g ^ 2 := by field_simp
    rwa [heq] at h
  have hstep3 : g.rpow alpha0 * (g ^ 2)⁻¹ ≤ (m : ℝ) * p * t ^ 2 := by
    have hpos_inv : 0 ≤ (g ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hg2_pos)
    exact mul_le_mul hsparse ht_sq_bound hpos_inv (le_of_lt hA_pos)
  have hmain : 18 * Lv ^ 2 ≤ (m : ℝ) * p * t ^ 2 :=
    le_trans hstep1 (le_trans hstep2 hstep3)
  have hden : 0 < ((m : ℝ) * p) * t ^ 2 := mul_pos hA_pos (pow_pos ht 2)
  rw [div_div]
  rw [div_le_iff₀ hden]
  nlinarith [hmain]
  /- @proof-region region.target-node.session.71c70db94672ee5b end -/

end Statlib.Imported

