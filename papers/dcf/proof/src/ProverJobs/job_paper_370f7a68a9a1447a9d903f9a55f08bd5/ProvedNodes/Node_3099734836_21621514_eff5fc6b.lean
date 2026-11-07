import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5

open scoped BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3099734836_21621514 : 1 ≤ (Real.log 2)⁻¹ * (Real.log 2)⁻¹ + (Real.log 2)⁻¹ + 1 ∧
      (∀ (p : ℕ), 0 < p → 0 < Real.log (p : ℝ) → ∀ φ : ℝ, 1 ≤ φ →
        φ ^ 3 + φ ^ 2 * (φ * Real.log (p : ℝ)) + φ * (φ * Real.log (p : ℝ)) ^ 2
          ≤ ((Real.log 2)⁻¹ * (Real.log 2)⁻¹ + (Real.log 2)⁻¹ + 1)
              * (φ * (φ * Real.log (p : ℝ)) ^ 2)) := by
  /- @proof-region region.target-node.session.4d127a481b0455bc begin -/
  constructor
  · have hpos : (0:ℝ) < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
    nlinarith [sq_nonneg ((Real.log 2)⁻¹)]
  · intro p hp hlog φ hφ
    have hMpos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hLpos : (0:ℝ) < Real.log (p:ℝ) := hlog
    have hp' : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have h1p : (1:ℝ) < (p:ℝ) := by
      have h0 : Real.log 1 < Real.log (p:ℝ) := by rw [Real.log_one]; exact hlog
      exact (Real.log_lt_log_iff zero_lt_one hp').mp h0
    have h2pnat : (2:ℕ) ≤ p := by
      have h : (1:ℕ) < p := by exact_mod_cast h1p
      omega
    have h2p : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast h2pnat
    have hlogmono : Real.log 2 ≤ Real.log (p:ℝ) := Real.log_le_log (by norm_num) h2p
    have hainv : (Real.log (p:ℝ))⁻¹ ≤ (Real.log 2)⁻¹ :=
      (inv_le_inv₀ hLpos hMpos).mpr hlogmono
    have hainvpos : (0:ℝ) < (Real.log (p:ℝ))⁻¹ := inv_pos.mpr hLpos
    have hsq : (Real.log (p:ℝ))⁻¹ * (Real.log (p:ℝ))⁻¹
        ≤ (Real.log 2)⁻¹ * (Real.log 2)⁻¹ :=
      mul_self_le_mul_self (le_of_lt hainvpos) hainv
    have hbracket : (Real.log (p:ℝ))⁻¹ * (Real.log (p:ℝ))⁻¹ + (Real.log (p:ℝ))⁻¹ + 1
        ≤ (Real.log 2)⁻¹ * (Real.log 2)⁻¹ + (Real.log 2)⁻¹ + 1 := by linarith
    have hfac : (0:ℝ) ≤ φ * (φ * Real.log (p:ℝ)) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfac
    have hkey : (φ * (φ * Real.log (p:ℝ)) ^ 2)
          * ((Real.log (p:ℝ))⁻¹ * (Real.log (p:ℝ))⁻¹ + (Real.log (p:ℝ))⁻¹ + 1)
        = φ ^ 3 + φ ^ 2 * (φ * Real.log (p:ℝ)) + φ * (φ * Real.log (p:ℝ)) ^ 2 := by
      have hLne : (Real.log (p:ℝ)) ≠ 0 := ne_of_gt hLpos
      field_simp
    calc φ ^ 3 + φ ^ 2 * (φ * Real.log (p:ℝ)) + φ * (φ * Real.log (p:ℝ)) ^ 2
        = (φ * (φ * Real.log (p:ℝ)) ^ 2)
            * ((Real.log (p:ℝ))⁻¹ * (Real.log (p:ℝ))⁻¹ + (Real.log (p:ℝ))⁻¹ + 1) :=
          hkey.symm
      _ ≤ (φ * (φ * Real.log (p:ℝ)) ^ 2)
            * ((Real.log 2)⁻¹ * (Real.log 2)⁻¹ + (Real.log 2)⁻¹ + 1) := hmul
      _ = ((Real.log 2)⁻¹ * (Real.log 2)⁻¹ + (Real.log 2)⁻¹ + 1)
            * (φ * (φ * Real.log (p:ℝ)) ^ 2) := by ring
  /- @proof-region region.target-node.session.4d127a481b0455bc end -/

end Statlib.Imported
end

