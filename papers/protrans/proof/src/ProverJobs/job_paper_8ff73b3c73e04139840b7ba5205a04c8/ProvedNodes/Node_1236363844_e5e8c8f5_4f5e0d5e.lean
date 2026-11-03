import Lean
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Vocabulary
import ProverJobs.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Base

namespace PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open _root_.PaperProofTasks.job_paper_8ff73b3c73e04139840b7ba5205a04c8.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1236363844_e5e8c8f5 : ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : ℝ) (hV : 0 < V) (W : Ω → ℝ) (hW : Measurable W)
    (h_moment : ∀ (r : ℕ), 2 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|W ω| ^ r) ∂μ ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)),
    ∀ (r : ℕ), 2 ≤ r →
      Integrable (fun ω => |W ω| ^ r) μ ∧
        ∫ ω, |W ω| ^ r ∂μ ≤ (r.factorial : ℝ) * V ^ r := by
  /- @proof-region region.target-node.session.f7e26033be843a8f begin -/
  intro Ω _ μ _ V hV W hW h_moment r hr
  have h_meas : Measurable fun ω => |W ω| ^ r := hW.abs.pow_const r
  have h_nonneg : 0 ≤ᵐ[μ] fun ω => |W ω| ^ r :=
    Filter.Eventually.of_forall fun ω => by positivity
  have h_lt : ∫⁻ ω, ENNReal.ofReal (|W ω| ^ r) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne (h_moment r hr)
  have hint : Integrable (fun ω => |W ω| ^ r) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (f := fun ω => |W ω| ^ r)
      h_meas.aestronglyMeasurable h_nonneg).mp h_lt
  refine ⟨hint, ?_⟩
  have hfac : (0 : ℝ) ≤ (r.factorial : ℝ) * V ^ r :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hV.le r)
  have h1 : ENNReal.ofReal (∫ ω, |W ω| ^ r ∂μ) ≤
      ENNReal.ofReal ((r.factorial : ℝ) * V ^ r) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint h_nonneg]
    exact h_moment r hr
  exact (ENNReal.ofReal_le_ofReal_iff hfac).mp h1
  /- @proof-region region.target-node.session.f7e26033be843a8f end -/

end Statlib.Imported

