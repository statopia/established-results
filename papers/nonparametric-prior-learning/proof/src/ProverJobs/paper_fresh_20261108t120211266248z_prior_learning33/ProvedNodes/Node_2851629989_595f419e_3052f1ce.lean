import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2851629989_595f419e : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (flim : Ω → ℝ) (g : Ω → ℝ)
    (hf_meas : ∀ n : ℕ, Measurable (f n)) (hflim_meas : Measurable flim)
    (hg_int : Integrable g μ) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (h_dom : ∀ᵐ ω ∂μ, ∀ n : ℕ, ‖f n ω‖ ≤ g ω)
    (h_conv : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (flim ω))),
    Integrable flim μ ∧
      Tendsto (fun n : ℕ => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, flim ω ∂μ)) := by
  /- @proof-region region.external.9053309767cb676ba6b0e0931dd9d7c7 begin -/
  intro Ω inst μ f flim g hf_meas hflim_meas hg_int hg_nonneg h_dom h_conv
  have hbound : ∀ᵐ ω ∂μ, ‖flim ω‖ ≤ g ω := by
    filter_upwards [h_dom, h_conv] with ω hω hconv
    exact le_of_tendsto hconv.norm (Filter.Eventually.of_forall hω)
  refine ⟨Integrable.mono' hg_int hflim_meas.aestronglyMeasurable hbound, ?_⟩
  exact tendsto_integral_of_dominated_convergence g
    (fun n => (hf_meas n).aestronglyMeasurable) hg_int
    (fun n => h_dom.mono fun ω h => h n) h_conv
  /- @proof-region region.external.9053309767cb676ba6b0e0931dd9d7c7 end -/

end Statlib.Imported
end

