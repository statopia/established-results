import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_1715789988_72947f49 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ n : ℕ, Measurable (f n))
    (hconv : ∀ᵐ ω ∂μ, ∃ x : ℝ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 x)),
    ∃ G : Ω → ℝ, Measurable G ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (G ω)) := by
  /- @proof-region region.target-node.session.ba6b3c228a886dff begin -/
  intro Ω _ μ f hf hconv
  refine ⟨fun ω => Filter.limsup (fun n : ℕ => f n ω) atTop, Measurable.limsup hf, ?_⟩
  filter_upwards [hconv] with ω hω
  obtain ⟨x, hx⟩ := hω
  rw [hx.limsup_eq]
  exact hx
  /- @proof-region region.target-node.session.ba6b3c228a886dff end -/

end Statlib.Imported
end

