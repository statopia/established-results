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
theorem statopia_math_node_2663820550_efe405d1 : ∀ (Omega : Type*) [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : ℕ → Omega → ℝ) (G : Omega → ℝ)
    (hX : ∀ n : ℕ, AEStronglyMeasurable (X n) mu)
    (hlim : ∀ᵐ omega ∂mu, Filter.Tendsto (fun n : ℕ => X n omega) Filter.atTop (𝓝 (G omega))),
    AEStronglyMeasurable G mu := by
  /- @proof-region region.target-node.session.d2054d3ed767cd8c begin -/
  intro Omega _ mu _ X G hX hlim
  exact aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) hX hlim
  /- @proof-region region.target-node.session.d2054d3ed767cd8c end -/

end Statlib.Imported
end

