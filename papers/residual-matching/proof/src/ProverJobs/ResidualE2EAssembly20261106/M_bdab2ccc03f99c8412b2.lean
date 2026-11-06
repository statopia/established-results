import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_1035201060_6a460451 : ∀ (a b : ℕ),
    ∃ u : ℕ → Matrix (Fin a) (Fin b) ℝ, DenseRange u := by
  /- @proof-region region.target-node.session.39b651cbfe3b3c3f begin -/
  intro a b
  refine ⟨fun n => TopologicalSpace.denseSeq ((_ : Fin a) → (_ : Fin b) → ℝ) n, ?_⟩
  exact TopologicalSpace.denseRange_denseSeq ((_ : Fin a) → (_ : Fin b) → ℝ)
  /- @proof-region region.target-node.session.39b651cbfe3b3c3f end -/

end Statlib.Imported

