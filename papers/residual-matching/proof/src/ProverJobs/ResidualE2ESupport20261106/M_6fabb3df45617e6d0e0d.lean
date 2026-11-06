import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ad2660411b093d071ccc
import ProverJobs.ResidualE2ESupport20261106.M_f00de8b445341c78f04b
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualLoss20261106.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3980448475_62265ffe : (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin (min m n)) (c : ℝ), 0 ≤ c →
      Statlib.HighDim.MatrixAnalysis.singularValues (c • A) k
        = c * Statlib.HighDim.MatrixAnalysis.singularValues A k) ∧
    (∀ {m n : ℕ} (k : Fin (min m n)),
      Measurable fun A : Matrix (Fin m) (Fin n) ℝ =>
        Statlib.HighDim.MatrixAnalysis.singularValues A k) := by
  /- @proof-region region.target-node.session.ccc5587f192fd92f begin -/
  constructor
  · intro m n A k c hc
    exact (statopia_math_node_3786437948_943d4007 m n A c k).2.2.1 hc
  · intro m n k
    exact statopia_math_node_3334131066_c2302711 k
  /- @proof-region region.target-node.session.ccc5587f192fd92f end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3980448475_62265ffe


