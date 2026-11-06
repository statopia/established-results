import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.Vocabulary.SVD
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_8d90299ec67dcb83531b

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
theorem statopia_math_node_3402644224_aa9fa448 : ∀ (m n : ℕ) (hnm : n ≤ m) (c : ℝ) (hc : 0 ≤ c)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
    sv hnm (fun a b => c * A a b) i = c * sv hnm A i := by
  /- @proof-region region.target-node.session.ac7269cd584845e6 begin -/
  intro m n hnm c hc A i
  unfold sv
  rw [Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary,
      Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
  unfold Statlib.HighDim.Vocabulary.singularValues
  have heig := statopia_math_node_3531617169_7b5c941e (c := c) (hc := hc)
    (A := A) (k := Fin.castLE (sv._proof_1 hnm) i)
  rw [heig]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

  /- @proof-region region.target-node.session.ac7269cd584845e6 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3402644224_aa9fa448


