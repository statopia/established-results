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
theorem statopia_math_node_2245285305_8fe98c79 : ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) = 1 := by
  /- @proof-region region.target-node.session.ef8863a3aec319f2 begin -/
  have hmean : ∫ x : ℝ, x ∂(ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) = 0 := by
    simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  have hvar := ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x)
    (μ := ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) aemeasurable_id
  have hid := ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [hvar] at hid
  simpa [hmean] using hid
  /- @proof-region region.target-node.session.ef8863a3aec319f2 end -/

end Statlib.Imported

