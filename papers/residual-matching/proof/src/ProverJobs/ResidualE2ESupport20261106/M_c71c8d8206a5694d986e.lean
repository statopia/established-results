import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_e390773efbd96d9c4469
import ProverJobs.ResidualE2ESupport20261106.M_9005fcf5aaa1ba711e3e

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
theorem statopia_math_node_3875775941_f40cd015 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hH : ((A.map Complex.ofReal).transpose * (A.map Complex.ofReal)).IsHermitian),
    (Finset.univ.val.map (fun i : Fin n => hH.eigenvalues i)) =
      (Finset.univ.val.map (fun i : Fin n => (Statlib.Imported.svals A i) ^ 2)) := by
  /- @proof-region region.target-node.session.3068dce4e228869d begin -/
  intro m n A hH
  have hroot : Finset.univ.val.map (fun i : Fin n => hH.eigenvalues i)
      = Finset.univ.val.map (fun i : Fin n =>
          (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
    exact statopia_math_node_3611940486_e5c47169 m n A hH
  have hsq : Finset.univ.val.map (fun i : Fin n => (Statlib.Imported.svals A i) ^ 2)
      = Finset.univ.val.map (fun i : Fin n =>
          (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
    simpa only [Statlib.Imported.svals] using
      (statopia_math_node_1809001392_3907642a m n A)
  rw [hroot, hsq]
  /- @proof-region region.target-node.session.3068dce4e228869d end -/

end Statlib.Imported

