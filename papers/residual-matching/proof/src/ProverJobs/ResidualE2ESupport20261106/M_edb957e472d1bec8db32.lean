import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_35bed150fbe6905c6172

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3840929802_9daf1dcd :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n →
      (∫ g : (Fin m × Fin n) → ℝ,
        Statlib.HighDim.MatrixAnalysis.opNorm
          (fun (i : Fin m) (j : Fin n) => g (i, j))
        ∂(MeasureTheory.Measure.pi
          (fun _ : Fin m × Fin n => ProbabilityTheory.gaussianReal 0 1)))
        ≤ Real.sqrt (m : ℝ) + Real.sqrt (n : ℝ) + C := by
  refine ⟨1, by norm_num, ?_⟩
  intro m n _ _
  exact (statopia_math_node_3041891103_ca9d76ef m n).trans (by linarith)

#print axioms statopia_math_node_3840929802_9daf1dcd
end Statlib.Imported

