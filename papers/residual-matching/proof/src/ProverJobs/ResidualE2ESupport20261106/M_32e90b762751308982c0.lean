import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_0b72df93bbfde3dcfb84

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
theorem statopia_math_node_3243536340_6e6dfa97 : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian),
    (Polynomial.map (algebraMap ℝ ℂ) M.charpoly).roots
      = Multiset.map (RCLike.ofReal ∘ hM.eigenvalues) Finset.univ.val := by
  /- @proof-region region.target-node.session.dd87ed32cbbe8879 begin -/
  intro n M hM
  have h1 : M.charpoly.roots = Multiset.map hM.eigenvalues Finset.univ.val := by
    simpa using (Matrix.IsHermitian.roots_charpoly_eq_eigenvalues (𝕜 := ℝ) hM)
  have hsplit : M.charpoly.Splits := statopia_math_node_1091255960_d6b37970 n M hM
  have h2 : (Polynomial.map (algebraMap ℝ ℂ) M.charpoly).roots
      = (M.charpoly.roots).map (algebraMap ℝ ℂ) :=
    Polynomial.roots_map hsplit (algebraMap ℝ ℂ)
  rw [h2, h1]
  simp
  exact List.Perm.refl _
  /- @proof-region region.target-node.session.dd87ed32cbbe8879 end -/

end Statlib.Imported

