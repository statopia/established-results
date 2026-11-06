import Statlib.HighDim.Vocabulary.SVD
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_3f6faa1c6fc9a539d94b

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
theorem statopia_math_node_3531617169_7b5c941e : ∀ (m n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin (min m n)),
    (Statlib.HighDim.Vocabulary.singularValues._proof_1 (fun a b => c * A a b)).eigenvalues₀
        (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2
          (Fin.castLE (Nat.min_le_right m n) k))
      = c ^ 2 *
        (Statlib.HighDim.Vocabulary.singularValues._proof_1 A).eigenvalues₀
          (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2
            (Fin.castLE (Nat.min_le_right m n) k)) := by
  /- @proof-region region.target-node.session.c08d1cd138127ff1 begin -/
  intro m n c hc A k
  let B : Matrix (Fin m) (Fin n) ℝ := fun a b => c * A a b
  have hmat : B.transpose * B = c ^ 2 • (A.transpose * A) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    change ∑ l, (c * A l i) * (c * A l j) = c ^ 2 * ∑ l, A l i * A l j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  show (Statlib.HighDim.Vocabulary.singularValues._proof_1 B).eigenvalues₀
      (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2
        (Fin.castLE (Nat.min_le_right m n) k))
    = c ^ 2 *
      (Statlib.HighDim.Vocabulary.singularValues._proof_1 A).eigenvalues₀
        (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2
          (Fin.castLE (Nat.min_le_right m n) k))
  exact statopia_math_node_3275750866_883f8e1a n (B.transpose * B) (A.transpose * A)
    (Statlib.HighDim.Vocabulary.singularValues._proof_1 B)
    (Statlib.HighDim.Vocabulary.singularValues._proof_1 A)
    (c ^ 2) (sq_nonneg c) hmat
    (Fin.cast Statlib.HighDim.Vocabulary.singularValues._proof_2
      (Fin.castLE (Nat.min_le_right m n) k))
  /- @proof-region region.target-node.session.c08d1cd138127ff1 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3531617169_7b5c941e


