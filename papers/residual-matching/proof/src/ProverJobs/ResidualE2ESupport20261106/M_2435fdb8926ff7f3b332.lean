import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_066e1a47284608d211dc

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3797206296_f8b95f54 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (h : 0 < n), svals A ⟨0, h⟩ = ‖A‖ := by
  /- @proof-region region.target-node.session.1040fdd2834fefbd begin -/
  intro m n A h
  unfold svals
  have hpsd : ∀ (x : EuclideanSpace ℝ (Fin n)),
      0 ≤ inner ℝ ((Matrix.toEuclideanLin (A.conjTranspose * A)) x) x :=
    LinearMap.IsPositive.inner_nonneg_left
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (Matrix.posSemidef_conjTranspose_mul_self A))
  have hmain : (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
      (Fin.cast (Fintype.card_fin n).symm ⟨0, h⟩) = ‖A.conjTranspose * A‖ :=
    statopia_math_node_2989538586_f823134e (A.conjTranspose * A)
      (Matrix.isHermitian_conjTranspose_mul_self A) hpsd h
  rw [hmain, Matrix.l2_opNorm_conjTranspose_mul_self A, ← pow_two]
  exact Real.sqrt_sq (norm_nonneg A)
  /- @proof-region region.target-node.session.1040fdd2834fefbd end -/

end Statlib.Imported

