import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_603be9b01d60bdf91269

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
theorem statopia_math_node_3837097212_a755865c : ∀ (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n),
    svals A i ≤ ‖A‖ := by
  /- @proof-region region.target-node.session.7f97006857d93d2a begin -/
  intro m n A i
  have hgen : ∀ (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      (hT : T.IsSymmetric)
      (hk : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n))
      (j : Fin (Fintype.card (Fin n))),
      T = 0 → Real.sqrt (hT.eigenvalues hk j) = 0 := by
    intro T hT hk j hT0
    have h1 : T ((hT.eigenvectorBasis hk) j) =
        hT.eigenvalues hk j • (hT.eigenvectorBasis hk) j := by
      simpa using (hT.hasEigenvector_eigenvectorBasis hk j).apply_eq_smul
    have hz : T ((hT.eigenvectorBasis hk) j) = 0 := by
      have hcongr := congrArg (fun S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) =>
        S ((hT.eigenvectorBasis hk) j)) hT0
      simpa using hcongr
    have h1' : (0 : EuclideanSpace ℝ (Fin n)) =
        hT.eigenvalues hk j • (hT.eigenvectorBasis hk) j := hz.symm.trans h1
    have hv : (hT.eigenvectorBasis hk) j ≠ 0 := by
      intro h0
      have h2 := (hT.eigenvectorBasis hk).norm_eq_one j
      rw [h0, norm_zero] at h2
      exact zero_ne_one h2
    have hlam : hT.eigenvalues hk j = 0 := by
      rcases smul_eq_zero.mp h1'.symm with h | h
      · exact h
      · exact absurd h hv
    rw [hlam, Real.sqrt_zero]
  have hzero : svals (0 : Matrix (Fin m) (Fin n) ℝ) i = 0 := by
    simp only [svals, Matrix.IsHermitian.eigenvalues₀]
    refine hgen _ _ _ _ ?_
    simp
  have hweyl := statopia_math_node_1482569421_d5eba7e6 A (0 : Matrix (Fin m) (Fin n) ℝ) i
  rw [hzero] at hweyl
  simpa using (abs_le.mp hweyl).2
  /- @proof-region region.target-node.session.7f97006857d93d2a end -/

end Statlib.Imported

