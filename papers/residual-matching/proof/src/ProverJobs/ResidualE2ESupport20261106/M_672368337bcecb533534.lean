import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_1409213541_c481236b : ∀ (m n : ℕ) (E : Matrix (Fin m) (Fin n) ℝ),
    ‖E‖ ≤ Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (E i j) ^ 2) := by
  /- @proof-region region.target-node.session.94bd56815a779b0a begin -/
  intro m n E
  set S : ℝ := ∑ i : Fin m, ∑ j : Fin n, (E i j) ^ 2 with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg S) ?_
  intro x
  have happ : ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) E) x
      = (EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp) := by
    simp [Matrix.toEuclideanLin]
  rw [happ]
  have hterm : ∀ i : Fin m,
      ‖((EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp)).ofLp i‖ ^ 2
        ≤ (∑ j : Fin n, (E i j) ^ 2) * (∑ j : Fin n, (x.ofLp j) ^ 2) := by
    intro i
    have h1 : ((EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp)).ofLp i
        = ∑ j : Fin n, E i j * x.ofLp j := by
      first
        | rfl
        | (simp only [Matrix.mulVec]; rfl)
        | (simp [Matrix.mulVec]; rfl)
    rw [h1, Real.norm_eq_abs, sq_abs]
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : Fin n => E i j) (fun j : Fin n => x.ofLp j)
  have hsq : ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp)‖ ^ 2 ≤ S * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin m,
          ‖((EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp)).ofLp i‖ ^ 2
        ≤ ∑ i : Fin m, (∑ j : Fin n, (E i j) ^ 2) * (∑ j : Fin n, (x.ofLp j) ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = S * (∑ j : Fin n, (x.ofLp j) ^ 2) := by
          rw [hSdef, ← Finset.sum_mul]
      _ = S * ‖x‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq x]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  calc ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp)‖
      = Real.sqrt (‖(EuclideanSpace.equiv (Fin m) ℝ).symm (E.mulVec x.ofLp)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (S * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt S * ‖x‖ := by
        rw [Real.sqrt_mul hSnn, Real.sqrt_sq (norm_nonneg x)]
  /- @proof-region region.target-node.session.94bd56815a779b0a end -/

end Statlib.Imported

