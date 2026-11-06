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
theorem statopia_math_node_2970505295_46650432 : ∀ (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ),
    (∑ i : Fin m, ∑ j : Fin n, a i * A i j * b j)
      ≤ Real.sqrt (∑ i : Fin m, (a i) ^ 2) * ‖A‖ * Real.sqrt (∑ j : Fin n, (b j) ^ 2) := by
  /- @proof-region region.target-node.session.f0f367b40a717827 begin -/
  intro m n A a b
  have hnorm_formula : ∀ (k : ℕ) (w : Fin k → ℝ),
      ‖(WithLp.toLp (p := 2) w : EuclideanSpace ℝ (Fin k))‖
        = Real.sqrt (∑ i : Fin k, (w i) ^ 2) := by
    intro k w
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have h_e : (∑ i : Fin m, ∑ j : Fin n, a i * A i j * b j)
      = ∑ i : Fin m, a i * (A.mulVec b) i := by
    have hdot : ∀ i : Fin m, (A.mulVec b) i = ∑ j : Fin n, A i j * b j := fun i => rfl
    simp only [hdot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hN : ‖(WithLp.toLp (p := 2) (A.mulVec b) : EuclideanSpace ℝ (Fin m))‖
      ≤ ‖A‖ * ‖(WithLp.toLp (p := 2) (b : Fin n → ℝ) : EuclideanSpace ℝ (Fin n))‖ := by
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp (p := 2) (b : Fin n → ℝ) : EuclideanSpace ℝ (Fin n))
    simpa using h
  have hCS : (∑ i : Fin m, a i * (A.mulVec b) i)
      ≤ Real.sqrt (∑ i : Fin m, (a i) ^ 2)
          * Real.sqrt (∑ i : Fin m, ((A.mulVec b) i) ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m)) a
      (fun i => (A.mulVec b) i)
    simpa using h
  have hsqrt_w : Real.sqrt (∑ i : Fin m, ((A.mulVec b) i) ^ 2)
      ≤ ‖A‖ * Real.sqrt (∑ j : Fin n, (b j) ^ 2) := by
    rw [← hnorm_formula m (A.mulVec b), ← hnorm_formula n b]
    exact hN
  calc (∑ i : Fin m, ∑ j : Fin n, a i * A i j * b j)
      = ∑ i : Fin m, a i * (A.mulVec b) i := h_e
    _ ≤ Real.sqrt (∑ i : Fin m, (a i) ^ 2)
          * Real.sqrt (∑ i : Fin m, ((A.mulVec b) i) ^ 2) := hCS
    _ ≤ Real.sqrt (∑ i : Fin m, (a i) ^ 2)
          * (‖A‖ * Real.sqrt (∑ j : Fin n, (b j) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsqrt_w (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ i : Fin m, (a i) ^ 2) * ‖A‖ * Real.sqrt (∑ j : Fin n, (b j) ^ 2) := by
        ring
  /- @proof-region region.target-node.session.f0f367b40a717827 end -/

end Statlib.Imported

