import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

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
theorem statopia_math_node_3319165159_31a3e20a : ∀ (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℝ),
    Statlib.HighDim.MatrixAnalysis.opNorm X ≤ ∑ a : Fin m, ∑ b : Fin n, |X a b| := by
  /- @proof-region region.target-node.session.f116796cd9c908c8 begin -/
  intro m n X
  unfold Statlib.HighDim.MatrixAnalysis.opNorm
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg _)))
    (fun v => ?_)
  have hmain : ‖(Matrix.toEuclideanLin X) v‖ ≤ (∑ a : Fin m, ∑ b : Fin n, |X a b|) * ‖v‖ := by
    have hw : ‖(Matrix.toEuclideanLin X) v‖
        = Real.sqrt (∑ a : Fin m, |X.mulVec v.ofLp a| ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
    have hvb : ∀ b : Fin n, |v.ofLp b| ≤ ‖v‖ :=
      fun b => by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v b
    have h1 : Real.sqrt (∑ a : Fin m, |X.mulVec v.ofLp a| ^ 2)
        ≤ ∑ a : Fin m, |X.mulVec v.ofLp a| := by
      have hnn : (0:ℝ) ≤ ∑ a : Fin m, |X.mulVec v.ofLp a| :=
        Finset.sum_nonneg (fun a _ => abs_nonneg _)
      have hsq : (∑ a : Fin m, |X.mulVec v.ofLp a| ^ 2)
          ≤ (∑ a : Fin m, |X.mulVec v.ofLp a|) * (∑ b : Fin m, |X.mulVec v.ofLp b|) := by
        have key : ∀ a : Fin m, |X.mulVec v.ofLp a| ^ 2
            ≤ |X.mulVec v.ofLp a| * (∑ b : Fin m, |X.mulVec v.ofLp b|) := by
          intro a
          have hle : |X.mulVec v.ofLp a| ≤ ∑ b : Fin m, |X.mulVec v.ofLp b| :=
            Finset.single_le_sum (f := fun b : Fin m => |X.mulVec v.ofLp b|)
              (fun b _ => abs_nonneg _) (Finset.mem_univ a)
          calc |X.mulVec v.ofLp a| ^ 2
              = |X.mulVec v.ofLp a| * |X.mulVec v.ofLp a| := pow_two _
            _ ≤ |X.mulVec v.ofLp a| * (∑ b : Fin m, |X.mulVec v.ofLp b|) :=
                mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        calc (∑ a : Fin m, |X.mulVec v.ofLp a| ^ 2)
            ≤ ∑ a : Fin m, |X.mulVec v.ofLp a| * (∑ b : Fin m, |X.mulVec v.ofLp b|) :=
              Finset.sum_le_sum (fun a _ => key a)
          _ = (∑ a : Fin m, |X.mulVec v.ofLp a|) * (∑ b : Fin m, |X.mulVec v.ofLp b|) := by
              rw [Finset.sum_mul]
      calc Real.sqrt (∑ a : Fin m, |X.mulVec v.ofLp a| ^ 2)
          ≤ Real.sqrt ((∑ a : Fin m, |X.mulVec v.ofLp a|)
              * (∑ b : Fin m, |X.mulVec v.ofLp b|)) := Real.sqrt_le_sqrt hsq
        _ = ∑ a : Fin m, |X.mulVec v.ofLp a| := Real.sqrt_mul_self hnn
    have h2 : ∑ a : Fin m, |X.mulVec v.ofLp a|
        ≤ (∑ a : Fin m, ∑ b : Fin n, |X a b|) * ‖v‖ := by
      have hrow : ∀ a : Fin m, |X.mulVec v.ofLp a| ≤ (∑ b : Fin n, |X a b|) * ‖v‖ := by
        intro a
        have hentry : |X.mulVec v.ofLp a| ≤ ∑ b : Fin n, |X a b| * |v.ofLp b| := by
          calc |X.mulVec v.ofLp a| = |∑ b : Fin n, X a b * v.ofLp b| := by
                simp [Matrix.mulVec, dotProduct]
            _ ≤ ∑ b : Fin n, |X a b * v.ofLp b| :=
                Finset.abs_sum_le_sum_abs (fun b : Fin n => X a b * v.ofLp b) Finset.univ
            _ = ∑ b : Fin n, |X a b| * |v.ofLp b| :=
                Finset.sum_congr rfl (fun b _ => abs_mul _ _)
        calc |X.mulVec v.ofLp a| ≤ ∑ b : Fin n, |X a b| * |v.ofLp b| := hentry
          _ ≤ ∑ b : Fin n, |X a b| * ‖v‖ :=
              Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hvb b) (abs_nonneg _))
          _ = (∑ b : Fin n, |X a b|) * ‖v‖ := by rw [Finset.sum_mul]
      calc ∑ a : Fin m, |X.mulVec v.ofLp a|
          ≤ ∑ a : Fin m, (∑ b : Fin n, |X a b|) * ‖v‖ :=
            Finset.sum_le_sum (fun a _ => hrow a)
        _ = (∑ a : Fin m, ∑ b : Fin n, |X a b|) * ‖v‖ := by rw [Finset.sum_mul]
    calc ‖(Matrix.toEuclideanLin X) v‖
        = Real.sqrt (∑ a : Fin m, |X.mulVec v.ofLp a| ^ 2) := hw
      _ ≤ ∑ a : Fin m, |X.mulVec v.ofLp a| := h1
      _ ≤ (∑ a : Fin m, ∑ b : Fin n, |X a b|) * ‖v‖ := h2
  simpa [LinearMap.coe_toContinuousLinearMap'] using hmain
  /- @proof-region region.target-node.session.f116796cd9c908c8 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3319165159_31a3e20a


