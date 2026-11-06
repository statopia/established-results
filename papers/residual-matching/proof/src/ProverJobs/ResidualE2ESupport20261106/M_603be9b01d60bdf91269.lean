import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SoftThresholdDenoisingHelpers
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_e86eff258501a72e4b7c

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
theorem statopia_math_node_1482569421_d5eba7e6 : ∀ {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (k : Fin n),
    |svals A k - svals B k| ≤ ‖A - B‖ := by
  /- @proof-region region.target-node.session.52bcda795b935a29 begin -/
  have hsv : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n) (h : k.val < min m n),
      svals A k = Statlib.HighDim.MatrixAnalysis.singularValues A ⟨k.val, h⟩ := by
    intro m n A k h
    rfl
  have hzero : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n),
      min m n ≤ k.val → svals A k = 0 :=
    fun A k hk => statopia_math_node_645163511_ea48f44b A k hk
  have weyl : ∀ {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (k : Fin n),
      k.val < min m n → svals A k ≤ svals B k + ‖A - B‖ := by
    intro m n A B k hk
    have h1 := hsv A k hk
    have h2 := hsv B k hk
    have h3 :=
      Statlib.HighDim.MatrixAnalysis.rectangular_singularValues_weyl_upper
        (A := B) (E := A - B) ⟨k.val, hk⟩
    rw [show B + (A - B) = A from by abel] at h3
    rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2] at h3
    rw [← h1, ← h2] at h3
    exact h3
  intro m n A B k
  rw [abs_le]
  by_cases hlt : k.val < min m n
  · refine ⟨?_, ?_⟩
    · have h1 := weyl B A k hlt
      have hnorm : ‖B - A‖ = ‖A - B‖ := by
        rw [show B - A = -(A - B) from (neg_sub A B).symm, norm_neg]
      linarith
    · have h2 := weyl A B k hlt
      linarith
  · have hge : min m n ≤ k.val := by omega
    have hA0 := hzero A k hge
    have hB0 := hzero B k hge
    have hn := norm_nonneg (A - B)
    rw [hA0, hB0]
    constructor <;> linarith
  /- @proof-region region.target-node.session.52bcda795b935a29 end -/

end Statlib.Imported

