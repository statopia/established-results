import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_65e04f137ddff025e657

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
theorem statopia_math_node_2382536492_f7c626d4 : ∀ (m n : ℕ) (hnm : n ≤ m)
    (A B : Matrix (Fin m) (Fin n) ℝ),
    (∑ i : Fin n, (sv hnm A i - sv hnm B i) ^ 2
        ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2) ∧
    (∀ I : Finset (Fin n),
      (∑ i ∈ I, (sv hnm A i - sv hnm B i) ^ 2
          ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2) ∧
      (∑ i ∈ I, |sv hnm A i - sv hnm B i|
          ≤ Real.sqrt (I.card : ℝ) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B))) := by
  /- @proof-region region.target-node.session.6f9d63849667fea0 begin -/
  intro m n hnm A B
  have htrace_sv : ∀ X : Matrix (Fin m) (Fin n) ℝ,
      (X.transpose * X).trace = ∑ i : Fin n, sv hnm X i ^ 2 := by
    intro X
    have hreindex : ∑ i : Fin n, sv hnm X i ^ 2
        = ∑ i : Fin (min m n), Statlib.HighDim.MatrixAnalysis.singularValues X i ^ 2 := by
      refine Finset.sum_bij (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
        Fin.castLE (le_min hnm le_rfl) i) ?_ ?_ ?_ ?_
      · intro i _
        exact Finset.mem_univ _
      · intro i _ j _ hij
        exact Fin.ext (by simpa using congrArg Fin.val hij)
      · intro j _
        exact ⟨Fin.castLE (Nat.min_le_right m n) j, Finset.mem_univ _, by
          ext
          simp⟩
      · intro i _
        simp only [sv]
    rw [hreindex]
    exact ((Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation X).2.1).symm
  have hvn : (A.transpose * B).trace ≤ ∑ i : Fin n, sv hnm A i * sv hnm B i := by
    simpa only [sv] using statopia_math_node_3642284588_bdf66dbb m n hnm A B
  have hfrob_sq : Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2
      = ((A - B).transpose * (A - B)).trace := by
    simp only [Statlib.HighDim.MatrixAnalysis.frobeniusNorm]
    rw [Real.sq_sqrt (by positivity)]
    exact ((Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation (A - B)).2.2).symm
  have htrace_expand : ((A - B).transpose * (A - B)).trace
      = (A.transpose * A).trace - 2 * (A.transpose * B).trace
        + (B.transpose * B).trace := by
    have h1 : (A - B).transpose * (A - B)
        = A.transpose * A - A.transpose * B - (B.transpose * A - B.transpose * B) := by
      rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have h2 : (B.transpose * A).trace = (A.transpose * B).trace := by
      rw [← Matrix.trace_transpose (B.transpose * A), Matrix.transpose_mul,
        Matrix.transpose_transpose]
    rw [h1]
    simp only [Matrix.trace_sub]
    rw [h2]
    ring
  have hmain : ∑ i : Fin n, (sv hnm A i - sv hnm B i) ^ 2
      ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2 := by
    have hexp : ∑ i : Fin n, (sv hnm A i - sv hnm B i) ^ 2
        = (∑ i : Fin n, sv hnm A i ^ 2) + (∑ i : Fin n, sv hnm B i ^ 2)
          - 2 * ∑ i : Fin n, sv hnm A i * sv hnm B i := by
      have hpt : ∀ i : Fin n, (sv hnm A i - sv hnm B i) ^ 2
          = sv hnm A i ^ 2 + sv hnm B i ^ 2 - 2 * (sv hnm A i * sv hnm B i) :=
        fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexp, hfrob_sq, htrace_expand, htrace_sv A, htrace_sv B]
    linarith [hvn]
  have hFnn : (0 : ℝ) ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) := by
    simp only [Statlib.HighDim.MatrixAnalysis.frobeniusNorm]; positivity
  refine ⟨hmain, ?_⟩
  intro I
  have hsub : ∑ i ∈ I, (sv hnm A i - sv hnm B i) ^ 2
      ≤ Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun i _ _ => sq_nonneg (sv hnm A i - sv hnm B i))) hmain
  refine ⟨hsub, ?_⟩
  have hlen : (∑ i ∈ I, |sv hnm A i - sv hnm B i|) ^ 2
      ≤ (I.card : ℝ) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2 := by
    refine le_trans (sq_sum_le_card_mul_sum_sq (s := I)
      (f := fun i => |sv hnm A i - sv hnm B i|)) ?_
    simp only [sq_abs]
    exact mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg I.card)
  have hlen' : (∑ i ∈ I, |sv hnm A i - sv hnm B i|) ^ 2
      ≤ (Real.sqrt (I.card : ℝ)
          * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B)) ^ 2 := by
    calc (∑ i ∈ I, |sv hnm A i - sv hnm B i|) ^ 2
        ≤ (I.card : ℝ) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B) ^ 2 := hlen
      _ = (Real.sqrt (I.card : ℝ)
            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (A - B)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg I.card)]
  have hLnn : (0 : ℝ) ≤ ∑ i ∈ I, |sv hnm A i - sv hnm B i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (sv hnm A i - sv hnm B i))
  nlinarith [hlen', hLnn, mul_nonneg (Real.sqrt_nonneg (I.card : ℝ)) hFnn]
  /- @proof-region region.target-node.session.6f9d63849667fea0 end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_2382536492_f7c626d4


