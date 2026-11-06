import Statlib.HighDim.MatrixAnalysis.FrobeniusNormSvdRelation
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.HighDim.MatrixRecovery.MatrixRipRecoveryBound
import Statlib.HighDim.Vocabulary.SVD
import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_13128476a96508fa7e2e
import ProverJobs.ResidualE2EAssembly20261106.M_b8e5edcf2347c67d3548

namespace PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_residual_matching.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false in
theorem statopia_math_node_3416671836_4f7362e6 : ∀ (m n r : ℕ)
    (Om M0 M : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ i j, Om i j = 0 ∨ Om i j = 1)
    (hrank : Matrix.rank (M - M0) ≤ 2 * r),
    (frobNorm (projMask Om (M - M0))) ^ 2 ≤
      Real.sqrt (2 * (r : ℝ)) * frobNorm (M - M0) *
        spectralNorm (projMask Om (M - M0)) := by
  /- @proof-region region.target-node.session.4ba0c0b636f649bc begin -/
  intro m n r Om M0 M hOm hrank
  by_cases hmn : 0 < min m n
  · set Δ : Matrix (Fin m) (Fin n) ℝ := M - M0 with hΔ
    set A : Matrix (Fin m) (Fin n) ℝ := projMask Om Δ with hA
    have hrank' : Δ.rank ≤ 2 * r := by simpa only [← hΔ] using hrank
    have hAdiag : ∀ i j, A i j * A i j = A i j * Δ i j := by
      intro i j
      rw [hA]
      unfold projMask
      rcases hOm i j with h | h <;> simp [h]
    have hAA : Statlib.HighDim.MatrixAnalysis.traceInner A A
        = Statlib.HighDim.MatrixAnalysis.traceInner Δ A := by
      unfold Statlib.HighDim.MatrixAnalysis.traceInner
      unfold Matrix.trace
      try unfold Matrix.diag
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        (hAdiag j i).trans (mul_comm (A j i) (Δ j i))))
    have hfrob : frobNorm A ^ 2 = Statlib.HighDim.MatrixAnalysis.traceInner A A := by
      unfold frobNorm Statlib.HighDim.MatrixAnalysis.frobeniusNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => sq_nonneg (A i j))))]
      unfold Statlib.HighDim.MatrixAnalysis.traceInner
      exact ((Statlib.HighDim.MatrixAnalysis.frobenius_norm_svd_relation A).2.2).symm
    have hop : Statlib.HighDim.MatrixAnalysis.opNorm A = spectralNorm A := by
      rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
      unfold spectralNorm
      rw [dif_pos hmn]
      have hne : Nonempty (Fin m) := ⟨⟨0, Nat.lt_of_lt_of_le hmn (Nat.min_le_left m n)⟩⟩
      exact ((Statlib.HighDim.MatrixAnalysis.singular_value_properties A (Or.inl hne)).1 hmn).symm
    have hspec_nonneg : 0 ≤ spectralNorm A := by
      unfold spectralNorm
      rw [dif_pos hmn]
      have hne : Nonempty (Fin m) := ⟨⟨0, Nat.lt_of_lt_of_le hmn (Nat.min_le_left m n)⟩⟩
      exact (Statlib.HighDim.MatrixAnalysis.singular_value_properties A (Or.inl hne)).2.1 ⟨0, hmn⟩
    have hQ : frobNorm A ^ 2 ≤ Statlib.HighDim.Vocabulary.nuclearNorm Δ * spectralNorm A := by
      rw [hfrob, hAA]
      calc Statlib.HighDim.MatrixAnalysis.traceInner Δ A
          ≤ Statlib.HighDim.Vocabulary.nuclearNorm Δ * Statlib.HighDim.MatrixAnalysis.opNorm A :=
            Statlib.HighDim.MatrixAnalysis.trace_dual_nuclear_op Δ A
        _ = Statlib.HighDim.Vocabulary.nuclearNorm Δ * spectralNorm A := by rw [hop]
    have hnu : Statlib.HighDim.Vocabulary.nuclearNorm Δ ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm Δ := by
      have h := Statlib.HighDim.MatrixRecovery.nuclearNorm_le_sqrt_two_mul_rank_mul_frobenius_of_rank_le
        (T := Δ) hrank'
      simpa [frobNorm] using h
    calc frobNorm A ^ 2
        ≤ Statlib.HighDim.Vocabulary.nuclearNorm Δ * spectralNorm A := hQ
      _ ≤ (Real.sqrt (2 * (r : ℝ)) * frobNorm Δ) * spectralNorm A :=
          mul_le_mul_of_nonneg_right hnu hspec_nonneg
      _ = Real.sqrt (2 * (r : ℝ)) * frobNorm Δ * spectralNorm A := by ring_nf
  · have hmin0 : min m n = 0 := Nat.eq_zero_of_not_pos hmn
    have hspec0 : spectralNorm (projMask Om (M - M0)) = 0 := by
      unfold spectralNorm
      exact dif_neg hmn
    have hA0 : projMask Om (M - M0) = 0 := by
      rcases Nat.min_eq_zero_iff.1 hmin0 with hm0 | hn0
      · ext i j
        exact absurd i.isLt (by omega)
      · ext i j
        exact absurd j.isLt (by omega)
    have hfrob0 : frobNorm (projMask Om (M - M0)) = 0 := by
      rw [hA0]
      simp [frobNorm, Statlib.HighDim.MatrixAnalysis.frobeniusNorm]
    rw [hfrob0, hspec0]
    simp
  /- @proof-region region.target-node.session.4ba0c0b636f649bc end -/

end Statlib.Imported

