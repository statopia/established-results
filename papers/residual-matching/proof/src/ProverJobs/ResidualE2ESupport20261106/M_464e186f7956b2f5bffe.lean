import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

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
theorem statopia_math_node_1519428770_08e15fe6 : ∀ (m n : ℕ) (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ),
    Statlib.HighDim.MatrixAnalysis.opNorm M = svals M ⟨0, hn⟩ ∧
      (∀ r : ℝ, svals M ⟨0, hn⟩ ≤ r ↔ Statlib.HighDim.MatrixAnalysis.opNorm M ≤ r) := by
  /- @proof-region region.target-node.session.de1a9f368f506317 begin -/
  have hbridge : ∀ {m n : ℕ} (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℝ) (hm : 0 < m),
      svals M ⟨0, hn⟩ =
        Statlib.HighDim.MatrixAnalysis.singularValues M ⟨0, Nat.lt_min.mpr ⟨hm, hn⟩⟩ := by
    intro m n hn M hm
    simp only [svals, Statlib.HighDim.MatrixAnalysis.singularValues]
    rfl
  intro m n hn M
  have hmain : Statlib.HighDim.MatrixAnalysis.opNorm M = svals M ⟨0, hn⟩ := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : Nonempty (Fin 1) := ⟨⟨0, Nat.zero_lt_one⟩⟩
      have hM0 : M = 0 := by
        ext i j
        exact Fin.elim0 i
      have hz0 : M.conjTranspose * M = (0 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp [Matrix.mul_apply]
      have hz1 : (0 : Matrix (Fin 1) (Fin n) ℝ).conjTranspose * (0 : Matrix (Fin 1) (Fin n) ℝ)
          = (0 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp [Matrix.mul_apply]
      have eigenvalues₀_congr : ∀ {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : A = B)
          (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card (Fin n))),
          hA.eigenvalues₀ i = hB.eigenvalues₀ i := by
        intro A B hAB hA hB i
        cases hAB
        rfl
      have svals_congr : ∀ {m₁ m₂ : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ)
          (B : Matrix (Fin m₂) (Fin n) ℝ), A.conjTranspose * A = B.conjTranspose * B →
          svals A ⟨0, hn⟩ = svals B ⟨0, hn⟩ := by
        intro m₁ m₂ A B hAB
        simp only [svals]
        exact congrArg Real.sqrt (eigenvalues₀_congr hAB _ _ _)
      have hsvn : (0 : Matrix (Fin n) (Fin n) ℝ).conjTranspose * (0 : Matrix (Fin n) (Fin n) ℝ)
          = (0 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        simp [Matrix.mul_apply]
      have hsv : svals M ⟨0, hn⟩ = svals (0 : Matrix (Fin n) (Fin n) ℝ) ⟨0, hn⟩ :=
        svals_congr M _ (hz0.trans hsvn.symm)
      have hz : ‖(0 : Matrix (Fin n) (Fin n) ℝ)‖ = 0 := norm_zero
      have hspec : svals (0 : Matrix (Fin n) (Fin n) ℝ) ⟨0, hn⟩ = 0 := by
        rw [hbridge hn (0 : Matrix (Fin n) (Fin n) ℝ) hn,
          (Statlib.HighDim.MatrixAnalysis.singular_value_properties (0 : Matrix (Fin n) (Fin n) ℝ)
            (Or.inr ⟨⟨0, hn⟩⟩)).1 (Nat.lt_min.mpr ⟨hn, hn⟩)]
        exact hz
      have hop : Statlib.HighDim.MatrixAnalysis.opNorm M = 0 := by
        rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
        have h := Matrix.l2_opNorm_conjTranspose_mul_self M
        rw [hz0] at h
        rw [hz] at h
        exact (mul_eq_zero.mp h.symm).elim id id
      rw [hsv, hspec, hop]
    · rw [Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2, hbridge hn M hm,
        (Statlib.HighDim.MatrixAnalysis.singular_value_properties M (Or.inr ⟨⟨0, hn⟩⟩)).1
          (Nat.lt_min.mpr ⟨hm, hn⟩)]
  refine ⟨hmain, ?_⟩
  intro r
  rw [hmain]

  /- @proof-region region.target-node.session.de1a9f368f506317 end -/

end Statlib.Imported

