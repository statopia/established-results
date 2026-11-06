import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046
import ProverJobs.ResidualE2ESupport20261106.M_d0f032484907adf37baf

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3857640630_330b31cd : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hnm : n ≤ m) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) {Ωm : Type*}
    [MeasurableSpace Ωm] (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ) (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_int : ∀ i j, MeasureTheory.Integrable (Om i j) P)
    (hmom1 : Matrix.of (fun i k =>
        ∫ ω, (∑ j : Fin n,
            ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) *
              ((Om k j ω - p) / Real.sqrt ((m : ℝ) * p))) ∂P)
      = ((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
    (hmom2 : Matrix.of (fun j l =>
        ∫ ω, (∑ i : Fin m,
            ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) *
              ((Om i l ω - p) / Real.sqrt ((m : ℝ) * p))) ∂P)
      = (1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ)),
        Matrix.of (fun a b =>
            ∫ ω,
              (Matrix.reindex finSumFinEquiv finSumFinEquiv
                  (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                    (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)))
                    (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))).transpose
                    (0 : Matrix (Fin n) (Fin n) ℝ)) *
                Matrix.reindex finSumFinEquiv finSumFinEquiv
                  (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                    (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)))
                    (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))).transpose
                    (0 : Matrix (Fin n) (Fin n) ℝ))) a b ∂P) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
              (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
                          ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))) ∧
                  Real.sqrt (specNorm (Matrix.of (fun a b =>
                      ∫ ω,
                        (Matrix.reindex finSumFinEquiv finSumFinEquiv
                            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                              (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)))
                              (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))).transpose
                              (0 : Matrix (Fin n) (Fin n) ℝ)) *
                          Matrix.reindex finSumFinEquiv finSumFinEquiv
                            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ)
                              (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p)))
                              (Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))).transpose
                              (0 : Matrix (Fin n) (Fin n) ℝ))) a b ∂P))) = Real.sqrt (1 - p) := by
  /- @proof-region region.target-node.session.90ef3ba0da1d4555 begin -/
  intro m n hm hn hnm p hp0 hp1 Ωm _ P _ Om hOm_meas hOm_int hmom1 hmom2
  let Ξ : Ωm → Matrix (Fin m) (Fin n) ℝ := fun ω => Matrix.of (fun i j => (Om i j ω - p) / Real.sqrt ((m : ℝ) * p))
  let Y : Ωm → Matrix (Fin (m + n)) (Fin (m + n)) ℝ := fun ω =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose (0 : Matrix (Fin n) (Fin n) ℝ))
  have hsq : ∀ ω : Ωm, Y ω * Y ω = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Ξ ω * (Ξ ω).transpose) (0 : Matrix (Fin m) (Fin n) ℝ)
        (0 : Matrix (Fin n) (Fin m) ℝ) ((Ξ ω).transpose * (Ξ ω))) := by
    intro ω
    have hYY : Y ω = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ)) := rfl
    have hM : Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
          (0 : Matrix (Fin n) (Fin n) ℝ))
        = (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv)
          (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
            (0 : Matrix (Fin n) (Fin n) ℝ)) :=
      Matrix.reindexLinearEquiv_apply ℝ ℝ finSumFinEquiv finSumFinEquiv _
    calc Y ω * Y ω
        = (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) *
          (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
              (0 : Matrix (Fin n) (Fin n) ℝ))) := by
            rw [hYY, hM]
      _ = Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ) *
              Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) (Ξ ω) (Ξ ω).transpose
                (0 : Matrix (Fin n) (Fin n) ℝ)) := by
            rw [Matrix.reindexLinearEquiv_mul ℝ ℝ]
      _ = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (Ξ ω * (Ξ ω).transpose) (0 : Matrix (Fin m) (Fin n) ℝ)
              (0 : Matrix (Fin n) (Fin m) ℝ) ((Ξ ω).transpose * (Ξ ω))) := by
            rw [Matrix.fromBlocks_multiply, Matrix.reindexLinearEquiv_apply]
            simp
  have hC1 : Matrix.of (fun i k => ∫ ω, (Ξ ω * (Ξ ω).transpose) i k ∂P)
      = ((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    simpa [Ξ, Matrix.mul_apply] using hmom1
  have hC2 : Matrix.of (fun j l => ∫ ω, ((Ξ ω).transpose * (Ξ ω)) j l ∂P)
      = (1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [Ξ, Matrix.mul_apply] using hmom2
  have hCov : ∀ x y : Fin m ⊕ Fin n,
      (Matrix.of (fun a b => ∫ ω, (Y ω * Y ω) a b ∂P)) (finSumFinEquiv x) (finSumFinEquiv y)
        = (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
            (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
            ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))) x y := by
    intro x y
    have hpt : ∀ ω : Ωm, (Y ω * Y ω) (finSumFinEquiv x) (finSumFinEquiv y)
        = (Matrix.fromBlocks (Ξ ω * (Ξ ω).transpose) (0 : Matrix (Fin m) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin m) ℝ) ((Ξ ω).transpose * (Ξ ω))) x y := by
      intro ω
      rw [hsq ω, Matrix.reindex_apply, Matrix.submatrix_apply]
      simp
    show (∫ ω, (Y ω * Y ω) (finSumFinEquiv x) (finSumFinEquiv y) ∂P)
      = (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
          (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
          ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))) x y
    simp only [hpt]
    rcases x with i | j <;> rcases y with k | l
    · show (∫ ω, (Ξ ω * (Ξ ω).transpose) i k ∂P)
          = (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ)) i k
      exact congr_fun (congr_fun hC1 i) k
    · show (∫ ω, (0 : ℝ) ∂P) = 0
      simp
    · show (∫ ω, (0 : ℝ) ∂P) = 0
      simp
    · show (∫ ω, ((Ξ ω).transpose * (Ξ ω)) j l ∂P)
          = ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ)) j l
      exact congr_fun (congr_fun hC2 j) l
  have hcov : (Matrix.of (fun a b => ∫ ω, (Y ω * Y ω) a b ∂P))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
            (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
            ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
    ext a b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    simpa using hCov (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  refine ⟨hcov, ?_⟩
  change Real.sqrt (specNorm (Matrix.of (fun a b => ∫ ω, (Y ω * Y ω) a b ∂P)))
    = Real.sqrt (1 - p)
  rw [hcov]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp1nonneg : (0 : ℝ) ≤ 1 - p := by linarith
  have hA1 : (0 : ℝ) ≤ (n : ℝ) * (1 - p) / (m : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) hp1nonneg) (le_of_lt hmR)
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hA2 : (n : ℝ) * (1 - p) / (m : ℝ) ≤ 1 - p := by
    rw [div_le_iff₀ hmR]
    nlinarith [mul_le_mul_of_nonneg_right hnmR hp1nonneg]
  have hnorm := statopia_math_node_2432609000_515200a8 m n hn
    ((n : ℝ) * (1 - p) / (m : ℝ)) (1 - p) hA1 hA2
  have hspec : specNorm (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
        (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
        ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ))))
      = ‖Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ))
        (0 : Matrix (Fin m) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin m) ℝ)
        ((1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ)))‖ :=
    (Matrix.l2_opNorm_def _).symm
  rw [hspec, hnorm]
  /- @proof-region region.target-node.session.90ef3ba0da1d4555 end -/

end

end Statlib.Imported

