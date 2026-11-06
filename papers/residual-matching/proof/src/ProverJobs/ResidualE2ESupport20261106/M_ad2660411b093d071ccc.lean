import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.Vocabulary.SVD
import Lean
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_ca782bc74b0775d6b6b6
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231
import ProverJobs.ResidualE2ESupport20261106.M_3f6faa1c6fc9a539d94b

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
theorem statopia_math_node_3786437948_943d4007 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) (k : Fin (min m n)),
    (Statlib.HighDim.MatrixAnalysis.singularValues (c • A) k
        = |c| * Statlib.HighDim.MatrixAnalysis.singularValues A k) ∧
    (Statlib.HighDim.Vocabulary.singularValues (c • A) k
        = |c| * Statlib.HighDim.Vocabulary.singularValues A k) ∧
    (0 ≤ c → Statlib.HighDim.MatrixAnalysis.singularValues (c • A) k
        = c * Statlib.HighDim.MatrixAnalysis.singularValues A k) ∧
    (0 ≤ c → Statlib.HighDim.Vocabulary.singularValues (c • A) k
        = c * Statlib.HighDim.Vocabulary.singularValues A k) ∧
    (∀ (hnm : n ≤ m) (i : Fin n), sv hnm (c • A) i = |c| * sv hnm A i) ∧
    (∀ (hnm : n ≤ m) (i : Fin n), 0 ≤ c → sv hnm (c • A) i = c * sv hnm A i) ∧
    (Statlib.HighDim.MatrixAnalysis.singularValues ((0 : ℝ) • A) k = 0) ∧
    (Statlib.HighDim.Vocabulary.singularValues ((0 : ℝ) • A) k = 0) ∧
    (Statlib.HighDim.MatrixAnalysis.singularValues ((1 : ℝ) • A) k
        = Statlib.HighDim.MatrixAnalysis.singularValues A k) ∧
    (Statlib.HighDim.Vocabulary.singularValues ((1 : ℝ) • A) k
        = Statlib.HighDim.Vocabulary.singularValues A k) := by
  /- @proof-region region.target-node.session.198876dea36a788a begin -/
  intro m n A c k
  have hmain : ∀ (c : ℝ) (k : Fin (min m n)),
      Statlib.HighDim.MatrixAnalysis.singularValues (c • A) k
        = |c| * Statlib.HighDim.MatrixAnalysis.singularValues A k := by
    intro c k
    have hanti : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (h : B.IsHermitian),
        Antitone (fun i => h.eigenvalues₀ i) := by
      intro B h
      unfold Matrix.IsHermitian.eigenvalues₀
      exact LinearMap.IsSymmetric.eigenvalues_antitone _ _
    have hantiMul : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (h : B.IsHermitian) (a : ℝ), 0 ≤ a →
        Antitone (fun i => a * h.eigenvalues₀ i) := by
      intro B h a ha i j hij
      exact mul_le_mul_of_nonneg_left (hanti B h hij) ha
    have hcanon : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (h₀ : B.IsHermitian),
        ∀ (h : ((c * c) • B).IsHermitian) (i : Fin (Fintype.card (Fin n))),
          h.eigenvalues₀ i = (c * c) * h₀.eigenvalues₀ i := by
      intro B h₀ h i
      exact statopia_math_node_3275750866_883f8e1a n ((c * c) • B) B h h₀ (c * c)
        (by nlinarith [sq_nonneg c]) rfl i
    have hEigScale : ∀ (B₁ B₀ : Matrix (Fin n) (Fin n) ℝ)
        (h₁ : B₁.IsHermitian) (h₀ : B₀.IsHermitian), B₁ = (c * c) • B₀ →
        ∀ i : Fin (Fintype.card (Fin n)), h₁.eigenvalues₀ i = (c * c) * h₀.eigenvalues₀ i := by
      intro B₁ B₀ h₁ h₀ hEq i
      subst hEq
      exact hcanon B₀ h₀ h₁ i
    have hmat : (c • A).conjTranspose * (c • A) = (c * c) • (A.conjTranspose * A) := by
      ext p q
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum, star_trivial]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    have hgen : ∀ (h₁ : ((c • A).conjTranspose * (c • A)).IsHermitian)
        (h₀ : (A.conjTranspose * A).IsHermitian) (i : Fin (Fintype.card (Fin n))),
        Real.sqrt (h₁.eigenvalues₀ i) = |c| * Real.sqrt (h₀.eigenvalues₀ i) := by
      intro h₁ h₀ i
      rw [hEigScale ((c • A).conjTranspose * (c • A)) (A.conjTranspose * A) h₁ h₀ hmat i,
        Real.sqrt_mul (by nlinarith [sq_nonneg c] : (0 : ℝ) ≤ c * c)]
      rw [show Real.sqrt (c * c) = |c| from by
        rw [show c * c = c ^ 2 from (pow_two c).symm, Real.sqrt_sq_eq_abs]]
    unfold Statlib.HighDim.MatrixAnalysis.singularValues
    exact hgen _ _ _
  have hmainv : ∀ (c : ℝ) (k : Fin (min m n)),
      Statlib.HighDim.Vocabulary.singularValues (c • A) k
        = |c| * Statlib.HighDim.Vocabulary.singularValues A k := by
    intro c k
    rw [← Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary (c • A) k,
      ← Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary A k]
    exact hmain c k
  have hne : Nonempty (Fin m) ∨ Nonempty (Fin n) := by
    have hpos : 0 < min m n := Nat.lt_of_le_of_lt (Nat.zero_le _) k.2
    refine Or.inl ⟨⟨0, ?_⟩⟩
    by_contra h
    have hm : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hm] at hpos
    simp at hpos
  have hrank0 : ∀ (k' : Fin (min m n)),
      Statlib.HighDim.MatrixAnalysis.singularValues (0 : Matrix (Fin m) (Fin n) ℝ) k' = 0 := by
    intro k'
    obtain ⟨-, -, -, htail⟩ :=
      Statlib.HighDim.MatrixAnalysis.singular_value_properties
        (0 : Matrix (Fin m) (Fin n) ℝ) hne
    exact htail k' (by rw [Matrix.rank_zero]; exact Nat.zero_lt_succ _)
  have hrank0v : ∀ (k' : Fin (min m n)),
      Statlib.HighDim.Vocabulary.singularValues (0 : Matrix (Fin m) (Fin n) ℝ) k' = 0 := by
    intro k'
    rw [← Statlib.HighDim.MatrixAnalysis.singularValues_eq_vocabulary]
    exact hrank0 k'
  refine ⟨hmain c k, hmainv c k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    rw [hmain c k, abs_of_nonneg hc]
  · intro hc
    rw [hmainv c k, abs_of_nonneg hc]
  · intro hnm i
    exact hmain c (Fin.castLE (le_min hnm le_rfl) i)
  · intro hnm i hc
    show Statlib.HighDim.MatrixAnalysis.singularValues (c • A)
        (Fin.castLE (le_min hnm le_rfl) i)
      = c * Statlib.HighDim.MatrixAnalysis.singularValues A
        (Fin.castLE (le_min hnm le_rfl) i)
    rw [hmain c (Fin.castLE (le_min hnm le_rfl) i), abs_of_nonneg hc]
  · rw [zero_smul]
    exact hrank0 k
  · rw [zero_smul]
    exact hrank0v k
  · rw [one_smul]
  · rw [one_smul]
  /- @proof-region region.target-node.session.198876dea36a788a end -/

end Statlib.Imported

end

#print axioms Statlib.Imported.statopia_math_node_3786437948_943d4007


