import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_7d80961f4faa3f6a6bf5

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
theorem statopia_math_node_3509768721_4632c62e : ∀ (m n : ℕ) (hm : 16 ≤ m)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAmeas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => A ω i j)
    (hAint : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => A ω i j) μ)
    (hAmean : ∀ (i : Fin m) (j : Fin n), ∫ ω, A ω i j ∂μ = 0)
    (hAcov : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      ∫ ω, A ω i j * A ω k l ∂μ = if (i, j) = (k, l) then 1 / (m : ℝ) else 0)
    (hAprodint : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      Integrable (fun ω => A ω i j * A ω k l) μ),
    sSup {y : ℝ | ∃ v w : Fin (m + n) → ℝ,
      (∑ a : Fin (m + n), (v a) ^ 2 = 1 ∧ ∑ b : Fin (m + n), (w b) ^ 2 = 1) ∧
      y = Real.sqrt (∫ ω, ‖∑ a : Fin (m + n), ∑ b : Fin (m + n),
        (v a : ℂ) * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm) a b * (w b : ℂ)‖ ^ 2 ∂μ)} ≤ 1 := by
  /- @proof-region region.target-node.session.9653ce5698a0523b begin -/
  intro m n hm Ω _ μ _ A hAmeas hAint hAmean hAcov hAprodint
  apply Real.sSup_le
  · intro y hy
    obtain ⟨v, w, ⟨hv, hw⟩, rfl⟩ := hy
    rw [Real.sqrt_le_one]
    set b : Fin m → Fin n → ℝ := fun i j =>
      v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) +
      v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i)) with hbdef
    have sum_split : ∀ (g : Fin (m + n) → ℝ),
        (∑ a, g a) = (∑ i, g (finSumFinEquiv (Sum.inl i))) + ∑ j, g (finSumFinEquiv (Sum.inr j)) := by
      intro g
      rw [← Equiv.sum_comp finSumFinEquiv g, Fintype.sum_sum_type]
    have key : (∫ ω, ‖∑ a : Fin (m + n), ∑ b' : Fin (m + n),
        (v a : ℂ) * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm) a b' * (w b' : ℂ)‖ ^ 2 ∂μ)
        = (1 / (m : ℝ)) * ∑ i, ∑ j, (b i j) ^ 2 := by
      rw [statopia_math_node_4096280673_29405c81 m n μ A hAcov hAprodint v w]
    have hv1 : 0 ≤ ∑ i, (v (finSumFinEquiv (Sum.inl i))) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (v (finSumFinEquiv (Sum.inl i))))
    have hv2 : 0 ≤ ∑ j, (v (finSumFinEquiv (Sum.inr j))) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (v (finSumFinEquiv (Sum.inr j))))
    have hw1 : 0 ≤ ∑ i, (w (finSumFinEquiv (Sum.inl i))) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (w (finSumFinEquiv (Sum.inl i))))
    have hw2 : 0 ≤ ∑ j, (w (finSumFinEquiv (Sum.inr j))) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (w (finSumFinEquiv (Sum.inr j))))
    have hvsum : (∑ i, (v (finSumFinEquiv (Sum.inl i))) ^ 2) + (∑ j, (v (finSumFinEquiv (Sum.inr j))) ^ 2) = 1 := by
      rw [← sum_split (fun a => (v a) ^ 2)]; exact hv
    have hwsum : (∑ i, (w (finSumFinEquiv (Sum.inl i))) ^ 2) + (∑ j, (w (finSumFinEquiv (Sum.inr j))) ^ 2) = 1 := by
      rw [← sum_split (fun x => (w x) ^ 2)]; exact hw
    have hbterm : ∀ i j, (b i j) ^ 2 ≤ 2 * ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2) := by
      intro i j
      simp only [hbdef]
      nlinarith [sq_nonneg (v (finSumFinEquiv (Sum.inl i)) * w (finSumFinEquiv (Sum.inr j)) - v (finSumFinEquiv (Sum.inr j)) * w (finSumFinEquiv (Sum.inl i)))]
    have hb_le : ∑ i, ∑ j, (b i j) ^ 2 ≤ 2 := by
      have hP : (∑ i, ∑ j, (v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2) = (∑ i, (v (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (w (finSumFinEquiv (Sum.inr j))) ^ 2) :=
        (Fintype.sum_mul_sum (fun i => (v (finSumFinEquiv (Sum.inl i))) ^ 2) (fun j => (w (finSumFinEquiv (Sum.inr j))) ^ 2)).symm
      have hQ : (∑ i, ∑ j, (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2) = (∑ i, (w (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (v (finSumFinEquiv (Sum.inr j))) ^ 2) :=
        (Fintype.sum_mul_sum (fun i => (w (finSumFinEquiv (Sum.inl i))) ^ 2) (fun j => (v (finSumFinEquiv (Sum.inr j))) ^ 2)).symm
      have step1 : ∑ i, ∑ j, (b i j) ^ 2 ≤ ∑ i, ∑ j, 2 * ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hbterm i j
      have step2 : (∑ i, ∑ j, 2 * ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2)) = 2 * ((∑ i, (v (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (w (finSumFinEquiv (Sum.inr j))) ^ 2) + (∑ i, (w (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (v (finSumFinEquiv (Sum.inr j))) ^ 2)) := by
        have e1 : (∑ i, ∑ j, 2 * ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2)) = (∑ i, ∑ j, ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2)) + (∑ i, ∑ j, ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2)) := by
          simp only [two_mul, Finset.sum_add_distrib]
        rw [e1]
        simp only [Finset.sum_add_distrib, hP, hQ]
        ring
      have hcross : (∑ i, (v (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (w (finSumFinEquiv (Sum.inr j))) ^ 2) + (∑ i, (w (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (v (finSumFinEquiv (Sum.inr j))) ^ 2) ≤ 1 := by
        nlinarith [hvsum, hwsum, hv1, hv2, hw1, hw2, mul_nonneg hv1 hw1, mul_nonneg hv2 hw2]
      calc ∑ i, ∑ j, (b i j) ^ 2 ≤ ∑ i, ∑ j, 2 * ((v (finSumFinEquiv (Sum.inl i))) ^ 2 * (w (finSumFinEquiv (Sum.inr j))) ^ 2 + (w (finSumFinEquiv (Sum.inl i))) ^ 2 * (v (finSumFinEquiv (Sum.inr j))) ^ 2) := step1
        _ = 2 * ((∑ i, (v (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (w (finSumFinEquiv (Sum.inr j))) ^ 2) + (∑ i, (w (finSumFinEquiv (Sum.inl i))) ^ 2) * (∑ j, (v (finSumFinEquiv (Sum.inr j))) ^ 2)) := step2
        _ ≤ 2 := by nlinarith [hcross]
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by
      have h16 : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    calc (∫ ω, ‖∑ a : Fin (m + n), ∑ b' : Fin (m + n),
        (v a : ℂ) * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm) a b' * (w b' : ℂ)‖ ^ 2 ∂μ)
        = (1 / (m : ℝ)) * ∑ i, ∑ j, (b i j) ^ 2 := key
      _ ≤ (1 / (m : ℝ)) * 2 := by
          apply mul_le_mul_of_nonneg_left hb_le
          positivity
      _ ≤ 1 := by
          have h2 : (1 / (m : ℝ)) * 2 = 2 / (m : ℝ) := by ring
          rw [h2, div_le_one hmpos]
          linarith
  · norm_num
  /- @proof-region region.target-node.session.9653ce5698a0523b end -/

end Statlib.Imported

