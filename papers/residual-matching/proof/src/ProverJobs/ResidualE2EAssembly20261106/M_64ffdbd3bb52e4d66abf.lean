import Lean
import ProverJobs.ResidualE2EAssembly20261106.M_17285beb91dc0986e103
import ProverJobs.ResidualE2EAssembly20261106.M_fa28e8f81da21b420c48

namespace PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_165f462a7e494b7a9c0f4fb377733656.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3302904835_67c2c5f7 : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (p : ℝ) (hp : p ≠ 0)
    (Om : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ (i : Fin m) (j : Fin n), Om i j = 0 ∨ Om i j = 1),
    (∀ (A B : Matrix (Fin m) (Fin n) ℝ), innerTrace A B = innerTrace B A) ∧
      (∀ (A B : Matrix (Fin m) (Fin n) ℝ),
        innerTrace (TOm p Om A) B = innerTrace A (TOm p Om B)) ∧
        (∀ (A : Matrix (Fin m) (Fin n) ℝ),
          p⁻¹ * frobSq (projMask Om A) - frobSq A = innerTrace (TOm p Om A) A) := by
  /- @proof-region region.target-node.session.b565cd57fd97cf0b begin -/
  intro m n hm hn p hp Om hOm
  have hT (C : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
      TOm p Om C i j = p⁻¹ * (Om i j * C i j) - C i j := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro A B
    simp only [innerTrace, mul_comm]
  · intro A B
    simp only [innerTrace, hT]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro A
    have hsq (i : Fin m) (j : Fin n) : Om i j ^ 2 = Om i j := by
      rcases hOm i j with h | h <;> simp [h]
    have hPAsq (i : Fin m) (j : Fin n) : projMask Om A i j ^ 2 = Om i j * A i j ^ 2 := by
      have h1 : projMask Om A i j = Om i j * A i j := rfl
      rw [h1]
      calc (Om i j * A i j) ^ 2 = Om i j ^ 2 * A i j ^ 2 := by ring
        _ = Om i j * A i j ^ 2 := by rw [hsq i j]
    simp only [frobSq, innerTrace, hT, hPAsq]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  /- @proof-region region.target-node.session.b565cd57fd97cf0b end -/

end

end Statlib.Imported

