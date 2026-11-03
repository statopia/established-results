import Lean
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Vocabulary
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Base

namespace PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e

open _root_.PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1900557282_1188bc25 : ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (Prow : Measure ((Fin p → ℝ) × (Fin q → ℝ))) [IsProbabilityMeasure Prow]
    (f : (Fin q → ℝ) → (Fin p → ℝ))
    (M : Fin p → Fin q → ℝ)
    (hM : ∀ (i : Fin p) (j : Fin q),
      M i j = ∫ x : (Fin p → ℝ) × (Fin q → ℝ), (f x.2 i + x.1 i) * x.2 j ∂Prow)
    (hInt : ∀ (i : Fin p) (j : Fin q),
      Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => (f x.2 i + x.1 i) * x.2 j) Prow)
    (hIntE : ∀ (i : Fin p) (j : Fin q),
      Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i * x.2 j) Prow)
    (hZero : ∀ (i : Fin p) (j : Fin q),
      ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.1 i * x.2 j ∂Prow = 0),
    ∀ (i : Fin p) (j : Fin q),
      M i j = ∫ x : (Fin p → ℝ) × (Fin q → ℝ), f x.2 i * x.2 j ∂Prow := by
  /- @proof-region region.target-node.session.d208c43a5a5d9386 begin -/
  intro p q hp hq Prow hProw f M hM hInt hIntE hZero i j
  have hAint : Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i * x.2 j) Prow := by
    have h1 : Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
        (f x.2 i + x.1 i) * x.2 j - x.1 i * x.2 j) Prow :=
      (hInt i j).sub (hIntE i j)
    refine h1.congr ?_
    filter_upwards with x
    ring
  have hadd : (∫ x : (Fin p → ℝ) × (Fin q → ℝ), (f x.2 i + x.1 i) * x.2 j ∂Prow)
      = (∫ x : (Fin p → ℝ) × (Fin q → ℝ), f x.2 i * x.2 j ∂Prow)
        + ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.1 i * x.2 j ∂Prow := by
    have h : (fun x : (Fin p → ℝ) × (Fin q → ℝ) => (f x.2 i + x.1 i) * x.2 j)
        = fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i * x.2 j + x.1 i * x.2 j := by
      funext x
      ring
    rw [h]
    exact integral_add hAint (hIntE i j)
  rw [hM i j, hadd, hZero i j, add_zero]
  /- @proof-region region.target-node.session.d208c43a5a5d9386 end -/

end

end Statlib.Imported

