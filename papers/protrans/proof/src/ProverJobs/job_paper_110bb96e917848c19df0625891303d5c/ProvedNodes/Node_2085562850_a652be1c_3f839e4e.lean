import Lean
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.Vocabulary
import ProverJobs.job_paper_110bb96e917848c19df0625891303d5c.Base

namespace PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c

open _root_.PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2085562850_a652be1c : ∀ {ι Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : ι → Ω → α) (hP : ∀ i, Measurable (P i))
    (hindep : iIndepFun (fun i => P i) μ)
    (Ψ : ι → α → ℝ)
    (hΨ_rep : ∀ i, ∃ g : α → ℝ, Measurable g ∧
      Measure.map (P i) μ {x : α | Ψ i x ≠ g x} = 0)
    (hΨ : ∀ i, AEMeasurable (Ψ i) (Measure.map (P i) μ)),
    iIndepFun (fun i ω => Ψ i (P i ω)) μ := by
  /- @proof-region region.target-node.session.6773279675047f5a begin -/
  intro ι Ω α _ _ μ _ P hP_meas hP_indep Ψ hΨ_rep hΨ_ae
  exact iIndepFun.comp₀ hP_indep Ψ (fun i => (hP_meas i).aemeasurable) hΨ_ae
  /- @proof-region region.target-node.session.6773279675047f5a end -/

end Statlib.Imported

