import ProverJobs.job_paper_383d12cb48d74c8f98648c6beef78bb3.Base

namespace PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

/-- Massart's bounded empirical-process tail bound for a countable index family. -/
axiom massart_countable_average_tail
    {Ω F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hF : Countable F) {n : ℕ} (hn : 0 < n)
    (W : Fin n → F → Ω → ℝ)
    (hW_meas : ∀ i f, Measurable (W i f))
    (hW_indep : iIndepFun (fun i => fun ω => fun f => W i f ω) μ)
    (b2 b3 t : ℝ) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (hW_bound : ∀ i f ω, |W i f ω| ≤ b2)
    (hW_mean : ∀ i f, ∫ ω, W i f ω ∂μ = 0)
    (hW_sq_int : ∀ i f, Integrable (fun ω => (W i f ω) ^ 2) μ)
    (hW_sq : ∀ i f, ∫ ω, (W i f ω) ^ 2 ∂μ ≤ b3)
    (ht : 0 < t) :
    μ.real {ω | (⨆ f : F, |(1 / (n : ℝ)) * ∑ i, W i f ω|) >
      2 * expectedSup μ (fun f ω' => |(1 / (n : ℝ)) * ∑ i, W i f ω'|)
        + Real.sqrt (8 * b3 * t / (n : ℝ)) + 35 * b2 * t / (n : ℝ)} ≤
      Real.exp (-t)

end PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3
