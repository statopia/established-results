import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf

-- External DAG node: ext_model_4 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ)
    (hξ_nonneg : ∀ ω, 0 ≤ ξ ω)
    (hξ_meas : Measurable ξ)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (htail : ∀ x : ℝ, 0 ≤ x → P {ω | x < ξ ω} ≤ ENNReal.ofReal (A * Real.exp (- x / B))),
    ∀ t : ℝ, 0 ≤ t →
      ∫ ω, (ξ ω) ^ 3 * (if t < ξ ω then (1 : ℝ) else 0) ∂P
          ≤ 6 * A * (t + B) ^ 3 * Real.exp (- t / B)))
axiom ext_model_4 : (open MeasureTheory ProbabilityTheory in (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ)
    (hξ_nonneg : ∀ ω, 0 ≤ ξ ω)
    (hξ_meas : Measurable ξ)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (htail : ∀ x : ℝ, 0 ≤ x → P {ω | x < ξ ω} ≤ ENNReal.ofReal (A * Real.exp (- x / B))),
    ∀ t : ℝ, 0 ≤ t →
      ∫ ω, (ξ ω) ^ 3 * (if t < ξ ω then (1 : ℝ) else 0) ∂P
          ≤ 6 * A * (t + B) ^ 3 * Real.exp (- t / B)))

