import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2490289310_a8cb3761_ef64bef0
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

-- External DAG node: ext_model_2 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (open scoped BigOperators ENNReal in (∀ (b : ℝ), 0 < b →
      ∃ C : ℝ, 0 < C ∧
        ∀ (p : ℕ) (hp : 3 ≤ p) (μ_Y : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ_Y],
          ProbabilityTheory.IsGaussian μ_Y →
          (∫ y, y ∂μ_Y = fun _ => (0 : ℝ)) →
          (∀ j : Fin p, b ≤ ∫ y, (y j) ^ 2 ∂μ_Y) →
          ∀ (y : Fin p → ℝ) (a : ℝ), 0 < a →
            (μ_Y {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j + a}).toReal -
                (μ_Y {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j}).toReal ≤
              C * a * Real.sqrt (Real.log (p : ℝ)))))
theorem ext_model_2 : (open MeasureTheory ProbabilityTheory in (open scoped BigOperators ENNReal in (∀ (b : ℝ), 0 < b →
      ∃ C : ℝ, 0 < C ∧
        ∀ (p : ℕ) (hp : 3 ≤ p) (μ_Y : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ_Y],
          ProbabilityTheory.IsGaussian μ_Y →
          (∫ y, y ∂μ_Y = fun _ => (0 : ℝ)) →
          (∀ j : Fin p, b ≤ ∫ y, (y j) ^ 2 ∂μ_Y) →
          ∀ (y : Fin p → ℝ) (a : ℝ), 0 < a →
            (μ_Y {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j + a}).toReal -
                (μ_Y {z : Fin p → ℝ | ∀ j : Fin p, z j ≤ y j}).toReal ≤
              C * a * Real.sqrt (Real.log (p : ℝ))))) := by
  exact Statlib.Imported.statopia_math_node_2490289310_a8cb3761

