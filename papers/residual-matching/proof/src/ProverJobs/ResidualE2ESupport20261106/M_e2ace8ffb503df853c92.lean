import Lean
import ProverJobs.ResidualE2ESupport20261106.M_a75ea75a9ac4707e1a61

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianVariance

private theorem realCoordinateMatrix_measurable (m n : ℕ) :
    Measurable (realCoordinateMatrix (m := m) (n := n)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => measurable_pi_apply _

theorem flat_normalized_gram_trace_mean (m n : ℕ) (z : ℂ) :
    (∫ ω : Fin (m * n) → ℝ, normalizedGramTrace (coordinateMatrix ω) z ∂flatGaussianMeasure m n) =
      ∫ A : Matrix (Fin m) (Fin n) ℝ, normalizedCovarianceTrace A z ∂stdNormalMatrixMeasure m n := by
  have hpoint (ω : Fin (m * n) → ℝ) : normalizedGramTrace (coordinateMatrix ω) z =
      normalizedCovarianceTrace (realCoordinateMatrix ω) z :=
    normalized_gram_trace_ofReal (realCoordinateMatrix ω) z
  simp_rw [hpoint]
  rw [← realCoordinateMatrix_map_gaussian m n]
  exact (integral_map (realCoordinateMatrix_measurable m n).aemeasurable
    (normalizedCovarianceTrace_measurable z).aestronglyMeasurable).symm

theorem flat_normalized_gram_trace_variance_eq (m n : ℕ) (z : ℂ) :
    (∫ ω : Fin (m * n) → ℝ,
        ‖normalizedGramTrace (coordinateMatrix ω) z -
          ∫ v : Fin (m * n) → ℝ, normalizedGramTrace (coordinateMatrix v) z
            ∂flatGaussianMeasure m n‖ ^ 2 ∂flatGaussianMeasure m n) =
      ∫ A : Matrix (Fin m) (Fin n) ℝ,
        ‖normalizedCovarianceTrace A z -
          ∫ B : Matrix (Fin m) (Fin n) ℝ, normalizedCovarianceTrace B z
            ∂stdNormalMatrixMeasure m n‖ ^ 2 ∂stdNormalMatrixMeasure m n := by
  have hpoint (ω : Fin (m * n) → ℝ) : normalizedGramTrace (coordinateMatrix ω) z =
      normalizedCovarianceTrace (realCoordinateMatrix ω) z :=
    normalized_gram_trace_ofReal (realCoordinateMatrix ω) z
  rw [flat_normalized_gram_trace_mean]
  simp_rw [hpoint]
  let a : ℂ := ∫ B : Matrix (Fin m) (Fin n) ℝ, normalizedCovarianceTrace B z ∂stdNormalMatrixMeasure m n
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => ‖normalizedCovarianceTrace A z - a‖ ^ 2) :=
    ((normalizedCovarianceTrace_measurable z).sub measurable_const).norm.pow_const 2
  have h := (integral_map (μ := flatGaussianMeasure m n) (realCoordinateMatrix_measurable m n).aemeasurable
    hf.aestronglyMeasurable).symm
  rw [realCoordinateMatrix_map_gaussian m n] at h
  exact h

theorem flat_normalized_gram_trace_variance (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    (∫ ω : Fin (m * n) → ℝ,
        ‖normalizedGramTrace (coordinateMatrix ω) z -
          ∫ v : Fin (m * n) → ℝ, normalizedGramTrace (coordinateMatrix v) z
            ∂flatGaussianMeasure m n‖ ^ 2 ∂flatGaussianMeasure m n)
      ≤ 2 * (m : ℝ) / ((n : ℝ) ^ 2 * z.im ^ 2) := by
  rw [flat_normalized_gram_trace_variance_eq]
  exact gaussian_normalized_trace_variance m n hn z hz

theorem flat_normalized_gram_trace_variance_aspect (rhoMinus : ℝ) (hrho : 0 < rhoMinus)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hratio : rhoMinus ≤ (n : ℝ) / (m : ℝ)) (z : ℂ) (hz : 0 < z.im) :
    (∫ ω : Fin (m * n) → ℝ,
        ‖normalizedGramTrace (coordinateMatrix ω) z -
          ∫ v : Fin (m * n) → ℝ, normalizedGramTrace (coordinateMatrix v) z
            ∂flatGaussianMeasure m n‖ ^ 2 ∂flatGaussianMeasure m n)
      ≤ (2 / rhoMinus ^ 2) / ((m : ℝ) * z.im ^ 2) := by
  rw [flat_normalized_gram_trace_variance_eq]
  exact gaussian_normalized_trace_variance_aspect rhoMinus hrho m n hm hn hratio z hz

#print axioms flat_normalized_gram_trace_mean
#print axioms flat_normalized_gram_trace_variance
#print axioms flat_normalized_gram_trace_variance_aspect
end ResidualSparseRepair20261106.GaussianCalculus

