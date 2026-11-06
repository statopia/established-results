import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_0314001920a67b69ef1c

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000

namespace ResidualSparseRepair20261106.GaussianTail

/-- Flattening a matrix of independent standard normal entries gives the canonical product law. -/
theorem gaussian_flat_map {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hGm : ∀ i j, Measurable fun ω => G ω i j)
    (hGi : iIndepFun (fun ij : Fin m × Fin n => fun ω => G ω ij.1 ij.2) μ)
    (hGs : ∀ i j, Measure.map (fun ω => G ω i j) μ = gaussianReal 0 1) :
    Measure.map (fun ω => fun ij : Fin m × Fin n => G ω ij.1 ij.2) μ = canonicalMeasure m n := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun ij : Fin m × Fin n => (hGm ij.1 ij.2).aemeasurable)).mp hGi
  simpa only [hGs, canonicalMeasure] using h

/-- The scalar covariance outlier budget for any actual iid standard Gaussian matrix. -/
theorem gaussian_covariance_tail {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hGm : ∀ i j, Measurable fun ω => G ω i j)
    (hGi : iIndepFun (fun ij : Fin m × Fin n => fun ω => G ω ij.1 ij.2) μ)
    (hGs : ∀ i j, Measure.map (fun ω => G ω i j) μ = gaussianReal 0 1)
    (hm : 1 ≤ m) (hnm : n ≤ m) :
    Integrable (fun ω => Statlib.HighDim.MatrixAnalysis.opNorm (G ω) ^ 2) μ ∧
    Integrable (fun ω => max (Statlib.HighDim.MatrixAnalysis.opNorm (G ω) ^ 2 / (m : ℝ) - 4) 0) μ ∧
    (∫ ω, max (Statlib.HighDim.MatrixAnalysis.opNorm (G ω) ^ 2 / (m : ℝ) - 4) 0 ∂μ) ≤
      24 / Real.sqrt (m : ℝ) := by
  let Φ : Ω → ((Fin m × Fin n) → ℝ) := fun ω ij => G ω ij.1 ij.2
  have hmΦ : Measurable Φ := measurable_pi_iff.mpr fun ij => hGm ij.1 ij.2
  have hmap : Measure.map Φ μ = canonicalMeasure m n := gaussian_flat_map μ G hGm hGi hGs
  have hnorm (ω) : matrixNorm (Φ ω) = Statlib.HighDim.MatrixAnalysis.opNorm (G ω) := rfl
  obtain ⟨hi2, hiE, hb⟩ := canonical_covariance_tail m n hm hnm
  have hi2' : Integrable (fun g => matrixNorm g ^ 2) (Measure.map Φ μ) := by rwa [hmap]
  have hiE' : Integrable (fun g => max (matrixNorm g ^ 2 / (m : ℝ) - 4) 0)
      (Measure.map Φ μ) := by rwa [hmap]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_def, hnorm] using hi2'.comp_measurable hmΦ
  · simpa only [Function.comp_def, hnorm] using hiE'.comp_measurable hmΦ
  · have heq := integral_map hmΦ.aemeasurable hiE'.aestronglyMeasurable
    rw [hmap] at heq
    simpa only [hnorm] using heq ▸ hb

#print axioms gaussian_flat_map
#print axioms gaussian_covariance_tail
end ResidualSparseRepair20261106.GaussianTail

