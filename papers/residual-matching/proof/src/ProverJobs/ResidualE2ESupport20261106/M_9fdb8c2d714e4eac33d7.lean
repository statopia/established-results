import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPasturConvergence
import Statlib.RandomMatrix.Vocabulary.SpectralMeasure
import Statlib.RandomMatrix.Vocabulary.StieltjesTransform
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_39628c85a756d64b346a

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory
namespace ResidualSparseRepair20261106.GaussianCalculus
open Statlib.RandomMatrix Statlib.RandomMatrix.Vocabulary

theorem stieltjes_im_nonneg (μ : ProbabilityMeasure ℝ) (z : UpperHalfPlane) :
    0 ≤ (stieltjesTransform μ z).im := by
  have hm : Continuous (fun x : ℝ => ((x : ℂ) - (z : ℂ))⁻¹) := by
    apply (Complex.continuous_ofReal.sub continuous_const).inv₀
    intro x he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hh
    exact z.im_pos.ne' (neg_eq_zero.mp hh)
  have hi : Integrable (fun x : ℝ => ((x : ℂ) - (z : ℂ))⁻¹) (μ : Measure ℝ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable z.im⁻¹
    filter_upwards with x
    have hb : z.im ≤ ‖(x : ℂ) - (z : ℂ)‖ := by
      simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        UpperHalfPlane.coe_im, abs_of_pos z.im_pos] using Complex.abs_im_le_norm ((x : ℂ) - (z : ℂ))
    rw [norm_inv]
    exact inv_anti₀ z.im_pos hb
  have hpoint (x : ℝ) : 0 ≤ (((x : ℂ) - (z : ℂ))⁻¹).im := by
    simp only [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    exact div_nonneg z.im_pos.le (Complex.normSq_nonneg _)
  change 0 ≤ Complex.imCLM (∫ x : ℝ, ((x : ℂ) - (z : ℂ))⁻¹ ∂(μ : Measure ℝ))
  rw [← Complex.imCLM.integral_comp_comm hi]
  exact integral_nonneg hpoint

theorem sample_covariance_isHermitian {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (sampleCovarianceMatrix A).IsHermitian := by
  change ((1 / (m : ℝ)) • (A.transpose * A)).conjTranspose = _
  simp [sampleCovarianceMatrix]

theorem normalized_covariance_trace_im_nonneg {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (z : UpperHalfPlane) :
    0 ≤ (GaussianVariance.normalizedCovarianceTrace A (z : ℂ)).im := by
  have ht := stieltjesTransform_empiricalSpectralMeasure_eq_trace
    (show 0 < n by omega) (sampleCovarianceMatrix A) (sample_covariance_isHermitian A) z
  have hb := stieltjes_im_nonneg
    (empiricalSpectralMeasure (sampleCovarianceMatrix A) (sample_covariance_isHermitian A)) z
  rw [ht] at hb
  exact hb

theorem gaussian_mean_trace_im_nonneg (m n : ℕ) (hn : 1 ≤ n) (z : UpperHalfPlane) :
    0 ≤ (∫ ω, flatNormalizedTrace (m := m) (n := n) ω (z : ℂ)
      ∂(flatGaussianMeasure m n)).im := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by
    unfold flatGaussianMeasure; infer_instance
  have hi := (flat_normalized_trace_memLp m n hn (z : ℂ) z.im_pos).integrable (by norm_num)
  change 0 ≤ Complex.imCLM (∫ ω, flatNormalizedTrace (m := m) (n := n) ω (z : ℂ)
    ∂(flatGaussianMeasure m n))
  rw [← Complex.imCLM.integral_comp_comm hi]
  apply integral_nonneg
  intro ω
  change 0 ≤ (normalizedGramTrace ((realCoordinateMatrix ω).map Complex.ofReal) (z : ℂ)).im
  rw [normalized_gram_trace_ofReal]
  exact normalized_covariance_trace_im_nonneg hn (realCoordinateMatrix ω) z

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.gaussian_mean_trace_im_nonneg

