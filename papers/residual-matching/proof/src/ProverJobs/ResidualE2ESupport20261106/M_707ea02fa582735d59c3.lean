import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.Vocabulary.Distributions
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_bcea7c3a4846305ca98f
import ProverJobs.ResidualE2ESupport20261106.M_25b575e712786d8e5814

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory
namespace ResidualSparseRepair20261106.DenseGaussian
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianTail Statlib.RandomMatrix.Vocabulary

theorem gaussian_sym_sqrt_cdf_polynomial_rate (rhoMinus : ℝ) (hmin : 0 < rhoMinus) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n → n ≤ m →
      rhoMinus ≤ (n : ℝ) / m → ∀ x : ℝ,
        |(symmetricSqrtMeasure (gaussianExpectedCovariance m n)).real (Set.Iic x) -
          (symmetricSqrtMeasure (mpMeasure ((n : ℝ) / m))).real (Set.Iic x)| ≤
          C * Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := gaussian_covariance_cdf_polynomial_rate rhoMinus hmin
  refine ⟨C, hC, ?_⟩
  intro m n hm hn hnm hratio x
  haveI : IsProbabilityMeasure (gaussianExpectedCovariance m n) :=
    gaussianExpectedCovariance_probability m n hn
  haveI : IsProbabilityMeasure (mpMeasure ((n : ℝ) / m)) :=
    Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure ((n : ℝ) / m)
      (lt_of_lt_of_le hmin hratio)
  have hh := symmetricSqrtMeasure_kolmogorov_le_half
    (gaussianExpectedCovariance m n) (mpMeasure ((n : ℝ) / m))
    (C * Real.rpow (m : ℝ) (-(1 / 9 : ℝ)))
    (hbound m n hm hn hnm hratio) x
  have he : 0 ≤ C * Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) :=
    mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

end ResidualSparseRepair20261106.DenseGaussian

#print axioms ResidualSparseRepair20261106.DenseGaussian.gaussian_sym_sqrt_cdf_polynomial_rate

