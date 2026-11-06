import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.Vocabulary.Distributions
import Statlib.RandomMatrix.Vocabulary.StieltjesTransform
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_0b80cd745de119f180a9
import ProverJobs.ResidualE2ESupport20261106.M_e56a536fb60164c1d909
import ProverJobs.ResidualE2ESupport20261106.M_72c3ed5da738fdd670a7
import ProverJobs.ResidualE2ESupport20261106.M_402934599e9a55c6d176

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
namespace ResidualSparseRepair20261106.DenseGaussian
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianCalculus _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianTail Statlib.RandomMatrix.Vocabulary

theorem gaussian_covariance_cdf_polynomial_rate (rhoMinus : ℝ) (hmin : 0 < rhoMinus) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n → n ≤ m →
      rhoMinus ≤ (n : ℝ) / m → ∀ x : ℝ,
        |measureCDF (gaussianExpectedCovariance m n) x -
          measureCDF (mpMeasure ((n : ℝ) / m)) x| ≤
          C * Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) := by
  let K := 577 * (42 / rhoMinus ^ 2 + 22) / rhoMinus
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨Csm, hCsm, hsm⟩ := bai_smoothing_holder_half (2 / (Real.pi * rhoMinus)) (by positivity)
  refine ⟨Csm * (40 * K + 25), mul_pos (by linarith) (by positivity), ?_⟩
  intro m n hm hn hnm hratio x
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmgt : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  let rho : ℝ := (n : ℝ) / m
  have hrho : 0 < rho := lt_of_lt_of_le hmin hratio
  have hrho1 : rho ≤ 1 := (div_le_one hm0).2 (by exact_mod_cast hnm)
  let μ := gaussianExpectedCovariance m n
  let ν := mpMeasure rho
  haveI : IsProbabilityMeasure μ := gaussianExpectedCovariance_probability m n hn
  haveI : IsProbabilityMeasure ν := Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho hrho
  obtain ⟨htail, htailBound⟩ := gaussianExpectedCovariance_tail m n hm1 hn hnm rho hrho hrho1
  let η := Real.rpow (m : ℝ) (-(2 / 9 : ℝ))
  obtain ⟨hη, hη1, hsqrt, hden, htailExp⟩ := gaussian_smoothing_exponents (m : ℝ) hmgt
  change 0 < η at hη
  change η < 1 at hη1
  change Real.sqrt η = Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) at hsqrt
  change 1 / ((m : ℝ) * η ^ 4) = Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) at hden
  change η⁻¹ / Real.sqrt (m : ℝ) ≤ Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) at htailExp
  have hpt (u : ℝ) (hu : |u| ≤ 20) :
      ‖(∫ y, ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
        (∫ y, ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖ ≤
        K / ((m : ℝ) * η ^ 4) := by
    let z : UpperHalfPlane := ⟨(u : ℂ) + (η : ℂ) * Complex.I, by simpa using hη⟩
    have hz : z.im = η := by
      change ((u : ℂ) + (η : ℂ) * Complex.I).im = η
      simp
    have hzRe : (z : ℂ).re = u := by simp [z]
    have hh := gaussian_expected_trace_mp_bound rhoMinus hmin m n hm1 hn hnm hratio z
      (by rw [hz]; exact hη1.le) (by rw [hzRe]; exact hu)
    simp only [flatNormalizedTrace] at hh
    rw [flat_normalized_gram_trace_mean,
      ← gaussianExpectedCovariance_stieltjes m n hn (z : ℂ) z.im_pos] at hh
    have he (y : ℝ) : ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I) =
        (y : ℂ) - (z : ℂ) := by
      change (y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I =
        (y : ℂ) - ((u : ℂ) + (η : ℂ) * Complex.I)
      ring
    simp_rw [he]
    simpa only [stieltjesTransform, hz, μ, ν, rho, K] using hh
  have hL1 : (∫ u in (-20 : ℝ)..20,
      ‖(∫ y, ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
        (∫ y, ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖) ≤
      (K / ((m : ℝ) * η ^ 4)) * 40 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u : ℝ =>
        ‖(∫ y, ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
          (∫ y, ((y : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖)
      (a := (-20 : ℝ)) (b := 20) (C := K / ((m : ℝ) * η ^ 4)) (by
        intro u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        apply hpt
        have hmem : u ∈ Set.Ioc (-20 : ℝ) 20 := by simpa using hu
        exact abs_le.mpr ⟨hmem.1.le, hmem.2⟩)
    rw [show |(20 : ℝ) - (-20)| = 40 by norm_num, Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh
  have hBai := hsm μ ν (mpMeasure_cdf_holder_half rhoMinus rho hmin hratio hrho1)
    htail η hη hη1
  have hbd : BddAbove (Set.range fun y : ℝ => |measureCDF μ y - measureCDF ν y|) := by
    refine ⟨1, ?_⟩
    rintro a ⟨y, rfl⟩
    have hμ : measureCDF μ y = cdf μ y := (cdf_eq_real μ y).symm
    have hν : measureCDF ν y = cdf ν y := (cdf_eq_real ν y).symm
    change |measureCDF μ y - measureCDF ν y| ≤ 1
    rw [hμ, hν, abs_le]
    constructor <;> linarith [cdf_nonneg μ y, cdf_le_one μ y, cdf_nonneg ν y, cdf_le_one ν y]
  refine (le_csSup hbd (Set.mem_range_self x)).trans (hBai.trans ?_)
  have hηnonneg : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  have hCnonneg : 0 ≤ Csm := by linarith
  have htailSmall : η⁻¹ * (24 / Real.sqrt (m : ℝ)) ≤
      24 * Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) := by
    calc _ = 24 * (η⁻¹ / Real.sqrt (m : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htailExp (by norm_num)
  calc
    _ ≤ Csm * ((K / ((m : ℝ) * η ^ 4)) * 40 + Real.sqrt η +
        η⁻¹ * (24 / Real.sqrt (m : ℝ))) := by
      gcongr
      exact htailBound
    _ ≤ Csm * ((K * Real.rpow (m : ℝ) (-(1 / 9 : ℝ))) * 40 +
        Real.rpow (m : ℝ) (-(1 / 9 : ℝ)) + 24 * Real.rpow (m : ℝ) (-(1 / 9 : ℝ))) := by
      rw [hsqrt, div_eq_mul_one_div K, hden]
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl htailSmall) hCnonneg
    _ = _ := by ring

end ResidualSparseRepair20261106.DenseGaussian

#print axioms ResidualSparseRepair20261106.DenseGaussian.gaussian_covariance_cdf_polynomial_rate

