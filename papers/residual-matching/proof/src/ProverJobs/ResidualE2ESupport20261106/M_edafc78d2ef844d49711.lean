import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Statlib.RandomMatrix.Vocabulary.Distributions
import Statlib.RandomMatrix.Vocabulary.StieltjesTransform
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_4ebde1490080e3345e15
import ProverJobs.ResidualE2ESupport20261106.M_a6dac61b78897832f17b
import ProverJobs.ResidualE2ESupport20261106.M_42376bcdfff0114fa6af
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory
open Statlib.RandomMatrix.Vocabulary

namespace ResidualSparseRepair20261106.DenseGaussian

/-- On the Bai window, the genuine MP transform is quantitatively determined by
its quadratic residual. Only the approximate transform's Herglotz sign is needed. -/
theorem mpMeasure_stieltjes_stability (rhoMinus rho : ℝ) (hmin : 0 < rhoMinus)
    (hlo : rhoMinus ≤ rho) (hhi : rho ≤ 1) (z : UpperHalfPlane)
    (hz1 : z.im ≤ 1) (hRe : |(z : ℂ).re| ≤ 20) (s : ℂ) (hs : 0 ≤ s.im)
    (δ : ℝ)
    (hδ : ‖(rho : ℂ) * (z : ℂ) * s ^ 2 + ((z : ℂ) + (rho : ℂ) - 1) * s + 1‖ ≤ δ) :
    ‖s - stieltjesTransform
        ⟨mpMeasure rho, Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho (lt_of_lt_of_le hmin hlo)⟩ z‖ ≤
      577 * δ / (rhoMinus * z.im ^ 2) := by
  have hρ : 0 < rho := lt_of_lt_of_le hmin hlo
  let q : ℂ := stieltjesTransform
    ⟨mpMeasure rho, Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho hρ⟩ z
  have hq : (rho : ℂ) * (z : ℂ) * q ^ 2 + ((z : ℂ) + (rho : ℂ) - 1) * q + 1 = 0 := by
    simpa only [q, mpSelfConsistentEquation] using
      Statlib.RandomMatrix.mpMeasure_stieltjesTransform_satisfies_SCE rho hρ z
  haveI : IsProbabilityMeasure (mpMeasure rho) :=
    Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho hρ
  have hqim : (1 / 577 : ℝ) * (z : ℂ).im ≤ q.im := by
    have hh := stieltjes_im_lower_bound (mpMeasure rho) 4 20 (by norm_num) (by norm_num)
      (z : ℂ) z.im_pos hz1 hRe (mpMeasure_support_four rho hρ hhi)
    norm_num only [show ((4 : ℝ) + 20) ^ 2 + 1 = 577 by norm_num, one_div] at hh
    exact hh
  have hh := mp_sce_stability rho (1 / 577) hρ hhi (by norm_num) (z : ℂ) q s
    z.im_pos hq hqim hs δ hδ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hden : 0 < rhoMinus * (1 / 577) * (z : ℂ).im ^ 2 := by
    exact mul_pos (mul_pos hmin (by norm_num)) (sq_pos_of_pos z.im_pos)
  have hdenle : rhoMinus * (1 / 577) * (z : ℂ).im ^ 2 ≤
      rho * (1 / 577) * (z : ℂ).im ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hlo (sq_nonneg (z : ℂ).im)]
  refine hh.trans ?_
  refine (div_le_div_of_nonneg_left hδ0 hden hdenle).trans_eq ?_
  simp only [UpperHalfPlane.coe_im]
  field_simp [ne_of_gt z.im_pos, ne_of_gt hmin]
  <;> ring

#print axioms mpMeasure_stieltjes_stability
end ResidualSparseRepair20261106.DenseGaussian

