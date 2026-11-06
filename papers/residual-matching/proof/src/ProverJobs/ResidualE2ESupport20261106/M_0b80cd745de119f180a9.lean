import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.Vocabulary.Distributions
import Statlib.RandomMatrix.Vocabulary.StieltjesTransform
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_e2ace8ffb503df853c92
import ProverJobs.ResidualE2ESupport20261106.M_9fdb8c2d714e4eac33d7
import ProverJobs.ResidualE2ESupport20261106.M_7dbef3b83a30566f0882
import ProverJobs.ResidualE2ESupport20261106.M_edafc78d2ef844d49711

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianVariance Statlib.RandomMatrix.Vocabulary

theorem gaussian_expected_trace_residual (rhoMinus : ℝ) (hmin : 0 < rhoMinus)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hratio : rhoMinus ≤ (n : ℝ) / m)
    (z : ℂ) (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hRe : |z.re| ≤ 20) :
    ‖(((n : ℝ) / (m : ℝ) : ℝ) : ℂ) * z *
        (∫ ω, flatNormalizedTrace (m := m) (n := n) ω z ∂(flatGaussianMeasure m n)) ^ 2 +
      (z + (((n : ℝ) / (m : ℝ) : ℝ) : ℂ) - 1) *
        (∫ ω, flatNormalizedTrace (m := m) (n := n) ω z ∂(flatGaussianMeasure m n)) + 1‖ ≤
      (42 / rhoMinus ^ 2 + 22) / ((m : ℝ) * z.im ^ 2) := by
  haveI : IsProbabilityMeasure (flatGaussianMeasure m n) := by
    unfold flatGaussianMeasure; infer_instance
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hrho0 : 0 ≤ (n : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hm0.le
  have hrho1 : (n : ℝ) / m ≤ 1 := (div_le_one hm0).2 hnm'
  apply mp_quadratic_residual_on_window (flatGaussianMeasure m n)
    (fun ω => flatNormalizedTrace ω z) (fun ω => flatNormalizedSquareTrace ω z)
    (flat_normalized_trace_memLp m n hn z hz)
    (flat_normalized_square_trace_integrable m n hn z hz)
    rhoMinus ((n : ℝ) / m) hmin hrho0 hrho1 m hm z hz hz1 hRe
  · exact ae_of_all _ (fun ω => normalized_gram_trace_bound hn (coordinateMatrix ω) z hz)
  · exact ae_of_all _ (fun ω => normalized_gram_square_trace_bound hn (coordinateMatrix ω) z hz)
  · simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
      gaussian_exact_loop_equation m n hm hn z hz
  · exact flat_normalized_gram_trace_variance_aspect rhoMinus hmin m n hm hn hratio z hz

theorem gaussian_expected_trace_mp_bound (rhoMinus : ℝ) (hmin : 0 < rhoMinus)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hratio : rhoMinus ≤ (n : ℝ) / m)
    (z : UpperHalfPlane) (hz1 : z.im ≤ 1) (hRe : |(z : ℂ).re| ≤ 20) :
    ‖(∫ ω, flatNormalizedTrace (m := m) (n := n) ω (z : ℂ)
        ∂(flatGaussianMeasure m n)) -
      stieltjesTransform
        ⟨mpMeasure ((n : ℝ) / m),
          Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure ((n : ℝ) / m)
            (lt_of_lt_of_le hmin hratio)⟩ z‖ ≤
      (577 * (42 / rhoMinus ^ 2 + 22) / rhoMinus) / ((m : ℝ) * z.im ^ 4) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrho1 : (n : ℝ) / m ≤ 1 := (div_le_one hm0).2 (by exact_mod_cast hnm)
  have hh := DenseGaussian.mpMeasure_stieltjes_stability rhoMinus ((n : ℝ) / m)
    hmin hratio hrho1 z hz1 hRe
    (∫ ω, flatNormalizedTrace (m := m) (n := n) ω (z : ℂ) ∂(flatGaussianMeasure m n))
    (gaussian_mean_trace_im_nonneg m n hn z)
    ((42 / rhoMinus ^ 2 + 22) / ((m : ℝ) * z.im ^ 2))
    (gaussian_expected_trace_residual rhoMinus hmin m n hm hn hnm hratio
      (z : ℂ) z.im_pos hz1 hRe)
  refine hh.trans_eq ?_
  field_simp
  <;> ring

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.gaussian_expected_trace_mp_bound

