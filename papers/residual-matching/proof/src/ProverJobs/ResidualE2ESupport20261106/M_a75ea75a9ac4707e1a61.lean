import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_931591cefea10099d3b2
import ProverJobs.ResidualE2ESupport20261106.M_431237dd61193662d1a2

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace ResidualSparseRepair20261106.GaussianCalculus
open _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianResolventBounds _root_.PaperProofTasks.ResidualE2ESupport20261106.ResidualSparseRepair20261106.GaussianVariance

theorem matrix_trace_norm_le_l2 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ‖B.trace‖ ≤ (n : ℝ) * ‖B‖ := by
  calc
    ‖B.trace‖ ≤ ∑ i : Fin n, ‖B i i‖ := by
      simpa only [Matrix.trace, Matrix.diag_apply] using
        norm_sum_le Finset.univ (fun i : Fin n => B i i)
    _ ≤ ∑ _i : Fin n, ‖B‖ :=
      Finset.sum_le_sum (fun i _ => matrix_entry_le_l2_norm B i i)
    _ = _ := by simp

noncomputable def normalizedGramTrace {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) : ℂ :=
  (n : ℂ)⁻¹ * (gramResolvent A z).trace

noncomputable def normalizedGramSquareTrace {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) : ℂ :=
  (n : ℂ)⁻¹ * (gramResolvent A z * gramResolvent A z).trace

theorem normalized_gram_trace_bound {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    ‖normalizedGramTrace A z‖ ≤ z.im⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [normalizedGramTrace, norm_mul, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖(gramResolvent A z).trace‖
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖gramResolvent A z‖) := by
        gcongr
        exact matrix_trace_norm_le_l2 _
    _ = ‖gramResolvent A z‖ := by field_simp
    _ ≤ z.im⁻¹ := gram_resolvent_norm A z hz

theorem normalized_gram_square_trace_bound {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : 0 < z.im) :
    ‖normalizedGramSquareTrace A z‖ ≤ (z.im⁻¹) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [normalizedGramSquareTrace, norm_mul, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖(gramResolvent A z * gramResolvent A z).trace‖
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖gramResolvent A z * gramResolvent A z‖) := by
        gcongr
        exact matrix_trace_norm_le_l2 _
    _ = ‖gramResolvent A z * gramResolvent A z‖ := by field_simp
    _ ≤ ‖gramResolvent A z‖ * ‖gramResolvent A z‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (z.im⁻¹) ^ 2 := by
      rw [pow_two]
      gcongr <;> exact gram_resolvent_norm A z hz

theorem matrix_trace_continuous (n : ℕ) :
    Continuous (fun B : Matrix (Fin n) (Fin n) ℂ => B.trace) := by
  change Continuous (fun B : Matrix (Fin n) (Fin n) ℂ => ∑ i : Fin n, B i i)
  exact continuous_finset_sum _ (fun i _ => (matrixEntryCLM n n i i).continuous)

theorem normalized_gram_trace_continuous (m n : ℕ)
    (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => normalizedGramTrace A z) := by
  have hQ : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => gramResolvent A z) :=
    gramResolvent_continuous m n z hz
  exact continuous_const.mul ((matrix_trace_continuous n).comp hQ)

theorem normalized_gram_square_trace_continuous (m n : ℕ)
    (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => normalizedGramSquareTrace A z) := by
  have hQ : Continuous (fun A : Matrix (Fin m) (Fin n) ℂ => gramResolvent A z) :=
    gramResolvent_continuous m n z hz
  exact continuous_const.mul ((matrix_trace_continuous n).comp (hQ.mul hQ))

theorem normalized_gram_square_trace_integrable {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) (hX : Continuous X)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun ω => normalizedGramSquareTrace (X ω) z) μ := by
  apply Integrable.of_bound
    (((normalized_gram_square_trace_continuous m n z hz).comp hX).measurable.aestronglyMeasurable)
    ((z.im⁻¹) ^ 2)
  exact ae_of_all _ (fun ω => normalized_gram_square_trace_bound hn (X ω) z hz)

theorem gram_matrix_ofReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    gramMatrix (A.map Complex.ofReal) =
      (Statlib.RandomMatrix.sampleCovarianceMatrix A).map Complex.ofReal := by
  ext i j
  simp [gramMatrix, Statlib.RandomMatrix.sampleCovarianceMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Complex.real_smul, Complex.ofReal_sum, Complex.ofReal_mul]

theorem normalized_gram_trace_ofReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (z : ℂ) : normalizedGramTrace (A.map Complex.ofReal) z =
      normalizedCovarianceTrace A z := by
  simp only [normalizedGramTrace, gramResolvent, gram_matrix_ofReal,
    normalizedCovarianceTrace, covarianceTrace]

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.normalized_gram_square_trace_integrable
#print axioms ResidualSparseRepair20261106.GaussianCalculus.normalized_gram_trace_ofReal

