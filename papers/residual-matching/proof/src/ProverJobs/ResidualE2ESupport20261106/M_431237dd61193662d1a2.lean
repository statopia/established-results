import Lean
import ProverJobs.ResidualE2ESupport20261106.M_627769f17e264af810a3

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
namespace ResidualSparseRepair20261106.GaussianVariance

/-- All normalized resolvent traces under the canonical real Gaussian measure are square integrable. -/
theorem gaussian_normalized_trace_memLp (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    MemLp (fun A : Matrix (Fin m) (Fin n) ℝ => normalizedCovarianceTrace A z)
      2 (stdNormalMatrixMeasure m n) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    infer_instance
  exact normalizedCovarianceTrace_memLp (stdNormalMatrixMeasure m n) hn id measurable_id z hz

theorem gaussian_normalized_trace_integrable (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => normalizedCovarianceTrace A z)
      (stdNormalMatrixMeasure m n) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    infer_instance
  exact (gaussian_normalized_trace_memLp m n hn z hz).integrable (by norm_num)

theorem gaussian_normalized_trace_norm_sq_integrable (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => ‖normalizedCovarianceTrace A z‖ ^ 2)
      (stdNormalMatrixMeasure m n) := by
  have h := gaussian_normalized_trace_memLp m n hn z hz
  exact (memLp_two_iff_integrable_sq_norm h.1).mp h

theorem gaussian_normalized_trace_centered_norm_sq_integrable (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      ‖normalizedCovarianceTrace A z - ∫ B : Matrix (Fin m) (Fin n) ℝ,
        normalizedCovarianceTrace B z ∂(stdNormalMatrixMeasure m n)‖ ^ 2)
      (stdNormalMatrixMeasure m n) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    infer_instance
  have h := (gaussian_normalized_trace_memLp m n hn z hz).sub
    (memLp_const (∫ B : Matrix (Fin m) (Fin n) ℝ,
      normalizedCovarianceTrace B z ∂(stdNormalMatrixMeasure m n)))
  exact (memLp_two_iff_integrable_sq_norm h.1).mp h

/-- Finite variance from row Efron--Stein, with no open Gaussian estimate as an input. -/
theorem gaussian_normalized_trace_variance (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    (∫ A : Matrix (Fin m) (Fin n) ℝ,
        ‖normalizedCovarianceTrace A z -
          ∫ B : Matrix (Fin m) (Fin n) ℝ, normalizedCovarianceTrace B z
            ∂(stdNormalMatrixMeasure m n)‖ ^ 2 ∂(stdNormalMatrixMeasure m n))
      ≤ 2 * (m : ℝ) / ((n : ℝ) ^ 2 * z.im ^ 2) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    infer_instance
  obtain ⟨hmeas, hindep, _⟩ := ResidualSparseRepair.standard_gaussian_coordinates m n
  have hRows : iIndepFun (fun i (A : Matrix (Fin m) (Fin n) ℝ) => A i)
      (stdNormalMatrixMeasure m n) :=
    mpIndependentRows (fun A : Matrix (Fin m) (Fin n) ℝ => A) hmeas hindep
  exact normalizedCovarianceTrace_variance (stdNormalMatrixMeasure m n) hn id hmeas hRows z hz

/-- Uniform `O(1 / (m * eta^2))` variance at a fixed lower aspect ratio. -/
theorem gaussian_normalized_trace_variance_aspect (rhoMinus : ℝ) (hrho : 0 < rhoMinus)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hratio : rhoMinus ≤ (n : ℝ) / (m : ℝ))
    (z : ℂ) (hz : 0 < z.im) :
    (∫ A : Matrix (Fin m) (Fin n) ℝ,
        ‖normalizedCovarianceTrace A z -
          ∫ B : Matrix (Fin m) (Fin n) ℝ, normalizedCovarianceTrace B z
            ∂(stdNormalMatrixMeasure m n)‖ ^ 2 ∂(stdNormalMatrixMeasure m n))
      ≤ (2 / rhoMinus ^ 2) / ((m : ℝ) * z.im ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnm : rhoMinus * (m : ℝ) ≤ n := (le_div_iff₀ hm0).mp hratio
  have hden : (rhoMinus * (m : ℝ)) ^ 2 * z.im ^ 2 ≤ (n : ℝ) ^ 2 * z.im ^ 2 :=
    mul_le_mul_of_nonneg_right ((sq_le_sq₀ (mul_pos hrho hm0).le hn0.le).2 hnm)
      (sq_nonneg _)
  refine (gaussian_normalized_trace_variance m n hn z hz).trans ?_
  calc 2 * (m : ℝ) / ((n : ℝ) ^ 2 * z.im ^ 2)
      ≤ 2 * (m : ℝ) / ((rhoMinus * (m : ℝ)) ^ 2 * z.im ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (2 / rhoMinus ^ 2) / ((m : ℝ) * z.im ^ 2) := by
      field_simp
      <;> ring

#print axioms gaussian_normalized_trace_memLp
#print axioms gaussian_normalized_trace_integrable
#print axioms gaussian_normalized_trace_norm_sq_integrable
#print axioms gaussian_normalized_trace_centered_norm_sq_integrable
#print axioms gaussian_normalized_trace_variance
#print axioms gaussian_normalized_trace_variance_aspect
end ResidualSparseRepair20261106.GaussianVariance

