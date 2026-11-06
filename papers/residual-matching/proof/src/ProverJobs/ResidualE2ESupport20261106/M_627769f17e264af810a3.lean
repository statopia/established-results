import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_02b9183c60624c6d1cd5
import ProverJobs.ResidualE2ESupport20261106.M_7607257e8c8d3943332a

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
namespace ResidualSparseRepair20261106.GaussianVariance
open Statlib.RandomMatrix

noncomputable def covarianceTrace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (z : ℂ) : ℂ :=
  Matrix.trace (((sampleCovarianceMatrix A).map (fun r : ℝ => (r : ℂ)) - z • 1)⁻¹)

noncomputable def normalizedCovarianceTrace {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (z : ℂ) : ℂ :=
  (n : ℂ)⁻¹ * covarianceTrace A z

private theorem partialCovariance_univ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    mpPartialCovariance Finset.univ A = sampleCovarianceMatrix A := by
  classical
  change (1 / (m : ℝ)) • (∑ k ∈ (Finset.univ : Finset (Fin m)), Matrix.vecMulVec (A k) (A k)) = _
  ext i j
  simp [sampleCovarianceMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply]

private theorem partialTrace_univ {m n : ℕ} (z : ℂ) (A : Matrix (Fin m) (Fin n) ℝ) :
    mpPartialTrace Finset.univ z A = covarianceTrace A z := by
  change Matrix.trace (((mpPartialCovariance Finset.univ A).map
    (fun r : ℝ => (r : ℂ)) - z • 1)⁻¹) = _
  rw [partialCovariance_univ]
  rfl

theorem covarianceTrace_measurable {m n : ℕ} (z : ℂ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceTrace A z) := by
  have hf : mpPartialTrace (p := n) (n := m) Finset.univ z =
      (fun A => covarianceTrace A z) := funext (partialTrace_univ z)
  rw [← hf]
  exact mpPartialTraceMeasurable Finset.univ z

theorem covarianceTrace_bound {m n : ℕ} (z : ℂ) (hz : 0 < z.im)
    (A : Matrix (Fin m) (Fin n) ℝ) : ‖covarianceTrace A z‖ ≤ (n : ℝ) / z.im := by
  rw [← partialTrace_univ]
  exact mpPartialTraceBound Finset.univ z hz A

/-- Efron--Stein bound for independent rows; it needs no distributional or moment hypothesis. -/
theorem covarianceTrace_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ}
    (X : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hRows : iIndepFun (fun i ω => X ω i) μ)
    (z : ℂ) (hz : 0 < z.im) :
    (∫ ω, ‖covarianceTrace (X ω) z - ∫ ω', covarianceTrace (X ω') z ∂μ‖ ^ 2 ∂μ)
      ≤ 2 * (m : ℝ) / z.im ^ 2 := by
  have h := mpPartialTraceVariance μ X hX hRows Finset.univ z hz
  simpa only [partialTrace_univ] using h

theorem normalizedCovarianceTrace_measurable {m n : ℕ} (z : ℂ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => normalizedCovarianceTrace A z) :=
  measurable_const.mul (covarianceTrace_measurable z)

theorem normalizedCovarianceTrace_bound {m n : ℕ} (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖normalizedCovarianceTrace A z‖ ≤ 1 / z.im := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  rw [normalizedCovarianceTrace, norm_mul, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖covarianceTrace A z‖ ≤ (n : ℝ)⁻¹ * ((n : ℝ) / z.im) :=
      mul_le_mul_of_nonneg_left (covarianceTrace_bound z hz A) (inv_nonneg.mpr hn0.le)
    _ = 1 / z.im := by field_simp

theorem normalizedCovarianceTrace_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin m) (Fin n) ℝ) (hX : Measurable X)
    (z : ℂ) (hz : 0 < z.im) :
    MemLp (fun ω => normalizedCovarianceTrace (X ω) z) 2 μ :=
  MemLp.of_bound ((normalizedCovarianceTrace_measurable z).comp hX).aestronglyMeasurable
    (1 / z.im) (ae_of_all _ (fun ω => normalizedCovarianceTrace_bound hn z hz (X ω)))

set_option maxHeartbeats 1000000 in
theorem normalizedCovarianceTrace_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} (hn : 1 ≤ n)
    (X : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hRows : iIndepFun (fun i ω => X ω i) μ)
    (z : ℂ) (hz : 0 < z.im) :
    (∫ ω, ‖normalizedCovarianceTrace (X ω) z -
        ∫ ω', normalizedCovarianceTrace (X ω') z ∂μ‖ ^ 2 ∂μ)
      ≤ 2 * (m : ℝ) / ((n : ℝ) ^ 2 * z.im ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hTraceMeas : Measurable (fun ω => covarianceTrace (X ω) z) :=
    (covarianceTrace_measurable z).comp (measurable_pi_iff.mpr fun i =>
      measurable_pi_iff.mpr fun j => hX i j)
  have hTraceLp : MemLp (fun ω => covarianceTrace (X ω) z) 2 μ :=
    MemLp.of_bound hTraceMeas.aestronglyMeasurable ((n : ℝ) / z.im)
      (ae_of_all _ (fun ω => covarianceTrace_bound z hz (X ω)))
  have hCenterInt : Integrable (fun ω => ‖covarianceTrace (X ω) z -
      ∫ ω', covarianceTrace (X ω') z ∂μ‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hTraceLp.sub (memLp_const _)).1).mp
      (hTraceLp.sub (memLp_const _))
  have hmean : (∫ ω, normalizedCovarianceTrace (X ω) z ∂μ) =
      (n : ℂ)⁻¹ * ∫ ω, covarianceTrace (X ω) z ∂μ := by
    exact integral_const_mul _ _
  have hpoint : ∀ ω, ‖normalizedCovarianceTrace (X ω) z -
      ∫ ω', normalizedCovarianceTrace (X ω') z ∂μ‖ ^ 2 =
      ((n : ℝ)⁻¹) ^ 2 * ‖covarianceTrace (X ω) z -
        ∫ ω', covarianceTrace (X ω') z ∂μ‖ ^ 2 := by
    intro ω
    rw [hmean, normalizedCovarianceTrace, ← mul_sub, norm_mul, norm_inv,
      Complex.norm_natCast, mul_pow]
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hvar := covarianceTrace_variance μ X hX hRows z hz
  calc ((n : ℝ)⁻¹) ^ 2 * (∫ ω, ‖covarianceTrace (X ω) z -
        ∫ ω', covarianceTrace (X ω') z ∂μ‖ ^ 2 ∂μ)
      ≤ ((n : ℝ)⁻¹) ^ 2 * (2 * (m : ℝ) / z.im ^ 2) :=
        mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    _ = 2 * (m : ℝ) / ((n : ℝ) ^ 2 * z.im ^ 2) := by ring

#print axioms covarianceTrace_variance
#print axioms normalizedCovarianceTrace_variance
end ResidualSparseRepair20261106.GaussianVariance

