import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_c625efd6886bf6866e28
import ProverJobs.ResidualE2ESupport20261106.M_25b575e712786d8e5814

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

namespace ResidualSparseRepair20261106.GaussianTail
open Statlib.RandomMatrix
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

noncomputable def normalizedGaussianMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ := (Real.sqrt (m : ℝ))⁻¹ • A

lemma normalizedGaussianMatrix_gram {m n : ℕ} (hm : 1 ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    (normalizedGaussianMatrix A).conjTranspose * normalizedGaussianMatrix A =
      sampleCovarianceMatrix A := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs := Real.sq_sqrt hm0.le
  have hc : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = 1 / (m : ℝ) := by
    rw [← mul_inv, ← pow_two, hs, one_div]
  ext i j
  simp only [normalizedGaussianMatrix, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, sampleCovarianceMatrix, Matrix.transpose_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    ((Real.sqrt (m : ℝ))⁻¹ * A k i) * ((Real.sqrt (m : ℝ))⁻¹ * A k j)
        = ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹) * (A k i * A k j) := by ring
    _ = (1 / (m : ℝ)) * (A k i * A k j) := by rw [hc]

/-- The finite covariance spectrum is the square of the actual singular-value list,
up to a concrete permutation of the finite index set. -/
theorem covarianceEigenvalue_eq_svals_sq {m n : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ e : Fin n ≃ Fin n, ∀ i : Fin n,
      covarianceEigenvalue A i = svals (normalizedGaussianMatrix A) (e i) ^ 2 := by
  let e1 : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
  let e2 : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin n).symm
  refine ⟨e1.trans e2.symm, ?_⟩
  intro i
  let B := normalizedGaussianMatrix A
  have hmat := normalizedGaussianMatrix_gram hm A
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self B
  have hn : 0 ≤ (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues₀ (e1 i) := by
    have h := hpsd.eigenvalues_nonneg (e1 i |> (Fintype.equivOfCardEq (Fintype.card_fin _)))
    simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h
  have he : (Fin.cast (Fintype.card_fin n).symm ((e1.trans e2.symm) i)) = e1 i := by
    change e2 (e2.symm (e1 i)) = e1 i
    exact e2.apply_symm_apply _
  simp only [svals, he]
  rw [Real.sq_sqrt hn]
  unfold covarianceEigenvalue Matrix.IsHermitian.eigenvalues
  change (covarianceHermitian A).eigenvalues₀ (e1 i) =
    (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues₀ (e1 i)
  congr 2
  exact hmat.symm

/-- A permutation-independent finite spectral counting identity. -/
theorem covariance_svals_count {m n : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (p : ℝ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin n => p (covarianceEigenvalue A i))).card =
      (Finset.univ.filter (fun i : Fin n => p (svals (normalizedGaussianMatrix A) i ^ 2))).card := by
  classical
  obtain ⟨e, he⟩ := covarianceEigenvalue_eq_svals_sq hm A
  have hsum := e.sum_comp (fun i : Fin n => if p (svals (normalizedGaussianMatrix A) i ^ 2)
    then (1 : ℕ) else 0)
  simp_rw [← he] at hsum
  simpa only [Finset.sum_boole] using hsum

/-- The nonnegative singular-value CDF is exactly the covariance CDF at the square. -/
theorem gaussianExpectedCovariance_cdf_svals (m n : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : 0 ≤ t) :
    ((gaussianExpectedCovariance m n) (Set.Iic (t^2))).toReal =
      ∫ A : Matrix (Fin m) (Fin n) ℝ, (n : ℝ)⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => svals (normalizedGaussianMatrix A) i ≤ t)).card : ℝ)
        ∂stdNormalMatrixMeasure m n := by
  rw [gaussianExpectedCovariance_cdf]
  apply integral_congr_ae
  filter_upwards with A
  congr 2
  have hc := covariance_svals_count hm A (fun x => x ≤ t^2)
  rw [hc]
  congr 1
  apply Finset.filter_congr
  intro i _
  have hs : 0 ≤ svals (normalizedGaussianMatrix A) i := Real.sqrt_nonneg _
  constructor <;> intro h <;> nlinarith

/-- Averaging the eigenvalue laws commutes with any measurable event. -/
theorem expectedEigenMeasure_real_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (lam : Fin n → Ω → ℝ)
    (hlam : ∀ i, Measurable (lam i)) (s : Set ℝ) [DecidablePred (fun x => x ∈ s)] (hs : MeasurableSet s) :
    (expectedEigenMeasure μ lam).real s =
      ∫ ω, (n : ℝ)⁻¹ * ((Finset.univ.filter (fun i : Fin n => lam i ω ∈ s)).card : ℝ) ∂μ := by
  classical
  let f : ℝ → ℝ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hi (i : Fin n) : Integrable (fun ω => f (lam i ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hf.comp (hlam i)).aestronglyMeasurable
    filter_upwards with ω
    dsimp [f]
    by_cases h : lam i ω ∈ s <;> simp [h]
  rw [← integral_indicator_one hs]
  change (∫ x, f x ∂expectedEigenMeasure μ lam) = _
  rw [expectedEigenMeasure_integral μ lam hlam f hf hi, smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  simp only [f, Set.indicator_apply]
  exact Finset.sum_boole (fun i : Fin n => lam i ω ∈ s) Finset.univ

/-- Taking square roots removes the squaring in the finite spectral permutation. -/
theorem covariance_svals_sqrt_count {m n : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (p : ℝ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin n => p (Real.sqrt (covarianceEigenvalue A i)))).card =
      (Finset.univ.filter (fun i : Fin n => p (svals (normalizedGaussianMatrix A) i))).card := by
  have hc := covariance_svals_count hm A (fun x => p (Real.sqrt x))
  have heq (i : Fin n) : Real.sqrt (svals (normalizedGaussianMatrix A) i ^ 2) =
      svals (normalizedGaussianMatrix A) i := Real.sqrt_sq (Real.sqrt_nonneg _)
  simpa only [heq] using hc

/-- The actual symmetrized square-root mean covariance ESD is the expected
symmetrized singular-value count used by the locked main theorem. -/
theorem gaussianExpectedCovariance_symmetric_cdf (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℝ) :
    (DenseGaussian.symmetricSqrtMeasure (gaussianExpectedCovariance m n)).real (Set.Iic x) =
      ∫ A : Matrix (Fin m) (Fin n) ℝ, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n => svals (normalizedGaussianMatrix A) i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n => -(svals (normalizedGaussianMatrix A) i) ≤ x)).card : ℝ))
        ∂stdNormalMatrixMeasure m n := by
  classical
  haveI := gaussianExpectedCovariance_probability m n hn
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  let P := {y : ℝ | Real.sqrt y ≤ x}
  let N := {y : ℝ | -Real.sqrt y ≤ x}
  have hmP : MeasurableSet P := measurableSet_le Real.continuous_sqrt.measurable measurable_const
  have hmN : MeasurableSet N := measurableSet_le Real.continuous_sqrt.measurable.neg measurable_const
  let fP := fun A : Matrix (Fin m) (Fin n) ℝ => (n : ℝ)⁻¹ *
    ((Finset.univ.filter (fun i : Fin n => covarianceEigenvalue A i ∈ P)).card : ℝ)
  let fN := fun A : Matrix (Fin m) (Fin n) ℝ => (n : ℝ)⁻¹ *
    ((Finset.univ.filter (fun i : Fin n => covarianceEigenvalue A i ∈ N)).card : ℝ)
  have hInt (s : Set ℝ) (hs : MeasurableSet s) : Integrable
      (fun A : Matrix (Fin m) (Fin n) ℝ => (n : ℝ)⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => covarianceEigenvalue A i ∈ s)).card : ℝ))
      (stdNormalMatrixMeasure m n) := by
    have hi (i : Fin n) : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ =>
        if covarianceEigenvalue A i ∈ s then (1 : ℝ) else 0) (stdNormalMatrixMeasure m n) := by
      simpa only [Set.indicator_apply, Set.mem_preimage] using
        (integrable_const (1 : ℝ) (μ := stdNormalMatrixMeasure m n)).indicator
          (hs.preimage (covarianceEigenvalue_measurable m n i))
    have hh := (integrable_finset_sum (μ := stdNormalMatrixMeasure m n) Finset.univ (fun i _ => hi i)).const_mul ((n : ℝ)⁻¹)
    simpa only [Finset.sum_boole] using hh
  have heP : (gaussianExpectedCovariance m n).real P = ∫ A, fP A ∂stdNormalMatrixMeasure m n :=
    expectedEigenMeasure_real_apply (stdNormalMatrixMeasure m n) (fun i A => covarianceEigenvalue A i)
      (covarianceEigenvalue_measurable m n) P hmP
  have heN : (gaussianExpectedCovariance m n).real N = ∫ A, fN A ∂stdNormalMatrixMeasure m n :=
    expectedEigenMeasure_real_apply (stdNormalMatrixMeasure m n) (fun i A => covarianceEigenvalue A i)
      (covarianceEigenvalue_measurable m n) N hmN
  rw [DenseGaussian.symmetricSqrtMeasure_real_Iic]
  change (1 / 2 : ℝ) * (gaussianExpectedCovariance m n).real P +
    (1 / 2 : ℝ) * (gaussianExpectedCovariance m n).real N = _
  have hIP : Integrable fP (stdNormalMatrixMeasure m n) := hInt P hmP
  have hIN : Integrable fN (stdNormalMatrixMeasure m n) := hInt N hmN
  rw [heP, heN, ← integral_const_mul, ← integral_const_mul]
  change (∫ A : Matrix (Fin m) (Fin n) ℝ, (1 / 2 : ℝ) * fP A ∂stdNormalMatrixMeasure m n) +
    (∫ A : Matrix (Fin m) (Fin n) ℝ, (1 / 2 : ℝ) * fN A ∂stdNormalMatrixMeasure m n) = _
  rw [← integral_add (hIP.const_mul (1 / 2)) (hIN.const_mul (1 / 2))]
  apply integral_congr_ae
  filter_upwards with A
  have hp := covariance_svals_sqrt_count hm A (fun y => y ≤ x)
  have hn' := covariance_svals_sqrt_count hm A (fun y => -y ≤ x)
  dsimp [fP, fN, P, N]
  change (1 / 2 : ℝ) * ((n : ℝ)⁻¹ *
      ((Finset.univ.filter (fun i : Fin n => Real.sqrt (covarianceEigenvalue A i) ≤ x)).card : ℝ)) +
    (1 / 2 : ℝ) * ((n : ℝ)⁻¹ *
      ((Finset.univ.filter (fun i : Fin n => -Real.sqrt (covarianceEigenvalue A i) ≤ x)).card : ℝ)) = _
  rw [hp, hn']
  field_simp

#print axioms covarianceEigenvalue_eq_svals_sq
#print axioms covariance_svals_count
#print axioms gaussianExpectedCovariance_cdf_svals
#print axioms gaussianExpectedCovariance_symmetric_cdf
end ResidualSparseRepair20261106.GaussianTail

