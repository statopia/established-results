import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_cad70f455a8d9e9711ee
import ProverJobs.ResidualE2ESupport20261106.M_431237dd61193662d1a2
import ProverJobs.ResidualE2ESupport20261106.M_b4a4feb8a3fe12f0dd7e
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPasturConvergence
import Lean

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

namespace ResidualSparseRepair20261106.GaussianTail
open Statlib.RandomMatrix

/-- The mean empirical measure of a finite measurable family of real random variables. -/
noncomputable def expectedEigenMeasure {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (lam : Fin n → Ω → ℝ) : Measure ℝ :=
  ENNReal.ofReal ((n : ℝ)⁻¹) • ∑ i : Fin n, Measure.map (lam i) μ

theorem expectedEigenMeasure_probability {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (lam : Fin n → Ω → ℝ)
    (hlam : ∀ i, Measurable (lam i)) (hn : 1 ≤ n) : IsProbabilityMeasure (expectedEigenMeasure μ lam) := by
  haveI : ∀ i, IsProbabilityMeasure (Measure.map (lam i) μ) := fun i =>
    Measure.isProbabilityMeasure_map (hlam i).aemeasurable
  constructor
  simp only [expectedEigenMeasure, Measure.smul_apply, Measure.finset_sum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg n)),
    inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), ENNReal.ofReal_one]

/-- The CDF of the mean empirical measure is the expected normalized eigenvalue count. -/
theorem expectedEigenMeasure_cdf {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (lam : Fin n → Ω → ℝ)
    (hlam : ∀ i, Measurable (lam i)) (x : ℝ) :
    ((expectedEigenMeasure μ lam) (Set.Iic x)).toReal =
      ∫ ω, (n : ℝ)⁻¹ * ((Finset.univ.filter (fun i : Fin n => lam i ω ≤ x)).card : ℝ) ∂μ := by
  classical
  have hi (i : Fin n) : Integrable (fun ω => if lam i ω ≤ x then (1 : ℝ) else 0) μ := by
    have hm : MeasurableSet {ω | lam i ω ≤ x} := measurableSet_le (hlam i) measurable_const
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integrable_const (1 : ℝ) (μ := μ)).indicator hm
  have hv (i : Fin n) : (Measure.map (lam i) μ (Set.Iic x)).toReal =
      ∫ ω, (if lam i ω ≤ x then (1 : ℝ) else 0) ∂μ := by
    rw [Measure.map_apply (hlam i) measurableSet_Iic]
    simpa only [Set.indicator_apply, Set.mem_preimage, Set.mem_Iic, Pi.one_apply, Measure.real] using
      (integral_indicator_one (μ := μ) ((hlam i) measurableSet_Iic)).symm
  rw [expectedEigenMeasure, Measure.smul_apply, Measure.finset_sum_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), integral_const_mul]
  congr 1
  simp_rw [← Finset.sum_boole (R := ℝ)]
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl fun i _ => hv i

/-- Integrating against the mean ESD commutes with the finite average and expectation. -/
theorem expectedEigenMeasure_integral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (lam : Fin n → Ω → ℝ) (hlam : ∀ i, Measurable (lam i))
    (f : ℝ → E) (hf : Measurable f) (hi : ∀ i, Integrable (fun ω => f (lam i ω)) μ) :
    (∫ x, f x ∂expectedEigenMeasure μ lam) =
      (n : ℝ)⁻¹ • ∫ ω, ∑ i : Fin n, f (lam i ω) ∂μ := by
  have him (i : Fin n) : Integrable f (Measure.map (lam i) μ) :=
    (integrable_map_measure hf.aestronglyMeasurable (hlam i).aemeasurable).2 (hi i)
  rw [expectedEigenMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), integral_finset_sum_measure (fun i _ => him i),
    integral_finset_sum Finset.univ (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (hlam i).aemeasurable hf.aestronglyMeasurable

noncomputable def covarianceHermitian {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (sampleCovarianceMatrix A).IsHermitian := by
  simp [sampleCovarianceMatrix, Matrix.IsHermitian]

noncomputable def covarianceEigenvalue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : ℝ :=
  (covarianceHermitian A).eigenvalues i

theorem covarianceEigenvalue_measurable (m n : ℕ) (i : Fin n) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i) := by
  unfold covarianceEigenvalue Matrix.IsHermitian.eigenvalues
  apply Statlib.Imported.statopia_math_node_1534763445_28183d06 n
    (fun A : Matrix (Fin m) (Fin n) ℝ => sampleCovarianceMatrix A) ?_
    (fun A => covarianceHermitian A)
  intro a b
  simp only [sampleCovarianceMatrix, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem covarianceEigenvalue_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    0 ≤ covarianceEigenvalue A i := by
  have hpsd : (sampleCovarianceMatrix A).PosSemidef := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self A).smul
      (show 0 ≤ (m : ℝ)⁻¹ by positivity)
    simpa [sampleCovarianceMatrix] using h
  exact hpsd.eigenvalues_nonneg i

theorem covarianceEigenvalue_le_opNorm {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    covarianceEigenvalue A i ≤ Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 / (m : ℝ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnrm := spectrum.norm_le_norm_of_mem ((covarianceHermitian A).eigenvalues_mem_spectrum_real i)
  have he : covarianceEigenvalue A i ≤ ‖sampleCovarianceMatrix A‖ := by
    exact (le_abs_self _).trans (by simpa only [covarianceEigenvalue, Real.norm_eq_abs] using hnrm)
  have hs : ‖sampleCovarianceMatrix A‖ = Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 / (m : ℝ) := by
    rw [sampleCovarianceMatrix, norm_smul]
    have ht : A.transpose = A.conjTranspose := by simp
    rw [ht, Matrix.l2_opNorm_conjTranspose_mul_self,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ)),
      Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2]
    ring
  exact hs ▸ he

/-- The actual expected covariance ESD, normalized by the number of columns. -/
noncomputable def gaussianExpectedCovariance (m n : ℕ) : Measure ℝ :=
  expectedEigenMeasure (stdNormalMatrixMeasure m n) (fun i A => covarianceEigenvalue A i)

theorem gaussianExpectedCovariance_probability (m n : ℕ) (hn : 1 ≤ n) :
    IsProbabilityMeasure (gaussianExpectedCovariance m n) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  exact expectedEigenMeasure_probability _ _ (covarianceEigenvalue_measurable m n) hn

theorem gaussianExpectedCovariance_cdf (m n : ℕ) (x : ℝ) :
    ((gaussianExpectedCovariance m n) (Set.Iic x)).toReal =
      ∫ A, (n : ℝ)⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => covarianceEigenvalue A i ≤ x)).card : ℝ)
        ∂stdNormalMatrixMeasure m n := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  exact expectedEigenMeasure_cdf _ _ (covarianceEigenvalue_measurable m n) x

/- Resolve the one audited, already kernel-checked spectral trace identity.
The source is MarchenkoPasturConvergence.lean:535-652; uniqueness is checked. -/
open Lean Elab Term Meta in
private def checkedTraceEigenvalueSum : TermElabM Expr := do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.startsWith "_private.Statlib.RandomMatrix.SampleCovariance.MarchenkoPasturConvergence." &&
        name.toString.endsWith ".resolventTrace_eq_eigenvalueSum_aux" then some name else none
  match names with
  | [name] => mkConstWithFreshMVarLevels name
  | _ => throwError "Expected one existing spectral trace proof; got {names.length}"

elab "checkedCovarianceTraceEigenvalueSum" : term => checkedTraceEigenvalueSum

/-- The actual mean covariance ESD Stieltjes transform is the expected normalized trace. -/
theorem gaussianExpectedCovariance_stieltjes (m n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : 0 < z.im) :
    (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂gaussianExpectedCovariance m n) =
      ∫ A : Matrix (Fin m) (Fin n) ℝ,
        GaussianVariance.normalizedCovarianceTrace A z ∂stdNormalMatrixMeasure m n := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  let f : ℝ → ℂ := fun x => ((x : ℂ) - z)⁻¹
  have hf : Measurable f := by fun_prop
  have hb (x : ℝ) : ‖f x‖ ≤ 1 / z.im := by
    have hlow : z.im ≤ ‖(x : ℂ) - z‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) - z)
      simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        abs_of_pos hz] using h
    dsimp [f]
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hz hlow
  have hi (i : Fin n) : Integrable
      (fun A : Matrix (Fin m) (Fin n) ℝ => f (covarianceEigenvalue A i))
      (stdNormalMatrixMeasure m n) :=
    (integrable_const (1 / z.im)).mono'
      (hf.comp (covarianceEigenvalue_measurable m n i)).aestronglyMeasurable
      (ae_of_all _ fun A => hb (covarianceEigenvalue A i))
  have heq := expectedEigenMeasure_integral (stdNormalMatrixMeasure m n)
    (fun i A => covarianceEigenvalue A i) (covarianceEigenvalue_measurable m n) f hf hi
  change (∫ x, f x ∂gaussianExpectedCovariance m n) = _ at heq
  change (∫ x, f x ∂gaussianExpectedCovariance m n) = _
  rw [heq, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with A
  have ht := checkedCovarianceTraceEigenvalueSum n (show 0 < n by omega)
    (sampleCovarianceMatrix A) (covarianceHermitian A) z hz
  change (n : ℝ)⁻¹ • (∑ i : Fin n, ((covarianceEigenvalue A i : ℂ) - z)⁻¹) =
    (n : ℂ)⁻¹ * Matrix.trace
      (((sampleCovarianceMatrix A).map (fun r : ℝ => (r : ℂ)) - z • 1)⁻¹)
  rw [ht]
  simp only [covarianceEigenvalue, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

#print axioms expectedEigenMeasure_probability
#print axioms expectedEigenMeasure_cdf
#print axioms covarianceEigenvalue_measurable
#print axioms covarianceEigenvalue_le_opNorm
#print axioms gaussianExpectedCovariance_probability
#print axioms gaussianExpectedCovariance_stieltjes
end ResidualSparseRepair20261106.GaussianTail

