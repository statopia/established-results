import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.RandomMatrix.MeasuresAreProbability
import Statlib.RandomMatrix.Vocabulary.Distributions
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_c625efd6886bf6866e28
import ProverJobs.ResidualE2ESupport20261106.M_42376bcdfff0114fa6af

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

namespace ResidualSparseRepair20261106.GaussianTail

/-- Layer cake at the cutoff four, with integrability obtained from the actual moment. -/
theorem cdf_upper_tail_layercake (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => max (x - 4) 0) μ) :
    IntegrableOn (fun x : ℝ => μ.real (Set.Ioi x)) (Set.Ioi 4) ∧
    (∫ x in Set.Ioi (4 : ℝ), μ.real (Set.Ioi x)) = ∫ x, max (x - 4) 0 ∂μ := by
  let f : ℝ → ℝ := fun x => max (x - 4) 0
  let T : ℝ → ℝ := fun t => μ.real {x | t < f x}
  have hn : 0 ≤ᵐ[μ] f := ae_of_all _ fun x => le_max_right _ _
  have hm : Measurable T := by
    unfold T Measure.real
    apply Measurable.ennreal_toReal
    apply Antitone.measurable
    intro a b hab
    exact measure_mono fun x hx => lt_of_le_of_lt hab hx
  have hTi : IntegrableOn T (Set.Ioi 0) := by
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => by positivity)).2 ?_⟩
    have hl := lintegral_eq_lintegral_meas_lt μ hn hi.aemeasurable
    have he : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (T t)) =
        ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t < f x} := by
      apply lintegral_congr
      intro t
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    rw [he, ← hl]
    exact hi.lintegral_lt_top
  have hevent (t : ℝ) (ht : 0 < t) : {x | t < f x} = Set.Ioi (t + 4) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, f, lt_max_iff]
    constructor
    · intro h
      rcases h with h | h <;> linarith
    · intro h
      left
      linarith
  have heq : Set.EqOn T (fun t : ℝ => μ.real (Set.Ioi (t + 4))) (Set.Ioi 0) := by
    intro t ht
    dsimp [T]
    rw [hevent t ht]
  have htrans := measurePreserving_add_right (volume : Measure ℝ) (4 : ℝ)
  have hemb : MeasurableEmbedding (fun t : ℝ => t + 4) :=
    (Homeomorph.addRight (4 : ℝ)).measurableEmbedding
  have hpre : (fun t : ℝ => t + 4) ⁻¹' Set.Ioi (4 : ℝ) = Set.Ioi 0 := by
    ext t
    simp
  have hTf : IntegrableOn (fun t : ℝ => μ.real (Set.Ioi (t + 4))) (Set.Ioi 0) :=
    hTi.congr_fun heq measurableSet_Ioi
  have hU : IntegrableOn (fun t : ℝ => μ.real (Set.Ioi t)) (Set.Ioi 4) := by
    apply (htrans.integrableOn_comp_preimage hemb).1
    simpa only [hpre, Function.comp_def] using hTf
  refine ⟨hU, ?_⟩
  have ht := htrans.setIntegral_preimage_emb hemb (fun t : ℝ => μ.real (Set.Ioi t)) (Set.Ioi 4)
  rw [hpre] at ht
  rw [← ht, ← setIntegral_congr_fun measurableSet_Ioi heq]
  exact (hi.integral_eq_integral_meas_lt hn).symm

/-- For nonnegative measures and a comparator supported in [-4,4], the Bai tail
is exactly the positive spectral excess at four. -/
theorem cdf_tail_eq_excess (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, |x| ≤ 4)
    (hi : Integrable (fun x : ℝ => max (x - 4) 0) μ) :
    IntegrableOn (fun x : ℝ => |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal|)
      {x : ℝ | 4 < |x|} ∧
    (∫ x in {x : ℝ | 4 < |x|}, |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal|) =
      ∫ x, max (x - 4) 0 ∂μ := by
  let D := fun x : ℝ => |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal|
  have hleft (x : ℝ) (hx : x < -4) : D x = 0 := by
    have hμx : μ (Set.Iic x) = 0 := by
      have he : Set.Iic x =ᵐ[μ] (∅ : Set ℝ) := by
        filter_upwards [hμ] with y hy
        apply propext
        change (y ≤ x) ↔ False
        simp only [iff_false]
        linarith
      rw [measure_congr he, measure_empty]
    have hνx : ν (Set.Iic x) = 0 := by
      have he : Set.Iic x =ᵐ[ν] (∅ : Set ℝ) := by
        filter_upwards [hν] with y hy
        apply propext
        change (y ≤ x) ↔ False
        simp only [iff_false]
        have := neg_le_of_abs_le hy
        linarith
      rw [measure_congr he, measure_empty]
    simp [D, hμx, hνx]
  have hright (x : ℝ) (hx : 4 < x) : D x = μ.real (Set.Ioi x) := by
    have hνx : ν (Set.Iic x) = 1 := by
      have he : Set.Iic x =ᵐ[ν] (Set.univ : Set ℝ) := by
        filter_upwards [hν] with y hy
        apply propext
        change (y ≤ x) ↔ True
        simp only [iff_true]
        exact (le_of_abs_le hy).trans hx.le
      rw [measure_congr he, measure_univ]
    have hm : (μ (Set.Iic x)).toReal ≤ 1 := by
      exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
    rw [show D x = |(μ (Set.Iic x)).toReal - 1| by simp [D, hνx]]
    rw [abs_of_nonpos (by linarith)]
    have hc := measureReal_compl (μ := μ) (s := Set.Iic x) measurableSet_Iic
    simp only [Measure.real, Set.compl_Iic, measure_univ, ENNReal.toReal_one] at hc
    change -((μ (Set.Iic x)).toReal - 1) = (μ (Set.Ioi x)).toReal
    linarith
  obtain ⟨hiU, heU⟩ := cdf_upper_tail_layercake μ hi
  have hiL : IntegrableOn D (Set.Iio (-4)) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Iio (-4)) volume).congr_fun
      (fun x hx => (hleft x hx).symm) measurableSet_Iio
  have hiR : IntegrableOn D (Set.Ioi 4) :=
    hiU.congr_fun (fun x hx => (hright x hx).symm) measurableSet_Ioi
  have hset : {x : ℝ | 4 < |x|} = Set.Iio (-4) ∪ Set.Ioi 4 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · intro h
      rcases h with h | h
      · exact Or.inr (by linarith)
      · exact Or.inl h
  rw [hset]
  refine ⟨integrableOn_union.2 ⟨hiL, hiR⟩, ?_⟩
  have hdis : Disjoint (Set.Iio (-4 : ℝ)) (Set.Ioi 4) := by
    apply Set.disjoint_left.2
    intro x hx hy
    change x < -4 at hx
    change 4 < x at hy
    linarith
  have hz : (∫ x in Set.Iio (-4 : ℝ), D x) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hleft x hx)
  rw [setIntegral_union hdis measurableSet_Ioi hiL hiR, hz, zero_add]
  rw [setIntegral_congr_fun measurableSet_Ioi hright]
  exact heU

/-- The mean covariance ESD has nonnegative support, with no spectral cutoff assumption. -/
theorem gaussianExpectedCovariance_nonnegative (m n : ℕ) :
    ∀ᵐ x ∂gaussianExpectedCovariance m n, 0 ≤ x := by
  rw [ae_iff]
  change (gaussianExpectedCovariance m n) {x : ℝ | ¬0 ≤ x} = 0
  have hmap (i : Fin n) :
      (Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i)
        (stdNormalMatrixMeasure m n)) {x : ℝ | ¬0 ≤ x} = 0 := by
    have hmset : MeasurableSet {x : ℝ | ¬0 ≤ x} := by
      simpa only [not_le] using (measurableSet_Iio : MeasurableSet (Set.Iio (0 : ℝ)))
    rw [Measure.map_apply (covarianceEigenvalue_measurable m n i) hmset]
    have he : (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i) ⁻¹'
        {x : ℝ | ¬0 ≤ x} = ∅ := by
      ext A
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact covarianceEigenvalue_nonneg A i
    rw [he, measure_empty]
  rw [gaussianExpectedCovariance, expectedEigenMeasure, Measure.smul_apply, Measure.finset_sum_apply]
  have hsum : (∑ i : Fin n, (Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i)
      (stdNormalMatrixMeasure m n)) {x : ℝ | ¬0 ≤ x}) = 0 :=
    Finset.sum_eq_zero (fun i _ => hmap i)
  change ENNReal.ofReal ((n : ℝ)⁻¹) • (∑ i : Fin n,
    (Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i)
      (stdNormalMatrixMeasure m n)) {x : ℝ | ¬0 ≤ x}) = 0
  rw [hsum, smul_zero]

/-- The positive first spectral excess of the actual mean covariance ESD is small. -/
theorem gaussianExpectedCovariance_excess (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m) :
    Integrable (fun x : ℝ => max (x - 4) 0) (gaussianExpectedCovariance m n) ∧
    (∫ x : ℝ, max (x - 4) 0 ∂gaussianExpectedCovariance m n) ≤
      24 / Real.sqrt (m : ℝ) := by
  haveI : IsProbabilityMeasure (stdNormalMatrixMeasure m n) := by
    unfold stdNormalMatrixMeasure
    infer_instance
  obtain ⟨hgm, hgi, hgs⟩ := ResidualSparseRepair.standard_gaussian_coordinates m n
  obtain ⟨_, hiop, hbop⟩ := gaussian_covariance_tail (stdNormalMatrixMeasure m n)
    (fun A : Matrix (Fin m) (Fin n) ℝ => A) hgm hgi hgs hm hnm
  let f : ℝ → ℝ := fun x => max (x - 4) 0
  have hf : Measurable f := by fun_prop
  have hle (i : Fin n) (A : Matrix (Fin m) (Fin n) ℝ) :
      f (covarianceEigenvalue A i) ≤ max (Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 / (m : ℝ) - 4) 0 := by
    exact max_le_max (sub_le_sub_right (covarianceEigenvalue_le_opNorm hn A i) 4) le_rfl
  have hi (i : Fin n) : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      f (covarianceEigenvalue A i)) (stdNormalMatrixMeasure m n) :=
    hiop.mono (hf.comp (covarianceEigenvalue_measurable m n i)).aestronglyMeasurable
      (ae_of_all _ fun A => by
        have ha : 0 ≤ f (covarianceEigenvalue A i) := le_max_right _ _
        have hb : 0 ≤ max (Statlib.HighDim.MatrixAnalysis.opNorm A ^ 2 / (m : ℝ) - 4) 0 := le_max_right _ _
        simpa only [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using hle i A)
  have him (i : Fin n) : Integrable f
      (Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i)
        (stdNormalMatrixMeasure m n)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (covarianceEigenvalue_measurable m n i).aemeasurable).2 (hi i)
  have hsum : Integrable f
      (∑ i : Fin n, Measure.map (fun A : Matrix (Fin m) (Fin n) ℝ => covarianceEigenvalue A i)
        (stdNormalMatrixMeasure m n)) :=
    integrable_finset_sum_measure.2 (fun i _ => him i)
  have hie : Integrable f (gaussianExpectedCovariance m n) := by
    exact hsum.smul_measure ENNReal.ofReal_ne_top
  refine ⟨hie, ?_⟩
  have heq := expectedEigenMeasure_integral (stdNormalMatrixMeasure m n)
    (fun i A => covarianceEigenvalue A i) (covarianceEigenvalue_measurable m n) f hf hi
  change (∫ x, f x ∂gaussianExpectedCovariance m n) = _ at heq
  change (∫ x, f x ∂gaussianExpectedCovariance m n) ≤ _
  rw [heq, smul_eq_mul]
  change (n : ℝ)⁻¹ * (∫ A : Matrix (Fin m) (Fin n) ℝ, ∑ i : Fin n,
    f (covarianceEigenvalue A i) ∂stdNormalMatrixMeasure m n) ≤ _
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  have hiBound (i : Fin n) :
      (∫ A : Matrix (Fin m) (Fin n) ℝ, f (covarianceEigenvalue A i) ∂stdNormalMatrixMeasure m n) ≤
        24 / Real.sqrt (m : ℝ) :=
    (integral_mono (hi i) hiop (hle i)).trans hbop
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, (24 / Real.sqrt (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hiBound i)) (by positivity)
    _ = 24 / Real.sqrt (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_mul]

/-- The actual Gaussian covariance mean ESD has the required finite Bai tail budget. -/
theorem gaussianExpectedCovariance_tail (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    IntegrableOn (fun x : ℝ => |((gaussianExpectedCovariance m n) (Set.Iic x)).toReal -
      ((Statlib.RandomMatrix.Vocabulary.mpMeasure rho) (Set.Iic x)).toReal|) {x : ℝ | 4 < |x|} ∧
    (∫ x in {x : ℝ | 4 < |x|}, |((gaussianExpectedCovariance m n) (Set.Iic x)).toReal -
      ((Statlib.RandomMatrix.Vocabulary.mpMeasure rho) (Set.Iic x)).toReal|) ≤
      24 / Real.sqrt (m : ℝ) := by
  haveI := gaussianExpectedCovariance_probability m n hn
  haveI := Statlib.RandomMatrix.mpMeasure_isProbabilityMeasure rho hrho
  obtain ⟨hi, hb⟩ := gaussianExpectedCovariance_excess m n hm hn hnm
  obtain ⟨hT, heq⟩ := cdf_tail_eq_excess (gaussianExpectedCovariance m n)
    (Statlib.RandomMatrix.Vocabulary.mpMeasure rho) (gaussianExpectedCovariance_nonnegative m n)
    (DenseGaussian.mpMeasure_support_four rho hrho hrho1) hi
  exact ⟨hT, heq ▸ hb⟩

#print axioms cdf_upper_tail_layercake
#print axioms cdf_tail_eq_excess
#print axioms gaussianExpectedCovariance_nonnegative
#print axioms gaussianExpectedCovariance_excess
#print axioms gaussianExpectedCovariance_tail

end ResidualSparseRepair20261106.GaussianTail

