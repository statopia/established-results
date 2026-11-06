import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace ResidualSparseRepair20261106.DenseGaussian

noncomputable def symmetricSqrtMeasure (μ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • Measure.map Real.sqrt μ +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.map (fun y : ℝ => -Real.sqrt y) μ

theorem symmetricSqrtMeasure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetricSqrtMeasure μ) := by
  haveI : IsProbabilityMeasure (Measure.map Real.sqrt μ) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (Measure.map (fun y : ℝ => -Real.sqrt y) μ) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  simp only [symmetricSqrtMeasure, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem symmetricSqrtMeasure_real_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (symmetricSqrtMeasure μ).real (Iic x) =
      (1 / 2 : ℝ) * μ.real {y | Real.sqrt y ≤ x} +
        (1 / 2 : ℝ) * μ.real {y | -Real.sqrt y ≤ x} := by
  simp only [symmetricSqrtMeasure, measureReal_def, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  rfl

theorem symmetricSqrtMeasure_cdf_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) (hx : 0 ≤ x) :
    (symmetricSqrtMeasure μ).real (Iic x) = (1 / 2 : ℝ) + (1 / 2 : ℝ) * μ.real (Iic (x ^ 2)) := by
  have hp : {y : ℝ | Real.sqrt y ≤ x} = Iic (x ^ 2) := by
    ext y
    simp only [mem_setOf_eq, mem_Iic, Real.sqrt_le_iff, hx, true_and]
  have hn : {y : ℝ | -Real.sqrt y ≤ x} = univ := by
    ext y
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact (neg_nonpos.mpr (Real.sqrt_nonneg y)).trans hx
  rw [symmetricSqrtMeasure_real_Iic, hp, hn, probReal_univ]
  ring

theorem symmetricSqrtMeasure_cdf_neg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) (hx : x < 0) :
    (symmetricSqrtMeasure μ).real (Iic x) =
      (1 / 2 : ℝ) * (1 - μ.real (Iio (x ^ 2))) := by
  have hp : {y : ℝ | Real.sqrt y ≤ x} = ∅ := by
    ext y
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact not_le.mpr (hx.trans_le (Real.sqrt_nonneg y))
  have hn : {y : ℝ | -Real.sqrt y ≤ x} = (Iio (x ^ 2))ᶜ := by
    ext y
    simp only [mem_setOf_eq, mem_compl_iff, mem_Iio, not_lt]
    rw [neg_le, Real.le_sqrt' (neg_pos.mpr hx)]
    simp only [neg_sq]
  rw [symmetricSqrtMeasure_real_Iic, hp, hn, measureReal_empty, mul_zero, zero_add,
    measureReal_compl measurableSet_Iio, probReal_univ]

theorem abs_real_Iio_sub_le_of_Iic (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : ℝ)
    (h : ∀ x : ℝ, |μ.real (Iic x) - ν.real (Iic x)| ≤ e) (a : ℝ) :
    |μ.real (Iio a) - ν.real (Iio a)| ≤ e := by
  let t : ℕ → ℝ := fun k => a - 1 / ((k : ℝ) + 1)
  have ht : Monotone t := by
    intro i j hij
    dsimp [t]
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < i + 1)
      (by linarith : (i : ℝ) + 1 ≤ j + 1)
    linarith
  have hlt : ∀ k, t k < a := by
    intro k
    dsimp [t]
    exact sub_lt_self _ (by positivity)
  have hlim : Tendsto t atTop (𝓝 a) := by
    convert tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> simp [t]
  have hu : (⋃ k, Iic (t k)) = Iio a :=
    iUnion_Iic_eq_Iio_of_lt_of_tendsto hlt hlim
  have hm (ξ : Measure ℝ) [IsFiniteMeasure ξ] :
      Tendsto (fun k => ξ.real (Iic (t k))) atTop (𝓝 (ξ.real (Iio a))) := by
    have hh := tendsto_measure_iUnion_atTop (μ := ξ) (monotone_Iic.comp ht)
    simp only [Function.comp_def] at hh
    rw [hu] at hh
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hh
  exact le_of_tendsto ((hm μ).sub (hm ν)).abs (Eventually.of_forall (fun k => h (t k)))

theorem symmetricSqrtMeasure_kolmogorov_le_half (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (e : ℝ)
    (h : ∀ x : ℝ, |μ.real (Iic x) - ν.real (Iic x)| ≤ e) (x : ℝ) :
    |(symmetricSqrtMeasure μ).real (Iic x) -
      (symmetricSqrtMeasure ν).real (Iic x)| ≤ e / 2 := by
  by_cases hx : 0 ≤ x
  · rw [symmetricSqrtMeasure_cdf_nonneg μ x hx, symmetricSqrtMeasure_cdf_nonneg ν x hx]
    have heq (a b : ℝ) : (1 / 2 + 1 / 2 * a) - (1 / 2 + 1 / 2 * b) =
        (1 / 2 : ℝ) * (a - b) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [h (x ^ 2)]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [symmetricSqrtMeasure_cdf_neg μ x hx', symmetricSqrtMeasure_cdf_neg ν x hx']
    have heq (a b : ℝ) : 1 / 2 * (1 - a) - 1 / 2 * (1 - b) =
        -(1 / 2 : ℝ) * (a - b) := by ring
    rw [heq, abs_mul]
    norm_num
    linarith [abs_real_Iio_sub_le_of_Iic μ ν e h (x ^ 2)]

end ResidualSparseRepair20261106.DenseGaussian

#print axioms ResidualSparseRepair20261106.DenseGaussian.symmetricSqrtMeasure_kolmogorov_le_half

