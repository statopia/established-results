import Lean
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import Mathlib.Probability.CDF
import Mathlib.Analysis.Real.Pi.Bounds

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory

namespace ResidualSparseRepair20261106

noncomputable def measureCDF (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Iic x)).toReal

/-- Bai–Silverstein 2010, Theorem B.14, fixed parameters a=sqrt(3), B=4, A=20.
The source's modulus term is retained verbatim in mathematical content.
Official source: https://link.springer.com/content/pdf/bbm:978-1-4419-0661-8/1
Printed page 520, PDF page index 51. -/
axiom bai_smoothing_modulus :
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    Integrable (fun x => |measureCDF μ x - measureCDF ν x|) volume →
    ∀ (η : ℝ), 0 < η → η < 1 →
      sSup (Set.range fun x : ℝ => |measureCDF μ x - measureCDF ν x|) ≤
        (3 / (Real.pi - 3)) *
          ((∫ u in (-20 : ℝ)..20,
              ‖(∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
                (∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖) +
            2 * Real.pi * η⁻¹ *
              (∫ x in {x : ℝ | 4 < |x|}, |measureCDF μ x - measureCDF ν x|) +
            η⁻¹ * sSup (Set.range fun x : ℝ =>
              ∫ y in Set.Icc (-(2 * η * Real.sqrt 3)) (2 * η * Real.sqrt 3),
                |measureCDF ν (x + y) - measureCDF ν x|))

private theorem measureCDF_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (measureCDF μ) := by
  have he : measureCDF μ = cdf μ := by
    funext x
    exact (cdf_eq_real μ x).symm
  rw [he]
  exact (monotone_cdf μ).measurable

private theorem measureCDF_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ measureCDF μ x ∧ measureCDF μ x ≤ 1 := by
  have he : measureCDF μ x = cdf μ x := (cdf_eq_real μ x).symm
  rw [he]
  exact ⟨cdf_nonneg μ x, cdf_le_one μ x⟩

/-- Tail integrability plus bounded probability CDFs supplies B.14's global L1 premise. -/
theorem cdfDifference_integrable_of_tail (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (htail : IntegrableOn (fun x => |measureCDF μ x - measureCDF ν x|)
      {x : ℝ | 4 < |x|} volume) :
    Integrable (fun x => |measureCDF μ x - measureCDF ν x|) volume := by
  have hm : Measurable (fun x => |measureCDF μ x - measureCDF ν x|) :=
    ((measureCDF_measurable μ).sub (measureCDF_measurable ν)).abs
  have hi : IntegrableOn (fun x => |measureCDF μ x - measureCDF ν x|)
      (Set.Icc (-4 : ℝ) 4) volume := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hm.aestronglyMeasurable 1
    filter_upwards with x
    have hx := measureCDF_bounds μ x
    have hy := measureCDF_bounds ν x
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> linarith
  have he : Set.Icc (-4 : ℝ) 4 ∪ {x : ℝ | 4 < |x|} = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases hx : 4 < |x|
    · exact Or.inr hx
    · left
      have hh : |x| ≤ 4 := le_of_not_gt hx
      simpa only [abs_le] using hh
  have hh := hi.union htail
  rw [he] at hh
  simpa only [MeasureTheory.IntegrableOn, Measure.restrict_univ] using hh

/-- A bounded-density/Lipschitz specialization proved from the retained B.14 modulus form. -/
theorem bai_smoothing (M : ℝ) (hM : 0 < M) :
    ∃ Csm : ℝ, 1 ≤ Csm ∧
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        (∀ x y : ℝ, |measureCDF ν x - measureCDF ν y| ≤ M * |x - y|) →
        IntegrableOn (fun x => |measureCDF μ x - measureCDF ν x|)
          {x : ℝ | 4 < |x|} volume →
        ∀ (η : ℝ), 0 < η → η < 1 →
          sSup (Set.range fun x : ℝ => |measureCDF μ x - measureCDF ν x|) ≤
            Csm * ((∫ u in (-20 : ℝ)..20,
              ‖(∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
                (∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖) +
              η + η⁻¹ *
                (∫ x in {x : ℝ | 4 < |x|}, |measureCDF μ x - measureCDF ν x|)) := by
  let K : ℝ := 3 / (Real.pi - 3)
  have hK : 0 < K := div_pos (by norm_num) (sub_pos.mpr Real.pi_gt_three)
  let C : ℝ := 1 + K * (1 + 2 * Real.pi + 24 * M)
  have hC : 1 ≤ C := by
    have hh : 0 ≤ K * (1 + 2 * Real.pi + 24 * M) := mul_nonneg hK.le (by positivity)
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro μ ν _ _ hLip htail η hη hη1
  have hfull := cdfDifference_integrable_of_tail μ ν htail
  have hraw := bai_smoothing_modulus μ ν hfull η hη hη1
  let r : ℝ := 2 * η * Real.sqrt 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hJ : ∀ x : ℝ,
      (∫ y in Set.Icc (-r) r, |measureCDF ν (x + y) - measureCDF ν x|) ≤
        24 * M * η ^ 2 := by
    intro x
    have hb : ∀ y ∈ Set.Icc (-r) r,
        ‖|measureCDF ν (x + y) - measureCDF ν x|‖ ≤ M * r := by
      intro y hy
      rw [Real.norm_eq_abs, abs_abs]
      have hh := hLip (x + y) x
      have hyb : |y| ≤ r := abs_le.mpr hy
      have he : x + y - x = y := by ring
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hyb hM.le)
    have hh := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-r) r)
      (f := fun y => |measureCDF ν (x + y) - measureCDF ν x|)
      isCompact_Icc.measure_lt_top hb
    have hv : volume.real (Set.Icc (-r) r) = 2 * r := by
      rw [Real.volume_real_Icc_of_le (by linarith : -r ≤ r)]
      ring
    rw [hv] at hh
    have he : (M * r) * (2 * r) = 24 * M * η ^ 2 := by
      calc (M * r) * (2 * r) = 8 * M * η ^ 2 * (Real.sqrt 3) ^ 2 := by dsimp only [r]; ring
        _ = 24 * M * η ^ 2 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
    rw [he] at hh
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)
  have hsup : sSup (Set.range fun x : ℝ =>
      ∫ y in Set.Icc (-r) r, |measureCDF ν (x + y) - measureCDF ν x|) ≤
      24 * M * η ^ 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨x, rfl⟩
    exact hJ x
  have hmod : η⁻¹ * sSup (Set.range fun x : ℝ =>
      ∫ y in Set.Icc (-r) r, |measureCDF ν (x + y) - measureCDF ν x|) ≤ 24 * M * η := by
    calc _ ≤ η⁻¹ * (24 * M * η ^ 2) := mul_le_mul_of_nonneg_left hsup (inv_nonneg.mpr hη.le)
      _ = 24 * M * η := by field_simp
  let I : ℝ := ∫ u in (-20 : ℝ)..20,
      ‖(∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
        (∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖
  let T : ℝ := η⁻¹ * ∫ x in {x : ℝ | 4 < |x|}, |measureCDF μ x - measureCDF ν x|
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  have hT : 0 ≤ T := mul_nonneg (inv_nonneg.mpr hη.le) (integral_nonneg fun _ => abs_nonneg _)
  have hCK : K ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, mul_pos hK hM]
  have hCpi : K * (2 * Real.pi) ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, mul_pos hK hM]
  have hCM : K * (24 * M) ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, mul_pos hK Real.pi_pos]
  have hstep : sSup (Set.range fun x : ℝ => |measureCDF μ x - measureCDF ν x|) ≤
      K * (I + 2 * Real.pi * T + 24 * M * η) := by
    refine hraw.trans ?_
    apply mul_le_mul_of_nonneg_left _ hK.le
    change I + 2 * Real.pi * η⁻¹ * _ + η⁻¹ * _ ≤ _
    dsimp only [T]
    nlinarith [hmod]
  refine hstep.trans ?_
  change K * (I + 2 * Real.pi * T + 24 * M * η) ≤ C * (I + η + T)
  calc K * (I + 2 * Real.pi * T + 24 * M * η) =
      K * I + (K * (2 * Real.pi)) * T + (K * (24 * M)) * η := by ring
    _ ≤ C * I + C * T + C * η :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCK hI)
        (mul_le_mul_of_nonneg_right hCpi hT)) (mul_le_mul_of_nonneg_right hCM hη.le)
    _ = C * (I + η + T) := by ring

#print axioms bai_smoothing
end ResidualSparseRepair20261106

