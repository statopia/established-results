import Lean
import ProverJobs.ResidualE2ESupport20261106.ExternalNodes.Node_610ef984489599a94e55

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory

namespace ResidualSparseRepair20261106.DenseGaussian

/-- The reviewed finite-window B.14 inequality specialized to a Hölder-one-half target CDF. -/
theorem bai_smoothing_holder_half (M : ℝ) (hM : 0 < M) :
    ∃ Csm : ℝ, 1 ≤ Csm ∧
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        (∀ x y : ℝ, |measureCDF ν x - measureCDF ν y| ≤ M * Real.sqrt |x - y|) →
        IntegrableOn (fun x => |measureCDF μ x - measureCDF ν x|)
          {x : ℝ | 4 < |x|} volume →
        ∀ (η : ℝ), 0 < η → η < 1 →
          sSup (Set.range fun x : ℝ => |measureCDF μ x - measureCDF ν x|) ≤
            Csm * ((∫ u in (-20 : ℝ)..20,
              ‖(∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
                (∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖) +
              Real.sqrt η + η⁻¹ *
                (∫ x in {x : ℝ | 4 < |x|}, |measureCDF μ x - measureCDF ν x|)) := by
  let K : ℝ := 3 / (Real.pi - 3)
  have hK : 0 < K := div_pos (by norm_num) (sub_pos.mpr Real.pi_gt_three)
  let C : ℝ := 1 + K * (1 + 2 * Real.pi + 16 * M)
  have hC : 1 ≤ C := by
    have hh : 0 ≤ K * (1 + 2 * Real.pi + 16 * M) := mul_nonneg hK.le (by positivity)
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro μ ν _ _ hLip htail η hη hη1
  have hfull := cdfDifference_integrable_of_tail μ ν htail
  have hraw := bai_smoothing_modulus μ ν hfull η hη hη1
  let r : ℝ := 2 * η * Real.sqrt 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hrbound : r ≤ 4 * η := by
    have hs : Real.sqrt (3 : ℝ) ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    dsimp only [r]
    nlinarith [mul_le_mul_of_nonneg_left hs hη.le]
  have hJ : ∀ x : ℝ,
      (∫ y in Set.Icc (-r) r, |measureCDF ν (x + y) - measureCDF ν x|) ≤
        16 * M * η * Real.sqrt η := by
    intro x
    have hb : ∀ y ∈ Set.Icc (-r) r,
        ‖|measureCDF ν (x + y) - measureCDF ν x|‖ ≤ 2 * M * Real.sqrt η := by
      intro y hy
      rw [Real.norm_eq_abs, abs_abs]
      have hh := hLip (x + y) x
      have hyb : |y| ≤ 4 * η := (abs_le.mpr hy).trans hrbound
      have hs : Real.sqrt |y| ≤ 2 * Real.sqrt η := by
        refine (Real.sqrt_le_sqrt hyb).trans_eq ?_
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      have he : x + y - x = y := by ring
      rw [he] at hh
      calc _ ≤ M * Real.sqrt |y| := hh
        _ ≤ M * (2 * Real.sqrt η) := mul_le_mul_of_nonneg_left hs hM.le
        _ = 2 * M * Real.sqrt η := by ring
    have hh := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-r) r)
      (f := fun y => |measureCDF ν (x + y) - measureCDF ν x|)
      isCompact_Icc.measure_lt_top hb
    have hv : volume.real (Set.Icc (-r) r) = 2 * r := by
      rw [Real.volume_real_Icc_of_le (by linarith : -r ≤ r)]
      ring
    rw [hv] at hh
    have hbound : (2 * M * Real.sqrt η) * (2 * r) ≤ 16 * M * η * Real.sqrt η := by
      have hc : 0 ≤ 2 * M * Real.sqrt η := by positivity
      have hb := mul_le_mul_of_nonneg_left (show 2 * r ≤ 8 * η by linarith) hc
      nlinarith [hb]
    simp only [Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans (hh.trans hbound)
  have hsup : sSup (Set.range fun x : ℝ =>
      ∫ y in Set.Icc (-r) r, |measureCDF ν (x + y) - measureCDF ν x|) ≤
      16 * M * η * Real.sqrt η := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨x, rfl⟩
    exact hJ x
  have hmod : η⁻¹ * sSup (Set.range fun x : ℝ =>
      ∫ y in Set.Icc (-r) r, |measureCDF ν (x + y) - measureCDF ν x|) ≤
        16 * M * Real.sqrt η := by
    calc _ ≤ η⁻¹ * (16 * M * η * Real.sqrt η) :=
        mul_le_mul_of_nonneg_left hsup (inv_nonneg.mpr hη.le)
      _ = 16 * M * Real.sqrt η := by field_simp
  let I : ℝ := ∫ u in (-20 : ℝ)..20,
      ‖(∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂μ) -
        (∫ x, ((x : ℂ) - (u : ℂ) - (η : ℂ) * Complex.I)⁻¹ ∂ν)‖
  let T : ℝ := η⁻¹ * ∫ x in {x : ℝ | 4 < |x|}, |measureCDF μ x - measureCDF ν x|
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  have hT : 0 ≤ T := mul_nonneg (inv_nonneg.mpr hη.le) (integral_nonneg fun _ => abs_nonneg _)
  have hCK : K ≤ C := by dsimp [C]; nlinarith [mul_pos hK Real.pi_pos, mul_pos hK hM]
  have hCpi : K * (2 * Real.pi) ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, mul_pos hK hM]
  have hCM : K * (16 * M) ≤ C := by dsimp [C]; nlinarith [Real.pi_pos, mul_pos hK Real.pi_pos]
  have hstep : sSup (Set.range fun x : ℝ => |measureCDF μ x - measureCDF ν x|) ≤
      K * (I + 2 * Real.pi * T + 16 * M * Real.sqrt η) := by
    refine hraw.trans ?_
    apply mul_le_mul_of_nonneg_left _ hK.le
    change I + 2 * Real.pi * η⁻¹ * _ + η⁻¹ * _ ≤ _
    dsimp only [T]
    nlinarith [hmod]
  refine hstep.trans ?_
  change K * (I + 2 * Real.pi * T + 16 * M * Real.sqrt η) ≤ C * (I + Real.sqrt η + T)
  calc K * (I + 2 * Real.pi * T + 16 * M * Real.sqrt η) =
      K * I + (K * (2 * Real.pi)) * T + (K * (16 * M)) * Real.sqrt η := by ring
    _ ≤ C * I + C * T + C * Real.sqrt η :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCK hI)
        (mul_le_mul_of_nonneg_right hCpi hT))
        (mul_le_mul_of_nonneg_right hCM (Real.sqrt_nonneg η))
    _ = C * (I + Real.sqrt η + T) := by ring

#print axioms bai_smoothing_holder_half
end ResidualSparseRepair20261106.DenseGaussian

