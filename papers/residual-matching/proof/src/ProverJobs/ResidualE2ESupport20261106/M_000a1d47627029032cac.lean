import Lean
import ProverJobs.ResidualE2ESupport20261106.M_c5aeedf2f1c047528231

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualLoss20261106.Statlib.Imported

/-- One deterministic threshold supplies all small-error requirements in finite
spectral calibration. Its constants do not depend on dimensions or the law. -/
theorem calibration_growth_threshold (CI CL edge cb : ℝ)
    (hCI : 0 < CI) (hCL : 0 < CL) (hedge : 0 < edge) (hcb : 0 < cb) :
    ∃ m0 : ℕ, 3 ≤ m0 ∧ ∀ m : ℕ, m0 ≤ m →
      1 ≤ Real.log (m : ℝ) ∧
      CI * deltaM m ≤ 1 ∧ CL * deltaM m ≤ edge / 2 ∧
      ((CI + CL) / cb) * deltaM m ≤ 1 / 2 := by
  let L : ℝ := max 1 (max CI (max (2 * CL / edge) (2 * ((CI + CL) / cb))))
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp L)
  refine ⟨max 3 N, le_max_left _ _, ?_⟩
  intro m hm
  have hNm : N ≤ m := le_trans (le_max_right 3 N) hm
  have hmlarge : Real.exp L < (m : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNm)
  have hlogL : L ≤ Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos L) hmlarge
    simpa only [Real.log_exp] using h.le
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hLCI : CI ≤ L := le_trans (le_max_left CI _) (le_max_right 1 _)
  have hLCL : 2 * CL / edge ≤ L :=
    le_trans (le_max_left _ _) (le_trans (le_max_right CI _) (le_max_right 1 _))
  have hLcal : 2 * ((CI + CL) / cb) ≤ L :=
    le_trans (le_max_right _ _) (le_trans (le_max_right CI _) (le_max_right 1 _))
  have hlog1 : 1 ≤ Real.log (m : ℝ) := le_trans hL1 hlogL
  have hlogpos : 0 < Real.log (m : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  refine ⟨hlog1, ?_, ?_, ?_⟩
  · rw [deltaM, ← div_eq_mul_inv, div_le_iff₀ hlogpos]
    simpa only [one_mul] using le_trans hLCI hlogL
  · rw [deltaM, ← div_eq_mul_inv, div_le_iff₀ hlogpos]
    have h := (div_le_iff₀ hedge).1 (le_trans hLCL hlogL)
    nlinarith
  · rw [deltaM, ← div_eq_mul_inv, div_le_iff₀ hlogpos]
    have h := le_trans hLcal hlogL
    nlinarith

end ResidualLoss20261106.Statlib.Imported
#print axioms ResidualLoss20261106.Statlib.Imported.calibration_growth_threshold

