import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

namespace ResidualSparseRepair20261106.DenseGaussian

theorem gaussian_smoothing_exponents (x : ℝ) (hx : 1 < x) :
    0 < (x ^ (-(2 / 9 : ℝ))) ∧
      (x ^ (-(2 / 9 : ℝ))) < 1 ∧
      Real.sqrt ((x ^ (-(2 / 9 : ℝ)))) = (x ^ (-(1 / 9 : ℝ))) ∧
      1 / (x * (x ^ (-(2 / 9 : ℝ))) ^ 4) = (x ^ (-(1 / 9 : ℝ))) ∧
      ((x ^ (-(2 / 9 : ℝ))))⁻¹ / Real.sqrt x ≤ (x ^ (-(1 / 9 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have heta0 := Real.rpow_pos_of_pos hx0 (-(2 / 9 : ℝ))
  have heta1 : (x ^ (-(2 / 9 : ℝ))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  refine ⟨heta0, heta1, ?_, ?_, ?_⟩
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  · have hp : (x ^ (-(2 / 9 : ℝ))) ^ 4 = (x ^ (-(8 / 9 : ℝ))) := by
      rw [← Real.rpow_mul_natCast hx0.le]
      norm_num
    have hd : x * (x ^ (-(2 / 9 : ℝ))) ^ 4 = (x ^ (1 / 9 : ℝ)) := by
      calc
        _ = (x ^ (1 : ℝ)) * (x ^ (-(8 / 9 : ℝ))) := by rw [hp, Real.rpow_one]
        _ = (x ^ (1 + -(8 / 9 : ℝ))) := (Real.rpow_add hx0 _ _).symm
        _ = _ := by norm_num
    rw [hd, one_div, ← Real.rpow_neg hx0.le]
  · have he : ((x ^ (-(2 / 9 : ℝ))))⁻¹ / Real.sqrt x =
        (x ^ (-(5 / 18 : ℝ))) := by
      rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hx0.le,
        ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
      norm_num
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)

end ResidualSparseRepair20261106.DenseGaussian

#print axioms ResidualSparseRepair20261106.DenseGaussian.gaussian_smoothing_exponents

