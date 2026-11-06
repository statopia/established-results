import Lean
import Mathlib

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory
namespace ResidualSparseRepair20261106.GaussianCalculus

theorem complex_second_moment_sub_mean_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℂ) (hf : MemLp f 2 μ) :
    (∫ ω, (f ω - ∫ ω', f ω' ∂μ) ^ 2 ∂μ) =
      (∫ ω, (f ω) ^ 2 ∂μ) - (∫ ω, f ω ∂μ) ^ 2 := by
  let a := ∫ ω, f ω ∂μ
  have hi : Integrable f μ := hf.integrable (by norm_num)
  have h2 : Integrable (fun ω => f ω * f ω) μ := hf.integrable_mul hf
  have he : (fun ω => (f ω - a) ^ 2) =
      (fun ω => (f ω * f ω - f ω * a) - (a * f ω - a * a)) := by
    funext ω
    ring
  rw [he]
  have houter := integral_sub (h2.sub (hi.mul_const a))
    ((hi.const_mul a).sub (integrable_const (a * a)))
  change (∫ ω, (f ω * f ω - f ω * a) - (a * f ω - a * a) ∂μ) = _
  calc
    _ = (∫ ω, f ω * f ω - f ω * a ∂μ) -
        (∫ ω, a * f ω - a * a ∂μ) := houter
    _ = ((∫ ω, f ω * f ω ∂μ) - (∫ ω, f ω * a ∂μ)) -
        ((∫ ω, a * f ω ∂μ) - (∫ _ω, a * a ∂μ)) := by
      congr 1
      · exact integral_sub h2 (hi.mul_const a)
      · exact integral_sub (hi.const_mul a) (integrable_const (a * a))
    _ = _ := by
      rw [integral_mul_const, integral_const_mul]
    
      simp only [integral_const, probReal_univ, one_smul]
      dsimp [a]
      simp only [pow_two]
      ring
theorem norm_complex_second_moment_sub_mean_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℂ) (hf : MemLp f 2 μ) :
    ‖(∫ ω, (f ω) ^ 2 ∂μ) - (∫ ω, f ω ∂μ) ^ 2‖ ≤
      ∫ ω, ‖f ω - ∫ ω', f ω' ∂μ‖ ^ 2 ∂μ := by
  rw [← complex_second_moment_sub_mean_sq μ f hf]
  calc ‖∫ ω, (f ω - ∫ ω', f ω' ∂μ) ^ 2 ∂μ‖
      ≤ ∫ ω, ‖(f ω - ∫ ω', f ω' ∂μ) ^ 2‖ ∂μ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_pow]

end ResidualSparseRepair20261106.GaussianCalculus

#print axioms ResidualSparseRepair20261106.GaussianCalculus.norm_complex_second_moment_sub_mean_sq_le

