import Lean
import ProverJobs.ResidualE2ESupport20261106.M_71771031c80e5d133256

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
namespace ResidualMaskRepair20261106

/-- An a.e. binary mask has a pointwise binary version with exactly the same law. -/
noncomputable def binaryVersion (x : ℝ) : ℝ := if x = 1 then 1 else 0

lemma binaryVersion_measurable : Measurable binaryVersion := by
  exact measurable_const.ite (measurableSet_singleton 1) measurable_const

lemma binaryVersion_binary (x : ℝ) : binaryVersion x = 0 ∨ binaryVersion x = 1 := by
  by_cases hx : x = 1 <;> simp [binaryVersion, hx]

lemma binaryVersion_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    (fun ω => binaryVersion (X ω)) =ᵐ[μ] X := by
  filter_upwards [hX] with ω hω
  rcases hω with h | h <;> simp [binaryVersion, h]

lemma binaryVersion_independent {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) (hX : iIndepFun X μ) :
    iIndepFun (fun i ω => binaryVersion (X i ω)) μ :=
  hX.comp (fun _ => binaryVersion) (fun _ => binaryVersion_measurable)

lemma binaryVersion_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    (∫ ω, binaryVersion (X ω) ∂μ) = ∫ ω, X ω ∂μ :=
  integral_congr_ae (binaryVersion_ae μ X hX)

lemma normalized_binary_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (x : ℝ) :
    |(binaryVersion x - p) / Real.sqrt ((m : ℝ) * p)| ≤
      1 / Real.sqrt ((m : ℝ) * p) := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  rcases binaryVersion_binary x with h | h
  · rw [h, zero_sub, abs_neg, abs_of_nonneg hp0]
    exact hp1
  · rw [h, abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith

#print axioms binaryVersion_independent
#print axioms normalized_binary_bound
end ResidualMaskRepair20261106

