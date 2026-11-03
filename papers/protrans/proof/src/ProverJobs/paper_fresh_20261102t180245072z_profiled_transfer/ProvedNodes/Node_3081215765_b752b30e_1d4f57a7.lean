import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.ProvedNodes.Node_3817391059_5fc0230f_6ac3240f

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

set_option autoImplicit false in
theorem statopia_math_node_3081215765_b752b30e : ∀ (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (L : ℝ) (hL : 0 < L)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → Fin p → ℝ) (H : Ω → Fin q → ℝ)
    (hF : ∀ j : Fin p, HasSubGaussNorm L (fun ω => F ω j) μ)
    (hH : ∀ s : Fin q, HasSubGaussNorm L (fun ω => H ω s) μ),
    (∀ (j : Fin p) (s : Fin q), Integrable (fun ω => F ω j * H ω s) μ) ∧
      maxAbs (fun j => Real.sqrt (∑ s : Fin q, (∫ ω, F ω j * H ω s ∂μ) ^ 2)) ≤
        (4 * L ^ 2) * Real.sqrt (q : ℝ) := by
  /- @proof-region region.target-node.session.f5e87d2e0fd6b19a begin -/
  intro p q hp hq L hL Ω _ μ _ F H hF hH
  refine ⟨?_, ?_⟩
  · intro j s
    have hj : MemLp (fun ω => F ω j) 2 μ := HasSubgaussianMGF.memLp (hF j) 2
    have hs : MemLp (fun ω => H ω s) 2 μ := HasSubgaussianMGF.memLp (hH s) 2
    simpa [Pi.mul_apply] using hj.integrable_mul hs
  · have h2F : ∀ j : Fin p, ∫ ω, (F ω j) ^ 2 ∂μ ≤ 4 * L ^ 2 :=
      fun j => statopia_math_node_3817391059_5fc0230f Ω μ (fun ω => F ω j) L hL (hF j)
    have h2H : ∀ s : Fin q, ∫ ω, (H ω s) ^ 2 ∂μ ≤ 4 * L ^ 2 :=
      fun s => statopia_math_node_3817391059_5fc0230f Ω μ (fun ω => H ω s) L hL (hH s)
    have hentry : ∀ (j : Fin p) (s : Fin q), |∫ ω, F ω j * H ω s ∂μ| ≤ 4 * L ^ 2 := by
      intro j s
      have hj : MemLp (fun ω => F ω j) 2 μ := HasSubgaussianMGF.memLp (hF j) 2
      have hs : MemLp (fun ω => H ω s) 2 μ := HasSubgaussianMGF.memLp (hH s) 2
      have hFint : Integrable (fun ω => (F ω j) ^ 2) μ := MeasureTheory.MemLp.integrable_sq hj
      have hHint : Integrable (fun ω => (H ω s) ^ 2) μ := MeasureTheory.MemLp.integrable_sq hs
      have hprod : Integrable (fun ω => F ω j * H ω s) μ := by
        simpa [Pi.mul_apply] using hj.integrable_mul hs
      have habs : Integrable (fun ω => |F ω j * H ω s|) μ := by
        simpa only [Real.norm_eq_abs] using hprod.norm
      have hsum : Integrable (fun ω => (1 / 2) * (F ω j) ^ 2 + (1 / 2) * (H ω s) ^ 2) μ :=
        (hFint.const_mul (1 / 2)).add (hHint.const_mul (1 / 2))
      have hpoint : (fun ω => |F ω j * H ω s|)
          ≤ (fun ω => (1 / 2) * (F ω j) ^ 2 + (1 / 2) * (H ω s) ^ 2) := by
        intro ω
        change |F ω j * H ω s| ≤ (1 / 2) * (F ω j) ^ 2 + (1 / 2) * (H ω s) ^ 2
        have h := sq_nonneg (|F ω j| - |H ω s|)
        rw [abs_mul]
        nlinarith [sq_abs (F ω j), sq_abs (H ω s), h]
      have hmono : ∫ ω, |F ω j * H ω s| ∂μ
          ≤ ∫ ω, ((1 / 2) * (F ω j) ^ 2 + (1 / 2) * (H ω s) ^ 2) ∂μ :=
        MeasureTheory.integral_mono habs hsum hpoint
      have hsplit : ∫ ω, ((1 / 2) * (F ω j) ^ 2 + (1 / 2) * (H ω s) ^ 2) ∂μ
          = (1 / 2) * (∫ ω, (F ω j) ^ 2 ∂μ) + (1 / 2) * (∫ ω, (H ω s) ^ 2 ∂μ) := by
        rw [MeasureTheory.integral_add (hFint.const_mul (1 / 2)) (hHint.const_mul (1 / 2)),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hbd : (1 / 2) * (∫ ω, (F ω j) ^ 2 ∂μ) + (1 / 2) * (∫ ω, (H ω s) ^ 2 ∂μ)
          ≤ 4 * L ^ 2 := by
        linarith [h2F j, h2H s]
      calc |∫ ω, F ω j * H ω s ∂μ| ≤ ∫ ω, |F ω j * H ω s| ∂μ := by
            simpa only [Real.norm_eq_abs] using
              MeasureTheory.norm_integral_le_integral_norm (fun ω => F ω j * H ω s)
        _ ≤ ∫ ω, ((1 / 2) * (F ω j) ^ 2 + (1 / 2) * (H ω s) ^ 2) ∂μ := hmono
        _ = (1 / 2) * (∫ ω, (F ω j) ^ 2 ∂μ) + (1 / 2) * (∫ ω, (H ω s) ^ 2 ∂μ) := hsplit
        _ ≤ 4 * L ^ 2 := hbd
    have hrow : ∀ j : Fin p,
        Real.sqrt (∑ s, (∫ ω, F ω j * H ω s ∂μ) ^ 2) ≤ (4 * L ^ 2) * Real.sqrt (q : ℝ) := by
      intro j
      have hC : 0 ≤ 4 * L ^ 2 := by positivity
      have hsum_le : ∑ s : Fin q, (∫ ω, F ω j * H ω s ∂μ) ^ 2 ≤ ∑ s : Fin q, (4 * L ^ 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro s _
        have h := hentry j s
        have h4 : 0 ≤ (4 * L ^ 2 - |∫ ω, F ω j * H ω s ∂μ|)
            * (4 * L ^ 2 + |∫ ω, F ω j * H ω s ∂μ|) :=
          mul_nonneg (by linarith) (by linarith [abs_nonneg (∫ ω, F ω j * H ω s ∂μ)])
        have hkey : |∫ ω, F ω j * H ω s ∂μ| ^ 2 ≤ (4 * L ^ 2) ^ 2 := by
          nlinarith [h4]
        simpa [sq_abs] using hkey
      have hcard : (∑ s : Fin q, (4 * L ^ 2) ^ 2) = (q : ℝ) * (4 * L ^ 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hcard] at hsum_le
      have hsqrt_le := Real.sqrt_le_sqrt hsum_le
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (q : ℝ)), Real.sqrt_sq hC] at hsqrt_le
      rw [mul_comm (Real.sqrt (q : ℝ)) (4 * L ^ 2)] at hsqrt_le
      exact hsqrt_le
    unfold maxAbs
    refine csSup_le ?_ ?_
    · exact ⟨_, ⟨⟨0, by omega⟩, rfl⟩⟩
    · rintro y ⟨j, rfl⟩
      change |Real.sqrt (∑ s, (∫ ω, F ω j * H ω s ∂μ) ^ 2)| ≤ (4 * L ^ 2) * Real.sqrt (q : ℝ)
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hrow j
  /- @proof-region region.target-node.session.f5e87d2e0fd6b19a end -/

end ModelShiftLasso
end

