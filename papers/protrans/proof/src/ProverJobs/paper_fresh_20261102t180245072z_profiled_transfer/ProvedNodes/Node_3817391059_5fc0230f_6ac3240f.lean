import Statlib.StatFoundation.BasicAnalysis.TailIntegral
import Statlib.StatFoundation.RandomVariable.SubExponential.subexp_mgf_le_of_sq_subgaussian
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Vocabulary
import ProverJobs.paper_fresh_20261102t180245072z_profiled_transfer.Base

namespace PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.paper_fresh_20261102t180245072z_profiled_transfer.ModelShiftLasso

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace ModelShiftLasso

set_option autoImplicit false in
theorem statopia_math_node_3817391059_5fc0230f : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (L : ℝ) (hL : 0 < L) (hX : HasSubGaussNorm L X μ),
    ∫ ω, (X ω) ^ 2 ∂μ ≤ 4 * L ^ 2 := by
  /- @proof-region region.target-node.session.f8723d1ad1e4da83 begin -/
  intro Ω _ μ _ X L hL hX
  have hX' : HasSubgaussianMGF X ⟨L ^ 2, sq_nonneg L⟩ μ := hX
  have hmemLp : MemLp X 2 μ := hX'.memLp 2
  have hInt : Integrable (fun ω => (X ω) ^ 2) μ := hmemLp.integrable_sq
  have hIntAbs : ∫ ω, |(X ω) ^ 2| ∂μ = ∫ ω, (X ω) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun ω => abs_of_nonneg (sq_nonneg (X ω))))
  have hlayer : ∫ ω, |(X ω) ^ 2| ∂μ
      = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < |(X ω) ^ 2|} :=
    Statlib.StatFoundation.BasicAnalysis.TailIntegral.integral_abs_eq_integral_measReal_gt
      μ (fun ω => (X ω) ^ 2) hInt
  have hset : ∀ t : ℝ, {ω | t < |(X ω) ^ 2|} = {ω | t < (X ω) ^ 2} := by
    intro t
    ext ω
    simp
  have hlayer' : ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < |(X ω) ^ 2|}
      = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < (X ω) ^ 2} := by
    have hfun : (fun t : ℝ => μ.real {ω | t < |(X ω) ^ 2|})
        = fun t : ℝ => μ.real {ω | t < (X ω) ^ 2} := by
      funext t
      exact congrArg (fun s => μ.real s) (hset t)
    rw [hfun]
  have htail : ∀ t : ℝ, 0 < t →
      μ.real {ω | t < (X ω) ^ 2} ≤ 2 * Real.exp (-t / (2 * L ^ 2)) := by
    intro t ht
    have hb : μ.real {ω | t ≤ (X ω) ^ 2} ≤ 2 * Real.exp (-t / (2 * L ^ 2)) := by
      have h0 := Statlib.StatFoundation.RandomVariable.SubExponential.sub_gauss_tail_sq
        (c := ⟨L ^ 2, sq_nonneg L⟩) hX' (le_of_lt ht)
      simpa using h0
    have hsub : {ω | t < (X ω) ^ 2} ⊆ {ω | t ≤ (X ω) ^ 2} := by
      intro ω h
      simp only [Set.mem_setOf_eq] at h ⊢
      exact le_of_lt h
    have hm : μ.real {ω | t < (X ω) ^ 2} ≤ μ.real {ω | t ≤ (X ω) ^ 2} :=
      MeasureTheory.measureReal_mono hsub
    exact hm.trans hb
  have hargfun : (fun t : ℝ => 2 * Real.exp (-t / (2 * L ^ 2)))
      = fun t : ℝ => 2 * Real.exp ((-(2 * L ^ 2)⁻¹) * t) := by
    funext t
    rw [show -t / (2 * L ^ 2) = (-(2 * L ^ 2)⁻¹) * t by ring_nf]
  have hgi : Integrable (fun t : ℝ => 2 * Real.exp (-t / (2 * L ^ 2)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hb : Integrable (fun t : ℝ => Real.exp ((-(2 * L ^ 2)⁻¹) * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      exp_neg_integrableOn_Ioi (0 : ℝ) (b := (2 * L ^ 2)⁻¹) (by positivity)
    rw [hargfun]
    exact hb.const_mul 2
  have hle : ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < (X ω) ^ 2}
      ≤ ∫ t in Set.Ioi (0 : ℝ), 2 * Real.exp (-t / (2 * L ^ 2)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hgi ?_
    · filter_upwards with t
      exact MeasureTheory.measureReal_nonneg
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact htail t ht
  have hIntExp : ∫ t in Set.Ioi (0 : ℝ), 2 * Real.exp (-t / (2 * L ^ 2)) = 4 * L ^ 2 := by
    have hpos : (0 : ℝ) < 2 * L ^ 2 := by positivity
    have ha : -(2 * L ^ 2)⁻¹ < 0 := by
      rw [neg_lt_zero]
      exact inv_pos.mpr hpos
    rw [hargfun, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi ha 0,
      mul_zero, Real.exp_zero]
    have hkey : (-(1 : ℝ)) / (-(2 * L ^ 2)⁻¹) = 2 * L ^ 2 := by
      rw [neg_div_neg_eq]
      simp
    rw [hkey]
    ring
  calc ∫ ω, (X ω) ^ 2 ∂μ
      = ∫ ω, |(X ω) ^ 2| ∂μ := hIntAbs.symm
    _ = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < |(X ω) ^ 2|} := hlayer
    _ = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < (X ω) ^ 2} := hlayer'
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), 2 * Real.exp (-t / (2 * L ^ 2)) := hle
    _ = 4 * L ^ 2 := hIntExp
  /- @proof-region region.target-node.session.f8723d1ad1e4da83 end -/

end ModelShiftLasso
end

