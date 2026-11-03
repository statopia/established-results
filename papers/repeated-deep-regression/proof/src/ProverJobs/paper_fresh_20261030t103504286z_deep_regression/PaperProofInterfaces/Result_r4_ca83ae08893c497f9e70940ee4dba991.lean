import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProofSupport.ExpectedSupRestriction
import Lean
import ProverJobs.job_paper_383d12cb48d74c8f98648c6beef78bb3.ExternalNodes.Node_94432b52633046d7cf21
import ProverJobs.job_paper_383d12cb48d74c8f98648c6beef78bb3.Vocabulary
import ProverJobs.job_paper_383d12cb48d74c8f98648c6beef78bb3.Base

namespace PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

theorem paper_383d12cb48d74c8f98648c6beef78bb3
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Type*}
    {n : ℕ} (hn : 0 < n)
    (W : Fin n → F → Ω → ℝ)
    (hW_meas : ∀ i f, Measurable (W i f))
    (hW_indep : iIndepFun (fun i : Fin n => fun ω => fun f : F => W i f ω) μ)
    (b2 b3 t : ℝ)
    (hW_bound : ∀ i f ω, |W i f ω| ≤ b2)
    (hb2 : 0 ≤ b2)
    (hW_int : ∀ i f, Integrable (W i f) μ)
    (hW_mean : ∀ i f, ∫ ω, W i f ω ∂μ = 0)
    (hW_sq_int : ∀ i f, Integrable (fun ω => (W i f ω) ^ 2) μ)
    (hW_sq : ∀ i f, ∫ ω, (W i f ω) ^ 2 ∂μ ≤ b3)
    (hb3 : 0 ≤ b3)
    (hsep : ∃ s : Set F, s.Countable ∧
      ∀ ω, (⨆ f : F, |(1 / (n : ℝ)) * ∑ i, W i f ω|) ≤
        ⨆ f : s, |(1 / (n : ℝ)) * ∑ i, W i f.1 ω|) :
    1 - Real.exp (-t) ≤
      μ.real {ω : Ω | (⨆ f : F, |(1 / (n : ℝ)) * ∑ i : Fin n, W i f ω|) ≤
        2 * expectedSup μ (fun f ω' => |(1 / (n : ℝ)) * ∑ i : Fin n, W i f ω'|)
          + Real.sqrt (8 * b3 * t / (n : ℝ)) + 35 * b2 * t / (n : ℝ)}
 := by
  classical
  by_cases ht : 0 < t
  · obtain ⟨s, hs, hcontrol⟩ := hsep
    have hs' : Countable s := hs.to_subtype
    let V : F → Ω → ℝ := fun f ω => |(1 / (n : ℝ)) * ∑ i, W i f ω|
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hV : ∀ f ω, 0 ≤ V f ω ∧ V f ω ≤ b2 := by
      intro f ω
      refine ⟨abs_nonneg _, ?_⟩
      dsimp [V]
      rw [abs_mul, abs_of_pos (div_pos one_pos hnR)]
      calc (1 / (n : ℝ)) * |∑ i, W i f ω|
          ≤ (1 / (n : ℝ)) * ∑ i, |W i f ω| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, b2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hW_bound i f ω) (by positivity)
        _ = b2 := by simp [hnR.ne']
    have hE := expectedSup_restrict_le μ V b2 hV s
    have hWs_indep : iIndepFun (fun i : Fin n => fun ω => fun f : s => W i f.1 ω) μ := by
      apply hW_indep.comp (fun _ => fun v : F → ℝ => fun f : s => v f.1)
      intro i
      exact measurable_pi_lambda _ (fun f => measurable_pi_apply f.1)
    have htail := massart_countable_average_tail hs' hn
      (fun i (f : s) ω => W i f.1 ω) (fun i f => hW_meas i f.1) hWs_indep
      b2 b3 t hb2 hb3 (fun i f => hW_bound i f.1) (fun i f => hW_mean i f.1)
      (fun i f => hW_sq_int i f.1) (fun i f => hW_sq i f.1) ht
    let D := 2 * expectedSup μ V + Real.sqrt (8 * b3 * t / (n : ℝ)) + 35 * b2 * t / (n : ℝ)
    let T := fun ω => ⨆ f : F, V f ω
    have hbad : μ.real {ω | D < T ω} ≤ Real.exp (-t) := by
      refine le_trans (measureReal_mono ?_) htail
      intro ω hω
      change 2 * expectedSup μ (fun f : s => V f.1) +
        Real.sqrt (8 * b3 * t / (n : ℝ)) + 35 * b2 * t / (n : ℝ) <
          ⨆ f : s, V f.1 ω
      have hD : 2 * expectedSup μ (fun f : s => V f.1) +
          Real.sqrt (8 * b3 * t / (n : ℝ)) + 35 * b2 * t / (n : ℝ) ≤ D := by
        dsimp [D]
        linarith [hE]
      exact lt_of_le_of_lt hD (lt_of_lt_of_le hω (hcontrol ω))
    have hunion : {ω | D < T ω} ∪ {ω | T ω ≤ D} = Set.univ := by
      ext ω
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_or_ge D (T ω)
    have hsum : (1 : ℝ) ≤ μ.real {ω | D < T ω} + μ.real {ω | T ω ≤ D} := by
      have h := measure_union_le (μ := μ) {ω | D < T ω} {ω | T ω ≤ D}
      rw [hunion, measure_univ] at h
      have h' := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩) h
      simpa only [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] using h'
    change 1 - Real.exp (-t) ≤ μ.real {ω | T ω ≤ D}
    linarith [hbad, hsum]
  · have h : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    exact le_trans (by linarith) measureReal_nonneg

end Statlib.Imported
