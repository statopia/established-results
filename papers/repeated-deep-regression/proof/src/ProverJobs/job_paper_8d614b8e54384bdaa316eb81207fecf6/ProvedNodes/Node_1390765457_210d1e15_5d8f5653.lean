import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_1390765457_210d1e15 : ∀ (B1 : ℝ) (hB1 : 0 < B1)
    {Ωs : Type*} [MeasurableSpace Ωs]
    (PX : Measure Ωs) (hPX : IsProbabilityMeasure PX)
    (f0 f : Ωs → ℝ) (hf0_meas : Measurable f0) (hf_meas : Measurable f)
    (hf0_bound : ∀ x : Ωs, |f0 x| ≤ B1)
    (hf_bound : ∀ x : Ωs, |f x| ≤ B1),
    (∀ x : Ωs,
        0 ≤ (f x - f0 x) ^ 2 ∧ (f x - f0 x) ^ 2 ≤ 4 * B1 ^ 2 ∧
          ((f x - f0 x) ^ 2) ^ 2 ≤ 4 * B1 ^ 2 * ((f x - f0 x) ^ 2)) ∧
    (Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX →
      (0 ≤ predError PX f0 f ∧ predError PX f0 f ≤ 4 * B1 ^ 2 ∧
        Integrable (fun x : Ωs => ((f x - f0 x) ^ 2) ^ 2) PX ∧
        (∫ x : Ωs, ((f x - f0 x) ^ 2) ^ 2 ∂PX) ≤ 4 * B1 ^ 2 * predError PX f0 f ∧
        (predError PX f0 f = 0 → (fun x : Ωs => (f x - f0 x) ^ 2) =ᵐ[PX] 0))) ∧
    (∀ (Ωrand : Type*) [MeasurableSpace Ωrand] (P : Measure Ωrand)
        (hP : IsProbabilityMeasure P),
      ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
        (X : Fin n → Fin m → Ωrand → Ωs),
        (∀ (i : Fin n) (j : Fin m), Measurable (X i j)) →
        (∀ (i : Fin n) (j : Fin m), Measure.map (X i j) P = PX) →
        Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX →
        ∀ ω : Ωrand,
          0 ≤ empSqDisc X f0 ω f ∧ empSqDisc X f0 ω f ≤ 4 * B1 ^ 2 ∧
            |empSqDisc X f0 ω f - predError PX f0 f| ≤ 4 * B1 ^ 2 ∧
            (predError PX f0 f = 0 →
              ∀ (i : Fin n) (j : Fin m),
                ∀ᵐ ω ∂P, (f (X i j ω) - f0 (X i j ω)) ^ 2 = 0)) := by
  /- @proof-region region.target-node.session.7642047f0d982d8b begin -/
  intro B1 hB1 Ωs _ PX _ f0 f hf0_meas hf_meas hf0_bound hf_bound
  have key : ∀ x : Ωs,
      0 ≤ (f x - f0 x) ^ 2 ∧
        (f x - f0 x) ^ 2 ≤ 4 * B1 ^ 2 ∧
          ((f x - f0 x) ^ 2) ^ 2 ≤ 4 * B1 ^ 2 * ((f x - f0 x) ^ 2) := by
    intro x
    have habs : |f x - f0 x| ≤ 2 * B1 := by
      have hfx := hf_bound x
      have hf0x := hf0_bound x
      rw [abs_le] at hfx hf0x
      rw [abs_le]
      constructor <;> linarith [hfx.1, hfx.2, hf0x.1, hf0x.2]
    have hsq : (f x - f0 x) ^ 2 ≤ 4 * B1 ^ 2 := by
      have hb := habs
      rw [abs_le] at hb
      nlinarith [hb.1, hb.2]
    have hsq2 : ((f x - f0 x) ^ 2) ^ 2 ≤ 4 * B1 ^ 2 * ((f x - f0 x) ^ 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (f x - f0 x))]
    exact ⟨sq_nonneg _, hsq, hsq2⟩
  have hpred0 : ∀ (_hint : Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX),
      0 ≤ predError PX f0 f := by
    intro hint
    unfold predError
    exact integral_nonneg (fun x => sq_nonneg (f x - f0 x))
  have hpred4 : ∀ (_hint : Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX),
      predError PX f0 f ≤ 4 * B1 ^ 2 := by
    intro hint
    have hmono : ∫ x, (f x - f0 x) ^ 2 ∂PX ≤ ∫ x, (4 * B1 ^ 2 : ℝ) ∂PX :=
      integral_mono hint (integrable_const (4 * B1 ^ 2)) (fun x => (key x).2.1)
    have hc : ∫ x : Ωs, (4 * B1 ^ 2 : ℝ) ∂PX = 4 * B1 ^ 2 := by simp
    unfold predError
    linarith [hc, hmono]
  have hintSq : ∀ (_hint : Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX),
      Integrable (fun x : Ωs => ((f x - f0 x) ^ 2) ^ 2) PX := by
    intro hint
    have hdom : Integrable (fun x : Ωs => 4 * B1 ^ 2 * ((f x - f0 x) ^ 2)) PX :=
      hint.const_mul (4 * B1 ^ 2)
    have hg1 : Measurable (fun x : Ωs => f x - f0 x) := hf_meas.sub hf0_meas
    have hg2 : Measurable (fun x : Ωs => (f x - f0 x) ^ 2) := by
      simpa [pow_two] using hg1.mul hg1
    have hg3 : Measurable (fun x : Ωs => ((f x - f0 x) ^ 2) ^ 2) := by
      simpa [pow_two] using hg2.mul hg2
    refine hdom.mono' hg3.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (key x).2.2
  have hintInt : ∀ (_hint : Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX),
      ∫ x, ((f x - f0 x) ^ 2) ^ 2 ∂PX ≤ 4 * B1 ^ 2 * predError PX f0 f := by
    intro hint
    have hdom : Integrable (fun x : Ωs => 4 * B1 ^ 2 * ((f x - f0 x) ^ 2)) PX :=
      hint.const_mul (4 * B1 ^ 2)
    have hmono : ∫ x, ((f x - f0 x) ^ 2) ^ 2 ∂PX ≤ ∫ x, 4 * B1 ^ 2 * ((f x - f0 x) ^ 2) ∂PX :=
      integral_mono (hintSq hint) hdom (fun x => (key x).2.2)
    have hcm : ∫ x, 4 * B1 ^ 2 * ((f x - f0 x) ^ 2) ∂PX
        = 4 * B1 ^ 2 * ∫ x, ((f x - f0 x) ^ 2) ∂PX :=
      integral_const_mul (4 * B1 ^ 2) (fun x => ((f x - f0 x) ^ 2))
    unfold predError
    linarith [hmono, hcm]
  have hae : ∀ (_hint : Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX),
      predError PX f0 f = 0 → ∀ᵐ x ∂PX, (f x - f0 x) ^ 2 = 0 := by
    intro hint hzero
    unfold predError at hzero
    have hnn : ∀ᵐ x ∂PX, 0 ≤ (f x - f0 x) ^ 2 := by
      filter_upwards with x
      exact sq_nonneg (f x - f0 x)
    exact (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hzero
  refine ⟨key, ?_, ?_⟩
  · intro hint
    exact ⟨hpred0 hint, hpred4 hint, hintSq hint, hintInt hint, hae hint⟩
  · intro Ωrand _ P hP n m hn hm X hXmeas hlaw hint
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := mul_pos hnR hmR
    have hcoef : 0 < ((n : ℝ) * (m : ℝ))⁻¹ := inv_pos.mpr hNpos
    have hcalc : ((n : ℝ) * (m : ℝ))⁻¹ * ((n : ℝ) * (m : ℝ) * (4 * B1 ^ 2)) = 4 * B1 ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]
    intro ω
    unfold empSqDisc
    have hS0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (key (X i j ω)).1))
    have hSle : ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2
        ≤ (n : ℝ) * (m : ℝ) * (4 * B1 ^ 2) := by
      calc ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2
          ≤ ∑ i : Fin n, ∑ j : Fin m, (4 * B1 ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact (key (X i j ω)).2.1
        _ = (n : ℝ) * (m : ℝ) * (4 * B1 ^ 2) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hS'0 : 0 ≤ ((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2 :=
      mul_nonneg (le_of_lt hcoef) hS0
    have hS'le : ((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2 ≤ 4 * B1 ^ 2 := by
      have h1 : ((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m, (f (X i j ω) - f0 (X i j ω)) ^ 2
          ≤ ((n : ℝ) * (m : ℝ))⁻¹ * ((n : ℝ) * (m : ℝ) * (4 * B1 ^ 2)) :=
        mul_le_mul_of_nonneg_left hSle (le_of_lt hcoef)
      rw [hcalc] at h1
      exact h1
    refine ⟨hS'0, hS'le, ?_, ?_⟩
    · have hp0 := hpred0 hint
      have hp4 := hpred4 hint
      rw [abs_le]
      constructor <;> linarith [hS'le, hS'0, hp0, hp4]
    · intro hzero i j
      have hb := hae hint hzero
      have hp : MeasurableSet {y : Ωs | (f y - f0 y) ^ 2 = 0} := by
        have hg1 : Measurable (fun y : Ωs => f y - f0 y) := hf_meas.sub hf0_meas
        have hg2 : Measurable (fun y : Ωs => (f y - f0 y) ^ 2) := by
          simpa [pow_two] using hg1.mul hg1
        exact hg2 (measurableSet_singleton (0 : ℝ))
      have hmap : ∀ᵐ y ∂Measure.map (X i j) P, (f y - f0 y) ^ 2 = 0 := by
        rw [hlaw i j]
        exact hb
      exact (MeasureTheory.ae_map_iff ((hXmeas i j).aemeasurable) hp).mp hmap

  /- @proof-region region.target-node.session.7642047f0d982d8b end -/

end

end Statlib.Imported

