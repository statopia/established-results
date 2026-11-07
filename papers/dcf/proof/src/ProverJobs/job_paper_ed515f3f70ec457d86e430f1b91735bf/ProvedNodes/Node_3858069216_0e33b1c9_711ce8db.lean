import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3858069216_0e33b1c9 : ∀ (α : Type*) [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (f : ℝ → α → ℝ) (hf : Measurable (Function.uncurry f)) (K : ℝ)
    (hK : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Integrable (f t) P ∧
        (∫ x, |f t x| ∂P) ≤ K * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)),
    Integrable (fun x => ∫ t in (0 : ℝ)..1, f t x) P ∧
      (∫ x, |∫ t in (0 : ℝ)..1, f t x| ∂P) ≤ 4 * K := by
  /- @proof-region region.target-node.session.2f3f1ce6913dbd40 begin -/
  intro α _ P _ f hf K hK
  have hKnn : 0 ≤ K := by
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have hpos : (0 : ℝ) < (Real.sqrt ((1 : ℝ) / 2))⁻¹ + (Real.sqrt (1 - 1 / 2))⁻¹ := by positivity
    have h0 : (0 : ℝ) ≤ ∫ x, |f (1 / 2) x| ∂P := integral_nonneg fun x => abs_nonneg _
    have hbound := (hK (1 / 2) hhalf).2
    by_contra hneg
    push_neg at hneg
    have hlt : K * ((Real.sqrt ((1 : ℝ) / 2))⁻¹ + (Real.sqrt (1 - 1 / 2))⁻¹) < 0 :=
      mul_neg_of_neg_of_pos hneg hpos
    linarith
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ∈ Set.Ioo (0 : ℝ) 1 := by
    have hne1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp
    have hmem : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ∈ Set.Ioc (0 : ℝ) 1 :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    have hne1' : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ≠ 1 :=
      (MeasureTheory.ae_mono Measure.restrict_le_self) hne1
    filter_upwards [hmem, hne1'] with t ht ht1
    exact ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  have hsqrt_eq : ∀ y : ℝ, 0 ≤ y → (Real.sqrt y)⁻¹ = y ^ (-(1 / 2) : ℝ) := by
    intro y hy
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (x := y) hy (1 / 2 : ℝ)]
  have h1 : Integrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) (f := fun t : ℝ => t ^ (-(1 / 2) : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := -(1 / 2)) (by norm_num))
  have h2 : Integrable (fun t : ℝ => (1 - t) ^ (-(1 / 2) : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) volume 1 0 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hcomp : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2) : ℝ)) volume 0 1 := by
      simpa using hbase.comp_sub_left 1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
      (f := fun t : ℝ => (1 - t) ^ (-(1 / 2) : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)).mp hcomp
  have hp1 : Integrable (fun t : ℝ => (Real.sqrt t)⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MeasureTheory.Integrable.mono' h1
      ((by measurability : Measurable (fun t : ℝ => (Real.sqrt t)⁻¹)).aestronglyMeasurable) ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg t)), hsqrt_eq t (le_of_lt ht.1)]
  have hp2 : Integrable (fun t : ℝ => (Real.sqrt (1 - t))⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MeasureTheory.Integrable.mono' h2
      ((by measurability : Measurable (fun t : ℝ => (Real.sqrt (1 - t))⁻¹)).aestronglyMeasurable) ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg (1 - t))),
      hsqrt_eq (1 - t) (by linarith [ht.2])]
  have hw_int : Integrable (fun t : ℝ => (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hp1.add hp2
  have hw4 : (∫ t in (0 : ℝ)..1, ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)) = 4 := by
    have hint1 : IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) (f := fun t : ℝ => (Real.sqrt t)⁻¹)
        (by norm_num : (0 : ℝ) ≤ 1)).mpr hp1
    have hint2 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 - t))⁻¹) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (f := fun t : ℝ => (Real.sqrt (1 - t))⁻¹) (by norm_num : (0 : ℝ) ≤ 1)).mpr hp2
    have hval : ∀ y : ℝ, 2 * (1 / (2 * Real.sqrt y)) = (Real.sqrt y)⁻¹ := by
      intro y
      by_cases hs : Real.sqrt y = 0
      · rw [hs]
        simp
      · field_simp
    have hfirst : (∫ t in (0 : ℝ)..1, (Real.sqrt t)⁻¹) = 2 := by
      have hcont : ContinuousOn (fun y : ℝ => 2 * Real.sqrt y) (Set.Icc (0 : ℝ) 1) := by fun_prop
      have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun y : ℝ => 2 * Real.sqrt y) ((Real.sqrt x)⁻¹) x := by
        intro x hx
        have hd := (Real.hasDerivAt_sqrt (ne_of_gt hx.1)).const_mul 2
        simpa only [hval x] using hd
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
        (by norm_num : (0 : ℝ) ≤ 1) hcont hderiv hint1
      simpa using h
    have hsecond : (∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t))⁻¹) = 2 := by
      have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
        (fun y : ℝ => (Real.sqrt y)⁻¹) 1
      rw [h]
      simpa using hfirst
    rw [intervalIntegral.integral_add hint1 hint2, hfirst, hsecond]
    norm_num
  have hKw_int : Integrable (fun t : ℝ => K * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hw_int.const_mul K
  have hKw4 : (∫ t, K * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) = 4 * K := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), intervalIntegral.integral_const_mul, hw4]
    ring
  have hF1 : Integrable (fun z : ℝ × α => |f z.1 z.2|) ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P) := by
    refine (MeasureTheory.integrable_prod_iff ?_).mpr ⟨?_, ?_⟩
    · exact hf.abs.aestronglyMeasurable
    · filter_upwards [hae] with t ht
      have h := (hK t ht).1.abs
      simpa only [Real.norm_eq_abs] using h
    · have hdom : Integrable (fun t : ℝ => ∫ x, |f t x| ∂P) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        refine MeasureTheory.Integrable.mono' hKw_int ?_ ?_
        · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
            (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (ν := P)
            (f := fun z : ℝ × α => |f z.1 z.2|) hf.abs.aestronglyMeasurable
        · filter_upwards [hae] with t ht
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => abs_nonneg (f t x))]
          exact (hK t ht).2
      simpa only [Real.norm_eq_abs, abs_abs] using hdom
  have hB_int : Integrable (fun x : α => ∫ t, |f t x| ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) P :=
    hF1.integral_prod_right
  have hB_int' : Integrable (fun x : α => ∫ t in (0 : ℝ)..1, |f t x|) P := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hB_int
  have hI_aesm : AEStronglyMeasurable (fun x : α => ∫ t in (0 : ℝ)..1, f t x) P := by
    have h := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := P) (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun z : α × ℝ => f z.2 z.1)
      ((hf.comp measurable_swap).aestronglyMeasurable)
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h
  have hI : Integrable (fun x : α => ∫ t in (0 : ℝ)..1, f t x) P := by
    refine hB_int'.mono' hI_aesm ?_
    filter_upwards with x
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => f t x)
      (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [Real.norm_eq_abs] using h
  refine ⟨hI, ?_⟩
  have hswap : (∫ x : α, (∫ t, |f t x| ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ∂P)
      = ∫ t, (∫ x : α, |f t x| ∂P) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (ν := P)
      (f := fun t x => |f t x|) hF1).symm
  have hbnd : (∫ t, (∫ x : α, |f t x| ∂P) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ 4 * K := by
    have hle : (fun t : ℝ => ∫ x, |f t x| ∂P) ≤ᶠ[ae (volume.restrict (Set.Ioc (0 : ℝ) 1))]
        (fun t => K * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)) := by
      filter_upwards [hae] with t ht
      exact (hK t ht).2
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun t : ℝ => ∫ x, |f t x| ∂P)
      (g := fun t : ℝ => K * ((Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹))
      (Filter.Eventually.of_forall fun t => integral_nonneg fun x => abs_nonneg (f t x)) hKw_int hle
    rwa [hKw4] at h
  have hmono : (∫ x : α, |∫ t in (0 : ℝ)..1, f t x| ∂P) ≤
      ∫ x : α, (∫ t in (0 : ℝ)..1, |f t x|) ∂P := by
    refine MeasureTheory.integral_mono_of_nonneg
      (f := fun x : α => |∫ t in (0 : ℝ)..1, f t x|)
      (g := fun x : α => ∫ t in (0 : ℝ)..1, |f t x|) ?_ hB_int' ?_
    · filter_upwards with x using abs_nonneg (∫ t in (0 : ℝ)..1, f t x)
    · filter_upwards with x
      have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => f t x)
        (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [Real.norm_eq_abs] using h
  calc (∫ x : α, |∫ t in (0 : ℝ)..1, f t x| ∂P)
      ≤ ∫ x : α, (∫ t in (0 : ℝ)..1, |f t x|) ∂P := hmono
    _ = ∫ x : α, (∫ t, |f t x| ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ∂P := by
        simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = ∫ t, (∫ x : α, |f t x| ∂P) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := hswap
    _ ≤ 4 * K := hbnd
  /- @proof-region region.target-node.session.2f3f1ce6913dbd40 end -/

end

end Statlib.Imported

