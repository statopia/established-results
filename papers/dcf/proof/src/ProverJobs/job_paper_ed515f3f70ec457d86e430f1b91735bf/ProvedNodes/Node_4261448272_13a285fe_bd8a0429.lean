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
theorem statopia_math_node_4261448272_13a285fe : MeasureTheory.Integrable
      (fun t : ℝ => (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)
      ((MeasureTheory.volume).restrict (Set.uIoc (0 : ℝ) 1)) := by
  /- @proof-region region.target-node.session.ca76fbedc0786d8f begin -/
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hae_pos : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (0 : ℝ) < t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    exact ht.1
  have h1 : Integrable (fun t : ℝ => (Real.sqrt t)⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1/2) : ℝ)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1/2)) (by norm_num)
    have hInt : Integrable (fun x : ℝ => x ^ (-(1/2) : ℝ))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (f := fun x : ℝ => x ^ (-(1/2) : ℝ)) h01).1 hbase
    refine hInt.congr ?_
    filter_upwards [hae_pos] with t ht
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_neg (le_of_lt ht) (1/2)
  have h2 : Integrable (fun t : ℝ => (Real.sqrt (1 - t))⁻¹)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have p1 : Measure.map (fun x : ℝ => 1 + x) volume = volume :=
      MeasureTheory.map_add_left_eq_self (volume : Measure ℝ) 1
    have p2 : Measure.map (fun t : ℝ => -t) volume = volume :=
      MeasureTheory.Measure.map_neg_eq_self (volume : Measure ℝ)
    have hME : MeasurableEmbedding (fun t : ℝ => 1 - t) :=
      (measurableEmbedding_addLeft (1 : ℝ)).comp measurableEmbedding_neg
    have hMP : MeasurePreserving (fun t : ℝ => 1 - t) volume volume := by
      have hm1 : Measurable (fun x : ℝ => 1 + x) := measurable_const.add measurable_id
      have hm2 : Measurable (fun t : ℝ => -t) := measurable_neg
      have hm : Measurable (fun t : ℝ => 1 - t) := measurable_const.sub measurable_id
      refine ⟨hm, ?_⟩
      have key : Measure.map ((fun x : ℝ => 1 + x) ∘ (fun t : ℝ => -t)) volume = volume := by
        rw [← MeasureTheory.Measure.map_map hm1 hm2, p2, p1]
      exact key
    have hpre : ((fun t : ℝ => 1 - t) ⁻¹' Set.Ioc (0 : ℝ) 1) = Set.Ico (0 : ℝ) 1 := by
      ext t
      constructor
      · intro ht
        simp only [Set.mem_preimage, Set.mem_Ioc] at ht
        simp only [Set.mem_Ico]
        constructor <;> linarith [ht.1, ht.2]
      · intro ht
        simp only [Set.mem_Ico] at ht
        simp only [Set.mem_preimage, Set.mem_Ioc]
        constructor <;> linarith [ht.1, ht.2]
    have hstep : Integrable ((fun s : ℝ => (Real.sqrt s)⁻¹) ∘ (fun t : ℝ => 1 - t))
        (volume.restrict ((fun t : ℝ => 1 - t) ⁻¹' (Set.Ioc (0 : ℝ) 1))) :=
      (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
        (f := fun s : ℝ => (Real.sqrt s)⁻¹) (s := Set.Ioc (0 : ℝ) 1) hMP hME).mpr h1
    have hvol : volume.restrict (Set.Ico (0 : ℝ) 1) = volume.restrict (Set.Ioc (0 : ℝ) 1) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc
    rw [hpre, hvol] at hstep
    simpa [Function.comp] using hstep
  have hW : Integrable (fun t : ℝ => (Real.sqrt t)⁻¹ + (Real.sqrt (1 - t))⁻¹)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := h1.add h2
  rw [Set.uIoc_of_le h01]
  exact hW
  /- @proof-region region.target-node.session.ca76fbedc0786d8f end -/

end

end Statlib.Imported

