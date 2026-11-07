import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261101t120354916065z_dcf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_114943470_1080d526 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω)
    (t : ℝ) (ht : 0 ≤ t),
    ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) ∂P
      = ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (3 * s ^ 2) * (P {ω : Ω | ξ ω > max s t}) ∂volume := by
  /- @proof-region region.target-node.session.5fddb94cc1544a43 begin -/
  intro Ω _ P _ ξ hξ hξ_nonneg t ht
  have hA : MeasurableSet {ω : Ω | ξ ω > t} := hξ measurableSet_Ioi
  have hInt : ∀ ω : Ω, (∫ x in (0 : ℝ)..ξ ω, 3 * x ^ 2) = (ξ ω) ^ 3 := by
    intro ω
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (ξ ω), HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      intro x _
      simpa using hasDerivAt_pow 3 x
    have hii : IntervalIntegrable (fun x : ℝ => 3 * x ^ 2) volume 0 (ξ ω) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have key : (∫ x in (0 : ℝ)..ξ ω, 3 * x ^ 2)
        = (fun y : ℝ => y ^ 3) (ξ ω) - (fun y : ℝ => y ^ 3) 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
    rw [key]
    show (ξ ω) ^ 3 - (0 : ℝ) ^ 3 = (ξ ω) ^ 3
    ring
  have hg_int : ∀ t' > 0, IntervalIntegrable (fun x : ℝ => 3 * x ^ 2) volume 0 t' := by
    intro t' _
    apply Continuous.intervalIntegrable
    fun_prop
  have hkey :
      ∫⁻ ω, ENNReal.ofReal (∫ x in (0 : ℝ)..ξ ω, 3 * x ^ 2) ∂(P.restrict {ω : Ω | ξ ω > t})
        = ∫⁻ s in Set.Ioi (0 : ℝ),
            (P.restrict {ω : Ω | ξ ω > t}) {ω : Ω | ξ ω > s} * ENNReal.ofReal (3 * s ^ 2) ∂volume :=
    MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul (P.restrict {ω : Ω | ξ ω > t})
      (Filter.Eventually.of_forall hξ_nonneg) hξ.aemeasurable hg_int
      (Filter.Eventually.of_forall (fun x => by positivity))
  have hL : ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) ∂P
      = ∫⁻ ω in {ω : Ω | ξ ω > t}, ENNReal.ofReal ((ξ ω) ^ 3) ∂P := by
    rw [← MeasureTheory.lintegral_indicator (f := fun ω => ENNReal.ofReal ((ξ ω) ^ 3)) hA]
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    by_cases hω : ξ ω > t
    · have hmem : ω ∈ {ω : Ω | ξ ω > t} := hω
      simp [hmem, hω]
    · have hmem : ω ∉ {ω : Ω | ξ ω > t} := hω
      simp [hmem, hω]
  have hR :
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) * (P {ω : Ω | ξ ω > max s t}) ∂volume
        = ∫⁻ s in Set.Ioi (0 : ℝ),
            (P.restrict {ω : Ω | ξ ω > t}) {ω : Ω | ξ ω > s} * ENNReal.ofReal (3 * s ^ 2) ∂volume := by
    refine MeasureTheory.lintegral_congr (fun s => ?_)
    have hrc : (P.restrict {ω : Ω | ξ ω > t}) {ω : Ω | ξ ω > s} = P {ω : Ω | ξ ω > max s t} := by
      rw [MeasureTheory.Measure.restrict_apply]
      · congr 1
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact max_lt h1 h2
        · intro h
          exact ⟨lt_of_le_of_lt (le_max_left s t) h, lt_of_le_of_lt (le_max_right s t) h⟩
      · measurability
    rw [hrc]
    exact mul_comm _ _
  calc ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) ∂P
      = ∫⁻ ω in {ω : Ω | ξ ω > t}, ENNReal.ofReal ((ξ ω) ^ 3) ∂P := hL
    _ = ∫⁻ ω, ENNReal.ofReal (∫ x in (0 : ℝ)..ξ ω, 3 * x ^ 2) ∂(P.restrict {ω : Ω | ξ ω > t}) := by
        refine MeasureTheory.lintegral_congr (fun ω => ?_)
        rw [← hInt ω]
    _ = ∫⁻ s in Set.Ioi (0 : ℝ),
            (P.restrict {ω : Ω | ξ ω > t}) {ω : Ω | ξ ω > s} * ENNReal.ofReal (3 * s ^ 2) ∂volume := hkey
    _ = ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) * (P {ω : Ω | ξ ω > max s t}) ∂volume := hR.symm
  /- @proof-region region.target-node.session.5fddb94cc1544a43 end -/

end Statlib.Imported

