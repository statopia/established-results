import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Statlib.StatFoundation.RandomVariable.Gaussian.Stein
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ProvedNodes.Node_114943470_1080d526_d4ef43cb
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ProvedNodes.Node_1857258558_235502cf_4f879d2f

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
theorem statopia_math_node_1953254498_13530db2 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c)
    (ξ : Ω → ℝ) (hξ_meas : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω)
    (htail : ∀ s : ℝ, 0 ≤ s →
      (P {ω : Ω | ξ ω > s}).toReal ≤ A * Real.exp (-(s ^ 2) / (2 * c))),
    Integrable (fun ω => (ξ ω) ^ 3) P ∧
      ∀ t : ℝ, 0 ≤ t →
        ∫ ω, (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0) ∂P
          ≤ 10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c)) := by
  /- @proof-region region.target-node.session.45d31edfe2c72913 begin -/
  intro Ω _instΩ P _instP A c hA hc ξ hξ_meas hξ_nonneg htail
  have hξ3_nonneg : 0 ≤ᶠ[ae P] (fun ω => (ξ ω) ^ 3) :=
    Filter.Eventually.of_forall fun ω => pow_nonneg (hξ_nonneg ω) 3
  have hξ3_meas : Measurable fun ω : Ω => (ξ ω) ^ 3 := by
    have h := hξ_meas.mul (hξ_meas.mul hξ_meas)
    simpa [pow_succ, pow_two, mul_assoc] using h
  have hmeas_gt : ∀ s : ℝ, MeasurableSet {ω : Ω | ξ ω > s} := fun s => hξ_meas measurableSet_Ioi
  have htail_enn : ∀ s : ℝ, 0 ≤ s →
      P {ω : Ω | ξ ω > s} ≤ ENNReal.ofReal (A * Real.exp (-(s ^ 2) / (2 * c))) := by
    intro s hs
    have hne : P {ω : Ω | ξ ω > s} ≠ ⊤ := MeasureTheory.measure_ne_top P _
    calc P {ω : Ω | ξ ω > s}
        = ENNReal.ofReal ((P {ω : Ω | ξ ω > s}).toReal) := (ENNReal.ofReal_toReal hne).symm
      _ ≤ ENNReal.ofReal (A * Real.exp (-(s ^ 2) / (2 * c))) := ENNReal.ofReal_le_ofReal (htail s hs)
  have hmain : ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) ∂P
        ≤ ENNReal.ofReal (10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c))) := by
    intro t ht
    have hlayer := statopia_math_node_114943470_1080d526 P ξ hξ_meas hξ_nonneg t ht
    have hb := statopia_math_node_1857258558_235502cf c t hc ht
    have hbint : Integrable (fun s : ℝ => s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := hb.1
    have hbval : ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))
        ≤ (t ^ 3 / 3 + 3 * (t + Real.sqrt c) ^ 3) * Real.exp (-(t ^ 2) / (2 * c)) := hb.2
    have hnn_f0 : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))]
        (fun s : ℝ => s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) :=
      Filter.Eventually.of_forall fun s => by positivity
    have hstep1 : ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) * (P {ω : Ω | ξ ω > max s t})
        ≤ ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) *
            ENNReal.ofReal (A * Real.exp (-((max s t) ^ 2) / (2 * c))) := by
      apply MeasureTheory.lintegral_mono
      intro s
      have hmax : 0 ≤ max s t := le_trans ht (le_max_right s t)
      show ENNReal.ofReal (3 * s ^ 2) * (P {ω : Ω | ξ ω > max s t})
          ≤ ENNReal.ofReal (3 * s ^ 2) * ENNReal.ofReal (A * Real.exp (-((max s t) ^ 2) / (2 * c)))
      gcongr
      exact htail_enn (max s t) hmax
    have hstep2 : ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) *
          ENNReal.ofReal (A * Real.exp (-((max s t) ^ 2) / (2 * c)))
        = ENNReal.ofReal (3 * A) * ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (3 * A))
        (fun s : ℝ => ENNReal.ofReal (s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))))
        ENNReal.ofReal_ne_top]
      apply MeasureTheory.lintegral_congr
      intro s
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 * s ^ 2 by positivity),
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 * A by positivity)]
      congr 1
      ring
    have hstep3 : ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)))
        = ENNReal.ofReal (∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbint hnn_f0).symm
    have hstep5 : ENNReal.ofReal ((3 * A) * ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)))
        ≤ ENNReal.ofReal (10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c))) := by
      apply ENNReal.ofReal_le_ofReal
      have hcube : t ^ 3 ≤ (t + Real.sqrt c) ^ 3 := by
        have hts : t ≤ t + Real.sqrt c := le_add_of_nonneg_right (Real.sqrt_nonneg c)
        have h0 : (0 : ℝ) ≤ t + Real.sqrt c := by positivity
        have h2 : t * t ≤ (t + Real.sqrt c) * (t + Real.sqrt c) := mul_le_mul hts hts ht h0
        have h3 : t * t * t ≤ (t + Real.sqrt c) * (t + Real.sqrt c) * (t + Real.sqrt c) :=
          mul_le_mul h2 hts (by positivity) (by positivity)
        calc t ^ 3 = t * t * t := by ring
          _ ≤ (t + Real.sqrt c) * (t + Real.sqrt c) * (t + Real.sqrt c) := h3
          _ = (t + Real.sqrt c) ^ 3 := by ring
      have h1 : A * t ^ 3 + 9 * A * (t + Real.sqrt c) ^ 3 ≤ 10 * A * (t + Real.sqrt c) ^ 3 := by
        have hA' : A * t ^ 3 ≤ A * (t + Real.sqrt c) ^ 3 :=
          mul_le_mul_of_nonneg_left hcube (le_of_lt hA)
        linarith
      calc (3 * A) * ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))
          ≤ (3 * A) * ((t ^ 3 / 3 + 3 * (t + Real.sqrt c) ^ 3) * Real.exp (-(t ^ 2) / (2 * c))) :=
            mul_le_mul_of_nonneg_left hbval (by positivity)
        _ = (A * t ^ 3 + 9 * A * (t + Real.sqrt c) ^ 3) * Real.exp (-(t ^ 2) / (2 * c)) := by ring
        _ ≤ 10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    have hstep4 : ENNReal.ofReal (3 * A) *
          ENNReal.ofReal (∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c)))
        = ENNReal.ofReal ((3 * A) * ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) := by
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 * A by positivity)]
    calc ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) ∂P
        = ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) * (P {ω : Ω | ξ ω > max s t}) := hlayer
      _ ≤ ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (3 * s ^ 2) *
            ENNReal.ofReal (A * Real.exp (-((max s t) ^ 2) / (2 * c))) := hstep1
      _ = ENNReal.ofReal (3 * A) * ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) := hstep2
      _ = ENNReal.ofReal (3 * A) *
            ENNReal.ofReal (∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) := by
          rw [hstep3]
      _ = ENNReal.ofReal ((3 * A) * ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * Real.exp (-((max s t) ^ 2) / (2 * c))) := hstep4
      _ ≤ ENNReal.ofReal (10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c))) := hstep5
  have hInt : Integrable (fun ω : Ω => (ξ ω) ^ 3) P := by
    have hzerob := hmain 0 (le_refl 0)
    have hcongr : ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3) ∂P
        = ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > 0 then (1 : ℝ) else 0)) ∂P := by
      apply MeasureTheory.lintegral_congr
      intro ω
      congr 1
      by_cases h : ξ ω > 0
      · rw [if_pos h, mul_one]
      · have hz : ξ ω = 0 := le_antisymm (not_lt.mp h) (hξ_nonneg ω)
        simp [h, hz]
    have hne : ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3) ∂P ≠ ⊤ := by
      rw [hcongr]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hzerob
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hξ3_meas.aestronglyMeasurable hξ3_nonneg).mp hne
  refine ⟨hInt, ?_⟩
  intro t ht
  have h0 := hmain t ht
  have hnn : 0 ≤ᶠ[ae P] (fun ω : Ω => (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) :=
    Filter.Eventually.of_forall fun ω => by
      show (0 : ℝ) ≤ (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)
      by_cases h : ξ ω > t
      · rw [if_pos h, mul_one]
        exact pow_nonneg (hξ_nonneg ω) 3
      · rw [if_neg h, mul_zero]
  have haesm : AEStronglyMeasurable (fun ω : Ω => (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) P := by
    have hmeas : Measurable ({ω : Ω | ξ ω > t}.indicator (fun ω => (ξ ω) ^ 3)) := by
      measurability
    have heq : (fun ω : Ω => (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0))
        = {ω : Ω | ξ ω > t}.indicator (fun ω => (ξ ω) ^ 3) := by
      funext ω
      show (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)
        = {ω : Ω | ξ ω > t}.indicator (fun ω => (ξ ω) ^ 3) ω
      by_cases h : ξ ω > t
      · rw [if_pos h, mul_one, Set.indicator_of_mem (show ω ∈ {ω : Ω | ξ ω > t} from h)]
      · rw [if_neg h, mul_zero,
          Set.indicator_of_notMem (show ω ∉ {ω : Ω | ξ ω > t} from fun hc => h hc)]
    rw [heq]
    exact hmeas.aestronglyMeasurable
  have hbnd : ∀ᵐ ω ∂P, ‖(ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)‖ ≤ (ξ ω) ^ 3 := by
    filter_upwards with ω
    show ‖(ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)‖ ≤ (ξ ω) ^ 3
    by_cases h : ξ ω > t
    · exact le_of_eq (by
        rw [if_pos h, mul_one, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hξ_nonneg ω) 3)])
    · rw [if_neg h, mul_zero, norm_zero]
      exact pow_nonneg (hξ_nonneg ω) 3
  have hInt2 : Integrable (fun ω : Ω => (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) P :=
    hInt.mono' haesm hbnd
  calc ∫ ω, (ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0) ∂P
      = (∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 3 * (if ξ ω > t then (1 : ℝ) else 0)) ∂P).toReal :=
        Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hnn hInt2
    _ ≤ (ENNReal.ofReal (10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h0
    _ = 10 * A * (t + Real.sqrt c) ^ 3 * Real.exp (-(t ^ 2) / (2 * c)) :=
        ENNReal.toReal_ofReal (by positivity)
  /- @proof-region region.target-node.session.45d31edfe2c72913 end -/

end Statlib.Imported

