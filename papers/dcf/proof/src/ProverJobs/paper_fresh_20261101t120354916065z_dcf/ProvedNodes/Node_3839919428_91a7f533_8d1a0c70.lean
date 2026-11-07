import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
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
theorem statopia_math_node_3839919428_91a7f533 : ∀ (p : ℕ) (hp : 1 ≤ p) (B : ℝ) (hB : 0 < B)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Fin p → ℝ) (Z : Fin p → Ω → ℝ) (ξ : Ω → ℝ)
    (hZ : ∀ j : Fin p, Measurable (Z j))
    (hξ : ∀ ω : Ω, ξ ω = ⨆ j : Fin p, |Z j ω - μ j|)
    (hExpInt : ∀ j : Fin p, Integrable (fun ω => Real.exp (|Z j ω - μ j| / B)) P)
    (hExpBound : ∀ j : Fin p, ∫ ω, Real.exp (|Z j ω - μ j| / B) ∂P ≤ 2),
    Measurable ξ ∧ (∀ ω : Ω, 0 ≤ ξ ω) ∧
      (∀ s : ℝ, 0 ≤ s →
        P {ω : Ω | s < ξ ω} ≤ ENNReal.ofReal (2 * (p : ℝ) * Real.exp (- s / B))) := by
  /- @proof-region region.target-node.session.1faa97656bb78e01 begin -/
  intro p hp B hB Ω _ P _ μ Z ξ hZ hξ hExpInt hExpBound
  have hp0 : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one hp
  refine ⟨?_, ?_, ?_⟩
  · have h : Measurable (fun ω : Ω => ⨆ j : Fin p, |Z j ω - μ j|) :=
      Measurable.iSup (fun j => ((hZ j).sub measurable_const).abs)
    rw [show ξ = (fun ω : Ω => ⨆ j : Fin p, |Z j ω - μ j|) from funext hξ]
    exact h
  · intro ω
    rw [hξ ω]
    exact Real.iSup_nonneg (fun j => abs_nonneg (Z j ω - μ j))
  · intro s _
    have hsub : {ω : Ω | s < ξ ω} ⊆ ⋃ j : Fin p, {ω : Ω | s < |Z j ω - μ j|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      rw [hξ ω] at hω
      rw [Set.mem_iUnion]
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_exists, not_lt] at hcon
      have hle : (⨆ j : Fin p, |Z j ω - μ j|) ≤ s :=
        csSup_le ⟨_, Set.mem_range_self (⟨0, hp0⟩ : Fin p)⟩
          (by rintro _ ⟨j, rfl⟩; exact hcon j)
      exact absurd hω (not_lt.mpr hle)
    have hterm : ∀ j : Fin p,
        P {ω : Ω | s < |Z j ω - μ j|} ≤ ENNReal.ofReal (2 * Real.exp (-s / B)) := by
      intro j
      have hfnonneg : ∀ᵐ ω ∂P, 0 ≤ Real.exp (|Z j ω - μ j| / B) :=
        Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
      have hstep : {ω : Ω | s < |Z j ω - μ j|} ⊆
          {ω : Ω | Real.exp (s / B) ≤ Real.exp (|Z j ω - μ j| / B)} := by
        intro ω hω
        exact le_of_lt (Real.exp_lt_exp.mpr (div_lt_div_of_pos_right hω hB))
      have e2 : P {ω : Ω | Real.exp (s / B) ≤ Real.exp (|Z j ω - μ j| / B)} ≤
          ENNReal.ofReal ((∫ ω, Real.exp (|Z j ω - μ j| / B) ∂P) / Real.exp (s / B)) :=
        Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.meas_ge_le_ofReal_integral_div P
          (fun ω => Real.exp (|Z j ω - μ j| / B)) hfnonneg (hExpInt j) (Real.exp (s / B))
          (Real.exp_pos _)
      have e3 : (∫ ω, Real.exp (|Z j ω - μ j| / B) ∂P) / Real.exp (s / B) ≤
          2 * Real.exp (-s / B) := by
        have h4 : 2 / Real.exp (s / B) = 2 * Real.exp (-s / B) := by
          rw [div_eq_mul_inv, ← Real.exp_neg, neg_div]
        have h : (∫ ω, Real.exp (|Z j ω - μ j| / B) ∂P) / Real.exp (s / B) ≤
            2 / Real.exp (s / B) := by
          simp only [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hExpBound j) (inv_nonneg.mpr (Real.exp_pos _).le)
        rwa [h4] at h
      calc P {ω : Ω | s < |Z j ω - μ j|}
          ≤ P {ω : Ω | Real.exp (s / B) ≤ Real.exp (|Z j ω - μ j| / B)} := measure_mono hstep
        _ ≤ ENNReal.ofReal ((∫ ω, Real.exp (|Z j ω - μ j| / B) ∂P) / Real.exp (s / B)) := e2
        _ ≤ ENNReal.ofReal (2 * Real.exp (-s / B)) := ENNReal.ofReal_le_ofReal e3
    have hsum : (∑ j : Fin p, ENNReal.ofReal (2 * Real.exp (-s / B))) =
        ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-s / B)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hc : (p : ENNReal) = ENNReal.ofReal (p : ℝ) := by simp
      have hmul : ENNReal.ofReal ((p : ℝ) * (2 * Real.exp (-s / B))) =
          ENNReal.ofReal (p : ℝ) * ENNReal.ofReal (2 * Real.exp (-s / B)) :=
        ENNReal.ofReal_mul (Nat.cast_nonneg p)
      rw [hc, ← hmul]
      congr 1
      ring
    calc P {ω : Ω | s < ξ ω}
        ≤ P (⋃ j : Fin p, {ω : Ω | s < |Z j ω - μ j|}) := measure_mono hsub
      _ ≤ ∑ j : Fin p, P {ω : Ω | s < |Z j ω - μ j|} := measure_iUnion_fintype_le P _
      _ ≤ ∑ j : Fin p, ENNReal.ofReal (2 * Real.exp (-s / B)) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-s / B)) := hsum
  /- @proof-region region.target-node.session.1faa97656bb78e01 end -/

end Statlib.Imported

