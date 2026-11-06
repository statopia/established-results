import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_334888657_5530b0ba : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hInt : Integrable f P)
    (h01 : ∀ᵐ ω ∂P, f ω = 0 ∨ f ω = 1)
    (hprob : P {ω | f ω = 1} = ENNReal.ofReal p),
    ∫ ω, (p⁻¹ * f ω - 1) ^ 2 ∂P = (1 - p) / p := by
  /- @proof-region region.target-node.session.fd2c26c6e3424ff7 begin -/
  intro Ω _ P _ f p hp hp1 hf h01 hprob
  have hfa : AEMeasurable f P := hf.aemeasurable
  set g : Ω → ℝ := hfa.mk f with hgdef
  have hgm : Measurable g := by
    rw [hgdef]
    exact hfa.measurable_mk
  have hfg : f =ᵐ[P] g := by
    rw [hgdef]
    exact hfa.ae_eq_mk
  have hAmeas : MeasurableSet {ω | g ω = 1} := hgm (measurableSet_singleton (1 : ℝ))
  have hmeasP : P {ω | g ω = 1} = ENNReal.ofReal p := by
    rw [← hprob]
    refine MeasureTheory.measure_congr ?_
    filter_upwards [hfg] with ω hω
    change (g ω = 1) = (f ω = 1)
    exact congrArg (fun x : ℝ => x = 1) hω.symm
  have hRealP : P.real {ω | g ω = 1} = p := by
    show (P {ω | g ω = 1}).toReal = p
    rw [hmeasP, ENNReal.toReal_ofReal (le_of_lt hp)]
  have hRealUniv : P.real (Set.univ : Set Ω) = 1 := by
    show (P Set.univ).toReal = 1
    rw [measure_univ]
    simp
  have hg01 : ∀ᵐ ω ∂P, g ω = 0 ∨ g ω = 1 := by
    filter_upwards [h01, hfg] with ω h1 h2
    simpa [h2] using h1
  have hgind : g =ᵐ[P] {ω | g ω = 1}.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hg01] with ω hω
    rcases hω with h0 | h1
    · simp [Set.indicator, h0]
    · simp [Set.indicator, h1]
  have hIntG : ∫ ω, g ω ∂P = p := by
    calc ∫ ω, g ω ∂P
        = ∫ ω, {ω | g ω = 1}.indicator (fun _ => (1 : ℝ)) ω ∂P :=
          MeasureTheory.integral_congr_ae hgind
      _ = P.real {ω | g ω = 1} := MeasureTheory.integral_indicator_one hAmeas
      _ = p := hRealP
  have hIntF : ∫ ω, f ω ∂P = p := by
    rw [MeasureTheory.integral_congr_ae hfg]
    exact hIntG
  have hpt : ∀ᵐ ω ∂P, (p⁻¹ * f ω - 1) ^ 2 = ((p⁻¹ - 1) ^ 2 - 1) * f ω + 1 := by
    filter_upwards [h01] with ω hω
    rcases hω with h | h
    · rw [h]; ring
    · rw [h]; ring
  have hIntCf : Integrable (fun ω => ((p⁻¹ - 1) ^ 2 - 1) * f ω) P := by
    simpa only [smul_eq_mul] using hf.const_mul (((p⁻¹ - 1) ^ 2 - 1) : ℝ)
  have hIntOne : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hIntOneVal : ∫ _ : Ω, (1 : ℝ) ∂P = 1 := by
    have h := MeasureTheory.integral_indicator_one (μ := P) (s := Set.univ) MeasurableSet.univ
    rw [hRealUniv] at h
    simpa using h
  have hIntAdd : ∫ ω, (((p⁻¹ - 1) ^ 2 - 1) * f ω + 1) ∂P
      = ((p⁻¹ - 1) ^ 2 - 1) * (∫ ω, f ω ∂P) + 1 := by
    rw [MeasureTheory.integral_add hIntCf hIntOne, MeasureTheory.integral_const_mul,
      hIntOneVal]
  have hmain : ∫ ω, (p⁻¹ * f ω - 1) ^ 2 ∂P = ((p⁻¹ - 1) ^ 2 - 1) * p + 1 := by
    rw [MeasureTheory.integral_congr_ae hpt, hIntAdd, hIntF]
  have hp0 : p ≠ 0 := ne_of_gt hp
  rw [hmain]
  field_simp
  ring
  /- @proof-region region.target-node.session.fd2c26c6e3424ff7 end -/

end

end Statlib.Imported

