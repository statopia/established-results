import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4168644478_42c29445 : ∀ (ΩS : Type*) [MeasurableSpace ΩS] (Ω : Type*) [MeasurableSpace Ω]
    (mu : Measure ΩS) [IsProbabilityMeasure mu] (PX : Measure Ω) [IsProbabilityMeasure PX]
    (X : ΩS → Ω) (hX : Measurable X) (hX_law : MeasureTheory.Measure.map X mu = PX)
    (ζ : ΩS → Ω → ℝ) (f0 fcirc : Ω → ℝ)
    (hζ : AEMeasurable (fun ω => ζ ω (X ω)) mu) (hf0 : Measurable f0)
    (hf0_eq_fcirc : ∀ᵐ x ∂PX, f0 x = fcirc x)
    (B2 : ℝ) (hB2 : 0 < B2)
    (hExp : ∫⁻ ω, ENNReal.ofReal (Real.exp (|ζ ω (X ω) - fcirc (X ω)| / B2)) ∂mu ≤ 1),
    MeasureTheory.Integrable (fun ω => Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) mu ∧
      (∫ ω, Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2| ∂mu) ≤ 1 := by
  /- @proof-region region.target-node.session.a7b1535cd51cfd8b begin -/
  intro ΩS _ Ω _ mu _ PX _ X hX hX_law ζ f0 fcirc hζ hf0 hf0_eq_fcirc B2 hB2 hExp
  have h_ae : ∀ᵐ ω ∂mu, f0 (X ω) = fcirc (X ω) := by
    have hmap : ∀ᵐ x ∂Measure.map X mu, f0 x = fcirc x := by
      rw [hX_law]
      exact hf0_eq_fcirc
    exact MeasureTheory.ae_of_ae_map hX.aemeasurable hmap
  have hg_ae : (fun ω => Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) =ᵐ[mu]
      (fun ω => Real.exp (|ζ ω (X ω) - fcirc (X ω)| / B2)) := by
    filter_upwards [h_ae] with ω hω
    rw [hω, abs_div, abs_of_pos hB2]
  have hf0X : AEMeasurable (fun ω => f0 (X ω)) mu := (hf0.comp hX).aemeasurable
  have hsub : AEMeasurable (fun ω => ζ ω (X ω) - f0 (X ω)) mu := hζ.sub hf0X
  have hg0_aestrong :
      AEStronglyMeasurable (fun ω => Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) mu := by
    have hφ : Measurable (fun t : ℝ => Real.exp |t / B2|) :=
      Real.measurable_exp.comp ((measurable_id.div_const B2).abs)
    exact (hφ.comp_aemeasurable hsub).aestronglyMeasurable
  have hg0_nonneg : 0 ≤ᵐ[mu] (fun ω => Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hlin_eq : ∫⁻ ω, ENNReal.ofReal (Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) ∂mu
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (|ζ ω (X ω) - fcirc (X ω)| / B2)) ∂mu := by
    refine lintegral_congr_ae ?_
    filter_upwards [h_ae] with ω hω
    simp only [hω, abs_div, abs_of_pos hB2]

  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) ∂mu ≤ 1 := by
    rw [hlin_eq]
    exact hExp
  have hlt : ∫⁻ ω, ENNReal.ofReal (Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) ∂mu < ⊤ :=
    lt_of_le_of_lt hfin ENNReal.one_lt_top
  have hint : Integrable (fun ω => Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) mu :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hg0_aestrong hg0_nonneg).mp
      (ne_of_lt hlt)
  refine ⟨hint, ?_⟩
  rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
    hg0_nonneg hint]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp |(ζ ω (X ω) - f0 (X ω)) / B2|) ∂mu).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hfin
    _ = 1 := ENNReal.toReal_one

  /- @proof-region region.target-node.session.a7b1535cd51cfd8b end -/

end Statlib.Imported
end

