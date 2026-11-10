import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1149977467_459d085b_98158d46

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4230448783_12afbf86 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : ℕ → Ω → ℝ) (ρ : Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hAEMeas : ∀ n : ℕ, AEMeasurable (h n) μ)
    (hnonneg : ∀ n : ℕ, 0 ≤ᵐ[μ] h n)
    (hnorm : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ = 1)
    (hsqbound : ∀ n : ℕ, ∫⁻ ω, (ENNReal.ofReal (h n ω)) ^ 2 ∂μ ≤ C)
    (haeconv : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ENNReal.ofReal (h n ω)) atTop (𝓝 (ρ ω)))
    (hCtop : C ≠ ⊤),
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ) atTop (𝓝 0) ∧
      (∫⁻ ω, ρ ω ∂μ = 1) := by
  /- @proof-region region.target-node.session.45353c9779254687 begin -/
  intro Ω _ μ _ h ρ C hAEMeas hnonneg hnorm hsqbound haeconv hCtop
  classical
  have hFmeas : ∀ n : ℕ, AEMeasurable (fun ω => ENNReal.ofReal (h n ω)) μ :=
    fun n => by measurability
  have hρmeas : AEMeasurable ρ μ :=
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hFmeas n).aestronglyMeasurable)
      haeconv).aemeasurable
  have hρle : ∫⁻ ω, ρ ω ∂μ ≤ 1 := by
    have hlim : (fun ω => Filter.liminf (fun n : ℕ => ENNReal.ofReal (h n ω)) atTop) =ᵐ[μ] ρ := by
      filter_upwards [haeconv] with ω hω
      exact Filter.Tendsto.liminf_eq hω
    calc ∫⁻ ω, ρ ω ∂μ
        = ∫⁻ ω, Filter.liminf (fun n : ℕ => ENNReal.ofReal (h n ω)) atTop ∂μ :=
          (MeasureTheory.lintegral_congr_ae hlim).symm
      _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ) atTop :=
          MeasureTheory.lintegral_liminf_le' hFmeas
      _ = 1 := by simp [hnorm]
  have hρtop : ∀ᵐ ω ∂μ, ρ ω < ⊤ := by
    refine MeasureTheory.ae_lt_top' hρmeas ?_
    exact ne_of_lt (lt_of_le_of_lt hρle (by simp))
  have hmain : Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ) atTop (𝓝 0) := by
    have hchild := statopia_math_node_1149977467_459d085b (μ := μ)
      (F := fun n ω => ENNReal.ofReal (h n ω)) (ρ := ρ) (C := C) hFmeas hsqbound hCtop haeconv
    have hcongr : (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ)
        = (fun n : ℕ => ∫⁻ ω,
            ENNReal.ofReal |(ENNReal.ofReal (h n ω)).toReal - (ρ ω).toReal| ∂μ) := by
      funext n
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [hnonneg n] with ω hω
      rw [ENNReal.toReal_ofReal hω]
    rw [hcongr]
    exact hchild
  refine ⟨hmain, ?_⟩
  have hkey : ∀ x y : ℝ, 0 ≤ y → ENNReal.ofReal x - ENNReal.ofReal y ≤ ENNReal.ofReal |x - y| := by
    intro x y hy
    rw [← ENNReal.ofReal_sub x hy]
    rcases le_total 0 (x - y) with h | h
    · have h1 : ENNReal.ofReal (x - y) = ENNReal.ofReal |x - y| := by
        rw [← Real.enorm_eq_ofReal h, ← Real.enorm_eq_ofReal_abs]
      exact le_of_eq h1
    · have h1 : ENNReal.ofReal (x - y) ≤ ENNReal.ofReal (0 : ℝ) := ENNReal.ofReal_le_ofReal h
      rw [show ENNReal.ofReal (0 : ℝ) = 0 from by simp] at h1
      exact le_trans h1 (zero_le _)
  have hGmeas : AEMeasurable (fun ω => ENNReal.ofReal ((ρ ω).toReal)) μ := by measurability
  have hstep : ∀ n : ℕ, (1 : ℝ≥0∞) - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ := by
    intro n
    have hB : ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (h n ω) - ENNReal.ofReal ((ρ ω).toReal)) ∂μ :=
      MeasureTheory.lintegral_sub_le' (f := fun ω => ENNReal.ofReal ((ρ ω).toReal))
        (g := fun ω => ENNReal.ofReal (h n ω)) hGmeas
    have hA : ∫⁻ ω, (ENNReal.ofReal (h n ω) - ENNReal.ofReal ((ρ ω).toReal)) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ :=
      MeasureTheory.lintegral_mono_ae
        (Filter.Eventually.of_forall (fun ω => hkey (h n ω) ((ρ ω).toReal) ENNReal.toReal_nonneg))
    calc (1 : ℝ≥0∞) - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ := by
          rw [hnorm n]
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (h n ω) - ENNReal.ofReal ((ρ ω).toReal)) ∂μ := hB
      _ ≤ ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ := hA
  have hlow : (1 : ℝ≥0∞) ≤ ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ := by
    have hlim0 : (1 : ℝ≥0∞) - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ ≤ 0 :=
      le_of_tendsto_of_tendsto (f := fun _ => (1 : ℝ≥0∞) - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ)
        (g := fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |h n ω - (ρ ω).toReal| ∂μ)
        tendsto_const_nhds hmain (Filter.Eventually.of_forall hstep)
    have hz : (1 : ℝ≥0∞) - ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ = 0 :=
      le_antisymm hlim0 (zero_le _)
    exact tsub_eq_zero_iff_le.mp hz
  have hGle : ∫⁻ ω, ENNReal.ofReal ((ρ ω).toReal) ∂μ ≤ ∫⁻ ω, ρ ω ∂μ :=
    MeasureTheory.lintegral_mono (fun ω => ENNReal.ofReal_toReal_le)
  exact le_antisymm hρle (hlow.trans hGle)
  /- @proof-region region.target-node.session.45353c9779254687 end -/

end Statlib.Imported
end

