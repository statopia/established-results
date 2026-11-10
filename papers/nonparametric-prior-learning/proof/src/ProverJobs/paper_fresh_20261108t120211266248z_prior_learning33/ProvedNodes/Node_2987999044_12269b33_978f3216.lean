import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1921948430_865bfebf_b8fdcaca
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2860392294_355ed9db_f7089ae5

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
theorem statopia_math_node_2987999044_12269b33 : ∀ (Ω : Type*) [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω)
    (hFmono : ∀ n : ℕ, F n ≤ F (n + 1))
    (hFle : ∀ n : ℕ, F n ≤ m0)
    (h : ℕ → Ω → ℝ) (rho : Ω → ℝ≥0∞) (C : ℝ)
    (hmeas : ∀ n : ℕ, @Measurable Ω ℝ (F n) (by infer_instance) (h n))
    (hint : ∀ n : ℕ, Integrable (fun ω => (h n ω) ^ 2) μ)
    (hart : ∀ (n : ℕ) (B : Set Ω), @MeasurableSet Ω (F n) B →
      ∫ ω in B, h (n + 1) ω ∂μ = ∫ ω in B, h n ω ∂μ)
    (hnonneg : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ h n ω)
    (hmom : Tendsto (fun n : ℕ => ∫ ω, (h n ω) ^ 2 ∂μ) atTop (𝓝 C))
    (haeconv : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ENNReal.ofReal (h n ω)) atTop (𝓝 (rho ω))),
    ∫⁻ ω, (rho ω) ^ 2 ∂μ = ENNReal.ofReal C := by
  /- @proof-region region.target-node.session.3973be75deb726cc begin -/
  intro Ω _ μ _ F hFmono hFle h rho C hmeas hint hart hnonneg hmom haeconv
  classical
  have hmeasA : ∀ n : ℕ, Measurable (h n) := fun n => (hmeas n).mono (hFle n) le_rfl
  have hmemLp : ∀ n : ℕ, MemLp (h n) 2 μ := fun n =>
    (memLp_two_iff_integrable_sq (hmeasA n).aestronglyMeasurable).mpr (hint n)
  let a : ℕ → ℝ := fun n => ∫ ω, (h n ω) ^ 2 ∂μ
  have hInt : ∀ n : ℕ, Integrable (h n) μ := by
    intro n
    refine MeasureTheory.Integrable.mono' (g := fun ω => (h n ω) ^ 2 + 1)
      ((hint n).add (integrable_const (1 : ℝ))) (hmeasA n).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (h n ω), sq_nonneg (|h n ω| - 1 / 2), abs_nonneg (h n ω)]
  have hprod : ∀ m n : ℕ, Integrable (fun ω => h m ω * h n ω) μ := by
    intro m n
    refine MeasureTheory.Integrable.mono' (g := fun ω => (h m ω) ^ 2 + (h n ω) ^ 2)
      ((hint m).add (hint n)) ((hmeasA m).mul (hmeasA n)).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (h m ω), sq_abs (h n ω), sq_nonneg (|h m ω| - |h n ω|)]
  have horth : ∀ m n : ℕ, n ≤ m → (∫ ω, h m ω * h n ω ∂μ) = a n := by
    intro m n hmn
    exact statopia_math_node_2860392294_355ed9db Ω μ F hFmono hFle h hmeas hint hart m n hmn
  have hdiff : ∀ m n : ℕ, n ≤ m → (∫ ω, (h m ω - h n ω) ^ 2 ∂μ) = a m - a n := by
    intro m n hmn
    have hI : Integrable (fun ω => (h m ω) ^ 2 + (h n ω) ^ 2) μ := (hint m).add (hint n)
    have hK : Integrable (fun ω => (h m ω * h n ω) + (h m ω * h n ω)) μ :=
      (hprod m n).add (hprod m n)
    have hpt : (fun ω => (h m ω - h n ω) ^ 2)
        = fun ω => ((h m ω) ^ 2 + (h n ω) ^ 2 - ((h m ω * h n ω) + (h m ω * h n ω))) := by
      funext ω
      ring
    rw [hpt, integral_sub hI hK, integral_add (hint m) (hint n),
      integral_add (hprod m n) (hprod m n), horth m n hmn]
    ring
  have hamono : ∀ n m : ℕ, n ≤ m → a n ≤ a m := by
    intro n m hnm
    have hnn : (0 : ℝ) ≤ ∫ ω, (h m ω - h n ω) ^ 2 ∂μ := by
      apply integral_nonneg
      intro ω
      exact sq_nonneg _
    have hm := hdiff m n hnm
    linarith
  obtain ⟨g, hg_nonneg, hg_eq, hgInt, hgsq⟩ :=
    statopia_math_node_1921948430_865bfebf Ω μ h rho C hmeasA hnonneg hint
      (fun m n hmn => hdiff m n hmn) hmom haeconv
  have hcongr : ∫⁻ ω, (rho ω) ^ 2 ∂μ = ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 2) ∂μ := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hg_eq, hg_nonneg] with ω heq hnn
    rw [heq, ← ENNReal.ofReal_pow hnn 2]
  have hfin : ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 2) ∂μ = ENNReal.ofReal C := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgInt
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (g ω))), hgsq]
  rw [hcongr]
  exact hfin

  /- @proof-region region.target-node.session.3973be75deb726cc end -/

end Statlib.Imported
end

