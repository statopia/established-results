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
theorem statopia_math_node_1928020627_7c479ed8 : ∀ {ΩS Ω : Type*} [MeasurableSpace ΩS] [MeasurableSpace Ω]
    (mu : Measure ΩS) [IsProbabilityMeasure mu]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n × Fin m → ΩS → Ω) (hX : ∀ ij : Fin n × Fin m, Measurable (X ij))
    (Z : Fin n → ΩS → Ω → ℝ)
    (hZ : ∀ i : Fin n, Measurable (fun p : ΩS × Ω => Z i p.1 p.2))
    (fcirc : Ω → ℝ) (hfcirc : Measurable fcirc)
    (eps : Fin n × Fin m → ΩS → ℝ)
    (heps : ∀ ij : Fin n × Fin m, Measurable (eps ij))
    (B2 B3 : ℝ) (hB2 : 0 < B2) (hB3 : 0 < B3)
    (hU_exp : ∀ ij : Fin n × Fin m,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|stochPart Z fcirc ij.1 ω (X ij ω)| / B2)) ∂mu ≤ 1)
    (heps_exp : ∀ ij : Fin n × Fin m,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|eps ij ω| / B3)) ∂mu ≤ 1),
    ∀ᵐ ω ∂mu,
      (∀ ij : Fin n × Fin m, stochPart Z fcirc ij.1 ω (X ij ω) = 0 ∧ eps ij ω = 0) ∧
        (∀ ij : Fin n × Fin m, response Z eps X fcirc ij ω = fcirc (X ij ω)) := by
  /- @proof-region region.target-node.session.d4f8a929b915585d begin -/
  intro ΩS Ω instΩS instΩ mu instMu n m hn hm X hX Z hZ fcirc hfcirc eps heps B2 B3 hB2 hB3 hU hE
  have key : ∀ (g : ΩS → ℝ) (B : ℝ), 0 < B →
      AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (|g ω| / B))) mu →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|g ω| / B)) ∂mu ≤ 1 →
      ∀ᵐ ω ∂mu, g ω = 0 := by
    intro g B hB hmeas hint
    have hle : (fun _ : ΩS => (1 : ℝ≥0∞)) ≤ᶠ[ae mu]
        (fun ω => ENNReal.ofReal (Real.exp (|g ω| / B))) := by
      filter_upwards with ω
      have h0 : (0 : ℝ) ≤ |g ω| / B := div_nonneg (abs_nonneg (g ω)) hB.le
      have h1 : (1 : ℝ) ≤ Real.exp (|g ω| / B) := by
        simpa using Real.exp_le_exp_of_le h0
      simpa using ENNReal.ofReal_le_ofReal h1
    have htop : ∫⁻ (ω : ΩS), (1 : ℝ≥0∞) ∂mu ≠ ⊤ := by
      rw [MeasureTheory.lintegral_one, measure_univ]
      exact ENNReal.one_ne_top
    have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (|g ω| / B)) ∂mu
        ≤ ∫⁻ (ω : ΩS), (1 : ℝ≥0∞) ∂mu := by
      rw [MeasureTheory.lintegral_one, measure_univ]
      exact hint
    have heq := MeasureTheory.ae_eq_of_ae_le_of_lintegral_le hle htop hmeas hfin
    filter_upwards [heq] with ω hω
    have hge : (1 : ℝ) ≤ Real.exp (|g ω| / B) := by
      have h0 : (0 : ℝ) ≤ |g ω| / B := div_nonneg (abs_nonneg (g ω)) hB.le
      simpa using Real.exp_le_exp_of_le h0
    have hof : ENNReal.ofReal (Real.exp (|g ω| / B)) = ENNReal.ofReal (1 : ℝ) := by
      simpa [ENNReal.ofReal_one] using hω.symm
    have hle1 : Real.exp (|g ω| / B) ≤ 1 := by
      have h1 : ENNReal.ofReal (Real.exp (|g ω| / B)) ≤ ENNReal.ofReal (1 : ℝ) := le_of_eq hof
      rcases ENNReal.ofReal_le_ofReal_iff'.mp h1 with h | h
      · exact h
      · linarith [Real.exp_pos (|g ω| / B)]
    have hexp : Real.exp (|g ω| / B) = 1 := le_antisymm hle1 hge
    have hdiv : |g ω| / B = 0 := by
      have hexp0 : Real.exp (|g ω| / B) ≤ Real.exp (0 : ℝ) := by
        rw [hexp, Real.exp_zero]
      have h1 : |g ω| / B ≤ 0 := Real.exp_le_exp.mp hexp0
      have h0 : (0 : ℝ) ≤ |g ω| / B := div_nonneg (abs_nonneg (g ω)) hB.le
      linarith
    have habs : |g ω| = 0 := by
      have h2 : |g ω| / B * B = 0 := by rw [hdiv, zero_mul]
      rwa [div_mul_cancel₀ _ (ne_of_gt hB)] at h2
    exact abs_eq_zero.mp habs
  have hZm : ∀ (i : Fin n) (j : Fin m), Measurable (fun ω : ΩS => Z i ω (X (i, j) ω)) := by
    intro i j
    exact (hZ i).comp (Measurable.prodMk measurable_id (hX (i, j)))
  have hSm : ∀ (i : Fin n) (j : Fin m),
      Measurable (fun ω : ΩS => stochPart Z fcirc i ω (X (i, j) ω)) := by
    intro i j
    simpa [stochPart] using (hZm i j).sub (hfcirc.comp (hX (i, j)))
  have hmeasU : ∀ (i : Fin n) (j : Fin m),
      AEMeasurable
        (fun ω => ENNReal.ofReal (Real.exp (|stochPart Z fcirc i ω (X (i, j) ω)| / B2))) mu := by
    intro i j
    exact ((Real.measurable_exp.comp (((hSm i j).abs).div_const B2)).ennreal_ofReal).aemeasurable
  have hmeasE : ∀ (i : Fin n) (j : Fin m),
      AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (|eps (i, j) ω| / B3))) mu := by
    intro i j
    exact ((Real.measurable_exp.comp (((heps (i, j)).abs).div_const B3)).ennreal_ofReal).aemeasurable
  have hstat : ∀ᵐ ω ∂mu, ∀ ij : Fin n × Fin m, stochPart Z fcirc ij.1 ω (X ij ω) = 0 := by
    rw [Filter.eventually_all]
    rintro ⟨i, j⟩
    exact key (fun ω => stochPart Z fcirc i ω (X (i, j) ω)) B2 hB2 (hmeasU i j) (hU (i, j))
  have heps0 : ∀ᵐ ω ∂mu, ∀ ij : Fin n × Fin m, eps ij ω = 0 := by
    rw [Filter.eventually_all]
    rintro ⟨i, j⟩
    exact key (fun ω => eps (i, j) ω) B3 hB3 (hmeasE i j) (hE (i, j))
  filter_upwards [hstat, heps0] with ω hst hepz
  exact ⟨fun ij => ⟨hst ij, hepz ij⟩, fun ij => by simp [response, hst ij, hepz ij]⟩
  /- @proof-region region.target-node.session.d4f8a929b915585d end -/

end Statlib.Imported
end

