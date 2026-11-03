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
theorem statopia_math_node_3805701343_fc432acd : ∀ (d : ℕ) (hd : 0 < d)
    (ΩS : Type*) [MeasurableSpace ΩS]
    (mu : Measure ΩS) [IsProbabilityMeasure mu]
    (Ω : Set (Fin d → ℝ)) (hΩ_meas : MeasurableSet Ω)
    (hΩ_sub : Ω ⊆ Set.Icc (0 : Fin d → ℝ) 1)
    (PX : Measure Ω) [IsProbabilityMeasure PX]
    (hPX_ac : PX ≪ Measure.comap (fun x : Ω => (x : Fin d → ℝ))
      (volume : Measure (Fin d → ℝ)))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n × Fin m → ΩS → Ω) (Z : Fin n → ΩS → Ω → ℝ)
    (eps sig : Fin n × Fin m → ΩS → ℝ)
    (F : Set (Ω → ℝ)) (fcirc : Ω → ℝ) (fhat : ΩS → Ω → ℝ)
    (B1 B2 B3 rstar : ℝ) (phi : ℝ → ℝ) (f0 : Ω → ℝ)
    (c38 c39 t : ℝ) (ht : 0 < t)
    (hX_meas : ∀ ij : Fin n × Fin m, Measurable (X ij))
    (hX_indep : iIndepFun X mu)
    (hX_ident : ∀ ij ij' : Fin n × Fin m, IdentDistrib (X ij) (X ij') mu mu)
    (hX_law : ∀ ij : Fin n × Fin m, Measure.map (X ij) mu = PX)
    (hZ_meas : ∀ i : Fin n, Measurable (fun p : ΩS × Ω => Z i p.1 p.2))
    (hZ_indep : iIndepFun Z mu)
    (hZ_ident : ∀ i i' : Fin n, IdentDistrib (Z i) (Z i') mu mu)
    (hfcirc_cond : ∀ (i : Fin n) (j : Fin m),
      ∀ᵐ ω ∂mu, fcirc (X (i, j) ω) =
        mu[fun ω => Z i ω (X (i, j) ω) |
            MeasurableSpace.comap (X (i, j)) (inferInstance : MeasurableSpace Ω)] ω)
    (hXZ_indep : IndepFun (Function.swap X) (Function.swap Z) mu)
    (hEps_meas : ∀ ij : Fin n × Fin m, Measurable (eps ij))
    (hEps_indep : iIndepFun eps mu)
    (hEps_data_indep : IndepFun (Function.swap eps)
      (fun ω : ΩS => (Function.swap X ω, Function.swap Z ω)) mu)
    (hEps_int : ∀ ij : Fin n × Fin m, Integrable (eps ij) mu)
    (hEps_mean : ∀ ij : Fin n × Fin m, ∫ ω, eps ij ω ∂mu = 0)
    (hU_int : ∀ (i : Fin n) (j : Fin m),
      Integrable (fun ω => stochPart Z fcirc i ω (X (i, j) ω) * fcirc (X (i, j) ω)) mu)
    (hU_center : ∀ (i : Fin n) (j : Fin m),
      ∫ ω, stochPart Z fcirc i ω (X (i, j) ω) * fcirc (X (i, j) ω) ∂mu = 0)
    (hU_cont : ∀ (i : Fin n) (ω : ΩS), Continuous (fun z : Ω => Z i ω z - f0 z))
    (hSig_meas : ∀ ij : Fin n × Fin m, Measurable (sig ij))
    (hSig_indep : iIndepFun sig mu)
    (hSig_val : ∀ ij : Fin n × Fin m,
      mu {ω | sig ij ω = 1} = 1 / 2 ∧ mu {ω | sig ij ω = -1} = 1 / 2)
    (hSig_data_indep : IndepFun (Function.swap sig)
      (fun ω : ΩS => (Function.swap X ω, (Function.swap Z ω, Function.swap eps ω))) mu)
    (hFhat_meas : Measurable fhat)
    (hFhat_argmin : ∀ᵐ ω ∂mu, fhat ω ∈ F ∧
      ∀ f ∈ F, empRisk X (response Z eps X fcirc) (fhat ω) ω ≤
        empRisk X (response Z eps X fcirc) f ω)
    (hfcirc_meas : Measurable fcirc)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hFhat_joint : AEMeasurable (fun p : ΩS × Ω => fhat p.1 p.2) (mu.prod PX))
    (hFhat_risk_meas : AEMeasurable (fun ω => l2Err PX fcirc (fhat ω)) mu)
    (hGood : ∀ᵐ ω ∂mu, fhat ω ∈ F)
    (hB1_pos : 0 < B1)
    (hB1_ge_one : 1 ≤ B1)
    (hfcirc_bound : ∀ x : Ω, |fcirc x| ≤ B1)
    (hF_bound : ∀ f ∈ F, ∀ x : Ω, |f x| ≤ B1)
    (hB2_pos : 0 < B2)
    (hU_exp : ∀ (i : Fin n) (j : Fin m),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|stochPart Z fcirc i ω (X (i, j) ω)| / B2)) ∂mu ≤ 1)
    (hB3_pos : 0 < B3)
    (hEps_exp : ∀ (i : Fin n) (j : Fin m),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|eps (i, j) ω| / B3)) ∂mu ≤ 1)
    (hrstar_pos : 0 < rstar)
    (hphi_nonneg : ∀ r ∈ Set.Ici rstar, 0 ≤ phi r / Real.sqrt r)
    (hphi_antitone : AntitoneOn (fun r => phi r / Real.sqrt r) (Set.Ici rstar))
    (hphi_fix : phi rstar ≤ rstar)
    (hphi_dom : ∀ r ∈ Set.Ici rstar,
      radSup mu PX F fcirc sig X r ≤ ENNReal.ofReal (phi r))
    (hZ_int : ∀ i : Fin n, ∀ᵐ x ∂PX, Integrable (fun ω => Z i ω x) mu)
    (hf0_def : ∀ i : Fin n, ∀ᵐ x ∂PX, f0 x = ∫ (ω : ΩS), Z i ω x ∂mu)
    (hf0_meas : Measurable f0)
    (hf0_bound : ∀ x : Ω, |f0 x| ≤ B1)
    (hf0_eq_fcirc : ∀ᵐ x ∂PX, f0 x = fcirc x)
    (hF_star : StarConvex ℝ f0 F)
    (hF_sep : ∃ F0 : Set (Ω → ℝ), F0.Countable ∧ F0 ⊆ F ∧
      ∀ f ∈ F, ∃ u : ℕ → (Ω → ℝ),
        (∀ k : ℕ, u k ∈ F0) ∧
          ∀ x : Ω, Filter.Tendsto (fun k : ℕ => u k x) Filter.atTop (nhds (f x)))
    (hNoRegime : ¬ (rstar ≤
      2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)))),
    (c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) < rstar / 2) ∧
      ∀ᵐ ω ∂mu,
        |(l2Err PX fcirc (fhat ω)).toReal -
            (1 / ((n : ℝ) * (m : ℝ))) *
              ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2| ≤
          (1 / 2) * (l2Err PX fcirc (fhat ω)).toReal + 4 * B1 ^ 2 := by
  /- @proof-region region.target-node.session.0e446706386c33b3 begin -/
  intro d hd ΩS imeas mu iprob Ω hΩ_meas hΩ_sub PX iprobPX hPX_ac
  intro n m hn hm X Z eps sig F fcirc fhat
  intro B1 B2 B3 rstar phi f0 c38 c39 t ht
  intro hX_meas hX_indep hX_ident hX_law hZ_meas hZ_indep hZ_ident hfcirc_cond hXZ_indep
  intro hEps_meas hEps_indep hEps_data_indep hEps_int hEps_mean hU_int hU_center hU_cont
  intro hSig_meas hSig_indep hSig_val hSig_data_indep
  intro hFhat_meas hFhat_argmin hfcirc_meas hF_meas hFhat_joint hFhat_risk_meas hGood
  intro hB1_pos hB1_ge_one hfcirc_bound hF_bound hB2_pos hU_exp hB3_pos hEps_exp
  intro hrstar_pos hphi_nonneg hphi_antitone hphi_fix hphi_dom
  intro hZ_int hf0_def hf0_meas hf0_bound hf0_eq_fcirc hF_star hF_sep
  intro hNoRegime
  constructor
  · have hlt : 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) < rstar :=
      not_le.mp hNoRegime
    have h2 : 2 * (c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ))) < rstar := by
      have heq : 2 * (c38 * B1 ^ 2 * rstar + c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)))
          = 2 * c38 * B1 ^ 2 * rstar + 2 * c39 * B1 ^ 2 * t / ((n : ℝ) * (m : ℝ)) := by ring
      rw [heq]
      exact hlt
    linarith only [h2]
  · filter_upwards [hGood] with ω hmem
    set A := (l2Err PX fcirc (fhat ω)).toReal with hAdef
    set E := (1 / ((n : ℝ) * (m : ℝ))) *
      ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2 with hEdef
    have hsq : ∀ x : Ω, (fhat ω x - fcirc x) ^ 2 ≤ 4 * B1 ^ 2 := by
      intro x
      have h3 := abs_le.mp (hF_bound (fhat ω) hmem x)
      have h4 := abs_le.mp (hfcirc_bound x)
      have hp : 0 ≤ (2 * B1 - (fhat ω x - fcirc x)) * (2 * B1 + (fhat ω x - fcirc x)) := by
        apply mul_nonneg <;> linarith [h3.1, h3.2, h4.1, h4.2]
      nlinarith [hp]
    have hA : A ≤ 4 * B1 ^ 2 := by
      rw [hAdef]
      have hlin : l2Err PX fcirc (fhat ω) ≤ ENNReal.ofReal (4 * B1 ^ 2) := by
        show (∫⁻ x, ENNReal.ofReal ((fhat ω x - fcirc x) ^ 2) ∂PX) ≤ ENNReal.ofReal (4 * B1 ^ 2)
        calc (∫⁻ x, ENNReal.ofReal ((fhat ω x - fcirc x) ^ 2) ∂PX)
            ≤ ∫⁻ _x, ENNReal.ofReal (4 * B1 ^ 2) ∂PX :=
              lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hsq x)
          _ = ENNReal.ofReal (4 * B1 ^ 2) * PX Set.univ := lintegral_const _
          _ = ENNReal.ofReal (4 * B1 ^ 2) := by rw [measure_univ, mul_one]
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    have hAn : 0 ≤ A := by
      rw [hAdef]
      exact ENNReal.toReal_nonneg
    have hDpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact mul_pos h1 h2
    have hE : E ≤ 4 * B1 ^ 2 := by
      rw [hEdef]
      have hsum : ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
          ≤ ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2) := by
        have h1 : ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
            ≤ ∑ _ij : Fin n × Fin m, (4 * B1 ^ 2) :=
          Finset.sum_le_sum fun ij _ => hsq (X ij ω)
        have h2 : (∑ _ij : Fin n × Fin m, (4 * B1 ^ 2))
            = ((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2) := by
          simp [Finset.card_univ, Fintype.card_prod]
        linarith [h1, h2]
      calc (1 / ((n : ℝ) * (m : ℝ))) *
            ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2
          ≤ (1 / ((n : ℝ) * (m : ℝ))) * (((n : ℝ) * (m : ℝ)) * (4 * B1 ^ 2)) :=
            mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hDpos))
        _ = 4 * B1 ^ 2 := by
            rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul]
    have hEn : 0 ≤ E := by
      rw [hEdef]
      have hsum : 0 ≤ ∑ ij : Fin n × Fin m, (fhat ω (X ij ω) - fcirc (X ij ω)) ^ 2 :=
        Finset.sum_nonneg fun ij _ => sq_nonneg _
      exact mul_nonneg (le_of_lt (one_div_pos.mpr hDpos)) hsum
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  /- @proof-region region.target-node.session.0e446706386c33b3 end -/

end Statlib.Imported
end

