import Lean
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Vocabulary
import ProverJobs.job_paper_6881610d85e44b6089ed4cd810570574.Base

namespace PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.PaperProofTasks.job_paper_6881610d85e44b6089ed4cd810570574.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))

set_option autoImplicit false in
theorem statopia_math_node_1907643924_c0d46037 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {κ : Type*} [Fintype κ]
    (V D : ℝ) (hV : 0 < V) (hD : 0 ≤ D)
    (u : κ → ℝ) (hu : ∑ k, |u k| ≤ D)
    (W : κ → Ω → ℝ) (hW : ∀ k, Measurable (W k))
    (hmoment : ∀ (k : κ) (r : ℕ), 2 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|W k ω| ^ r) ∂μ
        ≤ ENNReal.ofReal ((r.factorial : ℝ) * V ^ r)),
    ∀ (r : ℕ), 2 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|∑ k, u k * W k ω| ^ r) ∂μ
        ≤ ENNReal.ofReal ((r.factorial : ℝ) * (V * D) ^ r) := by
  /- @proof-region region.target-node.session.ec25cb560ffb3f62 begin -/
  intro Ω _ μ _ κ _ V D hV hD u hu W hW hbound r hr
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hfactpos : (0 : ℝ) < (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos r
  have hr1 : (1 : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by
    have h : (1 : ℕ) ≤ r := by omega
    exact_mod_cast h
  have hp : (r : NNReal) ≠ 0 := by
    intro h0
    have h3 := congrArg (fun x : NNReal => (x : ℝ)) h0
    have h4 : (r : ℝ) = 0 := by simpa using h3
    exact hrne h4
  set C : ℝ := (r.factorial : ℝ) ^ (1 / (r : ℝ)) * V with hC
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hfactpos) _) (le_of_lt hV)
  have hroot : ((r.factorial : ℝ) ^ (1 / (r : ℝ))) ^ r = (r.factorial : ℝ) := by
    have h1 : 1 / (r : ℝ) * (r : ℝ) = 1 := by field_simp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hfactpos), h1, Real.rpow_one]
  have hkey : ∀ g : Ω → ℝ,
      (∫⁻ ω, ‖g ω‖ₑ ^ r ∂μ) = ∫⁻ ω, ENNReal.ofReal (|g ω| ^ r) ∂μ := by
    intro g
    apply lintegral_congr_ae
    filter_upwards with ω
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow (abs_nonneg (g ω))]
  have hCpow : (ENNReal.ofReal C) ^ (r : ℝ) = ENNReal.ofReal ((r.factorial : ℝ) * V ^ r) := by
    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hCnonneg, hC]
    congr 1
    rw [mul_pow, hroot]
  have hterm : ∀ k : κ, eLpNorm (W k) (r : ℝ≥0∞) μ ≤ ENNReal.ofReal C := by
    intro k
    refine (ENNReal.rpow_le_rpow_iff hrpos).mp ?_
    have hid : (eLpNorm (W k) (r : ℝ≥0∞) μ) ^ r
        = ∫⁻ ω, ENNReal.ofReal (|W k ω| ^ r) ∂μ := by
      have hidW := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (f := W k) (μ := μ)
        (p := (r : NNReal)) hp
      rw [← hkey (W k)]
      simpa using hidW
    rw [hCpow, ENNReal.rpow_natCast, hid]
    exact hbound k r hr
  have hterm2 : ∀ k : κ,
      eLpNorm (fun ω => u k * W k ω) (r : ℝ≥0∞) μ
        ≤ ENNReal.ofReal |u k| * ENNReal.ofReal C := by
    intro k
    have h1 : eLpNorm (fun ω => u k * W k ω) (r : ℝ≥0∞) μ
        = ‖u k‖ₑ * eLpNorm (W k) (r : ℝ≥0∞) μ := by
      have hs := MeasureTheory.eLpNorm_const_smul (c := u k) (f := W k) (p := (r : ℝ≥0∞)) (μ := μ)
      simpa using hs
    rw [h1, Real.enorm_eq_ofReal_abs]
    exact mul_le_mul_left' (hterm k) _
  have hsum : eLpNorm (fun ω => ∑ k, u k * W k ω) (r : ℝ≥0∞) μ
      ≤ ENNReal.ofReal (C * D) := by
    have h1 : eLpNorm (fun ω => ∑ k, u k * W k ω) (r : ℝ≥0∞) μ
        ≤ ∑ k, eLpNorm (fun ω => u k * W k ω) (r : ℝ≥0∞) μ := by
      have hmeas : ∀ k ∈ (Finset.univ : Finset κ),
          AEStronglyMeasurable (fun ω => u k * W k ω) μ :=
        fun k _ => (measurable_const.mul (hW k)).aestronglyMeasurable
      have h1' := MeasureTheory.eLpNorm_sum_le (f := fun k ω => u k * W k ω)
        (s := (Finset.univ : Finset κ)) hmeas hr1
      have hfun : (∑ k, fun ω => u k * W k ω) = (fun ω => ∑ k, u k * W k ω) := by
        funext ω
        rw [Finset.sum_apply]
      rw [hfun] at h1'
      exact h1'
    have h2 : ∑ k, eLpNorm (fun ω => u k * W k ω) (r : ℝ≥0∞) μ
        ≤ ENNReal.ofReal (C * D) := by
      have step1 : ∑ k, eLpNorm (fun ω => u k * W k ω) (r : ℝ≥0∞) μ
          ≤ ∑ k, ENNReal.ofReal |u k| * ENNReal.ofReal C :=
        Finset.sum_le_sum (fun k _ => hterm2 k)
      have step2 : ∑ k, ENNReal.ofReal |u k| * ENNReal.ofReal C
          = (∑ k, ENNReal.ofReal |u k|) * ENNReal.ofReal C := (Finset.sum_mul _ _ _).symm
      have step3 : (∑ k, ENNReal.ofReal |u k|) = ENNReal.ofReal (∑ k, |u k|) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg (u k))]
      have step4 : ENNReal.ofReal (∑ k, |u k|) ≤ ENNReal.ofReal D :=
        ENNReal.ofReal_le_ofReal hu
      have step5 : ENNReal.ofReal D * ENNReal.ofReal C = ENNReal.ofReal (C * D) := by
        rw [← ENNReal.ofReal_mul hD, mul_comm]
      calc ∑ k, eLpNorm (fun ω => u k * W k ω) (r : ℝ≥0∞) μ
          ≤ ∑ k, ENNReal.ofReal |u k| * ENNReal.ofReal C := step1
        _ = (∑ k, ENNReal.ofReal |u k|) * ENNReal.ofReal C := step2
        _ = ENNReal.ofReal (∑ k, |u k|) * ENNReal.ofReal C := by rw [step3]
        _ ≤ ENNReal.ofReal D * ENNReal.ofReal C := mul_le_mul_left step4 (ENNReal.ofReal C)
        _ = ENNReal.ofReal (C * D) := step5
    exact le_trans h1 h2
  have hmain : (eLpNorm (fun ω => ∑ k, u k * W k ω) (r : ℝ≥0∞) μ) ^ (r : ℝ)
      ≤ (ENNReal.ofReal (C * D)) ^ (r : ℝ) :=
    ENNReal.rpow_le_rpow hsum (le_of_lt hrpos)
  have hleft : (eLpNorm (fun ω => ∑ k, u k * W k ω) (r : ℝ≥0∞) μ) ^ (r : ℝ)
      = ∫⁻ ω, ENNReal.ofReal (|∑ k, u k * W k ω| ^ r) ∂μ := by
    rw [ENNReal.rpow_natCast]
    have hidS : (eLpNorm (fun ω => ∑ k, u k * W k ω) (r : ℝ≥0∞) μ) ^ r
        = ∫⁻ ω, ENNReal.ofReal (|∑ k, u k * W k ω| ^ r) ∂μ := by
      have hs := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
        (f := fun ω => ∑ k, u k * W k ω) (μ := μ) (p := (r : NNReal)) hp
      rw [← hkey (fun ω => ∑ k, u k * W k ω)]
      simpa using hs
    exact hidS
  have hright : (ENNReal.ofReal (C * D)) ^ (r : ℝ)
      = ENNReal.ofReal ((r.factorial : ℝ) * (V * D) ^ r) := by
    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (mul_nonneg hCnonneg hD)]
    congr 1
    have hCD : C * D = (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (V * D) := by
      rw [hC]; ring
    rw [hCD, mul_pow, hroot]
  rw [← hleft, ← hright]
  exact hmain
  /- @proof-region region.target-node.session.ec25cb560ffb3f62 end -/

end Statlib.Imported

