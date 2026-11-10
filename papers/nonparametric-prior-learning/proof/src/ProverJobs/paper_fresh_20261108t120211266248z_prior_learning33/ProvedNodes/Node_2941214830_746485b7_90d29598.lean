import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_2941214830_746485b7 : ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (G : Ω → ℝ) (C : ℝ)
    (hX : ∀ n : ℕ, MemLp (X n) 2 μ)
    (hG : MemLp G 2 μ)
    (hconv : Filter.Tendsto (fun n : ℕ => eLpNorm (fun ω => X n ω - G ω) 2 μ)
      Filter.atTop (𝓝 0))
    (hlaw : Filter.Tendsto (fun n : ℕ => ∫ ω, (X n ω) ^ 2 ∂μ) Filter.atTop (𝓝 C)),
    ∫ ω, (G ω) ^ 2 ∂μ = C := by
  /- @proof-region region.target-node.session.14ce3a29002ceabf begin -/
  intro Ω _ μ _ X G C hX hG hconv hlaw
  have hIntXn : ∀ n, Integrable (fun ω => (X n ω) ^ 2) μ := fun n => (hX n).integrable_sq
  have hIntG : Integrable (fun ω => (G ω) ^ 2) μ := hG.integrable_sq
  have hIntD : ∀ n, Integrable (fun ω => (X n ω - G ω) ^ 2) μ :=
    fun n => ((hX n).sub hG).integrable_sq
  have hDnn : ∀ n, 0 ≤ ∫ ω, (X n ω - G ω) ^ 2 ∂μ :=
    fun n => integral_nonneg (fun ω => sq_nonneg (X n ω - G ω))
  have hform : ∀ (f : Ω → ℝ), MemLp f 2 μ →
      eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ)) := by
    intro f hf
    rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
    have htoReal : ENNReal.toReal (2 : ENNReal) = 2 := by norm_num
    have hbase : (∫ ω, ‖f ω‖ ^ ENNReal.toReal (2 : ENNReal) ∂μ) = ∫ ω, (f ω) ^ 2 ∂μ := by
      rw [htoReal]
      simp
    rw [hbase, Real.sqrt_eq_rpow, htoReal]
    norm_num
  have hb : Tendsto (fun n => ∫ ω, (X n ω - G ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hfun : (fun n => eLpNorm (fun ω => X n ω - G ω) 2 μ)
        = fun n => ENNReal.ofReal (Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ)) := by
      funext n
      exact hform (fun ω => X n ω - G ω) ((hX n).sub hG)
    have h2 : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ)))
        atTop (𝓝 0) := by
      rw [← hfun]
      exact hconv
    have h3 : Tendsto (fun n => Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
      have hcomp := (ENNReal.tendsto_toReal (show (0 : ENNReal) ≠ ⊤ from by simp)).comp h2
      have hEq : (ENNReal.toReal ∘ fun n => ENNReal.ofReal (Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ)))
          = fun n => Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ) := by
        funext n
        exact ENNReal.toReal_ofReal (Real.sqrt_nonneg (∫ ω, (X n ω - G ω) ^ 2 ∂μ))
      rw [hEq] at hcomp
      have hz : (0 : ENNReal).toReal = 0 := by simp
      rwa [hz] at hcomp
    have h4 : (fun n => ∫ ω, (X n ω - G ω) ^ 2 ∂μ)
        = fun n => Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ)
            * Real.sqrt (∫ ω, (X n ω - G ω) ^ 2 ∂μ) := by
      funext n
      exact (Real.sq_sqrt (hDnn n)).symm.trans (by rw [pow_two])
    rw [h4]
    simpa using h3.mul h3
  have hbound1 : ∀ (s : ℝ), 0 < s → ∀ n,
      s * (∫ ω, (G ω) ^ 2 ∂μ) ≤ s * ((1 + s) * (∫ ω, (X n ω) ^ 2 ∂μ))
        + (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ) := by
    intro s hs n
    have hpt : ∀ ω, s * (G ω) ^ 2
        ≤ s * ((1 + s) * (X n ω) ^ 2) + (s + 1) * (X n ω - G ω) ^ 2 := by
      intro ω
      nlinarith [sq_nonneg (s * X n ω + (X n ω - G ω))]
    have hIntL : Integrable (fun ω => s * (G ω) ^ 2) μ := hIntG.const_mul s
    have hIntR : Integrable (fun ω => s * ((1 + s) * (X n ω) ^ 2)
        + (s + 1) * (X n ω - G ω) ^ 2) μ :=
      (((hIntXn n).const_mul (1 + s)).const_mul s).add ((hIntD n).const_mul (s + 1))
    have e1 : (∫ ω, s * ((1 + s) * (X n ω) ^ 2) ∂μ)
        = s * ∫ ω, (1 + s) * (X n ω) ^ 2 ∂μ :=
      integral_const_mul s (fun ω => (1 + s) * (X n ω) ^ 2)
    have e2 : (∫ ω, (1 + s) * (X n ω) ^ 2 ∂μ)
        = (1 + s) * ∫ ω, (X n ω) ^ 2 ∂μ :=
      integral_const_mul (1 + s) (fun ω => (X n ω) ^ 2)
    have e3 : (∫ ω, (s + 1) * (X n ω - G ω) ^ 2 ∂μ)
        = (s + 1) * ∫ ω, (X n ω - G ω) ^ 2 ∂μ :=
      integral_const_mul (s + 1) (fun ω => (X n ω - G ω) ^ 2)
    calc s * (∫ ω, (G ω) ^ 2 ∂μ)
        = ∫ ω, s * (G ω) ^ 2 ∂μ := by rw [integral_const_mul]
      _ ≤ ∫ ω, (s * ((1 + s) * (X n ω) ^ 2) + (s + 1) * (X n ω - G ω) ^ 2) ∂μ :=
          integral_mono hIntL hIntR hpt
      _ = s * ((1 + s) * (∫ ω, (X n ω) ^ 2 ∂μ))
            + (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ) := by
          rw [integral_add (((hIntXn n).const_mul (1 + s)).const_mul s)
              ((hIntD n).const_mul (s + 1)), e1, e2, e3]
  have hbound2 : ∀ (s : ℝ), 0 < s → ∀ n,
      s * (∫ ω, (X n ω) ^ 2 ∂μ) ≤ s * ((1 + s) * (∫ ω, (G ω) ^ 2 ∂μ))
        + (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ) := by
    intro s hs n
    have hpt : ∀ ω, s * (X n ω) ^ 2
        ≤ s * ((1 + s) * (G ω) ^ 2) + (s + 1) * (X n ω - G ω) ^ 2 := by
      intro ω
      nlinarith [sq_nonneg (s * G ω - (X n ω - G ω))]
    have hIntL : Integrable (fun ω => s * (X n ω) ^ 2) μ := (hIntXn n).const_mul s
    have hIntR : Integrable (fun ω => s * ((1 + s) * (G ω) ^ 2)
        + (s + 1) * (X n ω - G ω) ^ 2) μ :=
      ((hIntG.const_mul (1 + s)).const_mul s).add ((hIntD n).const_mul (s + 1))
    have e1 : (∫ ω, s * ((1 + s) * (G ω) ^ 2) ∂μ)
        = s * ∫ ω, (1 + s) * (G ω) ^ 2 ∂μ :=
      integral_const_mul s (fun ω => (1 + s) * (G ω) ^ 2)
    have e2 : (∫ ω, (1 + s) * (G ω) ^ 2 ∂μ)
        = (1 + s) * ∫ ω, (G ω) ^ 2 ∂μ :=
      integral_const_mul (1 + s) (fun ω => (G ω) ^ 2)
    have e3 : (∫ ω, (s + 1) * (X n ω - G ω) ^ 2 ∂μ)
        = (s + 1) * ∫ ω, (X n ω - G ω) ^ 2 ∂μ :=
      integral_const_mul (s + 1) (fun ω => (X n ω - G ω) ^ 2)
    calc s * (∫ ω, (X n ω) ^ 2 ∂μ)
        = ∫ ω, s * (X n ω) ^ 2 ∂μ := by rw [integral_const_mul]
      _ ≤ ∫ ω, (s * ((1 + s) * (G ω) ^ 2) + (s + 1) * (X n ω - G ω) ^ 2) ∂μ :=
          integral_mono hIntL hIntR hpt
      _ = s * ((1 + s) * (∫ ω, (G ω) ^ 2 ∂μ))
            + (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ) := by
          rw [integral_add ((hIntG.const_mul (1 + s)).const_mul s)
              ((hIntD n).const_mul (s + 1)), e1, e2, e3]
  have stepA : ∀ s : ℝ, 0 < s → (∫ ω, (G ω) ^ 2 ∂μ) ≤ (1 + s) * C := by
    intro s hs
    have hg : Tendsto (fun n => s * ((1 + s) * (∫ ω, (X n ω) ^ 2 ∂μ))
        + (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ)) atTop (𝓝 (s * ((1 + s) * C))) := by
      have ha : Tendsto (fun n => s * ((1 + s) * (∫ ω, (X n ω) ^ 2 ∂μ))) atTop
          (𝓝 (s * ((1 + s) * C))) := (hlaw.const_mul (1 + s)).const_mul s
      have hb' : Tendsto (fun n => (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
        simpa using hb.const_mul (s + 1)
      simpa using ha.add hb'
    have h := le_of_tendsto_of_tendsto tendsto_const_nhds hg
      (Filter.Eventually.of_forall (fun n => hbound1 s hs n))
    by_contra hc
    push_neg at hc
    nlinarith [h, mul_pos hs (sub_pos.mpr hc)]
  have stepB : ∀ s : ℝ, 0 < s → C ≤ (1 + s) * (∫ ω, (G ω) ^ 2 ∂μ) := by
    intro s hs
    have hf : Tendsto (fun n => s * (∫ ω, (X n ω) ^ 2 ∂μ)) atTop (𝓝 (s * C)) :=
      hlaw.const_mul s
    have hg : Tendsto (fun n => s * ((1 + s) * (∫ ω, (G ω) ^ 2 ∂μ))
        + (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ)) atTop
        (𝓝 (s * ((1 + s) * (∫ ω, (G ω) ^ 2 ∂μ)))) := by
      have ha : Tendsto (fun _ : ℕ => s * ((1 + s) * (∫ ω, (G ω) ^ 2 ∂μ))) atTop
          (𝓝 (s * ((1 + s) * (∫ ω, (G ω) ^ 2 ∂μ)))) := tendsto_const_nhds
      have hb' : Tendsto (fun n => (s + 1) * (∫ ω, (X n ω - G ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
        simpa using hb.const_mul (s + 1)
      simpa using ha.add hb'
    have h := le_of_tendsto_of_tendsto hf hg
      (Filter.Eventually.of_forall (fun n => hbound2 s hs n))
    by_contra hc
    push_neg at hc
    nlinarith [h, mul_pos hs (sub_pos.mpr hc)]
  have hAC : (∫ ω, (G ω) ^ 2 ∂μ) ≤ C := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    by_cases hC : C ≤ 0
    · have h1 : (∫ ω, (G ω) ^ 2 ∂μ) ≤ (1 + 1) * C := stepA 1 one_pos
      nlinarith
    · push_neg at hC
      have hCne : C ≠ 0 := ne_of_gt hC
      have hCc : (ε / (2 * C)) * C = ε / 2 := by
        field_simp
      have h1 : (∫ ω, (G ω) ^ 2 ∂μ) ≤ (1 + ε / (2 * C)) * C := stepA _ (by positivity)
      nlinarith [h1, hCc, hε]
  have hCA : C ≤ (∫ ω, (G ω) ^ 2 ∂μ) := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    by_cases hA : (∫ ω, (G ω) ^ 2 ∂μ) ≤ 0
    · have h1 : C ≤ (1 + 1) * (∫ ω, (G ω) ^ 2 ∂μ) := stepB 1 one_pos
      nlinarith
    · push_neg at hA
      have hAne : (∫ ω, (G ω) ^ 2 ∂μ) ≠ 0 := ne_of_gt hA
      have hCc : (ε / (2 * (∫ ω, (G ω) ^ 2 ∂μ))) * (∫ ω, (G ω) ^ 2 ∂μ) = ε / 2 := by
        field_simp
      have h1 : C ≤ (1 + ε / (2 * (∫ ω, (G ω) ^ 2 ∂μ))) * (∫ ω, (G ω) ^ 2 ∂μ) :=
        stepB _ (by positivity)
      nlinarith [h1, hCc, hε]
  exact le_antisymm hAC hCA


  /- @proof-region region.target-node.session.14ce3a29002ceabf end -/

end Statlib.Imported
end

