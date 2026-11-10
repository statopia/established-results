import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3300259176_dcd675c6_198ffd58

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
theorem statopia_math_node_3147937759_08d5a7be : ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY_meas : ∀ k : ℕ, Measurable (Y k))
    (hY_indep : ProbabilityTheory.iIndepFun Y μ)
    (hY_mean : ∀ k : ℕ, (∫ ω, Y k ω ∂μ) = 0)
    (hY_memLp : ∀ k : ℕ, MeasureTheory.MemLp (Y k) 2 μ)
    (hY_summable : Summable (fun k : ℕ => ∫ ω, (Y k ω) ^ 2 ∂μ)),
    ∀ᵐ ω ∂μ, ∃ L : ℝ,
      Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Y k ω) Filter.atTop (𝓝 L) := by
  /- @proof-region region.target-node.session.a2bb3704e11ffd02 begin -/
  intro Ω _ μ _ Y hY_meas hY_indep hY_mean hY_memLp hY_summable
  have hf : ∀ k : ℕ, StronglyMeasurable (Y k) := fun k => (hY_meas k).stronglyMeasurable
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural (β := fun _ => ℝ) Y hf
  let S : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n + 1), Y k ω
  let C : ℝ := ∑' k : ℕ, ∫ ω, (Y k ω) ^ 2 ∂μ
  let R : NNReal := ⟨Real.sqrt C, Real.sqrt_nonneg C⟩
  have hMemLp : ∀ n : ℕ, MemLp (S n) 2 μ := fun n =>
    memLp_finset_sum (Finset.range (n + 1)) (fun k _ => hY_memLp k)
  have hVarY : ∀ k : ℕ, variance (Y k) μ = ∫ ω, (Y k ω) ^ 2 ∂μ := by
    intro k
    rw [variance_eq_sub (hY_memLp k), hY_mean k]
    simp
  have hMeanS : ∀ n : ℕ, ∫ ω, S n ω ∂μ = 0 := by
    intro n
    have h1 : ∫ ω, S n ω ∂μ = ∑ k ∈ Finset.range (n + 1), ∫ ω, Y k ω ∂μ :=
      integral_finset_sum (Finset.range (n + 1))
        (fun k _ => (hY_memLp k).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    rw [h1]
    simp [hY_mean]
  have hVarS : ∀ n : ℕ, variance (S n) μ = ∫ ω, (S n ω) ^ 2 ∂μ := by
    intro n
    rw [variance_eq_sub (hMemLp n), hMeanS n]
    simp
  have hVarSum : ∀ n : ℕ, variance (S n) μ = ∑ k ∈ Finset.range (n + 1), variance (Y k) μ := by
    intro n
    have h := IndepFun.variance_sum (X := Y) (s := Finset.range (n + 1))
      (fun k _ => hY_memLp k) (fun i _ j _ hij => hY_indep.indepFun hij)
    have hfun : (∑ k ∈ Finset.range (n + 1), Y k) = S n := by
      funext ω
      simp [S, Finset.sum_apply]
    rwa [hfun] at h
  have hIntBound : ∀ n : ℕ, ∫ ω, (S n ω) ^ 2 ∂μ ≤ C := by
    intro n
    have h1 : ∫ ω, (S n ω) ^ 2 ∂μ = ∑ k ∈ Finset.range (n + 1), ∫ ω, (Y k ω) ^ 2 ∂μ := by
      rw [← hVarS n, hVarSum n]
      exact Finset.sum_congr rfl (fun k _ => hVarY k)
    rw [h1]
    exact Summable.sum_le_tsum (Finset.range (n + 1))
      (fun k _ => integral_nonneg (fun ω => sq_nonneg (Y k ω))) hY_summable
  have hS : Submartingale S ℱ μ :=
    statopia_math_node_3300259176_dcd675c6 Ω μ Y hY_meas hY_indep hY_mean hY_memLp
  have hbdd : ∀ n : ℕ, eLpNorm (S n) 1 μ ≤ R := by
    intro n
    have h2tr : ((2 : ℝ≥0∞)).toReal = 2 := by simp
    have hnonneg : 0 ≤ ∫ ω, (S n ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg (S n ω))
    have h3 : ∫ ω, ‖S n ω‖ ^ ((2 : ℝ≥0∞)).toReal ∂μ = ∫ ω, (S n ω) ^ 2 ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [h2tr, Real.norm_eq_abs]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp
    have h4 : (∫ ω, ‖S n ω‖ ^ ((2 : ℝ≥0∞)).toReal ∂μ) ^ ((2 : ℝ≥0∞)).toReal⁻¹
        ≤ Real.sqrt C := by
      rw [h3, h2tr, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
        Real.rpow_div_two_eq_sqrt 1 hnonneg, Real.rpow_one]
      exact Real.sqrt_le_sqrt (hIntBound n)
    calc eLpNorm (S n) 1 μ ≤ eLpNorm (S n) 2 μ :=
          eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num)
            (hMemLp n).aestronglyMeasurable
      _ = ENNReal.ofReal ((∫ ω, ‖S n ω‖ ^ ((2 : ℝ≥0∞)).toReal ∂μ)
            ^ ((2 : ℝ≥0∞)).toReal⁻¹) :=
          (hMemLp n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)
      _ ≤ ENNReal.ofReal (Real.sqrt C) := ENNReal.ofReal_le_ofReal h4
      _ = ↑R := by
          rw [← ENNReal.ofReal_coe_nnreal (p := R)]
          simp [R]
  have hconv := MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd (f := S) (ℱ := ℱ) (R := R) hS hbdd
  filter_upwards [hconv] with ω hω
  obtain ⟨c, hc⟩ := hω
  refine ⟨c, ?_⟩
  exact (tendsto_add_atTop_iff_nat (f := fun n => ∑ k ∈ Finset.range n, Y k ω) (k := 1)).mp
    (by simpa [S] using hc)
  /- @proof-region region.target-node.session.a2bb3704e11ffd02 end -/

end Statlib.Imported
end

