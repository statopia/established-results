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
theorem statopia_math_node_18671509_e0d2ff36 : ∀ (n : ℕ) (c d s : ℕ → ℝ)
    (hc : ∀ i : ℕ, 0 < c i),
    ∫⁻ x : Fin n → ℝ,
        (ENNReal.ofReal (Real.exp ((∑ i : Fin n, d (i : ℕ) * (x i - s (i : ℕ)))
          - (∑ i : Fin n, d (i : ℕ) ^ 2 * c (i : ℕ)) / 2))) ^ 2
        ∂(MeasureTheory.Measure.pi (fun i : Fin n =>
          ProbabilityTheory.gaussianReal (s (i : ℕ))
            ⟨c (i : ℕ), le_of_lt (hc (i : ℕ))⟩))
      = ENNReal.ofReal (Real.exp (∑ i : Fin n, d (i : ℕ) ^ 2 * c (i : ℕ))) := by
  /- @proof-region region.target-node.session.ba4d3d5f01effab9 begin -/
  intro n c d s hc
  let μ : (i : Fin n) → Measure ℝ := fun i => ProbabilityTheory.gaussianReal (s (i:ℕ)) ⟨c (i:ℕ), le_of_lt (hc (i:ℕ))⟩
  let P : Measure (Fin n → ℝ) := MeasureTheory.Measure.pi μ
  let E : (Fin n → ℝ) → ℝ := fun x => (∑ i : Fin n, d (i:ℕ) * (x i - s (i:ℕ))) - (∑ i : Fin n, d (i:ℕ)^2 * c (i:ℕ)) / 2
  let f : (i : Fin n) → ℝ → ℝ := fun i y => Real.exp (2 * d (i:ℕ) * (y - s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ))
  change ∫⁻ x : Fin n → ℝ, (ENNReal.ofReal (Real.exp (E x)))^2 ∂P = ENNReal.ofReal (Real.exp (∑ i : Fin n, d (i:ℕ)^2 * c (i:ℕ)))
  have hexp : ∀ x : Fin n → ℝ, (ENNReal.ofReal (Real.exp (E x)))^2 = ENNReal.ofReal (Real.exp (2 * E x)) := by
    intro x
    rw [← ENNReal.ofReal_pow (Real.exp_pos (E x)).le 2]
    congr 1
    rw [pow_two, ← Real.exp_add, ← two_mul]
  have step1 : ∫⁻ x : Fin n → ℝ, (ENNReal.ofReal (Real.exp (E x)))^2 ∂P = ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (2 * E x)) ∂P := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with x
    exact hexp x
  have hNonneg : 0 ≤ᵐ[P] (fun x : Fin n → ℝ => Real.exp (2 * E x)) :=
    Filter.Eventually.of_forall (fun x => (Real.exp_pos (2 * E x)).le)
  have hE : ∀ x : Fin n → ℝ, 2 * E x = ∑ i : Fin n, (2 * d (i:ℕ) * (x i - s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) := by
    intro x
    show 2 * ((∑ i : Fin n, d (i:ℕ) * (x i - s (i:ℕ))) - (∑ i : Fin n, d (i:ℕ)^2 * c (i:ℕ)) / 2) = ∑ i : Fin n, (2 * d (i:ℕ) * (x i - s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ))
    rw [Finset.sum_sub_distrib]
    have hA : (∑ i : Fin n, 2 * d (i:ℕ) * (x i - s (i:ℕ))) = 2 * (∑ i : Fin n, d (i:ℕ) * (x i - s (i:ℕ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hA]
    ring
  have hprod : ∀ x : Fin n → ℝ, Real.exp (2 * E x) = ∏ i : Fin n, f i (x i) := by
    intro x
    rw [hE x, Real.exp_sum]
  have hfun : (fun x : Fin n → ℝ => Real.exp (2 * E x)) = fun x => ∏ i : Fin n, f i (x i) := by
    funext x
    exact hprod x
  have hsplitG : ∀ (i : Fin n) (y : ℝ), f i y = Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) * Real.exp ((2 * d (i:ℕ)) * y) := by
    intro i y
    show Real.exp (2 * d (i:ℕ) * (y - s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) = Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) * Real.exp ((2 * d (i:ℕ)) * y)
    rw [← Real.exp_add]
    congr 1
    ring
  have hInt : MeasureTheory.Integrable (fun x : Fin n → ℝ => Real.exp (2 * E x)) P := by
    rw [hfun]
    apply MeasureTheory.Integrable.fin_nat_prod (μ := μ) (f := f)
    intro i
    have h0 : MeasureTheory.Integrable (fun y : ℝ => Real.exp ((2 * d (i:ℕ)) * y)) (μ i) :=
      ProbabilityTheory.integrable_exp_mul_gaussianReal (2 * d (i:ℕ))
    have hbase : MeasureTheory.Integrable (fun y : ℝ => Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) * Real.exp ((2 * d (i:ℕ)) * y)) (μ i) :=
      h0.const_mul (Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)))
    refine hbase.congr ?_
    filter_upwards with y
    exact (hsplitG i y).symm
  have step2 : ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (2 * E x)) ∂P = ENNReal.ofReal (∫ x : Fin n → ℝ, Real.exp (2 * E x) ∂P) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
  have step3 : ∫ x : Fin n → ℝ, Real.exp (2 * E x) ∂P = Real.exp (∑ i : Fin n, d (i:ℕ)^2 * c (i:ℕ)) := by
    rw [hfun]
    rw [MeasureTheory.integral_fin_nat_prod_eq_prod (μ := μ) (f := f)]
    have hmgf : ∀ i : Fin n, ∫ y, Real.exp ((2 * d (i:ℕ)) * y) ∂μ i = Real.exp (s (i:ℕ) * (2 * d (i:ℕ)) + (c (i:ℕ) : ℝ) * (2 * d (i:ℕ)) ^ 2 / 2) := by
      intro i
      have h := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := s (i:ℕ)) (v := ⟨c (i:ℕ), le_of_lt (hc (i:ℕ))⟩)) (2 * d (i:ℕ))
      unfold ProbabilityTheory.mgf at h
      simpa only [NNReal.coe_mk] using h
    have hfac : ∀ i : Fin n, ∫ y, f i y ∂μ i = Real.exp (d (i:ℕ)^2 * c (i:ℕ)) := by
      intro i
      calc ∫ y, f i y ∂μ i
          = ∫ y, Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) * Real.exp ((2 * d (i:ℕ)) * y) ∂μ i := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              exact hsplitG i y
        _ = Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) * ∫ y, Real.exp ((2 * d (i:ℕ)) * y) ∂μ i := by
              rw [MeasureTheory.integral_const_mul]
        _ = Real.exp (-(2 * d (i:ℕ) * s (i:ℕ)) - d (i:ℕ)^2 * c (i:ℕ)) * Real.exp (s (i:ℕ) * (2 * d (i:ℕ)) + (c (i:ℕ) : ℝ) * (2 * d (i:ℕ)) ^ 2 / 2) := by
              rw [hmgf i]
        _ = Real.exp (d (i:ℕ)^2 * c (i:ℕ)) := by
              rw [← Real.exp_add]
              congr 1
              ring
    have hprod2 : ∏ i : Fin n, ∫ y, f i y ∂μ i = ∏ i : Fin n, Real.exp (d (i:ℕ)^2 * c (i:ℕ)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact hfac i
    rw [hprod2, ← Real.exp_sum]
  rw [step1, step2, step3]
  /- @proof-region region.target-node.session.ba4d3d5f01effab9 end -/

end Statlib.Imported
end

