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
theorem statopia_math_node_3199133157_4a242571 : ∀ (c : ℝ) (hc : 0 < c) (m n : ℝ),
    let δ : ℝ := n - m
    let a : ℝ := c⁻¹ * δ
    let d : ℝ → ℝ := fun y => Real.exp (a * (y - m) - (2 : ℝ)⁻¹ * a * δ)
    Measurable (fun y : ℝ => ENNReal.ofReal (d y)) ∧
      gaussianReal n (Real.toNNReal c) =
        (gaussianReal m (Real.toNNReal c)).withDensity (fun y => ENNReal.ofReal (d y)) ∧
      (∫⁻ y, ENNReal.ofReal (d y) ∂(gaussianReal m (Real.toNNReal c)) = 1) ∧
      (∫⁻ y, (ENNReal.ofReal (d y)) ^ 2 ∂(gaussianReal m (Real.toNNReal c)) =
        ENNReal.ofReal (Real.exp (c⁻¹ * δ ^ 2))) := by
  /- @proof-region region.target-node.session.2b86a41d45243a9c begin -/
  intro c hc m n
  dsimp only
  set δ : ℝ := n - m with hδ
  set a : ℝ := c⁻¹ * δ with ha
  set v : NNReal := Real.toNNReal c with hv
  have hcoe : (v : ℝ) = c := by rw [hv]; exact Real.coe_toNNReal c hc.le
  have hv0 : v ≠ 0 := by
    intro h
    have h0 : (0 : ℝ) = c := by simpa [h] using hcoe
    linarith
  have hpt : ∀ y : ℝ, Real.exp (-(a * m) - 2⁻¹ * a * δ) * Real.exp (a * y)
      = Real.exp (a * (y - m) - 2⁻¹ * a * δ) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    ring
  have hmom (t : ℝ) : ∫ y, Real.exp (t * y) ∂(gaussianReal m v)
      = Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
    have h := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := m) (v := v)) t
    simpa [ProbabilityTheory.mgf] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((continuous_const.mul (continuous_id.sub continuous_const)).sub continuous_const).measurable)
  · have hmeasd : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (a * (y - m) - 2⁻¹ * a * δ))) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((continuous_const.mul (continuous_id.sub continuous_const)).sub continuous_const).measurable)
    have hcont : Continuous fun x : ℝ => gaussianPDFReal m v x := by
      simp only [ProbabilityTheory.gaussianPDFReal]
      fun_prop
    have hmpdf : Measurable (gaussianPDF m v) := by
      show Measurable fun x : ℝ => ENNReal.ofReal (gaussianPDFReal m v x)
      exact ENNReal.measurable_ofReal.comp hcont.measurable
    have hpoint : ∀ x : ℝ, gaussianPDFReal n v x
        = gaussianPDFReal m v x * Real.exp (a * (x - m) - 2⁻¹ * a * δ) := by
      intro x
      simp only [ProbabilityTheory.gaussianPDFReal]
      have hexp : -(x - n) ^ 2 / (2 * (v : ℝ))
          = -(x - m) ^ 2 / (2 * (v : ℝ)) + (a * (x - m) - 2⁻¹ * a * δ) := by
        rw [ha, hcoe, hδ]
        have hcne : c ≠ 0 := ne_of_gt hc
        field_simp
        ring
      rw [hexp, Real.exp_add]
      ring
    have hden : ∀ x : ℝ, gaussianPDF n v x
        = gaussianPDF m v x * ENNReal.ofReal (Real.exp (a * (x - m) - 2⁻¹ * a * δ)) := by
      intro x
      show ENNReal.ofReal (gaussianPDFReal n v x)
        = ENNReal.ofReal (gaussianPDFReal m v x)
          * ENNReal.ofReal (Real.exp (a * (x - m) - 2⁻¹ * a * δ))
      rw [hpoint x, ENNReal.ofReal_mul' (le_of_lt (Real.exp_pos _))]
    have hmulden : gaussianPDF n v
        = gaussianPDF m v * fun y : ℝ => ENNReal.ofReal (Real.exp (a * (y - m) - 2⁻¹ * a * δ)) := by
      funext x
      simpa using hden x
    rw [ProbabilityTheory.gaussianReal_of_var_ne_zero n hv0,
      ProbabilityTheory.gaussianReal_of_var_ne_zero m hv0,
      ← MeasureTheory.withDensity_mul _ hmpdf hmeasd, hmulden]
  · have hint : Integrable (fun y : ℝ => Real.exp (a * (y - m) - 2⁻¹ * a * δ))
        (gaussianReal m v) := by
      have h0 : Integrable (fun y : ℝ => Real.exp (a * y)) (gaussianReal m v) :=
        ProbabilityTheory.integrable_exp_mul_gaussianReal a
      refine (h0.const_mul (Real.exp (-(a * m) - 2⁻¹ * a * δ))).congr ?_
      filter_upwards with y
      simpa using hpt y
    have hreal : ∫ y, Real.exp (a * (y - m) - 2⁻¹ * a * δ) ∂(gaussianReal m v) = 1 := by
      have hfun : (fun y : ℝ => Real.exp (a * (y - m) - 2⁻¹ * a * δ))
          = fun y : ℝ => Real.exp (-(a * m) - 2⁻¹ * a * δ) * Real.exp (a * y) := by
        funext y
        exact (hpt y).symm
      rw [hfun, MeasureTheory.integral_const_mul, hmom a, ← Real.exp_add]
      have hzero : -(a * m) - 2⁻¹ * a * δ + (m * a + (v : ℝ) * a ^ 2 / 2) = 0 := by
        rw [ha, hcoe]
        have hcne : c ≠ 0 := ne_of_gt hc
        field_simp
        ring
      rw [hzero, Real.exp_zero]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le), hreal, ENNReal.ofReal_one]
  · have hsq : ∀ y : ℝ, (ENNReal.ofReal (Real.exp (a * (y - m) - 2⁻¹ * a * δ))) ^ 2
        = ENNReal.ofReal (Real.exp (a * (y - m) - 2⁻¹ * a * δ) ^ 2) := by
      intro y
      simp only [pow_two]
      rw [ENNReal.ofReal_mul' (le_of_lt (Real.exp_pos _))]
    have hexp2 : ∀ y : ℝ, Real.exp (a * (y - m) - 2⁻¹ * a * δ) ^ 2
        = Real.exp (-(2 * a * m) - a * δ) * Real.exp (2 * a * y) := by
      intro y
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring_nf
    have hint2 : Integrable (fun y : ℝ => Real.exp (a * (y - m) - 2⁻¹ * a * δ) ^ 2)
        (gaussianReal m v) := by
      have h0 : Integrable (fun y : ℝ => Real.exp ((2 * a) * y)) (gaussianReal m v) :=
        ProbabilityTheory.integrable_exp_mul_gaussianReal (2 * a)
      refine (h0.const_mul (Real.exp (-(2 * a * m) - a * δ))).congr ?_
      filter_upwards with y
      simpa using (hexp2 y).symm
    have hreal2 : ∫ y, Real.exp (a * (y - m) - 2⁻¹ * a * δ) ^ 2 ∂(gaussianReal m v)
        = Real.exp (c⁻¹ * δ ^ 2) := by
      have hfun : (fun y : ℝ => Real.exp (a * (y - m) - 2⁻¹ * a * δ) ^ 2)
          = fun y : ℝ => Real.exp (-(2 * a * m) - a * δ) * Real.exp (2 * a * y) :=
        funext fun y => hexp2 y
      rw [hfun, MeasureTheory.integral_const_mul, hmom (2 * a), ← Real.exp_add]
      have hzero : -(2 * a * m) - a * δ + (m * (2 * a) + (v : ℝ) * (2 * a) ^ 2 / 2)
          = c⁻¹ * δ ^ 2 := by
        rw [ha, hcoe, hδ]
        have hcne : c ≠ 0 := ne_of_gt hc
        field_simp
        ring
      rw [hzero]
    simp only [hsq]
    rw [← ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun y => sq_nonneg (Real.exp (a * (y - m) - 2⁻¹ * a * δ))), hreal2]
  /- @proof-region region.target-node.session.2b86a41d45243a9c end -/

end Statlib.Imported
end

