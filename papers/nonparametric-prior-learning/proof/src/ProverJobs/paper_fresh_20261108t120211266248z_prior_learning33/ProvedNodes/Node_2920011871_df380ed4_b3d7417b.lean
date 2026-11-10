import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1240864340_853faf10_38c55dab
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4190851802_dd7b3e47_812a2222
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_659555420_43074f04_a6ad3ba0

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
theorem statopia_math_node_2920011871_df380ed4 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu : Measure U) [IsProbabilityMeasure mu]
    (hmu_gauss : ProbabilityTheory.IsGaussian mu)
    (m_mu m_nu : U)
    (hmu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂mu) = inner ℝ v m_mu)
    (hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_mu) * (inner ℝ w u - inner ℝ w m_mu) ∂mu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (hsigma2 : Summable
      (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)),
    ∀ q : ℝ, 0 < q →
      (∫⁻ u : U,
          ENNReal.rpow
            (ENNReal.ofReal
              (Real.exp
                (Filter.limsup
                    (fun n : ℕ => ∑ k ∈ Finset.range n,
                      (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) *
                        inner ℝ (e k) (u - m_mu))
                    atTop
                  - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2)))
            q ∂mu)
        = ENNReal.ofReal
            (Real.exp
              (q * (q - 1) / 2 *
                (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))) := by
  /- @proof-region region.target-node.session.26fdb63564cf0c91 begin -/
  intro U i1 i2 i3 i4 i5 i6 e c hc_pos mu ipmu hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2 q hq
  set σ2 : ℝ := ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2 with hσ2
  let Y : U → ℝ := fun u => Filter.limsup
    (fun n : ℕ => Finset.sum (Finset.range n) (fun k =>
      (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))) atTop
  have hσ2_nonneg : 0 ≤ σ2 := by
    rw [hσ2]
    exact tsum_nonneg fun k => mul_nonneg (inv_nonneg.mpr (hc_pos k).le) (sq_nonneg _)
  haveI hGauss : IsGaussian mu := hmu_gauss
  have hmemLp : MemLp (fun u : U => u) 2 mu := ProbabilityTheory.IsGaussian.memLp_two_fun_id
  have hInt : Integrable (fun u : U => u) mu := hmemLp.integrable (by norm_num)
  have hinner : ∀ v : U, inner ℝ v (∫ u : U, u ∂mu) = ∫ u : U, inner ℝ v u ∂mu := by
    intro v
    simpa only [coe_innerSL_apply] using
      (ContinuousLinearMap.integral_comp_comm (innerSL ℝ v) (φ := fun u : U => u) hInt).symm
  have hmean : (∫ u : U, id u ∂mu) = m_mu := by
    have hmain : (∫ u : U, u ∂mu) = m_mu := by
      refine ext_inner_left ℝ fun v => ?_
      rw [hinner v, hmu_mean v]
    simpa using hmain
  have hcov_eq : ∀ v w : U, ((covarianceBilin mu) v) w
      = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w := by
    intro v w
    rw [ProbabilityTheory.covarianceBilin_apply hmemLp v w, hmean]
    simp only [inner_sub_right]
    exact hmu_cov v w
  have hYlaw : MeasureTheory.Measure.map Y mu = gaussianReal 0 ⟨σ2, hσ2_nonneg⟩ :=
    (statopia_math_node_1240864340_853faf10 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean hmu_cov
      hsigma2 ⟨σ2, hσ2_nonneg⟩ hσ2).1
  have hYmeas : Measurable Y :=
    (statopia_math_node_1240864340_853faf10 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean hmu_cov
      hsigma2 ⟨σ2, hσ2_nonneg⟩ hσ2).2
  have hYaeme : AEMeasurable Y mu := hYmeas.aemeasurable
  have hchar : ∀ v : U, charFun mu v
      = Complex.exp (↑(inner ℝ v m_mu) * Complex.I - ↑(((covarianceBilin mu) v) v) / 2) := by
    intro v
    rw [IsGaussian.charFun_eq', hmean]
  have hIntExpG : Integrable (fun x : ℝ => Real.exp (q * x)) (gaussianReal 0 ⟨σ2, hσ2_nonneg⟩) := by
    by_contra hcon
    have hzero : (∫ x : ℝ, Real.exp (q * x) ∂gaussianReal 0 ⟨σ2, hσ2_nonneg⟩) = 0 :=
      MeasureTheory.integral_undef hcon
    rw [Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp q σ2
      hσ2_nonneg] at hzero
    exact absurd hzero (Real.exp_pos _).ne'
  have hGaussMoment :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (q * x)) ∂gaussianReal 0 ⟨σ2, hσ2_nonneg⟩)
        = ENNReal.ofReal (Real.exp (q ^ 2 * σ2 / 2)) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntExpG
      (Filter.Eventually.of_forall fun x => le_of_lt (Real.exp_pos _)),
      Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp q σ2 hσ2_nonneg]
  change (∫⁻ u : U, ENNReal.rpow (ENNReal.ofReal (Real.exp (Y u - σ2 / 2))) q ∂mu)
      = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 * σ2))
  have hpt : ∀ u : U, ENNReal.rpow (ENNReal.ofReal (Real.exp (Y u - σ2 / 2))) q
      = ENNReal.ofReal (Real.exp (q * Y u - q * σ2 / 2)) := by
    intro u
    rw [ENNReal.rpow_eq_pow,
      ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.exp_pos (Y u - σ2 / 2))) (le_of_lt hq)]
    congr 1
    rw [Real.rpow_def_of_pos (Real.exp_pos (Y u - σ2 / 2)), Real.log_exp]
    congr 1
    ring
  rw [show (∫⁻ u : U, ENNReal.rpow (ENNReal.ofReal (Real.exp (Y u - σ2 / 2))) q ∂mu)
      = (∫⁻ u : U, ENNReal.ofReal (Real.exp (q * Y u - q * σ2 / 2)) ∂mu) from
        lintegral_congr hpt]
  have hmgf : Integrable (fun u : U => Real.exp (q * Y u)) mu ∧
      (∫ u : U, Real.exp (q * Y u) ∂mu) = Real.exp (q ^ 2 * σ2 / 2) := by
    have hf : AEStronglyMeasurable (fun x : ℝ => Real.exp (q * x)) (Measure.map Y mu) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map (μ := mu) (φ := Y)
      (f := fun x : ℝ => Real.exp (q * x)) hYaeme hf
    have hval : (∫ u : U, Real.exp (q * Y u) ∂mu) = Real.exp (q ^ 2 * σ2 / 2) := by
      rw [← hmap, hYlaw,
        Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp q σ2 hσ2_nonneg]
    have hIntY : Integrable (fun u : U => Real.exp (q * Y u)) mu := by
      by_contra hcon
      have hzero : (∫ u : U, Real.exp (q * Y u) ∂mu) = 0 := MeasureTheory.integral_undef hcon
      rw [hval] at hzero
      exact absurd hzero (Real.exp_pos _).ne'
    exact ⟨hIntY, hval⟩
  obtain ⟨hIntY, hIntVal⟩ := hmgf
  have hexp_eq : ∀ u : U, Real.exp (q * Y u - q * σ2 / 2)
      = Real.exp (q * Y u) * Real.exp (-(q * σ2 / 2)) := by
    intro u
    rw [← Real.exp_add]
    congr 1
  have hInt1 : Integrable (fun u : U => Real.exp (q * Y u - q * σ2 / 2)) mu := by
    have hEq : (fun u : U => Real.exp (q * Y u - q * σ2 / 2))
        = fun u : U => Real.exp (q * Y u) * Real.exp (-(q * σ2 / 2)) := by
      funext u
      exact hexp_eq u
    rw [hEq]
    exact hIntY.mul_const _
  have hnn : 0 ≤ᶠ[ae mu] (fun u : U => Real.exp (q * Y u - q * σ2 / 2)) :=
    Filter.Eventually.of_forall fun u => le_of_lt (Real.exp_pos _)
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt1 hnn
  rw [← hbridge]
  congr 1
  have h1 : (∫ u : U, Real.exp (q * Y u - q * σ2 / 2) ∂mu)
      = ∫ u : U, Real.exp (q * Y u) * Real.exp (-(q * σ2 / 2)) ∂mu := by
    simp only [hexp_eq]
  rw [h1, MeasureTheory.integral_mul_const, hIntVal, ← Real.exp_add]
  congr 1
  ring
  /- @proof-region region.target-node.session.26fdb63564cf0c91 end -/

end Statlib.Imported
end

