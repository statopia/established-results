import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_217884646_5adaea34_f1c80027
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
theorem statopia_math_node_1240864340_853faf10 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
      (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))
    (v : NNReal)
    (hv : (v : ℝ) = ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2),
    MeasureTheory.Measure.map
        (fun u : U =>
          Filter.limsup
            (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            atTop) mu
      = ProbabilityTheory.gaussianReal 0 v ∧
      Measurable
        (fun u : U =>
          Filter.limsup
            (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            atTop) := by
  /- @proof-region region.target-node.session.055b1eab7df01ad5 begin -/
  intro U _ _ _ _ _ _ e c hc_pos mu _ hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2 v hv
  let Z : U → ℝ := fun u => Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) atTop
  let C : ℝ := ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2
  change Measure.map Z mu = ProbabilityTheory.gaussianReal 0 v ∧ Measurable Z
  have hZmeas : Measurable Z := by
    have hdep : Measurable (fun u : U => ENNReal.ofReal (Real.exp (Z u - C / 2))) :=
      statopia_math_node_4190851802_dd7b3e47 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2
    have hlog : Measurable (fun u : U => Real.log ((ENNReal.ofReal (Real.exp (Z u - C / 2))).toReal)) :=
      Real.measurable_log.comp (ENNReal.measurable_toReal.comp hdep)
    have heq : (fun u : U => Real.log ((ENNReal.ofReal (Real.exp (Z u - C / 2))).toReal)) = fun u => Z u - C / 2 := by
      funext u
      simp only [ENNReal.toReal_ofReal (Real.exp_pos (Z u - C / 2)).le, Real.log_exp]
    rw [heq] at hlog
    have h2 : Measurable (fun u : U => (Z u - C / 2) + C / 2) :=
      hlog.add (measurable_const : Measurable (fun _ : U => C / 2))
    have h3 : (fun u : U => (Z u - C / 2) + C / 2) = Z := by
      funext u
      ring
    rwa [h3] at h2
  have hae : ∀ᵐ u ∂mu, ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) Filter.atTop (nhds L) :=
    statopia_math_node_659555420_43074f04 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2
  have hlaw : Measure.map Z mu = ProbabilityTheory.gaussianReal 0 v :=
    statopia_math_node_217884646_5adaea34 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2 hae hZmeas v hv
  exact ⟨hlaw, hZmeas⟩
  /- @proof-region region.target-node.session.055b1eab7df01ad5 end -/

end Statlib.Imported
end

