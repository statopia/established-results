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
theorem statopia_math_node_4190851802_dd7b3e47 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
    Measurable (fun u : U =>
      ENNReal.ofReal
        (Real.exp
          (Filter.limsup
            (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
            atTop
            - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) := by
  /- @proof-region region.target-node.session.8c60cb68ee60a8af begin -/
  intro U _ _ _ _ _ _ e c hc_pos mu _ hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2
  have hinner : ∀ k : ℕ, Measurable (fun u : U => inner ℝ (e k) (u - m_mu)) := by
    intro k
    have hc : Continuous fun u : U => (e k, u - m_mu) :=
      continuous_const.prodMk (continuous_id.sub continuous_const)
    exact (continuous_inner.comp hc).measurable
  have hS : ∀ n : ℕ, Measurable (fun u : U => ∑ k ∈ Finset.range n,
      (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) := by
    intro n
    exact Finset.measurable_sum (Finset.range n) fun k _ => measurable_const.mul (hinner k)
  have hlim : Measurable (fun u : U => Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
      (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) atTop) :=
    Measurable.limsup hS
  exact Measurable.ennreal_ofReal
    (Real.continuous_exp.measurable.comp (hlim.sub measurable_const))
  /- @proof-region region.target-node.session.8c60cb68ee60a8af end -/

end Statlib.Imported
end

