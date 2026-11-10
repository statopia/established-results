import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2920011871_df380ed4_b3d7417b
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_303701622_51d4ad9b_2d3121e0
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
theorem statopia_math_node_744484935_68a4c774 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu nu : Measure U) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu_gauss : ProbabilityTheory.IsGaussian mu)
    (hnu_gauss : ProbabilityTheory.IsGaussian nu)
    (m_mu m_nu : U)
    (hmu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂mu) = inner ℝ v m_mu)
    (hnu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂nu) = inner ℝ v m_nu)
    (hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_mu) * (inner ℝ w u - inner ℝ w m_mu) ∂mu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (hnu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_nu) * (inner ℝ w u - inner ℝ w m_nu) ∂nu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (hmu_int1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) mu)
    (hnu_int1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) nu)
    (hmu_int2 : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v m_mu) * (inner ℝ w u - inner ℝ w m_mu)) mu)
    (hnu_int2 : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v m_nu) * (inner ℝ w u - inner ℝ w m_nu)) nu)
    (hsigma2 : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)),
    ∃ rho : U → ℝ≥0∞,
      Measurable rho ∧
      nu = mu.withDensity rho ∧
      rho =ᵐ[mu] (fun u : U =>
        ENNReal.ofReal (Real.exp
          ((Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) Filter.atTop)
            - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) ∧
      mu {u : U | rho u = ⊤} = 0 ∧
      (∀ᵐ u ∂mu, 0 < rho u) ∧
      (∀ q : ℝ, 0 < q →
        (∫⁻ u : U, ENNReal.rpow (rho u) q ∂mu)
          = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
              (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)))) ∧
      (∫⁻ u : U, rho u ∂mu) = 1 ∧
      (∫⁻ u : U, ENNReal.rpow (rho u) (2 : ℝ) ∂mu)
        = ENNReal.ofReal (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)) ∧
      ENNReal.ofReal (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)) < ⊤ := by
  /- @proof-region region.target-node.session.d79081ed12efa609 begin -/
  intro U _ _ _ _ _ _ e c hc_pos mu nu _ _ hmu_gauss hnu_gauss m_mu m_nu hmu_mean hnu_mean hmu_cov hnu_cov
    hmu_int1 hnu_int1 hmu_int2 hnu_int2 hsigma2
  let rho : U → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (
      Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        Filter.atTop
      - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))
  have hmeas : Measurable rho :=
    statopia_math_node_4190851802_dd7b3e47 U e c hc_pos mu hmu_gauss m_mu m_nu
      hmu_mean hmu_cov hsigma2
  have hν : nu = mu.withDensity rho :=
    statopia_math_node_303701622_51d4ad9b U e c hc_pos mu nu hmu_gauss hnu_gauss m_mu m_nu
      hmu_mean hnu_mean hmu_cov hnu_cov hsigma2
  have hmom : ∀ q : ℝ, 0 < q → (∫⁻ u, ENNReal.rpow (rho u) q ∂mu)
      = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
          (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))) :=
    statopia_math_node_2920011871_df380ed4 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean hmu_cov
      hsigma2
  have htop : mu {u : U | rho u = ⊤} = 0 := by
    have hgen : ∀ f : U → ℝ≥0∞, (∀ u : U, f u < ⊤) → mu {u : U | f u = ⊤} = 0 := by
      intro f hf
      have hempty : {u : U | f u = ⊤} = ∅ := by
        ext u
        simp [(hf u).ne]
      rw [hempty]
      simp
    exact hgen rho (fun u => by simp [rho])
  have hpos : ∀ᵐ u ∂mu, 0 < rho u := by
    exact Filter.Eventually.of_forall (fun u => by simp [rho, Real.exp_pos])
  have hone : (∫⁻ u, rho u ∂mu) = 1 := by
    have h1 : (mu.withDensity rho) Set.univ = 1 := by
      rw [← hν]
      exact measure_univ
    simpa using h1
  have htwo : (∫⁻ u, ENNReal.rpow (rho u) 2 ∂mu)
      = ENNReal.ofReal (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)) := by
    rw [hmom 2 (by norm_num), (show 2 * (2 - 1) / 2 = (1 : ℝ) by norm_num), one_mul]
  refine ⟨rho, hmeas, hν, ?_, htop, hpos, hmom, hone, htwo, ?_⟩
  · exact Filter.Eventually.of_forall (fun u => rfl)
  · simp
  /- @proof-region region.target-node.session.d79081ed12efa609 end -/

end Statlib.Imported
end

