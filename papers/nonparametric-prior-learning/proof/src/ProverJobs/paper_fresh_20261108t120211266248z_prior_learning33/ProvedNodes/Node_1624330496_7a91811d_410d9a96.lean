import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1446388444_2df19b16_f145f1f3
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1939896492_b20f2010_659f2bca
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3664839893_07e7a1c0_85f524ed
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_842457010_92ed615e_9ed0bfe8

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
theorem statopia_math_node_1624330496_7a91811d : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (ν : Measure U) [IsProbabilityMeasure ν]
    (hnu_gauss : ProbabilityTheory.IsGaussian ν)
    (mUM mNU : U)
    (hmean_mu : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v mUM)
    (hmean_nu : ∀ v : U, ∫ u, inner ℝ v u ∂ν = inner ℝ v mNU)
    (hcov_mu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
        (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ = if k = l then c k else 0)
    (hcov_nu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mNU) *
        (inner ℝ (e l) u - inner ℝ (e l) mNU) ∂ν = if k = l then c k else 0)
    (hint1_mu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2_mu : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ)
    (hint1_nu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) ν)
    (hint2_nu : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mNU) * (inner ℝ w u - inner ℝ w mNU)) ν)
    (hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
    (rho : U → ℝ≥0∞) (hrho_meas : Measurable rho)
    (hrho_limit : ∀ᵐ u ∂μ,
      Tendsto (fun n : ℕ => ENNReal.ofReal
        (Real.exp ((∑ k ∈ Finset.range n,
            (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) atTop (𝓝 (rho u))),
    (∀ (F : Finset ℕ) (B : Set ({k : ℕ // k ∈ F} → ℝ)), MeasurableSet B →
      ∫⁻ u in {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B}, rho u ∂μ
        = ν {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B}) ∧
      ν = μ.withDensity rho ∧
      ν ≪ μ ∧ μ ≪ ν ∧
      ν.rnDeriv μ =ᵐ[μ] rho := by
  /- @proof-region region.target-node.session.a02b19533658b64e begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss ν _ hnu_gauss mUM mNU
    hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
    ρ hρ_meas hρ_limit
  classical
  have dep2 := statopia_math_node_3664839893_07e7a1c0 U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
    hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum
  obtain ⟨-, -, -, -, hex⟩ := dep2
  obtain ⟨ρ', hP⟩ := hex
  have hρ'_lim := hP.2.1
  have hρ'_pos := hP.2.2.2.2.2
  have hρ_eq : ρ =ᵐ[μ] ρ' := by
    filter_upwards [hρ_limit, hρ'_lim] with u hu hu'
    exact tendsto_nhds_unique hu hu'
  have hρ'_ne : ∀ᵐ u ∂μ, ρ' u ≠ 0 := by
    filter_upwards [hρ'_pos] with u hu
    obtain ⟨x, _, hx_eq, _⟩ := hu
    rw [hx_eq]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hρ_ne : ∀ᵐ u ∂μ, ρ u ≠ 0 := by
    filter_upwards [hρ_eq, hρ'_ne] with u hueq hne
    rw [hueq]
    exact hne
  have hcyl := statopia_math_node_1939896492_b20f2010 U e c hc μ hmu_gauss ν hnu_gauss mUM mNU
    hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum ρ hρ_meas hρ_limit
  have h2 : ν = μ.withDensity ρ :=
    statopia_math_node_1446388444_2df19b16 U e μ ν ρ hρ_meas hcyl
  have h3 : ν ≪ μ := by
    rw [h2]
    exact withDensity_absolutelyContinuous μ ρ
  have h5 : ν.rnDeriv μ =ᵐ[μ] ρ := by
    rw [h2]
    exact Measure.rnDeriv_withDensity μ hρ_meas
  refine ⟨hcyl, h2, h3, ?_, h5⟩
  · rw [h2]
    exact withDensity_absolutelyContinuous' hρ_meas.aemeasurable hρ_ne
  /- @proof-region region.target-node.session.a02b19533658b64e end -/

end Statlib.Imported
end

