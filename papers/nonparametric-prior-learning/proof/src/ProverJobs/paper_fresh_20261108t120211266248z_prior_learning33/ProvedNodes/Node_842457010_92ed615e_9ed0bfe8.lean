import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_114927384_d5c2bee4_75a6a0a7
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_18671509_e0d2ff36_418b4aba
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_4234478114_9734e7cc_9452e5ed
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_454462448_6086eebe_8546ee4b
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_479546447_56c0a7ce_01331cfa

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
theorem statopia_math_node_842457010_92ed615e : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) * (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ
        = if k = l then c k else 0)
    (hcov_nu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mNU) * (inner ℝ (e l) u - inner ℝ (e l) mNU) ∂ν
        = if k = l then c k else 0)
    (hint1_mu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2_mu : ∀ v w : U, Integrable (fun u : U =>
      (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ)
    (hint1_nu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) ν)
    (hint2_nu : ∀ v w : U, Integrable (fun u : U =>
      (inner ℝ v u - inner ℝ v mNU) * (inner ℝ w u - inner ℝ w mNU)) ν)
    (hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
    (F : Finset ℕ),
    Measurable (fun u : U =>
        Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∧
      (∀ u : U, 0 < Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
          - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∧
      (∀ B : Set ({k : ℕ // k ∈ F} → ℝ), MeasurableSet B →
        ν {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B}
          = ∫⁻ u in {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ B},
              ENNReal.ofReal
                (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
                  - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ) ∧
      (∫⁻ u : U,
          ENNReal.ofReal
            (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
              - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∂μ = 1) ∧
      (∫⁻ u : U,
          (ENNReal.ofReal
            (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
              - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) ^ 2 ∂μ
        = ENNReal.ofReal
            (Real.exp (∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
  /- @proof-region region.target-node.session.01241f1e57dfedd3 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss ν _ hnu_gauss mUM mNU hmean_mu hmean_nu hcov_mu hcov_nu hint1_mu hint2_mu hint1_nu hint2_nu hsum F
  try dsimp only
  have hmeas : Measurable (fun u : U => Real.exp (∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM) - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) := by measurability
  have hpos : ∀ u : U, 0 < Real.exp (∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM) - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) := fun u => Real.exp_pos _
  have hdep_mu := statopia_math_node_114927384_d5c2bee4 (e := e) (c := c) (hc := hc) (μ := μ) (hmu_gauss := hmu_gauss) (m := mUM) (hmean := hmean_mu) (hcov_diag := hcov_mu) (hint1 := hint1_mu) (hint2 := hint2_mu)
  let ι : U → ({k : ℕ // k ∈ F} → ℝ) := fun u k => inner ℝ (e k.1) u
  let Pmu : Measure ({k : ℕ // k ∈ F} → ℝ) := Measure.pi (fun k => gaussianReal (inner ℝ (e k.1) mUM) (Real.toNNReal (c k.1)))
  have hmap_mu : Measure.map ι μ = Pmu := (hdep_mu.1 F).1
  let Pnu : Measure ({k : ℕ // k ∈ F} → ℝ) := Measure.pi (fun k => gaussianReal (inner ℝ (e k.1) mNU) (Real.toNNReal (c k.1)))
  have hdep_nu := statopia_math_node_114927384_d5c2bee4 (e := e) (c := c) (hc := hc) (μ := ν) (hmu_gauss := hnu_gauss) (m := mNU) (hmean := hmean_nu) (hcov_diag := hcov_nu) (hint1 := hint1_nu) (hint2 := hint2_nu)
  have hmap_nu : Measure.map ι ν = Pnu := (hdep_nu.1 F).1
  have hii := statopia_math_node_4234478114_9734e7cc U e c hc μ ν mUM mNU F hmap_mu hmap_nu
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hmeas
  · exact hpos
  · exact hii
  · have h := (hii Set.univ MeasurableSet.univ).symm
    rw [show {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) ∈ Set.univ} = Set.univ from by ext u; simp] at h
    rw [Measure.restrict_univ, measure_univ] at h
    exact h
  · exact statopia_math_node_479546447_56c0a7ce U e c hc μ mUM mNU F hmap_mu
  /- @proof-region region.target-node.session.01241f1e57dfedd3 end -/

end Statlib.Imported
end

