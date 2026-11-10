import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1011247203_7dc03555_72b83afd
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_114927384_d5c2bee4_75a6a0a7
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2291221282_5741a895_ef4586d7
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3664839893_07e7a1c0_85f524ed

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
theorem statopia_math_node_3480907983_5dd3c633 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (mUM mNU : U)
    (hmean : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v mUM)
    (hcov_diag : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
        (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ = if k = l then c k else 0)
    (hint1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2 : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ)
    (hsum : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))
    (hae : ∀ᵐ u ∂μ,
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) atTop
        (𝓝 (∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))))
    (ν : Measure U) [IsProbabilityMeasure ν]
    (hnu_gauss : ProbabilityTheory.IsGaussian ν)
    (hmean_nu : ∀ v : U, ∫ u, inner ℝ v u ∂ν = inner ℝ v mNU)
    (hcov_nu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mNU) *
        (inner ℝ (e l) u - inner ℝ (e l) mNU) ∂ν = if k = l then c k else 0)
    (hint1_nu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) ν)
    (hint2_nu : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v mNU) * (inner ℝ w u - inner ℝ w mNU)) ν)
    (ρ : U → ℝ≥0∞) (hρ_meas : Measurable ρ)
    (hρ_lim : ∀ᵐ u ∂μ,
      Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (
          (∑ k ∈ Finset.range n,
              (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
            - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
                (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) atTop (𝓝 (ρ u)))

    (hν : ν = μ.withDensity ρ),
    Measurable (fun u : U =>
        ∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) ∧
      Measure.map (fun u : U =>
          ∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) μ
        = gaussianReal 0
            (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) ∧
      (∀ q : ℝ, 0 < q →
        ∫⁻ u : U, ENNReal.rpow (ρ u) q ∂μ
          = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
              (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)))) ∧
      (∀ g : U → ℝ≥0∞, Measurable g → ∫⁻ u : U, g u ∂ν = ∫⁻ u : U, g u * ρ u ∂μ) := by
  /- @proof-region region.target-node.session.444435b5fa80dd93 begin -/
  intro U _ _ _ _ _ _ e c hc mu _ hmu_gauss mUM mNU
    hmean_mu hcov_mu hint1_mu hint2_mu hsum hae nu _ hnu_gauss hmean_nu hcov_nu hint1_nu hint2_nu
    rho hrho_meas hrho_lim hnu
  have hSnn : (0 : ℝ) ≤ ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (inv_nonneg.2 (le_of_lt (hc k))) (sq_nonneg _)
  have hZmeas : Measurable (fun u : U => ∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) :=
    statopia_math_node_1011247203_7dc03555 U e (fun k : ℕ => (c k)⁻¹ * inner ℝ (e k) (mNU - mUM)) mUM
  have hfin : ∀ n : ℕ,
      Measure.map (fun u : U => ∑ k : {k : ℕ // k ∈ Finset.range n},
          ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)) * (inner ℝ (e k) u - inner ℝ (e k) mUM)) mu
        = gaussianReal 0 (Real.toNNReal (∑ k : {k : ℕ // k ∈ Finset.range n},
            ((c k)⁻¹ * inner ℝ (e k) (mNU - mUM)) ^ 2 * c k)) := fun n =>
    (statopia_math_node_114927384_d5c2bee4 U e c hc mu hmu_gauss mUM hmean_mu hcov_mu hint1_mu hint2_mu).2
      (Finset.range n) (fun k => (c k)⁻¹ * inner ℝ (e k) (mNU - mUM))
  have hZ_law : Measure.map (fun u : U => ∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) mu
      = gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) :=
    statopia_math_node_2291221282_5741a895 U e c mu mUM mNU hsum hae hfin
  have hsig : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) atTop
      (𝓝 (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) :=
    hsum.hasSum.tendsto_sum_nat
  have hne_top : ∀ᵐ u ∂mu, rho u ≠ ⊤ := by
    have hkey := MeasureTheory.lintegral_withDensity_eq_lintegral_mul mu hrho_meas
      (measurable_const : Measurable fun _ : U => (1 : ℝ≥0∞))
    have hone : ∫⁻ a : U, (1 : U → ℝ≥0∞) a ∂(mu.withDensity rho) = 1 := by
      rw [← hnu]
      simp
    have hone' : ∫⁻ u : U, rho u ∂mu = 1 := by
      calc ∫⁻ u : U, rho u ∂mu
          = ∫⁻ u : U, (rho * fun _ : U => (1 : ℝ≥0∞)) u ∂mu := lintegral_congr fun u => by simp
        _ = ∫⁻ u : U, (1 : U → ℝ≥0∞) u ∂(mu.withDensity rho) := hkey.symm
        _ = 1 := hone
    have hzero : mu {u : U | rho u = ⊤} = 0 :=
      MeasureTheory.measure_eq_top_of_lintegral_ne_top hrho_meas.aemeasurable
        (by rw [hone']; exact ENNReal.one_ne_top)
    have hmem : {u : U | rho u ≠ ⊤} ∈ ae mu := by
      rw [MeasureTheory.mem_ae_iff]
      have hcompl : {u : U | ¬rho u = ⊤}ᶜ = {u : U | rho u = ⊤} := by
        ext u
        simp
      rw [hcompl]
      exact hzero

    exact hmem


  have hrho_form : ∀ᵐ u ∂mu, rho u = ENNReal.ofReal (Real.exp ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) := by
    refine (hne_top.and (hrho_lim.and hae)).mono ?_
    intro u hu
    obtain ⟨hne, hlim, htsum⟩ := hu
    have hreal : Tendsto (fun n : ℕ => Real.exp ((∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) atTop
        (𝓝 (Real.exp ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) :=
      (Real.continuous_exp.tendsto _).comp (htsum.sub (hsig.const_mul (2 : ℝ)⁻¹))
    have htoReal : Tendsto (fun n : ℕ => (ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))).toReal) atTop
        (𝓝 ((rho u).toReal)) :=
      (ENNReal.continuousAt_toReal hne).tendsto.comp hlim
    have hfun : (fun n : ℕ => (ENNReal.ofReal (Real.exp ((∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))).toReal)
        = (fun n : ℕ => Real.exp ((∑ k ∈ Finset.range n, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) := by
      funext n
      exact ENNReal.toReal_ofReal (Real.exp_pos _).le
    rw [hfun] at htoReal
    have hval := tendsto_nhds_unique htoReal hreal
    rw [← ENNReal.ofReal_toReal hne, hval]
    have harg : (∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
        = (∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2 := by
      ring
    rw [harg]

  refine ⟨hZmeas, hZ_law, ?_, ?_⟩
  · intro q hq
    have h1 : ∫⁻ u : U, ENNReal.rpow (rho u) q ∂mu
        = ∫⁻ u : U, ENNReal.ofReal (Real.exp (q * ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))) ∂mu := by
      refine lintegral_congr_ae ?_
      refine hrho_form.mono ?_
      intro u hu
      simp only [hu]
      have hpos : 0 < Real.exp ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2) := Real.exp_pos _
      show ENNReal.ofReal (Real.exp ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) ^ q = ENNReal.ofReal (Real.exp (q * ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)))
      rw [ENNReal.ofReal_rpow_of_nonneg hpos.le (le_of_lt hq), Real.rpow_def_of_pos hpos q, Real.log_exp]
      rw [mul_comm ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2) q]
    have h2 : ∫⁻ u : U, ENNReal.ofReal (Real.exp (q * ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))) ∂mu
        = ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (q * (x - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))) ∂(gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
      have hF : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (q * (x - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)))) := by
        measurability
      have hkey := MeasureTheory.lintegral_map (μ := mu) hF hZmeas
      rw [hZ_law] at hkey
      exact hkey.symm
    have hInt : Integrable (fun x : ℝ => Real.exp (q * (x - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))) (gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
      have hbase : Integrable (fun x : ℝ => Real.exp (q * x)) (gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) :=
        ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) q
      refine (hbase.const_mul (Real.exp (-(q * (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)))).congr ?_
      filter_upwards with x
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (q * (x - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))) ∂(gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)))
        = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 * (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
      have hpt : ∫ x : ℝ, Real.exp (q * (x - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) ∂(gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)))
          = Real.exp (-(q * (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) * ∫ x : ℝ, Real.exp (q * x) ∂(gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [← Real.exp_add]
        congr 1
        ring
      have hge : ∫ x : ℝ, Real.exp (q * x) ∂(gaussianReal 0 (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) = Real.exp (q ^ 2 * (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) : ℝ) / 2) :=
        Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp q (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) : ℝ) (Real.toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)).2
      rw [hpt, hge]
      rw [Real.coe_toNNReal (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) hSnn, ← Real.exp_add]
      congr 1
      ring
    rw [h1, h2, h3]
  · intro g hg
    rw [hnu, MeasureTheory.lintegral_withDensity_eq_lintegral_mul mu hrho_meas hg]
    simp only [Pi.mul_apply, mul_comm]

  /- @proof-region region.target-node.session.444435b5fa80dd93 end -/

end Statlib.Imported
end

