import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_114927384_d5c2bee4_75a6a0a7
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1624330496_7a91811d_410d9a96
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2920011871_df380ed4_b3d7417b
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3480907983_5dd3c633_93bdea34
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
theorem statopia_math_node_1415516798_19cc68d1 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (Nc : ℕ) (theta2 : Fin Nc → ℝ) (C0th : (Fin Nc → ℝ) → U →L[ℝ] U)
    (hC0th_basis : ∀ k : ℕ, C0th theta2 (e k) = priorEigen lam Nc theta2 k • e k)
    (hC0th_expand : ∀ u : U,
      HasSum (fun k : ℕ => (priorEigen lam Nc theta2 k * inner ℝ (e k) u) • e k) (C0th theta2 u))
    (μ ν : Measure U) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (hnu_gauss : ProbabilityTheory.IsGaussian ν)
    (mUM mNU : U)
    (hmean_mu : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v mUM)
    (hmean_nu : ∀ v : U, ∫ u, inner ℝ v u ∂ν = inner ℝ v mNU)
    (hcov_mu : ∀ v w : U,
      ∫ u, (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM) ∂μ
        = inner ℝ v (C0th theta2 w))
    (hcov_nu : ∀ v w : U,
      ∫ u, (inner ℝ v u - inner ℝ v mNU) * (inner ℝ w u - inner ℝ w mNU) ∂ν
        = inner ℝ v (C0th theta2 w))
    (hint1_mu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2_mu : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ)
    (hint1_nu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) ν)
    (hint2_nu : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v mNU) * (inner ℝ w u - inner ℝ w mNU)) ν)
    (hsum : Summable (fun k : ℕ =>
      (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)),
    ∃ rho : U → ℝ≥0∞,
      Measurable rho ∧
      ν = μ.withDensity rho ∧
      ν.rnDeriv μ =ᵐ[μ] rho ∧
      (∀ q : ℝ, 0 < q →
        ∫⁻ u : U, ENNReal.rpow (rho u) q ∂μ
          = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
              (∑' k : ℕ,
                (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)))) ∧
      (∀ g : U → ℝ, Measurable g → (∀ u : U, 0 ≤ g u) →
        ∫ u : U, g u ∂ν = ∫ u : U, g u * (rho u).toReal ∂μ) := by
  /- @proof-region region.target-node.session.a8aef087681cb34f begin -/
  classical
  intro U hNACG hIPS hCS hSep hMeas hBorel e lam hlam_pos Nc theta2 C0th hC0th_basis hC0th_expand
    mu hmu_prob hmu_gauss nu hnu_prob hnu_gauss mUM mNU
    hmu_mean hnu_mean hcovmu hcovnu hmu_int1 hmu_int2 hnu_int1 hnu_int2 hsum
  haveI : IsProbabilityMeasure mu := hmu_gauss
  have hc : ∀ k : ℕ, 0 < priorEigen lam Nc theta2 k := by
    intro k
    unfold priorEigen
    split_ifs with h
    · exact Real.exp_pos _
    · exact hlam_pos k
  have hkl : ∀ k l : ℕ, inner ℝ (e k) (e l) = if k = l then (1 : ℝ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      have hn : ‖e k‖ = 1 := e.orthonormal.norm_eq_one k
      rw [hn]
      norm_num
    · rw [if_neg h]
      exact e.orthonormal.inner_eq_zero h
  have hcov_mu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) * (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂mu
        = if k = l then priorEigen lam Nc theta2 k else 0 := by
    intro k l
    rw [hcovmu (e k) (e l), hC0th_basis l, inner_smul_right, hkl k l]
    by_cases h : k = l
    · subst h
      simp
    · simp [h]
  have hcov_nu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mNU) * (inner ℝ (e l) u - inner ℝ (e l) mNU) ∂hmu_prob
        = if k = l then priorEigen lam Nc theta2 k else 0 := by
    intro k l
    rw [hcovnu (e k) (e l), hC0th_basis l, inner_smul_right, hkl k l]
    by_cases h : k = l
    · subst h
      simp
    · simp [h]
  obtain ⟨_, _, _, _, ρ, hρ_meas, hρ_lim, _, _, _, hρ_ae⟩ :=
    statopia_math_node_3664839893_07e7a1c0 U e (fun k : ℕ => priorEigen lam Nc theta2 k) hc
      mu hnu_prob hmu_prob hnu_gauss mUM mNU hmu_mean hnu_mean hcov_mu hcov_nu
      hmu_int1 hmu_int2 hnu_int1 hnu_int2 hsum
  obtain ⟨_, hdens, _, _, hrn⟩ :=
    statopia_math_node_1624330496_7a91811d U e (fun k : ℕ => priorEigen lam Nc theta2 k) hc
      mu hnu_prob hmu_prob hnu_gauss mUM mNU hmu_mean hnu_mean hcov_mu hcov_nu
      hmu_int1 hmu_int2 hnu_int1 hnu_int2 hsum ρ hρ_meas hρ_lim
  set Z : U → ℝ := fun u =>
    Real.log (ρ u).toReal +
      (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2
    with hZ_def
  have hZ_meas : Measurable Z := by
    have hlog : Measurable fun u : U => Real.log (ρ u).toReal :=
      Real.measurable_log.comp (ENNReal.measurable_toReal.comp hρ_meas)
    exact hlog.add measurable_const
  have hZ_ae : ∀ᵐ u ∂mu, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      (priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))
      atTop (𝓝 (Z u)) := by
    filter_upwards [hρ_ae] with u hu
    obtain ⟨x, hx, hρx, _⟩ := hu
    have hZx : Z u = x := by
      have hval : Z u = Real.log (ρ u).toReal +
          (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2 := by
        simp only [hZ_def]
      have h1 : (ρ u).toReal = Real.exp (x -
          (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2) := by
        rw [hρx, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      rw [hval, h1, Real.log_exp]
      ring
    rw [hZx]
    exact hx
  have hρ_ident : ∀ᵐ u ∂mu, ρ u = ENNReal.ofReal
      (Real.exp (Z u -
        (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2)) ∧
      ρ u ≠ ⊤ := by
    filter_upwards [hρ_ae] with u hu
    obtain ⟨x, hx, hρx, hne⟩ := hu
    have hZx : Z u = x := by
      have hval : Z u = Real.log (ρ u).toReal +
          (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2 := by
        simp only [hZ_def]
      have h1 : (ρ u).toReal = Real.exp (x -
          (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2) := by
        rw [hρx, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      rw [hval, h1, Real.log_exp]
      ring
    rw [hZx]
    exact ⟨hρx, hne⟩
  set v : ℕ → U := fun n =>
    ∑ k : {k : ℕ // k ∈ Finset.range n},
      ((priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM)) • e k with hv_def
  have hL : ∀ (n : ℕ) (u : U),
      (∑ k : {k : ℕ // k ∈ Finset.range n},
        ((priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM)) *
          (inner ℝ (e k) u - inner ℝ (e k) mUM))
        = inner ℝ (v n) u - inner ℝ (v n) mUM := by
    intro n u
    have h1 : inner ℝ (v n) u = ∑ k : {k : ℕ // k ∈ Finset.range n},
        ((priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM)) * inner ℝ (e k) u := by
      simp only [hv_def]
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [real_inner_smul_left]
    have h2 : inner ℝ (v n) mUM = ∑ k : {k : ℕ // k ∈ Finset.range n},
        ((priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM)) * inner ℝ (e k) mUM := by
      simp only [hv_def]
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [real_inner_smul_left]
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hgauss : ∀ n : ℕ,
      Measure.map (fun u : U =>
          ∑ k : {k : ℕ // k ∈ Finset.range n},
            ((priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM)) *
              (inner ℝ (e k) u - inner ℝ (e k) mUM)) mu
        = ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (∑ k : {k : ℕ // k ∈ Finset.range n},
              ((priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM)) ^ 2 *
                priorEigen lam Nc theta2 k)) := by
    intro n
    exact (statopia_math_node_114927384_d5c2bee4 U e
      (fun k : ℕ => priorEigen lam Nc theta2 k) hc mu hnu_prob mUM hmu_mean hcov_mu
      hmu_int1 hmu_int2).2 (Finset.range n)
      (fun k : {k : ℕ // k ∈ Finset.range n} =>
        (priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM))
  have hfnn : ∀ k : ℕ,
      0 ≤ (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 :=
    fun k => mul_nonneg (le_of_lt (inv_pos.mpr (hc k))) (sq_nonneg _)
  have hnorm_summable : Summable (fun k : ℕ =>
      ‖(priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2‖) := by
    have hfe : (fun k : ℕ =>
        ‖(priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2‖)
        = fun k : ℕ =>
          (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 :=
      funext (fun k => Real.norm_of_nonneg (hfnn k))
    rw [hfe]
    exact hsum
  have hvar : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) atTop
      (𝓝 (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) :=
    (hasSum_iff_tendsto_nat_of_summable_norm hnorm_summable).mp hsum.hasSum
  have hsigma2 : 0 ≤ ∑' k : ℕ,
      (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := by
    by_contra hneg
    have hlt : ∀ᶠ n : ℕ in atTop, (∑ k ∈ Finset.range n,
        (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2) < 0 :=
      (tendsto_order.mp hvar).2 0 (not_le.mp hneg)
    obtain ⟨n, hn⟩ := hlt.exists
    exact absurd hn (not_lt.mpr (Finset.sum_nonneg (fun k _ => hfnn k)))
  have hcov_tsum : ∀ v w : U,
      ∫ u, (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM) ∂mu
        = ∑' k : ℕ, priorEigen lam Nc theta2 k * inner ℝ (e k) v * inner ℝ (e k) w := by
    intro v w
    have hmap : inner ℝ v (∑' k : ℕ,
        (priorEigen lam Nc theta2 k * inner ℝ (e k) w) • e k)
        = ∑' k : ℕ, inner ℝ v ((priorEigen lam Nc theta2 k * inner ℝ (e k) w) • e k) :=
      (innerSL ℝ v).map_tsum (hC0th_expand w).summable
    rw [hcovmu v w, ← (hC0th_expand w).tsum_eq, hmap]
    refine tsum_congr (fun k => ?_)
    rw [inner_smul_right, real_inner_comm v (e k)]
    ring
  have hmom : ∀ q : ℝ, 0 < q →
      ∫⁻ u : U, ENNReal.rpow (ρ u) q ∂mu
        = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
            (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) := by
    intro q hq
    have hcand := statopia_math_node_2920011871_df380ed4 U e
      (fun k : ℕ => priorEigen lam Nc theta2 k) hc mu hnu_prob mUM mNU hmu_mean hcov_tsum
      hsum q hq
    have hcongr : ∫⁻ u : U, ENNReal.rpow (ρ u) q ∂mu
        = ∫⁻ u : U, ENNReal.rpow (ENNReal.ofReal (Real.exp
            (Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
              (priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM) *
                inner ℝ (e k) (u - mUM)) atTop
              - (∑' k : ℕ, (priorEigen lam Nc theta2 k)⁻¹ *
                  (inner ℝ (e k) (mNU - mUM)) ^ 2) / 2))) q ∂mu := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [hρ_ident, hZ_ae] with u hu hzu
      obtain ⟨hρu, -⟩ := hu
      have hlim : Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
          (priorEigen lam Nc theta2 k)⁻¹ * inner ℝ (e k) (mNU - mUM) *
            inner ℝ (e k) (u - mUM)) atTop = Z u :=
        Filter.Tendsto.limsup_eq hzu
      rw [hρu, hlim]
    rw [hcongr]
    exact hcand
  refine ⟨ρ, hρ_meas, hdens, hrn, ?_, ?_⟩
  · exact hmom
  · intro g hg hg0
    have hρ_lt : ∀ᵐ u ∂mu, ρ u < ⊤ := hρ_ident.mono (fun u hu => lt_top_iff_ne_top.mpr hu.2)
    rw [hdens]
    rw [integral_withDensity_eq_integral_toReal_smul (μ := mu) (f := ρ) hρ_meas hρ_lt g]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [smul_eq_mul, mul_comm]
  /- @proof-region region.target-node.session.a8aef087681cb34f end -/

end Statlib.Imported
end

