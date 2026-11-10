import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_744484935_68a4c774_8f753d90

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
theorem statopia_math_node_376187579_6cbc376f : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (lam : ℕ → ℝ) (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (Nc : ℕ) (θ2 : Fin Nc → ℝ)
    (C0th : U →L[ℝ] U)
    (hC0th_expand : ∀ u : U,
      HasSum (fun k : ℕ => (priorEigen lam Nc θ2 k * inner ℝ (e k) u) • e k) (C0th u))
    (P Q : Measure U) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP_gauss : ProbabilityTheory.IsGaussian P)
    (hQ_gauss : ProbabilityTheory.IsGaussian Q)
    (mP mQ : U)
    (hP_mean : ∀ v : U, (∫ u, inner ℝ v u ∂P) = inner ℝ v mP)
    (hQ_mean : ∀ v : U, (∫ u, inner ℝ v u ∂Q) = inner ℝ v mQ)
    (hP_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v mP) * (inner ℝ w u - inner ℝ w mP) ∂P)
        = inner ℝ v (C0th w))
    (hQ_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v mQ) * (inner ℝ w u - inner ℝ w mQ) ∂Q)
        = inner ℝ v (C0th w))
    (hP_int1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) P)
    (hQ_int1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) Q)
    (hP_int2 : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mP) * (inner ℝ w u - inner ℝ w mP)) P)
    (hQ_int2 : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mQ) * (inner ℝ w u - inner ℝ w mQ)) Q)
    (hsigma2 : Summable (fun k : ℕ =>
      (priorEigen lam Nc θ2 k)⁻¹ * (inner ℝ (e k) (mQ - mP)) ^ 2)),
    let rho : U → ℝ≥0∞ := fun u : U =>
      ENNReal.ofReal (Real.exp
        ((Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
            (priorEigen lam Nc θ2 k)⁻¹ * inner ℝ (e k) (mQ - mP)
              * inner ℝ (e k) (u - mP)) Filter.atTop)
          - (∑' k : ℕ, (priorEigen lam Nc θ2 k)⁻¹ * (inner ℝ (e k) (mQ - mP)) ^ 2) / 2))
    Q = P.withDensity rho ∧
      (∀ q : ℝ, 0 < q →
        (∫⁻ u : U, ENNReal.rpow (rho u) q ∂P)
          = ENNReal.ofReal (Real.exp (q * (q - 1) / 2 *
              (∑' k : ℕ, (priorEigen lam Nc θ2 k)⁻¹ * (inner ℝ (e k) (mQ - mP)) ^ 2)))) ∧
      (∫⁻ u : U, rho u ∂P) = 1 ∧
      (∫⁻ u : U, ENNReal.rpow (rho u) (2 : ℝ) ∂P)
        = ENNReal.ofReal (Real.exp (∑' k : ℕ,
            (priorEigen lam Nc θ2 k)⁻¹ * (inner ℝ (e k) (mQ - mP)) ^ 2)) ∧
      (∀ g : U → ℝ, Measurable g → (∀ u : U, 0 ≤ g u) →
        (∫ u, g u ∂Q) = ∫ u, g u * (rho u).toReal ∂P) ∧
      Measure.AbsolutelyContinuous Q P ∧
      Q.rnDeriv P =ᵐ[P] rho := by
  /- @proof-region region.target-node.session.e86e610349a93b1b begin -/
  intro U _ _ _ _ _ _ e lam hlam_pos Nc θ2 C0th hC0th_expand P Q _ _ hP_gauss hQ_gauss
    mP mQ hP_mean hQ_mean hP_cov hQ_cov hP_int1 hQ_int1 hP_int2 hQ_int2 hsigma2
  have hc_pos : ∀ k : ℕ, 0 < priorEigen lam Nc θ2 k := by
    intro k
    simp only [priorEigen]
    split_ifs with hk
    · exact Real.exp_pos _
    · exact hlam_pos k
  have hstep1 : ∀ v w : U,
      inner ℝ v (C0th w) = ∑' k : ℕ, priorEigen lam Nc θ2 k * inner ℝ (e k) v * inner ℝ (e k) w := by
    intro v w
    have h := ContinuousLinearMap.hasSum (innerSL ℝ v) (hC0th_expand w)
    have hinner : ∀ x : U, (innerSL ℝ v) x = inner ℝ v x := fun x => by simp
    have hterm : ∀ k : ℕ, (innerSL ℝ v) ((priorEigen lam Nc θ2 k * inner ℝ (e k) w) • e k)
        = priorEigen lam Nc θ2 k * inner ℝ (e k) v * inner ℝ (e k) w := by
      intro k
      rw [hinner, real_inner_smul_right, real_inner_comm v (e k)]
      ring
    rw [(hinner (C0th w)).symm, h.tsum_eq.symm]
    exact tsum_congr hterm
  have hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v mP) * (inner ℝ w u - inner ℝ w mP) ∂P)
        = ∑' k : ℕ, priorEigen lam Nc θ2 k * inner ℝ (e k) v * inner ℝ (e k) w := by
    intro v w
    rw [hP_cov v w]
    exact hstep1 v w
  have hnu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v mQ) * (inner ℝ w u - inner ℝ w mQ) ∂Q)
        = ∑' k : ℕ, priorEigen lam Nc θ2 k * inner ℝ (e k) v * inner ℝ (e k) w := by
    intro v w
    rw [hQ_cov v w]
    exact hstep1 v w
  obtain ⟨ρ, hρ_meas, hQ_eq_ρ, hρ_ae, _, _, hLq, hint1, hint2, _⟩ :=
    statopia_math_node_744484935_68a4c774 U e (fun k => priorEigen lam Nc θ2 k) hc_pos P Q
      hP_gauss hQ_gauss mP mQ hP_mean hQ_mean hmu_cov hnu_cov hP_int1 hQ_int1 hP_int2 hQ_int2 hsigma2
  have hρ_goal : ρ =ᵐ[P] (fun u : U => ENNReal.ofReal (Real.exp
      (Filter.limsup (fun n : ℕ => ∑ k ∈ Finset.range n,
          (priorEigen lam Nc θ2 k)⁻¹ * inner ℝ (e k) (mQ - mP) * inner ℝ (e k) (u - mP))
        Filter.atTop
        - (∑' k : ℕ, (priorEigen lam Nc θ2 k)⁻¹ * (inner ℝ (e k) (mQ - mP)) ^ 2) / 2))) :=
    hρ_ae
  have hfinρ : ∀ᵐ u ∂P, ρ u < ⊤ := by
    filter_upwards [hρ_goal] with u hu
    rw [hu]
    exact ENNReal.ofReal_lt_top
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hQ_eq_ρ.trans (MeasureTheory.withDensity_congr_ae hρ_goal)
  · intro q hq
    refine Eq.trans ?_ (hLq q hq)
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hρ_goal.symm] with u hu
    rw [hu]
  · refine Eq.trans ?_ hint1
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hρ_goal.symm] with u hu
    rw [hu]
  · refine Eq.trans ?_ hint2
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hρ_goal.symm] with u hu
    rw [hu]
  · intro g _ _
    rw [hQ_eq_ρ]
    rw [integral_withDensity_eq_integral_toReal_smul (μ := P) (f := ρ) hρ_meas hfinρ g]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hρ_goal] with u hu
    rw [hu, smul_eq_mul, mul_comm]
  · rw [hQ_eq_ρ]
    exact MeasureTheory.withDensity_absolutelyContinuous P ρ
  · rw [hQ_eq_ρ]
    exact (MeasureTheory.Measure.rnDeriv_withDensity P hρ_meas).trans hρ_goal
  /- @proof-region region.target-node.session.e86e610349a93b1b end -/

end Statlib.Imported
end

