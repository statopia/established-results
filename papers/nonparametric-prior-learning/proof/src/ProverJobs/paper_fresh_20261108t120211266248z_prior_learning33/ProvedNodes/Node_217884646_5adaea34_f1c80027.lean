import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2874563188_84f9c4a1_46398dad

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
theorem statopia_math_node_217884646_5adaea34 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu : Measure U) [IsProbabilityMeasure mu]
    (hmu_gauss : ProbabilityTheory.IsGaussian mu) (m_mu m_nu : U)
    (hmu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂mu) = inner ℝ v m_mu)
    (hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_mu) * (inner ℝ w u - inner ℝ w m_mu) ∂mu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (hsigma2 : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))
    (hae : ∀ᵐ u ∂mu, ∃ L : ℝ,
      Filter.Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        Filter.atTop (nhds L))
    (hmeas : Measurable (fun u : U =>
      Filter.limsup
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        Filter.atTop))
    (v : NNReal)
    (hv : (v : ℝ) = ∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2),
    MeasureTheory.Measure.map (fun u : U =>
      Filter.limsup
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        Filter.atTop) mu = ProbabilityTheory.gaussianReal 0 v := by
  /- @proof-region region.target-node.session.cbcb605cdd05ab0c begin -/
  intro U _ _ _ _ _ _ e c hc_pos mu _ hmu_gauss m_mu m_nu hmu_mean hmu_cov hsigma2 hae hmeas v hv
  haveI : IsGaussian mu := hmu_gauss
  haveI : SecondCountableTopology U := inferInstance
  have hM2 : MemLp (fun u : U => u) 2 mu := IsGaussian.memLp_two_id (μ := mu)
  have hI1 : Integrable (fun u : U => u) mu := hM2.integrable (by norm_num)
  have hIinner : ∀ w : U, Integrable (fun u : U => inner ℝ w u) mu :=
    fun w => (innerSL ℝ w).integrable_comp hI1
  have hid : ∫ u, id u ∂mu = m_mu := by
    refine ext_inner_left ℝ (fun w => ?_)
    change (innerSL ℝ w) (∫ u, u ∂mu) = inner ℝ w m_mu
    have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ w) hI1
    rw [← h]
    simpa only [innerSL_apply_apply] using hmu_mean w
  have hcov : ∀ w : U,
      ((covarianceBilin mu) w) w = ∫ u, (inner ℝ w u - inner ℝ w m_mu) ^ 2 ∂mu := by
    intro w
    have hcoe : (⇑((InnerProductSpace.toDualMap ℝ U) w)) = fun u : U => inner ℝ w u := by
      show (⇑((innerSL ℝ) w)) = fun u : U => inner ℝ w u
      exact coe_innerSL_apply ℝ w
    have hL : ((covarianceBilin mu) w) w
        = variance (⇑((InnerProductSpace.toDualMap ℝ U) w)) mu := by
      rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_self_eq_variance hM2]
    rw [hL, hcoe, variance_eq_integral (X := fun u : U => inner ℝ w u) (by fun_prop)]
    simp only [hmu_mean w]
  have hcf : ∀ w : U,
      charFun mu w
        = Complex.exp (↑(inner ℝ w m_mu) * Complex.I - ↑(((covarianceBilin mu) w) w) / 2) := by
    intro w
    rw [IsGaussian.charFun_eq' (μ := mu) w, hid, hcov w]
  let a : ℕ → ℝ := fun k => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)
  let S : ℕ → U → ℝ := fun n u => ∑ k ∈ Finset.range n, a k * inner ℝ (e k) (u - m_mu)
  let Z : U → ℝ := fun u => limsup (fun n => S n u) atTop
  have hZmeas : Measurable Z := hmeas
  have haeT : ∀ᵐ u ∂mu, Tendsto (fun n => S n u) atTop (nhds (Z u)) := by
    filter_upwards [hae] with u hu
    obtain ⟨L, hL⟩ := hu
    have hlim : Z u = L := hL.limsup_eq
    rw [hlim]
    exact hL
  have hchar0 : ∀ w : U,
      (∫ u, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I) ∂mu)
        = Complex.exp (-(↑(((covarianceBilin mu) w) w)) / 2) := by
    intro w
    have hpt : ∀ u : U, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I)
        = Complex.exp (-(↑(inner ℝ w m_mu) * Complex.I))
          * Complex.exp (↑(inner ℝ w u) * Complex.I) := by
      intro u
      rw [← Complex.exp_add]
      congr 1
      rw [inner_sub_right, Complex.ofReal_sub]
      ring
    calc (∫ u, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I) ∂mu)
        = ∫ u, Complex.exp (-(↑(inner ℝ w m_mu) * Complex.I))
            * Complex.exp (↑(inner ℝ w u) * Complex.I) ∂mu := by
          simp only [hpt]
      _ = Complex.exp (-(↑(inner ℝ w m_mu) * Complex.I))
            * ∫ u, Complex.exp (↑(inner ℝ w u) * Complex.I) ∂mu := by
          rw [integral_const_mul]
      _ = Complex.exp (-(↑(inner ℝ w m_mu) * Complex.I)) * charFun mu w := by
          have hch : (∫ u, Complex.exp (↑(inner ℝ w u) * Complex.I) ∂mu) = charFun mu w := by
            unfold charFun
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with u
            first | rfl | rw [real_inner_comm]
          rw [hch]
      _ = Complex.exp (-(↑(((covarianceBilin mu) w) w)) / 2) := by
          rw [hcf w, ← Complex.exp_add]
          congr 1
          ring
  have hterm : ∀ k : ℕ, c k * (a k) ^ 2 = (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2 := by
    intro k
    have hne : c k ≠ 0 := ne_of_gt (hc_pos k)
    show c k * ((c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)) ^ 2
        = (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2
    field_simp
  have hsum_a : Summable (fun k : ℕ => c k * (a k) ^ 2) := by
    simpa only [hterm] using hsigma2
  have hv2 : (v : ℝ) = ∑' k : ℕ, c k * (a k) ^ 2 := by
    rw [hv]
    exact tsum_congr (fun k => (hterm k).symm)
  have hpar : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, c k * (a k) ^ 2) atTop
      (nhds ((v : ℝ))) := by
    rw [hv2]
    exact (hasSum_iff_tendsto_nat_of_nonneg (f := fun k : ℕ => c k * (a k) ^ 2)
      (fun k => mul_nonneg (le_of_lt (hc_pos k)) (sq_nonneg (a k))) _).mp hsum_a.hasSum
  have hstep : ∀ (t : ℝ) (N : ℕ),
      (∫ u, Complex.exp (↑(t * S N u) * Complex.I) ∂mu)
        = Complex.exp (-(↑(t ^ 2 * ∑ k ∈ Finset.range N, c k * (a k) ^ 2)) / 2) := by
    intro t N
    exact statopia_math_node_2874563188_84f9c4a1 U e c hc_pos mu hmu_gauss m_mu m_nu hmu_mean
      hmu_cov t N
  have hmain : ∀ t : ℝ,
      (∫ u, Complex.exp (↑(t * Z u) * Complex.I) ∂mu)
        = Complex.exp (-(↑(t ^ 2 * (v : ℝ))) / 2) := by
    intro t
    have hexp : Tendsto
        (fun N : ℕ => Complex.exp (-(↑(t ^ 2 * ∑ k ∈ Finset.range N, c k * (a k) ^ 2)) / 2))
        atTop (nhds (Complex.exp (-(↑(t ^ 2 * (v : ℝ))) / 2))) := by
      have hlim : Tendsto (fun N : ℕ => t ^ 2 * ∑ k ∈ Finset.range N, c k * (a k) ^ 2) atTop
          (nhds (t ^ 2 * (v : ℝ))) := hpar.const_mul (t ^ 2)
      have hf : Continuous fun x : ℝ => Complex.exp (-(↑x : ℂ) / 2) := by fun_prop
      exact Filter.Tendsto.comp (g := fun x : ℝ => Complex.exp (-(↑x : ℂ) / 2))
        (f := fun N : ℕ => t ^ 2 * ∑ k ∈ Finset.range N, c k * (a k) ^ 2)
        (hf.tendsto (t ^ 2 * (v : ℝ))) hlim
    have hdct : Tendsto (fun N : ℕ => ∫ u, Complex.exp (↑(t * S N u) * Complex.I) ∂mu)
        atTop (nhds (∫ u, Complex.exp (↑(t * Z u) * Complex.I) ∂mu)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun _ : U => (1 : ℝ)) ?_ ?_ ?_ ?_
      · intro N
        have h1 : Measurable fun u : U => t * S N u := by
          show Measurable fun u : U =>
            t * ∑ k ∈ Finset.range N, a k * inner ℝ (e k) (u - m_mu)
          fun_prop
        have h2 : Measurable fun u : U => Complex.exp (↑(t * S N u) * Complex.I) := by
          have h3 : Measurable fun u : U => (↑(t * S N u) : ℂ) := h1.complex_ofReal
          exact Complex.continuous_exp.measurable.comp (h3.mul_const Complex.I)
        exact h2.stronglyMeasurable.aestronglyMeasurable
      · exact MeasureTheory.integrable_const 1
      · intro N
        filter_upwards with u
        simpa using (Complex.norm_exp_ofReal_mul_I (t * S N u)).le
      · filter_upwards [haeT] with u hu
        have h1 : Tendsto (fun n : ℕ => t * S n u) atTop (nhds (t * Z u)) := hu.const_mul t
        have h2 : Continuous fun x : ℝ => Complex.exp (↑x * Complex.I) := by fun_prop
        exact (h2.tendsto (t * Z u)).comp h1
    have hexp' : Tendsto (fun N : ℕ => ∫ u, Complex.exp (↑(t * S N u) * Complex.I) ∂mu)
        atTop (nhds (Complex.exp (-(↑(t ^ 2 * (v : ℝ))) / 2))) :=
      hexp.congr (fun N => (hstep t N).symm)
    exact tendsto_nhds_unique hdct hexp'
  haveI : IsFiniteMeasure (Measure.map Z mu) := inferInstance
  have hgauss : charFun (gaussianReal 0 v)
      = fun t : ℝ => Complex.exp (-(↑(t ^ 2 * (v : ℝ))) / 2) := by
    funext t
    rw [ProbabilityTheory.charFun_gaussianReal]
    congr 1
    simp only [Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have hcharZ : charFun (Measure.map Z mu)
      = fun t : ℝ => Complex.exp (-(↑(t ^ 2 * (v : ℝ))) / 2) := by
    funext t
    have hmap : charFun (Measure.map Z mu) t
        = ∫ u, Complex.exp (↑(t * Z u) * Complex.I) ∂mu := by
      unfold charFun
      rw [MeasureTheory.integral_map hZmeas.aemeasurable
        ((by fun_prop : Continuous fun x : ℝ => Complex.exp (↑(inner ℝ x t) * Complex.I))
          |>.stronglyMeasurable.aestronglyMeasurable)]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with u
      have hin : inner ℝ (Z u) t = t * Z u := by
        first
          | rfl
          | (rw [real_inner_comm]; rfl)
      rw [hin]
    rw [hmap]
    exact hmain t
  have hlaw : Measure.map Z mu = gaussianReal 0 v := by
    refine MeasureTheory.Measure.ext_of_charFun ?_
    rw [hcharZ, hgauss]
  exact hlaw
  /- @proof-region region.target-node.session.cbcb605cdd05ab0c end -/

end Statlib.Imported
end

