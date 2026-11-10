import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3039133055_9a199646_833aaefb
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3147937759_08d5a7be_97776da1
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_488254885_6df2d178_79332d6b

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
theorem statopia_math_node_659555420_43074f04 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
    ∀ᵐ u ∂mu, ∃ L : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.range n,
          (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
        atTop (𝓝 L) := by
  /- @proof-region region.target-node.session.e9a290fe2644cc1e begin -/
  intro U instN instI instC instS instM instB e c hc_pos mu instP hmu_gauss m_mu m_nu
    hmu_mean hmu_cov hsigma2
  haveI hgauss : ProbabilityTheory.IsGaussian mu := hmu_gauss
  set a : ℕ → ℝ := fun k => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) with ha
  have hvar : Summable (fun k => (a k) ^ 2 * c k) := by
    refine hsigma2.congr (fun k => ?_)
    simp only [ha]
    have hck : c k ≠ 0 := ne_of_gt (hc_pos k)
    field_simp
  let Y : ℕ → U → ℝ := fun k u => a k * (inner ℝ (e k) u - inner ℝ (e k) m_mu)
  have hmeas : ∀ k, Measurable (Y k) := by
    intro k
    show Measurable (fun u => a k * (inner ℝ (e k) u - inner ℝ (e k) m_mu))
    measurability
  have hindep : iIndepFun Y mu := by
    have hindepZ : iIndepFun (fun k : ℕ => fun u : U => inner ℝ (e k) u) mu :=
      statopia_math_node_3039133055_9a199646 U mu
        (fun k : ℕ => fun u : U => inner ℝ (e k) u)
        (fun i : ℕ => ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩)
        (fun i => inferInstance)
        (fun i => by measurability)
        (fun n => statopia_math_node_488254885_6df2d178 U e c hc_pos mu hmu_gauss m_mu hmu_mean hmu_cov n)
    have hg : ∀ k : ℕ, Measurable (fun x : ℝ => a k * (x - inner ℝ (e k) m_mu)) :=
      fun k => by measurability
    have hcomp := hindepZ.comp (fun k (x : ℝ) => a k * (x - inner ℝ (e k) m_mu)) hg
    simpa only [Y, Function.comp] using hcomp
  have hmean : ∀ k, (∫ u, Y k u ∂mu) = 0 := by
    intro k
    have hY : Y k = fun u => a k * (inner ℝ (e k) u - inner ℝ (e k) m_mu) := rfl
    rw [hY, integral_const_mul]
    have hZ : MemLp (fun u : U => inner ℝ (e k) u) 2 mu :=
      (IsGaussian.memLp_two_id (μ := mu)).const_inner (e k)
    have hf : Integrable (fun u : U => inner ℝ (e k) u) mu :=
      MemLp.integrable (q := 2) (by norm_num) hZ
    have hg : Integrable (fun _ : U => inner ℝ (e k) m_mu) mu := integrable_const _
    have h1 : (∫ u : U, inner ℝ (e k) u ∂mu) = inner ℝ (e k) m_mu := hmu_mean (e k)
    have h2 : (∫ _ : U, inner ℝ (e k) m_mu ∂mu) = inner ℝ (e k) m_mu := by simp
    rw [integral_sub hf hg, h1, h2]
    ring
  have hmemLp : ∀ k, MemLp (Y k) 2 mu := by
    intro k
    have hZ : MemLp (fun u : U => inner ℝ (e k) u) 2 mu :=
      (IsGaussian.memLp_two_id (μ := mu)).const_inner (e k)
    have h2 : MemLp (fun u : U => inner ℝ (e k) u - inner ℝ (e k) m_mu) 2 mu :=
      hZ.sub (memLp_const (inner ℝ (e k) m_mu))
    exact h2.const_mul (a k)
  have hsumm : Summable (fun k => ∫ u, (Y k u) ^ 2 ∂mu) := by
    have hvX : ∀ k, (∫ u, (inner ℝ (e k) u - inner ℝ (e k) m_mu) ^ 2 ∂mu) = c k := by
      intro k
      have hcov := hmu_cov (e k) (e k)
      have hcongr : (∫ u, (inner ℝ (e k) u - inner ℝ (e k) m_mu) ^ 2 ∂mu)
          = ∫ u, (inner ℝ (e k) u - inner ℝ (e k) m_mu) * (inner ℝ (e k) u - inner ℝ (e k) m_mu) ∂mu := by
        simp only [pow_two]
      rw [hcongr, hcov]
      have hpt : ∀ k', c k' * inner ℝ (e k') (e k) * inner ℝ (e k') (e k) = if k' = k then c k else 0 := by
        intro k'
        by_cases h : k' = k
        · rw [h, if_pos rfl]
          have h1 : inner ℝ (e k) (e k) = 1 := by
            rw [real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one k]; norm_num
          rw [h1]; ring
        · have hik0 : inner ℝ (e k') (e k) = 0 := e.orthonormal.inner_eq_zero h
          rw [if_neg h, hik0]; ring
      rw [tsum_congr hpt, tsum_eq_single k (fun b hb => by rw [if_neg hb]), if_pos rfl]
    refine hvar.congr (fun k => ?_)
    have hYsq : (fun u => (Y k u) ^ 2) = fun u => (a k) ^ 2 * (inner ℝ (e k) u - inner ℝ (e k) m_mu) ^ 2 := by
      funext u
      show (a k * (inner ℝ (e k) u - inner ℝ (e k) m_mu)) ^ 2
        = (a k) ^ 2 * (inner ℝ (e k) u - inner ℝ (e k) m_mu) ^ 2
      ring
    rw [hYsq, integral_const_mul, hvX k]
  have hconv := statopia_math_node_3147937759_08d5a7be U mu Y hmeas hindep hmean hmemLp hsumm
  simpa [Y, ha, inner_sub_right] using hconv
  /- @proof-region region.target-node.session.e9a290fe2644cc1e end -/

end Statlib.Imported
end

