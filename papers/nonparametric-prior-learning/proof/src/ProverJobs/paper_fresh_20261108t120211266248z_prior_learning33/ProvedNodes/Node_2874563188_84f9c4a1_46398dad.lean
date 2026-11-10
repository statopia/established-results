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
theorem statopia_math_node_2874563188_84f9c4a1 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu : Measure U) [IsProbabilityMeasure mu]
    (hmu_gauss : ProbabilityTheory.IsGaussian mu) (m_mu m_nu : U)
    (hmu_mean : ∀ v : U, (∫ u, inner ℝ v u ∂mu) = inner ℝ v m_mu)
    (hmu_cov : ∀ v w : U,
      (∫ u, (inner ℝ v u - inner ℝ v m_mu) * (inner ℝ w u - inner ℝ w m_mu) ∂mu)
        = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) w)
    (t : ℝ) (N : ℕ),
    (∫ u, Complex.exp
        (↑(t * ∑ k ∈ Finset.range N,
            (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)) * Complex.I) ∂mu)
      = Complex.exp
          (-(↑(t ^ 2 * ∑ k ∈ Finset.range N, c k * ((c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)) ^ 2)) / 2) := by
  /- @proof-region region.target-node.session.d5eb2a4d3a670e3a begin -/
  intro U _ _ _ _ _ _ e c hc_pos mu _ hmu_gauss m_mu m_nu hmu_mean hmu_cov t N
  set a : ℕ → ℝ := fun k => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) with ha
  haveI : ProbabilityTheory.IsGaussian mu := hmu_gauss
  haveI : SecondCountableTopology U := inferInstance
  set w : U := ∑ k ∈ Finset.range N, (t * a k) • e k with hw
  have hinner : ∀ u : U, inner ℝ w (u - m_mu)
      = t * ∑ k ∈ Finset.range N, a k * inner ℝ (e k) (u - m_mu) := by
    intro u
    rw [hw, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left]
    ring
  have hmemLp : MeasureTheory.MemLp (id : U → U) 2 mu := ProbabilityTheory.IsGaussian.memLp_two_id
  have hmean : (∫ x : U, id x ∂mu) = m_mu := by
    refine ext_inner_left ℝ fun v => ?_
    have hdual : (∫ x : U, inner ℝ v x ∂mu) = inner ℝ v (∫ x : U, id x ∂mu) := by
      simpa using ProbabilityTheory.IsGaussian.integral_dual (μ := mu) (innerSL ℝ v)
    rw [← hdual, hmu_mean v]
  have hchar : ∀ v : U, charFun mu v
      = Complex.exp (↑(inner ℝ v m_mu) * Complex.I - ↑(((ProbabilityTheory.covarianceBilin mu) v) v) / 2) := by
    intro v
    rw [ProbabilityTheory.IsGaussian.charFun_eq', hmean]
  have hcov : ∀ v : U, ((ProbabilityTheory.covarianceBilin mu) v) v
      = ∑' k : ℕ, c k * inner ℝ (e k) v * inner ℝ (e k) v := by
    intro v
    rw [ProbabilityTheory.covarianceBilin_apply hmemLp v v]
    simp only [hmean, inner_sub_right]
    rw [← hmu_cov v v]
  have hCharFunW : (∫ u, Complex.exp (↑(inner ℝ w u) * Complex.I) ∂mu) = charFun mu w := by
    rw [MeasureTheory.charFun_eq_integral_innerProbChar]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    rw [BoundedContinuousFunction.innerProbChar_apply, real_inner_comm w u]
  have hpt : ∀ u : U, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I)
      = Complex.exp (↑(inner ℝ w u) * Complex.I) * Complex.exp (-(↑(inner ℝ w m_mu) * Complex.I)) := by
    intro u
    rw [inner_sub_right, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hstep2 : (∫ u, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I) ∂mu)
      = Complex.exp (-(↑(((ProbabilityTheory.covarianceBilin mu) w) w)) / 2) := by
    have h1 : (∫ u, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I) ∂mu)
        = (∫ u, Complex.exp (↑(inner ℝ w u) * Complex.I) ∂mu) * Complex.exp (-(↑(inner ℝ w m_mu) * Complex.I)) := by
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with u using hpt u
    rw [h1, hCharFunW, hchar w, ← Complex.exp_add]
    congr 1
    ring
  have hw_e : ∀ k : ℕ, inner ℝ (e k) w = if k ∈ Finset.range N then t * a k else 0 := by
    intro k
    rw [hw, inner_sum]
    have hstep : ∀ k' : ℕ, inner ℝ (e k) ((t * a k') • e k')
        = if k = k' then t * a k' else 0 := by
      intro k'
      rw [real_inner_smul_right, orthonormal_iff_ite.mp e.orthonormal k k', mul_ite]
      simp
    calc ∑ k' ∈ Finset.range N, inner ℝ (e k) ((t * a k') • e k')
        = ∑ k' ∈ Finset.range N, (if k = k' then t * a k' else 0) := by
          exact Finset.sum_congr rfl fun k' _ => hstep k'
      _ = if k ∈ Finset.range N then t * a k else 0 := by
          rw [Finset.sum_ite_eq]
  have hTsum : ∑' k : ℕ, c k * inner ℝ (e k) w * inner ℝ (e k) w = t ^ 2 * ∑ k ∈ Finset.range N, c k * (a k) ^ 2 := by
    have hterm : ∀ k : ℕ, c k * inner ℝ (e k) w * inner ℝ (e k) w
        = if k ∈ Finset.range N then c k * (t * a k) ^ 2 else 0 := by
      intro k
      rw [hw_e k]
      by_cases hk : k ∈ Finset.range N
      · rw [if_pos hk, if_pos hk]; ring
      · rw [if_neg hk, if_neg hk]; ring
    calc ∑' k : ℕ, c k * inner ℝ (e k) w * inner ℝ (e k) w
        = ∑' k : ℕ, (if k ∈ Finset.range N then c k * (t * a k) ^ 2 else 0) := tsum_congr hterm
      _ = ∑ k ∈ Finset.range N, (if k ∈ Finset.range N then c k * (t * a k) ^ 2 else 0) := by
          rw [tsum_eq_sum]
          intro k hk
          rw [if_neg hk]
      _ = ∑ k ∈ Finset.range N, c k * (t * a k) ^ 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [if_pos hk]
      _ = t ^ 2 * ∑ k ∈ Finset.range N, c k * (a k) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  have hL : (∫ u, Complex.exp (↑(t * ∑ k ∈ Finset.range N, a k * inner ℝ (e k) (u - m_mu)) * Complex.I) ∂mu)
      = ∫ u, Complex.exp (↑(inner ℝ w (u - m_mu)) * Complex.I) ∂mu := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    rw [hinner u]
  rw [hL, hstep2, hcov w, hTsum]

  /- @proof-region region.target-node.session.d5eb2a4d3a670e3a end -/

end Statlib.Imported
end

