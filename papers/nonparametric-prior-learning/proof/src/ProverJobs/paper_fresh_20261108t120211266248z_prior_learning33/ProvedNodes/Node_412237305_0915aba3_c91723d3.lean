import Statlib.StatFoundation.Convergence.AnalysisTools.CramerWold
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_784943557_45aa83b0_5b793da1

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
theorem statopia_math_node_412237305_0915aba3 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hμ_gauss : ProbabilityTheory.IsGaussian μ)
    (mUM : U)
    (hmean_mu : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v mUM)
    (hcov_mu : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
        (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ = if k = l then c k else 0)
    (hint1_mu : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2_mu : ∀ v w : U,
      Integrable (fun u : U => (inner ℝ v u - inner ℝ v mUM) * (inner ℝ w u - inner ℝ w mUM)) μ),
    ProbabilityTheory.iIndepFun (fun (k : ℕ) (u : U) => inner ℝ (e k) (u - mUM)) μ ∧
      Measure.map (fun u : U => fun k : ℕ => inner ℝ (e k) (u - mUM)) μ =
        Measure.infinitePi (fun k : ℕ => gaussianReal 0 (Real.toNNReal (c k))) ∧
      (∀ k : ℕ, (∫ u, inner ℝ (e k) (u - mUM) ∂μ) = 0 ∧
        (∫ u, (inner ℝ (e k) (u - mUM)) ^ 2 ∂μ) = c k) ∧
      (∀ k l : ℕ, k ≠ l →
        (∫ u, (inner ℝ (e k) (u - mUM)) * (inner ℝ (e l) (u - mUM)) ∂μ) = 0) := by
  /- @proof-region region.target-node.session.9e077c6587862900 begin -/
  classical
  intro U _ _ _ _ _ _ e c hc μ _ hμ_gauss mUM hmean_mu hcov_mu hint1_mu hint2_mu
  have hdev : ∀ (k : ℕ) (u : U),
      inner ℝ (e k) (u - mUM) = inner ℝ (e k) u - inner ℝ (e k) mUM := by
    intro k u
    rw [inner_sub_right]
  have hmean0 : ∀ k : ℕ, (∫ u, inner ℝ (e k) (u - mUM) ∂μ) = 0 := by
    intro k
    have h1 : (∫ u, inner ℝ (e k) (u - mUM) ∂μ)
        = ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun u => hdev k u)
    rw [h1, integral_sub (hint1_mu (e k)) (integrable_const _), hmean_mu (e k)]
    simp
  have hsecond : ∀ k : ℕ, (∫ u, (inner ℝ (e k) (u - mUM)) ^ 2 ∂μ) = c k := by
    intro k
    have h := hcov_mu k k
    rw [if_pos rfl] at h
    have h1 : (∫ u, (inner ℝ (e k) (u - mUM)) ^ 2 ∂μ)
        = ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
            (inner ℝ (e k) u - inner ℝ (e k) mUM) ∂μ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [hdev k u, pow_two]
    rw [h1, h]
  have hcross : ∀ k l : ℕ, k ≠ l →
      (∫ u, (inner ℝ (e k) (u - mUM)) * (inner ℝ (e l) (u - mUM)) ∂μ) = 0 := by
    intro k l hkl
    have h := hcov_mu k l
    rw [if_neg hkl] at h
    have h1 : (∫ u, (inner ℝ (e k) (u - mUM)) * (inner ℝ (e l) (u - mUM)) ∂μ)
        = ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
            (inner ℝ (e l) u - inner ℝ (e l) mUM) ∂μ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [hdev k u, hdev l u]
    rw [h1, h]
  have hmeas : ∀ k : ℕ, Measurable (fun u : U => inner ℝ (e k) (u - mUM)) := by
    intro k
    exact (continuous_const.inner (continuous_id.sub continuous_const)).measurable
  have hvar : ∀ k : ℕ, Var[fun u : U => inner ℝ (e k) u; μ] = c k := by
    intro k
    have hlin : AEMeasurable (fun u : U => inner ℝ (e k) u) μ :=
      (continuous_const.inner continuous_id).measurable.aemeasurable
    rw [variance_eq_integral hlin]
    have h1 : (∫ u, (inner ℝ (e k) u - ∫ x, inner ℝ (e k) x ∂μ) ^ 2 ∂μ)
        = ∫ u, (inner ℝ (e k) u - inner ℝ (e k) mUM) *
            (inner ℝ (e k) u - inner ℝ (e k) mUM) ∂μ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [hmean_mu (e k), pow_two]
    rw [h1, hcov_mu k k, if_pos rfl]
  have hmarg : ∀ k : ℕ,
      Measure.map (fun u : U => inner ℝ (e k) (u - mUM)) μ =
        gaussianReal 0 (Real.toNNReal (c k)) := by
    intro k
    haveI : IsProbabilityMeasure (Measure.map (fun u : U => inner ℝ (e k) (u - mUM)) μ) :=
      Measure.isProbabilityMeasure_map (hmeas k).aemeasurable
    have hgauss : ProbabilityTheory.IsGaussian μ := hμ_gauss
    haveI : ProbabilityTheory.IsGaussian μ := hgauss
    refine Measure.ext_of_charFun ?_
    funext t
    have hmap_f : Measure.map (fun u : U => inner ℝ (e k) (u - mUM)) μ
        = Measure.map (fun x : ℝ => x + (-(inner ℝ (e k) mUM)))
            (Measure.map (⇑(innerSL ℝ (e k))) μ) := by
      rw [MeasureTheory.Measure.map_map]
      · congr 1
        funext u
        simp only [Function.comp_apply]
        rw [hdev k u]
        have h1 : ⇑(innerSL ℝ (e k)) u = inner ℝ (e k) u := by simp
        rw [h1]
        ring
      · simpa using (continuous_id.add continuous_const).measurable
      · exact (innerSL ℝ (e k)).continuous.measurable
    have hchar_map : charFun (Measure.map (fun u : U => inner ℝ (e k) (u - mUM)) μ) t
        = charFun μ (t • e k) *
            Complex.exp (↑(inner ℝ (-(inner ℝ (e k) mUM)) t) * Complex.I) := by
      rw [hmap_f, MeasureTheory.charFun_map_add_const,
        Statlib.StatFoundation.Convergence.CramerWold.charFun_map_innerSL]
    have hint_c : (∫ x : U, ((inner ℝ (t • e k) x : ℝ) : ℂ) ∂μ)
        = ((t * inner ℝ (e k) mUM : ℝ) : ℂ) := by
      have hreal : (∫ x : U, inner ℝ (t • e k) x ∂μ) = t * inner ℝ (e k) mUM := by
        have step1 : (∫ x : U, inner ℝ (t • e k) x ∂μ)
            = ∫ x : U, t * inner ℝ (e k) x ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [real_inner_smul_left]
        rw [step1, MeasureTheory.integral_const_mul, hmean_mu (e k)]
      have hcast :=
        integral_ofReal (𝕜 := ℂ) (μ := μ) (f := fun x : U => inner ℝ (t • e k) x)
      rw [hreal] at hcast
      exact hcast
    have hvar_c : Var[fun x : U => inner ℝ (t • e k) x; μ] = t ^ 2 * c k := by
      have h1 : (fun x : U => inner ℝ (t • e k) x) = fun x : U => t * inner ℝ (e k) x := by
        funext x
        rw [real_inner_smul_left]
      rw [h1, ProbabilityTheory.variance_const_mul, hvar k]
    have hinner_c : inner ℝ (-(inner ℝ (e k) mUM)) t = -(inner ℝ (e k) mUM) * t := by
      simpa using real_inner_smul_left (x := (1 : ℝ)) (y := t) (r := -(inner ℝ (e k) mUM))
    have hgauss_char : charFun μ (t • e k)
        = Complex.exp ((↑(t * inner ℝ (e k) mUM) : ℂ) * Complex.I - ↑(t ^ 2 * c k) / 2) := by
      have h := ProbabilityTheory.IsGaussian.charFun_eq (μ := μ) (t • e k)
      rw [h]
      simp only [hint_c, hvar_c]
    have hcc : ((Real.toNNReal (c k) : NNReal) : ℂ) = ((c k : ℝ) : ℂ) := by
      exact_mod_cast Real.coe_toNNReal (c k) (le_of_lt (hc k))
    rw [hchar_map, hgauss_char, ProbabilityTheory.charFun_gaussianReal, hinner_c, hcc,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hjoint : Measure.map (fun u : U => fun k : ℕ => inner ℝ (e k) (u - mUM)) μ
      = Measure.infinitePi (fun k : ℕ => gaussianReal 0 (Real.toNNReal (c k))) := by
    exact statopia_math_node_784943557_45aa83b0 U e c hc μ hμ_gauss mUM hmean_mu hcov_mu
      hint1_mu hint2_mu
  have hindep : ProbabilityTheory.iIndepFun (fun (k : ℕ) (u : U) => inner ℝ (e k) (u - mUM)) μ := by
    rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map hmeas]
    rw [hjoint]
    simp only [hmarg]
  exact ⟨hindep, hjoint, fun k => ⟨hmean0 k, hsecond k⟩, hcross⟩
  /- @proof-region region.target-node.session.9e077c6587862900 end -/

end Statlib.Imported
end

