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
theorem statopia_math_node_3186299420_34298c40 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ]
    (hmu_gauss : ProbabilityTheory.IsGaussian μ)
    (m : U)
    (hmean : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v m)
    (hcov_diag : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) m) * (inner ℝ (e l) u - inner ℝ (e l) m) ∂μ
        = if k = l then c k else 0)
    (hint1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2 : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v m) * (inner ℝ w u - inner ℝ w m)) μ)
    (k : ℕ),
    Measure.map (fun u : U => inner ℝ (e k) u) μ
      = gaussianReal (inner ℝ (e k) m) (Real.toNNReal (c k)) := by
  /- @proof-region region.target-node.session.f08754575259aa72 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss m hmean hcov_diag hint1 hint2 k
  haveI : ProbabilityTheory.IsGaussian μ := hmu_gauss
  have hcoe : ⇑(innerSL ℝ (e k) : U →L[ℝ] ℝ) = fun u : U => inner ℝ (e k) u :=
    coe_innerSL_apply ℝ (e k)
  have hcont : Continuous fun u : U => inner ℝ (e k) u := by
    have h := (innerSL ℝ (e k)).continuous
    rwa [hcoe] at h
  have hν : ProbabilityTheory.IsGaussian (Measure.map (fun u : U => inner ℝ (e k) u) μ) := by
    have h := ProbabilityTheory.isGaussian_map (μ := μ) (innerSL ℝ (e k))
    rwa [hcoe] at h
  have hmean_id : ∫ x : ℝ, id x ∂(Measure.map (fun u : U => inner ℝ (e k) u) μ)
      = inner ℝ (e k) m := by
    rw [MeasureTheory.integral_map (φ := fun u : U => inner ℝ (e k) u) (f := id)
      hcont.measurable.aemeasurable continuous_id.measurable.aestronglyMeasurable]
    simpa using hmean (e k)
  have hvar : ProbabilityTheory.variance id (Measure.map (fun u : U => inner ℝ (e k) u) μ)
      = c k := by
    rw [ProbabilityTheory.variance_eq_integral (X := id) continuous_id.measurable.aemeasurable]
    rw [hmean_id]
    simp only [pow_two]
    rw [MeasureTheory.integral_map (φ := fun u : U => inner ℝ (e k) u)
      (f := fun x : ℝ => (id x - inner ℝ (e k) m) * (id x - inner ℝ (e k) m))
      hcont.measurable.aemeasurable
      ((continuous_id.sub continuous_const).mul
        (continuous_id.sub continuous_const)).measurable.aestronglyMeasurable]
    have h := hcov_diag k k
    simp at h
    rw [← h]
    simp
  have hmain := ProbabilityTheory.IsGaussian.eq_gaussianReal
    (Measure.map (fun u : U => inner ℝ (e k) u) μ) hν
  rw [hmain, hmean_id, hvar]
  /- @proof-region region.target-node.session.f08754575259aa72 end -/

end Statlib.Imported
end

