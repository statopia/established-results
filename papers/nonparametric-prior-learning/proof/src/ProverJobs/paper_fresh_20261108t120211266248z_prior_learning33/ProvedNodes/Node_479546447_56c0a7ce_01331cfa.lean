import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_454462448_6086eebe_8546ee4b

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
theorem statopia_math_node_479546447_56c0a7ce : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc : ∀ k : ℕ, 0 < c k)
    (μ : Measure U) [IsProbabilityMeasure μ] (mUM mNU : U) (F : Finset ℕ)
    (hmap : Measure.map (fun u : U => fun k : {k : ℕ // k ∈ F} => inner ℝ (e k) u) μ
      = Measure.pi (fun k : {k : ℕ // k ∈ F} =>
          ProbabilityTheory.gaussianReal (inner ℝ (e k) mUM) (Real.toNNReal (c k)))), ∫⁻ u : U, (ENNReal.ofReal (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) *
          inner ℝ (e k) (u - mUM)) - (2 : ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ *
          (inner ℝ (e k) (mNU - mUM)) ^ 2))) ^ 2 ∂μ
      = ENNReal.ofReal (Real.exp (∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)) := by
  /- @proof-region region.target-node.session.07c0159597a9a737 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ mUM mNU F hmap
  classical
  let ι := {k : ℕ // k ∈ F}
  let m : ι → ℝ := fun k => inner ℝ (e (k:ℕ)) mUM
  let n : ι → ℝ := fun k => inner ℝ (e (k:ℕ)) mNU
  let σ : ι → ℝ := fun k => c (k:ℕ)
  let δ : ι → ℝ := fun k => n k - m k
  let a : ι → ℝ := fun k => (σ k)⁻¹ * δ k
  let D : ι → ℝ → ℝ := fun k y => Real.exp (a k * (y - m k) - (2:ℝ)⁻¹ * a k * δ k)
  let Pmu : Measure (ι → ℝ) := Measure.pi (fun k => gaussianReal (m k) (Real.toNNReal (σ k)))
  let ιF : U → (ι → ℝ) := fun u k => inner ℝ (e (k:ℕ)) u
  have hmap' : Measure.map ιF μ = Pmu := hmap
  have hσ : ∀ k : ι, 0 < σ k := fun k => hc (k:ℕ)
  have hchild := statopia_math_node_454462448_6086eebe ι σ m n hσ
  have h4' : ∫⁻ y : ι → ℝ, (ENNReal.ofReal (∏ k, D k (y k))) ^ 2 ∂Pmu
      = ENNReal.ofReal (Real.exp (∑ k, (σ k)⁻¹ * (δ k) ^ 2)) := hchild.2.2.2
  have h3 : ∀ u : U, (∑ k : ι, a k * (ιF u k - m k))
      = ∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM) := by
    intro u
    have h3a : (∑ k : ι, a k * (ιF u k - m k))
        = ∑ k : ι, ((c (k:ℕ))⁻¹ * inner ℝ (e (k:ℕ)) (mNU - mUM) * inner ℝ (e (k:ℕ)) (u - mUM)) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [a, δ, ιF, m, n]
      simp only [inner_sub_right]
      ring
    rw [h3a]
    exact (Finset.sum_subtype F (fun x => Iff.rfl) (fun k => (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM))).symm
  have h4 : (∑ k : ι, a k * δ k)
      = ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := by
    have h4a : (∑ k : ι, a k * δ k)
        = ∑ k : ι, ((c (k:ℕ))⁻¹ * (inner ℝ (e (k:ℕ)) (mNU - mUM)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [a, δ, σ, m, n]
      simp only [inner_sub_right]
      ring
    rw [h4a]
    exact (Finset.sum_subtype F (fun x => Iff.rfl) (fun k => (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)).symm
  have hpt : ∀ u : U, Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2:ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
      = ∏ k : ι, D k (ιF u k) := by
    intro u
    show Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2:ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2)
      = ∏ k : ι, Real.exp (a k * (ιF u k - m k) - (2:ℝ)⁻¹ * a k * δ k)
    have hprod : (∏ k : ι, Real.exp (a k * (ιF u k - m k) - (2:ℝ)⁻¹ * a k * δ k))
        = Real.exp (∑ k : ι, (a k * (ιF u k - m k) - (2:ℝ)⁻¹ * a k * δ k)) := by
      rw [← Real.exp_sum]
    have h2a : (∑ k : ι, (2:ℝ)⁻¹ * a k * δ k) = (2:ℝ)⁻¹ * ∑ k : ι, a k * δ k := by
      have h : (∑ k : ι, (2:ℝ)⁻¹ * a k * δ k) = ∑ k : ι, (2:ℝ)⁻¹ * (a k * δ k) :=
        Finset.sum_congr rfl (fun k _ => by ring)
      rw [h]
      conv_lhs => rw [← Finset.mul_sum]
    have h2 : (∑ k : ι, (a k * (ιF u k - m k) - (2:ℝ)⁻¹ * a k * δ k))
        = (∑ k : ι, a k * (ιF u k - m k)) - (2:ℝ)⁻¹ * ∑ k : ι, a k * δ k := by
      rw [Finset.sum_sub_distrib, h2a]
    rw [hprod]
    congr 1
    rw [h2, h3 u, h4]
  have hιF_meas : Measurable ιF :=
    measurable_pi_iff.2 (fun k => (continuous_const.inner continuous_id).measurable)
  have hDmeas : ∀ k : ι, Measurable (D k) := by
    intro k
    have hcont : Continuous (fun y : ℝ => a k * (y - m k) - (2:ℝ)⁻¹ * a k * δ k) := by
      continuity
    exact Real.continuous_exp.measurable.comp hcont.measurable
  have hENN : Measurable (fun y : ι → ℝ => ENNReal.ofReal (∏ k, D k (y k))) := by
    refine Measurable.ennreal_ofReal ?_
    refine Finset.measurable_prod (s := (Finset.univ : Finset ι)) (f := fun k (y : ι → ℝ) => D k (y k)) ?_
    intro k _
    exact (hDmeas k).comp (measurable_pi_apply k)
  have hFmeas : Measurable (fun y : ι → ℝ => (ENNReal.ofReal (∏ k, D k (y k))) ^ 2) :=
    hENN.pow_const 2
  have step1 : (∫⁻ u : U, (ENNReal.ofReal (Real.exp ((∑ k ∈ F, (c k)⁻¹ * inner ℝ (e k) (mNU - mUM) * inner ℝ (e k) (u - mUM)) - (2:ℝ)⁻¹ * ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2))) ^ 2 ∂μ)
      = ∫⁻ u : U, (ENNReal.ofReal (∏ k, D k (ιF u k))) ^ 2 ∂μ := by
    apply MeasureTheory.lintegral_congr
    intro u
    rw [hpt u]
  have step2 : (∫⁻ u : U, (ENNReal.ofReal (∏ k, D k (ιF u k))) ^ 2 ∂μ)
      = ∫⁻ y : ι → ℝ, (ENNReal.ofReal (∏ k, D k (y k))) ^ 2 ∂Pmu := by
    rw [← hmap']
    exact (MeasureTheory.lintegral_map
      (f := fun y : ι → ℝ => (ENNReal.ofReal (∏ k, D k (y k))) ^ 2) hFmeas hιF_meas).symm
  have hsum : (∑ k : ι, (σ k)⁻¹ * (δ k) ^ 2)
      = ∑ k ∈ F, (c k)⁻¹ * (inner ℝ (e k) (mNU - mUM)) ^ 2 := by
    have hsa : (∑ k : ι, (σ k)⁻¹ * (δ k) ^ 2) = ∑ k : ι, a k * δ k := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [a]
      ring
    rw [hsa, h4]
  exact step1.trans (step2.trans (h4'.trans (by rw [hsum])))
  /- @proof-region region.target-node.session.07c0159597a9a737 end -/

end Statlib.Imported
end

