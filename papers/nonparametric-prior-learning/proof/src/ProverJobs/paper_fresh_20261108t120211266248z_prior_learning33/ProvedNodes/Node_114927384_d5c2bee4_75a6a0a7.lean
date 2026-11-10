import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1420010127_b25b6ecd_7a5d1e55
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3186299420_34298c40_d72dbf33
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_3790836939_db69a6aa_df46cf06

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
theorem statopia_math_node_114927384_d5c2bee4 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
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
        (inner ℝ v u - inner ℝ v m) * (inner ℝ w u - inner ℝ w m)) μ),
    (∀ F : Finset ℕ,
      Measure.map (fun u : U => fun k : (F : Set ℕ) => inner ℝ (e k) u) μ
        = Measure.pi (fun k : (F : Set ℕ) =>
            gaussianReal (inner ℝ (e k) m) (Real.toNNReal (c k))) ∧
      iIndepFun (fun k : (F : Set ℕ) => fun u : U => inner ℝ (e k) u) μ) ∧
    (∀ (F : Finset ℕ) (t : {k : ℕ // k ∈ F} → ℝ),
      Measure.map (fun u : U => ∑ k : {k : ℕ // k ∈ F},
          t k * (inner ℝ (e k) u - inner ℝ (e k) m)) μ
        = gaussianReal 0
            (Real.toNNReal (∑ k : {k : ℕ // k ∈ F}, (t k) ^ 2 * c k))) := by
  /- @proof-region region.target-node.session.8adeae23124bc993 begin -/
  intro U _ _ _ _ _ _ e c hc μ _ hmu_gauss m hmean hcov_diag hint1 hint2
  refine ⟨?_, ?_⟩
  · intro F
    have hmap : Measure.map (fun u : U => fun k : (F : Set ℕ) => inner ℝ (e k) u) μ
        = Measure.pi (fun k : (F : Set ℕ) => gaussianReal (inner ℝ (e k) m) (Real.toNNReal (c k))) :=
      statopia_math_node_1420010127_b25b6ecd (U := U) (e := e) (c := c) (hc := hc) (μ := μ)
        (hmu_gauss := hmu_gauss) (m := m) (hmean := hmean) (hcov_diag := hcov_diag)
        (hint1 := hint1) (hint2 := hint2) F
    refine ⟨hmap, ?_⟩
    refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (fun i => ?_)).mpr ?_
    · exact ((continuous_const : Continuous (fun _ : U => e i)).inner continuous_id).measurable.aestronglyMeasurable.aemeasurable
    · have h2 : Measure.map (fun u : U => fun k : (F : Set ℕ) => inner ℝ (e k) u) μ
          = Measure.pi (fun i : (F : Set ℕ) => Measure.map (fun u => inner ℝ (e i) u) μ) := by
        rw [hmap]
        congr 1
        funext i
        exact (statopia_math_node_3186299420_34298c40 (U := U) (e := e) (c := c) (hc := hc)
          (μ := μ) (hmu_gauss := hmu_gauss) (m := m) (hmean := hmean) (hcov_diag := hcov_diag)
          (hint1 := hint1) (hint2 := hint2) i).symm
      exact h2
  · intro F t
    haveI : ProbabilityTheory.IsGaussian μ := hmu_gauss
    set V : U := (∑ k : {k : ℕ // k ∈ F}, t k • (e (k : ℕ))) with hV
    set b : ℝ := inner ℝ V m with hb
    have hV1 : ∀ u : U, (innerSL ℝ V) u + (-b)
        = ∑ k : {k : ℕ // k ∈ F}, t k * (inner ℝ (e k) u - inner ℝ (e k) m) := by
      intro u
      change inner ℝ V u + (-b)
        = ∑ k : {k : ℕ // k ∈ F}, t k * (inner ℝ (e k) u - inner ℝ (e k) m)
      have ha : inner ℝ V u = ∑ k : {k : ℕ // k ∈ F}, t k * inner ℝ (e k) u := by
        rw [hV, sum_inner]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [inner_smul_left]
      have hbm : b = ∑ k : {k : ℕ // k ∈ F}, t k * inner ℝ (e k) m := by
        rw [hb, hV, sum_inner]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [inner_smul_left]
      rw [ha, hbm]
      have hr : (∑ k : {k : ℕ // k ∈ F}, t k * (inner ℝ (e k) u - inner ℝ (e k) m))
          = ∑ k : {k : ℕ // k ∈ F}, (t k * inner ℝ (e k) u - t k * inner ℝ (e k) m) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [mul_sub]
      rw [hr, Finset.sum_sub_distrib, sub_eq_add_neg]
    have hmom : (∫ x : ℝ, id x ∂(Measure.map (innerSL ℝ V) μ) = b)
        ∧ (Var[id; Measure.map (innerSL ℝ V) μ]
            = ∑ k : {k : ℕ // k ∈ F}, (t k) ^ 2 * c k) := by
      constructor
      · rw [MeasureTheory.integral_map
          ((innerSL ℝ V).continuous.measurable.aemeasurable)
          (measurable_id.aestronglyMeasurable)]
        show (∫ x, inner ℝ V x ∂μ) = b
        rw [hmean V, ← hb]
      · rw [hV]
        exact statopia_math_node_3790836939_db69a6aa (U := U) (e := e) (c := c) (μ := μ) (m := m)
          (hmean := hmean) (hcov_diag := hcov_diag) (hint1 := hint1) (hint2 := hint2) F t
    have hGauss : ProbabilityTheory.IsGaussian (Measure.map (innerSL ℝ V) μ) :=
      ProbabilityTheory.isGaussian_map (innerSL ℝ V)
    have hν : Measure.map (innerSL ℝ V) μ
        = gaussianReal b (Real.toNNReal (∑ k : {k : ℕ // k ∈ F}, (t k) ^ 2 * c k)) := by
      rw [ProbabilityTheory.IsGaussian.eq_gaussianReal (Measure.map (innerSL ℝ V) μ) hGauss,
        hmom.1, hmom.2]
    have hcomp : (fun u : U => ∑ k : {k : ℕ // k ∈ F}, t k * (inner ℝ (e k) u - inner ℝ (e k) m))
        = ((fun x : ℝ => x + (-b)) ∘ (innerSL ℝ V)) := by
      funext u
      rw [Function.comp_apply]
      exact (hV1 u).symm
    rw [hcomp]
    rw [← MeasureTheory.Measure.map_map
      (show Measurable (fun x : ℝ => x + (-b)) from measurable_id.add_const (-b))
      (innerSL ℝ V).continuous.measurable]
    rw [hν, ProbabilityTheory.gaussianReal_map_add_const (-b)]
    rw [add_neg_cancel]
  /- @proof-region region.target-node.session.8adeae23124bc993 end -/

end Statlib.Imported
end

