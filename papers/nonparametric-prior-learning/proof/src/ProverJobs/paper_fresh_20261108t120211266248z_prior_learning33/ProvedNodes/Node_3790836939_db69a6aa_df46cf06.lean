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
theorem statopia_math_node_3790836939_db69a6aa : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (μ : Measure U) [IsProbabilityMeasure μ] (m : U)
    (hmean : ∀ v : U, ∫ u, inner ℝ v u ∂μ = inner ℝ v m)
    (hcov_diag : ∀ k l : ℕ,
      ∫ u, (inner ℝ (e k) u - inner ℝ (e k) m) * (inner ℝ (e l) u - inner ℝ (e l) m) ∂μ
        = if k = l then c k else 0)
    (hint1 : ∀ v : U, Integrable (fun u : U => inner ℝ v u) μ)
    (hint2 : ∀ v w : U,
      Integrable (fun u : U =>
        (inner ℝ v u - inner ℝ v m) * (inner ℝ w u - inner ℝ w m)) μ)
    (F : Finset ℕ) (t : {k : ℕ // k ∈ F} → ℝ),
    ProbabilityTheory.variance (id : ℝ → ℝ)
        (Measure.map (innerSL ℝ (∑ k : {k : ℕ // k ∈ F}, t k • e (k : ℕ))) μ)
      = ∑ k : {k : ℕ // k ∈ F}, (t k) ^ 2 * c (k : ℕ) := by
  /- @proof-region region.target-node.session.e0efa7b30dd13bd2 begin -/
  intro U _ _ _ _ _ _ e c μ _ m hmean hcov_diag hint1 hint2 F t
  classical
  set V : U := ∑ k : {k : ℕ // k ∈ F}, t k • e (k : ℕ) with hV
  set b : ℝ := inner ℝ V m with hb
  set ν : Measure ℝ := Measure.map (innerSL ℝ V) μ with hν
  have hφ : AEMeasurable (⇑(innerSL ℝ V)) μ :=
    (innerSL ℝ V).continuous.measurable.aemeasurable
  have hmeanν : ∫ y : ℝ, y ∂ν = b := by
    have h1 : ∫ u : U, inner ℝ V u ∂μ = b := by
      rw [hb]
      exact hmean V
    rw [hν, ← h1]
    simpa only [innerSL_apply_apply] using
      (integral_map (φ := ⇑(innerSL ℝ V)) (μ := μ) hφ (f := fun y : ℝ => y)
        measurable_id.aestronglyMeasurable)
  have hvar : variance (id : ℝ → ℝ) ν = ∫ x : ℝ, (x - b) ^ 2 ∂ν := by
    have h := variance_eq_integral (μ := ν) (X := id) measurable_id.aemeasurable
    have h2 : ∫ x : ℝ, id x ∂ν = b := by simpa using hmeanν
    rw [h2] at h
    simpa using h
  have hf2 : AEStronglyMeasurable (fun y : ℝ => (y - b) ^ 2) (Measure.map (⇑(innerSL ℝ V)) μ) :=
    (((continuous_id.sub continuous_const).pow 2) :
      Continuous fun y : ℝ => (y - b) ^ 2).measurable.aestronglyMeasurable
  have hmap2 : ∫ x : ℝ, (x - b) ^ 2 ∂ν = ∫ u : U, (inner ℝ V u - b) ^ 2 ∂μ := by
    have key : ∫ y : ℝ, (y - b) ^ 2 ∂Measure.map (⇑(innerSL ℝ V)) μ
        = ∫ u : U, (⇑(innerSL ℝ V) u - b) ^ 2 ∂μ :=
      integral_map hφ (f := fun y : ℝ => (y - b) ^ 2) hf2
    rw [hν, key]
    simp only [innerSL_apply_apply]
  rw [hvar, hmap2]
  set X : {n : ℕ // n ∈ F} → U → ℝ :=
    fun k u => inner ℝ (e (k:ℕ)) u - inner ℝ (e (k:ℕ)) m with hX
  have hXpt : ∀ u : U, inner ℝ V u - b = ∑ k : {n : ℕ // n ∈ F}, t k * X k u := by
    intro u
    have h1 : inner ℝ V u = ∑ k : {n : ℕ // n ∈ F}, t k * inner ℝ (e (k:ℕ)) u := by
      rw [hV, sum_inner]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [inner_smul_left]
      simp
    have h2 : inner ℝ V m = ∑ k : {n : ℕ // n ∈ F}, t k * inner ℝ (e (k:ℕ)) m := by
      rw [hV, sum_inner]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [inner_smul_left]
      simp
    rw [h1, hb, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hX]
    ring
  have hXpt2 : ∀ u : U, (inner ℝ V u - b) ^ 2
      = ∑ k : {n : ℕ // n ∈ F}, ∑ l : {n : ℕ // n ∈ F},
          (t k * t l) * (X k u * X l u) := by
    intro u
    rw [hXpt u, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  have hGint : ∀ k l : {n : ℕ // n ∈ F},
      Integrable (fun u : U => (t k * t l) * (X k u * X l u)) μ := by
    intro k l
    simpa only [hX] using (hint2 (e (k:ℕ)) (e (l:ℕ))).const_mul (t k * t l)
  have hGsum : ∀ k : {n : ℕ // n ∈ F},
      Integrable (fun u : U => ∑ l : {n : ℕ // n ∈ F}, (t k * t l) * (X k u * X l u)) μ :=
    fun k => integrable_finset_sum _ (fun l _ => hGint k l)
  have hA : ∫ u : U, ∑ k : {n : ℕ // n ∈ F}, ∑ l : {n : ℕ // n ∈ F},
        (t k * t l) * (X k u * X l u) ∂μ
      = ∑ k : {n : ℕ // n ∈ F}, ∑ l : {n : ℕ // n ∈ F},
          ∫ u : U, (t k * t l) * (X k u * X l u) ∂μ := by
    rw [integral_finset_sum Finset.univ (fun k _ => hGsum k)]
    exact Finset.sum_congr rfl
      (fun k _ => integral_finset_sum Finset.univ (fun l _ => hGint k l))
  have hB : ∀ k l : {n : ℕ // n ∈ F},
      ∫ u : U, (t k * t l) * (X k u * X l u) ∂μ
        = (t k * t l) * (if ((k:ℕ) = (l:ℕ)) then c (k:ℕ) else 0) := by
    intro k l
    rw [integral_const_mul (t k * t l) (fun u : U => X k u * X l u)]
    congr 1
    simpa only [hX] using hcov_diag (k:ℕ) (l:ℕ)
  have hC : ∀ k : {n : ℕ // n ∈ F},
      ∑ l : {n : ℕ // n ∈ F}, (t k * t l) * (if ((k:ℕ) = (l:ℕ)) then c (k:ℕ) else 0)
        = (t k) ^ 2 * c (k:ℕ) := by
    intro k
    rw [Finset.sum_eq_single (a := k)]
    · simp [pow_two]
    · intro l _ hl
      have hkl : ¬ ((k:ℕ) = (l:ℕ)) := fun h => hl (Subtype.ext h).symm
      simp [hkl]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hstep : ∫ u : U, (inner ℝ V u - b) ^ 2 ∂μ
      = ∫ u : U, ∑ k : {n : ℕ // n ∈ F}, ∑ l : {n : ℕ // n ∈ F},
          (t k * t l) * (X k u * X l u) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall (fun u => ?_))
    exact hXpt2 u
  rw [hstep, hA]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_congr rfl (fun l _ => hB k l)]
  exact hC k
  /- @proof-region region.target-node.session.e0efa7b30dd13bd2 end -/

end Statlib.Imported
end

