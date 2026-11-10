import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1218121120_7255afae_cddb3a58

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
theorem statopia_math_node_1446388444_2df19b16 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U)
    (μ ν : Measure U) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : U → ℝ≥0∞) (hρ : Measurable ρ)
    (hcyl : ∀ (F : Finset ℕ) (B : Set ({k : ℕ // k ∈ F} → ℝ)), MeasurableSet B →
      ∫⁻ u in {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e (k : ℕ)) u) ∈ B}, ρ u ∂μ
        = ν {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e (k : ℕ)) u) ∈ B}),
    ν = μ.withDensity ρ := by
  /- @proof-region region.target-node.session.7931bdaf1899adb3 begin -/
  intro U _ _ _ _ _ _ e μ ν _ _ ρ hρ hcyl
  let C : Set (Set U) := {s | ∃ (F : Finset ℕ) (B : Set ({k : ℕ // k ∈ F} → ℝ)),
      MeasurableSet B ∧ s = {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e (k:ℕ)) u) ∈ B}}
  have hmeas_cyl : ∀ (F : Finset ℕ) (B : Set ({k : ℕ // k ∈ F} → ℝ)), MeasurableSet B →
      MeasurableSet {u : U | (fun k : {k : ℕ // k ∈ F} => inner ℝ (e (k:ℕ)) u) ∈ B} := by
    intro F B hB
    have hM : Measurable (fun u : U => fun k : {k : ℕ // k ∈ F} => inner ℝ (e (k:ℕ)) u) := by
      rw [measurable_pi_iff]
      intro k
      exact (continuous_const.inner continuous_id).measurable
    exact hM hB
  have hpi : IsPiSystem C := by
    intro s1 hs1 s2 hs2 _
    obtain ⟨F1, B1, hB1, hs1⟩ := hs1
    obtain ⟨F2, B2, hB2, hs2⟩ := hs2
    rw [hs1, hs2]
    refine ⟨F1 ∪ F2,
      {x | (fun k : {k : ℕ // k ∈ F1} => x ⟨k.1, Finset.mem_union.mpr (Or.inl k.2)⟩) ∈ B1} ∩
      {x | (fun k : {k : ℕ // k ∈ F2} => x ⟨k.1, Finset.mem_union.mpr (Or.inr k.2)⟩) ∈ B2}, ?_, ?_⟩
    · apply MeasurableSet.inter
      · have hm : Measurable (fun x : ({k : ℕ // k ∈ F1 ∪ F2} → ℝ) =>
            fun k : {k : ℕ // k ∈ F1} => x ⟨k.1, Finset.mem_union.mpr (Or.inl k.2)⟩) := by
          rw [measurable_pi_iff]; intro k
          exact measurable_pi_apply (⟨k.1, Finset.mem_union.mpr (Or.inl k.2)⟩ : {k : ℕ // k ∈ F1 ∪ F2})
        exact hm hB1
      · have hm : Measurable (fun x : ({k : ℕ // k ∈ F1 ∪ F2} → ℝ) =>
            fun k : {k : ℕ // k ∈ F2} => x ⟨k.1, Finset.mem_union.mpr (Or.inr k.2)⟩) := by
          rw [measurable_pi_iff]; intro k
          exact measurable_pi_apply (⟨k.1, Finset.mem_union.mpr (Or.inr k.2)⟩ : {k : ℕ // k ∈ F1 ∪ F2})
        exact hm hB2
    · ext u
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  let C0 : Set (Set U) := {s | ∃ (n : ℕ) (C' : Set (Fin n → ℝ)), MeasurableSet C' ∧
      s = (fun u : U => fun i : Fin n => inner ℝ (e (i:ℕ)) u) ⁻¹' C'}
  have hC0sub : C0 ⊆ C := by
    rintro s ⟨n, C', hC', hs⟩
    rw [hs]
    let B : Set ({k : ℕ // k ∈ Finset.range n} → ℝ) :=
      {v | (fun i : Fin n => v ⟨i.1, by rw [Finset.mem_range]; exact i.2⟩) ∈ C'}
    refine ⟨Finset.range n, B, ?_, ?_⟩
    · have hφ : Measurable (fun v : ({k : ℕ // k ∈ Finset.range n} → ℝ) =>
          fun i : Fin n => v ⟨i.1, by rw [Finset.mem_range]; exact i.2⟩) := by
        rw [measurable_pi_iff]
        intro i
        exact measurable_pi_apply (⟨i.1, by rw [Finset.mem_range]; exact i.2⟩ : {k : ℕ // k ∈ Finset.range n})
      exact hφ hC'
    · ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      exact Iff.rfl
  have hgen : (‹MeasurableSpace U›) = MeasurableSpace.generateFrom C := by
    have hchild : (‹MeasurableSpace U›) = MeasurableSpace.generateFrom C0 :=
      statopia_math_node_1218121120_7255afae (e := e)
    refine hchild.trans (le_antisymm (MeasurableSpace.generateFrom_mono hC0sub) ?_)
    have hle : MeasurableSpace.generateFrom C ≤ ‹MeasurableSpace U› :=
      MeasurableSpace.generateFrom_le (fun t ht => by
        obtain ⟨F, B, hB, ht_eq⟩ := ht
        rw [ht_eq]
        exact hmeas_cyl F B hB)
    exact hle.trans (le_of_eq hchild)
  have hagree : ∀ s ∈ C, ν s = (μ.withDensity ρ) s := by
    rintro s ⟨F, B, hB, hs⟩
    rw [hs, MeasureTheory.withDensity_apply ρ (hmeas_cyl F B hB)]
    exact (hcyl F B hB).symm
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion C (fun _ => Set.univ) hgen hpi ?_ ?_ ?_ hagree
  · ext x; simp
  · intro i; exact ⟨∅, Set.univ, MeasurableSet.univ, by simp⟩
  · intro i; rw [measure_univ]; exact ENNReal.one_ne_top
  /- @proof-region region.target-node.session.7931bdaf1899adb3 end -/

end Statlib.Imported
end

