import Lean
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Vocabulary
import ProverJobs.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Base

namespace PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e

open _root_.PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2778848356_36628207 : ∀ (q : ℕ) (hq : 1 ≤ q) (p : ℕ) (hp : 1 ≤ p)
    (f : (Fin q → ℝ) → (Fin p → ℝ)) (hf : Measurable f)
    (P : Measure ((Fin q → ℝ) × (Fin p → ℝ))) [hP : IsProbabilityMeasure P]
    (hInt : ∀ i j : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
      (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) P)
    (N : ℕ) (hN : 1 ≤ N)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (rows : Fin N → Ω → (Fin q → ℝ) × (Fin p → ℝ))
    (hrows : ∀ l : Fin N, Measurable (rows l))
    (hmap : ∀ l : Fin N, Measure.map (rows l) μ = P),
    (∀ (l : Fin N) (i j : Fin p),
      Measurable (fun ω : Ω =>
        (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)
          - SigmaX f P i j) ∧
      Integrable (fun ω : Ω =>
        (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)
          - SigmaX f P i j) μ ∧
      ∫ ω, ((f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)
          - SigmaX f P i j) ∂μ = 0) ∧
    (∀ i j : Fin p,
      Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
        (f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j)) ∧
    (∀ i j : Fin p, Measurable (fun ω : Ω => empSigma f rows ω i j)) ∧
    (∀ t : ℝ,
      MeasurableSet {ω : Ω | ∀ i j : Fin p,
        |empSigma f rows ω i j - SigmaX f P i j| ≤ t} ∧
      MeasurableSet {ω : Ω | ∃ i j : Fin p,
        t < |empSigma f rows ω i j - SigmaX f P i j|}) := by
  /- @proof-region region.target-node.session.861236ce5aa59642 begin -/
  intro q hq p hp f hf P hP hInt N hN Ω hΩ μ hμ rows hrows hmap
  have h_shift : ∀ k : Fin p, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k + z.2 k) := by
    intro k
    have h1 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k) :=
      (measurable_pi_apply k).comp (hf.comp measurable_fst)
    have h2 : Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    exact h1.add h2
  have h_base : ∀ i j : Fin p, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) :=
    fun i j => (h_shift i).mul (h_shift j)
  have h_prod : ∀ i j : Fin p, Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => (f z.1 i + z.2 i) * (f z.1 j + z.2 j) - SigmaX f P i j) :=
    fun i j => (h_base i j).sub measurable_const
  have h_entry : ∀ i j : Fin p, Measurable (fun ω : Ω => empSigma f rows ω i j) := by
    intro i j
    have heq : (fun ω : Ω => empSigma f rows ω i j) = fun ω => (N : ℝ)⁻¹ * ∑ l : Fin N, (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j) := by
      funext ω; rfl
    rw [heq]
    have hsum : Measurable (fun ω : Ω => ∑ l : Fin N, (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)) :=
      Finset.measurable_sum Finset.univ (fun l _ => (h_base i j).comp (hrows l))
    exact measurable_const.mul hsum
  refine ⟨?_, h_prod, h_entry, ?_⟩
  · intro l i j
    have hInt_base : Integrable (fun ω : Ω => (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)) μ := by
      have key := MeasureTheory.integrable_map_measure (μ := μ) (f := rows l) (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) ((h_base i j).stronglyMeasurable.aestronglyMeasurable) (hrows l).aemeasurable
      rw [hmap l] at key
      exact key.mp (hInt i j)
    have h_int_g : ∫ ω : Ω, (f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j) ∂μ = SigmaX f P i j := by
      have hstep := MeasureTheory.integral_map_of_stronglyMeasurable (μ := μ) (φ := rows l) (hrows l) (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) (h_base i j).stronglyMeasurable
      rw [hmap l] at hstep
      exact hstep.symm
    have hc : ∫ ω : Ω, (SigmaX f P i j : ℝ) ∂μ = SigmaX f P i j := by
      rw [MeasureTheory.integral_const]
      simp [Measure.real, measure_univ]
    refine ⟨?_, ?_, ?_⟩
    · exact (h_prod i j).comp (hrows l)
    · exact hInt_base.sub (integrable_const (SigmaX f P i j))
    · calc
        ∫ ω, ((f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j) - SigmaX f P i j) ∂μ
            = ∫ ω, ((f (rows l ω).1 i + (rows l ω).2 i) * (f (rows l ω).1 j + (rows l ω).2 j)) ∂μ - ∫ ω, (SigmaX f P i j : ℝ) ∂μ := integral_sub hInt_base (integrable_const (SigmaX f P i j))
        _ = SigmaX f P i j - SigmaX f P i j := by simp only [h_int_g, hc]
        _ = 0 := sub_self _
  · intro t
    refine ⟨?_, ?_⟩
    · have heq : {ω : Ω | ∀ i j : Fin p, |empSigma f rows ω i j - SigmaX f P i j| ≤ t} = ⋂ (i : Fin p), ⋂ (j : Fin p), {ω : Ω | |empSigma f rows ω i j - SigmaX f P i j| ≤ t} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [heq]
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_le ((h_entry i j).sub measurable_const).abs measurable_const
    · have heq : {ω : Ω | ∃ i j : Fin p, t < |empSigma f rows ω i j - SigmaX f P i j|} = ⋃ (i : Fin p), ⋃ (j : Fin p), {ω : Ω | t < |empSigma f rows ω i j - SigmaX f P i j|} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      rw [heq]
      apply MeasurableSet.iUnion
      intro i
      apply MeasurableSet.iUnion
      intro j
      exact measurableSet_lt measurable_const ((h_entry i j).sub measurable_const).abs
  /- @proof-region region.target-node.session.861236ce5aa59642 end -/

end Statlib.Imported

