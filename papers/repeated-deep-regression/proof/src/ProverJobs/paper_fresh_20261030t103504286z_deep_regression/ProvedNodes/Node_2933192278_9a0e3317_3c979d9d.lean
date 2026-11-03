import Statlib.StatFoundation.Vocabulary.EmpiricalProcess
import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.ProvedNodes.Node_388877899_e269fd78_7b6b480c

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2933192278_9a0e3317 : ∀ (ΩS : Type*) [MeasurableSpace ΩS] (mu : Measure ΩS) [IsProbabilityMeasure mu]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (sig : Fin n × Fin m → ΩS → ℝ)
    (hSig_meas : ∀ ij : Fin n × Fin m, Measurable (sig ij))
    (hSig_indep : iIndepFun sig mu)
    (hSig_val : ∀ ij : Fin n × Fin m,
      mu {ω | sig ij ω = 1} = 1 / 2 ∧ mu {ω | sig ij ω = -1} = 1 / 2),
    Measure.map (Function.swap sig) mu
      = (Fintype.card (Fin n × Fin m → Bool) : ℝ≥0∞)⁻¹ •
          ∑ ε : (Fin n × Fin m → Bool),
            Measure.dirac (fun ij => Statlib.StatFoundation.Vocabulary.rademacherSign (ε ij)) := by
  /- @proof-region region.target-node.session.4c340ed65a22d155 begin -/
  intro ΩS _ mu _ n m hn hm sig hSig_meas hSig_indep hSig_val
  have hpi : Measure.map (Function.swap sig) mu = Measure.pi (fun ij => Measure.map (sig ij) mu) := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (μ := mu) (f := sig)
      (fun ij => (hSig_meas ij).aemeasurable)).1 hSig_indep
    simpa using h
  have hcoord : ∀ ij : Fin n × Fin m,
      Measure.map (sig ij) mu = (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ)) := by
    intro ij
    have hf : Measurable (sig ij) := hSig_meas ij
    obtain ⟨h1, h2⟩ := hSig_val ij
    have hsmul : ∀ x : ℝ≥0∞, (2 : ℝ≥0∞)⁻¹ • x = (2 : ℝ≥0∞)⁻¹ * x := fun x => rfl
    have hA : MeasurableSet {ω | sig ij ω = 1} := hf (measurableSet_singleton 1)
    have hB : MeasurableSet {ω | sig ij ω = -1} := hf (measurableSet_singleton (-1))
    classical
    have hdisj : Disjoint {ω | sig ij ω = 1} {ω | sig ij ω = -1} := by
      rw [Set.disjoint_left]
      intro ω hω1 hω2
      simp only [Set.mem_setOf_eq] at hω1 hω2
      linarith
    have hu : mu ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1}) = 1 := by
      rw [measure_union hdisj hB, h1, h2]
      simpa using ENNReal.add_halves (1 : ℝ≥0∞)
    have hcompl : mu ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})ᶜ = 0 := by
      rw [measure_compl (hA.union hB) (by rw [hu]; simp), hu]
      simp
    have hkey : ∀ T : Set ΩS,
        mu T = mu (T ∩ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})) := by
      intro T
      have hTU : T = (T ∩ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1}))
          ∪ (T \ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})) := by
        ext ω
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
        tauto
      apply le_antisymm
      · have hle : mu ((T ∩ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1}))
            ∪ (T \ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})))
            ≤ mu (T ∩ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1}))
              + mu (T \ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})) := measure_union_le _ _
        rw [← hTU] at hle
        have hz : mu (T \ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})) = 0 := by
          refine le_antisymm ?_ (zero_le _)
          have hle' : mu (T \ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1}))
              ≤ mu ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})ᶜ :=
            measure_mono (fun ω hω => hω.2)
          rw [hcompl] at hle'
          exact hle'
        rw [hz, add_zero] at hle
        exact hle
      · exact measure_mono Set.inter_subset_left
    have hC : ∀ T : Set ℝ, mu (sig ij ⁻¹' T ∩ {ω | sig ij ω = 1})
        = (2 : ℝ≥0∞)⁻¹ * (if (1 : ℝ) ∈ T then 1 else 0) := by
      intro T
      by_cases hT1 : (1 : ℝ) ∈ T
      · have he : sig ij ⁻¹' T ∩ {ω | sig ij ω = 1} = {ω | sig ij ω = 1} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hT1, h⟩⟩
        rw [he, if_pos hT1, h1]
        simp
      · have h0 : mu (sig ij ⁻¹' T ∩ {ω | sig ij ω = 1}) = 0 := by
          refine le_antisymm ?_ (zero_le _)
          have hsub : sig ij ⁻¹' T ∩ {ω | sig ij ω = 1} ⊆ ∅ := by
            intro ω hω
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq] at hω
            exact hT1 (hω.2 ▸ hω.1)
          have hle : mu (sig ij ⁻¹' T ∩ {ω | sig ij ω = 1}) ≤ mu (∅ : Set ΩS) :=
            measure_mono hsub
          simpa using hle
        rw [h0, if_neg hT1, mul_zero]
    have hD : ∀ T : Set ℝ, mu (sig ij ⁻¹' T ∩ {ω | sig ij ω = -1})
        = (2 : ℝ≥0∞)⁻¹ * (if (-1 : ℝ) ∈ T then 1 else 0) := by
      intro T
      by_cases hT1 : (-1 : ℝ) ∈ T
      · have he : sig ij ⁻¹' T ∩ {ω | sig ij ω = -1} = {ω | sig ij ω = -1} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hT1, h⟩⟩
        rw [he, if_pos hT1, h2]
        simp
      · have h0 : mu (sig ij ⁻¹' T ∩ {ω | sig ij ω = -1}) = 0 := by
          refine le_antisymm ?_ (zero_le _)
          have hsub : sig ij ⁻¹' T ∩ {ω | sig ij ω = -1} ⊆ ∅ := by
            intro ω hω
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq] at hω
            exact hT1 (hω.2 ▸ hω.1)
          have hle : mu (sig ij ⁻¹' T ∩ {ω | sig ij ω = -1}) ≤ mu (∅ : Set ΩS) :=
            measure_mono hsub
          simpa using hle
        rw [h0, if_neg hT1, mul_zero]
    have hmem : ∀ T : Set ℝ, MeasurableSet T → mu (sig ij ⁻¹' T)
        = (2 : ℝ≥0∞)⁻¹ * ((if (1 : ℝ) ∈ T then 1 else 0) + (if (-1 : ℝ) ∈ T then 1 else 0)) := by
      intro T hT
      rw [hkey (sig ij ⁻¹' T)]
      have hdist : sig ij ⁻¹' T ∩ ({ω | sig ij ω = 1} ∪ {ω | sig ij ω = -1})
          = (sig ij ⁻¹' T ∩ {ω | sig ij ω = 1}) ∪ (sig ij ⁻¹' T ∩ {ω | sig ij ω = -1}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
        tauto
      have hdisj2 : Disjoint (sig ij ⁻¹' T ∩ {ω | sig ij ω = 1})
          (sig ij ⁻¹' T ∩ {ω | sig ij ω = -1}) := by
        rw [Set.disjoint_left]
        rintro ω ⟨-, hω1⟩ ⟨-, hω2⟩
        simp only [Set.mem_setOf_eq] at hω1 hω2
        linarith
      have hmeas2 : MeasurableSet (sig ij ⁻¹' T ∩ {ω | sig ij ω = -1}) := (hf hT).inter hB
      rw [hdist, measure_union hdisj2 hmeas2, hC T, hD T, mul_add]
    ext S hS
    rw [Measure.map_apply hf hS, Measure.smul_apply, Measure.add_apply,
      Measure.dirac_apply, Measure.dirac_apply, hsmul, hmem S hS]
    by_cases h1' : (1 : ℝ) ∈ S <;> by_cases h2' : (-1 : ℝ) ∈ S <;> simp [h1', h2']
  have hconst : Measure.pi (fun ij : Fin n × Fin m => Measure.map (sig ij) mu)
      = Measure.pi (fun _ : Fin n × Fin m => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))) := by
    rw [funext hcoord]
  have hlaw : Measure.pi (fun _ : Fin n × Fin m => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ)))
      = (Fintype.card (Fin n × Fin m → Bool) : ℝ≥0∞)⁻¹ •
          ∑ ε : (Fin n × Fin m → Bool),
            Measure.dirac (fun ij => Statlib.StatFoundation.Vocabulary.rademacherSign (ε ij)) := by
    exact statopia_math_node_388877899_e269fd78 (ι := Fin n × Fin m)
  rw [hpi, hconst, hlaw]
  /- @proof-region region.target-node.session.4c340ed65a22d155 end -/

end Statlib.Imported
end

