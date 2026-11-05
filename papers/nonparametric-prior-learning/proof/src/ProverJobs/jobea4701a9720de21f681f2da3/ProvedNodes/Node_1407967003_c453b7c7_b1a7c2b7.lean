import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3787853579_cb43d7c4_db2b2ae0
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_1407967003_c453b7c7 : ∀ {Theta U : Type*} [MeasurableSpace Theta] [MeasurableSpace U]
    [MeasurableSpace.CountableOrCountablyGenerated Theta U]
    (Q HP : ProbabilityMeasure Theta) (K L : Kernel Theta U)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (h : ¬ ((Q : Measure Theta) ≪ (HP : Measure Theta) ∧
        ∀ᵐ theta ∂(Q : Measure Theta), (K theta : Measure U) ≪ (L theta : Measure U))),
    InformationTheory.klDiv ((Q : Measure Theta) ⊗ₘ K) ((HP : Measure Theta) ⊗ₘ L) = ⊤ ∧
    InformationTheory.klDiv (Q : Measure Theta) (HP : Measure Theta)
      + ∫⁻ theta, InformationTheory.klDiv (K theta) (L theta) ∂(Q : Measure Theta) = ⊤ := by
  /- @proof-region region.target-node.session.2084c373815cfee9 begin -/
  intro Theta U mTheta mU hCG Q HP K L hKinst hLinst h
  have hkeyP : ∀ {μ ν : Measure (Theta × U)}, [IsFiniteMeasure μ] → [IsFiniteMeasure ν] →
      ¬ μ ≪ ν → InformationTheory.klDiv μ ν = ⊤ := by
    intro μ ν hm hν hμν
    rw [InformationTheory.klDiv_eq_lintegral_klFun, if_neg hμν]
  have hkeyT : ∀ {μ ν : Measure Theta}, [IsFiniteMeasure μ] → [IsFiniteMeasure ν] →
      ¬ μ ≪ ν → InformationTheory.klDiv μ ν = ⊤ := by
    intro μ ν hm hν hμν
    rw [InformationTheory.klDiv_eq_lintegral_klFun, if_neg hμν]
  have hkeyU : ∀ {μ ν : Measure U}, [IsFiniteMeasure μ] → [IsFiniteMeasure ν] →
      ¬ μ ≪ ν → InformationTheory.klDiv μ ν = ⊤ := by
    intro μ ν hm hν hμν
    rw [InformationTheory.klDiv_eq_lintegral_klFun, if_neg hμν]
  refine ⟨?_, ?_⟩
  · exact hkeyP (fun hac => h (statopia_math_node_3787853579_cb43d7c4 Q HP K L hac))
  · by_cases hB : ∀ᵐ theta ∂(Q : Measure Theta), (K theta : Measure U) ≪ (L theta : Measure U)
    · have hA : ¬ ((Q : Measure Theta) ≪ (HP : Measure Theta)) := fun hA => h ⟨hA, hB⟩
      rw [hkeyT hA]
      simp
    · let S : Set Theta := {theta : Theta | (K theta : Measure U) ≪ (L theta : Measure U)}ᶜ
      have hSmeas : MeasurableSet S := (Kernel.measurableSet_absolutelyContinuous K L).compl
      have hQS : (Q : Measure Theta) S ≠ 0 := by
        have h' := hB
        rw [MeasureTheory.ae_iff] at h'
        simpa only [S, Set.compl_setOf] using h'
      have hpt : ∀ theta, S.indicator (fun _ => (⊤ : ℝ≥0∞)) theta ≤ InformationTheory.klDiv (K theta) (L theta) := by
        intro theta
        by_cases hθ : theta ∈ S
        · rw [Set.indicator_of_mem hθ]
          have hθ' : ¬ ((K theta : Measure U) ≪ (L theta : Measure U)) := by
            simpa only [S, Set.mem_compl_iff, Set.mem_setOf_eq] using hθ
          exact le_of_eq (hkeyU hθ').symm
        · simp [Set.indicator, hθ]
      have hind : ∫⁻ theta, InformationTheory.klDiv (K theta) (L theta) ∂(Q : Measure Theta) = ⊤ := by
        have htop : ∫⁻ theta, S.indicator (fun _ => (⊤ : ℝ≥0∞)) theta ∂(Q : Measure Theta) = ⊤ := by
          rw [MeasureTheory.lintegral_indicator hSmeas]
          change ∫⁻ theta in S, (⊤ : ℝ≥0∞) ∂(Q : Measure Theta) = ⊤
          rw [MeasureTheory.setLIntegral_const]
          simp [hQS]
        have hle : (⊤ : ℝ≥0∞) ≤ ∫⁻ theta, InformationTheory.klDiv (K theta) (L theta) ∂(Q : Measure Theta) := by
          rw [← htop]
          exact MeasureTheory.lintegral_mono hpt
        exact top_le_iff.mp hle
      rw [hind]
      simp
  /- @proof-region region.target-node.session.2084c373815cfee9 end -/

end
end Statlib.Imported
